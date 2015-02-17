#include <stdio.h>
#include <string.h>
#include <math.h>

#include "builtin.h"
#include "commit.h"
#include "object.h"
#include "tree.h"
#include "tree-walk.h"
#include "blob.h"
#include "diff.h"
#include "diffcore.h"
#include "hash.h"
#include "revision.h"
#include "xdiff/xdiff.h"
#include "levenshtein.h"
#include "parse-options.h"

#define dprintf if (debug) printf

#define OUTPUT_SHOW_PATH 0x1
#define OUTPUT_SHOW_NUMBER 0x2
#define OUTPUT_LONG_SHA1 0x4
#define OUTPUT_SHOW_EMAIL 0x8
#define OUTPUT_STRUCTURE 0x10
#define OUTPUT_TIMESTAMP 0x20
#define OUTPUT_RAW_TIMESTAMP 0x40
#define OUTPUT_PORCELAIN 0x80
#define OUTPUT_LINE_PORCELAIN 0x100
#define OUTPUT_NO_AUTHOR 0x200
#define OUTPUT_WEIGHTED 0x400
#define OUTPUT_SHOW_CODE 0x800
#define OUTPUT_ONE_LINE 0x1000
#define OUTPUT_CHARACTER_AUTHORSHIP 0x2000
#define OUTPUT_LINE_SCORE 0x4000
#define OUTPUT_SINGLE_AUTHOR 0x8000
#define OUTPUT_TOTAL_COUNT 0x10000

#define DIFF_WHITESPACE 0x1

/************************   Parsing Options Code *********************************/

static char author_usage[] = "git author [options] [--] <file>";

static const char* const builtin_author_usage[] = {
        author_usage,
	NULL
};

static unsigned long up_line = 0;
static unsigned long down_line = 0;
static char * range_buf = NULL;
static int abbrev = -1;
static int output_format = 0;
static enum date_mode author_date_mode = DATE_ISO8601;
static int diff_opt = 0;
double leven_score_threshold = 0.4;
double range_score_threshold = 0.5;
int max_iteration = 2;
const char* line_token_type = "token";


/* Handle one part of -L options
 * range_buf: the current position of the argument string after -L
 * code: the file content
 * total_line: total number of the file
 * start: the previously parsed line number 
 * cur : the currently parsed line number
 * return value: the place where this time of pasrsing ends
 */
char * parse_line_number(char* range_buf, char **code, int total_line, unsigned long start, unsigned long *cur) {   
    char *next;
    if (*range_buf == '+' || *range_buf == '-'){
        if (start == 1) return range_buf;
	unsigned long delta = strtoul(range_buf + 1, &next, 10);
	if (*range_buf == '+') {
	    *cur = start + delta - 2;
	    if (*cur > total_line) *cur = total_line;
	}
	else {
	    if (start > delta) 
	        *cur = start - delta;
	    else
	        *cur = 1;		
	}
	return next;
    }

    *cur = strtoul(range_buf, &next, 10);
    if (next != range_buf) return next;

    if (*range_buf != '/') return range_buf;

    for (next = range_buf+1; *next && *next != '/'; ++next){
        if (*next == '\\')
	    ++next;
    }

    if (*next !=  '/') return range_buf;
    *next = 0;

    int reg_error;
    regex_t regexp;
    regmatch_t match[1];
    
    if (!(reg_error = regcomp(&regexp, range_buf + 1, REG_NEWLINE)) &&
        !(reg_error = regexec(&regexp, code[start], 1, match, 0))) {
	    const char *cp = code[start] + match[0].rm_so;
	    while (start++ <= total_line) {
		if (code[start] <= cp && cp < code[start+1]) break;
	    }
	    *cur = start;
	    regfree(&regexp);
	    *next++ = '/';
	    return next;
    }
    else {
        char errbuf[1024];
	regerror(reg_error, &regexp, errbuf, 1024);
	die("-L parameter '%s': %s", range_buf + 1, errbuf);
    }
}


/* Split the code into multiple lines.
 * code : code content in a char array
 * total_line: total line number
 * size : the length of the code array
 * return value: the two D array version of the code
 */
char ** split_into_lines(char *code, int total_line, unsigned long size){
   char **lines = (char **) xcalloc(total_line + 2, sizeof(char*));
   int i;
   lines[1] = code;
   for (i = 2; i <= total_line; ++i) {
       lines[i] = lines[i - 1];
       while (*lines[i] != '\n') ++lines[i];
       ++lines[i];
   }
   lines[total_line + 1] = code + size;
   return lines;
}

/* Handle the -L option
 * code : code content in a char array
 * total_line: the total line number
 * size : the length of the code array
 */
void parse_range_option(char *code, int total_line, unsigned long size){

   char *next;
   char **lines = split_into_lines(code, total_line, size);

   next = parse_line_number(range_buf, lines, total_line, 1, &up_line);
   if (*next == ',')
       next = parse_line_number(next + 1, lines, total_line, up_line + 1, &down_line);
   if (down_line < up_line) {
       unsigned long tmp;
       tmp = down_line;
       down_line = up_line;
       up_line = tmp;
   }
   if (*next)
       usage(author_usage);       
   free(lines);
}

void get_head_sha1(unsigned char *sha1) {
    FILE *f;
    char fileName[50];
    char branch[50];
    char hex[50];    

    f = fopen(".git/HEAD","r");  
    fscanf(f, "%s", hex);
    int headIsBranch = (fscanf(f, "%s", branch) != EOF);
    fclose(f);
    if (headIsBranch) {
        sprintf(fileName, ".git/%s", branch);
        f = fopen(fileName, "r");
        fscanf(f, "%s", hex);
        fclose(f);
    }

    get_sha1_hex(hex, sha1);
}

void parse_left_argument(int argc, const char **argv, unsigned char* start_commit_sha1, char *file_name){
    int dashdash = -1;
    int i;
    
    for (i = 1; i < argc; ++i) {
        if (!strcmp(argv[i], "--")) {
	    dashdash = i;
	    break;
	}
    }

    if (dashdash == -1 && argc == 2) {
       // Use curernt head as the starting point
       get_head_sha1(start_commit_sha1);
       strcat(file_name, argv[1]);       
    } else {
        if (dashdash == -1 && argc == 3){
	    // argument order: author <rev> <file>
	    strcat(file_name, argv[2]);
	} else if (argc == 4 && dashdash == 2){       
	    // argument: author <rev> -- <file>
	    strcat(file_name, argv[3]);
	} else if (argc == 4 && dashdash == 1){
	    // argument: author -- <file> <rev>
	    strcat(file_name, argv[2]);
	    argv[2] = argv[1];
	    argv[1] = argv[3];
	} else usage(author_usage);
	
	--argc;
	argv[argc] = NULL;

	

	struct rev_info revs;
	init_revisions(&revs, NULL);
	setup_revisions(argc, argv, &revs, NULL);
	prepare_revision_walk(&revs);
	
	memcpy(start_commit_sha1, get_revision(&revs)->object.sha1, 20);  
    }
    
}
/************** standard callback function for git parsing API ***************/

int author_range_callback(const struct option *opt, const char * arg, int unset){

    const char ** value = opt->value;
    if (!arg)
        return -1;
    if (*value)
        die("More than one range option given");
    *value = arg;
    return 0;
}

int author_score_callback(const struct option *opt, const char * arg, int unset){
    char * next;
    double *score = opt->value;
    *score = strtod(arg, &next);
    if (*next) return -1;
    return 0;

}

int author_token_callback(const struct option *opt, const char *arg, int unset){ 
    const char * line_token_type = opt->value;
    line_token_type = arg;
    return 0;
}

/*************** The full list of options *********************************/

static struct option builtin_author_options[] = {
//		OPT_BOOLEAN(0, "incremental", &incremental, "Show blame entries as we find them, incrementally"),
//		OPT_BOOLEAN('b', NULL, &blank_boundary, "Show blank SHA-1 for boundary commits (Default: off)"),
//		OPT_BOOLEAN(0, "root", &show_root, "Do not treat root commits as boundaries (Default: off)"),
//		OPT_BOOLEAN(0, "show-stats", &show_stats, "Show work cost statistics"),
//		OPT_BIT(0, "score-debug", &output_format, "Show output score for blame entries", OUTPUT_SHOW_SCORE),
		OPT_BIT('f', "show-path", &output_format, "Show original filename (Default: auto)", OUTPUT_SHOW_PATH),
		OPT_BIT('n', "show-number", &output_format, "Show original linenumber (Default: off)", OUTPUT_SHOW_NUMBER),
		OPT_BIT('c', "show-code", &output_format, "Show the corresponding line for each commit (Default: off)", OUTPUT_SHOW_CODE),		
		OPT_BIT('p', "porcelain", &output_format, "Show in a format designed for machine parsing", OUTPUT_PORCELAIN),
		OPT_BIT(0, "line-porcelain", &output_format, "Show porcelain format with per-line commit information", OUTPUT_PORCELAIN|OUTPUT_LINE_PORCELAIN),
//		OPT_BIT('c', NULL, &output_format, "Use the same output mode as git-annotate (Default: off)", OUTPUT_ANNOTATE_COMPAT),
		OPT_BIT('t', "time-stamp", &output_format, "Show timestamp (Default: off)", OUTPUT_TIMESTAMP),
		OPT_BIT(0, "raw-stamp", &output_format, "Show raw timestamp (Default: off)", OUTPUT_RAW_TIMESTAMP),
		OPT_BIT('l', NULL, &output_format, "Show long commit SHA1 (Default: off)", OUTPUT_LONG_SHA1),
		OPT_BIT('s', "no-name", &output_format, "Suppress author name (Default: off)", OUTPUT_NO_AUTHOR),
		OPT_BIT('e', "show-email", &output_format, "Show author email instead of name (Default: off)", OUTPUT_SHOW_EMAIL),
		OPT_BIT('W', "character-authorship", &output_format, "Show weighted contribution for each commit", OUTPUT_WEIGHTED),
		OPT_BIT(0, "line-score", &output_format, "Print the line score", OUTPUT_LINE_SCORE),

		OPT_BIT(0, "one-line", &output_format, "Print all commits in one line", OUTPUT_ONE_LINE),
		OPT_BIT(0, "single-author", &output_format, "Only print the author with the most contribution",  OUTPUT_SINGLE_AUTHOR), 
		OPT_BIT(0, "total-count", &output_format, "Print the total number of commits and the total number of author", OUTPUT_TOTAL_COUNT),
//		OPT_BIT(0, "character-authorship", &output_format, " Print code in character authorship", OUTPUT_CHARACTER_AUTHORSHIP),
//		OPT_BIT('s', "show-strcuture", &output_format, "Show structural authorship (Default: off)", OUTPUT_STRUCTURE),
//		OPT_BIT('w', NULL, &diff_opts, "Consider whitespace differences", DIFF_WHITESPACE),
//		OPT_BIT(0, "minimal", &xdl_opts, "Spend extra cycles to find better match", XDF_NEED_MINIMAL),
//		OPT_STRING('S', NULL, &revs_file, "file", "Use revisions from <file> instead of calling git-rev-list"),
//		OPT_STRING(0, "contents", &contents_from, "file", "Use <file>'s contents as the final image"),
//		{ OPTION_CALLBACK, 'C', NULL, &opt, "score", "Find line copies within and across files", PARSE_OPT_OPTARG, blame_copy_callback },
//		{ OPTION_CALLBACK, 'M', NULL, &opt, "score", "Find line movements within and across files", PARSE_OPT_OPTARG, blame_move_callback },
		OPT_CALLBACK('L', "range", &range_buf, "n,m", "Process only line range n,m, counting from 1", author_range_callback),
		OPT_CALLBACK(0, "line-score", &leven_score_threshold, "score", "Levenshtein distance threshold for matching lines", author_score_callback),
		OPT_CALLBACK(0, "range-score", &range_score_threshold, "score", "Cosine range score threshold for matching code chunk", author_score_callback),
		OPT_CALLBACK(0, "line-token", &line_token_type, "token", "Token Type", author_token_callback),

		OPT__ABBREV(&abbrev),
		OPT_END()

};

/********************** Memory ********************************/


/* never freed;
 * my_memory_ldiff_used for commit info, commit hash
 */
#define COMMIT_MEMORY_LIMIT (1 << 29)
char my_memory_commit[COMMIT_MEMORY_LIMIT];
int my_memory_commit_used = 0;

void * my_allocate_commit(int num, int size){
    static char* cur = my_memory_commit;
    char* p = cur;
    cur += num * size;
    my_memory_commit_used += num *size;
    
    if (my_memory_commit_used > COMMIT_MEMORY_LIMIT){
        fprintf(stderr, "Exceed my_memory_commit Limit!!\n");
    }
    return p;
}

/* my_memory_ldiff_used for each round of ldiff
 * freed after a round of ldiff
 */
#define LDIFF_MEMORY_LIMIT (1 << 28)
char my_memory_ldiff[LDIFF_MEMORY_LIMIT];
int my_memory_ldiff_used = 0;
void * my_allocate_ldiff(int num, int size){
    int cur = my_memory_ldiff_used;
    my_memory_ldiff_used += num *size;
    if (my_memory_ldiff_used > LDIFF_MEMORY_LIMIT){
        fprintf(stderr, "Exceed my_memory_ldiff Limit!!\n");
	exit(0);
    }
    return my_memory_ldiff + cur;
}

/******************************** Global Data Structure ******************************/

/* The commit_hash_list is for two purposes.
 * 1. the hash table entry for each commit.
 *    Hash key is the sha1 string.
 * 2. the commit info representing this commit,
 *    with the author of the commit, and sha1 hash.
 */
struct commit_hash_list {
    unsigned char sha1[20];
    char *author_name;
    char *email;
    unsigned long author_time;
    char *author_tz;
    char *cur_path;    
    int total;
    int *origin;
    int *next_line;
    struct commit_hash_list *next;

    int outputed;
};


/* string_hash_list is my_memory_ldiff_used for a string hash map
 * Key is the string; Value is the frequency of the string
 */
struct string_hash_list {
    double f;
    char * string;
    int len;
    struct string_hash_list* next;
};

/* commit_info_list is a linked list entry to store line info.
 * The line info of a line is a linked list.
 * Each entry points to the corresponding commit, which is a commit_hash_list
 */
struct commit_info_list {
    int line_number;
    char* path;
    char* code;
    struct commit_hash_list * info;
    struct commit_info_list * next;
};

/* The code_hunk_list abstract a continous chunk of code.
 * The first code_hunk_list node is a head node. 
 */
struct code_hunk_list {
    int total; // for the head node, it is the length of the list; ow is the total number of the lines
    int start; // the line number of the first line in the code hunk
    int *len;
    char **code;
    char ***token_begin;
    char ***token_end;
    int *token_total;
    struct code_hunk_list *next;
};

/* change_set represents a linked list entry for two lines of code
 * that are matched as changed. from_code is in the parent commit;
 * to_code is corresponding line in the child commit.
 */
struct change_set {
    int from;    
    int to;
    char *from_code;
    char *to_code;
    struct change_set *next;
};

/* delta_set is ldiff intermediate and 
 * final computation result my_memory_ldiff_used in ldiff algorithms
 */
struct delta_set {
    struct code_hunk_list* added;
    struct code_hunk_list* deleted;
    struct change_set *changed;
};

/* hunk_pair is a potential pair of matching code hunk in ldiff. 
 * add is the index in line_transfer for a code hunk from the child commit;
 * del is the index in line_transfer for a code hunk from the parent commit.
 */
struct hunk_pair {
    int add, del;
    double score;
};

/* a pair of matched code.
 * from is the line number in the parent commit;
 * to is the line number in the child commit
 */
struct change_pair {
    int from;
    int to;
    int is_move;
};

/* line_transfer is the final ldiff result my_memory_ldiff_used for transfering line info.
 * add is the array storing all line numbers added in the child commit in increasing order;
 * del is the array storing all line numbers deleted in the parent commit in increasing order;
 * chg_from is the array storing all the line numbers changed in the parent commit in increasing order;
 * chg is the array storing all changing pairs in increasing order of the line number in the child commit.
 */
struct line_transfer {
    int *add;
    int *del;
    int *chg_from;
    struct change_pair *chg;
    int add_total;
    int del_total;
    int chg_total;
    int add_size;
    int del_size;
    int chg_size;
};


/****************************** Global Variables ***************************/

int debug = 0;
struct commit* queue[500000];
int head, tail;
double* (*line_similarity_score) (struct code_hunk_list * , struct code_hunk_list*);
struct hash_table commit_hash_table;
int total_line_in_start;
/**************************  Data Structure Related Functions *****************************/

void push_int_back(int **vector_ptr, int *total_ptr, int *size_ptr, int v){
    if (*total_ptr == *size_ptr) {
        int new_size = (*size_ptr + 16) * 3 / 2;
        int *new_memory = (int*) xcalloc(new_size, sizeof(int));
	memcpy(new_memory, *vector_ptr, *size_ptr * sizeof(int));
	if (*vector_ptr) free(*vector_ptr);
	*vector_ptr = new_memory;
	*size_ptr = new_size;
    }
    (*vector_ptr)[*total_ptr] = v;
    ++(*total_ptr);
}
void push_chg_back(struct change_pair **vector_ptr, int *total_ptr, int *size_ptr, int v1, int v2, int is_move){
    if (*total_ptr == *size_ptr) {
        int new_size = (*size_ptr + 16) * 3 / 2;
        struct change_pair *new_memory = (struct change_pair*) xcalloc(new_size, sizeof(struct change_pair));
	memcpy(new_memory, *vector_ptr, *size_ptr * sizeof(struct change_pair));
	if (*vector_ptr) free(*vector_ptr);
	*vector_ptr = new_memory;
	*size_ptr = new_size;
    }
    (*vector_ptr)[*total_ptr].from = v1;
    (*vector_ptr)[*total_ptr].to = v2;
    (*vector_ptr)[*total_ptr].is_move = is_move;

    ++(*total_ptr);
}

void insert_commit_info_list(struct commit_info_list** info, int origin_line, int cur_line, 
                             struct commit_hash_list* c, char **lines){
    struct commit_info_list * new_entry = (struct commit_info_list*) my_allocate_commit(1, sizeof(struct commit_info_list));
    new_entry->next = info[origin_line];
    new_entry->info = c;
    new_entry->line_number = cur_line;
    new_entry->path = c->cur_path;
    int len = lines[cur_line + 1] - lines[cur_line];
    if (lines[cur_line][len - 1] == '\n') --len;
    new_entry->code = (char *) my_allocate_commit( len + 1, sizeof(char));
    strncpy(new_entry->code, lines[cur_line], len);
    new_entry->code[len] = 0;
    info[origin_line] = new_entry;
}

void insert_line_transfer(struct line_transfer *ret, struct delta_set *diff){
    struct code_hunk_list *h;
    struct change_set* cs;
    int i, is_move;
    for (h = diff->added->next; h != NULL; h = h->next)
        for (i = 0; i < h->total; ++i)
	    push_int_back(&ret->add, &ret->add_total, &ret->add_size, i + h->start);
    for (h = diff->deleted->next; h != NULL; h = h->next)
        for (i = 0; i < h->total; ++i)
	    push_int_back(&ret->del, &ret->del_total, &ret->del_size, i + h->start);
    int tmp_total = ret->chg_total;
    int tmp_size = ret->chg_size;
    for (cs = diff->changed->next; cs != NULL; cs = cs->next) {
        if (!strcmp(cs->from_code, cs->to_code)) is_move = 1; else is_move = 0;
        push_chg_back(&ret->chg, &ret->chg_total, &ret->chg_size, cs->from, cs->to, is_move);
	push_int_back(&ret->chg_from, &tmp_total, &tmp_size, cs->from);
    }
}

void insert_code_hunk_list(struct code_hunk_list* hunk_list, struct code_hunk_list* new_hunk){
    new_hunk->next = hunk_list->next;
    hunk_list->next = new_hunk;
    ++hunk_list->total;
}

void print_code_hunk_list(struct code_hunk_list* h, char *msg) {
    printf("%s\n", msg);
    printf("total hunk %d\n", h->total);
    while ( (h=h->next) != NULL){
        int i;
        printf("starting on line %d, has %d lines of code\n", h->start,h->total);
	for (i = 0; i < h->total; ++i)
	    printf("%d %s\n", h->len[i], h->code[i]);

    }
    
}

void print_delta_set(struct delta_set* diff, char *msg) {
    struct change_set* p = diff->changed;
    printf("%s\n",msg);
    print_code_hunk_list(diff->added , "add");
    print_code_hunk_list(diff->deleted, "del");
    if (p != NULL) p = p->next;
    printf("There are %d changes\n", diff->changed->from);
    while (p != NULL){    
        printf("from line %d: %s\n", p->from, p->from_code);
	printf("to line %d: %s\n", p->to, p->to_code);
	p = p->next;
    }


}

void print_string_hash(struct hash_table *ht, char *msg){
    dprintf("%s\n", msg);
    int i;
    for (i = 0; i < ht->size; ++i){
        struct string_hash_list * hl = (struct string_hash_list*)(ht->array[i].ptr);
	if (hl != NULL) hl = hl->next;
	while (hl != NULL){
	    dprintf("%s %.0lf\n", hl->string, hl->f);
	    hl=hl->next;
	}
    }
}

void print_line_transfer(struct line_transfer *l){
    int i;
    dprintf("line transfer add:\n");
    for (i = 0; i < l->add_total; ++i)
        dprintf("%d ", l->add[i]);
    dprintf("\n");

    dprintf("line transfer del:\n");
    for (i = 0; i < l->del_total; ++i)
        dprintf("%d ", l->del[i]);
    dprintf("\n");

    dprintf("line transfer chg:\n");
    for (i = 0; i < l->chg_total; ++i)
        dprintf("(%d,%d) ", l->chg[i].to, l->chg[i].from);
    dprintf("\n");
}

void free_code_hunk_list(struct code_hunk_list* h){
    struct code_hunk_list* next=h->next;
    int i;
    free(h);
    while (next != NULL){
        h = next;
	next = next->next;
	for (i = 0; i < h->total; ++i)
	    free(h->code[i]);
	free(h->code);
	free(h);
    }	
	
}

void free_line_transfer(struct line_transfer* lt){
    free(lt->add);
    free(lt->del);
    free(lt->chg);
    free(lt->chg_from);
    free(lt);
}

void free_commit_info_list(struct commit_info_list *cil){
    struct commit_info_list *next;
    while (cil != NULL){
        next = cil->next;
	free(cil);
	cil = next;
    }
}

int dcmp(double a, double b){
    if (a-b > 1e-8) return 1;
    else if (a-b < -1e-8) return -1;
    else return 0;
}

int hunk_pair_cmp(const void *a, const void *b){
    return dcmp(((const struct hunk_pair*)a)->score,((const struct hunk_pair*)b)->score);
}

int cmp_int(const void *a, const void *b){
    return *((const int*)a) - *((const int*)b);
}

int cmp_change_pair(const void *a, const void *b){
    return ((const struct change_set*)a)->to - ((const struct change_set*)b)->to;
}




/***************************** Hash Related Stuff **************************/

// One-at-a-Time hash
unsigned hash_function ( void *key, int len) {
    unsigned char *p = key;
    unsigned h = 0;
    int i;
    for ( i = 0; i < len; i++ ) {
        h += p[i];
	h += ( h << 10 );
	h ^= ( h >> 6 );
    }
    h += ( h << 3 );
    h ^= ( h >> 11 );
    h += ( h << 15 );
    return h;
}
static struct commit_hash_list* commit_hash_lookup(unsigned char *sha1){
    unsigned int hash = hash_function(sha1, 20);
    struct commit_hash_list *hl = (struct commit_hash_list*) lookup_hash(hash, &commit_hash_table);
    if (hl == NULL) return NULL;
    while ( (hl=hl->next) != NULL) {
        if (!memcmp(sha1, hl->sha1,20)){
	    return hl;
	}
    }
    return NULL;
}

static struct commit_hash_list* commit_hash_insert(unsigned char *sha1){
    unsigned int hash = hash_function(sha1, 20);
    struct commit_hash_list *newEntry;
    struct commit_hash_list *hl = (struct commit_hash_list*) lookup_hash(hash,&commit_hash_table);
    if (hl == NULL){
        hl = (struct commit_hash_list*)my_allocate_commit(1,sizeof(struct commit_hash_list));
	hl->cur_path = NULL;
	hl->author_name = NULL;
	insert_hash(hash, hl, &commit_hash_table);	
    }
    
    newEntry = (struct commit_hash_list*)my_allocate_commit(1,sizeof(struct commit_hash_list));
    memcpy(newEntry->sha1,sha1,20);
    newEntry->cur_path = NULL;
    newEntry->origin = NULL;
    newEntry->author_name = NULL;
    newEntry->next = hl->next;
    hl->next = newEntry;    
    return newEntry;
}

static struct string_hash_list* string_hash_lookup(struct hash_table* ht, char *key, int len){
    unsigned int hash = hash_function(key, len);
    struct string_hash_list *hl = (struct string_hash_list*) lookup_hash(hash, ht);
    if (hl == NULL) return NULL;
    while ( (hl=hl->next) != NULL) {
        if (!strncmp(key, hl->string, len)){
	    return hl;
	}
    }
    return NULL;
}

static struct string_hash_list* string_hash_insert(struct hash_table* ht, char *key, int len){
    unsigned int hash = hash_function(key, len);
    struct string_hash_list *newEntry;
    struct string_hash_list *hl = (struct string_hash_list*) lookup_hash(hash,ht);
    if (hl == NULL){
        hl = (struct string_hash_list*) my_allocate_ldiff(1,sizeof(struct string_hash_list));
	hl->string = NULL;
	hl->f = 0;
	hl->next = NULL;
	insert_hash(hash, hl, ht);	
    }
    
    newEntry = (struct string_hash_list*) my_allocate_ldiff(1,sizeof(struct string_hash_list));
    newEntry->len = len;
    newEntry->string = (char*) my_allocate_ldiff(len+1, sizeof(char));
    newEntry->f = 0;
    strncpy(newEntry->string, key, len);
    newEntry->string[len] = 0;
    newEntry->next = hl->next;
    hl->next = newEntry;    
    return newEntry;
}

/*static void StringHashClean(struct hash_table* ht) {
    int i;
    for (i = 0; i < ht->size; ++i){
        struct string_hash_list * hl = (struct string_hash_list*)(ht->array[i].ptr);
	struct string_hash_list * next = hl->next;
	while (next != NULL){
	    hl = next;
	    next = next->next;
	    free(hl->string);
	    free(hl);
	}
	free(ht->array[i].ptr);	
    }
    free(ht->array);

}
*/


/********************************** Ldiff Functions ***************************************/
char * next_character(char *cur_posi, char c){
    while (*cur_posi && *cur_posi != c) ++cur_posi;
    return cur_posi;
}

int is_operator(char ch){
    if (ch == '=' || ch == '+' || ch == '-') return 1;
    if (ch == '!' || ch == '/' || ch == '*') return 1;
    if (ch == '%' || ch == '<' || ch == '>') return 1;
    if (ch == '&' || ch == '|' || ch == '^') return 1;
    if (ch == '~') return 1;
    return 0;
}

void count_frequency(struct hash_table* tf, struct hash_table *ht, struct code_hunk_list *hunk){
    struct string_hash_list* posi, *lookup;
    char *cur, *next;
    int i,j;
    init_hash(tf);
    hunk->token_begin = (char ***) my_allocate_ldiff(hunk->total, sizeof(char**));
    hunk->token_end = (char ***) my_allocate_ldiff(hunk->total, sizeof(char**));
    hunk->token_total = (int *) my_allocate_ldiff(hunk->total, sizeof(int));
    for (i = 0; i < hunk->total; ++i) {
        cur = hunk->code[i];
	hunk->token_total[i] = 0;
	while (*cur) {
	    while (*cur && !(isalnum(*cur) || *cur == '_' || is_operator(*cur))) ++cur;
	    next = cur;
	    if (is_operator(*next))
	        while (*next && is_operator(*next)) ++next;
	    else
	        while (*next && (isalnum(*next) || *next == '_')) ++next;
	    if (next != cur) {
	        ++hunk->token_total[i];
		posi = (struct string_hash_list*) string_hash_lookup(tf, cur, next - cur);	    
		if (posi == NULL) {
		    posi = (struct string_hash_list*) string_hash_insert(tf, cur, next - cur);		
		}
		++posi->f;
	    }
	    cur = next;
	}
	cur = hunk->code[i];
	hunk->token_begin[i] = (char**) my_allocate_ldiff(hunk->token_total[i], sizeof(char*));
	hunk->token_end[i] = (char**) my_allocate_ldiff(hunk->token_total[i], sizeof(char*));
	j = 0;
	while (*cur) {
	    while (*cur && !(isalnum(*cur) || *cur == '_' || is_operator(*cur))) ++cur;
	    next = cur;
	    if (is_operator(*next))
	        while (*next && is_operator(*next)) ++next;
	    else
	        while (*next && (isalnum(*next) || *next == '_')) ++next;	    
	    if (next != cur){
	        hunk->token_begin[i][j] = cur;
		hunk->token_end[i][j] = next;
		++j;
	    }
	    cur = next;
	}
    }

    for (i = 0; i < tf->size; ++i){
        posi = (struct string_hash_list*)(tf->array[i].ptr);
	if (posi == NULL) continue;
	while ( (posi = posi->next) != NULL ){
	    int len = strlen(posi->string);
	    lookup = (struct string_hash_list*) string_hash_lookup(ht, posi->string, len);
	    if (lookup == NULL){
	        lookup = (struct string_hash_list*) string_hash_insert(ht, posi->string,len);
	    }
	    ++lookup->f;
	}
    }

}

void normalize(struct hash_table* ht){
    struct string_hash_list * l;
    int i;
    int sum = 0;
    for (i = 0; i < ht->size; ++i){
        l = (struct string_hash_list*) (ht->array[i].ptr);
	if (l == NULL) continue;
	while ((l=l->next) != NULL) {
	    sum += (int)(l->f);
	}
    }
    for (i = 0; i < ht->size; ++i){
        l = (struct string_hash_list*) (ht->array[i].ptr);
	if (l == NULL) continue;
	while ((l=l->next) != NULL) {
	    l->f = l->f / sum;
	}
    }
}

double range_similarity_score(struct hash_table *at, struct hash_table *dt, struct hash_table *df, int total) {
    int i;
    double norm1, norm2, inner, tmp;
    struct string_hash_list *l, *lookup;
    if (at->size == 0 && dt->size == 0) return 1;
    if (at->size == 0 || dt->size == 0) return 0;

    norm1 = norm2 = inner = 0;

    for (i = 0; i < at->size; ++i) {
        l = (struct string_hash_list*) (at->array[i].ptr);
	if (l == NULL) continue;
	while ( (l=l->next) != NULL ){
	    lookup = string_hash_lookup(df, l->string, l->len);
	    tmp = l->f * log(total/(0.5+lookup->f));
	    norm1 += tmp * tmp;
	}
    }

    for (i = 0; i < dt->size; ++i) {
        l = (struct string_hash_list*) (dt->array[i].ptr);
	if (l == NULL) continue;
	while ( (l=l->next) != NULL ){
	    lookup = string_hash_lookup(df, l->string, l->len);
	    tmp = l->f * log(total/(0.5+lookup->f));
	    norm2 += tmp * tmp;

            tmp = log(total/(0.5+lookup->f));
	    lookup = string_hash_lookup(at, l->string, l->len);
	    if (lookup != NULL){
	        inner += l->f * lookup->f * tmp * tmp; 
	    }
	}
    }

    return inner / (sqrt(norm1) * sqrt(norm2));
}

double * line_similarity_char_score(struct code_hunk_list* add, struct code_hunk_list* del){
    int i,j;
    double * score = (double*) my_allocate_ldiff(add->total * del->total, sizeof(double));
    for (i = 0; i < add->total; ++i)
        for (j = 0; j < del->total; ++j){
	    int max_len;
	    if (add->len[i] > del->len[j])
	        max_len = add->len[i];
	    else
	        max_len = del->len[j];
	    if (max_len == 0)
	        score[i * del->total + j] = 0;
	    else {
	        int leven_dis = levenshtein(add->code[i], del->code[j], 10000, 1,1,1);		
		score[i * del->total + j] = (max_len - leven_dis) / (double)(max_len);	       
	    }
	}
    return score;
}

int token_cmp(const char *t1_begin, const char *t1_end, const char *t2_begin, const char *t2_end){
    if (t1_end - t1_begin != t2_end - t2_begin) return 1;
    return strncmp(t1_begin, t2_begin, t2_end - t2_begin) != 0;
}

int token_levenshtein(char **token1_begin, char **token1_end, int len1,
                      char **token2_begin, char **token2_end, int len2,
		      int w, int s, int a, int d)
{
	int *row0 = xmalloc(sizeof(int) * (len2 + 1));
	int *row1 = xmalloc(sizeof(int) * (len2 + 1));
	int *row2 = xmalloc(sizeof(int) * (len2 + 1));
	int i, j;

	for (j = 0; j <= len2; j++)
		row1[j] = j * a;
	for (i = 0; i < len1; i++) {
		int *dummy;

		row2[0] = (i + 1) * d;
		for (j = 0; j < len2; j++) {
			/* substitution */
			row2[j + 1] = row1[j] + s * token_cmp(token1_begin[i], token1_end[i], token2_begin[j], token2_end[j]);
			/* swap */
			if (i > 0 && j > 0 && 
			    token_cmp(token1_begin[i - 1], token1_end[i - 1], token2_begin[j], token2_end[j]) == 0 &&
			    token_cmp(token1_begin[i], token1_end[i], token2_begin[j - 1], token2_end[j - 1]) == 0 &&
			    row2[j + 1] > row0[j - 1] + w)
				row2[j + 1] = row0[j - 1] + w;
			/* deletion */
			if (row2[j + 1] > row1[j + 1] + d)
				row2[j + 1] = row1[j + 1] + d;
			/* insertion */
			if (row2[j + 1] > row2[j] + a)
				row2[j + 1] = row2[j] + a;
		}

		dummy = row0;
		row0 = row1;
		row1 = row2;
		row2 = dummy;
	}

	i = row1[len2];
	free(row0);
	free(row1);
	free(row2);

	return i;
}
double * line_similarity_token_score(struct code_hunk_list * add, struct code_hunk_list* del){
    int i,j;
    double * score = (double*) my_allocate_ldiff(add->total * del->total, sizeof(double));
    for (i = 0; i < add->total; ++i)
        for (j = 0; j < del->total; ++j){
	    int max_len;
	    if (add->token_total[i] > del->token_total[j])
	        max_len = add->token_total[i];
	    else
	        max_len = del->token_total[j];
	    if (max_len == 0)
	        score[i * del->total + j] = 0;
	    else {
	        int leven_dis = token_levenshtein(add->token_begin[i], add->token_end[i], add->token_total[i],
		                                  del->token_begin[j], del->token_end[j], del->token_total[j],
						  10000, 1,1,1);		
		score[i * del->total + j] = (max_len - leven_dis) / (double)(max_len);	       
	    }
	}
    return score;
}
struct code_hunk_list* create_portion_code_hunk(int from, int to, struct code_hunk_list *hunk){
    int i;
    struct code_hunk_list* new_hunk = (struct code_hunk_list*) my_allocate_ldiff(1, sizeof(struct code_hunk_list));
    new_hunk->start = hunk->start + from;
    new_hunk->total = to - from;
    new_hunk->code = (char**) my_allocate_ldiff(new_hunk->total, sizeof(char*));
    new_hunk->len = (int*) my_allocate_ldiff(new_hunk->total, sizeof(int));
    for (i = 0; i < new_hunk->total; ++i) {
        new_hunk->code[i] = hunk->code[from + i];
	new_hunk->len[i] = hunk->len[from + i];
    }
    return new_hunk;
}
void linear_match_in_one_hunk_pair(struct code_hunk_list* add, struct code_hunk_list *del, struct delta_set *new_diff){
    struct code_hunk_list* new_hunk;
    int i;
    for (i = 0; i < add->total && i < del->total; ++i) {
        struct change_set* new_change = (struct change_set*) my_allocate_ldiff(1 , sizeof(struct change_set));
	new_change->from_code = del->code[i];
	new_change->to_code = add->code[i];
	new_change->from = del->start + i;
	new_change->to = add->start + i;
	new_change->next = new_diff->changed->next;
	new_diff->changed->next = new_change;
	++new_diff->changed->from;
    }
    if (i < add->total) {
        new_hunk = create_portion_code_hunk(i, add->total, add);
	insert_code_hunk_list(new_diff->added, new_hunk);
    }
    if (i < del->total){
        new_hunk = create_portion_code_hunk(i, del->total, del);
	insert_code_hunk_list(new_diff->deleted, new_hunk);
    }
}



void match_in_one_hunk_pair(struct code_hunk_list* add, struct code_hunk_list *del, double *line_score, struct delta_set *new_diff){
 // free add->code, del->code in the end. Their entries will be in new_diff (for unmatched), or freed( for matched)
    int cur_left, cur_right, next_left, next_right, i, j;
    struct code_hunk_list* new_hunk;
    next_left = next_right = cur_left = cur_right = 0; 
    while (1){
	
	double max_score = -1;
	int pos_sum = 0;

	for (i = cur_left; i < add->total; ++i)
	    for (j = cur_right; j < del->total; ++j)
	        if (dcmp(line_score[i * del->total + j],max_score) > 0 || (dcmp(line_score[i * del->total + j], max_score) == 0 && pos_sum > i + j)){
		    max_score = line_score[i * del->total + j];
		    pos_sum = i + j;
		    next_left = i;
		    next_right = j;
		}

	if (dcmp(max_score, leven_score_threshold) < 0){
	    if (cur_left < add->total){
	        new_hunk = create_portion_code_hunk(cur_left, add->total, add);
		insert_code_hunk_list(new_diff->added, new_hunk);
	    }
	    if (cur_right < del->total){
	        new_hunk = create_portion_code_hunk(cur_right, del->total, del);
		insert_code_hunk_list(new_diff->deleted, new_hunk);
	    }
	    break;
	}
	else {
	    struct change_set* new_change = (struct change_set*) my_allocate_ldiff(1 , sizeof(struct change_set));
	    new_change->from_code = del->code[next_right];
	    new_change->to_code = add->code[next_left];
	    new_change->from = del->start + next_right;
	    new_change->to = add->start + next_left;
	    new_change->next = new_diff->changed->next;
	    new_diff->changed->next = new_change;
	    ++new_diff->changed->from;
	    if (cur_left < next_left) {
	        new_hunk = create_portion_code_hunk(cur_left, next_left, add);
		insert_code_hunk_list(new_diff->added, new_hunk);
		
	    }
	    if (cur_right < next_right){
	        new_hunk = create_portion_code_hunk(cur_right, next_right, del);
		insert_code_hunk_list(new_diff->deleted, new_hunk);
	    }
	    cur_left = next_left + 1;
	    cur_right = next_right + 1;
	}
    }
}

void count_document_frequency(struct hash_table*df, struct hash_table* terms, struct code_hunk_list **vector, struct code_hunk_list* hunk_list) {
    struct code_hunk_list * hunk;
    int i;
    for (hunk = hunk_list->next, i = 0; hunk != NULL; hunk = hunk->next, ++i) {
	count_frequency(terms+i, df, hunk);
	vector[i] = hunk;
	normalize(terms+i);
    }

}

struct hunk_pair* build_hunk_pair_list(struct delta_set *old_diff, int* total_pair, struct hash_table * df, 
                          struct hash_table *add_terms, struct code_hunk_list **add_vector,
			  struct hash_table *delete_terms, struct code_hunk_list **del_vector){
    int i, j, k = 0;
    struct code_hunk_list *add, *del;
    int total_docs = old_diff->added->total + old_diff->deleted->total;
    struct hunk_pair* all_pair = (struct hunk_pair*) my_allocate_ldiff( old_diff->added->total * old_diff->deleted->total, sizeof(struct hunk_pair) );
    for (add = old_diff->added->next, i = 0; add != NULL; add = add->next, ++i) {
        for (del = old_diff->deleted->next, j = 0; del != NULL; del = del->next, ++j) {
	    if (i == old_diff->added->total || j == old_diff->deleted->total) {
//	        dprintf("%d %d %d %d\n", i, old_diff->added->total, j, old_diff->deleted->total);
		exit(0);
	    }
	    all_pair[k].score = range_similarity_score(add_terms + i, delete_terms + j, df, total_docs);
	    if (all_pair[k].score > range_score_threshold) {
	        all_pair[k].add = i;
	        all_pair[k].del = j;
		++k;
	    }
	}
    }
    *total_pair = k;
    return all_pair;
}

void init_new_diff(struct delta_set *new_diff){
    new_diff->added = (struct code_hunk_list*) my_allocate_ldiff(1, sizeof(struct code_hunk_list));
    new_diff->added->next = NULL;
    new_diff->added->total = 0;
    new_diff->deleted = (struct code_hunk_list*) my_allocate_ldiff(1, sizeof(struct code_hunk_list));
    new_diff->deleted->next = NULL;
    new_diff->deleted->total = 0;
    new_diff->changed = (struct change_set *) my_allocate_ldiff(1, sizeof(struct change_set));
    new_diff->changed->next = NULL;
    new_diff->changed->from = 0;
}

void concatenate_left(struct code_hunk_list* hunk, int total_hunk, int *choosen, struct code_hunk_list **vector){
    int i;
    for (i = 0; i < total_hunk; ++i)
        if (choosen[i] == 0) {
	    vector[i]->next = hunk->next;
	    hunk->next = vector[i];
	    ++hunk->total;
	}

}

void line_match_in_hunk(struct hunk_pair* all_pair, int total_pair,
                        struct delta_set *old_diff, struct delta_set *new_diff,
			struct hash_table *add_terms, struct code_hunk_list **add_vector,
			struct hash_table *delete_terms, struct code_hunk_list **del_vector){	
    int i;
    int *add_choosen, *del_choosen;
    double *line_score;
    
    add_choosen = (int*) my_allocate_ldiff( old_diff->added->total, sizeof(int) );
    del_choosen = (int*) my_allocate_ldiff( old_diff->deleted->total, sizeof(int) );
    memset(add_choosen, 0, old_diff->added->total * sizeof(int));
    memset(del_choosen, 0, old_diff->deleted->total * sizeof(int));

    for (i = 0; i < total_pair; ++i) {
        if (add_choosen[all_pair[i].add] || del_choosen[all_pair[i].del]) continue;
        add_choosen[all_pair[i].add] = 1;
	del_choosen[all_pair[i].del] = 1;
	if (add_vector[all_pair[i].add]->len == NULL || del_vector[all_pair[i].del]->len == NULL){
	    printf("ERROR, %d %d %d %d\n", all_pair[i].add, all_pair[i].del, old_diff->added->total, old_diff->deleted->total);
	    exit(0);
	}
	if (add_vector[all_pair[i].add]->total * del_vector[all_pair[i].del]->total < 10000) {
	    dprintf("%d line pairs\n", add_vector[all_pair[i].add]->total * del_vector[all_pair[i].del]->total);
	    line_score = line_similarity_score(add_vector[all_pair[i].add], del_vector[all_pair[i].del]);
	    dprintf("IN LOOP %d: %d\n", i,my_memory_ldiff_used);
	    match_in_one_hunk_pair(add_vector[all_pair[i].add], del_vector[all_pair[i].del], line_score, new_diff);
//	    free(line_score);
	}
	else { 
//	    printf("LINEAR MATCH\n");
	    linear_match_in_one_hunk_pair(add_vector[all_pair[i].add], del_vector[all_pair[i].del], new_diff);
	}
    }

    concatenate_left(new_diff->added, old_diff->added->total, add_choosen, add_vector);
    concatenate_left(new_diff->deleted, old_diff->deleted->total, del_choosen, del_vector);
     
    struct change_set * chg = old_diff->changed->next, *next;	
    while (chg != NULL){
        ++new_diff->changed->from;
	next = chg->next;
	chg->next = new_diff->changed->next;
	new_diff->changed->next = chg;
	chg = next;
    }

}
void match(struct delta_set *old_diff, struct delta_set *new_diff){
    struct hash_table df;    
    struct hash_table *add_terms, *delete_terms;
    struct code_hunk_list **add_vector, **del_vector;
    int total_pair;
    init_hash(&df);

    add_terms = (struct hash_table*) my_allocate_ldiff(old_diff->added->total, sizeof(struct hash_table));
    add_vector = (struct code_hunk_list**) my_allocate_ldiff(old_diff->added->total, sizeof(struct code_hunk_list*));
    count_document_frequency(&df, add_terms, add_vector, old_diff->added);


    delete_terms = (struct hash_table*) my_allocate_ldiff(old_diff->deleted->total, sizeof(struct hash_table));
    del_vector = (struct code_hunk_list**) my_allocate_ldiff(old_diff->deleted->total, sizeof(struct code_hunk_list*));
    count_document_frequency(&df, delete_terms, del_vector, old_diff->deleted);

    normalize(&df);

    struct hunk_pair* all_pair;
    all_pair = build_hunk_pair_list(old_diff, &total_pair, &df, add_terms, add_vector, delete_terms, del_vector);

    qsort(all_pair, total_pair, sizeof(struct hunk_pair), hunk_pair_cmp);

    init_new_diff(new_diff);

    line_match_in_hunk(all_pair, total_pair, old_diff, new_diff, add_terms, add_vector, delete_terms, del_vector);   
}

struct delta_set* ldiff(struct code_hunk_list* added_hunk, struct code_hunk_list *deleted_hunk) {
    struct delta_set old_diff;
    struct delta_set* new_diff = my_allocate_ldiff(1, sizeof(struct delta_set));
    int i;
    old_diff.added = added_hunk;
    old_diff.deleted = deleted_hunk;
    old_diff.changed = my_allocate_ldiff(1, sizeof(struct change_set));
    old_diff.changed->from = 0;
    old_diff.changed->next = NULL;

    for (i = 0; i < max_iteration; ++i) {
        match(&old_diff, new_diff);
	old_diff.added = new_diff->added;
	old_diff.deleted = new_diff->deleted;
	old_diff.changed = new_diff->changed;
//	print_delta_set(new_diff, "DIFF ITERATION");

    }
    return new_diff;

}

struct code_hunk_list * build_new_code_hunk(char* cur_posi, char ** next_position) {
    char *next_posi = *next_position;
    int index = 0;
    struct code_hunk_list* new_hunk = (struct code_hunk_list*) my_allocate_ldiff(1, sizeof(struct code_hunk_list));
    new_hunk->total = 1;

    char* start;
    while (*next_posi && *(next_posi+1) == *cur_posi){
        ++new_hunk->total;
	next_posi = next_character(next_posi+1, '\n');
    }
    
    next_posi = cur_posi - 1;
    new_hunk->code = (char**) my_allocate_ldiff(new_hunk->total, sizeof(char*));
    new_hunk->len = (int*) my_allocate_ldiff(new_hunk->total, sizeof(int));
    
    while (*next_posi && *(next_posi+1) == *cur_posi){
        start = next_posi + 2;
	next_posi = next_character(start, '\n');
	if (next_posi - start + 1 > 0){
	    new_hunk->len[index] = next_posi - start;
	    new_hunk->code[index] = (char*) my_allocate_ldiff(next_posi-start+1,sizeof(char));
	    strncpy(new_hunk->code[index], start, next_posi-start);
	    new_hunk->code[index][new_hunk->len[index]] = 0;
	    ++index;
	}
	else {
	    new_hunk->code[index] = NULL;
	    new_hunk->len[index++] = 0;
	}
    }
    *next_position = next_posi;

    dprintf("%d lines of code in current hunk, start at %d, type %c\n", new_hunk->total, new_hunk->start, *cur_posi);
    dprintf("Actually process %d lines of code\n", index);
    
    return new_hunk;
}


void check_changed_lines(struct delta_set *diff){

   struct change_set * chg = diff->changed;
   if (chg == NULL) return;
   for (chg = chg->next; chg != NULL; chg = chg->next)
       if (!strcmp(chg->from_code, chg->to_code)){
	    print_delta_set(diff, "SAME CHANGED LINE!");
       }

}

struct line_transfer* parse_diff_result(char *diff_result, size_t len){
    char *cur_posi = diff_result;
    struct delta_set *diff;
    struct line_transfer *ret = (struct line_transfer*) xcalloc(1, sizeof(struct line_transfer));
    ret->add_total = ret->del_total = ret->chg_total = 0;
    ret->add_size = ret->del_size = ret->chg_size = 0;
    dprintf("DIFF RESULT:\n%s", diff_result);
    
    /* Find the position where:
     * diff --git a/AA b/BB
     * Since we are only interested in a single file,
     * there should be only one "diff --git a/" structure in the diff result
     */
    while (*cur_posi){
        if (!strncmp(cur_posi, "diff --git a/" , 13)) break;
	++cur_posi;
    }
  
    /* There are possibly multiple @@ sections:
     * @@ -{deleted code starting line number},{total line} +{added code start line number},{total line} @@
     */
    while (*cur_posi) {
        if (!strncmp(cur_posi, "@@ -",4)){	 

	    my_memory_ldiff_used = 0;	  
	    char *next_posi;
	    struct code_hunk_list * added_hunk = (struct code_hunk_list*) my_allocate_ldiff(1, sizeof(struct code_hunk_list));
	    struct code_hunk_list * deleted_hunk = (struct code_hunk_list*) my_allocate_ldiff(1, sizeof(struct code_hunk_list));   
	    int added_lineno;
	    int deleted_lineno;
	    added_hunk->next = deleted_hunk->next = NULL;
	    added_hunk->total = deleted_hunk->total = 0;

	    // Get the starting line number for added and deleted code
	    cur_posi = next_character(cur_posi, '-');
	    deleted_lineno = atoi(cur_posi+1);

	    cur_posi = next_character(cur_posi, '+');
	    added_lineno = atoi(cur_posi+1);

	    cur_posi = next_character(cur_posi, '\n') + 1;
	    while (*cur_posi && strncmp(cur_posi, "@@ -", 4)) {
	        next_posi = next_character(cur_posi, '\n');
		if (*cur_posi == '+' || *cur_posi == '-') {

		    struct code_hunk_list * code_hunk = build_new_code_hunk(cur_posi, &next_posi);
		    if (*cur_posi == '+') {
                        insert_code_hunk_list(added_hunk, code_hunk);
			code_hunk->start = added_lineno;
			added_lineno += code_hunk->total;
		    }
		    else {
                        insert_code_hunk_list(deleted_hunk, code_hunk);
			code_hunk->start = deleted_lineno;
			deleted_lineno += code_hunk->total;
		    }
		}
		else if (strncmp(cur_posi, "\\ No newline at end of file", strlen("\\ No newline at end of file"))) {
		    // this is a unchanged line
		    ++deleted_lineno;
		    ++added_lineno;
		}
		cur_posi = next_posi + 1;

	    }

	    diff = ldiff(added_hunk, deleted_hunk);
//	    check_changed_lines(diff);
            

	    insert_line_transfer(ret, diff);
	}
	else
	    ++cur_posi;
    }  
    return ret;
}



/********************************** Visiting Commits Related Functions ***************************************/

void parse_commit_info(struct commit* cur, struct commit_hash_list* cur_info){
    char buf[1024];
    char *begin = strstr(cur->buffer, "author") + 7;
    char *end = strstr(cur->buffer, "<") - 1;    
    int len = end - begin;
    if (len < 0) {
        //This is the case where the author name start with the character "<"
	//Assume the name is <ABC>
        end = strstr(begin, ">") + 1;
	len = end - begin;
    }
//    printf("CUR commit %s\n%s\nBBBB\n",sha1_to_hex(cur->object.sha1), cur->buffer);
    cur_info->author_name = (char*) my_allocate_commit( len + 1 ,  sizeof(char) );
    strncpy(cur_info->author_name, begin, len);
    cur_info->author_name[len] = 0;

    begin = end + 2;
    end = strstr(begin, ">");
    len = end - begin;
    cur_info->email = (char*) my_allocate_commit( len + 1, sizeof(char));
    strncpy(cur_info->email, begin, len);
    cur_info->email[len] = 0;

    end += 2;
    sscanf(end, "%lu %s", &cur_info->author_time, buf);
    len = strlen(buf);
    cur_info->author_tz = (char*) my_allocate_commit( len + 1, sizeof(char));
    strncpy(cur_info->author_tz, buf, len);
    cur_info->author_tz[len] = 0;
}

/* put the current head commit's hash into sha1
 */


const unsigned char* get_blob_sha1(struct tree* t, const char* path){

    struct tree_desc desc;
    struct name_entry entry;
    parse_tree(t);    
    init_tree_desc(&desc, t->buffer, t->size);
    while (tree_entry(&desc, &entry)){
        if (!strcmp(path, entry.path)){
	    return entry.sha1;
	}
	int len = strlen(entry.path);
	if (!strncmp(entry.path, path, len) && path[len] == '/') {
	    struct tree* sub_tree = lookup_tree(entry.sha1);
            return get_blob_sha1(sub_tree, path + len + 1);
	}
    
    }
    return NULL;

}

char * get_file_content(struct tree* t, const char* path, unsigned long* size_ptr){
    const unsigned char* blob_sha1 = get_blob_sha1(t, path);
    if (blob_sha1 != NULL) {
        enum object_type type;
	char * buffer = read_sha1_file(blob_sha1, &type, size_ptr);
	return buffer;
    } else {
        *size_ptr = 0;
	return NULL;
    }
}

int get_total_line_number(struct tree* t, const char* path){
    int total = 0;
    unsigned long size;
    char *buffer = get_file_content(t, path, &size);
    int i;
    for (i = 0; i < size; ++i)
        if (buffer[i] == '\n') ++total;
    if (size > 0 && buffer[size - 1] != '\n') ++total;
    if (buffer != NULL) free(buffer);
    return total; 
}

struct commit_hash_list* init_start_commit_info(unsigned char *sha1, const char *file_name){
    struct commit_hash_list * info;

    queue[0] = lookup_commit(sha1);
    parse_commit(queue[0]);
    init_hash(&commit_hash_table);

    info = commit_hash_insert(sha1);
    info->cur_path = (char*) my_allocate_commit(strlen(file_name) + 1, sizeof(char));
    strcpy(info->cur_path, file_name);
    info->total = get_total_line_number(queue[0]->tree, info->cur_path);
    if (info->total == 0) {
        printf("Cannot find file \"%s\"!!\n", file_name);
	exit(0);
    }
    dprintf("%s has %d lines\n", sha1_to_hex(sha1), info->total);
    info->origin = (int*) xcalloc(info->total + 1 + info->total + 1, sizeof(int));
    info->next_line = info->origin + info->total + 1;

    return info;
}



void prepare_parse_range_option(struct commit_hash_list* head_info){

    if (range_buf != NULL) {
        unsigned long size;
        char *code = get_file_content(queue[0]->tree, head_info->cur_path, &size);
        parse_range_option(code, head_info->total, size);
	free(code);
    }

    if (up_line == 0 && down_line == 0){
        up_line = 1;
	down_line = head_info->total;
    }

}

void init_head_commit_range_info(struct commit_hash_list* head_info, struct commit_info_list ** final_info){
    int i;
    for (i = 1; i <= head_info->total; ++i) {
        head_info->origin[i] = 0;
	final_info[i] = NULL;
    }

    for (i = up_line; i <= down_line; ++i) {
        head_info->origin[i] = i;
    }
}


/* BFS to parse each commit
 *        create the commit graph       
 *        count the indegree of each commit node
 *        build hash entry for each commit (also eliminate redundency in BFS)
 */
void prepare_visit_all_commits(){

    head = 0;
    tail = 1;

    struct commit_hash_list* info;

    while (head < tail) {
        struct commit* cur = queue[head++];	
	struct commit_list *parents;	
	parents = cur->parents;
	for (; parents != NULL; parents = parents->next){
	    struct commit* prev = parents->item;
	    parse_commit(prev);
	    info = commit_hash_lookup(prev->object.sha1);
	    ++prev->indegree;
	    if (info == NULL){
		info = commit_hash_insert(prev->object.sha1);
		queue[tail++] = prev;
	    }
	}
    }
    dprintf("In BFS, visit %d commits\n", tail);
}

void set_diff_option(struct diff_options* opt, char **diff_result, size_t *diff_len) {
    /* the git diff api
     * 1. initialize diffopt with default values
     * 2. change diffopt to specified values
     * 3. use open_memstream to redirect output to memory 
     * 4. initialize pathspect to specify that only diff on given path
     * 5. run diff
     */
    diff_setup(opt);
    opt->output_format |= DIFF_FORMAT_PATCH;
    opt->detect_rename = DIFF_DETECT_RENAME;
    DIFF_OPT_SET(opt, FOLLOW_RENAMES);
    if (!(diff_opt & DIFF_WHITESPACE)) {
        DIFF_XDL_SET(opt, IGNORE_WHITESPACE_CHANGE);
    }
    DIFF_XDL_SET(opt, IGNORE_WHITESPACE_AT_EOL);

    /* Here the best way is to use diff_scoreopt_parse, but it is defined static in diff.c
     * The formula is MAX_SCORE * num / scale
     * MAX_SCORE is 60000.0 defined in diffcore.h, which shouldn't be included
     */
    opt->rename_score = 60000 * 80 / 100;
    opt->file = open_memstream(diff_result, diff_len);
}

void get_diff_between_commits(struct diff_options *diffopt, const char *paths_array[2],
                              const unsigned char* prev_sha1, const unsigned char* cur_sha1) {
    init_pathspec(&diffopt->pathspec, paths_array);
    diff_setup_done(diffopt);
    diff_tree_sha1(prev_sha1, cur_sha1, "", diffopt);
    diffcore_std(diffopt);
    diff_flush(diffopt);
    fclose(diffopt->file);
}

void get_diff_between_given_files(struct diff_options *diffopt, 
                                  const char *one_path, struct tree* one_tree,
				  const char *two_path, struct tree* two_tree){

    struct diff_filespec *one, *two;
    const unsigned char *one_blob_sha1 = get_blob_sha1(one_tree, one_path);
    const unsigned char *two_blob_sha1 = get_blob_sha1(two_tree, two_path); 

    if (memcmp(one_blob_sha1, two_blob_sha1,20)) {
        one = alloc_filespec(one_path);
	two = alloc_filespec(two_path);
	fill_filespec(one, one_blob_sha1, canon_mode(S_IFREG | 0644));
	fill_filespec(two, two_blob_sha1, canon_mode(S_IFREG | 0644));
	
	diff_queue(&diff_queued_diff, one, two);
	diff_setup_done(diffopt);
	diffcore_std(diffopt);
	diff_flush(diffopt);
    }
    fclose(diffopt->file);
}



void sort_line_transfer(struct line_transfer* line_delta){
    qsort(line_delta->add, line_delta->add_total, sizeof(int), cmp_int);
    qsort(line_delta->del, line_delta->del_total, sizeof(int), cmp_int);
    qsort(line_delta->chg, line_delta->chg_total, sizeof(struct change_pair), cmp_change_pair);
    qsort(line_delta->chg_from, line_delta->chg_total, sizeof(int), cmp_int);
}

void prepare_author_info_structure(struct commit_hash_list* prev_info, struct commit* prev, const char *paths_array[2]){
    if (prev_info->cur_path == NULL) {
        prev_info->cur_path = (char*) my_allocate_commit(strlen(paths_array[0]) + 1, sizeof(char));
	strcpy(prev_info->cur_path, paths_array[0]);	
	prev_info->total = get_total_line_number(prev->tree, prev_info->cur_path);
	dprintf("In Commit %s, file %s has %d lines\n", sha1_to_hex(prev->object.sha1), prev_info->cur_path, prev_info->total);
	prev_info->origin = (int*) xcalloc(prev_info->total + 1 + total_line_in_start + 1, sizeof(int));		 		 
	prev_info->next_line = prev_info->origin + prev_info->total + 1;
    }
    else {	    
        if (strcmp(prev_info->cur_path, paths_array[0])) {
	    /* It shouldn't happen that differrent paths lead to different path names.
	     * If this happens, something should be wrong.
	     */
	    printf("ERROR: paths don't match on %s, for %s and %s\n", sha1_to_hex(prev->object.sha1), prev_info->cur_path, paths_array[0]);
	    exit(0);
	}

    } 
}

int duplicate_entry(int cur_line, struct commit_hash_list* prev, int from){
    from = prev->origin[from];
    while (from != 0) {
        if (cur_line == from) return 1;
	from = prev->next_line[from];
    }
    return 0;
}

void unchanged_line_transfer(int to, int from, struct commit_hash_list* cur, struct commit_hash_list* prev){
	dprintf("To = %d, From = %d\n", to ,from);
	if (from > prev->total) {
	    printf("ERROR: OUT OF RANGE\n");
	    printf("Current Commit %s, line number %d, total line %d\n", sha1_to_hex(cur->sha1), to , cur->total);
	    printf("Parent Commit %s, line number %d, total line %d\n", sha1_to_hex(prev->sha1), from , prev->total);
	    exit(0);
	}
	int cur_line = cur->origin[to];
	while (cur_line){
	    if (!duplicate_entry(cur_line, prev, from)) {
	        prev->next_line[cur_line] = prev->origin[from];
		prev->origin[from] = cur_line;
	    }
	    cur_line = cur->next_line[cur_line];	    
	}
}

void move_index_in_old_commit(struct line_transfer* delta, int to, int add_index, int chg_to_index, 
                              int *del_index, int *chg_from_index){
    int finish = 0;
    while (!finish) {
        finish = 1;
	while (*del_index < delta->del_total && delta->del[*del_index] <= 
	       to - add_index - chg_to_index + *del_index + *chg_from_index) {
	    ++(*del_index);
	    finish = 0;
	}
	while (*chg_from_index < delta->chg_total && delta->chg_from[*chg_from_index] <= 
	       to - add_index - chg_to_index + *del_index + *chg_from_index) {
	    ++(*chg_from_index);
	    finish = 0;
	}
    }
}

void insert_author_info(struct commit_info_list** info, int origin_line, int cur_line, 
                        struct commit_hash_list* c, char **lines){
    while (origin_line != 0){
        insert_commit_info_list(info, origin_line, cur_line, c, lines);
	origin_line = c->next_line[origin_line];
    }
}

void apply_transfer_function(struct commit_info_list ** final_info, struct commit_hash_list* cur, struct commit_hash_list* prev, 
                             struct line_transfer * delta, int number_of_parents, char **lines){
    int add_index, del_index, chg_from_index, chg_to_index, from, to;
    add_index = del_index = chg_from_index = chg_to_index = 0;
    dprintf("NUMBER OF PARENTS %d\n", number_of_parents);
    for (to = 1; to <= cur->total; ++to){
        if (cur->origin[to] == 0) continue;

        // check if the line is an added line
	while (add_index < delta->add_total && delta->add[add_index] < to) ++add_index;
	if (add_index < delta->add_total && delta->add[add_index] == to) {
	    ++add_index;
	    if (number_of_parents <= 1){
	        insert_author_info(final_info, cur->origin[to], to, cur, lines);
	    }
	    continue;
	}

        // check if the line is a changed line
	while (chg_to_index < delta->chg_total && delta->chg[chg_to_index].to < to) ++chg_to_index;
	if (chg_to_index < delta->chg_total && delta->chg[chg_to_index].to == to) {
	    if (number_of_parents <= 1 && delta->chg[chg_to_index].is_move == 0){
	        insert_author_info(final_info, cur->origin[to], to, cur, lines);
	    }
	    from = delta->chg[chg_to_index].from;
	    ++chg_to_index;	    
	}
	else {
            move_index_in_old_commit(delta, to, add_index, chg_to_index, &del_index, &chg_from_index);
	    from = to - add_index - chg_to_index + del_index + chg_from_index;
	}

	unchanged_line_transfer(to, from, cur, prev);
    }
}

void apply_identity_function(const char *paths_array[2], struct commit* prev,
                             struct commit_hash_list* cur_info, struct commit_hash_list* prev_info){
    
    prepare_author_info_structure(prev_info, prev, paths_array);

    int to, from;
    for (to = 1; to <= cur_info->total; ++to){
        if (cur_info->origin[to] == 0) continue;
	from = to;
	unchanged_line_transfer(to, from, cur_info, prev_info);
    }
}

/* Base on the commit graph, topologically visit each commit.
 * By specifying the filename in diff options, use tree-diff to get diff
 * for specified file.
 */
void visit_all_commits(struct commit_info_list **final_info) {
    int i;
    head = 0;
    tail = 1;
    while (head < tail) {
        struct commit* cur = queue[head++];	
	struct commit_list *parents;
	struct commit_hash_list * cur_info = commit_hash_lookup(cur->object.sha1);

	if (cur_info == NULL){
	    printf("ERROR: Cannot find info in hash table for commit %s\n", sha1_to_hex(cur->object.sha1));
	    exit(0);
	}

	parse_commit_info(cur, cur_info);

	int number_of_parents = 0;
	for (parents = cur->parents; parents != NULL; parents = parents->next)
	    ++number_of_parents;

	dprintf("Handling Commit %s:", sha1_to_hex(cur->object.sha1));

        unsigned long size = 0;
	char *code = NULL; 	
	char **lines = NULL; 

	if (cur_info->cur_path != NULL){
	    code = get_file_content(cur->tree, cur_info->cur_path, &size);
	    lines = split_into_lines(code, cur_info->total, size);
	}
	

	if (number_of_parents == 0) {
	    // Handle the very first commit
	    for (i = 1; i <= cur_info->total; ++i)
	        if (cur_info->origin[i] != 0)
		    insert_author_info(final_info, cur_info->origin[i], i, cur_info, lines);
	}
	
	for (parents = cur->parents; parents != NULL; parents = parents->next){
	    struct commit* prev = parents->item;
	    struct commit_hash_list * prev_info = commit_hash_lookup(prev->object.sha1);

	    --prev->indegree;
	    if (prev->indegree == 0){
	        queue[tail++] = prev;
	    }
	    if (prev_info == NULL){
	        printf("ERROR: Cannot find info in hash table for commit %s\n", sha1_to_hex(prev->object.sha1));
		exit(0);
	    }

	    if (cur_info->cur_path == NULL) continue;

	    dprintf(" %s", sha1_to_hex(prev->object.sha1));


	    struct diff_options diffopt;
	    char *diff_result = NULL;
	    size_t diff_len;
	    set_diff_option(&diffopt, &diff_result, &diff_len);
	    
	    char path[1024];
	    const char *paths_array[2];

	    paths_array[0] = path;
	    paths_array[1] = NULL;
	    strcpy(path, cur_info->cur_path);
	    if (prev_info->cur_path == NULL)
	        get_diff_between_commits(&diffopt, paths_array, prev->tree->object.sha1, cur->tree->object.sha1);
	    else {
	        dprintf("FORCING path conversion\n");
	        get_diff_between_given_files(&diffopt, prev_info->cur_path, prev->tree, path, cur->tree);
		strcpy(path, prev_info->cur_path);
		dprintf("%s\n", diff_result);
	    }
	        
	    dprintf(" CUR PATH %s PATH AFTER DIFF %s", cur_info->cur_path, paths_array[0]);
	    
	    if (diff_len == 0 || strstr(diff_result, "\nsimilarity index 100%\n") != NULL){
	        dprintf(" UNIFORM COPY ");
		apply_identity_function(paths_array, prev, cur_info, prev_info);
	    }
	    else {
	        dprintf(" TANSFER ");
		struct line_transfer* line_delta = parse_diff_result(diff_result, diff_len);	     
		sort_line_transfer(line_delta);
		print_line_transfer(line_delta);
	
	        /* if this is a new file, no info will be added the prev commit
		 * so there is no need to prepare info data strcture for prev commit
		 */
		if (strstr(diff_result, "\nnew file mode ") == NULL) {
		    prepare_author_info_structure(prev_info, prev, paths_array);
		}

		apply_transfer_function(final_info, cur_info, prev_info, line_delta, number_of_parents, lines); 
		free_line_transfer(line_delta);		 

	    }

	    if (diff_result != NULL) {
	        free(diff_result);
		diff_result = NULL;
	    }
	   
	}
	dprintf("\n");
	if (cur->buffer != NULL)
	    free(cur->buffer);
	free(cur_info->origin);
	free(code);
	free(lines);

	
    }

}

/****************************************** Weighted Authorship ************************************/
int * leven_diff(int current, int *belong, int *map, int *length, struct commit_info_list** list, int *fixed){
    char *new_code = list[current]->code;
    char *old_code = list[current - 1]->code;

    int new_length = length[current];
    int old_length = length[current - 1];

    int *new_map = (int*) my_allocate_ldiff(old_length, sizeof(int));    
    int *f = (int*) my_allocate_ldiff( (new_length+1) * (old_length+1), sizeof(int));
    int i,j;

    for (i = 0; i < old_length; ++i) new_map[i] = -1;

    #define CHG(x,y) (x) * new_length + (y)
    for (i = 0; i <= old_length; ++i) f[CHG(i,0)] = 0;
    for (j = 0; j <= new_length; ++j) f[CHG(0,j)] = 0;
    for (i = 1; i <= old_length; ++i)
        for (j = 1; j <= new_length; ++j) {
            f[CHG(i,j)] = MIN(f[CHG(i-1,j)], f[CHG(i,j-1)]) + 1;
	    if (old_code[i - 1] == new_code[j - 1])
	        f[CHG(i,j)] = MIN( f[CHG(i-1,j-1)], f[CHG(i,j)] );	       
	    else
	        f[CHG(i,j)] = MIN( f[CHG(i-1,j-1)] + 5, f[CHG(i,j)] );	       

        }

    
    dprintf("old code: %s\n", old_code);
    dprintf("new code: %s\n", new_code);
    dprintf("map:");

    for (j = 0; j < new_length; ++j) dprintf(" %d", map[j]);
    dprintf("\n");

    i = old_length;
    j = new_length;
   
    while (i > 0 && j > 0) {
        dprintf("%d %d %c %c\n", i,j, old_code[i-1], new_code[j-1]);
        if (f[CHG(i,j)] == f[CHG(i-1,j-1)] && old_code[i-1] == new_code[j-1]) {
	    if (map[j-1] != -1 && fixed[map[j-1]] == 0) {
	        belong[map[j-1]] = current - 1;
	    }
	    new_map[i-1] = map[j-1];
	    --i;
	    --j;
	} else if (f[CHG(i,j)] == f[CHG(i-1,j-1)] + 5) {
	    if (map[j-1] != -1 && fixed[map[j-1]] == 0) {
	        belong[map[j-1]] = current;
		fixed[map[j-1]] = 1;
	    }
	    new_map[i-1] = map[j-1];
	    --i;
	    --j;
	} else if (f[CHG(i,j)] == f[CHG(i,j-1)] + 1){
	    if (map[j-1] != -1 && fixed[map[j-1]] == 0){
	        belong[map[j-1]] = current;
		fixed[map[j-1]] = 1;
	    }
	    --j;
	}
	else {
	   --i;
	}
    }

    
    #undef CHG 

    return new_map;
}


int** calculate_weighted_authorship(struct commit_info_list ** cil, int total, int ***char_authorship) {
    int i,j;
    int ** code_share = (int**) my_allocate_commit( total, sizeof(int*));    
    *char_authorship = (int**) my_allocate_commit( total, sizeof(int*));
    for (i = up_line; i <= down_line; ++i) {
        
        int total_commit = 0;
	struct commit_info_list *p , **list;
	my_memory_ldiff_used = 0;
	for (p = cil[i]; p != NULL; p = p->next) ++total_commit;


	list = (struct commit_info_list**) my_allocate_ldiff( total_commit, sizeof(struct commit_info_list*));

        int *length = (int*) my_allocate_ldiff( total_commit, sizeof(int));
	int max_length = 0;
	for (p = cil[i], j = 0; p != NULL; p = p->next, ++j) {
	    list[j] = p;
	    length[j] = strlen(p->code);
	    if (length[j] > max_length) max_length = length[j];
	}

	int cur_length = length[total_commit - 1];
	int *belong = (int*) my_allocate_commit( cur_length, sizeof(int));
	int *map = (int*) my_allocate_ldiff( cur_length, sizeof(int));
	int *fixed = (int*) my_allocate_ldiff( cur_length, sizeof(int));

	if (total_commit < 2){	  
	    code_share[i]  = NULL;
	    (*char_authorship)[i] = NULL;
	    continue;
	}

	for (j = 0; j < cur_length; ++j) {
	    belong[j] = total_commit - 1;
	    map[j] = j;
	    fixed[j] = 0;
	}    

	for (j = total_commit - 1; j; --j) {
	    map = leven_diff(j, belong, map, length, list, fixed);	   
	}
	
	int* cnt = (int*) my_allocate_commit( total_commit, sizeof(int));
	for (j = 0; j < total_commit; ++j) cnt[j] = 0;
	for (j = 0; j < cur_length; ++j)
	    ++cnt[belong[j]];
        code_share[i] = cnt;
	(*char_authorship)[i] = belong;
    }
    return code_share;
}


/************************************** Result Output ******************************************/

void print_porcelain(struct commit_info_list ** cil, int total) {
    int i;
    for (i = up_line; i <= down_line; ++i) {
        int total = 0;
	struct commit_info_list *p;
	for (p = cil[i]; p != NULL; p = p->next) 
	    ++total;

        printf("%d %d\n", i, total);

	for (p = cil[i]; p != NULL; p = p->next){
	    printf("commit %s %d\n", sha1_to_hex(p->info->sha1), p->line_number);
	    if ( (output_format & OUTPUT_LINE_PORCELAIN) || (!p->info->outputed) ){
	        p->info->outputed = 1;
		printf("author %s\n", p->info->author_name);
		printf("author-email <%s>\n", p->info->email);
		printf("author-time %lu\n", p->info->author_time);
		printf("author-tz %s\n", p->info->author_tz);
	    }
	}
    }
}

int duplicate_output(struct commit_info_list *line, struct commit_info_list * cur){
    while (line != cur) {
        if (line->info == cur->info) return 1;
	line = line->next;
    }
    return 0;
}

void print_author_information(struct commit_info_list ** cil, struct commit_hash_list* head_info){
    int total = head_info->total;
    int length, i, j;
    if (output_format & OUTPUT_LONG_SHA1) 
        length = 40;
    else if (abbrev != -1)
        length = abbrev;
    else 
        length = default_abbrev;

    int** code_share = NULL;
    int** char_authorship = NULL;
    if (output_format & OUTPUT_WEIGHTED)
        code_share = calculate_weighted_authorship(cil, total, &char_authorship);
	
    unsigned long size = 0;
    char *code = NULL; 	
    char **lines = NULL; 
    
    if (output_format & OUTPUT_SHOW_CODE){
        code = get_file_content(queue[0]->tree, head_info->cur_path, &size);
	lines = split_into_lines(code, head_info->total, size);
    }

    char output_buf[1024];
    char tmp_buf[1024];
    int author_max_len = 0;
    int file_name_max_len = 0;
    int line_no_max_len = 0;
    int summary_max_len = 0;
    int date_max_len = 0;
    int score_max_len = 0;
    int len;
    if (output_format & OUTPUT_LINE_SCORE) score_max_len = 8;
    // calculate the max length needed for each entry
    for (i = up_line; i <= down_line; ++i) {
	int cur_length = 0;
	struct commit_info_list *p;
	int total_commit = 0;
	for (p = cil[i]; p != NULL; p = p->next) ++total_commit;
	if (output_format & OUTPUT_WEIGHTED){
	    for (p = cil[i]; p != NULL; p = p->next) {
	     	if (p->next == NULL)
		    cur_length = strlen(p->code);
	    }	    
	}

        for (p = cil[i],j = 0; p != NULL; p = p->next, ++j){
	    if (output_format & OUTPUT_SHOW_EMAIL) {
	        len = strlen(p->info->email);
		if (len > author_max_len) author_max_len = len;
	    }
	    else if (!(output_format & OUTPUT_NO_AUTHOR)) {
	        len = strlen(p->info->author_name);
		if (len > author_max_len) author_max_len = len;
	    }

	    if (output_format & OUTPUT_SHOW_NUMBER) {
	        sprintf(output_buf, "%d", p->line_number);
	        len = strlen(output_buf);
	        if (len > line_no_max_len) line_no_max_len = len;
	    }
	    if (output_format & OUTPUT_SHOW_PATH) {
	        len = strlen(p->path);
		if (len > file_name_max_len) file_name_max_len = len;
	    }
	    if (output_format & OUTPUT_WEIGHTED) {
		if (cur_length == 0) 
		    sprintf(output_buf, "%d/%d=NA", 0, 0 );	    
	        else if (code_share[i] == NULL)
		    sprintf(output_buf, "%d/%d=%.2lf%%", cur_length, cur_length, 100.0);	    
		else
		    sprintf(output_buf, "%d/%d=%.2lf%%", code_share[i][j], cur_length, 100.0 * code_share[i][j] / cur_length);	    
		len = strlen(output_buf);
		if (len > summary_max_len) summary_max_len = len;
	    }
	    if ( (output_format & OUTPUT_TIMESTAMP) || (output_format & OUTPUT_RAW_TIMESTAMP) ){
	        if (output_format & OUTPUT_RAW_TIMESTAMP) {
		    sprintf(output_buf, "%lu %s", p->info->author_time, p->info->author_tz);
		}
		else {
		    int tz = atoi(p->info->author_tz);
		    const char *time_str = show_date(p->info->author_time, tz, author_date_mode);
		    sprintf(output_buf, "%s", time_str);
		}
		len = strlen(output_buf);
		if (len > date_max_len) date_max_len = len;
	    }
	}
    }
 
    // real output
    for (i = up_line; i <= down_line; ++i) {
	int total_commit = 0;
	struct commit_info_list *p;

	for (p = cil[i]; p != NULL; p = p->next) {
	    ++total_commit;
	}

	struct commit_info_list **list = my_allocate_commit(total_commit, sizeof(struct commit_info_list));

	for (p = cil[i], j = 0; p != NULL; p = p->next, ++j)
	    list[j] = p;	    

        sprintf(tmp_buf, "CURRENT LINE %-4d", i);	    

	int space = length + 1;
	if (!(output_format & OUTPUT_NO_AUTHOR)) space += author_max_len + 1;
	if ((output_format & OUTPUT_TIMESTAMP) || (output_format & OUTPUT_RAW_TIMESTAMP) ) space += date_max_len + 1;
        if (output_format & OUTPUT_SHOW_PATH) space += file_name_max_len + 1;	
	if (output_format & OUTPUT_LINE_SCORE) space += score_max_len + 1;
	if (output_format & OUTPUT_SHOW_NUMBER) space += line_no_max_len + 1;
        if (output_format & OUTPUT_WEIGHTED) space += summary_max_len + 1;
	sprintf(output_buf, "%*s:", space - 1,  tmp_buf );
	printf("%s ", output_buf);
	if (output_format & OUTPUT_SHOW_CODE){
	    // the -1 is for the \n at end of each line
	    printf("%.*s", (int)(lines[i + 1] - lines[i] - 1), lines[i]);
	}
	if (!(output_format & OUTPUT_ONE_LINE)) printf("\n");
	int cur_length = 0;
	if (output_format & OUTPUT_WEIGHTED){
	    for (p = cil[i]; p != NULL; p = p->next) {	        
	     	if (p->next == NULL)
		    cur_length = strlen(p->code);
	    }	    
	}
	int first = 1;
	for (j = total_commit - 1; j >= 0; --j) {	    
	    p = list[j];
//	    if (duplicate_output(cil[i], p)) continue;
	    int cur = 0;	    
	    sprintf(output_buf + cur, "%.*s,", length, sha1_to_hex(p->info->sha1));
	    cur += length + 1;
	    output_buf[cur - 1] = ' ';	    

	    if (output_format & OUTPUT_SHOW_EMAIL) {
	        sprintf(output_buf + cur, "%-*s", author_max_len, p->info->email);
		cur += author_max_len + 1;
		output_buf[cur - 1] = ' ';
	    }
	    else if (!(output_format & OUTPUT_NO_AUTHOR)) {
	        sprintf(output_buf + cur, "%-*s", author_max_len, p->info->author_name);
		cur += author_max_len + 1;
		output_buf[cur - 1] = ' ';
	    }

	    if ( (output_format & OUTPUT_TIMESTAMP) || (output_format & OUTPUT_RAW_TIMESTAMP) ){
	        if (output_format & OUTPUT_RAW_TIMESTAMP) {
		    sprintf(tmp_buf,  "%lu %s", p->info->author_time, p->info->author_tz);
		    sprintf(output_buf + cur, "%-*s", date_max_len, tmp_buf);
		}
		else {
		    int tz = atoi(p->info->author_tz);
		    const char *time_str = show_date(p->info->author_time, tz, author_date_mode);
		    sprintf(output_buf + cur, "%-*s", date_max_len, time_str);
		}
		cur += date_max_len + 1;
		output_buf[cur - 1] = ' ';	 
	    }

	    if (output_format & OUTPUT_SHOW_PATH) {
		sprintf(output_buf + cur, "%-*s",file_name_max_len, p->path);
		cur += file_name_max_len + 1;
		output_buf[cur - 1] = ' ';
	    }
            int ignore = 0;
	    if (output_format & OUTPUT_WEIGHTED) {
		if (cur_length == 0){
		    sprintf(tmp_buf,"%d/%d=NA", 0, 0 );	    
		    ignore = 1;
		}    
	        else if (code_share[i] == NULL)
		    sprintf(tmp_buf,"%d/%d=%.2lf%%", cur_length, cur_length, 100.0);	    
		else {
		    sprintf(tmp_buf,"%d/%d=%.2lf%%", code_share[i][j], cur_length, 100.0 * code_share[i][j] / cur_length);	    
		    if (code_share[i][j] == 0) ignore = 1;
		}
		sprintf(output_buf + cur, "%-*s", summary_max_len, tmp_buf);
		cur += summary_max_len + 1;
		output_buf[cur - 1] = ' ';

	    }

	    if (output_format & OUTPUT_WEIGHTED) {
	        if (ignore == 1) continue;
	    }

	    if (output_format & OUTPUT_LINE_SCORE){	        
	        if (first) {
		    first = 0;
		    sprintf(output_buf + cur, "1.000000");
		}
		else {		   
		    int max_len = 0;
		    if (strlen(list[j]->code) > max_len) max_len = strlen(list[j]->code);
		    if (strlen(list[j+1]->code) > max_len) max_len = strlen(list[j+1]->code); 

		    double score = 0;
		    if (max_len != 0) {
		        int leven_dis = levenshtein(list[j]->code, list[j+1]->code, 10000, 1, 1, 1);
			score = (max_len - leven_dis) * 1.0 / max_len;
		    }

		    sprintf(output_buf + cur, "%.6lf", score); 
		}
	
		cur += score_max_len + 1;
		output_buf[cur - 1] = ' ';
	    }

 	    if (output_format & OUTPUT_SHOW_NUMBER) {
	        sprintf(output_buf + cur, "%-*d:", line_no_max_len,p->line_number);
		cur += line_no_max_len + 2;
		output_buf[cur - 1] = ' ';
	    }
   
	    if (output_format & OUTPUT_SHOW_CODE) {
	        if (!(output_format & OUTPUT_WEIGHTED) || char_authorship[i] == NULL) {
		    sprintf(output_buf + cur, "%s", p->code);
		}
		else {
		    int k;
		    char code[1024];
		    strncpy(code, lines[i], (int)(lines[i+1]-lines[i]-1));
		    code[lines[i+1]-lines[i]-1] = 0;
		    for (k = 0; k < cur_length; ++k)
		        if (char_authorship[i][k] != j) code[k] = ' ';
		    sprintf(output_buf + cur, "%s", code);
		}
	    }
	    printf("%s\n", output_buf);
	}
	printf("\n");
    }

    free(lines);
    free(code);
}

void print_author_information_one_line(struct commit_info_list ** cil, int total){
    int length, i, j;
    if (output_format & OUTPUT_LONG_SHA1) 
        length = 40;
    else if (abbrev != -1)
        length = abbrev;
    else 
        length = default_abbrev;

    int** code_share = NULL;    
    int** char_authorship = NULL;
    if (output_format & OUTPUT_WEIGHTED)
        code_share = calculate_weighted_authorship(cil, total, &char_authorship);

    for (i = up_line; i <= down_line; ++i) {
        printf("%4d:", i);
        int cur_length = 0;
        struct commit_info_list *p;
        if (output_format & OUTPUT_WEIGHTED){
            for (p = cil[i]; p != NULL; p = p->next) {
                if (p->next == NULL)
                    cur_length = strlen(p->code);
            }       
        }

        for (p = cil[i],j = 0; p != NULL; p = p->next, ++j) {       
	    if (duplicate_output(cil[i],p)) continue;
            printf(" (%.*s,", length, sha1_to_hex(p->info->sha1));
            if (output_format & OUTPUT_SHOW_EMAIL)
                printf("%s", p->info->email);
            else if (!(output_format & OUTPUT_NO_AUTHOR))
                printf("%s", p->info->author_name);

            if (output_format & OUTPUT_SHOW_NUMBER)
                printf(",%d", p->line_number);
            
            if (output_format & OUTPUT_SHOW_PATH)
                printf(",%s", p->path);
            if (output_format & OUTPUT_SHOW_CODE)
                printf(",%s", p->code);
            if (output_format & OUTPUT_WEIGHTED) {
                if (cur_length == 0) 
                    printf(",%d/%d=NA", 0, 0 );     
                else if (code_share[i] == NULL)
                    printf(",%d/%d=%.2lf%%", cur_length, cur_length, 100.0);        
                else
                    printf(",%d/%d=%.2lf%%", code_share[i][j], cur_length, 100.0 * code_share[i][j] / cur_length);          
            }
            if ( (output_format & OUTPUT_TIMESTAMP) || (output_format & OUTPUT_RAW_TIMESTAMP) ){
                if (output_format & OUTPUT_RAW_TIMESTAMP) {
                    printf(",%lu %s", p->info->author_time, p->info->author_tz);
                }
                else {
                    int tz = atoi(p->info->author_tz);
                    const char *time_str = show_date(p->info->author_time, tz, author_date_mode);
                    printf(",%s", time_str);
                }
            }
            printf(")");
        }       
        printf("\n");

    }
}
void print_author_count(struct commit_info_list ** cil, int total){
    int i;

    for (i = up_line; i <= down_line; ++i) {
        printf("%4d:", i);

	int total_commit = 0;
	int total_author = 0;
        struct commit_info_list *p;


        for (p = cil[i]; p != NULL; p = p->next) {       
	    if (duplicate_output(cil[i],p)) continue;
	    ++total_commit;
        }       

	for (p = cil[i]; p != NULL; p = p->next){
	    int found = 0;
	    struct commit_info_list* q;
	    for (q = cil[i]; q != p; q = q -> next) {
	        if (!strcmp(p->info->author_name, q->info->author_name)) {
		    found = 1;
		    break;
		}
	    }
	    if (found == 0) ++total_author;

	}

        printf("%d %d\n", total_commit, total_author);

    }
}

void print_single_author(struct commit_info_list ** cil, int total){

    int** code_share = NULL;    
    int** char_authorship = NULL;
    int i,j;
    code_share = calculate_weighted_authorship(cil, total, &char_authorship);
    printf("%d\n", total);
    for (i = 1; i <= total; ++i) {
        int cur_length = 0;
        struct commit_info_list *p;
        if (output_format & OUTPUT_WEIGHTED){
            for (p = cil[i]; p != NULL; p = p->next) {
                if (p->next == NULL)
                    cur_length = strlen(p->code);
            }       
        }
	int max_share = 0;
	struct commit_info_list * max_commit = cil[i];

	if (code_share[i] != NULL)
	    for (p = cil[i],j = 0; p != NULL; p = p->next, ++j)
	        if (code_share[i][j] > max_share){
		    max_share = code_share[i][j];
		    max_commit = p;
		}
        if (max_commit == NULL)
	    printf("unknown\n");
	else
	    printf("%s\n", max_commit->info->author_name);

    }
}

/****************************************** Main Function *****************************************/
int cmd_author(int argc, const char **argv, const char *prefix){

    unsigned char start_commit_sha1[20];
    char file_name[128];
    file_name[0] = 0;

    argc = parse_options(argc, argv,prefix, builtin_author_options, builtin_author_usage, PARSE_OPT_KEEP_DASHDASH |  PARSE_OPT_KEEP_ARGV0);

    if (argc == 1) {
        usage(author_usage);        
    }

    if (!strcmp(line_token_type, "char"))
        line_similarity_score = &line_similarity_char_score;
    else
        line_similarity_score = &line_similarity_token_score;

    /* Possible candidate:
     *   Starting Commit: sha1
     *   File Name: path
     */
    if (prefix != NULL) strcpy(file_name, prefix);
    parse_left_argument(argc, argv, start_commit_sha1, file_name);

    struct commit_hash_list* head_info;
    head_info = init_start_commit_info(start_commit_sha1, file_name);
    total_line_in_start = head_info->total;

    struct commit_info_list ** final_info = (struct commit_info_list**) xcalloc(head_info->total + 1, sizeof(struct commit_info_list*));

    prepare_parse_range_option(head_info);

    init_head_commit_range_info(head_info, final_info);

    prepare_visit_all_commits();

    visit_all_commits(final_info);

    setup_pager();
    if (output_format & OUTPUT_TOTAL_COUNT) {
        print_author_count(final_info, head_info->total);
    } else if (output_format & OUTPUT_SINGLE_AUTHOR)
        print_single_author(final_info, head_info->total);
    else if ((output_format & OUTPUT_PORCELAIN) || (output_format & OUTPUT_LINE_PORCELAIN))
        print_porcelain(final_info, head_info->total);
    else if (output_format & OUTPUT_ONE_LINE) { 
        print_author_information_one_line(final_info, head_info->total);
    }
    else {
        print_author_information(final_info, head_info);
    }
    return 0;
}
