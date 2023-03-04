/* A minimal, didactic, extendible Lisp interpreter embeddable in C/C++ programs */
/*
Gli obiettivi di yoctoLisp: realizzare un interprete Lisp più puro possibile, minimale, embeddabile in programmi C/C++.
Deve essere VELOCE, con un uso minimale di memoria.
Non mi interessa la totale compatibilità con i vari sistemi LISP, interessa invece la portabilità.
due versioni: dynamic binding e lexical scoping.
garbage collector: mark-sweep.
*/

//timing
// 0.98.23
//         44% 8100 --> 42% 7800 se trovo l'errore (con gc a pseudo generazioni ... trovatO. non risolvibile!)
//                      43% 8000 risolto: marcare tutto e non fermarsi al primo 1
// 0.98.22 17%          I:2061 S:1782 L:1032
//         33% (fib 35) I:4247 S:3861 L:2217            pico:2152 picco:2126
// 0.98.11 19% fib      I:2406 S:2016 L:1063
//         44%          I:5171 S:4596 L:2465 femto:2707 pico:2679

#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <setjmp.h>
#include <math.h>
#include <time.h>

// cose da fare:
// test della memoria con memwatch
// "save" per salvare lo stato corrente in forma caricabile da "load"
// sistemare la named let che funziona solo se è una tail call, bisognerebbe fare in modo che funzioni così quando è una tail call in altro modo quando non lo è ...
// provare a fare caricamenti di file da altre directory con altri "load" nestati
// forse ho una strategia per le variabili locali: associare al simbolo una lista con valore e "transazione", all'entrata di funzioni si aumenta la "transazione" e si mette il valore, all'uscita si elimina la testa della lista
// sistemare il parser per il caso xx:yy:zz ... ora separa ma poi perde i :
// named let quando non è tail call, dilemma: così com'è non è quella di scheme ed ha un gran senso come "tail call" ... ma è totalmente fuori standard e non controllabile
// garbage collector senza mark e full ... dal test sembra più veloce!
// compilatore per #lap e #lambdalap
// fare parametri non valutati @x ?
// fare i parametri #0 con chiamata builtin?
// catch - throw - finally
// fare native: last, fold, reduce
// eliminare la sintassi #0 ... e puntare tutto su #lap?
// istruzione "case"
// cambiare da macro a ... come chiamare le fexpr?
// input da stringa
// open, close, read, read-line
// bignum? float? date? tipi di dati liberi
// estendibilità con librerie esterne
// moduli, oggetti e classi

// cose fatte:
// fare la "else" in cond
// fare "prog1", "rand", "randomize"
// do con variabili senza esprssione di step e anche senza inializzazione (25/4/2020)
// controllo dei parametri in named let (25/4/2020)
// stampa di strutture ricorsive (da rplaca) (22/04/2020)
// "named let" come in scheme per iterazione semplificata (22/04/2020)
// check del numero di parametri su tutte le funzioni (21/04/2020)
// "let" senza inizializzazione (20/04/2020)

// cose scartate:
// stampare in modo diverso le builtin (oggi ripetono il simbolo) -- provato, ma poi si vedono malissimo le funzioni che espongono il tipo dei simboli!
// garbage collector parallelo -- provato, ma rallenta!
// eliminare *plist* da system.yl -- non disturba ...

#define LEXICAL_SCOPING
//#define TAILCALL
#define SAFE_STACK
#define SAFE_CXR
//#define DEBUG_GC
//#define DEBUG_C_MEMORY
//#define REPL_TIMING
#define EVAL_FUNCPTR // eval con puntatori a funzioni, altrimenti eval con apply integrata e computed goto

#define MAX_CELLS 40000 // cons cells allocation block size
#define MAX_SYMS  500   // symbols allocation block size (not garbage collected)
#define MAX_STK   10000 // stack size

#ifdef DEBUG_C_MEMORY
#define MEMWATCH
#include "memwatch.h"
#endif

enum {TYPE_CONS=0,TYPE_SYM,TYPE_KEYWORD,TYPE_NUM,TYPE_STR,TYPE_BUILTINLAMBDA,TYPE_BUILTINMACRO,TYPE_BUILTINSTACK,TYPE_CXR,TYPE_LETLOOP,TYPE_FREE,TYPE_TRAMPOLINE};
enum {LT_NOLAMBDA=0,LT_LAMBDA,LT_MACRO,LT_LABEL,LT_SLAMBDA,LT_SLAMBDALAP};

typedef struct cell {
  unsigned char type,gc,globalassigned,lambdatype;
  union {
    struct {
      union {
        struct cell* car;
				struct cell* letloop;
        char* sym;
        int value;
        char* str;
      };
      union {
        struct cell* cdr;
        struct cell* (*builtinlambda)(int,struct cell*);
        struct cell* (*builtinmacro)(struct cell*,struct cell*);
        struct cell* (*builtinstack)(int);
        struct cell* globalvalue;
      };
    };
		/* lavoro da fare ... float e long
    union {
      double dvalue;
      long long int lvalue;
    } numV;
		*/
  };
#ifdef DEBUG_GC
    struct cell* free_cells;
#endif
} cell;

typedef struct cellsBlock {
  cell cells[MAX_CELLS];
  struct cellsBlock* next;
#ifdef DEBUG_GC
  int guard;
#endif // DEBUG_GC
} cellsBlock;

typedef struct symsBlock {
  cell syms[MAX_SYMS];
  struct symsBlock *next;
} symsBlock;

static jmp_buf yl_mainloop;

static cellsBlock *yl_fcb=0,*yl_lcb=0;
static symsBlock *yl_fsb,*yl_lsb;
static cell *yl_free_cells=0;
static int yl_nblocks,yl_nsymsblocks,yl_nsyms,yl_sp;
static cell* yl_stk[MAX_STK];

enum {LISP_ERROR=1,SYSTEM_ERROR,BYE_JMP};

static char yl_error_msg[1024];
void yl_lerror(const int code,const char* msg){strcpy(yl_error_msg,msg);longjmp(yl_mainloop,code);}
void yl_lerror_i(const int code,const char* msg,const int v){sprintf(yl_error_msg,msg,v);longjmp(yl_mainloop,code);}
void yl_lerror_s(const int code,const char* msg,const char* v){sprintf(yl_error_msg,msg,v);longjmp(yl_mainloop,code);}
void yl_lerror_ss(const int code,const char* msg,const char* v1,const char* v2){sprintf(yl_error_msg,msg,v1,v2);longjmp(yl_mainloop,code);}

static inline int is_num(const cell* c){return c->type==TYPE_NUM;}
static inline int is_str(const cell* c){return c->type==TYPE_STR;}
static inline int is_sym(const cell* c){return c->type==TYPE_SYM||c->type==TYPE_KEYWORD||c->type==TYPE_BUILTINLAMBDA||c->type==TYPE_BUILTINMACRO||c->type==TYPE_BUILTINSTACK||c->type==TYPE_CXR;}
static inline int is_cons(const cell* c){return c->type==TYPE_CONS;}

#ifdef SAFE_CXR
int max_stack=0;
// funzioni di gestione dello stack per tenere attive le strutture durante la garbage collection
static inline cell* push(cell* x){yl_stk[yl_sp++]=x;if(yl_sp>=MAX_STK) yl_lerror(SYSTEM_ERROR,"stack overflow");/*if(yl_sp>max_stack){printf("max:%d\n",yl_sp);max_stack=yl_sp;};*/return x;}
static inline cell* pop(cell* x){yl_sp--;if(yl_sp<0) yl_lerror(SYSTEM_ERROR,"stack undeflow");return x;}
static inline cell* pop2(cell* x){yl_sp-=2;if(yl_sp<0) yl_lerror(SYSTEM_ERROR,"stack undeflow");return x;}
static inline cell* popn(cell* x,int n){yl_sp-=n;if(yl_sp<0) yl_lerror(SYSTEM_ERROR,"stack undeflow in popn");return x;}
static inline cell* swp(cell* x){if(yl_sp<1) yl_lerror(SYSTEM_ERROR,"stack undeflow in swp"); yl_stk[yl_sp-1]=x;return x;}
#define CHECK_0(cond,t,msg) if (cond) yl_lerror(t,msg);
#define CHECK_I(cond,t,msg,i) if (cond) yl_lerror_i(t,msg,i);
#define CHECK_S(cond,t,msg,s) if (cond) yl_lerror_s(t,msg,s);
#define SAFE_CXR_STARTINGMSG
#else
// funzioni di gestione dello stack per tenere attive le strutture durante la garbage collection
#ifdef SAFE_STACK
static inline cell* push(cell* x){yl_stk[yl_sp++]=x;if(yl_sp>=MAX_STK) yl_lerror(SYSTEM_ERROR,"stack overflow");return x;}
#else
static inline cell* push(cell* x){yl_stk[yl_sp++]=x;return x;}
#endif
static inline cell* pop(cell* x){yl_sp--;return x;}
static inline cell* pop2(cell* x){yl_sp-=2;return x;}
static inline cell* popn(cell* x,int n){yl_sp-=n;return x;}
static inline cell* swp(cell* x){yl_stk[yl_sp-1]=x;return x;}
#define CHECK_0(cond,t,msg)
#define CHECK_I(cond,t,msg,i)
#define CHECK_S(cond,t,msg,s)
#define SAFE_CXR_STARTINGMSG  printf("NO CHECKS!\n");
#endif
#ifdef DEBUG_GC
int yl_stopping=0;
#define CHECKFREECELL(e) if (e && e->type==TYPE_FREE) yl_lerror(SYSTEM_ERROR,"referencing a free cell");if(e && e->type>TYPE_FREE) yl_lerror(SYSTEM_ERROR,"bad cell");
#define NEXTFREECELL(x) next_free_cell(x)
#define ASSERTGC(cond,msg) {if (!(cond)) printf("ASSERT:%s\n",msg);}
#define DEBUG_GC_STARTINGMSG  printf("Debugging GC\n");
cell* next_free_cell(cell* x){ASSERTGC(x->type==TYPE_FREE,"not free cell");return x->free_cells;}
#else
#define CHECKFREECELL(x)
#define NEXTFREECELL(x) (x)->car
#define ASSERTGC(cond,msg)
#define DEBUG_GC_STARTINGMSG
#endif

//static inline int ATOM(cell* a){return a->type!=TYPE_CONS;}
#define ATOM(a) a->type //!=TYPE_CONS
//static inline int atom(cell* a){if (!a) return 1;CHECKFREECELL(a);return a->type!=TYPE_CONS;}
#define atom(a) (a?a->type/*!=TYPE_CONS*/:1)

static void print_sexpr(cell* c,int mode);

static void yl_mark(cell* c){
  while (c && !c->gc){
    c->gc=1;
    if (ATOM(c)) return;
    yl_mark(c->car);
    c=c->cdr;
  }
}

static void yl_clearcellsgc(){
  cellsBlock* cb=yl_fcb;
  while (cb){
    int i;
    for(i=0;i<MAX_CELLS;i++) // mark all cells as unused
      cb->cells[i].gc=0;
    cb=cb->next;
  }
}

static int yl_ngc=0,yl_nfreecells=0;

static void yl_gc(){
  int i;
  cell* c,sc;
  cellsBlock* cb;
  symsBlock *sb;
  // se il garbage collector viene chiamato con celle libere è possibile che vengano rilasciate più volte, bisogna marcarle come libere
  c=yl_free_cells;
  while(c){
    c->type=TYPE_FREE;
    c=NEXTFREECELL(c);
  }
  // segna come libere le celle
  yl_clearcellsgc();
  // -- mark --
  for(i=0;i<yl_sp;i++)
    yl_mark(yl_stk[i]); // mark all locked objects
  sb=yl_fsb;
  while(sb){
    int nsyms=(sb->next?MAX_SYMS:yl_nsyms);
    cell* syms=sb->syms;
    for(i=0;i<nsyms;i++){
      sc=syms[i];
      if (sc.globalassigned) // && sc.globalvalue)
        yl_mark(sc.globalvalue); // mark all globals
    }
    sb=sb->next;
  }
  // -- sweep --
  yl_ngc++;
  yl_nfreecells=0;
  cell* l_free_cells=0;
  cb=yl_fcb;
  while(cb){
    ASSERTGC(cb->guard==12321,"invalid cell block!");
    int nfreeinblock=0;
    for(i=0;i<MAX_CELLS;i++){
      c=&(cb->cells[i]);
      ASSERTGC(c->type==TYPE_CONS||c->type==TYPE_NUM||c->type==TYPE_STR||c->type==TYPE_FREE||c->type==TYPE_TRAMPOLINE||c->type==TYPE_LETLOOP,"unexpected cell type");
      ASSERTGC(yl_stopping || c->type!=TYPE_FREE,"exploring a free cell");
      if (!c->gc){
        if (c->type==TYPE_STR) free(c->str);
        nfreeinblock++;
#ifdef DEBUG_GC
        c->type=TYPE_FREE;c->free_cells=l_free_cells;c->car=c->cdr=0;
#else
        c->car=l_free_cells;
#endif
        l_free_cells=c;  // connect all free cells
      }
    }
    //if (nfreeinblock==nc) printf("blocco liberabile %i\n",nc);
    yl_nfreecells+=nfreeinblock;
    cb=cb->next;
  }
  yl_free_cells=l_free_cells;
  //printf("%s gc: free cells=%d sp=%d cells=%d\n",(mode?"full":"partial"),yl_nfreecells,yl_sp,yl_nblocks*MAX_CELLS);
  //if(ngc%10000==0) printf("gc check\n");
}

static void yl_addCellsBlock(){
  cellsBlock *cb=malloc(sizeof(cellsBlock));
  if (!cb) yl_lerror(SYSTEM_ERROR,"memory exausted");
#ifdef DEBUG_GC
  cb->guard=12321;
#endif // DEBUG_GC
  yl_nblocks++;
  cb->next=0;
  if (yl_lcb) // add to block list
    yl_lcb->next=cb;
  else // first block
    yl_fcb=cb;
  yl_lcb=cb;
  // link free cells
  cell* l_free_cell=yl_free_cells;
  int i;
  for(i=0;i<MAX_CELLS;i++){
    cb->cells[i].car=l_free_cell;l_free_cell=&(cb->cells[i]);
#ifdef DEBUG_GC
    cb->cells[i].free_cells=cb->cells[i].car;cb->cells[i].type=TYPE_FREE;cb->cells[i].car=cb->cells[i].cdr=0;
#endif
  }
  yl_free_cells=l_free_cell;
  yl_nfreecells=MAX_CELLS;
}

static void yl_addSymsBlock(){
  symsBlock *sb=malloc(sizeof(symsBlock));
  if (!sb) yl_lerror(SYSTEM_ERROR,"memory exausted");
  yl_nsymsblocks++;
  sb->next=0;
  if (yl_lsb)
     yl_lsb->next=sb;
  else
     yl_fsb=sb;
  yl_lsb=sb;
  yl_nsyms=0;
}

static cell* yl_collect_cell(){
  yl_gc();
  if (!yl_free_cells || yl_nfreecells*8<yl_nblocks*MAX_CELLS){
    if(yl_free_cells) printf("adding for spare space ... free=%d alloc=%d\n",yl_nfreecells,yl_nblocks*MAX_CELLS);
    yl_addCellsBlock();
    ASSERTGC(yl_free_cells==&(yl_lcb->cells[MAX_CELLS-1]),"free cells not linked");
    ASSERTGC(yl_nfreecells==MAX_CELLS,"wrong number of free cells");
  }
  cell* c=yl_free_cells;
  yl_free_cells=NEXTFREECELL(c);
  return c;
}

static inline cell* yl_get_cell(){
  if (yl_free_cells){
    cell* c=yl_free_cells;
    yl_free_cells=NEXTFREECELL(c);
    return c;
  }
  return yl_collect_cell();
}

static cell* mk_num(int v){
  cell* c=yl_get_cell();
  c->type=TYPE_NUM;
  c->lambdatype=LT_NOLAMBDA;
  c->value=v;
  return c;
}

static cell* mk_str(char* n){
  cell* c=yl_get_cell();
  c->type=TYPE_STR;
  c->lambdatype=LT_NOLAMBDA;
  c->str=malloc(strlen(n)+1);
  strcpy(c->str,n);
  return c;
}

static cell* mk_cons(cell* car,cell* cdr){
  cell* c;
  if (!yl_free_cells){
    // non ci sono celle libere, bisogna bloccare gli argomenti perché potrebbe essere distrutti dall' operazione
    push(car);
    push(cdr);
    c=yl_collect_cell();
    pop2(0);
  } else{
    c=yl_free_cells;
    yl_free_cells=NEXTFREECELL(c);
  }
  ASSERTGC(c->type==TYPE_FREE,"not a free cell in mk_cons");
  c->type=TYPE_CONS;
  c->lambdatype=LT_NOLAMBDA;
  c->car=car;
  c->cdr=cdr;
  return c;
}

#ifdef TAILCALL
static cell* mk_trampoline(cell* car,cell* cdr){
  cell* c=mk_cons(car,cdr);
  c->type=TYPE_TRAMPOLINE;
  return c;
}
#endif

static cell* bi_cxxxrS(const int n,const char* sym);

static void makeCxxxR(cell* c){
  int l=strlen(c->sym);
  if (l>3 && c->sym[0]=='c' && c->sym[l-1]=='r'){
    int i;
    for(i=1;i<l-1;i++)
      if(c->sym[i]!='a' && c->sym[i]!='d') return;
    c->type=TYPE_CXR;
  }
}

static cell* mk_sym(const char* n){
  // cerca il simbolo tra quelli già creati
  int i;
  symsBlock *sb=yl_fsb;
  while (sb){
    int nsyms=(sb->next?MAX_SYMS:yl_nsyms);
    cell* syms=sb->syms;
    for(i=0;i<nsyms;i++){
      if (strcmp(syms[i].sym,n)==0) return &syms[i];
    }
    sb=sb->next;
  }
  // crea un nuovo simbolo
  //if (yl_nsyms==MAX_SYMS) yl_lerror(SYSTEM_ERROR,"symbols memory exausted");
  if (yl_nsyms==MAX_SYMS) yl_addSymsBlock();
  cell* c=&yl_lsb->syms[yl_nsyms++];
  c->type=(n[0]==':'?TYPE_KEYWORD:TYPE_SYM);
  c->sym=malloc(strlen(n)+1);
  strcpy(c->sym,n);
  c->globalvalue=0;
  c->globalassigned=0;
  c->lambdatype=LT_NOLAMBDA;
  c->gc=1;
  // verifica se è una funzione cxxxr
  makeCxxxR(c);
  return c;
}

static cell* mk_builtinLambda(const char* n,cell*(*b)(int,cell*)){
  cell* c=mk_sym(n);
  c->type=TYPE_BUILTINLAMBDA;
  c->builtinlambda=b;
  return c;
}

static cell* mk_builtinMacro(const char* n,cell*(*b)(cell*,cell*)){
  cell* c=mk_sym(n);
  c->type=TYPE_BUILTINMACRO;
  c->builtinmacro=b;
  return c;
}

static cell* mk_builtinStack(const char* n,cell*(*b)(int)){
  cell* c=mk_sym(n);
  c->type=TYPE_BUILTINSTACK;
  c->builtinstack=b;
  return c;
}

static cell* mk_namedlet(cell* name){
	cell* c=mk_cons(0,0);
	c->type=TYPE_LETLOOP;
	c->letloop=name;
  return c;
}

static cell *quote_atom,*t_atom,*lambda_atom,*macro_atom,*label_atom,*anon_atom,*invisible_atom,*else_atom;

#ifdef SAFE_CXR
static inline cell* rplaca(cell* c,cell* n){if(!c || c->type!=TYPE_CONS) yl_lerror(SYSTEM_ERROR,"rplaca not on a cons");c->car=n;return c;}
static inline cell* rplacd(cell* c,cell* n){if(!c || c->type!=TYPE_CONS) yl_lerror(SYSTEM_ERROR,"rplacd not on a cons");c->cdr=n;return c;}
#else
static inline cell* rplaca(cell* c,cell* n){c->car=n;return c;}
static inline cell* rplacd(cell* c,cell* n){c->cdr=n;return c;}
#endif // SAFE_CXR

// ------------ lo scanner --------------------

enum {TOK_NONE, TOK_OPEN, TOK_CLOSE, TOK_DOT, TOK_QUOTE, TOK_SYM, TOK_NUM, TOK_STR};

#define MAX_TOKEN_LEN 1024
static int  next_char=-1;
static char token_text[MAX_TOKEN_LEN];
static long token_value;

static char nextchar(FILE *f){
  char c;
  do {
    int ch = fgetc(f);
    if (ch == EOF)
      return 0;
    c = (char)ch;
    if (c == ';') { // single-line comment
      do {
        ch = fgetc(f);
        if (ch == EOF)
          return 0;
      } while ((char)ch != '\n');
      c = (char)ch;
    }
  } while (isspace(c));
  return c;
}

static int issymchar(char c){
  return (c=='+' || c=='*' || c=='-' || c=='/' || c=='_' || c=='=' || c=='<' || c=='>' || c=='!' || c=='?' || c==':'
          || ('0'<=c && c<='9') || ('A'<=c && c<='Z') || ('a'<=c && c<='z'));
}

static int nexttoken(FILE *f){
  int token;
  char c = (next_char==-1?nextchar(f):(char)next_char);
  if (c == 0) return TOK_NONE;
  next_char=-1;
  if (c == '(') token = TOK_OPEN;
  else if (c == ')') token = TOK_CLOSE;
  else if (c == '.') token = TOK_DOT;
  else if (c == '\'') token = TOK_QUOTE;
  else {
    token=TOK_SYM;
    int i=0;
    if (c=='"'){
      do {
        c =(char)fgetc(f);
        token_text[i++]=c;
        if (i==MAX_TOKEN_LEN) yl_lerror(LISP_ERROR,"token too large");
      } while(c!='"' && c!='\n');
      token_text[i-1]=0;
      if (c=='\n') yl_lerror_s(LISP_ERROR,"non terminating string \"%s\"",token_text);
      token=TOK_STR;
    } else {
      do {
        token_text[i++]=c;
        c = (char)fgetc(f);
      } while(issymchar(c));
      token_text[i]=0;
      // controlla se + un numero
      char *e;
      token_value = strtol(token_text, &e, 0);
      if (*e == '\0') token = TOK_NUM;
      // ora devo preparare per il prossimo
      if (c==0 || c=='(' || c==')' || c=='.' || c=='\'') // || c==':') // devo decidere se : separa o no ...
        next_char = c;
    }
  }
  return token;
}

static cell* read_sexpr_tok(FILE* f,int tok){
  switch(tok){
  case TOK_NUM: return mk_num(token_value);
  case TOK_STR: return mk_str(token_text);
  case TOK_SYM: return (strcmp(token_text,"nil")==0?0:mk_sym(token_text));
  case TOK_QUOTE:
    tok=nexttoken(f);
    return mk_cons(quote_atom,mk_cons(read_sexpr_tok(f,tok),0));
  case TOK_OPEN:
    tok=nexttoken(f);
    if (tok!=TOK_CLOSE){
      cell* c=push(mk_cons(t_atom,0));
      cell* n=c;
      while (tok!=TOK_CLOSE && tok!=TOK_DOT) {
        //printf("read-1 n:");print_sexpr(n,0);printf("\n");
        cell* xx=read_sexpr_tok(f,tok);
        //printf("read0 xx:");print_sexpr(xx,1);printf("\n");
        //printf("read0 n:");print_sexpr(n,0);printf("\n");
        rplaca(n,xx);
        //printf("read1 n:");print_sexpr(n,0);printf("\n");
        //printf("read1 c:");print_sexpr(c,0);printf("\n");
        tok=nexttoken(f);
        if (tok!=TOK_DOT && tok!=TOK_CLOSE){
          rplacd(n,mk_cons(t_atom,0));
          //printf("read4 n:");print_sexpr(n,0);printf("\n");
          //printf("read4 c:");print_sexpr(c,0);printf("\n");
          n=n->cdr;
        }
      }
      if (tok==TOK_DOT){
        tok=nexttoken(f);
        rplacd(n,read_sexpr_tok(f,tok));
        //printf("read2:");print_sexpr(c,0);printf("\n");
        tok=nexttoken(f);
      } else {
        n->cdr=0;
      }
      if (tok!=TOK_CLOSE){
        yl_lerror(LISP_ERROR,") expected");
      }
      //printf("read3:");print_sexpr(c,0);printf("\n");
      return pop(c);
    } else {
      return 0;
    }
  default:
    yl_lerror_s(LISP_ERROR,"unexpected %s",(tok==TOK_CLOSE?")":(tok==TOK_DOT?".":token_text)));
  };
  return 0;
}

static cell* read_sexpr(FILE* f){
  int tok=nexttoken(f);
  if(tok!=TOK_NONE)
    return read_sexpr_tok(f,tok);
  return 0;
}

static int yl_print_stack_base=-1;

static int already_printed(cell* c){
  int i;
  for(i=yl_print_stack_base;i<yl_sp;i++)
    if (yl_stk[i]==c)
      return i-yl_print_stack_base+1;
  return 0;
}

static void print_sexpr(cell* c,int mode){
  int isStart=(yl_print_stack_base==-1),ap;
  if (!isStart && c && c->type==TYPE_CONS) { // è una chiamata ricorsiva, controlla che non sia già stato stampato
    ap=already_printed(c);
    if (ap){
      printf(" #%d# ",ap);
      return;
    }
  } else if (isStart){
    yl_print_stack_base=yl_sp;
  }
  push(c);
  if (c){
    switch(c->type){
    case TYPE_NUM:printf("%i",c->value);break;
    case TYPE_STR:printf((mode?"\"%s\"":"%s"),c->str);break;
    case TYPE_SYM:
    case TYPE_KEYWORD:
    case TYPE_CXR:
    case TYPE_BUILTINSTACK:                           //printf("<lambda:%s>",c->sym);break;
    case TYPE_BUILTINLAMBDA:                          //printf("<LAMBDA:%s>",c->sym);break;
    case TYPE_BUILTINMACRO:printf("%s",c->sym);break; //printf("<macro:%s>",c->sym);break;
    case TYPE_LETLOOP:printf("<let:%s>",c->letloop->sym);break;
    case TYPE_CONS:
      printf("(");
      ap=0;
      while (c->cdr && is_cons(c->cdr) && !ap){
        print_sexpr(c->car,mode);
        printf(" ");
        c=c->cdr;
        ap=already_printed(c);
      }
      if (ap){
        printf(" #%d# ",ap);
      } else {
        print_sexpr(c->car,mode);
        if (c->cdr){
          printf(" . ");
          print_sexpr(c->cdr,mode);
        }
      }
      printf(")");
      break;
    default:yl_lerror(SYSTEM_ERROR,"printing a free cell");
    }
  } else {
    printf("nil");
  }
  pop(c);
  if (isStart) yl_print_stack_base=-1;
}

void showdbg(char* s,cell* x){printf("%s=",s);print_sexpr(x,0);printf("\n");}

// --------- l' interprete! ---------------------------------------

static cell* eval(cell* fn,cell* a);
#ifdef EVAL_FUNCPTR
static inline cell* apply(cell* fn,cell* x,cell* a);
#endif
static inline cell* assq_cdr(const cell* x,const cell* a);
static cell* lap(const cell* x,cell* a,const int stackbase);

static cell* curr_fn;

#ifdef SAFE_CXR
int count_params(const cell* x){int n=0;while(x) {x=x->cdr;n++;};return n;}
void cons_expected(){yl_lerror_s(LISP_ERROR,"\"%s\": cons expected",curr_fn->sym);}
static inline cell* car(const cell* c){if (!c||c->type!=TYPE_CONS) cons_expected();return c->car;}
static inline cell* cdr(const cell* c){if (!c||c->type!=TYPE_CONS) cons_expected();return c->cdr;}
void toomanyparms(const char * m){yl_lerror_ss(LISP_ERROR,"%s in \"%s\": too many parameters",m,curr_fn->sym);}
void wrongnparms(const char * m){yl_lerror_ss(LISP_ERROR,"%s in \"%s\": wrong number of parameters",m,curr_fn->sym);}
static inline void CHECK1PRM(const cell* x,const char* m){if (count_params(x)!=1) wrongnparms(m);}
static inline void CHECK2PRM(const cell* x,const char* m){if (count_params(x)!=2) wrongnparms(m);}
static inline void CHECKNPRM(const cell* x,const int mi,const int ma,const char* m){int n=count_params(x); if (n<mi || ma<n) wrongnparms(m);}
static inline void CHECK1PRMN(const int n,const char* m) {if(n!=1) wrongnparms(m);}
static inline void CHECK2PRMN(const int n,const char* m) {if(n!=2) wrongnparms(m);}
static inline void CHECKNPRMN(const int n,const int mi,const int ma,const char* m) {if(n<mi || ma<n) wrongnparms(m);}
#define CURRFN(x) curr_fn=x;
#define SAVE_CURRFN(x) cell* x=curr_fn;
#else
#define car(x) (x)->car //inline cell* car(cell* x){return x->car;}
#define cdr(x) (x)->cdr //inline cell* cdr(cell* x){return x->cdr;}
#define CHECK1PRM(a,m)
#define CHECK2PRM(a,m)
#define CHECKNPRM(a,mi,ma,m)
#define CHECK1PRMN(n,m)
#define CHECK2PRMN(n,m)
#define CHECKNPRMN(n,mi,ma,m)
#define CURRFN(x)
#define SAVE_CURRFN(x)
#endif

static cell* bi_atomS(int n){
  CHECK1PRMN(n,"atom");
  return (atom(yl_stk[yl_sp-1])?t_atom:0);
}

static cell* bi_nullS(int n){
  CHECK1PRMN(n,"null");
  return (yl_stk[yl_sp-1]?0:t_atom);
}

static cell* bi_numpS(int n){
  CHECK1PRMN(n,"nump");
  const cell* x=yl_stk[yl_sp-1];
  return (x && x->type==TYPE_NUM)?t_atom:0;
}

static cell* bi_strpS(int n){
  CHECK1PRMN(n,"strp");
  const cell* x=yl_stk[yl_sp-1];
  return (x && x->type==TYPE_STR)?t_atom:0;
}

static cell* bi_sympS(int n){
  CHECK1PRMN(n,"symp");
  const cell* x=yl_stk[yl_sp-1];
  return (x && (x->type==TYPE_SYM || x->type==TYPE_KEYWORD))?t_atom:0;
}

static cell* bi_celltypeS(int n){
  CHECK1PRMN(n,"celltype");
  const cell* x=yl_stk[yl_sp-1];
  if (x) return mk_num(x->type);
  return 0;
}

static cell* bi_rplacaS(int n){
  CHECK2PRMN(n,"rplaca");
  cell* c=yl_stk[yl_sp-2],*v=yl_stk[yl_sp-1];
  if (!c || c->type) yl_lerror(LISP_ERROR,"rplaca: cons expected");
  return rplaca(c,v);
}

static cell* bi_rplacdS(int n){
  CHECK2PRMN(n,"rplacd");
  cell* c=yl_stk[yl_sp-2],*v=yl_stk[yl_sp-1];
  if (!c || c->type) yl_lerror(LISP_ERROR,"rplacd: cons expected");
  return rplacd(c,v);
}

static int eq(const cell* v1,const cell* v2){
  if (!v1 || !v2) return (v1==v2);
  if (is_num(v1) && is_num(v2)) return (v1->value==v2->value);
  if (is_str(v1) && is_str(v2)) return (strcmp(v1->str,v2->str)==0);
  return (v1==v2);
}

static cell* bi_eqS(int n){
  const cell* v1=yl_stk[yl_sp-2];
  const cell* v2=yl_stk[yl_sp-1];
  CHECK2PRMN(n,"eq");
  return (eq(v1,v2)?t_atom:0);
}

static int equal(const cell* v1,const cell* v2){
  if (atom(v1)) return eq(v1,v2);
  if (atom(v2)) return 0; // v1 non è un atomo e v2 si
  return equal(car(v1),car(v2)) && equal(cdr(v1),cdr(v2));
}

static cell* bi_equalS(const int n){
  const cell* v1=yl_stk[yl_sp-2];
  const cell* v2=yl_stk[yl_sp-1];
  CHECK2PRMN(n,"equal");
  return (equal(v1,v2)?t_atom:0);
}

static cell* bi_neS(const int n){
  CHECK2PRMN(n,"ne");
  return (bi_eqS(n)?0:t_atom);
}

static cell* bi_carS(const int n){
  const cell* c=yl_stk[yl_sp-1];
  CHECK1PRMN(n,"car");
  if (!c) return 0; // car(nil) -> nil , come in common lisp
#ifdef SAFE_CXR
  CHECK_0(ATOM(c),LISP_ERROR,"applying \"car\" to an atom");
#endif
  return c->car;
}

static cell* bi_cdrS(const int n){
  const cell* c=yl_stk[yl_sp-1];
  CHECK1PRMN(n,"cdr");
  if (!c) return 0; // cdr(nil) -> nil , come in common lisp
#ifdef SAFE_CXR
  CHECK_0(ATOM(c),LISP_ERROR,"applying \"cdr\" to an atom");
#endif
  return c->cdr;
}

static cell* bi_cxxxrS(const int n,const char* sym){
  cell* c=yl_stk[yl_sp-1];
  //char* sym=current_fn->sym;
  CHECK1PRMN(n,"cxxxr");
  int i,l=strlen(sym);
  for(i=l-1;i>0;i--){
    if(sym[i]=='a') c=car(c);
    else if(sym[i]=='d') c=cdr(c);
  }
  return c;
}

static cell* bi_consS(const int n){
  CHECK2PRMN(n,"cons");
  return mk_cons(yl_stk[yl_sp-2],yl_stk[yl_sp-1]);
}

static inline int get_num(const cell* n,const char* op){
  CHECK_S(!n || !is_num(n),LISP_ERROR,"%s: number expected",op);
  return n->value;
}

static cell* math_addS(int n){
  int r=get_num(yl_stk[yl_sp-n],"+");
  n--;
  while (n){
    r+=get_num(yl_stk[yl_sp-n],"+");
    n--;
  }
  return mk_num(r);
}

static cell* bi_subS(int n){
  int r=get_num(yl_stk[yl_sp-n],"-");
  n--;
  if (!n) r=-r;
  while(n){
    r-=get_num(yl_stk[yl_sp-n],"-");
    n--;
  }
  return mk_num(r);
}

static cell* bi_multS(int n){
  int r=get_num(yl_stk[yl_sp-n],"-");
  n--;
  while(n){
    r*=get_num(yl_stk[yl_sp-n],"-");
    n--;
  }
  return mk_num(r);
}

static cell* bi_divS(int n){
  int r=get_num(yl_stk[yl_sp-n],"/");
  n--;
  while (n){
    int p=get_num(yl_stk[yl_sp-n],"/");
    if (p==0) yl_lerror_s(LISP_ERROR,"%s: division by 0","/");
    r=r/p;
    n--;
  }
  return mk_num(r);
}

static cell* bi_modS(int n){
  int r=get_num(yl_stk[yl_sp-n],"%");
  n--;
  while (n){
    int p=get_num(yl_stk[yl_sp-n],"%");
    if (p==0) yl_lerror_s(LISP_ERROR,"%s: division by 0","%");
    r=r%p;
    n--;
  }
  return mk_num(r);
}

static cell* bi_powS(int n){
  int r=get_num(yl_stk[yl_sp-n],"^");
  n--;
  while (n){
    int p=get_num(yl_stk[yl_sp-n],"^");
    r=(int)pow(r,p);
    n--;
  }
  return mk_num(r);
}

static cell* bi_addS(int n){
  char* add;
  char nbuff[20];
  if (n && yl_stk[yl_sp-n] && yl_stk[yl_sp-n]->type==TYPE_NUM) return math_addS(n);
  int fixsp=yl_sp;
  char *newstr,*tmp,buff[100]; // un buffer statico per la maggior parte delle operazioni, diventa allocato dinamicamente se la nuova stringa è troppo lunga
  newstr=buff;
  newstr[0]=0;
  int bl=100,l=0,nbl;
  while(n){
    cell *x=yl_stk[fixsp-n];
    if (!x)
      add="nil";
    else switch(x->type){
      case TYPE_STR:add=x->str;break;
      case TYPE_SYM:
      case TYPE_KEYWORD:add=x->sym;break;
      case TYPE_NUM:sprintf(nbuff,"%i",x->value);add=nbuff;break;
      default: if(bl!=100) free(newstr);yl_lerror(LISP_ERROR,"+: unespected type in string addition");
    }
    int strlen_add=strlen(add);
    if (l+strlen_add+1>=bl){
      // la nuova stringa non ci sta ... nuovo buffer
      nbl=l+strlen_add+1;if (nbl<bl*2) nbl=bl*2; //determina la lunghezza del nuovo buffer
      tmp=(char*)malloc(nbl); if (!tmp){if (bl!=100) free(newstr);yl_lerror(SYSTEM_ERROR,"memory exausted adding strings!");}
      strcpy(tmp,newstr);if (bl!=100) free(newstr); //copia il contenuto del buffer nel nuovo buffer e libera il vecchio buffer
      newstr=tmp;bl=nbl; // sposta tutto nel nuovo buffer
    }
    strcat(newstr,add);
    l+=strlen_add;
    n--;
  }
  cell* res=mk_str(newstr);
  if (bl!=100) free(newstr);
  return res;
}

static cell* bi_notS(const int n){
  CHECK1PRMN(n,"not");
  return (yl_stk[yl_sp-1]?0:t_atom);
}

static cell* bi_and(cell* x,cell* a){
  cell* last=t_atom;
  while(x){
    last=eval(car(x),a);
    if(!last) return 0;
    x=x->cdr;
  }
  return last;
}

static cell* bi_or(cell* x,cell* a){
  while(x){
    cell* last=eval(car(x),a);
    if (last) return last;
    x=x->cdr;
  }
  return 0;
}

static cell* bi_ltS(int n){
  cell* v1=yl_stk[yl_sp-2];
  cell* v2=yl_stk[yl_sp-1];
  CHECK2PRMN(n,"lt");
  if (is_num(v1) && is_num(v2)) return (v1->value<v2->value?t_atom:0);
  if (is_sym(v1) && is_sym(v2)) return (strcmp(v1->sym,v2->sym)<0?t_atom:0);
  if (is_str(v1) && is_str(v2)) return (strcmp(v1->str,v2->str)<0?t_atom:0);
  return 0;
}

static cell* bi_leS(int n){
  cell* v1=yl_stk[yl_sp-2];
  cell* v2=yl_stk[yl_sp-1];
  CHECK2PRMN(n,"le");
  if (is_num(v1) && is_num(v2)) return (v1->value<=v2->value?t_atom:0);
  if (is_sym(v1) && is_sym(v2)) return (strcmp(v1->sym,v2->sym)<=0?t_atom:0);
  if (is_str(v1) && is_str(v2)) return (strcmp(v1->str,v2->str)<=0?t_atom:0);
  return 0;
}

static cell* bi_geS(int n){
  cell* v1=yl_stk[yl_sp-2];
  cell* v2=yl_stk[yl_sp-1];
  CHECK2PRMN(n,"ge");
  if (is_num(v1) && is_num(v2)) return (v1->value>=v2->value?t_atom:0);
  if (is_sym(v1) && is_sym(v2)) return (strcmp(v1->sym,v2->sym)>=0?t_atom:0);
  if (is_str(v1) && is_str(v2)) return (strcmp(v1->str,v2->str)>=0?t_atom:0);
  return 0;
}

static cell* bi_gtS(int n){
  cell* v1=yl_stk[yl_sp-2];
  cell* v2=yl_stk[yl_sp-1];
  CHECK2PRMN(n,"gt");
  if (is_num(v1) && is_num(v2)) return (v1->value>v2->value?t_atom:0);
  if (is_sym(v1) && is_sym(v2)) return (strcmp(v1->sym,v2->sym)>0?t_atom:0);
  if (is_str(v1) && is_str(v2)) return (strcmp(v1->str,v2->str)>0?t_atom:0);
  return 0;
}

static cell* bi_rand(int n){
  if (n==0) return mk_num(rand());
  CHECK1PRMN(n,"rand");
  cell* v=yl_stk[yl_sp-1];
  if (!v || !is_num(v) || v->value<=0) yl_lerror(LISP_ERROR,"rand: number (>0) expected");
	return mk_num(rand()%v->value);
}

static cell* bi_randomize(int n){
	if (n==0){
		srand(time(NULL));
	} else {
    CHECK1PRMN(n,"randomize");
    cell* v=yl_stk[yl_sp-1];
    if (!v || !is_num(v) || v->value<=0) yl_lerror(LISP_ERROR,"randomize: number (>0) expected");
		srand(v->value);
	}
	return 0;
}

static cell* bi_lenS(int n){
  CHECK1PRMN(n,"len");
  int l=0;
  cell* x=yl_stk[yl_sp-n];
  if (x && x->type==TYPE_STR) return mk_num(strlen(x->str));
  while(x){
    l++;
    x=cdr(x);
  }
  return mk_num(l);
}

static cell* bi_nthS(int n){
  CHECK2PRMN(n,"nth");
  cell* nc=yl_stk[yl_sp-2];
  cell* l=yl_stk[yl_sp-1];
  if (!nc || nc->type!=TYPE_NUM || nc->value<0) yl_lerror(LISP_ERROR,"nth: number (>=0) expected");
  int v=nc->value;
  while (v-- && l){
    l=cdr(l);
  }
  return (l?car(l):0);
}

static cell* bi_substrS(int n){
  CHECK_I(n<2 || n>3,LISP_ERROR,"substr: 2 or 3 parameters, found %i",n);
  cell* s=yl_stk[yl_sp-n];
  cell* start=yl_stk[yl_sp-n+1];
  if (!s || s->type!=TYPE_STR) yl_lerror(LISP_ERROR,"substr: str expected as first parameter");
  if (!start || start->type!=TYPE_NUM || start->value<0) yl_lerror(LISP_ERROR,"substr: num >0 expected as second parameter");
  int sl=strlen(s->str);
  int p=sl;
  if (start->value<p) p=start->value;
  if (n==2) return mk_str((char*)(s->str+p));
  cell *len=yl_stk[yl_sp-1];
  if(!len || len->type!=TYPE_NUM || len->value<0) yl_lerror(LISP_ERROR,"substr: num >0 expected ad third parameter");
  int l=len->value;
  if (l+p>sl) l=sl-p;
  char c=s->str[p+l];
  s->str[p+l]=0;
  cell* res=mk_str(s->str+p);
  s->str[p+l]=c;
  return res;
}

static cell* bi_atS(int n){
  CHECK2PRMN(n,"at");
  cell* f=yl_stk[yl_sp-2];
  cell* s=yl_stk[yl_sp-1];
  if (!f || f->type!=TYPE_STR) yl_lerror(LISP_ERROR,"at: string expected as first parameter");
  if (!s || (s->type!=TYPE_STR && s->type!=TYPE_SYM && s->type!=TYPE_KEYWORD)) return 0; //yl_lerror(LISP_ERROR,"at: string or symbol expected as second parameter");
  char* ss=s->type==TYPE_STR?s->str:s->sym;
  char* p=strstr(ss,f->str);
  if (!p) return 0;
  return mk_num(p-ss);
}

static int current_stackbase;
static inline cell* popstackbase(cell* x,int old_base){current_stackbase=old_base;return x;}

static cell* setv(cell* name,cell* value,cell* e){
  //cell* e=a;
  CHECK_0(!name || name->type!=TYPE_SYM,LISP_ERROR,"set: not assigning to a symbol");
  if (name->sym[0]=='#'){
    yl_stk[current_stackbase+name->sym[1]-'A']=value;
    return value;
  }
  while(e){
    if (e->car->car==name) {
      rplacd(e->car,value);
      return value;
    }
    e=e->cdr;
  }
  name->globalvalue=value;
  name->globalassigned=1; // quando viene settato un valore globale viene marcato il simbolo
  return value;
}

static cell* bi_set(int n,cell* a){
  cell *value=0;
  int nn=0,base=yl_sp-n;
  while(nn<n){
    cell* name=yl_stk[base+nn];
    nn++;
    if (nn<n)
      value=yl_stk[base+nn];
    else
      value=0;
    nn++;
    setv(name,value,a);
  }
  return value;
}

static cell* bi_setq(cell* x,cell* a){
  cell *value=0;
  int n=0;
  while (x) {
    cell* name=car(x);
    x=x->cdr;
    if(x){
      value=push(eval(car(x),a));
      n++;
      x=cdr(x);
    } else
      value=0;
    setv(name,value,a);
  }
  return popn(value,n);
}

static cell* bi_defun(cell* x,cell* a){
	CHECKNPRM(x,3,3,"defun");
  cell* name=car(x);
  cell* parms=car(cdr(x));
  cell* body=cdr(cdr(x));
  cell* func=mk_cons(lambda_atom,mk_cons(parms,body));
  return pop2(setv(name,push(eval(push(func),a)),a));
}

static cell* bi_defmacro(cell* x,cell* a){
	CHECKNPRM(x,3,3,"defmacro");
  cell* name=car(x);
  cell* parms=car(cdr(x));
  cell* body=cdr(cdr(x));
  cell* macro=swp(mk_cons(macro_atom,push(mk_cons(parms,body))));
  return pop2(setv(name,push(eval(macro,a)),a));
}

static cell* print(int n,const int mode,const int newline){
  cell* last=0;
  while (n){
    last=yl_stk[yl_sp-n];
    if (last && last->type==TYPE_KEYWORD && strcmp(last->sym,":nl")==0) printf("\n");
    else print_sexpr(last,mode);
    n--;
  }
  if (newline) printf("\n");
  return last;
}

static cell* bi_princS(int n){return print(n,0,0);}
static cell* bi_princlnS(int n){return print(n,0,1);}
static cell* bi_printS(int n){return print(n,1,0);}
static cell* bi_printlnS(int n){return print(n,1,1);}

static cell* bi_spacesS(int n){
  CHECK1PRMN(n,"spaces");
  cell* x=yl_stk[yl_sp-1];
  if (x->type!=TYPE_NUM) yl_lerror(LISP_ERROR,"spaces requires a number as parameter.");
  int r=x->value,i;
  if (r<0) r=0;
  char *buff;
  buff=malloc(r+1);
  for(i=0;i<r;i++) buff[i]=' ';
  buff[r]=0;
  cell* res=mk_str(buff);
  free(buff);
  return res;
}

static cell* bi_listS(int n){
  int lsp=yl_sp;
  if (n==0) return 0;
  cell* x=push(mk_cons(yl_stk[lsp-n],0));
  cell* p=x;
  n--;
  while(n){
    rplacd(p,mk_cons(yl_stk[lsp-n],0));
    p=p->cdr;
    n--;
  }
  return pop(x);
}

// costruisce una lista lasciando l' ultimo elemento passato all' ultimo posto anziché aggiungere un nil
static cell* bi_listpS(int n){
  int lsp=yl_sp;
  if (n==0) return 0;
  if (n==1) return yl_stk[lsp-1];
  cell* x=push(mk_cons(yl_stk[lsp-n],0));
  cell* p=x;
  n--;
  while(n>1){
    p->cdr=mk_cons(yl_stk[lsp-n],0);
    p=p->cdr;
    n--;
  }
  rplacd(p,yl_stk[lsp-1]);
  return pop(x);
}

static int bye_value=0;

static cell* bi_byeS(int n){
	CHECKNPRMN(n,0,1,"bye");
  cell* x=(n>0?yl_stk[yl_sp-n]:0);
  if (x && x->type==TYPE_NUM) bye_value=x->value;
  longjmp(yl_mainloop,BYE_JMP);
  return(0);
}

static cell* bi_eval(int n,cell* a){
  cell *res,*exp;
  if (n==2){
    cell* env;
    // eval con l' ambiente specificato
    exp=yl_stk[yl_sp-2];
    env=yl_stk[yl_sp-1];
    res=eval(exp,env);
  } else {
    // eval nell' ambiente di default
    CHECK1PRMN(n,"eval");
    exp=yl_stk[yl_sp-1];
    res=eval(exp,a);
  }
  return res;
}

static cell* bi_apply(const int n,cell* a){
  CHECK2PRMN(n,"apply");
  cell* x=yl_stk[yl_sp-1];
  cell* fncquotelist=push(mk_cons(yl_stk[yl_sp-2],0)),*p=fncquotelist;
  while(x){
    rplacd(p,mk_cons(mk_cons(quote_atom,mk_cons(car(x),0)),0));
    p=p->cdr;
    x=x->cdr;
  }
  return pop(eval(fncquotelist,a));
}

static cell* bi_quote(cell* x,cell* a){
  CHECK1PRM(x,"quote");
  return car(x);
}

static cell* bi_cond(cell* x,cell* a){
  while(x){ //ATTENZIONE:  questa versione di cond torna NIL se nessun caso è vero (come common lisp)
#ifdef TAILCALL
    if (car(car(x))==else_atom) return mk_trampoline(car(x->car->cdr), a);
    if (eval(x->car->car, a)) return mk_trampoline(car(x->car->cdr), a);
#else
    if (car(car(x))==else_atom) return eval(car(x->car->cdr), a);
    if (eval(x->car->car, a)) return eval(car(x->car->cdr), a);
#endif
    x=x->cdr;
  }
  return 0;
}

static cell* bi_let(cell* x,cell* a){
  cell* res=push(a);
  cell* na=push(a);
  if (x && atom(x->car)) {
    // named let
    CHECKNPRM(x,3,3,"named let");
    cell* l=car(x);
    if (!is_sym(l)) yl_lerror(LISP_ERROR,"named let requires a symbol");
    // tail version
    cell* loop_sym=mk_namedlet(l);
    na=swp(mk_cons(mk_cons(l,loop_sym),na)); // qui va il trampolino per il loop
    // func version
    cell* loopname=l;
    cell* loopfnprms=swp(mk_cons(0,0));
    push(na);
    cell* loopfnprmsstart=loopfnprms;
    cell* loopfnbody=car(cdr(cdr(x)));
    //
    cell* basea=na;
    l=car(x->cdr);
    while (l) {
      cell* car_l=car(l);
      if (atom(car_l)){  // sintassi che dichiara variabili messe a nil ...
        na=swp(mk_cons(mk_cons(car_l,0),na));
        // func version
        loopfnprms->cdr=mk_cons(car_l,0);
        loopfnprms=loopfnprms->cdr;
        //
      } else {
        cell* n=car(car_l);
        cell* v=eval(car(car_l->cdr),a); // this is for let, using "na" implements "let*"
        na=swp(mk_cons(mk_cons(n,v),na));
        // func version
        loopfnprms->cdr=mk_cons(car(car_l),0);
        loopfnprms=loopfnprms->cdr;
        //
      }
      l=l->cdr;
    }
    // func version
    na=pop(na);
    loopfnprms=pop(loopfnprms);
    push(na);
    push(loopfnprms);
    cell* clo=push(mk_cons(mk_cons(loopname,0),na));
    cell* loopfn=swp(mk_cons(lambda_atom,mk_cons(loopfnprmsstart->cdr,mk_cons(loopfnbody,clo))));
    clo->car->cdr=loopfn;
    //print_sexpr(loopfn,1);printf("\n");
    pop2(0);
    na=swp(mk_cons(mk_cons(loopname,loopfn),na));
    //print_sexpr(na,1);printf("\n");
    //
    int loop=1;
    cell* fn=curr_fn;
    while (loop) {
      res=pop2(cdr(x->cdr)?eval(car(x->cdr->cdr),na):0);
      if (res && is_cons(res) && car(res)==loop_sym) {
        res=push(cdr(res));
        na=push(basea);
        l=car(x->cdr);
        while(l){
          cell* car_l=car(l);
          if (!res || !is_cons(res)) yl_lerror_ss(LISP_ERROR,"named let \"%s\" recursion in \"%s\" with too few parameters",curr_fn->sym,fn->sym);
          if (atom(car_l)){
            na=swp(mk_cons(mk_cons(car_l,car(res)),na));
          } else {
            cell* n=car(car_l);
            cell* v=car(res);
            na=swp(mk_cons(mk_cons(n,v),na));
          }
          l=l->cdr;
          res=res->cdr;
        }
        if (res) yl_lerror_ss(LISP_ERROR,"named let \"%s\" recursion in \"%s\" with too many parameters",curr_fn->sym,fn->sym);
      } else {
        loop=0;
      }
    }
    curr_fn=fn;
    return res;
  } else {
    // let
    CHECK2PRM(x,"let");
    cell* l=car(x);
    while (l){
      cell* car_l=car(l);
      if (atom(car_l)){  // sintassi che dichiara variabili messe a nil ...
        na=swp(mk_cons(mk_cons(car_l,0),na));
      } else {
        cell* n=car(car_l);
        cell* v=eval(car(car_l->cdr),a); // this is for let, using "na" implements "let*"
        na=swp(mk_cons(mk_cons(n,v),na));
      }
      l=l->cdr;
    }
#ifdef TAILCALL
    return pop2(cdr(x)?mk_trampoline(car(x->cdr),na):0);
#else
    return pop2(cdr(x)?eval(car(x->cdr),na):0);
#endif
	}
}

static cell* bi_do(cell* x,cell* a){
	CHECKNPRM(x,2,3,"do");
  cell* na=push(a);
  cell* do_vars=car(x);
  cell* do_test=car(car(x->cdr));
  cell* do_result=cdr(car(x->cdr));
  cell* do_body=cdr(x->cdr);
  while (do_vars){
    cell* car_l=car(do_vars);
    if(atom(car_l)){
      // caso di variabile senza inizializzazione
      na=swp(mk_cons(mk_cons(car_l,0),na));
    } else {
      cell* n=car(car_l);
      cell* v=eval(car(car_l->cdr),a);
      na=swp(mk_cons(mk_cons(n,v),na));
    }
    do_vars=do_vars->cdr;
  }
  int loop=1;
  cell* test_result;
  cell* res=0;
  cell* nna;
  while (loop){
    test_result=eval(do_test,na); //valuta il test, se è vero esce
    loop=(test_result==0);
    if (loop){
      // valuta il corpo
      if (do_body) eval(car(do_body),na);
      //esegue lo step delle variabili
      nna=push(a);
      do_vars=car(x);
      while(do_vars){
        cell* car_l=car(do_vars);
        if (is_cons(car_l)){
          cell* n=car(car_l);
          if (!cdr(car_l->cdr)){
            // variabile con solo inizializzazione
            nna=swp(mk_cons(mk_cons(n,assq_cdr(n,na)),nna));
          } else {
            // variabile con step
            cell* v=eval(car(cdr(car_l->cdr)),na);
            nna=swp(mk_cons(mk_cons(n,v),nna));
          }
        } else {
          // variabile con solo dichiarazione
          nna=swp(mk_cons(mk_cons(car_l,assq_cdr(car_l,na)),nna));
        }
        do_vars=do_vars->cdr;
      }
      // pronto il nuovo ambiente, sostituisce il vecchio
      pop(nna);pop(na);
      na=push(nna);
    } else {
      // valuta l'espressione di risultato
      res=(do_result?eval(car(do_result),na):0);
    }
  }
  return pop(res);
}

static inline cell* append(cell* a,cell* b){ // da errore di segmentazione se non sono liste!!!
  if (!a) return b;
  if (!b) return a;
  push(b);
  cell* res=push(mk_cons(car(a),0));
  cell* n=res;
  a=cdr(a);
  while (a){
    rplacd(n,mk_cons(a->car,0));
    n=n->cdr;
    if (a->type!=TYPE_CONS) yl_lerror(LISP_ERROR,"append: first expression is not a list");
    a=a->cdr;
  }
  rplacd(n,b);
  return pop2(res);
}

static cell* bi_appendS(int n){
  if (n==0) return(0);
  int lsp=yl_sp;
  cell* res=push(yl_stk[lsp-n]);
  n--;
  while(n){
    res=swp(append(res,yl_stk[lsp-n]));
    n--;
  }
  return pop(res);
}

static cell* bi_reverseS(const int n){
  CHECK1PRMN(n,"reverse");
  cell* l=yl_stk[yl_sp-1];
  if(!l) return 0;
  cell* res=mk_cons(car(l),0);
  l=l->cdr;
  while(l){
    res=mk_cons(car(l),res);
    l=l->cdr;
  }
  return res;
}

static cell* bi_removeS(const int n){
  CHECK2PRMN(n,"remove");
  cell* x=yl_stk[yl_sp-2];
  cell* l=yl_stk[yl_sp-1];
  cell* res=push(mk_cons(0,0)),*p=res;
  while(l){
    if(!eq(car(l),x)){
      rplacd(p,mk_cons(l->car,0));
      p=p->cdr;
    }
    l=l->cdr;
  }
  return pop(res->cdr);
}

static cell* bi_prog1(cell* x,cell* a){
  cell* first=0;
  if (x && car(x)) {
		first=eval(x->car,a);
	  x=x->cdr;
	}
  while (x) {
    eval(car(x),a);
    x=x->cdr;
  }
  return first;
}

static cell* bi_progn(cell* x,cell* a){
  cell* last=0;
  while (x) {
    last=eval(car(x),a);
    x=x->cdr;
  }
  return last;
}

static cell* bi_while(cell* x,cell* a){
  CHECKNPRM(x,2,3,"while");
  cell* cond=car(x);
  cell* body=car(x->cdr);
  cell* result=x->cdr->cdr;
  cell* l=push(0);
  while (eval(cond,a)){
    l=swp(eval(body,a));
  }
  if (result && result->type==TYPE_CONS && !result->cdr)
    l=swp(eval(result->car,a));
  return pop(l);
}

static cell* bi_if(cell* x,cell* a){
	CHECKNPRM(x,2,3,"if");
  if (eval(car(x),a))
#ifdef TAILCALL
    return mk_trampoline(car(x->cdr),a);
#else
    return eval(car(x->cdr),a);
#endif
  if (!cdr(x->cdr)) return 0; // without else
#ifdef TAILCALL
  return mk_trampoline(car(x->cdr->cdr),a);
#else
  return eval(car(x->cdr->cdr),a);
#endif
}

static cell* bi_dotimes(cell* x,cell* a){
  cell* var=car(car(x));
  cell* endv=eval(car(cdr(x->car)),a);
  cell* res=x->car->cdr->cdr;
  if (!var || !is_sym(var)) yl_lerror(LISP_ERROR,"\"dotimes\" var expected");
  if (!is_num(endv) || endv->value<0) yl_lerror(LISP_ERROR,"\"dotimes\" end value:positive number expected");
  if (!atom(res)) res=res->car;
  int i,l=endv->value;
  cell* loopcounter=mk_num(0);
  cell* loopvar=mk_cons(var,loopcounter); // crea la variabile di loop
  a=push(mk_cons(loopvar,a)); // la aggiunge all' ambiente corrente
  cell* body;
  for(i=0;i<l;i++){
    loopcounter->value=i;
    body=x->cdr;
    while (body){
      eval(car(body),a);
      body=body->cdr;
    }
  }
  rplacd(loopvar,mk_num(i));
  return pop(res?eval(res,a):0);
}

static cell* bi_dolist(cell* x,cell* a){
  cell* var=car(car(x));
  cell* res=x->car->cdr->cdr;
  if (!var || !is_sym(var)) yl_lerror(LISP_ERROR,"\"dolist\" var expected");
  if (!atom(res)) res=res->car;
  cell* loopvar=push(mk_cons(var,0));
  cell* body;
  a=push(mk_cons(loopvar,a));
  cell* lst=push(eval(car(cdr(x->car)),a));
  while(lst){
    rplacd(loopvar,car(lst));
    lst=cdr(lst);
    body=x->cdr;
    while (body){
     eval(car(body),a);
     body=body->cdr;
    }
  }
  rplacd(loopvar,0);
  return popn(res?eval(res,a):0,3);
}

static cell* bi_map(const int n,cell* a){
  CHECK2PRMN(n,"map");
  cell* fnc=yl_stk[yl_sp-2];
  cell* lst=yl_stk[yl_sp-1];
  cell* res=push(mk_cons(0,0));
  cell* p=res;
  cell* qv=mk_cons(0,0);
  fnc=push(mk_cons(fnc,mk_cons(mk_cons(quote_atom,qv),0)));
  while(lst){
    rplaca(qv,car(lst));
    cell* v=eval(fnc,a);
    rplacd(p,mk_cons(v,0));
    p=p->cdr;
    lst=lst->cdr;
  }
  return pop2(res->cdr);
}

static cell* bi_mapcar(const int n,cell* a){
  if (n>50) yl_lerror(LISP_ERROR,"\"mapcar\": function cannot have more than 50 args");
  cell* fncquotelist=push(mk_cons(yl_stk[yl_sp-n],0));
  cell* p=fncquotelist;
  cell* tmp;
  cell* lst[50];
  int i,stop=0;
  for(i=0;i<n-1;i++){
    tmp=mk_cons(mk_cons(quote_atom,mk_cons(0,0)),0);
    rplacd(p,tmp);
    p=p->cdr;
    lst[i]=yl_stk[yl_sp-n+i];
    stop=stop || lst[i]==0;
  }
  cell* res=push(mk_cons(0,0));
  cell* pp=res;
  while(!stop){
    p=fncquotelist;
    for(i=0;i<n-1;i++){ // riempie la lista dei parametri quotati
      rplaca(p->cdr->car->cdr,car(lst[i]));
      p=p->cdr;
    }
    rplacd(pp,mk_cons(eval(fncquotelist,a),0));
    pp=pp->cdr;
    for(i=0;i<n-1;i++){
      lst[i]=cdr(lst[i]);
      stop=stop || lst[i]==0;
    }
  }
  return pop2(res->cdr);
}

static cell* bi_filter(const int n,cell* a){
  CHECK2PRMN(n,"filter");
  cell* fnc=yl_stk[yl_sp-2];
  cell* lst=yl_stk[yl_sp-1];
  cell* res=push(mk_cons(0,0));
  cell* p=res;
  cell* qv=mk_cons(0,0);
  cell* fncquotelist=push(mk_cons(fnc,mk_cons(mk_cons(quote_atom,qv),0)));
  while(lst){
    rplaca(qv,car(lst));
    if (eval(fncquotelist,a)){
      rplacd(p,mk_cons(lst->car,0));
      p=p->cdr;
    }
    lst=lst->cdr;
  }
  return pop2(res->cdr);
}

static inline cell* assoc(const cell* x, cell* l){
  while (l){
    if (eq(x,car(car(l)))) return l->car;
    l=l->cdr;
  }
  return 0;
}

static cell* bi_assocS(const int n){
  CHECK2PRMN(n,"assoc");
  cell *x=yl_stk[yl_sp-2],*l=yl_stk[yl_sp-1];
  return assoc(x,l);
}

static cell* bi_pairlisS(const int n){
  CHECKNPRMN(n,3,3,"pairlis");
  cell *x=yl_stk[yl_sp-3],*y=yl_stk[yl_sp-2],*a=yl_stk[yl_sp-1];
  if (!x && !y) return a;
  cell* res=push(mk_cons(0,0)),*pl=res,*tmp;
  while(x){
    if (ATOM(x)){
      tmp=mk_cons(mk_cons(x,y),0);
      x=y=0;
    } else {
      tmp=mk_cons(mk_cons(car(x),car(y)),0);
      x=x->cdr;
      y=y->cdr;
    }
    rplacd(pl,tmp);
    pl=tmp;
  }
  rplacd(pl,a);
  return pop(res->cdr);
}

static inline cell* member(cell* i,cell* l){
  while(l){
    if (ATOM(l)) return 0;
    if (eq(car(l),i)) return l;
    l=l->cdr;
  }
  return 0;
}

static cell* bi_memberS(const int n){
  CHECK2PRMN(n,"member");
  cell *i=yl_stk[yl_sp-2],*l=yl_stk[yl_sp-1];
  return member(i,l);
}

static cell* load(cell* n,cell* report){
  FILE* f=0;
  if (is_sym(n)) f=fopen(n->sym,"r");
  else if (is_str(n)) f=fopen(n->str,"r");
  int mode=(report ? (report->type==TYPE_NUM?report->value:1):0);
  if (f) {
    while(!feof(f)){
			curr_fn=anon_atom;
      n=read_sexpr(f);
      if (mode>=2){printf(" in:");print_sexpr(n,1);printf("\n");}
      n=eval(n,0);
      if (mode>=1){printf("out:");print_sexpr(n,1);printf("\n");}
    }
    fclose(f);
    return t_atom;
  }
  return 0;
}

static cell* bi_loadS(const int n){
  CHECK_0(n==0,LISP_ERROR,"load: missing file name");
  cell* name=yl_stk[yl_sp-n];
  cell* report=(n>1?yl_stk[yl_sp-n+1]:0);
  return load(name,report);
}

#ifdef _WIN32
#include <windows.h>
//extern unsigned long GetTickCount();
#else
#include <time.h>
#include <sys/timeb.h>
#endif // _WIN32

static int getMillisec(){
#ifdef _WIN32
  return GetTickCount();
#else
#ifdef __MACH__
  //struct timeb tb;
  //ftime(&tb);
  //return tb.millitm+(tb.time&0xfffff)*1000;
  return clock()/(CLOCKS_PER_SEC/1000);
#else
  struct timespec t;
  clock_gettime(CLOCK_REALTIME,&t);
  return (t.tv_sec*1000+t.tv_nsec/1000000);
#endif
#endif
}

static cell* bi_time(cell* x, cell* a){
  int s=getMillisec();
  eval(car(x),a);
  return mk_num(getMillisec()-s);
}

static cell* bi_millisecS(const int n){
  return mk_num(getMillisec());
}

static cell* bi_lexicalscopingS(const int n){
#ifdef LEXICAL_SCOPING
  return t_atom;
#else
   return 0;
#endif // LEXICAL_SCOPING
}

static cell* bi_tailcallS(const int n){
#ifdef TAILCALL
  return t_atom;
#else
   return 0;
#endif
}

static cell* bi_env(cell* x,cell* a){
  if (x && x->type==TYPE_CONS && x->car && x->car->type==TYPE_NUM && x->car->value==1)
    return a; // con parametro 1 torna l' ambiente locale
  // altrimenti torna l' ambiente globale
  int i;
  cell* res=push(0);
  // ------ DA FARE ----- !!!!
  for(i=0;i<yl_nsyms;i++){
    cell* c=&yl_fsb->syms[i];
    if (c->type==TYPE_SYM && c->globalassigned){
      res=swp(mk_cons(mk_cons(c,c->globalvalue),res));
    }
  }
  return pop(res);
}

static cell* bi_errorS(const int n){
  cell* x=(n>0?yl_stk[yl_sp-n]:0);
  if (x && x->type==TYPE_STR) yl_lerror(LISP_ERROR,x->str);
  yl_lerror(LISP_ERROR,"user error");
  return 0;
}

static cell* bi_gcS(const int n){
#ifdef DEBUG_GC
  yl_stopping=1;
  yl_gc();
  yl_stopping=0;
#else
  yl_gc();
#endif
  int fcells=0,acells,asyms;
  cell* c=yl_free_cells;
  while(c){
    fcells++;
    c=NEXTFREECELL(c);
  }
  acells=yl_nblocks*MAX_CELLS-fcells;
  asyms=(yl_nsymsblocks-1)*MAX_SYMS+yl_nsyms;
  if (n>0) printf("%i allocated cells, %i active cells, %i symbols, %i gc executions\n",yl_nblocks*MAX_CELLS,acells,asyms,yl_ngc);
  return pop(mk_cons(push(mk_num(acells)),mk_num(yl_nblocks*MAX_CELLS)));
}

#ifdef LEXICAL_SCOPING
static inline cell* make_closure(const cell* f,cell* a){ // build a closure from lambda, macro, label
  cell *body=mk_cons(car(cdr(cdr(f))),(a?a:invisible_atom)); // body.env
  cell *res=mk_cons(f->car,mk_cons(f->cdr->car,body));
  return res;
}
static inline cell* get_closure(const cell* f,cell* a){ // get closure enviriment
  cell* env=f->cdr->cdr->cdr;
  if (env) return (env==invisible_atom?0:env);
  return a;
}
#define SCOPING_MODE "Lexical scoping\n"
#else
#define make_closure(x,a) (x)
#define get_closure(f,a) (a)
#define SCOPING_MODE "Dynamic scoping\n"
#endif

static inline cell* evlis(cell* m,cell* a) {
  if (!m) return 0;
  CHECK_0(m->type!=TYPE_CONS,LISP_ERROR,"list expected");
  cell *c=push(mk_cons(eval(m->car,a),0)); // iterative version
  cell *p=c;
  m=m->cdr;
  while(m){
    CHECK_0(m->type!=TYPE_CONS,LISP_ERROR,"list expected");
    p->cdr=mk_cons(eval(m->car,a),0);
    p=p->cdr;
    m=m->cdr;
  }
  return pop(c);
}

static inline int evstack(cell* m,cell* a){
  int n=0;
  while(m){
    CHECK_0(m->type!=TYPE_CONS,LISP_ERROR,"list expected");
    push(eval(m->car,a));
    m=m->cdr;
    n++;
  }
  return n;
}

static inline int evstackcnt(cell* m,cell* a,int nparms,const int rest){
  int n=0;
  while(nparms){
    CHECK_0(!m || m->type!=TYPE_CONS,LISP_ERROR,"list expected");
    push(eval(car(m),a));
    m=m->cdr;
    n++;
    nparms--;
  }
  if (m) {
    if (rest){
      cell* r=push(mk_cons(eval(car(m),a),0)),*p=r;
      m=m->cdr;
      while(m){
        rplacd(p,mk_cons(eval(car(m),a),0));
        m=m->cdr;
        p=p->cdr;
      }
    } else
     yl_lerror(LISP_ERROR,"too many parameters");
  } else if(rest)
    push(0);
  return n;
}

static inline cell* pairlis(cell* x, cell* y,cell* a) {
  // ATTENZIONE: questa versione gira la lista X Y Z che viene messa nell' ambiente come Z Y X
  SAVE_CURRFN(cfn);
  cell* res=push(a);
  while(x){
    if (ATOM(x)){
      res=swp(mk_cons(mk_cons(x,y),res));
      x=y=0;
    } else {
      CHECK_S(!y,LISP_ERROR,"\"%s\": too few arguments",cfn->sym);
      res=swp(mk_cons(mk_cons(car(x),car(y)),res));
      x=x->cdr;
      y=y->cdr;
    }
  }
  CHECK_S(y,LISP_ERROR,"\"%s\": too many arguments",cfn->sym);
  return pop(res);
}

static inline cell* assq_cdr(const cell* x,const cell* a) {
  if (x->str[0]=='#') // gestione delle variabili locali nello stack
    return yl_stk[current_stackbase+x->str[1]-'A'];
  // search in current environment
  while (a) {
    if (a->car->car==x) return a->car->cdr;
    a=a->cdr;
  }
  // and then in global environment
  if (!x->globalassigned) yl_lerror_s(LISP_ERROR,"variable \"%s\" not found",x->sym);
  return x->globalvalue;
}

static inline cell* ypa(cell* x, cell* y,cell* a, cell* env) {
  // ATTENZIONE: questa versione gira la lista X Y Z che viene messa nell' ambiente come Z Y X
  SAVE_CURRFN(cfn);
  cell* res=push(env);
  while(x){
    if (ATOM(x)){
      res=swp(mk_cons(mk_cons(x,evlis(y,a)),res));
      x=y=0;
    } else {
      CHECK_S(!y,LISP_ERROR,"\"%s\": too few arguments",cfn->sym);
      res=swp(mk_cons(mk_cons(car(x),eval(car(y),a)),res));
      x=x->cdr;
      y=y->cdr;
    }
  }
  CHECK_S(y,LISP_ERROR,"\"%s\": too many arguments",cfn->sym);
  return pop(res);
}

#ifdef EVAL_FUNCPTR

static cell*(*apply_by_type[20])(cell*,cell*,cell*);
static cell*(*applycons_by_type[20])(cell*,cell*,cell*);
static cell* apply_error(cell* fn,cell* x,cell* a){yl_lerror(SYSTEM_ERROR,"apply?");return 0;}
static cell* apply_num(cell* fn,cell* x,cell* a){yl_lerror_i(LISP_ERROR,"%i is not a function",fn->value);return 0;}
static cell* apply_str(cell* fn,cell* x,cell* a){yl_lerror_s(LISP_ERROR,"\"%s\" is not a function",fn->str);return 0;}
static cell* apply_keyword(cell* fn,cell* x,cell* a){yl_lerror_s(LISP_ERROR,"%s is a keyword, not a function",fn->sym);return 0;};

static cell* apply_sym(cell* fn,cell* x,cell* a){
  CURRFN(fn);
  return apply(assq_cdr(fn, a),x,a);
}

static cell* apply_lambda(cell* fn,cell* x,cell* a){
  int n=evstack(x,a);
  CURRFN(fn);
  return popn(fn->builtinlambda(n,a),n);
}

static cell* apply_macro(cell* fn,cell* x,cell* a){
  return fn->builtinmacro(x,a);
}

static cell* apply_stack(cell* fn,cell* x,cell* a){
  int n=evstack(x,a);
  //CURRFN(fn);
  return popn(fn->builtinstack(n),n);
}

static cell* apply_cxr(cell* fn,cell* x,cell* a){
  int n=evstack(x,a);
  //CURRFN(fn);
  return popn(bi_cxxxrS(n,fn->sym),n);
}

static cell* apply_lambdatype(cell* fn,cell* x,cell* a){
#ifdef TAILCALL
  return mk_trampoline(car(cdr(cdr(fn))),ypa(car(cdr(fn)),x,a,get_closure(fn,a)));
#else
  return eval(car(cdr(cdr(fn))),ypa(car(cdr(fn)),x,a,get_closure(fn,a)));
#endif
}

static cell* apply_macrotype(cell* fn,cell* x,cell* a){
  return pop(eval(swp(eval(car(cdr(cdr(fn))), push(pairlis(car(cdr(fn)), x, get_closure(fn,a) )))), a));
  //cell* m=swp(eval(car(cdr(cdr(fn))), push(pairlis(car(cdr(fn)), x, get_closure(fn,a) ))));showdbg("m",m);showdbg("a",a);cell* r=eval(m,a);showdbg("r",r);return pop(r);
}

static cell* apply_labeltype(cell* fn,cell* x,cell* a){
  return pop(apply(car(cdr(cdr(fn))), x, swp(mk_cons( push(mk_cons(car(cdr(fn)), car(cdr(cdr(fn))))), get_closure(fn,a) ))));
}

static cell* apply_nolambdatype(cell* fn,cell* x,cell* a){
  return pop(apply(push(eval(fn,a)),x,a)); //this is for "SCHEME like" evaluation
}
#endif // EVAL_FUNCPTR

static cell* apply_stacklambdatype(cell* fn,cell* x,cell* a){
  int lsp=yl_sp;
  CHECK_S(!car(car(cdr(fn))) || car(car(cdr(fn)))->type!=TYPE_NUM,LISP_ERROR,"\"%s\" wrong parameters definition",curr_fn->str);
  int nparms=fn->cdr->car->car->value;
  int stackspace=fn->cdr->car->cdr->value;
  int n,rest=0;
  if (nparms<0){
    nparms=-nparms-1;
    rest=1;
  }
  n=evstackcnt(x,a,nparms,rest);
  int save_base=current_stackbase;
  current_stackbase=lsp;
  CHECK_S(nparms!=n,LISP_ERROR,"\"%s\" wrong number of parameters",curr_fn->str);
  yl_sp+=stackspace;
  return popstackbase(popn(eval(car(cdr(cdr(fn))),get_closure(fn,a)),n+stackspace+rest),save_base);
}

static cell* apply_stacklambdalaptype(cell* fn,cell* x,cell* a){
  CHECK_S(!car(car(cdr(fn))) || car(car(cdr(fn)))->type!=TYPE_NUM,LISP_ERROR,"\"%s\" wrong parameters definition",curr_fn->str);
  int nparms=fn->cdr->car->car->value;
  int stackspace=fn->cdr->car->cdr->value;
  int n,rest=0;
  if (nparms<0){
    nparms=-nparms-1;
    rest=1;
  }
  n=evstackcnt(x,a,nparms,rest);
  CHECK_S(nparms!=n,LISP_ERROR,"\"%s\" wrong number of parameters",curr_fn->str);
  yl_sp+=stackspace;
  return popn(lap(car(cdr(cdr(fn))),get_closure(fn,a),yl_sp-n),n+stackspace+rest);
}

static cell* apply_letloop(cell* fn,cell* x,cell* a){
	return mk_cons(fn,evlis(x,a));
}

#ifdef EVAL_FUNCPTR
static cell* apply_cons(cell* fn,cell* x,cell* a){
  return applycons_by_type[(int)fn->car->lambdatype](fn,x,a);
}

static inline cell* apply(cell* fn,cell* x,cell* a) {
  CHECKFREECELL(fn)
	//printf("apply:");print_sexpr(fn,1);printf(" args:");print_sexpr(x,1);printf(" env:");print_sexpr(a,1);printf("\n");
  CHECK_0(!fn,LISP_ERROR,"\"nil\" is not a function");
  return apply_by_type[(int)(fn->type)](fn,x,a);
}

static cell* eval(cell* e,cell* a) {
  CHECKFREECELL(e)
  CHECKFREECELL(a)
  //printf("eval ");print_sexpr(e,1);printf(" env:");print_sexpr(a,1);printf("\n");
#ifdef TAILCALL
  tail_call:
#endif
  if (e){
    if (ATOM(e)) {
      if (e->type!=TYPE_SYM)
        return e; // numbers, strings, keywords and builtin are 'autoquoting'
      else
        return assq_cdr(e, a);
    } else {
      CHECK_0(!e->car,LISP_ERROR,"\"nil\" is not a function");
      if(e->car->lambdatype) {//if (e->car==lambda_atom || e->car==macro_atom || e->car==label_atom){
        return make_closure(e,a);
      } else {
#ifdef TAILCALL
        e=pop2(apply(push(e)->car,e->cdr,push(a)));
        if (!e || e->type!=TYPE_TRAMPOLINE) return e;
        a=e->cdr;
        e=e->car;
        goto tail_call;
#else
        return pop2(apply(push(e)->car,e->cdr,push(a)));
#endif
      }
    }
  }
  return 0;
}

#else

static cell* eval(cell* e,cell* a){
  static void* apply_jump[]={&&apply_cons,&&apply_sym,&&apply_keyword,&&apply_num,&&apply_str,&&apply_builtinlambda,
                             &&apply_builtinmacro,&&apply_builtinstack,&&apply_cxr,&&apply_letloop,&&apply_free,&&apply_trampoline};
  //static void* apply_cons[]={&&nolambda,&&lambda,&&macro,&&label,&&slambda,&&slambdalap};
  cell *fn,*x,*res;
  int n;
  tail_call:
  if (e){
    if (ATOM(e)) {
      if (e->type!=TYPE_SYM)
        return e; // numbers, strings, keywords and builtin are 'autoquoting'
      else
        return assq_cdr(e, a);
    } else {
      CHECK_0(!e->car,LISP_ERROR,"\"nil\" is not a function");
      if(e->car->lambdatype) {//if (e->car==lambda_atom || e->car==macro_atom || e->car==label_atom){
        return make_closure(e,a);
      } else {
        fn=e->car;
        x=e->cdr;
        goto apply_push;
      }
    }
  }
  return 0;
  /**/
  apply_push:
  push(a);
  push(x);
  push(fn);
  apply:
  //printf("apply:");print_sexpr(fn,1);printf(" ");print_sexpr(a,1);printf("\n");
  CHECK_0(!fn,LISP_ERROR,"\"nil\" is not a function");
  goto *apply_jump[(int)fn->type];
  apply_builtinlambda: n=evstack(x,a);/*CURRFN(fn)*/;res=popn(fn->builtinlambda(n,a),n);goto exit;
  apply_builtinmacro: res=fn->builtinmacro(x,a);goto exit;
  apply_builtinstack: n=evstack(x,a);/*CURRFN(fn)*/;res=popn(fn->builtinstack(n),n);goto exit;
  apply_cxr: n=evstack(x,a);CURRFN(fn);res=popn(bi_cxxxrS(n,fn->sym),n);goto exit;
	apply_letloop:res=mk_cons(fn,evlis(x,a));goto exit;
  apply_sym: CURRFN(fn);fn=swp(assq_cdr(fn, a));goto apply;
  apply_cons:
    /* geval
    goto *apply_cons[(int)fn->car->lambdatype];
    nolambda:fn=swp(eval(fn,a));goto apply;
    lambda:e=car(cdr(fn->cdr));a=popn(ypa(fn->cdr->car,x,a,get_closure(fn,a)),3);goto tail_call;
    macro:e=popn(eval(car(cdr(fn->cdr)), pairlis(fn->cdr->car, x, get_closure(fn,a) )),3);goto tail_call;
    label:a=mk_cons(push(mk_cons(car(fn->cdr),car(fn->cdr->cdr))),get_closure(fn,a));fn=popn(fn->cdr->cdr->car,4);goto apply_push;
    slambda:res=apply_stacklambdatype(fn,x,a);goto exit;    // !!!
    slambdalap:res=apply_stacklambdalaptype(fn,x,a);goto exit; // !!!
    */
    /* ieval
    n=fn->car->lambdatype;
    if (n==LT_LAMBDA){e=car(cdr(fn->cdr));a=popn(ypa(fn->cdr->car,x,a,get_closure(fn,a)),3);goto tail_call;}
    if (n==LT_SLAMBDA) {res=apply_stacklambdatype(fn,x,a);goto exit;}    // !!!
    if (n==LT_SLAMBDALAP) {res=apply_stacklambdalaptype(fn,x,a);goto exit;} // !!!
    if (n==LT_NOLAMBDA){fn=swp(eval(fn,a));goto apply;}
    if (n==LT_MACRO){e=popn(eval(car(cdr(fn->cdr)), pairlis(fn->cdr->car, x, get_closure(fn,a) )),3);goto tail_call;}
    if (n==LT_LABEL){a=mk_cons(push(mk_cons(car(fn->cdr),car(fn->cdr->cdr))),get_closure(fn,a));fn=popn(fn->cdr->cdr->car,4);goto apply_push;}
    */
    /* seval */
    switch(fn->car->lambdatype){
      case LT_LAMBDA: e=car(cdr(fn->cdr));a=popn(ypa(fn->cdr->car,x,a,get_closure(fn,a)),3);goto tail_call;
      case LT_SLAMBDA: res=apply_stacklambdatype(fn,x,a);goto exit;    // !!!
      case LT_SLAMBDALAP: res=apply_stacklambdalaptype(fn,x,a);goto exit; // !!!
      case LT_NOLAMBDA: fn=swp(eval(fn,a)); goto apply;
      case LT_MACRO: e=popn(eval(car(cdr(fn->cdr)), pairlis(fn->cdr->car, x, get_closure(fn,a) )),3);goto tail_call;
      case LT_LABEL: a=mk_cons(push(mk_cons(car(fn->cdr),car(fn->cdr->cdr))),get_closure(fn,a));fn=popn(fn->cdr->cdr->car,4);goto apply_push;
    }
    /**/
  apply_keyword: yl_lerror_s(LISP_ERROR,"%s is a keyword, not a function",fn->sym);
  apply_num: yl_lerror_i(LISP_ERROR,"%i is not a function",fn->value);
  apply_str: yl_lerror_s(LISP_ERROR,"\"%s\" is not a function",fn->str);
  apply_free: apply_trampoline: yl_lerror(LISP_ERROR,"apply of free or trampoline");
  exit:
#ifdef TAILCALL
  if (res && res->type==TYPE_TRAMPOLINE){a=res->cdr;e=popn(res->car,3);goto tail_call;}
#endif
  return popn(res,3);
}
#endif

#if defined(__GNUC__) || defined(__clang__) || defined(__TINYC__)
#define CALCULATEDGOTO
#endif
#ifdef CALCULATEDGOTO
#define OPLOOP      loop:goto *jumptbl[(int)prg[pc++]]
#define ENDOPLOOP   xop:
#define OP(lbl,ch)  lbl
#define NOP         nop
#define NEXTOP      goto loop;
#define OPJUMPTABLE static void* jumptbl[]={&&xop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop, \
                                            &&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop, \
                                            &&nop,&&exm,&&nop,&&shp,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop, \
                                            &&op0,&&op1,&&op2,&&op3,&&nop,&&nop,&&op6,&&op7,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop, \
                                            &&nop,&&opA,&&opB,&&opC,&&opD,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop, \
                                            &&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&opX,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop, \
                                            &&nop,&&opa,&&opb,&&opc,&&opd,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&nop,&&opl,&&nop,&&nop,&&nop  \
                                           };
#else
#define OPLOOP      while(prg[pc]) switch (prg[pc++]) {
#define ENDOPLOOP   }
#define OP(lbl,ch)  case ch
#define NOP         default
#define NEXTOP      break;
#define OPJUMPTABLE
#endif

static cell* lap(const cell* x,cell* a,const int stackbase){
  if (!x) return 0;
  OPJUMPTABLE;
  int n,pc=0,save_base;
  cell* v;
  char* prg=car(x)->str;
  x=cdr(x);
  OPLOOP;
      OP(exm,'!'): // LOAD CONSTANT
        yl_stk[yl_sp++]=x->car;
        x=x->cdr;
        NEXTOP;
      OP(op0,'0'): // LOAD STACK ...
        yl_stk[yl_sp++]=yl_stk[stackbase+prg[pc++]-'A'];
        NEXTOP;
      OP(op1,'1'): // LOAD STACK 0
        yl_stk[yl_sp++]=yl_stk[stackbase];
        NEXTOP;
      OP(op2,'2'): // LOAD STACK 1
        yl_stk[yl_sp++]=yl_stk[stackbase+1];
        NEXTOP;
      OP(op3,'3'): // LOAD STACK 2
        yl_stk[yl_sp++]=yl_stk[stackbase+2];
        NEXTOP;
      OP(op6,'6'): // LOAD GLOBAL
        yl_stk[yl_sp++]=x->car->globalvalue;
        x=x->cdr;
        NEXTOP;
      OP(op7,'7'): // LOAD
        yl_stk[yl_sp++]=assq_cdr(x->car,a);
        x=x->cdr;
        NEXTOP;
      OP(opA,'A'): // CALL BUILTIN STACK ...
        n=prg[pc++]-'A';
        CURRFN(x->car);
        v=x->car->builtinstack(n);
        yl_sp-=n;yl_stk[yl_sp++]=v;x=x->cdr;
        NEXTOP;
      OP(opB,'B'): // CALL BUILTIN STACK 1 parm
        CURRFN(x->car);
        v=x->car->builtinstack(1);
        yl_stk[yl_sp-1]=v;x=x->cdr;
        NEXTOP;
      OP(opC,'C'): // CALL BUILTIN STACK 2 parms
        CURRFN(x->car);
        v=x->car->builtinstack(2);
        yl_sp--;yl_stk[yl_sp-1]=v;x=x->cdr;
        NEXTOP;
      OP(opD,'D'): // CALL BUILTIN STACK 3 parms
        CURRFN(x->car);
        v=x->car->builtinstack(3);
        yl_sp-=3;yl_stk[yl_sp++]=v;x=x->cdr;
        NEXTOP;
      OP(opX,'X'): // chiamata speciale per le funzioni CxxxxR
        CURRFN(x->car);
        v=bi_cxxxrS(1,x->car->sym);
        yl_stk[yl_sp-1]=v;x=x->cdr;
        NEXTOP;
      OP(opa,'a'): // CALL GLOBAL (#lambdalap)
        n=prg[pc++]-'A';
        CURRFN(x->car);
        v=lap(x->car->globalvalue->cdr->cdr->car,get_closure(x->car->globalvalue,a),yl_sp-n);
        yl_sp-=n;yl_stk[yl_sp++]=v;x=x->cdr;
        NEXTOP;
      OP(opb,'b'): // CALL GLOBAL (stack) 1 parm
        CURRFN(x->car);
        v=lap(x->car->globalvalue->cdr->cdr->car,get_closure(x->car->globalvalue,a),yl_sp-1);
        yl_stk[yl_sp-1]=v;x=x->cdr;
        NEXTOP;
      OP(opc,'c'): // CALL GLOBAL (stack) 2 parms
        CURRFN(x->car);
        v=lap(x->car->globalvalue->cdr->cdr->car,get_closure(x->car->globalvalue,a),yl_sp-2);
        yl_sp--;yl_stk[yl_sp-1]=v;x=x->cdr;
        NEXTOP;
      OP(opd,'d'): // CALL GLOBAL (stack) 3 parms
        CURRFN(x->car);
        v=lap(x->car->globalvalue->cdr->cdr->car,get_closure(x->car->globalvalue,a),yl_sp-3);
        yl_sp-=3;yl_stk[yl_sp++]=v;x=x->cdr;
        NEXTOP;
      OP(opl,'l'): // CALL GLOBAL (#lambda)
        n=prg[pc++]-'A';
        save_base=current_stackbase;current_stackbase=yl_sp-1;
        CURRFN(x->car);
        v=eval(x->car->globalvalue->cdr->cdr->car,get_closure(x->car->globalvalue,a));
        current_stackbase=save_base;
        yl_sp-=n;yl_stk[yl_sp++]=v;x=x->cdr;
        NEXTOP;
      OP(shp,'#'): // IF
        if (yl_stk[--yl_sp]!=0){
          x=x->car;
          pc=0;
          prg=x->car->str;
          x=x->cdr;
        } else {
          x=x->cdr;
        }
        NEXTOP;
      NOP:
        yl_lerror_i(LISP_ERROR,"opcode %i not implemented",x->car->value);
  ENDOPLOOP;
  return yl_stk[--yl_sp];
}

static cell* bi_lap(cell* x, cell* a){
  return lap(x,a,current_stackbase);
}

static cell* bi_lambda_not_impl(int n,cell* x){yl_lerror_s(LISP_ERROR,"\"%s\" function not implemented",curr_fn->sym);return 0;}
//static cell* bi_macro_not_impl(cell* x,cell* a){lerror_s(LISP_ERROR,"\"%s\" macro not implemented",current_fn->sym);return 0;}

static int yl_init(){
  int i,res=0;
  yl_free_cells=0;yl_fcb=0;yl_lcb=0;yl_nblocks=0; // start with no unused cells
  yl_nsyms=0;yl_fsb=0;yl_lsb=0;yl_nsymsblocks=0; // start with an empty symbol table
  yl_ngc=yl_sp=0;
  i=setjmp(yl_mainloop);
  if (!i){
    yl_addCellsBlock(); // create the first cell block
    yl_addSymsBlock();
#ifdef EVAL_FUNCPTR
    // init apply jump table
    apply_by_type[TYPE_NUM]=&apply_num;
    apply_by_type[TYPE_SYM]=&apply_sym;
    apply_by_type[TYPE_KEYWORD]=&apply_keyword;
    apply_by_type[TYPE_STR]=&apply_str;
    apply_by_type[TYPE_BUILTINLAMBDA]=&apply_lambda;
    apply_by_type[TYPE_BUILTINMACRO]=&apply_macro;
    apply_by_type[TYPE_BUILTINSTACK]=&apply_stack;
    apply_by_type[TYPE_CXR]=&apply_cxr;
    apply_by_type[TYPE_CONS]=&apply_cons;
    apply_by_type[TYPE_FREE]=&apply_error;
		apply_by_type[TYPE_LETLOOP]=&apply_letloop;
    applycons_by_type[LT_NOLAMBDA]=&apply_nolambdatype;
    applycons_by_type[LT_LAMBDA]=&apply_lambdatype;
    applycons_by_type[LT_MACRO]=&apply_macrotype;
    applycons_by_type[LT_LABEL]=&apply_labeltype;
    applycons_by_type[LT_SLAMBDA]=&apply_stacklambdatype;
    applycons_by_type[LT_SLAMBDALAP]=&apply_stacklambdalaptype;
#endif
    // create system symbols and functions
    anon_atom=mk_sym("anonymous"); // symbol used to report errors on lambda and macro
    invisible_atom=mk_sym(""); // invisible symbol
    else_atom=mk_sym("else");
    t_atom=mk_builtinLambda("t",bi_lambda_not_impl);
    quote_atom=mk_builtinMacro("quote",bi_quote);
    lambda_atom=mk_builtinLambda("lambda",0);lambda_atom->lambdatype=LT_LAMBDA;
    macro_atom=mk_builtinLambda("macro",0);macro_atom->lambdatype=LT_MACRO;
    label_atom=mk_builtinLambda("label",0);label_atom->lambdatype=LT_LABEL;
    mk_builtinLambda("#lambda",0)->lambdatype=LT_SLAMBDA;
    mk_builtinLambda("#lambdalap",0)->lambdatype=LT_SLAMBDALAP;
    mk_builtinMacro("#lap",bi_lap);
    mk_builtinLambda("eval",bi_eval);mk_builtinLambda("apply",bi_apply);
    mk_builtinMacro("let",bi_let);
    mk_builtinMacro("cond",bi_cond);mk_builtinMacro("if",bi_if);
    mk_builtinStack("car",bi_carS);mk_builtinStack("cdr",bi_cdrS);mk_builtinStack("cons",bi_consS);
    mk_builtinStack("eq",bi_eqS);mk_builtinStack("equal",bi_equalS);mk_builtinStack("atom",bi_atomS);mk_builtinStack("null",bi_nullS);
    mk_builtinLambda("set",bi_set);mk_builtinMacro("setq",bi_setq);
    mk_builtinMacro("defun",bi_defun);mk_builtinMacro("defmacro",bi_defmacro);
    mk_builtinStack("+",bi_addS);mk_builtinStack("-",bi_subS);mk_builtinStack("*",bi_multS);mk_builtinStack("/",bi_divS);mk_builtinStack("%",bi_modS);mk_builtinStack("^",bi_powS);
    mk_builtinMacro("and",bi_and);mk_builtinMacro("or",bi_or);mk_builtinStack("not",bi_notS);
    mk_builtinStack("=",bi_eqS);mk_builtinStack("<>",bi_neS);mk_builtinStack("<",bi_ltS);mk_builtinStack("<=",bi_leS);mk_builtinStack(">=",bi_geS);mk_builtinStack(">",bi_gtS);
    mk_builtinStack("princ",bi_princS);mk_builtinStack("princln",bi_princlnS);mk_builtinStack("print",bi_printS);mk_builtinStack("println",bi_printlnS);mk_builtinStack("spaces",bi_spacesS);
    mk_builtinStack("bye",bi_byeS);mk_builtinStack("exit",bi_byeS);mk_builtinStack("quit",bi_byeS);
    mk_builtinMacro("env",bi_env);mk_builtinStack("gc",bi_gcS);
    mk_builtinMacro("prog1",bi_prog1);mk_builtinMacro("progn",bi_progn);mk_builtinMacro("while",bi_while);
    mk_builtinMacro("do",bi_do);mk_builtinMacro("dotimes",bi_dotimes);mk_builtinMacro("dolist",bi_dolist);
    mk_builtinStack("load",bi_loadS);
    mk_builtinMacro("time",bi_time);mk_builtinStack("millisec",bi_millisecS);
    mk_builtinLambda("filter",bi_filter);mk_builtinLambda("map",bi_map);mk_builtinLambda("mapcar",bi_mapcar);
    mk_builtinStack("list",bi_listS);mk_builtinStack("list*",bi_listpS);mk_builtinStack("append",bi_appendS);
    mk_builtinStack("reverse",bi_reverseS);mk_builtinStack("remove",bi_removeS);
    mk_builtinStack("assoc",bi_assocS);mk_builtinStack("pairlis",bi_pairlisS);mk_builtinStack("member",bi_memberS);
    mk_builtinStack("lexical-scoping",bi_lexicalscopingS);mk_builtinStack("tail-call",bi_tailcallS);mk_builtinStack("error",bi_errorS);
    mk_builtinStack("nump",bi_numpS);mk_builtinStack("strp",bi_strpS);mk_builtinStack("symp",bi_sympS);mk_builtinStack("celltype",bi_celltypeS);
    mk_builtinStack("rplaca",bi_rplacaS);mk_builtinStack("rplacd",bi_rplacdS);
    mk_builtinStack("len",bi_lenS);mk_builtinStack("substr",bi_substrS);mk_builtinStack("at",bi_atS);mk_builtinStack("nth",bi_nthS);
		mk_builtinStack("rand",bi_rand);mk_builtinStack("randomize",bi_randomize);
    load(mk_str("system.yl"),0);
    res=1;
  } else {
    printf("%s%s\nUnable to init environment\n",(i==SYSTEM_ERROR?"SYSTEM: ":""),yl_error_msg);
    yl_sp=0;
  }
  return res;
}

static void yl_bye(){
#ifdef DEBUG_GC
  yl_stopping=1;
#endif // DEBUG_GC
  cellsBlock *cb=yl_fcb;
  int i;
  cell* c;
  yl_sp=0; // se c'erano degli errori si riparte ...
  yl_gc(); // necessario per sapere quali sono effettivamente le stringhe da liberare
  while(cb){ // free all cells and cells blocks
    for(i=0;i<MAX_CELLS;i++){
      c=&(cb->cells[i]);
      ASSERTGC(c->type==TYPE_CONS||c->type==TYPE_NUM||c->type==TYPE_STR||c->type==TYPE_FREE||c->type==TYPE_LETLOOP,"unexpected cell type");
      if (c->gc==1){
        if (c->type==TYPE_STR) free(c->str);
      }
    }
    cellsBlock* tmpcb=cb;
    cb=cb->next;
    free(tmpcb);
  }
  symsBlock *sb=yl_fsb;
  while(sb){ // free all symbols and symbols blocks
    int nsyms=(sb->next?MAX_SYMS:yl_nsyms);
    for(i=0;i<nsyms;i++)
      free(sb->syms[i].sym);
    symsBlock* tmpsb=sb;
    sb=sb->next;
    free(tmpsb);
  }
}

#ifdef REPL_TIMING
int yl_replstarttime;
#define START_EVAL_TIME yl_replstarttime=getMillisec();
#define PRINT_EVAL_TIME printf("timing:%.4f sec.\n",(getMillisec()*1.0-yl_replstarttime)/1000);
#else
#define START_EVAL_TIME
#define PRINT_EVAL_TIME
#endif

int main(int argc,char* argv[]){
  int stop=0,lj;
  cell *res,*input;
  printf("\n    \\/octoLISP\n ---/------------\n0.9.24 %s\n",__DATE__);
  if (argc>1 && (strcmp(argv[1],"-h")==0 || strcmp(argv[1],"--help")==0)) {printf("\nyl [<file1.l> ... [ <fileN.l> | -bye]]\n");return 0;}
  //printf("SYSTEM: cell size %i, cell* size %i, long long int size %i\n",sizeof(cell),sizeof(cell*),sizeof(long long int));
  printf(SCOPING_MODE);
  printf("Mark/Sweep GC\n");
#ifdef TAILCALL
  printf("Tail call optimization\n");
#endif
#ifdef EVAL_FUNCPTR
  printf("Eval with function pointers\n");
#else
  printf("Eval with computed goto\n");
#endif
  if (MAX_CELLS<=100) printf("Blocksize %i cells\n",MAX_CELLS);
  DEBUG_GC_STARTINGMSG
  SAFE_CXR_STARTINGMSG
  if (!yl_init()) {yl_bye();return -1;} // init environment
  if (argc>1) { // command line file
    int i;
    for(i=1;i<argc;i++){
      if (strcmp(argv[i],"-bye")==0 || strcmp(argv[i],"-quit")==0 || strcmp(argv[i],"-exit")==0) {yl_bye();return 0;}
      printf("loading %s ...\n",argv[i]);
      lj=setjmp(yl_mainloop);
      if (!lj)
        load(mk_str(argv[i]),0);
      else if (lj==BYE_JMP)
        stop=1;
      else
        printf("%s%s\n",(lj==SYSTEM_ERROR?"SYSTEM: ":""),yl_error_msg);
    }
  }
  while(!feof(stdin) && !stop) { // REPL loop
    lj=setjmp(yl_mainloop);
    if (!lj){
      yl_sp=0;
      curr_fn=anon_atom;
      printf("\n> ");
      input=read_sexpr(stdin);START_EVAL_TIME;
      res=eval(input,0);PRINT_EVAL_TIME;
      print_sexpr(res,1); //read, eval and print an s-expression
      if (yl_sp!=0) printf("gc error bad stack pointer %i\n",yl_sp);
    } else if (lj==BYE_JMP)
      stop=1;
    else
      printf("%s%s\n",(lj==SYSTEM_ERROR?"SYSTEM: ":""),yl_error_msg);
  }
  yl_bye(); // free all memory
  return bye_value;
}
