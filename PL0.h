#include <stdio.h>

#define NRW        14    // number of reserved words
#define TXMAX      500    // length of identifier table
#define MAXNUMLEN  14     // maximum number of digits in numbers
#define NSYM       12     // maximum number of symbols in array ssym and csym
#define MAXIDLEN   10     // length of identifiers

#define MAXADDRESS 32767  // maximum address
#define MAXLEVEL   32     // maximum depth of nesting block
#define CXMAX      500    // size of code array

#define MAXSYM     30     // maximum number of symbols  

#define STACKSIZE  1000   // maximum storage

char output[MAXADDRESS];
int dimid=400;
int dimidlist[TXMAX];
int elsestatem;

enum symtype
{
	SYM_NULL,
	SYM_IDENTIFIER,
	SYM_NUMBER,
	SYM_PLUS,
	SYM_MINUS,
	SYM_TIMES,
	SYM_SLASH,
	SYM_ODD,
	SYM_EQU,
	SYM_NEQ,
	SYM_LES,
	SYM_LEQ,
	SYM_GTR,
	SYM_GEQ,
	SYM_LPAREN,
	SYM_RPAREN,
	SYM_COMMA,
	SYM_SEMICOLON,
	SYM_PERIOD,
	SYM_BECOMES,
    SYM_BEGIN,
	SYM_END,
	SYM_IF,
	SYM_THEN,
	SYM_WHILE,
	SYM_DO,
	SYM_CALL,
	SYM_CONST,
	SYM_VAR,
	SYM_PROCEDURE,
	SYM_BLOCKEXPLBEG,
	SYM_BLOCKEXPLEND,
	SYM_LINEEXPL,
	SYM_GOTO,
	SYM_LABEL,
	SYM_ADR,
	SYM_AND,
	SYM_OR,
	SYM_NOT,
	SYM_ELSE,
	SYM_LSQ,
	SYM_RSQ,
	SYM_RANDOM,
	SYM_PRINT,
	SYM_LABELEND
};

enum idtype
{
	ID_CONSTANT, ID_VARIABLE, ID_PROCEDURE, ID_ACTUAL
};

enum opcode
{
	LIT, OPR, LOD, STO, CAL, INT, JMP, JPC, STA, LOA, ADR, PRT
};

enum oprcode
{
	OPR_RET, OPR_NEG, OPR_ADD, OPR_MIN,
	OPR_MUL, OPR_DIV, OPR_ODD, OPR_EQU,
	OPR_NEQ, OPR_LES, OPR_LEQ, OPR_GTR,
	OPR_GEQ, OPR_AND, OPR_OR,  OPR_NOT,
	OPR_RAN, OPR_MOV
};


typedef struct
{
	int f; // function code
	int l; // level
	int a; // displacement address
} instruction;

//////////////////////////////////////////////////////////////////////
char* err_msg[] =
{
/*  0 */    "",
/*  1 */    "Found ':=' when expecting '='.",
/*  2 */    "There must be a number to follow '='.",
/*  3 */    "There must be an '=' to follow the identifier.",
/*  4 */    "There must be an identifier to follow 'const', 'var', or 'procedure'.",
/*  5 */    "Missing ',' or ';'.",
/*  6 */    "Incorrect procedure name.",
/*  7 */    "Statement expected.",
/*  8 */    "Follow the statement is an incorrect symbol.",
/*  9 */    "'.' expected.",
/* 10 */    "';' expected.",
/* 11 */    "Undeclared identifier.",
/* 12 */    "Illegal assignment.",
/* 13 */    "':=' expected.",
/* 14 */    "There must be an identifier to follow the 'call'.",
/* 15 */    "A constant or variable can not be called.",
/* 16 */    "'then' expected.",
/* 17 */    "';' or 'end' expected.",
/* 18 */    "'do' expected.",
/* 19 */    "Incorrect symbol.",
/* 20 */    "Relative operators expected.",
/* 21 */    "Procedure identifier can not be in an expression.",
/* 22 */    "Missing ')'.",
/* 23 */    "The symbol can not be followed by a factor.",
/* 24 */    "The symbol can not be as the beginning of an expression.",
/* 25 */    "The number is too great.",
/* 26 */    "The variable has been previously declared.",
/* 27 */    "The actual parameter must refer to a previously declared variable.",
/* 28 */    "Missing parameter list.",
/* 29 */    "',' expected.",
/* 30 */    "Parameter list mismatch.",
/* 31 */    "",
/* 32 */    "There are too many levels."
};

//////////////////////////////////////////////////////////////////////
char ch;         // last character read
int  sym;        // last symbol read
char id[MAXIDLEN + 1]; // last identifier read
int  num;        // last number read
int  cc;         // character count
int  ll;         // line length
int  kk;
int  err;
int  cx;         // index of current instruction to be generated.
int  level = 0;
int  tx = 0;

char line[80];

instruction code[CXMAX];

char* word[NRW + 1] =
{
	"", /* place holder */
	"begin", "call", "const", "do", "end","if",
	"odd", "procedure", "then", "var", "while",
	"label","goto", "else"
};

int wsym[NRW + 1] =
{
	SYM_NULL, SYM_BEGIN, SYM_CALL, SYM_CONST, SYM_DO, SYM_END,
	SYM_IF, SYM_ODD, SYM_PROCEDURE, SYM_THEN, SYM_VAR, SYM_WHILE,
	SYM_LABEL,SYM_GOTO,SYM_ELSE
};

int ssym[NSYM + 1] =
{
	SYM_NULL, SYM_PLUS, SYM_MINUS,
	SYM_LPAREN, SYM_RPAREN, SYM_EQU, SYM_COMMA, SYM_PERIOD, SYM_SEMICOLON,
	SYM_LSQ,SYM_RSQ,SYM_NOT
};

char csym[NSYM + 1] =
{
	' ', '+', '-', '(', ')', '=', ',', '.', ';', '[', ']', '!'
};

#define MAXINS   12
char* mnemonic[MAXINS] =
{
	"LIT", "OPR", "LOD", "STO", "CAL", "INT", "JMP", "JPC","STA","LOA","ADR","PRT"
};

typedef struct
{
	char name[MAXIDLEN + 1];
	int  kind;
	int  value;
} comtab;

comtab table[TXMAX];
short reftable[TXMAX];
short procparamnum[TXMAX];
typedef struct
{
	char  name[MAXIDLEN + 1];
	int   kind;
	short level;
	short address;
} mask,params,*paramlist;

params globalParamList[TXMAX+10];

short next[TXMAX+10],totalparam=0,first[TXMAX];

void addparameter(int prcd){
	next[++totalparam]=first[prcd];
	first[prcd]=totalparam;
}
int dimList[TXMAX+10];
short nextdim[TXMAX+10],totaldim=0,firstdim[TXMAX];
void adddim(int arrayid,int dimnum){
	dimList[++totaldim]=dimnum;
	nextdim[totaldim]=firstdim[arrayid];
	firstdim[arrayid]=totaldim;
}


FILE* infile;

// EOF PL0.h
