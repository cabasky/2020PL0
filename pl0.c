// pl0 compiler source code

#pragma warning(disable:4996)


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <time.h>

#include "PL0.h"
#include "set.c"
#include "label.h"

FILE * fpstack;
//////////////////////////////////////////////////////////////////////
// print error message.
//test
void orcondition(symset fsys);
//void FindAddress(mask*mk, symset fsys);
int position(char *id);
void listvar(){
	for(int i=1;i<=10;i++){
		printf("%d: %s\n",i,table[i].name);
		printf("kind %d ,level %d ,adr %d\n",table[i].kind,((mask*)&table[i])->level,((mask*)&table[i])->address);
	}
	puts("");
}
void error(int n)
{
	int i;

	printf("      ");
	for (i = 1; i <= cc - 1; i++)
		printf(" ");
	printf("^\n");
	printf("Error %3d: %s\n", n, err_msg[n]);
	err++;
} // error

//////////////////////////////////////////////////////////////////////
void getch(void)
{
	if (cc == ll)
	{
		if (feof(infile))
		{
			printf("\nPROGRAM INCOMPLETE\n");
			exit(1);
		}
		ll = cc = 0;
		printf("%5d  ", cx);
		while ( (!feof(infile)) // added & modified by alex 01-02-09
			    && ((ch = getc(infile)) != '\n'))
		{
			printf("%c", ch);
			line[++ll] = ch;
		} // while
		printf("\n");
		line[++ll] = ' ';
	}
	ch = line[++cc];
} // getch

//skip the block explnation
void blockExplanation(){
	int status=0;
	do{
		getch();
		if(status==0){
			if(ch=='*') status=1;
		}
		else if(status==1){
			if(ch=='/') status=2;
			else status=0;
		}
	}while(status!=2);
	getch();
}

//////////////////////////////////////////////////////////////////////
// gets a symbol from input stream.
void getsym(void)
{
	int i, k;
	char a[MAXIDLEN + 1],random_str[7] = "random", print_str[6] = "print";

	while (ch == ' '||ch == '\t')
		getch();

	if (isalpha(ch))
	{ // symbol is a reserved word or an identifier.
		k = 0;
		do
		{
			if (k < MAXIDLEN)
				a[k++] = ch;
			getch();
		}
		while (isalpha(ch) || isdigit(ch));
		a[k] = 0;
		strcpy(id, a);
		word[0] = id;
		i = NRW;
		while (strcmp(id, word[i--]));
		if (++i)
			sym = wsym[i]; // symbol is a reserved word
		else if (strcmp(id, random_str) == 0)
			sym = SYM_RANDOM;         //symbol is function "random"
		else if (strcmp(id, print_str) == 0)
			sym = SYM_PRINT;              //symbol is function "print"
		else
			sym = SYM_IDENTIFIER;   // symbol is an identifier
	}
	else if (isdigit(ch))
	{ // symbol is a number.
		k = num = 0;
		sym = SYM_NUMBER;
		do
		{
			num = num * 10 + ch - '0';
			k++;
			getch();
		}
		while (isdigit(ch));
		if (k > MAXNUMLEN)
			error(25);     // The number is too great.
	}
	else if (ch == ':')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_BECOMES; // :=
			getch();
		}
		else
		{
			sym = SYM_LABELEND;       // illegal?
		}
	}
	else if (ch == '>')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_GEQ;     // >=
			getch();
		}
		else
		{
			sym = SYM_GTR;     // >
		}
	}
	else if (ch == '<')
	{
		getch();
		if (ch == '=')
		{
			sym = SYM_LEQ;     // <=
			getch();
		}
		else if (ch == '>')
		{
			sym = SYM_NEQ;     // <>
			getch();
		}
		else
		{
			sym = SYM_LES;     // <
		}
	}
	else if(ch=='/'){
		getch();
		if(ch=='/'){
			sym=SYM_LINEEXPL;
			while(cc!=ll) getch();
			getsym();
		}
		else if(ch=='*'){
			sym=SYM_BLOCKEXPLBEG;
			blockExplanation();
			getsym();
		}
		else sym=SYM_SLASH;
	}
	else if(ch=='|'){
		getch();
		if(ch=='|'){
			sym=SYM_OR;
			getch();
		}
		else{
			printf("Fatal Error: Unknown character.\n");
			exit(1);
		}
	}
	else if(ch=='&'){
		getch();
		if(ch=='&'){
			sym=SYM_AND;
			getch();
		}
		else{
			sym=SYM_ADR;
		}
	}
	else if(ch=='*'){
		getch();
		if(ch=='/'){
			sym=SYM_BLOCKEXPLEND;
			getch();
		}
		else{
			sym=SYM_TIMES;
		}
	}
	else
	{ // other tokens
		i = NSYM;
		csym[0] = ch;
		while (csym[i--] != ch);
		if (++i)
		{
			sym = ssym[i];
			getch();
		}
		else
		{
			printf("Fatal Error: Unknown character.\n");
			exit(1);
		}
	}
} // getsym

//////////////////////////////////////////////////////////////////////
// generates (assembles) an instruction.
void gen(int x, int y, int z)
{
	if (cx > CXMAX)
	{
		printf("Fatal Error: Program too long.\n");
		exit(1);
	}
	code[cx].f = x;
	code[cx].l = y;
	code[cx++].a = z;
} // gen

//////////////////////////////////////////////////////////////////////
// tests if error occurs and skips all symbols that do not belongs to s1 or s2.
void test(symset s1, symset s2, int n)
{
	symset s;

	if (! inset(sym, s1))
	{
		error(n);
		s = uniteset(s1, s2);
		while(! inset(sym, s))
			getsym();
		destroyset(s);
	}
} // test
//actual variable initialize
void actualinit(){

}
//////////////////////////////////////////////////////////////////////
int dx;  // data allocation index
//check redefination in same block.
int redefinationcheck(char *id,int paranum){
	int i;
	for(i=tx;((mask*)&table[i])->address>=3;i--) if(!strcmp(id,table[i].name)) return 1;
	int j=i;
	for(i=0;i<paranum;i++) if(!strcmp(id,table[j--].name)) return 1;
	return 0;
}
// enter object(constant, variable or procedre) into table.
void enter(int kind,char *eid)
{
	mask* mk;

	tx++;
	strcpy(table[tx].name, eid);
	table[tx].kind = kind;
	switch (kind)
	{
	case ID_CONSTANT:
		if (num > MAXADDRESS)
		{
			error(25); // The number is too great.
			num = 0;
		}
		table[tx].value = num;
		break;
	case ID_VARIABLE:
		mk = (mask*) &table[tx];
		mk->level = level;
		mk->address = dx++;
		break;
	case ID_PROCEDURE:
		mk = (mask*) &table[tx];
		mk->level = level;
		mk->address = 0;
		break;
	case ID_ACTUAL:
		mk=(mask*) &table[tx];
		mk->level=level;
		mk->address=dx++;
		break;
	} // switch
} // enter
int FindAddressConst(int tpos,int flag)
{
	int dim,ret;
	getsym();
	if (sym == SYM_NUMBER) dim=num;
	else if(sym==SYM_IDENTIFIER){
		int idx=position(id);
		if(idx&&table[idx].kind==ID_CONSTANT) dim=table[idx].value;
		else error(0);
	}
	getsym();
	if (sym == SYM_RSQ)
	{
		getsym();
		if (sym == SYM_LSQ) ret=dim*FindAddressConst(tpos,1);
		else ret=dim;
	}
	else error(31);
	if(flag) adddim(tpos,ret);
	return ret;
}
int findaddress(symset fsys,int dims){
	getsym();
	orcondition(fsys);
	if(nextdim[dims]){
		gen(LIT,0,dimList[dims]);
		gen(OPR,0,OPR_MUL);
	}
	gen(OPR,0,OPR_ADD);
	//getsym();
	if(sym==SYM_RSQ){
		getsym();
		if(sym==SYM_LSQ){
			findaddress(fsys,nextdim[dims]);
		}
	}
	else error(31);
}
void enterArray(char *eid)
{
	mask* mk;
	tx++;
	strcpy(table[tx].name, eid);
	table[tx].kind = ID_VARIABLE;
	mk = (mask*)&table[tx];
	mk->level = level;
	mk->address=dx;
	firstdim[tx]=0;
	adddim(tx,1);
	int ofs=FindAddressConst(tx,0);
	int it;
	dx+=ofs;
}
void genoffset(symset fsys,int arrayid){
	findaddress(fsys,firstdim[arrayid]);
}
//////////////////////////////////////////////////////////////////////
// locates identifier in symbol table.
int position(char* id)
{
	int i;
	strcpy(table[0].name, id);
	i = tx + 1;
	while (strcmp(table[--i].name, id) != 0);
		/*
			So as parameter list. dx<=-1.
		*/
	return i;
} // position

//////////////////////////////////////////////////////////////////////
void constdeclaration()
{
	if (sym == SYM_IDENTIFIER)
	{
		getsym();
		if (sym == SYM_EQU || sym == SYM_BECOMES)
		{
			if (sym == SYM_BECOMES)
				error(1); // Found ':=' when expecting '='.
			getsym();
			if (sym == SYM_NUMBER)
			{
				enter(ID_CONSTANT,id);
				getsym();
			}
			else
			{
				error(2); // There must be a number to follow '='.
			}
		}
		else
		{
			error(3); // There must be an '=' to follow the identifier.
		}
	} else	error(4);
	 // There must be an identifier to follow 'const', 'var', or 'procedure'.
} // constdeclaration

//////////////////////////////////////////////////////////////////////
void vardeclaration(symset fsys,int paranum)
{
	int actualflag=0;
	if(sym==SYM_ADR){
		getsym();
		actualflag=1;
	}
	if (sym == SYM_IDENTIFIER)
	{
		if(actualflag){
			char tmp[20];
			strcpy(tmp,id);
			getsym();
			if(sym==SYM_EQU){
				getsym();
				if(sym==SYM_IDENTIFIER){
					int pos=position(id);
					if(!pos||((mask*)(&table[pos]))->kind==ID_CONSTANT||((mask*)(&table[pos]))->kind==ID_PROCEDURE) error(27);
						enter(ID_ACTUAL,tmp);
						if(((mask*)(&table[pos]))->kind==ID_VARIABLE){
							getsym();
							if(sym==SYM_LSQ){
								if(((mask*)&table[pos])->address<0) gen(LOD,0,((mask*)(&table[pos]))->address);
								else gen(ADR,level-((mask*)(&table[pos]))->level,((mask*)(&table[pos]))->address);
								findaddress(fsys,firstdim[pos]);
							}
							else gen(ADR,level-((mask*)(&table[pos]))->level,((mask*)(&table[pos]))->address);
						}
						else if(((mask*)(&table[pos]))->kind==ID_ACTUAL){
							gen(LOD,0,((mask*)(&table[pos]))->address);
							getsym();
						}
						gen(STO,0,((mask*)&table[tx])->address);
				}
				else{
					error(27);
				}
			}
			else{
				error(27);
			}
		}
		else{
			if(!redefinationcheck(id,paranum)){
				getsym();
				if(sym==SYM_LSQ) enterArray(id);
				else enter(ID_VARIABLE,id);
			}
			else{
				error(26);
				getsym();
			}
		}
	}
	else
	{
		error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
	}
} // vardeclaration

//////////////////////////////////////////////////////////////////////
void listcode(int from, int to)
{
	int i;
	
	printf("\n");
	for (i = from; i < to; i++)
	{
		printf("code---%5d %s\t%d\t%d\n", i, mnemonic[code[i].f], code[i].l, code[i].a);
	}
	printf("\n");
} // listcode

void factor(symset fsys)
{
	void expression(symset fsys);
	int i;
	symset set;
	test(facbegsys, fsys, 24); // The symbol can not be as the beginning of an expression.
	if (inset(sym, facbegsys))
	{
		if (sym == SYM_IDENTIFIER)
		{
			if ((i = position(id)) == 0)
			{
				error(11); // Undeclared identifier.
			}
			else
			{
				switch (table[i].kind)
				{
					mask* mk;
				case ID_CONSTANT:
					gen(LIT, 0, table[i].value);
					getsym();
					break;
				case ID_VARIABLE:
					mk = (mask*) &table[i];
					getsym();
					if(sym==SYM_LSQ){
						if(mk->address<0) gen(LOD,level-mk->level,mk->address);
						else gen(ADR,level-mk->level,mk->address);
						genoffset(fsys,i);
						gen(LOA,-1,0);
					}
					else{
						gen(LOD, level - mk->level, mk->address);
					}
					break;
				case ID_ACTUAL:
					mk=(mask*)&table[i];
					gen(LOA,level-mk->level,mk->address);
					getsym();
					break;
				case ID_PROCEDURE:
					error(21); // Procedure identifier can not be in an expression.
					break;
				} // switch
			}
			//getsym();
		}
		else if (sym == SYM_NUMBER)
		{
			if (num > MAXADDRESS)
			{
				error(25); // The number is too great.
				num = 0;
			}
			gen(LIT, 0, num);
			getsym();
		}
		else if (sym == SYM_LPAREN)
		{
			getsym();
			set = uniteset(createset(SYM_RPAREN, SYM_NULL), fsys);
			//expression(set);
			orcondition(set);
			destroyset(set);
			if (sym == SYM_RPAREN)
			{
				getsym();
			}
			else
			{
				error(22); // Missing ')'.
			}
		}
		else if(sym == SYM_MINUS) // UMINUS,  Expr -> '-' Expr
		{  
			 getsym();
			 factor(fsys);
			 gen(OPR, 0, OPR_NEG);
		}
		else if (sym == SYM_RANDOM) {
			getsym();
			if (sym == SYM_LPAREN) {
				getsym();
				if (sym == SYM_RPAREN) {   //����Ϊ��
					gen(LIT, 0, 32767);
					gen(OPR, 0, OPR_RAN);
					getsym();
				}
				else {    //����Ϊ����, const, var, ����ʽ
					set = uniteset(createset(SYM_RPAREN, SYM_NULL), fsys);
					expression(set);
					destroyset(set);
					if (sym == SYM_RPAREN) {
						gen(OPR, 0, OPR_RAN);
						getsym();
					}
				}
			}
		}
		else if(sym==SYM_NOT){
			 getsym();
			 factor(fsys);
			 gen(OPR, 0, OPR_NOT);
		}
		setinsert(fsys,SYM_COMMA);
		setinsert(fsys,SYM_RPAREN);
		setinsert(fsys,SYM_AND);
		setinsert(fsys,SYM_OR);
		setinsert(fsys,SYM_RSQ);
		test(fsys, createset(SYM_LPAREN, SYM_NULL), 23);
	} // if
} // factor

//////////////////////////////////////////////////////////////////////
void term(symset fsys)
{
	int mulop;
	symset set;
	
	set = uniteset(fsys, createset(SYM_TIMES, SYM_SLASH, SYM_NULL));
	factor(set);
	while (sym == SYM_TIMES || sym == SYM_SLASH)
	{
		mulop = sym;
		getsym();
		factor(set);
		if (mulop == SYM_TIMES)
		{
			gen(OPR, 0, OPR_MUL);
		}
		else
		{
			gen(OPR, 0, OPR_DIV);
		}
	} // while
	destroyset(set);
} // term

//////////////////////////////////////////////////////////////////////
void expression(symset fsys)
{
	int addop;
	symset set;

	set = uniteset(fsys, createset(SYM_PLUS, SYM_MINUS, SYM_NULL));
	
	term(set);
	while (sym == SYM_PLUS || sym == SYM_MINUS)
	{
		addop = sym;
		getsym();
		term(set);
		if (addop == SYM_PLUS)
		{
			gen(OPR, 0, OPR_ADD);
		}
		else
		{
			gen(OPR, 0, OPR_MIN);
		}
	} // while

	destroyset(set);
} // expression
//////////////////////////////////////////////////////////////////////
void condition(symset fsys)
{
	int relop;
	symset set;

	if (sym == SYM_ODD)
	{
		getsym();
		expression(fsys);
		gen(OPR, 0, 6);
	}
	else
	{
		set = uniteset(relset, fsys);
		expression(set);
		destroyset(set);
		if (! inset(sym, relset))
		{
			return;
		}
		else
		{
			relop = sym;
			getsym();
			expression(fsys);
			switch (relop)
			{
			case SYM_EQU:
				gen(OPR, 0, OPR_EQU);
				break;
			case SYM_NEQ:
				gen(OPR, 0, OPR_NEQ);
				break;
			case SYM_LES:
				gen(OPR, 0, OPR_LES);
				break;
			case SYM_GEQ:
				gen(OPR, 0, OPR_GEQ);
				break;
			case SYM_GTR:
				gen(OPR, 0, OPR_GTR);
				break;
			case SYM_LEQ:
				gen(OPR, 0, OPR_LEQ);
				break;
			} // switch
		} // else
	} // else
} // condition

void callProc(int procindex,symset fsys){
	mask *mk=(mask*)&table[procindex];
	int savedCx=cx,it,paramindex[20],pmnum=mk->level,erflag=0;
	for(it=first[procindex];it;it=next[it])
		paramindex[pmnum+1+((mask*)&globalParamList[it])->address]=it;
	getsym();
	if(sym!=SYM_LPAREN) erflag=1;
	else{
		for(it=1;it<=pmnum;it++){
			getsym();
			if(((mask*)&globalParamList[paramindex[it]])->kind==ID_ACTUAL){
				if(sym==SYM_IDENTIFIER){
					int key=position(id);
					if(!key) erflag=1;
					if(table[key].kind==ID_CONSTANT || table[key].kind==ID_PROCEDURE){
						erflag=12;
						error(12);
					}
					else if(table[key].kind==ID_VARIABLE){
						getsym();
						if(sym==SYM_LSQ){
							if(((mask*)&table[key])->address<0) gen(LOD,0,((mask*)&table[key])->address);
							else gen(ADR,level-((mask*)&table[key])->level,((mask*)&table[key])->address);
							findaddress(fsys,firstdim[key]);
						}
						else gen(ADR,level-((mask*)&table[key])->level,((mask*)&table[key])->address);
					}
					else if(table[key].kind==ID_ACTUAL){
						gen(LOD,level-((mask*)&table[key])->level,((mask*)&table[key])->address);
						getsym();
					}
				}
				else erflag=1;
			}
			else if(((mask*)&globalParamList[paramindex[it]])->kind==ID_VARIABLE){
				int idx=dimidlist[paramindex[it]];
				if(firstdim[idx]){
					if(sym==SYM_IDENTIFIER){
						int idx2=position(id);
						if(idx2&&table[idx2].kind==ID_VARIABLE&&firstdim[idx2]){
							if(((mask*)&table[idx2])->address<0) gen(LOD,0,((mask*)&table[idx2])->address);
							else gen(ADR,level-((mask*)&table[idx2])->level,((mask*)&table[idx2])->address);
						}
					}
					getsym();
				}
				else orcondition(fsys);
			}
			if(it!=pmnum&&sym!=SYM_COMMA||it==pmnum&&sym!=SYM_RPAREN){
				error(30);
				erflag=1;
				break;
			}
		}
		if(erflag==1){
			while(sym!=SYM_SEMICOLON) getsym();
			error(30);
			cx=savedCx;
		}
		if(!erflag){
			gen(CAL,level,mk->address);
			getsym();
		}
	}
	
	/*
	mask *mk=(mask*)&table[procindex];
	int savedCx=cx,it,paramindex[20],pmnum=mk->level,erflag=0;
	for(it=first[procindex];it;it=next[it])
		paramindex[pmnum+1+((mask*)&globalParamList[it])->address]=it;
	getsym();
	if(sym!=SYM_LPAREN) erflag=1;
	else{
		for(it=1;it<=pmnum;it++){
			if(((mask*)&globalParamList[paramindex[it]])->kind==ID_ACTUAL){
				getsym();
				if(sym==SYM_RPAREN){
					erflag=1;
					break;
				}
				else if(sym==SYM_COMMA){
					erflag=1;
				}
				else if(sym==SYM_IDENTIFIER){
					int key=position(id);
					if(!key) erflag=1;
					if(table[key].kind==ID_CONSTANT || table[key].kind==ID_PROCEDURE){
						erflag=12;
						error(12);
					}
					else if(table[key].kind==ID_VARIABLE){
						gen(ADR,level-((mask*)&table[key])->level,((mask*)&table[key])->address);
					}
					else if(table[key].kind==ID_ACTUAL){
						gen(LOD,level-((mask*)&table[key])->level,((mask*)&table[key])->address);
					}
				}
				else{
					erflag=12;
					error(12);
				}
				getsym();
			}
			else if(((mask*)&globalParamList[paramindex[it]])->kind==ID_VARIABLE){
				getsym();
				if(sym==SYM_RPAREN){
					erflag=1;
					break;
				}
				else if(sym==SYM_COMMA){
					erflag=1;
				}
				else{
					expression(fsys);
				}
			}
			if(it!=pmnum){
				if(sym!=SYM_COMMA){
					erflag=1;
					if(sym==SYM_COMMA){
						error(30);
						break;
					}
				}
			}
			else{
				if(sym!=SYM_RPAREN){
					error(30);
				}
			}
		}
		if(erflag==1){
			error(29);
		}
		if(erflag){
			cx=savedCx;
		}
		if(!erflag){
			gen(CAL,level,mk->address);
		}
	}*/
}
void andcondition(symset fsys){
	condition(fsys);
	while(sym==SYM_AND){
		getsym();
		condition(fsys);
		gen(OPR,0,OPR_AND);
	}
}
void orcondition(symset fsys){
	andcondition(fsys);
	while(sym==SYM_OR){
		getsym();
		andcondition(fsys);
		gen(OPR,0,OPR_OR);
	}
}
//////////////////////////////////////////////////////////////////////
void statement(symset fsys)
{
	int i, cx1, cx2;
	symset set1, set;

	if (sym == SYM_IDENTIFIER)
	{ // variable assignment
		mask* mk;
		if (! (i = position(id)))
		{
			int lidx=labelpos(id);
			if(!lidx){
				char eid[20];
				strcpy(eid,id);
				getsym();
				if(sym==SYM_LABELEND){
					enterlabel(eid,cx);
					return;
				}
				else{
					error(11);
				}
			}
			//error(11); // Undeclared identifier.
		}
		else if (table[i].kind != ID_VARIABLE&&table[i].kind != ID_ACTUAL)
		{
			error(12); // Illegal assignment.
			i = 0;
		}
		getsym();
		int arrayflag=0;
		if(sym==SYM_LSQ){
			mk=(mask*)(&table[i]);
			if(mk->address<0) gen(LOD,0,mk->address);
			else gen(ADR,level-mk->level,mk->address);
			genoffset(fsys,i);
			arrayflag=1;
		}
		if (sym == SYM_BECOMES)
		{
			getsym();
		}
		else
		{
			error(13); // ':=' expected.
		}
		//printf("test1 %d\n",i);
		expression(fsys);
		mk = (mask*) &table[i];
		if (i)
		{
			if(arrayflag){
				gen(OPR,0,OPR_MOV);
			}
			else{
				if(table[i].kind==ID_VARIABLE)
					gen(STO, level - mk->level, mk->address);
				else if (table[i].kind==ID_ACTUAL){
					gen(STA,level-mk->level,mk->address);
				}
			}
		}
	}
	else if (sym == SYM_CALL)
	{ // procedure call
		getsym();
		if (sym != SYM_IDENTIFIER)
		{
			error(14); // There must be an identifier to follow the 'call'.
		}
		else
		{
			if (! (i = position(id)))
			{
				error(11); // Undeclared identifier.
			}
			else if (table[i].kind == ID_PROCEDURE)
			{
				mask* mk;
				mk = (mask*) &table[i];
				callProc(i,fsys);
				/*
				if(paramCheck(i))
				gen(CAL,level, mk->address);*/
			}
			else
			{
				error(15); // A constant or variable can not be called. 
			}
		}
	} 
	else if (sym == SYM_IF)
	{ // if statement
		getsym();
		set1 = createset(SYM_THEN, SYM_DO, SYM_NULL);
		set = uniteset(set1, fsys);
		//condition(set);
		orcondition(set);
		destroyset(set1);
		destroyset(set);
		if (sym == SYM_THEN)
		{
			getsym();
		}
		else
		{
			error(16); // 'then' expected.
		}
		cx1 = cx;
		gen(JPC, 0, 0);
		statement(fsys);
		code[cx1].a = cx;
		getsym();
		if(sym==SYM_ELSE){
			getsym();
			int cx2=cx;
			gen(JMP, 0, 0);
			code[cx1].a = cx;
			statement(fsys);
			code[cx2].a=cx;
		}
		elsestatem=1;
		return;
	}
	else if (sym == SYM_BEGIN)
	{ // block
		getsym();
		set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
		set = uniteset(set1, fsys);
		statement(set);
		while (sym == SYM_SEMICOLON ||sym==SYM_LABELEND|| inset(sym, statbegsys)||elsestatem)
		{
			if (sym == SYM_SEMICOLON||sym==SYM_LABELEND)
			{
				getsym();
			}
			else if(elsestatem){
				elsestatem=0;
			}
			else
			{
				error(10);
			}
			statement(set);
		} // while
		destroyset(set1);
		destroyset(set);
		if (sym == SYM_END)
		{
			getsym();
		}
		else
		{
			error(17); // ';' or 'end' expected.
		}
	}
	else if (sym == SYM_WHILE)
	{ // while statement
		cx1 = cx;
		getsym();
		set1 = createset(SYM_DO, SYM_NULL);
		set = uniteset(set1, fsys);
		orcondition(set);
		destroyset(set1);
		destroyset(set);
		cx2 = cx;
		gen(JPC, 0, 0);
		if (sym == SYM_DO)
		{
			getsym();
		}
		else
		{
			error(18); // 'do' expected.
		}
		statement(fsys);
		gen(JMP, 0, cx1);
		code[cx2].a = cx;
	}
	else if (sym == SYM_PRINT) {
		getsym();
		if (sym == SYM_LPAREN) {
			getsym();
			if (sym == SYM_RPAREN) {   //����Ϊ��
				gen(PRT, 0, 0);
				getsym();
			}
			else {    //������Ϊ��
				i = 0;
				do {
					if (i != 0)
						getsym();
					set = uniteset(createset(SYM_COMMA, SYM_NULL), fsys);
					expression(set);
					destroyset(set);
					i++;
				} while (sym == SYM_COMMA);
				gen(PRT, 0, i);
				getsym();
			}
		}
	}
	else if (sym==SYM_GOTO){
		getsym();
		if(sym==SYM_IDENTIFIER){
			entergoto(id,cx);
			gen(JMP,0,0);
			getsym();
		}
		else error(32);
	}
	//add by HuangXi    end
	test(fsys, phi, 19);
	//getsym();
} // statement

int paramlistInit(int procindex){
	int paranum=0,ads=0;
	char eid[20];
	do{
		getsym();
		int actualflag=0,arrayflag=0;
		if(sym==SYM_IDENTIFIER){
			strcpy(eid,id);
			actualflag=0;
			getsym();
			if(sym==SYM_LSQ) arrayflag=1;
		}
		else if(sym==SYM_ADR){
			getsym();
			if(sym==SYM_IDENTIFIER){
				strcpy(eid,id);
				actualflag=1;
				getsym();
			}
			else{
				error(28);
			}
		}
		if(!redefinationcheck(id,0)){
			paranum++;
			tx++;
			if(actualflag) table[tx].kind=ID_ACTUAL;
			else{
				table[tx].kind=ID_VARIABLE;
				if(arrayflag) {
					firstdim[tx]=0;
					//printf("test2%d\n",firstdim[tx]);
					adddim(tx,1);
					FindAddressConst(dimid+1,1);
					//printf("test2%d\n",firstdim[tx]);
				}
			}
			strcpy(table[tx].name,eid);
			((mask*)&table[tx])->level=level;
			((mask*)&table[tx])->address=ads++;
			addparameter(procindex);
			globalParamList[totalparam]=*((mask*)&table[tx]);
			if(arrayflag) dimidlist[totalparam]=++dimid;
		}
		if(sym!=SYM_RPAREN&&sym!=SYM_COMMA){
			error(29);
		}
		/*check comma*/
	}while(sym!=SYM_RPAREN);
	int it;
	for(it=first[procindex];it;it=next[it])
		globalParamList[it].address-=paranum;
	for(it=procindex+1;it<=tx;it++)
		((mask*)&table[it])->address-=paranum;
	getsym();
	return paranum;
}

//////////////////////////////////////////////////////////////////////
void block(symset fsys,int procindex)
{
	int cx0; // initial code index
	mask* mk;
	int block_dx;
	int savedTx;
	symset set1, set;

	dx = 3;
	block_dx = dx;
	mk = (mask*) &table[procindex];
	mk->address = cx;
	gen(INT,0,0);
	if (level > MAXLEVEL)
	{
		error(32); // There are too many levels.
	}
	do
	{
		if (sym == SYM_CONST)
		{ // constant declarations
			getsym();
			do
			{
				if(!redefinationcheck(id,mk->level))
					constdeclaration();
				else{
					error(26);
					getsym();
				}
				while (sym == SYM_COMMA)
				{
					getsym();
					if(!redefinationcheck(id,mk->level))
						constdeclaration();
					else{
						error(26);
						getsym();
					}
				}
				if (sym == SYM_SEMICOLON)
				{
					getsym();
				}
				else
				{
					error(5); // Missing ',' or ';'.
				}
			}
			while (sym == SYM_IDENTIFIER);
		} // if

		if (sym == SYM_VAR)
		{ // variable declarations
			getsym();
			do
			{
				vardeclaration(fsys,mk->level);
				while (sym == SYM_COMMA)
				{
					getsym();
					vardeclaration(fsys,mk->level);
				}
				if (sym == SYM_SEMICOLON)
				{
					getsym();
				}
				else
				{
					error(5); // Missing ',' or ';'.
				}
			}
			while (sym == SYM_IDENTIFIER);
		} // if
		block_dx = dx; //save dx before handling procedure call!
		int jmpcx=0;
		while (sym == SYM_PROCEDURE)
		{ // procedure declarations
			if(!jmpcx){
				jmpcx=cx;
				gen(JMP,0,0);
			}
			getsym();
			if (sym == SYM_IDENTIFIER)
			{
				if(!redefinationcheck(id,mk->level))
					enter(ID_PROCEDURE,id);
				else{
					error(26);
				}
				getsym();
			}
			else
			{
				error(4); // There must be an identifier to follow 'const', 'var', or 'procedure'.
			}
			savedTx = tx;
			level++;
			if(sym==SYM_LPAREN){
				((mask*)&table[savedTx])->level=paramlistInit(tx);
			}
			else error(27);
			if (sym == SYM_SEMICOLON)
			{
				getsym();
			}
			else
			{
				error(5); // Missing ',' or ';'.
			}

			set1 = createset(SYM_SEMICOLON, SYM_NULL);
			set = uniteset(set1, fsys);
			block(set,savedTx);
			destroyset(set1);
			destroyset(set);
			tx = savedTx;
			level--;

			if (sym == SYM_SEMICOLON)
			{
				getsym();
				set1 = createset(SYM_VAR,SYM_IDENTIFIER, SYM_PROCEDURE, SYM_NULL);
				set = uniteset(statbegsys, set1);
				test(set, fsys, 6);
				destroyset(set1);
				destroyset(set);
			}
			else
			{
				error(5); // Missing ',' or ';'.
			}
		} // while
		code[jmpcx].a=cx;
		dx = block_dx; //restore dx after handling procedure call!
		set1 = createset(SYM_VAR,SYM_IDENTIFIER, SYM_NULL);
		set = uniteset(statbegsys, set1);
		test(set, declbegsys, 7);
		destroyset(set1);
		destroyset(set);
	}
	while (inset(sym, declbegsys));
	code[mk->address].a=dx;
	/*
	code[mk->address].a = cx;
	mk->address = cx;*/
	cx0 = cx;
	int it;
	/*
	for(it=procindex+1;it<=tx;it++){
		if(table[it].kind==ID_ACTUAL){
			if(((mask*)&table[it])->address<0) continue;
			int levdif=((mask*)&table[it])->level-((mask*)&table[reftable[it]])->level;
			if(((mask*)&table[reftable[it]])->address<0&&((mask*)&table[reftable[it]])->kind==ID_ACTUAL){
				gen(LOD,0,((mask*)&table[reftable[it]])->address);
				gen(STO,0,((mask*)&table[it])->address);
			}
			else{
				gen(ADR,levdif,((mask*)&table[reftable[it]])->address);
				gen(STO,0,((mask*)&table[it])->address);
			}
		}
	}*/
	
	set1 = createset(SYM_SEMICOLON, SYM_END, SYM_NULL);
	set = uniteset(set1, fsys);
	statement(set);
	destroyset(set1);
	destroyset(set);
	gen(OPR, 0, OPR_RET); // return
	test(fsys, phi, 8); // test for error: Follow the statement is an incorrect symbol.
	listcode(cx0, cx);
} // block

//////////////////////////////////////////////////////////////////////
int base(int stack[], int currentLevel, int levelDiff)
{
	int b = currentLevel;
	
	while (levelDiff--)
		b = stack[b];
	return b;
} // base

//////////////////////////////////////////////////////////////////////
// interprets and executes codes.
void interpret()
{
	int pc;        // program counter
	int stack[STACKSIZE];
	memset(stack,0,sizeof(stack));
	int top;       // top of stack
	int b;         // program, base, and top-stack register
	instruction i; // instruction register
	int j;
	printf("Begin executing PL/0 program.\n");

	pc = 0;
	b = 1;
	top = 0;
	stack[1] = stack[2] = stack[3] = 0;
	do
	{
		i = code[pc++];
		switch (i.f)
		{
		case LIT:
			stack[++top] = i.a;
			break;
		case OPR:
			switch (i.a) // operator
			{
			case OPR_RET:
				top = b - 1;
				pc = stack[top + 3];
				b = stack[top + 2];
				break;
			case OPR_NEG:
				stack[top] = -stack[top];
				break;
			case OPR_NOT:
				stack[top] = !stack[top];
				break;
			case OPR_ADD:
				top--;
				stack[top] += stack[top + 1];
				break;
			case OPR_MIN:
				top--;
				stack[top] -= stack[top + 1];
				break;
			case OPR_MUL:
				top--;
				stack[top] *= stack[top + 1];
				break;
			case OPR_DIV:
				top--;
				if (stack[top + 1] == 0)
				{
					fprintf(stderr, "Runtime Error: Divided by zero.\n");
					fprintf(stderr, "Program terminated.\n");
					continue;
				}
				stack[top] /= stack[top + 1];
				break;
			case OPR_ODD:
				stack[top] %= 2;
				break;
			case OPR_EQU:
				top--;
				stack[top] = stack[top] == stack[top + 1];
				break;
			case OPR_NEQ:
				top--;
				stack[top] = stack[top] != stack[top + 1];
				break;
			case OPR_LES:
				top--;
				stack[top] = stack[top] < stack[top + 1];
				break;
			case OPR_GEQ:
				top--;
				stack[top] = stack[top] >= stack[top + 1];
				break;
			case OPR_GTR:
				top--;
				stack[top] = stack[top] > stack[top + 1];
				break;
			case OPR_LEQ:
				top--;
				stack[top] = stack[top] <= stack[top + 1];
				break;
			case OPR_AND:
				top--;
				stack[top] = stack[top] && stack[top + 1];
				break;
			case OPR_OR:
				top--;
				stack[top] = stack[top] || stack[top + 1];
				break;
			case OPR_RAN:
				stack[top] = rand() % stack[top];
				break;
			case OPR_MOV:
				top--;
				stack[stack[top+i.l]]=stack[top+1];
				top--;
			} // switch
			break;
		case ADR:
			stack[++top]=base(stack,b,i.l)+i.a;
			break;
		case LOD:
			stack[++top] = stack[base(stack, b, i.l) + i.a];
			break;
		case LOA:
			if(i.l==-1) stack[top]=stack[stack[top+i.a]];
			else stack[++top] = stack[stack[base(stack, b, i.l)+i.a]];
			break;
		case STO:
			stack[base(stack, b, i.l) + i.a] = stack[top];
			printf("%d\n", stack[top]);
			top--;
			break;
		case STA:
			stack[stack[base(stack, b, i.l)+i.a]] = stack[top];
			printf("%d\n", stack[top]);
			top--;
			break;
		case CAL:
			stack[top + 1] = base(stack, b, i.l);
			// generate new block mark
			stack[top + 2] = b;
			stack[top + 3] = pc;
			b = top + 1;
			pc = i.a;
			break;
		case INT:
			top += i.a;
			break;
		case JMP:
			pc = i.a;
			break;
		case JPC:
			if (stack[top] == 0)
				pc = i.a;
			top--;
			break;
		case PRT:
			if (i.a == 0)     //�޲�������ӡ�س���
				sprintf(output+strlen(output),"\n");
			else                //�в���
				for (j = top-i.a+1; j <=top; j++) {
					sprintf(output+strlen(output),"%d ", stack[j]);
				}
				top-=i.a;
			break;
		} // switch
		int it;
		for(it=0;it<=top;it++){
			fprintf(fpstack,"%4d",stack[it]);
		}
		fprintf(fpstack,"\n");
		for(it=0;it<=top;it++){
			if(it<10) fprintf(fpstack,"---");
			else if(it<100) fprintf(fpstack,"--");
			else if(it<1000) fprintf(fpstack,"-");
			fprintf(fpstack,"%d",it);
		}
		fprintf(fpstack,"\n");
		for(it=0;it<b;it++){
			fprintf(fpstack,"    ");
		}
		fprintf(fpstack,"   b\n\n");
	}
	while (pc);
	
	printf("End executing PL/0 program.\n");
} // interpret
 
void gotobackpatch(){
	int i;
	for(i=1;i<=gx;i++){
		int lidx=labelpos(gtlist[i].name);
		//printf("test5 %s %d \n",gtlist[g])
		if(lidx){
			code[gtlist[i].cx].a=ltable[lidx].cx;
		}
		else error(30);
	}
}
//////////////////////////////////////////////////////////////////////
void main ()
{
	srand((int)time(NULL));
	FILE* hbin;
	char s[80];
	int i;
	symset set, set1, set2;

	printf("Please input source file name: \n"); // get file name to be compiled
	//scanf("%s", s);
	if ((infile = fopen("example.txt", "r")) == NULL)
	{
		printf("File %s can't be opened.\n", s);
		exit(1);
	}

	phi = createset(SYM_NULL);
	relset = createset(SYM_EQU, SYM_NEQ, SYM_LES, SYM_LEQ, SYM_GTR, SYM_GEQ, SYM_NULL);
	
	// create begin symbol sets
	declbegsys = createset(SYM_CONST, SYM_VAR, SYM_PROCEDURE, SYM_NULL);
	statbegsys = createset(SYM_BEGIN, SYM_CALL, SYM_IF, SYM_WHILE, SYM_NULL);
	facbegsys = createset(SYM_IDENTIFIER, SYM_NUMBER, SYM_LPAREN, SYM_MINUS,SYM_NOT,SYM_RANDOM, SYM_NULL);

	err = cc = cx = ll = 0; // initialize global variables
	ch = ' ';
	kk = MAXIDLEN;

	getsym();

	set1 = createset(SYM_PERIOD, SYM_NULL);
	set2 = uniteset(declbegsys, statbegsys);
	set = uniteset(set1, set2);
	block(set,0);
	destroyset(set1);
	destroyset(set2);
	destroyset(set);
	destroyset(phi);
	destroyset(relset);
	destroyset(declbegsys);
	destroyset(statbegsys);
	destroyset(facbegsys);

	if (sym != SYM_PERIOD)
		error(9); // '.' expected.
	gotobackpatch();
	if (err == 0)
	{
		hbin = fopen("hbin.txt", "w");
		for (i = 0; i < cx; i++)
			fwrite(&code[i], sizeof(instruction), 1, hbin);
		fclose(hbin);
	}
	listvar();
	fpstack=fopen("stacktest","w");
	if (err == 0)
		interpret();
	else
		printf("There are %d error(s) in PL/0 program.\n", err);
	listcode(0, cx);
	listlabel();
	listgt();
	printf("output:\n%s\n",output);
	fclose(fpstack);
} // main

//////////////////////////////////////////////////////////////////////
// eof pl0.c
