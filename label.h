//label.h
#include <stdio.h>
#include <string.h>
#define MAXLB 100
struct lbs{
    char name[20];
    int cx;
}ltable[MAXLB],gtlist[MAXLB];
int lx,gx,labelstatem;
int labelpos(char *lid){
    strcpy(ltable[0].name,lid);
    int i;
    for(i=lx;i>=0;i--){
        if(!strcmp(ltable[i].name,lid)) break;
    }
    return i;
}
void enterlabel(char *lid,char codex){
    ltable[++lx].cx=codex;
    strcpy(ltable[lx].name,lid);
}