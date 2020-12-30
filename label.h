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
void enterlabel(char *lid,int codex){
    ltable[++lx].cx=codex;
    strcpy(ltable[lx].name,lid);
}
void entergoto(char *gid,int codex){
    gtlist[++gx].cx=codex;
    strcpy(gtlist[gx].name,gid);
}
void listlabel(){
    int i;
    for(i=1;i<=lx;i++){
        printf("%d: %s %d\n",i,ltable[i].name,ltable[i].cx);
    }
}

void listgt(){
    int i;
    for(i=1;i<=gx;i++){
        printf("%d: %s %d\n",i,gtlist[i].name,gtlist[i].cx);
    }
}