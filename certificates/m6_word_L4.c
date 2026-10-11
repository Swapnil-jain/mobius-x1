/* m6_word_L4.c -- exhaustive L=4: C' D1 C' D2 C' D3 C' over F_16 (D_i diagonal, first entry 1),
   histogram of nnz and classification of nnz-5 products (row-type A / column-type B / 2x2-block C / other). */
#include <stdio.h>
#include <string.h>
static int MUL[16][16];
static int mulf(int a,int b){int r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&16)a^=0x13;}return r;}
typedef struct{unsigned char m[3][3];} M3;
static M3 mm(M3 A,M3 B){M3 C;for(int i=0;i<3;i++)for(int j=0;j<3;j++){C.m[i][j]=MUL[A.m[i][0]][B.m[0][j]]^MUL[A.m[i][1]][B.m[1][j]]^MUL[A.m[i][2]][B.m[2][j]];}return C;}
static M3 rs(M3 A,int a,int b,int c){/* A*diag(1,a,b) */ for(int i=0;i<3;i++){A.m[i][1]=MUL[A.m[i][1]][a];A.m[i][2]=MUL[A.m[i][2]][b];}(void)c;return A;}
int main(void){
  for(int a=0;a<16;a++)for(int b=0;b<16;b++)MUL[a][b]=mulf(a,b);
  int w=1; for(int i=0;i<5;i++) w=MUL[w][2]; int w2=MUL[w][w];
  M3 C={{{1,w2,w2},{w2,1,w2},{w2,w2,1}}};
  static M3 P2[225]; int n=0;
  for(int a=1;a<16;a++)for(int b=1;b<16;b++) P2[n++]=mm(rs(C,a,b,0),C);   /* C' D C' */
  long hist[10]={0}; long typ[4]={0};
  for(int i=0;i<225;i++){
    for(int a=1;a<16;a++)for(int b=1;b<16;b++){
      M3 X=rs(P2[i],a,b,0);
      for(int j=0;j<225;j++){
        M3 P=mm(X,P2[j]); int z=0; int rc[3]={0},cc[3]={0};
        for(int r=0;r<3;r++)for(int c=0;c<3;c++) if(P.m[r][c]){z++;rc[r]++;cc[c]++;}
        hist[z]++;
        if(z==5){ int r3=0,c3=0,r2=0,c2=0; for(int t=0;t<3;t++){if(rc[t]==3)r3++;if(cc[t]==3)c3++;if(rc[t]==2)r2++;if(cc[t]==2)c2++;}
          if(r3) typ[0]++; else if(c3) typ[1]++; else if(r2==2&&c2==2) typ[2]++; else typ[3]++; }
      }}}
  printf("L=4 exhaustive (11390625 words): nnz histogram:");
  for(int z=0;z<10;z++) if(hist[z]) printf(" %d:%ld",z,hist[z]); printf("\n");
  printf("nnz=5 types: A(row of 3)=%ld B(col of 3)=%ld C(2x2 block+1)=%ld other=%ld\n",typ[0],typ[1],typ[2],typ[3]);
  return 0;}
