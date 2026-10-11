/* m6_word_L5.c -- exhaustive L=5: C' D1 C' D2 C' D3 C' D4 C' over F_16; count nnz-4 products (elementary
   transvection up to monomials) and print the first few. */
#include <stdio.h>
static int MUL[16][16];
static int mulf(int a,int b){int r=0;while(b){if(b&1)r^=a;b>>=1;a<<=1;if(a&16)a^=0x13;}return r;}
typedef struct{unsigned char m[3][3];} M3;
static M3 mm(M3 A,M3 B){M3 C;for(int i=0;i<3;i++)for(int j=0;j<3;j++){C.m[i][j]=MUL[A.m[i][0]][B.m[0][j]]^MUL[A.m[i][1]][B.m[1][j]]^MUL[A.m[i][2]][B.m[2][j]];}return C;}
static M3 rs(M3 A,int a,int b){for(int i=0;i<3;i++){A.m[i][1]=MUL[A.m[i][1]][a];A.m[i][2]=MUL[A.m[i][2]][b];}return A;}
int main(void){
  for(int a=0;a<16;a++)for(int b=0;b<16;b++)MUL[a][b]=mulf(a,b);
  int w=1; for(int i=0;i<5;i++) w=MUL[w][2]; int w2=MUL[w][w];
  M3 C={{{1,w2,w2},{w2,1,w2},{w2,w2,1}}};
  static M3 P2[225]; int da[225],db[225]; int n=0;
  for(int a=1;a<16;a++)for(int b=1;b<16;b++){da[n]=a;db[n]=b;P2[n++]=mm(rs(C,a,b),C);}
  long cnt4=0, hist[10]={0};
  for(int i=0;i<225;i++)for(int k=0;k<225;k++){
    M3 Y=mm(rs(P2[i],da[k],db[k]),C);              /* C'D1C'D2C' */
    for(int l=0;l<225;l++){ M3 X=rs(Y,da[l],db[l]);
      for(int j=0;j<225;j++){ M3 P=mm(X,P2[j]); int z=0;
        for(int r=0;r<3;r++)for(int c=0;c<3;c++) z+= P.m[r][c]!=0;
        hist[z]++;
        if(z==4){ if(cnt4<5){printf("hit D1=(1,%d,%d) D2=(1,%d,%d) D3=(1,%d,%d) D4=(1,%d,%d) P=",da[i],db[i],da[k],db[k],da[l],db[l],da[j],db[j]);
            for(int r=0;r<3;r++)printf("[%d %d %d]",P.m[r][0],P.m[r][1],P.m[r][2]);printf("\n");}
          cnt4++; } }}}
  printf("L=5 exhaustive: nnz histogram:"); for(int z=0;z<10;z++) if(hist[z]) printf(" %d:%ld",z,hist[z]); printf("\n");
  printf("nnz=4 count %ld\n",cnt4); return 0;}
