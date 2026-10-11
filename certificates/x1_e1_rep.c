/* X1: full-network check of the E1 gadget (PROOF.md Theorem 2) by symmetry reduction.
 *
 * E1 = 7-subsets of [h] as F_3 labels, centre = all 3-subsets, side wires exactly on the
 * J-supported pairs (|S cap T| = 3), pre-pass (mu = 2, no correction kernel).
 * Mirrors x1_e2e_rep.c (Theorem 1): the label tables of PROOF.md Lemma 5.1 apply verbatim
 * (the three facts checked in [1c] below), so only the combinatorics block differs.
 *
 *  (1) Scalar network: ALL invocations at h <= 10, one representative invocation per stage at
 *      h = 11, 12 (Remark 5.2: Sym(h) is transitive on 7-subsets, so one invocation per stage
 *      describes all of them). Random F_4 values on every wire including auxiliaries, the 8-row
 *      schedule in all three stages. Checks (X,Y) -> (Y,X) and that every auxiliary is restored.
 *  (2) Frames, by brute-force F_3 linear algebra in F_3^m (m = h^3) on ONE representative
 *      invocation per stage (fixed indices = the first 7-subset T0), with every entry, every
 *      J-supported side-wire pair and every centre wire, plus the full bank path of d* =
 *      (T0,T0,T0) (source, the two stage boundaries, sink; no correction kernel: the pre-pass).
 *      Every edge: both labels nondegenerate, nesting, residual = big cap small^perp computed
 *      explicitly, residual dimension = dim difference, orthogonal basis with norms +-1 (fails
 *      loudly if degenerate).
 *      Every edge phase sum_j n_j (z_j.y)^2 is compared with Q(P_V y) - Q(P_U y) computed
 *      independently, for NF random frequencies y, and the phase sum along each wire is compared
 *      with its terminal labels.
 *  (3) Exact step count = sum over edges of residual dims, orbit-weighted: v^2 invocations per
 *      stage are images of the representative one, and all N0 bank paths are images of the d*
 *      path, under the isometries of F_3^m = (F_3^h)^{(x)3}. Compared with the closed form
 *      Wm - 2 N0 + 2 I0 c h (mu = 2) and with Delta = 2 v^2 (v - 3 c h).
 *
 * Build: cc -O2 -DH=11 -o x1_e1_rep11 x1_e1_rep.c
 * Run:   perl -e 'alarm 600; exec @ARGV' nice -n 15 ./x1_e1_rep11 [seed] [bad]
 *        bad=1: row-5 label uses the wrong entry's t-perp (nesting must fail);
 *        bad=2: centre = subsets of size 2 (Lemma 10.1 fails: C(n,2) odd at non-neighbour n=2).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#ifndef H
#define H 11
#endif
#define M (H*H*H)
#define NW ((M+63)/64)
#define NF 4
#define V ((H)*(H-1)*(H-2)*(H-3)*(H-4)*(H-5)*(H-6)/5040)
#define HH (H*H)
#define CMAX (1+H*(H-1)*(H-2)/6+H*(H-1)/2+2)

typedef struct { uint64_t a[NW], b[NW]; } vec;   /* a: coordinate == 1, b: coordinate == 2 */

static inline int vget(const vec *v, int i){ int w=i>>6,s=i&63; return (int)((v->a[w]>>s)&1) | (int)(((v->b[w]>>s)&1)<<1); }
static inline void vset(vec *v, int i, int x){ int w=i>>6,s=i&63; uint64_t m=1ULL<<s; v->a[w]&=~m; v->b[w]&=~m; if(x==1) v->a[w]|=m; else if(x==2) v->b[w]|=m; }
static inline void vadd(vec *r, const vec *x, const vec *y){
  for(int w=0;w<NW;w++){ uint64_t a1=x->a[w],a2=x->b[w],b1=y->a[w],b2=y->b[w];
    uint64_t a0=~(a1|a2), b0=~(b1|b2);
    uint64_t r1=(a0&b1)|(a1&b0)|(a2&b2), r2=(a0&b2)|(a2&b0)|(a1&b1);
    r->a[w]=r1; r->b[w]=r2; } }
static inline void vaxpy(vec *x, int f, const vec *z){ /* x += f z, f in {0,1,2} */
  if(f==0) return; if(f==1){ vadd(x,x,z); return; }
  vec nz; for(int w=0;w<NW;w++){ nz.a[w]=z->b[w]; nz.b[w]=z->a[w]; } vadd(x,x,&nz); }
static inline int vdot(const vec *x, const vec *y){
  int s=0; for(int w=0;w<NW;w++){ s+=__builtin_popcountll(x->a[w]&y->a[w])+__builtin_popcountll(x->b[w]&y->b[w]);
    s+=2*(__builtin_popcountll(x->a[w]&y->b[w])+__builtin_popcountll(x->b[w]&y->a[w])); } return s%3; }

/* fully reduced row echelon form over the first ncol coordinates; returns rank, pivots in piv[] */
static int rref(vec *rows, int n, int ncol, int *piv){
  int r=0;
  for(int col=0; col<ncol && r<n; col++){
    int p=-1; for(int i=r;i<n;i++) if(vget(&rows[i],col)){ p=i; break; }
    if(p<0) continue;
    vec t=rows[p]; rows[p]=rows[r]; rows[r]=t;
    if(vget(&rows[r],col)==2){ vec *x=&rows[r]; for(int w=0;w<NW;w++){ uint64_t q=x->a[w]; x->a[w]=x->b[w]; x->b[w]=q; } }
    for(int i=0;i<n;i++) if(i!=r){ int g=vget(&rows[i],col); if(g) vaxpy(&rows[i],(3-g)%3,&rows[r]); }
    piv[r++]=col;
  }
  return r;
}
/* nullspace of the rows (r x ncol, already in rref with pivots piv) as vectors over ncol coordinates */
static int nullspace(const vec *rows, int r, const int *piv, int ncol, vec *out){
  char *isp=calloc(ncol>0?ncol:1,1); for(int i=0;i<r;i++) isp[piv[i]]=1;
  int k=0;
  for(int f=0;f<ncol;f++) if(!isp[f]){ vec x; memset(&x,0,sizeof x); vset(&x,f,1);
    for(int i=0;i<r;i++){ int g=vget(&rows[i],f); if(g) vset(&x,piv[i],(3-g)%3); }
    out[k++]=x; }
  free(isp); return k;
}

/* orthogonal basis of span(in[0..n)) (n independent vectors); writes z[], norms nr[]; returns count or -1 if degenerate */
static int orth_basis(vec *in, int n, vec *z, int *nr){
  int cnt=0;
  while(n>0){ int i=-1,nz=0; for(int a=0;a<n;a++){ int q=vdot(&in[a],&in[a]); if(q){i=a;nz=q;break;} }
    if(i<0){ int pi=-1,pj=-1; for(int a=0;a<n&&pi<0;a++) for(int b=a+1;b<n;b++) if(vdot(&in[a],&in[b])){pi=a;pj=b;break;}
      if(pi<0) return -1; vadd(&in[pi],&in[pi],&in[pj]); i=pi; nz=vdot(&in[i],&in[i]); }
    vec w=in[i]; in[i]=in[n-1]; n--;
    for(int a=0;a<n;a++){ int g=vdot(&in[a],&w); if(g) vaxpy(&in[a],(3-(g*nz)%3)%3,&w); }
    z[cnt]=w; nr[cnt]=nz; cnt++; }
  return cnt;
}

/* ---------------- labels */
static vec Yf[NF]; static int QY[NF];
typedef struct { long id; int d; vec *basis; vec *perp; int qp[NF]; } label;
static long next_id=1, fail_nondeg=0, nlabels=0;

static label *label_new(const vec *span, int n){
  label *L=calloc(1,sizeof(label)); L->id=next_id++; nlabels++;
  vec *rows=malloc(sizeof(vec)*(n>0?n:1)); if(n) memcpy(rows,span,sizeof(vec)*n);
  int *piv=malloc(sizeof(int)*(M+1));
  int r=rref(rows,n,M,piv);
  L->d=r; L->basis=malloc(sizeof(vec)*(r>0?r:1)); if(r) memcpy(L->basis,rows,sizeof(vec)*r);
  L->perp=malloc(sizeof(vec)*(M-r>0?M-r:1));
  nullspace(rows,r,piv,M,L->perp);           /* U^perp for the standard dot product */
  free(rows); free(piv);
  /* nondegenerate + Q(P_L y) via an orthogonal basis of the smaller of L, L^perp (independent of the edge code) */
  int small=(r<=M-r); int k=small? r : M-r;
  vec *w=malloc(sizeof(vec)*(k>0?k:1)), *z=malloc(sizeof(vec)*(k>0?k:1)); int *nr=malloc(sizeof(int)*(k>0?k:1));
  if(k) memcpy(w, small? L->basis : L->perp, sizeof(vec)*k);
  int cnt = k? orth_basis(w,k,z,nr) : 0;
  if(cnt<0){ fail_nondeg++; cnt=0; }
  for(int f=0;f<NF;f++){ int s=0; for(int j=0;j<cnt;j++){ int c=vdot(&z[j],&Yf[f]); s+=nr[j]*c*c; } s%=3;
    L->qp[f]= small? s : (QY[f]-s+3)%3; }
  free(w); free(z); free(nr);
  return L;
}
static void label_free(label *L){ free(L->basis); free(L->perp); free(L); }

/* ---------------- edges */
static long fail_nest=0, fail_res=0, fail_degres=0, fail_phase=0, nedges=0;
typedef struct { long u,v; int rho, dec; unsigned char ph[NF]; } edge;
#define HS 65536
static edge cache[HS]; static char used[HS];

static edge *get_edge(label *U, label *Vl){
  unsigned long hsh=((unsigned long)U->id*1000003UL ^ (unsigned long)Vl->id*7919UL)%HS;
  while(used[hsh]){ if(cache[hsh].u==U->id && cache[hsh].v==Vl->id) return &cache[hsh]; hsh=(hsh+1)%HS; }
  used[hsh]=1; edge *e=&cache[hsh]; e->u=U->id; e->v=Vl->id; nedges++;
  label *sm,*bg; int inc;
  if(U->d<=Vl->d){ sm=U; bg=Vl; inc=1; } else { sm=Vl; bg=U; inc=0; }
  e->dec=!inc; e->rho=0; memset(e->ph,0,NF);
  int b=M-bg->d, a=M-sm->d;
  for(int i=0;i<sm->d;i++) for(int k=0;k<b;k++) if(vdot(&sm->basis[i],&bg->perp[k])){ fail_nest++; e->rho=-1; return e; }
  /* residual R = bg cap sm^perp, choosing the cheaper presentation */
  int rho_exp=bg->d-sm->d; vec *R=malloc(sizeof(vec)*(rho_exp>0?rho_exp:1)); int rho=0;
  if(rho_exp>0){
    if((long)sm->d*bg->d <= (long)a*b){       /* x = sum c_i bg.basis_i with x . sm.basis_k = 0 */
      vec *Cm=calloc(sm->d>0?sm->d:1,sizeof(vec)); int *pv=malloc(sizeof(int)*(bg->d+1));
      for(int k=0;k<sm->d;k++) for(int i=0;i<bg->d;i++) vset(&Cm[k],i,vdot(&sm->basis[k],&bg->basis[i]));
      int r=rref(Cm,sm->d,bg->d,pv);
      vec *ns=malloc(sizeof(vec)*(bg->d-r>0?bg->d-r:1)); int nn=nullspace(Cm,r,pv,bg->d,ns);
      for(int q=0;q<nn;q++){ vec x; memset(&x,0,sizeof x); for(int i=0;i<bg->d;i++){ int g=vget(&ns[q],i); if(g) vaxpy(&x,g,&bg->basis[i]); } R[rho++]=x; }
      free(Cm); free(pv); free(ns);
    } else {                                     /* x = sum c_i sm.perp_i with x . bg.perp_k = 0 */
      vec *Cm=calloc(b>0?b:1,sizeof(vec)); int *pv=malloc(sizeof(int)*(a+1));
      for(int k=0;k<b;k++) for(int i=0;i<a;i++) vset(&Cm[k],i,vdot(&bg->perp[k],&sm->perp[i]));
      int r=rref(Cm,b,a,pv);
      vec *ns=malloc(sizeof(vec)*(a-r>0?a-r:1)); int nn=nullspace(Cm,r,pv,a,ns);
      if(nn>rho_exp){ fail_res++; nn=rho_exp; }
      for(int q=0;q<nn;q++){ vec x; memset(&x,0,sizeof x); for(int i=0;i<a;i++){ int g=vget(&ns[q],i); if(g) vaxpy(&x,g,&sm->perp[i]); } R[rho++]=x; }
      free(Cm); free(pv); free(ns);
    }
  }
  if(rho!=rho_exp) fail_res++;
  vec *Z=malloc(sizeof(vec)*(rho>0?rho:1)); int *nr=malloc(sizeof(int)*(rho>0?rho:1));
  int cnt = rho? orth_basis(R,rho,Z,nr) : 0;
  if(cnt<0){ fail_degres++; cnt=0; }
  for(int j=0;j<cnt;j++){ for(int q=0;q<sm->d;q++) if(vdot(&Z[j],&sm->basis[q])){ fail_res++; break; }
    for(int q=0;q<b;q++) if(vdot(&Z[j],&bg->perp[q])){ fail_res++; break; } }
  e->rho=cnt;
  for(int f=0;f<NF;f++){ int s=0; for(int j=0;j<cnt;j++){ int c=vdot(&Z[j],&Yf[f]); s+=nr[j]*c*c; } s%=3;
    e->ph[f]=(unsigned char)(inc? s : (3-s)%3);
    if((Vl->qp[f]-U->qp[f]+3)%3 != e->ph[f]) fail_phase++; }
  free(R); free(Z); free(nr);
  return e;
}

/* nesting only (cheap): the vdot loop of get_edge without the residual/phase work.
   With nesting verified and the smaller label nondegenerate (checked in label_new), the residual
   dimension equals the dimension difference. */
static void check_nesting_only(label *U, label *Vl){
  label *sm = U->d<=Vl->d? U:Vl, *bg = U->d<=Vl->d? Vl:U;
  int b=M-bg->d;
  for(int i=0;i<sm->d;i++) for(int k=0;k<b;k++) if(vdot(&sm->basis[i],&bg->perp[k])){ fail_nest++; return; }
}

/* a wire path: accumulates steps and phases */
typedef struct { label *cur; long long steps, dec; int ph[NF]; } path;
static void go(path *p, label *L){
  if(p->cur==L) return;
  edge *e=get_edge(p->cur,L);
  if(e->rho>=0){ p->steps+=e->rho; if(e->dec) p->dec+=e->rho; for(int f=0;f<NF;f++) p->ph[f]=(p->ph[f]+e->ph[f])%3; }
  p->cur=L;
}
static long fail_wirephase=0;
static void path_end(path *p, label *src){ for(int f=0;f<NF;f++) if((p->cur->qp[f]-src->qp[f]+3)%3!=p->ph[f]) fail_wirephase++; }

/* ---------------- E1 combinatorics */
static int tv[V][H]; static int nb[V][V]; static int sw[V][V];
static int NC; static int cen[CMAX][3], cenSz[CMAX];
static int Rm[V][CMAX], Gm[CMAX][V], Jm[V][V];
static int bad=0;

static vec kron3(const int *e, int ne, const int *d, const int *q, int nq){
  vec x; memset(&x,0,sizeof x);
  for(int i=0;i<ne;i++) if(e[i]) for(int j=0;j<H;j++) if(d[j]) for(int k=0;k<nq;k++) if(q[k]){
    int idx=(i*H+j)*nq+k; vset(&x,idx,(e[i]*d[j]*q[k])%3); }
  return x;
}
static int perp_small(const int *p, int n, int out[][HH]){  /* basis of p^perp in F_3^n, p has a nonzero coordinate */
  int piv=-1; for(int i=0;i<n;i++) if(p[i]%3){ piv=i; break; }
  int pinv=p[piv]%3, cnt=0;
  for(int f=0;f<n;f++) if(f!=piv){ memset(out[cnt],0,sizeof(int)*HH); out[cnt][f]=1; out[cnt][piv]=(3-(p[f]%3)*pinv%3)%3; cnt++; }
  return cnt;
}

/* F_4: 0,1,w=2,w^2=3, addition = XOR */
static unsigned char rnd4(void){ return (unsigned char)(rand()&3); }

int main(int argc,char**argv){
  unsigned seed=argc>1?(unsigned)atoi(argv[1]):1; bad=argc>2?atoi(argv[2]):0; srand(seed);
  /* 7-subsets of [h] */
  int n=0; static int sub[V][7];
  { int c[7]; for(int i=0;i<7;i++) c[i]=i;
    for(;;){ for(int i=0;i<7;i++){ sub[n][i]=c[i]; tv[n][c[i]]=1; } n++;
      int i=6; while(i>=0 && c[i]==H-7+i) i--; if(i<0) break; c[i]++; for(int j=i+1;j<7;j++) c[j]=c[j-1]+1; } }
  long nnb=0, nnon=0, nsw=0, cnt_int[8]={0};
  for(int i=0;i<V;i++) for(int j=0;j<V;j++){ int it=0; for(int k=0;k<H;k++) it+=tv[i][k]&tv[j][k];
    nb[i][j]=(i!=j)&&(it%3==0); if(i!=j) cnt_int[it]++; if(nb[i][j]) nnb++; else if(i!=j) nnon++; }
  /* centre: 3-subsets (bad=2: 2-subsets, the refuted control) */
  NC=0;
  if(bad!=2){ for(int a=0;a<H;a++)for(int b=a+1;b<H;b++)for(int c=b+1;c<H;c++){
      cen[NC][0]=a; cen[NC][1]=b; cen[NC][2]=c; cenSz[NC]=3; NC++; } }
  else { cenSz[NC]=0; NC++;
    for(int a=0;a<H;a++){ cen[NC][0]=a; cenSz[NC]=1; NC++; }
    for(int a=0;a<H;a++)for(int b=a+1;b<H;b++){ cen[NC][0]=a; cen[NC][1]=b; cenSz[NC]=2; NC++; } }
  for(int p=0;p<NC;p++) for(int s=0;s<V;s++){ int in=1; for(int q=0;q<cenSz[p];q++) if(!tv[s][cen[p][q]]) in=0; Gm[p][s]=in; Rm[s][p]=in; }
  long idfail=0;
  for(int i=0;i<V;i++) for(int j=0;j<V;j++){ int s=0; for(int p=0;p<NC;p++) s^=Rm[i][p]&Gm[p][j]; Jm[i][j]=nb[i][j]? s:0;
    if(((s^Jm[i][j])&1)!=(i==j)) idfail++; }
  /* side-wire set = support of J: ordered pairs with |S cap T| = 3 */
  for(int i=0;i<V;i++) for(int j=0;j<V;j++){ int it=0; for(int k=0;k<H;k++) it+=tv[i][k]&tv[j][k];
    sw[i][j]=(i!=j)&&(it==3); if(sw[i][j]) nsw++; }
  long dn=nsw/V;
  printf("E1 h=%d m=%d v=%d centre=%d J-supported side wires/entry=%ld  ordered pairs by |S^T| (0..7):",
         H,M,V,NC,dn);
  for(int i=0;i<8;i++) printf(" %ld",cnt_int[i]); printf("  non-nbr=%ld bad=%d seed=%u\n",nnon,bad,seed);
  printf("[1a] scalar identity RG + JV = I over F_2 (V read on supp J): %ld wrong entries\n", idfail);

  /* [1c] the three facts behind PROOF.md Lemma 5.1 for E1, by enumeration */
  long f1=0,f2=0,f3=0;
  for(int i=0;i<V;i++){ int nn=0; for(int k=0;k<H;k++) nn+=tv[i][k]; if(nn%3!=1) f1++; }          /* norm 1 */
  for(int i=0;i<V;i++) for(int j=0;j<V;j++) if(nb[i][j]){ int d=0; for(int k=0;k<H;k++) d+=tv[i][k]*tv[j][k];
    if(d%3!=0) f2++; }                                                                          /* neighbours orthogonal */
  for(int i=0;i<V;i++) for(int j=0;j<V;j++) if(sw[i][j]){ int g[2][2];
    for(int a=0;a<2;a++) for(int b=0;b<2;b++){ int d=0; const int *u=a?tv[j]:tv[i], *w=b?tv[j]:tv[i];
      for(int k=0;k<H;k++) d+=u[k]*w[k]; g[a][b]=d%3; }
    if(!(g[0][0]==1&&g[1][1]==1&&g[0][1]==0&&g[1][0]==0)) f3++; }                                 /* Gram = I_2 */
  printf("[1c] three facts: norm!=1: %ld, neighbour not orthogonal: %ld, side-wire Gram != I2: %ld\n",f1,f2,f3);
  fflush(stdout);

  /* ---------------- (1) scalar network: all invocations (h <= 10), else one representative per stage.
     For all-invocations the three stages must swap the banks; for a representative invocation
     (which touches only a slice of the banks) Lemma 2.1' is verified per invocation. */
  int allinv = (H<=10);
  long N0=(long)V*V*V;
  unsigned char *X=malloc(N0), *Y=malloc(N0), *X0=malloc(N0), *Y0=malloc(N0);
  for(long d=0;d<N0;d++){ X[d]=X0[d]=rnd4(); Y[d]=Y0[d]=rnd4(); }
  static unsigned char A[V][V], A0[V][V]; static unsigned char Cw[CMAX], C0[CMAX];
  long auxbad=0, ninv=0, repbad=0;
  static unsigned char tgS[V], srS[V];
  for(int st=0;st<3;st++){
    int i1lo=0,i1hi=allinv?V:1, i2lo=0,i2hi=allinv?V:1;
    for(int i1=i1lo;i1<i1hi;i1++) for(int i2=i2lo;i2<i2hi;i2++){
    ninv++;
    long di[V]; for(int t=0;t<V;t++){ long d1,d2,d3; if(st==0){d1=t;d2=i1;d3=i2;} else if(st==1){d1=i1;d2=t;d3=i2;} else {d1=i1;d2=i2;d3=t;} di[t]=(d1*V+d2)*V+d3; }
    for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) A[S][T]=A0[S][T]=rnd4();
    for(int c=0;c<NC;c++) Cw[c]=C0[c]=rnd4();
    unsigned char *tg = st!=1? Y : X, *sr = st!=1? X : Y;   /* target, source (stage 2 is the inverse invocation) */
    if(!allinv) for(int t=0;t<V;t++){ tgS[t]=tg[di[t]]; srS[t]=sr[di[t]]; }
    /* rows 0..7 of the forward invocation sr -> tg; in characteristic 2 the inverse invocation of stage 2 is the same
       linear map, and its reversed row order is executed here as such (the order only matters for the labels) */
    if(st!=1){
      for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) tg[di[S]]^=A[S][T];
      for(int S=0;S<V;S++) for(int c=0;c<NC;c++) if(Rm[S][c]) tg[di[S]]^=Cw[c];
      for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) A[S][T]^=sr[di[T]];
      for(int c=0;c<NC;c++) for(int T=0;T<V;T++) if(Gm[c][T]) Cw[c]^=sr[di[T]];
      for(int S=0;S<V;S++) for(int c=0;c<NC;c++) if(Rm[S][c]) tg[di[S]]^=Cw[c];
      for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) tg[di[S]]^=A[S][T];
      for(int c=0;c<NC;c++) for(int T=0;T<V;T++) if(Gm[c][T]) Cw[c]^=sr[di[T]];
      for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) A[S][T]^=sr[di[T]];
    } else { /* reversed rows: A += V y, c += G y, x += J A, x += R c, c += G y, A += V y, x += R c, x += J A */
      for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) A[S][T]^=sr[di[T]];
      for(int c=0;c<NC;c++) for(int T=0;T<V;T++) if(Gm[c][T]) Cw[c]^=sr[di[T]];
      for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) tg[di[S]]^=A[S][T];
      for(int S=0;S<V;S++) for(int c=0;c<NC;c++) if(Rm[S][c]) tg[di[S]]^=Cw[c];
      for(int c=0;c<NC;c++) for(int T=0;T<V;T++) if(Gm[c][T]) Cw[c]^=sr[di[T]];
      for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) A[S][T]^=sr[di[T]];
      for(int S=0;S<V;S++) for(int c=0;c<NC;c++) if(Rm[S][c]) tg[di[S]]^=Cw[c];
      for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]) tg[di[S]]^=A[S][T];
    }
    for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]&&A[S][T]!=A0[S][T]) auxbad++;
    for(int c=0;c<NC;c++) if(Cw[c]!=C0[c]) auxbad++;
    if(!allinv) for(int t=0;t<V;t++){   /* Lemma 2.1' per invocation: tg -> tg + sr on the touched slice */
      if(tg[di[t]]!=(tgS[t]^srS[t])) repbad++; if(sr[di[t]]!=srS[t]) repbad++; }
    }
  }
  long swapbad=0;
  if(allinv){ for(long d=0;d<N0;d++){ if(X[d]!=Y0[d]) swapbad++; if(Y[d]!=X0[d]) swapbad++; } }
  else swapbad=repbad;
  printf("[1b] scalar network, %ld invocation(s)%s, random F_4 values: %s failures %ld / %ld, aux not restored %ld\n",
         ninv, allinv?" (all)":" (representative, one per stage)",
         allinv?"bank swap":"per-invocation y->y+x", swapbad, allinv?2*N0:6L*V, auxbad);
  fflush(stdout);
  if(bad==2 && (idfail>0 || swapbad>0)){ printf("control refuted as expected (scalar level)\n"); return 0; }

  /* ---------------- (2) frames on the representative invocations */
  for(int f=0;f<NF;f++){ memset(&Yf[f],0,sizeof(vec)); for(int i=0;i<M;i++) vset(&Yf[f],i,rand()%3); QY[f]=vdot(&Yf[f],&Yf[f]); }
  vec *units=malloc(sizeof(vec)*M); for(int i=0;i<M;i++){ memset(&units[i],0,sizeof(vec)); vset(&units[i],i,1); }
  label *FULL=label_new(units,M), *ZERO=label_new(NULL,0);
  int one[1]={1};
  /* d* = (T0,T0,T0), T0 = entry 0 */
  static int q2[HH]; for(int i=0;i<H;i++)for(int j=0;j<H;j++) q2[i*H+j]=tv[0][i]*tv[0][j];
  vec ustar=kron3(one,1,tv[0],q2,HH);
  printf("[2] u* . u* = %d (Lemma 6.1 needs norm 1)\n", vdot(&ustar,&ustar));
  label *Ustar=label_new(&ustar,1);
  path px={0}, py={0}; px.cur=Ustar; py.cur=ZERO;
  long long inv_steps[3]={0}, inv_dec[3]={0};
  long nside=0; long long outx=0, outy=0, outdec=0;
  for(int st=0;st<3;st++){
    memset(used,0,sizeof used);
    int ne = st==0?1:(st==1?H:HH), nq = st==2?1:(st==1?H:HH);
    static int p[HH], q[HH]; memset(p,0,sizeof p); memset(q,0,sizeof q);
    if(st==0){ p[0]=1; for(int i=0;i<HH;i++) q[i]=q2[i]; }
    if(st==1){ for(int i=0;i<H;i++){ p[i]=tv[0][i]; q[i]=tv[0][i]; } }
    if(st==2){ for(int i=0;i<HH;i++) p[i]=q2[i]; q[0]=1; }
    static int Bv[HH][HH]; int nB = st>0? perp_small(p,ne,Bv) : 0;
    static int ev[HH][HH]; for(int i=0;i<ne;i++){ memset(ev[i],0,sizeof ev[i]); ev[i][i]=1; }
    static int dv[H][H]; for(int i=0;i<H;i++){ memset(dv[i],0,sizeof dv[i]); dv[i][i]=1; }
    vec *span=malloc(sizeof(vec)*(M+8));
    int k=0; for(int i=0;i<nB;i++) for(int j=0;j<H;j++) span[k++]=kron3(Bv[i],ne,dv[j],q,nq);
    int k1=k; vec *BD=malloc(sizeof(vec)*(k1+H+1)); if(k1) memcpy(BD,span,sizeof(vec)*k1);
    label *L1=label_new(span,k);
    k=0; for(int i=0;i<ne;i++) for(int j=0;j<H;j++) span[k++]=kron3(ev[i],ne,dv[j],q,nq);
    label *L3=label_new(span,k);
    label *L0[V],*L2[V],*L5[V];
    for(int t=0;t<V;t++){
      k=0; for(int i=0;i<nB;i++) span[k++]=kron3(Bv[i],ne,tv[t],q,nq);
      L0[t]=label_new(span,k);
      k=k1; BD[k++]=kron3(p,ne,tv[t],q,nq);           /* BD[0..k1) holds B (x) D (x) q */
      L2[t]=label_new(BD,k);
      static int tp[HH][HH]; int tt=(bad==1&&t>0)? t-1 : t; int ntp=perp_small(tv[tt],H,tp);
      vec *s5=malloc(sizeof(vec)*(k1+H)); if(k1) memcpy(s5,BD,sizeof(vec)*k1);
      k=k1; for(int i=0;i<ntp;i++) s5[k++]=kron3(p,ne,tp[i],q,nq);
      L5[t]=label_new(s5,k); free(s5);
    }
    free(span); free(BD);
    long long s0=0, dec0=0;
    /* bank entries of the invocation: X touches rows 2,3,6,7; Y touches rows 0,1,4,5 */
    for(int t=0;t<V;t++){
      path a={0}; a.cur=L2[t]; go(&a,L3); s0+=a.steps; dec0+=a.dec;
      path b={0}; b.cur=L0[t]; go(&b,L1); go(&b,L5[t]); s0+=b.steps; dec0+=b.dec;
    }
    /* side wires A_{ST} on the J-supported pairs only: 0 -> L0[S] -> L2[T] -> L5[S] -> L3 -> FULL.
       All sw pairs lie in one Sym(h)-orbit (|S cap T| = 3), so the pair-dependent edges are fully
       checked on the first pair; every other pair gets an explicit nesting check on those edges
       (cheap), with its steps from the representative's (isometry-invariant residual dims) */
    long ns=0;
    { int S0=-1,T0=-1;
      for(int S=0;S<V&&S0<0;S++) for(int T=0;T<V;T++) if(sw[S][T]){ S0=S; T0=T; break; }
      if(S0>=0){
        path rp={0}; rp.cur=ZERO;
        go(&rp,L0[S0]); go(&rp,L2[T0]); go(&rp,L5[S0]); go(&rp,L3); go(&rp,FULL); path_end(&rp,ZERO);
        long long rsteps=rp.steps, rdec=rp.dec;
        for(int S=0;S<V;S++) for(int T=0;T<V;T++) if(sw[S][T]){
          if(!(S==S0&&T==T0)){ check_nesting_only(L0[S],L2[T]); check_nesting_only(L2[T],L5[S]); }
          s0+=rsteps; dec0+=rdec; ns++;
        }
      } }
    /* centre wires: 0 -> L1 -> L3 -> L1 -> L3 -> FULL */
    for(int c=0;c<NC;c++){
      path a={0}; a.cur=ZERO; go(&a,L1); go(&a,L3); go(&a,L1); go(&a,L3); go(&a,FULL); path_end(&a,ZERO);
      s0+=a.steps; dec0+=a.dec; }
    inv_steps[st]=s0; inv_dec[st]=dec0; nside=ns;
    /* bank path of d*: the full path is followed for the phase check; only the edges outside invocations
       (source -> first touch, stage boundaries, sinks) are added to the count, the rest is already in s0 */
    { long long b4=px.steps, d4=px.dec; go(&px,L2[0]); outx+=px.steps-b4; outdec+=px.dec-d4; go(&px,L3); }
    { long long b4=py.steps, d4=py.dec; go(&py,L0[0]); outy+=py.steps-b4; outdec+=py.dec-d4; go(&py,L1); go(&py,L5[0]); }
    printf("[2] stage %d representative invocation: %d labels, steps %lld (decrease %lld), side wires %ld, centre %d; "
           "edges so far %ld; fails nondeg %ld nest %ld res %ld degres %ld phase %ld wirephase %ld\n",
           st+1, 3*V+2, s0, dec0, ns, NC, nedges, fail_nondeg, fail_nest, fail_res, fail_degres, fail_phase, fail_wirephase);
    fflush(stdout);
    /* the next stage needs L3 and L5[0] of this stage as the d* boundary labels; keep them, free the rest */
    for(int t=0;t<V;t++){ label_free(L0[t]); label_free(L2[t]); if(t) label_free(L5[t]); }
    label_free(L1);
  }
  /* d* sinks (no correction kernel: Theorem 2 uses the pre-pass, mu = 2) */
  { long long b4=px.steps, d4=px.dec; go(&px,FULL); outx+=px.steps-b4; outdec+=px.dec-d4; path_end(&px,Ustar); }
  vec *pp=malloc(sizeof(vec)*(M-1)); memcpy(pp,Ustar->perp,sizeof(vec)*(M-1)); label *Up=label_new(pp,M-1); free(pp);
  { long long b4=py.steps, d4=py.dec; go(&py,Up); outy+=py.steps-b4; outdec+=py.dec-d4; path_end(&py,ZERO); }
  long long bank_out = outx + outy;   /* mu = 2: no correction kernel */
  long long I0v=(long long)V*V;
  long long total = I0v*(inv_steps[0]+inv_steps[1]+inv_steps[2]) + N0*bank_out;
  long long totdec = I0v*(inv_dec[0]+inv_dec[1]+inv_dec[2]) + N0*outdec;
  long long I0=3*I0v, Wl=2*N0 + I0*(nside+NC);
  long long pred = Wl*M - 2*N0 + 2*I0*NC*H;
  printf("[3] d* path: edges outside invocations X %lld, Y %lld (no correction: pre-pass mu=2), decrease %lld; whole path X %lld, Y %lld\n", outx, outy, outdec, px.steps, py.steps);
  printf("[3] W = %lld; orbit-weighted exact steps = %lld; closed form Wm - 2 N0 + 2 I0 c h = %lld; match=%s; "
         "decrease %lld (pred I0 c h = %lld)\n", Wl, total, pred, total==pred?"YES":"NO", totdec, I0*NC*H);
  printf("[3] Delta = Wm - steps = %lld  (2 v^2 (v - 3ch) = %lld)\n", Wl*M-total, 2LL*V*V*((long long)V-3LL*NC*H));
  printf("FAIL totals: nondeg %ld nest %ld residual %ld degenerate-residual %ld edge-phase %ld wire-phase %ld | labels %ld edges %ld\n",
         fail_nondeg, fail_nest, fail_res, fail_degres, fail_phase, fail_wirephase, nlabels, nedges);
  return 0;
}
