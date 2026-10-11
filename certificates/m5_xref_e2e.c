/* Independent per-frequency end-to-end simulation of the FLIPPED Section-2 network
 * (proofs/PROOF.md), written from scratch.
 *
 * Labels: subspaces of F_3^m, m = h^3, h = 6 (4-subsets of [6]; neighbours = |S^T| in {0,3};
 *         non-neighbours |S^T| = 2 are present).  Data: F_4.
 * Every wire carries one F_4 scalar per random frequency y in F_3^m (NF frequencies).
 * Every edge U -> V (consecutive touches of a physical wire, plus source/sink) is processed by brute-force
 * F_3 linear algebra in F_3^216:  check nesting, compute the residual R = big cap small^perp explicitly,
 * find an orthogonal basis z_j (norms n_j = +-1) of R (fails loudly if R is degenerate), and multiply the
 * wire by w^{+- sum_j n_j (z_j.y)^2}  (= the product of rho directional kernels K_{z_j}, Lemma 2.2').
 * Gates are the real scalar maps (R, G from the centre "subsets of size <= 2", J = RG on neighbour pairs).
 * At the sinks: every role must equal w^{Q(y)} * (routed source value); for Y_d one correction kernel
 * w^{-(u_d.y)^2} is applied first and counted as one step.
 * Also counts total steps (sum of residual dims + corrections) and the total decrease.
 *
 * Build: cc -O2 -o m5_xref_e2e m5_xref_e2e.c
 * Run:   perl -e 'alarm 600; exec @ARGV' nice -n 15 ./m5_xref_e2e [seed] [bad]
 *        bad=1: negative control, neighbours := |S^T| = 3 only is kept but side label t^perp replaced
 *        by <t>^perp of the WRONG entry (should fail nesting);  bad=2: drop the sink correction kernel
 *        (Y_d roles should fail);  bad=3: centre = subsets of size <= 1 (scalar network should fail).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define H 6
#define M (H*H*H)
#define NW ((M+63)/64)
#define NF 4
#define V 15          /* C(6,4) */

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
static inline int viszero(const vec *x){ for(int w=0;w<NW;w++) if(x->a[w]|x->b[w]) return 0; return 1; }

/* fully reduced row echelon form in place; returns rank, rows[0..r) independent, piv[] pivots */
static int rref(vec *rows, int n, int *piv){
  int r=0;
  for(int col=0; col<M && r<n; col++){
    int p=-1; for(int i=r;i<n;i++) if(vget(&rows[i],col)){ p=i; break; }
    if(p<0) continue;
    vec t=rows[p]; rows[p]=rows[r]; rows[r]=t;
    if(vget(&rows[r],col)==2){ vec *x=&rows[r]; for(int w=0;w<NW;w++){ uint64_t q=x->a[w]; x->a[w]=x->b[w]; x->b[w]=q; } }
    for(int i=0;i<n;i++) if(i!=r){ int g=vget(&rows[i],col); if(g) vaxpy(&rows[i],(3-g)%3,&rows[r]); }
    piv[r++]=col;
  }
  return r;
}

typedef struct label { long id; int d; vec *basis; vec *perp; int ref; int perm; } label;
static long next_id=1; static long nlabels=0, nlabels_alive=0, maxalive=0;
static long fail_nondeg=0;

static int gram_rank(vec *v, int k){ /* rank of k x k Gram matrix over F_3 */
  if(k==0) return 0;
  unsigned char *g=malloc((size_t)k*k);
  for(int i=0;i<k;i++) for(int j=i;j<k;j++){ int x=vdot(&v[i],&v[j]); g[i*k+j]=g[j*k+i]=(unsigned char)x; }
  int r=0;
  for(int c=0;c<k && r<k;c++){
    int p=-1; for(int i=r;i<k;i++) if(g[i*k+c]){p=i;break;} if(p<0) continue;
    if(p!=r) for(int j=0;j<k;j++){ unsigned char t=g[p*k+j]; g[p*k+j]=g[r*k+j]; g[r*k+j]=t; }
    int inv=g[r*k+c]; /* 1 or 2, self-inverse */
    for(int j=0;j<k;j++) g[r*k+j]=(unsigned char)((g[r*k+j]*inv)%3);
    for(int i=0;i<k;i++) if(i!=r && g[i*k+c]){ int f=g[i*k+c]; for(int j=0;j<k;j++) g[i*k+j]=(unsigned char)((g[i*k+j]+3*3-f*g[r*k+j])%3); }
    r++;
  }
  free(g); return r;
}

static label *label_new(const vec *span, int n, int perm){
  label *L=calloc(1,sizeof(label)); L->id=next_id++; L->perm=perm; L->ref=1;
  vec *rows=malloc(sizeof(vec)*(n>0?n:1)); if(n) memcpy(rows,span,sizeof(vec)*n);
  int *piv=malloc(sizeof(int)*(M+1));
  int r=rref(rows,n,piv);
  L->d=r; L->basis=malloc(sizeof(vec)*(r>0?r:1)); if(r) memcpy(L->basis,rows,sizeof(vec)*r);
  /* nullspace = U^perp (standard dot product) */
  char ispiv[M]; memset(ispiv,0,M); for(int i=0;i<r;i++) ispiv[piv[i]]=1;
  L->perp=malloc(sizeof(vec)*(M-r>0?M-r:1)); int k=0;
  for(int f=0;f<M;f++) if(!ispiv[f]){ vec x; memset(&x,0,sizeof x); vset(&x,f,1);
    for(int i=0;i<r;i++){ int g=vget(&L->basis[i],f); if(g) vset(&x,piv[i],(3-g)%3); }
    L->perp[k++]=x; }
  free(rows); free(piv);
  /* nondegeneracy: Gram of the smaller side has full rank */
  if(r<=M-r){ if(gram_rank(L->basis,r)!=r) fail_nondeg++; } else { if(gram_rank(L->perp,M-r)!=M-r) fail_nondeg++; }
  nlabels++; nlabels_alive++; if(nlabels_alive>maxalive) maxalive=nlabels_alive;
  return L;
}
static void label_release(label *L){ if(L->perm) return; if(--L->ref==0){ free(L->basis); free(L->perp); free(L); nlabels_alive--; } }

/* ---------------- frequencies, F_4 */
static vec Y[NF]; static int QY[NF];
static unsigned char MW[3][4]; /* multiply by w^e */
static unsigned char f4mul(int a,int b){ int a0=a&1,a1=a>>1,b0=b&1,b1=b>>1; int c0=(a0&b0)^(a1&b1), c1=(a0&b1)^(a1&b0)^(a1&b1); return (unsigned char)(c0|(c1<<1)); }

/* ---------------- edges */
typedef struct { long u,v; int rho; int sgn; unsigned char ph[NF]; int used; } edge;
#define HS 16384
static edge cache[HS];
static long fail_nest=0, fail_res=0, fail_degres=0, nedges_distinct=0;
static long long steps=0, decr=0;

static long long xchk=0, xchk_fail=0;
static int QP(label *L, int f){ /* Q(P_L y_f), computed independently via an orthogonal basis of L or L^perp */
  int small = (L->d <= M-L->d);
  int k = small? L->d : M-L->d; if(k==0) return small? 0 : QY[f];
  vec *w=malloc(sizeof(vec)*k); memcpy(w, small? L->basis : L->perp, sizeof(vec)*k);
  int *nr=malloc(sizeof(int)*k);
  /* orth_basis writes results into w[0..cnt) */
  vec *tmp=malloc(sizeof(vec)*k); memcpy(tmp,w,sizeof(vec)*k);
  int cnt=0; int n=k;
  while(n>0){ int i=-1,nz=0; for(int a=0;a<n;a++){ int q=vdot(&tmp[a],&tmp[a]); if(q){i=a;nz=q;break;} }
    if(i<0){ int pi=-1,pj=-1; for(int a=0;a<n&&pi<0;a++) for(int b=a+1;b<n;b++) if(vdot(&tmp[a],&tmp[b])){pi=a;pj=b;break;}
      if(pi<0){ free(w);free(nr);free(tmp); return -1; } vadd(&tmp[pi],&tmp[pi],&tmp[pj]); i=pi; nz=vdot(&tmp[i],&tmp[i]); }
    vec z=tmp[i]; tmp[i]=tmp[n-1]; n--;
    for(int a=0;a<n;a++){ int g=vdot(&tmp[a],&z); if(g) vaxpy(&tmp[a],(3-(g*nz)%3)%3,&z); }
    w[cnt]=z; nr[cnt]=nz; cnt++; }
  int s=0; for(int j=0;j<cnt;j++){ int c=vdot(&w[j],&Y[f]); s+=nr[j]*c*c; }
  free(w); free(nr); free(tmp);
  s%=3; return small? s : (QY[f]-s+3)%3;
}

static edge *get_edge(label *U, label *Vl){
  unsigned long hsh=((unsigned long)U->id*1000003UL ^ (unsigned long)Vl->id*7919UL)%HS;
  while(cache[hsh].used){ if(cache[hsh].u==U->id && cache[hsh].v==Vl->id) return &cache[hsh]; hsh=(hsh+1)%HS; }
  edge *e=&cache[hsh]; e->used=1; e->u=U->id; e->v=Vl->id; nedges_distinct++;
  label *sm,*bg; int sgn;
  if(U->d<=Vl->d){ sm=U; bg=Vl; sgn=1; } else { sm=Vl; bg=U; sgn=-1; }
  e->sgn=sgn; e->rho=0; memset(e->ph,0,NF);
  /* nesting: sm subset bg  <=>  sm.basis perp bg.perp */
  int nested=1;
  for(int i=0;i<sm->d && nested;i++) for(int k=0;k<M-bg->d;k++) if(vdot(&sm->basis[i],&bg->perp[k])){ nested=0; break; }
  if(!nested){ fail_nest++; e->rho=-1; return e; }
  /* residual R = bg cap sm^perp = { sum c_i w_i : w_i in sm.perp, (sum c_i w_i).n_k = 0 for n_k in bg.perp } */
  int a=M-sm->d, b=M-bg->d;
  unsigned char *C=malloc((size_t)(b>0?b:1)*(a>0?a:1));
  for(int k=0;k<b;k++) for(int i=0;i<a;i++) C[k*a+i]=(unsigned char)vdot(&bg->perp[k],&sm->perp[i]);
  int *pv=malloc(sizeof(int)*(a+1)); int r=0;
  for(int c=0;c<a && r<b;c++){
    int p=-1; for(int i=r;i<b;i++) if(C[i*a+c]){p=i;break;} if(p<0) continue;
    if(p!=r) for(int j=0;j<a;j++){ unsigned char t=C[p*a+j]; C[p*a+j]=C[r*a+j]; C[r*a+j]=t; }
    int inv=C[r*a+c]; for(int j=0;j<a;j++) C[r*a+j]=(unsigned char)((C[r*a+j]*inv)%3);
    for(int i=0;i<b;i++) if(i!=r && C[i*a+c]){ int f=C[i*a+c]; for(int j=0;j<a;j++) C[i*a+j]=(unsigned char)((C[i*a+j]+9-f*C[r*a+j])%3); }
    pv[r++]=c;
  }
  int rho=a-r;
  if(rho!=bg->d-sm->d){ fail_res++; }
  char *isp=calloc(a>0?a:1,1); for(int i=0;i<r;i++) isp[pv[i]]=1;
  vec *R=malloc(sizeof(vec)*(rho>0?rho:1)); int k=0;
  for(int f=0;f<a;f++) if(!isp[f]){ vec x=sm->perp[f];
    for(int i=0;i<r;i++){ int g=C[i*a+f]; if(g) vaxpy(&x,(3-g)%3,&sm->perp[pv[i]]); }
    R[k++]=x; }
  int *nr=malloc(sizeof(int)*(rho>0?rho:1));
  /* orthogonal basis: results collected in Z */
  vec *Z=malloc(sizeof(vec)*(rho>0?rho:1)); int cnt=0, n=rho, deg=0;
  while(n>0){ int i=-1,nz=0; for(int q=0;q<n;q++){ int t=vdot(&R[q],&R[q]); if(t){i=q;nz=t;break;} }
    if(i<0){ int pi=-1,pj=-1; for(int x=0;x<n&&pi<0;x++) for(int y=x+1;y<n;y++) if(vdot(&R[x],&R[y])){pi=x;pj=y;break;}
      if(pi<0){ deg=1; break; } vadd(&R[pi],&R[pi],&R[pj]); i=pi; nz=vdot(&R[i],&R[i]); }
    vec z=R[i]; R[i]=R[n-1]; n--;
    for(int q=0;q<n;q++){ int g=vdot(&R[q],&z); if(g) vaxpy(&R[q],(3-(g*nz)%3)%3,&z); }
    Z[cnt]=z; nr[cnt]=nz; cnt++; }
  if(deg){ fail_degres++; }
  /* residual vectors must be in bg and orthogonal to sm (sanity) */
  for(int j=0;j<cnt;j++){ for(int q=0;q<sm->d;q++) if(vdot(&Z[j],&sm->basis[q])) fail_res++; for(int q=0;q<b;q++) if(vdot(&Z[j],&bg->perp[q])) fail_res++; }
  e->rho=cnt;
  for(int f=0;f<NF;f++){ int s=0; for(int j=0;j<cnt;j++){ int c=vdot(&Z[j],&Y[f]); s+=nr[j]*c*c; } s%=3; e->ph[f]=(unsigned char)(sgn>0? s : (3-s)%3); }
  /* independent cross-check on a sample: phase == Q(P_V y) - Q(P_U y) */
  if((nedges_distinct % 97)==1){ for(int f=0;f<NF;f++){ int qv=QP(Vl,f), qu=QP(U,f); xchk++; if(qv<0||qu<0|| (qv-qu+3)%3!=e->ph[f]) xchk_fail++; } }
  free(C); free(pv); free(isp); free(R); free(nr); free(Z);
  return e;
}

/* ---------------- wires */
typedef struct { label *cur; unsigned char val[NF], init[NF]; } wire;
static void touch(wire *w, label *L){
  if(w->cur==L) return;
  edge *e=get_edge(w->cur,L);
  if(e->rho<0){ /* not nested: still move on, failure counted */ }
  else { steps+=e->rho; if(e->sgn<0) decr+=e->rho; for(int f=0;f<NF;f++) w->val[f]=MW[e->ph[f]][w->val[f]]; }
  L->ref++; label_release(w->cur); w->cur=L;
}

/* ---------------- combinatorics */
static int sub[V][4]; static signed char tv[V][H];   /* 4-subsets and their indicators */
static int nb[V][V];      /* neighbour */
static int NC; static int cen[64][2], cenSz[64];
static int Rm[V][64], Gm[64][V]; static int Jm[V][V];
static int bad=0;

static void small_nullspace(const signed char *p, int n, signed char out[][36], int *cnt){
  /* basis of { x in F_3^n : x.p = 0 } for a single vector p with a nonzero coordinate */
  int piv=-1; for(int i=0;i<n;i++) if(p[i]%3){ piv=i; break; }
  int pinv=p[piv]%3; /* 1 or 2, self inverse */
  *cnt=0;
  for(int f=0;f<n;f++) if(f!=piv){ memset(out[*cnt],0,36); out[*cnt][f]=1; out[*cnt][piv]=(signed char)((3-(p[f]%3)*pinv%3)%3); (*cnt)++; }
}

static vec kron3(const signed char *e, int ne, const signed char *d, const signed char *q, int nq){
  vec x; memset(&x,0,sizeof x);
  for(int i=0;i<ne;i++) if(e[i]) for(int j=0;j<H;j++) if(d[j]) for(int k=0;k<nq;k++) if(q[k]){
    int idx=(i*H+j)*nq+k; vset(&x,idx,(e[i]*d[j]*q[k])%3); }
  return x;
}

int main(int argc,char**argv){
  unsigned seed=argc>1?(unsigned)atoi(argv[1]):1; bad=argc>2?atoi(argv[2]):0; srand(seed);
  for(int e=0;e<3;e++) for(int x=0;x<4;x++){ int wpow = e==0?1:(e==1?2:3); MW[e][x]=f4mul(wpow,x); }
  /* 4-subsets */
  int n=0; for(int a=0;a<H;a++)for(int b=a+1;b<H;b++)for(int c=b+1;c<H;c++)for(int d=c+1;d<H;d++){
    sub[n][0]=a;sub[n][1]=b;sub[n][2]=c;sub[n][3]=d; memset(tv[n],0,H); tv[n][a]=tv[n][b]=tv[n][c]=tv[n][d]=1; n++; }
  if(n!=V){ printf("bad V\n"); return 1; }
  int nnb=0, nnon=0;
  for(int i=0;i<V;i++) for(int j=0;j<V;j++){ int it=0; for(int k=0;k<H;k++) it+=tv[i][k]&tv[j][k];
    nb[i][j]= (i!=j) && (it%3==0); if(nb[i][j]) nnb++; else if(i!=j) nnon++; }
  /* centre: subsets of size <= 2 (bad=3: size <= 1) */
  NC=0; cenSz[NC]=0; NC++;
  for(int a=0;a<H;a++){ cenSz[NC]=1; cen[NC][0]=a; NC++; }
  if(bad!=3) for(int a=0;a<H;a++)for(int b=a+1;b<H;b++){ cenSz[NC]=2; cen[NC][0]=a; cen[NC][1]=b; NC++; }
  for(int p=0;p<NC;p++) for(int s=0;s<V;s++){ int in=1; for(int q=0;q<cenSz[p];q++) if(!tv[s][cen[p][q]]) in=0; Gm[p][s]=in; Rm[s][p]=in; }
  for(int i=0;i<V;i++) for(int j=0;j<V;j++){ int s=0; for(int p=0;p<NC;p++) s^=Rm[i][p]&Gm[p][j]; Jm[i][j]= nb[i][j]? s : 0; }
  printf("h=%d m=%d v=%d centre=%d ordered nbr pairs=%d non-nbr pairs=%d bad=%d seed=%u\n",H,M,V,NC,nnb,nnon,bad,seed);
  /* frequencies */
  for(int f=0;f<NF;f++){ memset(&Y[f],0,sizeof(vec)); for(int i=0;i<M;i++) vset(&Y[f],i,rand()%3); QY[f]=vdot(&Y[f],&Y[f]); }
  /* permanent labels */
  vec *units=malloc(sizeof(vec)*M); for(int i=0;i<M;i++){ memset(&units[i],0,sizeof(vec)); vset(&units[i],i,1); }
  label *FULL=label_new(units,M,1), *ZERO=label_new(NULL,0,1);
  /* banks */
  int NB=V*V*V; wire *X=calloc(NB,sizeof(wire)), *Yb=calloc(NB,sizeof(wire));
  for(int d=0;d<NB;d++){ for(int f=0;f<NF;f++){ X[d].init[f]=X[d].val[f]=(unsigned char)(rand()&3); Yb[d].init[f]=Yb[d].val[f]=(unsigned char)(rand()&3); }
    X[d].cur=NULL; Yb[d].cur=ZERO; }
  long nwires=2L*NB; long auxfail=0, invoc=0;
  signed char one[1]={1};
  for(int st=0;st<3;st++) for(int A1=0;A1<V;A1++) for(int A2=0;A2<V;A2++){
    invoc++;
    memset(cache,0,sizeof cache);
    int didx[V];  /* bank index for each value t of the varying index */
    for(int t=0;t<V;t++){ int d1,d2,d3; if(st==0){d1=t;d2=A1;d3=A2;} else if(st==1){d1=A1;d2=t;d3=A2;} else {d1=A1;d2=A2;d3=t;} didx[t]=(d1*V+d2)*V+d3; }
    /* component spaces */
    int ne = st==0?1:(st==1?H:H*H), nq = st==2?1:(st==1?H:H*H);
    static signed char p[36], q[36]; memset(p,0,36); memset(q,0,36);
    if(st==0){ p[0]=1; for(int i=0;i<H;i++)for(int j=0;j<H;j++) q[i*H+j]=(signed char)(tv[A1][i]*tv[A2][j]); }
    if(st==1){ for(int i=0;i<H;i++) p[i]=tv[A1][i]; for(int i=0;i<H;i++) q[i]=tv[A2][i]; }
    if(st==2){ for(int i=0;i<H;i++)for(int j=0;j<H;j++) p[i*H+j]=(signed char)(tv[A1][i]*tv[A2][j]); q[0]=1; }
    static signed char Bv[36][36]; int nB=0;
    if(st>0) small_nullspace(p,ne,Bv,&nB);   /* B = p^perp in E */
    static signed char ev[36][36]; for(int i=0;i<ne;i++){ memset(ev[i],0,36); ev[i][i]=1; }
    static signed char dv[H][H]; for(int i=0;i<H;i++){ memset(dv[i],0,H); dv[i][i]=1; }
    vec *span=malloc(sizeof(vec)*(M+8));
    /* L1 = B (x) D (x) q */
    int k=0; for(int i=0;i<nB;i++) for(int j=0;j<H;j++) span[k++]=kron3(Bv[i],ne,dv[j],q,nq);
    label *L1=label_new(span,k,0);
    int k1=k;
    /* L3 = E (x) D (x) q */
    k=0; for(int i=0;i<ne;i++) for(int j=0;j<H;j++) span[k++]=kron3(ev[i],ne,dv[j],q,nq);
    label *L3=label_new(span,k,0);
    label *L0[V],*L2[V],*L5[V];
    for(int t=0;t<V;t++){
      k=0; for(int i=0;i<nB;i++) span[k++]=kron3(Bv[i],ne,tv[t],q,nq);
      L0[t]=label_new(span,k,0);
      k=0; for(int i=0;i<nB;i++) for(int j=0;j<H;j++) span[k++]=kron3(Bv[i],ne,dv[j],q,nq);
      span[k++]=kron3(p,ne,tv[t],q,nq);
      L2[t]=label_new(span,k,0);
      k=k1; static signed char tp[36][36]; int ntp;
      int tt = (bad==1 && t>0)? t-1 : t;   /* negative control: wrong entry's t^perp */
      small_nullspace(tv[tt],H,tp,&ntp);
      for(int i=0;i<ntp;i++) span[k++]=kron3(p,ne,tp[i],q,nq);
      L5[t]=label_new(span,k,0);
    }
    /* stage-1 sources: X_d has label U_d = <t1 (x) t2 (x) t3> */
    if(st==0) for(int t=0;t<V;t++){ int d=didx[t]; vec u=kron3(one,1,tv[t],q,nq); label *U=label_new(&u,1,0); X[d].cur=U; }
    free(span);
    /* auxiliaries */
    static wire Aw[V][V]; static wire Cw[64];
    for(int i=0;i<V;i++) for(int j=0;j<V;j++) if(nb[i][j]){ Aw[i][j].cur=ZERO; for(int f=0;f<NF;f++) Aw[i][j].init[f]=Aw[i][j].val[f]=(unsigned char)(rand()&3); }
    for(int c=0;c<NC;c++){ Cw[c].cur=ZERO; for(int f=0;f<NF;f++) Cw[c].init[f]=Cw[c].val[f]=(unsigned char)(rand()&3); }
    nwires += nnb + NC;
    wire *xs[V], *ys[V]; for(int t=0;t<V;t++){ xs[t]=&X[didx[t]]; ys[t]=&Yb[didx[t]]; }
    if(st!=1){ /* forward X -> Y : y += (RG + JV) x */
      for(int S=0;S<V;S++){ touch(ys[S],L0[S]); for(int T=0;T<V;T++) if(nb[S][T]){ touch(&Aw[S][T],L0[S]); if(Jm[S][T]) for(int f=0;f<NF;f++) ys[S]->val[f]^=Aw[S][T].val[f]; } }
      for(int S=0;S<V;S++) touch(ys[S],L1); for(int c=0;c<NC;c++) touch(&Cw[c],L1);
      for(int S=0;S<V;S++) for(int c=0;c<NC;c++) if(Rm[S][c]) for(int f=0;f<NF;f++) ys[S]->val[f]^=Cw[c].val[f];
      for(int T=0;T<V;T++){ touch(xs[T],L2[T]); for(int S=0;S<V;S++) if(nb[S][T]){ touch(&Aw[S][T],L2[T]); for(int f=0;f<NF;f++) Aw[S][T].val[f]^=xs[T]->val[f]; } }
      for(int T=0;T<V;T++) touch(xs[T],L3); for(int c=0;c<NC;c++) touch(&Cw[c],L3);
      for(int c=0;c<NC;c++) for(int T=0;T<V;T++) if(Gm[c][T]) for(int f=0;f<NF;f++) Cw[c].val[f]^=xs[T]->val[f];
      for(int S=0;S<V;S++) touch(ys[S],L1); for(int c=0;c<NC;c++) touch(&Cw[c],L1);
      for(int S=0;S<V;S++) for(int c=0;c<NC;c++) if(Rm[S][c]) for(int f=0;f<NF;f++) ys[S]->val[f]^=Cw[c].val[f];
      for(int S=0;S<V;S++){ touch(ys[S],L5[S]); for(int T=0;T<V;T++) if(nb[S][T]){ touch(&Aw[S][T],L5[S]); if(Jm[S][T]) for(int f=0;f<NF;f++) ys[S]->val[f]^=Aw[S][T].val[f]; } }
      for(int T=0;T<V;T++) touch(xs[T],L3); for(int c=0;c<NC;c++) touch(&Cw[c],L3);
      for(int c=0;c<NC;c++) for(int T=0;T<V;T++) if(Gm[c][T]) for(int f=0;f<NF;f++) Cw[c].val[f]^=xs[T]->val[f];
      for(int T=0;T<V;T++){ touch(xs[T],L3); for(int S=0;S<V;S++) if(nb[S][T]){ touch(&Aw[S][T],L3); for(int f=0;f<NF;f++) Aw[S][T].val[f]^=xs[T]->val[f]; } }
    } else { /* stage 2: inverse of forward Y -> X : x += (RG + JV) y ; side A[S][T], S = X entry, T = Y entry */
      for(int T=0;T<V;T++){ touch(ys[T],L0[T]); for(int S=0;S<V;S++) if(nb[S][T]){ touch(&Aw[S][T],L0[T]); for(int f=0;f<NF;f++) Aw[S][T].val[f]^=ys[T]->val[f]; } }
      for(int T=0;T<V;T++) touch(ys[T],L1); for(int c=0;c<NC;c++) touch(&Cw[c],L1);
      for(int c=0;c<NC;c++) for(int T=0;T<V;T++) if(Gm[c][T]) for(int f=0;f<NF;f++) Cw[c].val[f]^=ys[T]->val[f];
      for(int S=0;S<V;S++){ touch(xs[S],L2[S]); for(int T=0;T<V;T++) if(nb[S][T]){ touch(&Aw[S][T],L2[S]); if(Jm[S][T]) for(int f=0;f<NF;f++) xs[S]->val[f]^=Aw[S][T].val[f]; } }
      for(int S=0;S<V;S++) touch(xs[S],L3); for(int c=0;c<NC;c++) touch(&Cw[c],L3);
      for(int S=0;S<V;S++) for(int c=0;c<NC;c++) if(Rm[S][c]) for(int f=0;f<NF;f++) xs[S]->val[f]^=Cw[c].val[f];
      for(int T=0;T<V;T++) touch(ys[T],L1); for(int c=0;c<NC;c++) touch(&Cw[c],L1);
      for(int c=0;c<NC;c++) for(int T=0;T<V;T++) if(Gm[c][T]) for(int f=0;f<NF;f++) Cw[c].val[f]^=ys[T]->val[f];
      for(int T=0;T<V;T++){ touch(ys[T],L5[T]); for(int S=0;S<V;S++) if(nb[S][T]){ touch(&Aw[S][T],L5[T]); for(int f=0;f<NF;f++) Aw[S][T].val[f]^=ys[T]->val[f]; } }
      for(int S=0;S<V;S++) touch(xs[S],L3); for(int c=0;c<NC;c++) touch(&Cw[c],L3);
      for(int S=0;S<V;S++) for(int c=0;c<NC;c++) if(Rm[S][c]) for(int f=0;f<NF;f++) xs[S]->val[f]^=Cw[c].val[f];
      for(int S=0;S<V;S++){ touch(xs[S],L3); for(int T=0;T<V;T++) if(nb[S][T]){ touch(&Aw[S][T],L3); if(Jm[S][T]) for(int f=0;f<NF;f++) xs[S]->val[f]^=Aw[S][T].val[f]; } }
    }
    /* auxiliary sinks: label FULL, must equal w^{Q(y)} * own initial value */
    for(int i=0;i<V;i++) for(int j=0;j<V;j++) if(nb[i][j]){ touch(&Aw[i][j],FULL); for(int f=0;f<NF;f++) if(Aw[i][j].val[f]!=MW[QY[f]][Aw[i][j].init[f]]) auxfail++; label_release(Aw[i][j].cur); }
    for(int c=0;c<NC;c++){ touch(&Cw[c],FULL); for(int f=0;f<NF;f++) if(Cw[c].val[f]!=MW[QY[f]][Cw[c].init[f]]) auxfail++; label_release(Cw[c].cur); }
    label_release(L1); label_release(L3); for(int t=0;t<V;t++){ label_release(L0[t]); label_release(L2[t]); label_release(L5[t]); }
    if(invoc%75==0){ printf("  stage %d invocation %ld/675 distinct edges %ld steps %lld labels alive %ld\n",st+1,invoc,nedges_distinct,steps,nlabels_alive); fflush(stdout); }
  }
  /* bank sinks */
  long xfail=0,yfail=0; memset(cache,0,sizeof cache);
  for(int d1=0;d1<V;d1++)for(int d2=0;d2<V;d2++)for(int d3=0;d3<V;d3++){
    int d=(d1*V+d2)*V+d3;
    touch(&X[d],FULL);
    for(int f=0;f<NF;f++) if(X[d].val[f]!=MW[QY[f]][Yb[d].init[f]]) xfail++;
    label_release(X[d].cur);
    /* Y_d sink label U_d^perp */
    signed char qq[36]; for(int i=0;i<H;i++)for(int j=0;j<H;j++) qq[i*H+j]=(signed char)(tv[d2][i]*tv[d3][j]);
    vec u=kron3(one,1,tv[d1],qq,H*H);
    label *Ud=label_new(&u,1,0);
    vec *pp=malloc(sizeof(vec)*(M-1)); memcpy(pp,Ud->perp,sizeof(vec)*(M-1));
    label *Up=label_new(pp,M-1,0); free(pp); label_release(Ud);
    touch(&Yb[d],Up); label_release(Up);
    if(bad!=2){ steps+=1; for(int f=0;f<NF;f++){ int c=vdot(&u,&Y[f]); Yb[d].val[f]=MW[(3-(c*c)%3)%3][Yb[d].val[f]]; } }
    for(int f=0;f<NF;f++) if(Yb[d].val[f]!=MW[QY[f]][X[d].init[f]]) yfail++;
    label_release(Yb[d].cur);
  }
  long long Wl=nwires; long long N0=(long long)V*V*V, I0=3LL*V*V;
  long long pred = Wl*M - N0 + 2*I0*NC*H;
  printf("wires W=%lld  labels made=%ld (max alive %ld)  distinct edges=%ld\n",Wl,nlabels,maxalive,nedges_distinct);
  printf("FAIL counts: nondegenerate-label %ld, nesting %ld, residual-dim %ld, degenerate-residual %ld, phase-crosscheck %lld/%lld\n",
         fail_nondeg,fail_nest,fail_res,fail_degres,xchk_fail,xchk);
  printf("sink checks (x NF=%d freqs): aux role failures %ld, X_d failures %ld, Y_d failures %ld\n",NF,auxfail,xfail,yfail);
  printf("steps = %lld   predicted Wm - N0 + 2 I0 c h = %lld   match=%s   total decrease = %lld (pred I0 c h = %lld)\n",
         steps,pred,steps==pred?"YES":"NO",decr,I0*NC*H);
  printf("Delta' = Wm - steps = %lld   (= v^2 (v - 6ch) = %lld)\n", Wl*M-steps, (long long)V*V*(V-6LL*NC*H));
  return 0;
}
