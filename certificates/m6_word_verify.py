# m6_word_verify.py -- build and EXACTLY verify explicit positive words
#   (a) S(+)1  (width 3)  = M0 C' D1 C' D2 C' D3 C' D4 C' M1      (5 C'-slots; L<=4 impossible, m6_word_L4/L5.c)
#   (b) S(x)S  (width 4)  = product of 12 slots (C'(+)1) interleaved with F_16-monomials
# F_16 = F_2[x]/(x^4+x+1) (elements as ints, bit i = coeff of x^i), w = x^5 = x^2+x = 6, w^2 = 7.
# C' = wI + w^2 J_3 = [[1,w2,w2],[w2,1,w2],[w2,w2,1]] (forward form only; no inverses used).
import itertools, random, sys

MOD, DEG = 0b10011, 4
def _mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> DEG: a ^= MOD
    return r
MUL = [[_mul(a, b) for b in range(16)] for a in range(16)]
INV = [0] + [next(b for b in range(1, 16) if MUL[a][b] == 1) for a in range(1, 16)]
w = 1
for _ in range(5): w = MUL[w][2]
w2 = MUL[w][w]
assert (w, w2) == (6, 7) and w ^ w2 ^ 1 == 0

def mm(A, B):
    n, m, p = len(A), len(B), len(B[0])
    return tuple(tuple(_x(MUL[A[i][l]][B[l][j]] for l in range(m)) for j in range(p)) for i in range(n))
def _x(it):
    r = 0
    for v in it: r ^= v
    return r
def eye(n): return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
def diag(d): return tuple(tuple(d[i] if i == j else 0 for j in range(len(d))) for i in range(len(d)))
def perm(p):  # matrix sending e_j -> e_{p[j]}
    n = len(p); return tuple(tuple(int(p[j] == i) for j in range(n)) for i in range(n))
def nnz(A): return sum(1 for r in A for v in r if v)
def tr(A): return tuple(zip(*A))
def is_monomial(A):
    return all(sum(1 for v in r if v) == 1 for r in A) and all(sum(1 for v in c if v) == 1 for c in tr(A))
def mono_inv(A):  # inverse of a monomial matrix
    n = len(A); R = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(n):
            if A[i][j]: R[j][i] = INV[A[i][j]]
    return tuple(map(tuple, R))
def inv3(A):  # generic Gauss-Jordan inverse over F_16
    n = len(A); M = [list(A[i]) + list(eye(n)[i]) for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c]); M[c], M[p] = M[p], M[c]
        iv = INV[M[c][c]]; M[c] = [MUL[iv][v] for v in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]; M[r] = [M[r][j] ^ MUL[f][M[c][j]] for j in range(2 * n)]
    return tuple(tuple(M[i][n:]) for i in range(n))

Cp = ((1, w2, w2), (w2, 1, w2), (w2, w2, 1))
def word(ds):  # C' D1 C' D2 ... C'
    P = Cp
    for d in ds: P = mm(mm(P, diag(d)), Cp)
    return P

def monomial_match(P, T):
    """find monomials M0, M1 with M0 P M1 = T, or None.  Iterate M1 over all 6*15^3 monomials."""
    Ti = inv3(T)
    for p in itertools.permutations(range(3)):
        for d in itertools.product(range(1, 16), repeat=3):
            M1 = mm(perm(p), diag(d))
            Q = mm(mm(P, M1), Ti)          # = M0^{-1}
            if is_monomial(Q): return mono_inv(Q), M1
    return None

def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name)
    if not cond: sys.exit(1)

# ---------- (a) S(+)1 at width 3 with 5 C' slots (hit from m6_word_L5.c) ----------
DS5 = [(1, 1, 2), (1, 1, 14), (1, 4, 11), (1, 14, 3)]
P5 = word(DS5)
S1 = ((1, 0, 0), (1, 1, 0), (0, 0, 1))
mt = monomial_match(P5, S1)
check("L=5 word has nnz 4", nnz(P5) == 4)
M0a, M1a = mt
check("S(+)1 = M0 * C'D1C'D2C'D3C'D4C' * M1", mm(mm(M0a, P5), M1a) == S1)

# ---------- (b) type-A transvection with 4 C' slots ----------
# find one by a seeded random search (fraction ~6e-4 of L=4 words, m6_word_L4.c)
rnd = random.Random(7); DIAGS = [(1, a, b) for a in range(1, 16) for b in range(1, 16)]
while True:
    DS4 = [rnd.choice(DIAGS) for _ in range(3)]
    P4 = word(DS4)
    if nnz(P4) == 5 and any(sum(1 for v in r if v) == 3 for r in P4): break
print("type-A L=4 word D's:", DS4, " product:", P4)

# Width-4 coordinates: 00->0, 01->1, 10->2, 11->3 ; S(x)S[(a,b),(c,d)] = [c<=a][d<=b]
SS = tuple(tuple(int((j >> 1) <= (i >> 1) and (j & 1) <= (i & 1)) for j in range(4)) for i in range(4))
def embed(A3, coords):  # A3 acting on coords (c0,c1,c2) of F^4, identity on the remaining one
    R = [list(r) for r in eye(4)]
    for a in range(3):
        for b in range(3): R[coords[a]][coords[b]] = A3[a][b]
    return tuple(map(tuple, R))
def transv(u, phi):  # I + u phi^T  (4x4)
    return tuple(tuple(int(i == j) ^ MUL[u[i]][phi[j]] for j in range(4)) for i in range(4))

lam = 2                       # any lam not in {0,1}
l1 = 1 ^ lam
e = lambda i: tuple(int(i == j) for j in range(4))
def add(*vs): return tuple(_x(v[j] for v in vs) for j in range(4))
def sc(a, v): return tuple(MUL[a][x] for x in v)
T1 = transv(add(e(1), e(2)), e(0))                       # I + (e01+e10) e00^T          coords {0,1,2}, type B
T2a = transv(e(3), add(e(0), sc(lam, e(2))))              # I + e11 (e00 + lam e10)^T     coords {0,2,3}, type A
T2b = transv(e(3), add(e(1), sc(l1, e(2))))               # I + e11 (e01 + (1+lam)e10)^T  coords {1,2,3}, type A
check("S(x)S = T1 * T2a * T2b", mm(mm(T1, T2a), T2b) == SS)

# each factor: restrict to its 3 coords, match to P4 (type A) or P4^T (type B = reversed word, C' symmetric)
P4B = word(list(reversed(DS4)))
check("reversed word = transpose", P4B == tr(P4))
slots = []   # list of 4x4 matrices whose product is S(x)S; 'C' marks a (C'(+)1) slot
def restrict(T, coords): return tuple(tuple(T[coords[a]][coords[b]] for b in range(3)) for a in range(3))
for T, coords, ds in ((T1, (0, 1, 2), list(reversed(DS4))), (T2a, (0, 2, 3), DS4), (T2b, (1, 2, 3), DS4)):
    T3 = restrict(T, coords)
    check("factor is identity off its 3 coords", embed(T3, coords) == T)
    M0, M1 = monomial_match(word(ds), T3)
    seq = [M0, Cp]
    for d in ds: seq += [diag(d), Cp]
    seq.append(M1)
    for X in seq: slots.append(("C" if X == Cp else "M", embed(X, coords)))

# merge consecutive monomials; C'-slots on coords other than {0,1,2} are conjugates of C'(+)1 by a permutation,
# which is itself a monomial, so the count of (C'(+)1)-slots is the count of 'C' entries.
prod = eye(4)
for _, X in slots: prod = mm(prod, X)
check("product of the explicit 4x4 slot list == S(x)S over F_16 (entries 0/1)", prod == SS)
nC = sum(1 for k, _ in slots if k == "C")
print("number of (C'(+)1) slots w =", nC)

# check (C'(+)1) conjugation claim: a C' slot on coords (c0,c1,c2) = Pi (C'(+)1) Pi^{-1} for a coordinate perm Pi
for coords in ((0, 2, 3), (1, 2, 3)):
    rest = [i for i in range(4) if i not in coords][0]
    p = list(coords) + [rest]                  # e_j -> e_{p[j]}
    Pi = perm(p); Pinv = tr(Pi)
    check("C' on %s is a permutation conjugate of C'(+)1" % (coords,), mm(mm(Pi, embed(Cp, (0, 1, 2))), Pinv) == embed(Cp, coords))

if "-v" in sys.argv:
    print("S(+)1 word: M0 =", M0a, " D's =", DS5, " M1 =", M1a)
    for k, X in slots: print(k, X)
