# m6_word_search.py -- search for an explicit positive word
#   C' D_1 C' D_2 ... D_{L-1} C'   (D_i diagonal over F_16, normalised d_1 = 1)
# whose product has exactly 4 nonzero entries (=> monomial x elementary transvection x monomial).
# Permutations commute with C' (C' = wI + w^2 J), so they never help inside the word.
# F_16 = F_2[x]/(x^4+x+1), w = x^5.
import itertools, sys

MOD, DEG = 0b10011, 4
def mul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> DEG: a ^= MOD
    return r
MUL = [[mul(a, b) for b in range(16)] for a in range(16)]
INV = [0] + [next(b for b in range(1, 16) if MUL[a][b] == 1) for a in range(1, 16)]
def pw(a, e):
    r = 1
    for _ in range(e): r = MUL[r][a]
    return r
w = pw(2, 5); w2 = MUL[w][w]
assert w ^ w2 ^ 1 == 0
Cp = ((1, w2, w2), (w2, 1, w2), (w2, w2, 1))

def mm(A, B):
    return tuple(tuple(MUL[A[i][0]][B[0][j]] ^ MUL[A[i][1]][B[1][j]] ^ MUL[A[i][2]][B[2][j]] for j in range(3)) for i in range(3))
def diag(d):
    return tuple(tuple(d[i] if i == j else 0 for j in range(3)) for i in range(3))
def nnz(A):
    return sum(1 for r in A for x in r if x)

DIAGS = [(1, a, b) for a in range(1, 16) for b in range(1, 16)]

def search(L, maxhits=5):
    hits = []
    hist = {}
    for ds in itertools.product(DIAGS, repeat=L - 1):
        P = Cp
        for d in ds:
            P = mm(mm(P, diag(d)), Cp)
        z = nnz(P)
        hist[z] = hist.get(z, 0) + 1
        if z == 4 and len(hits) < maxhits:
            hits.append((ds, P))
    return hist, hits

if __name__ == "__main__" and len(sys.argv) == 1:
    for L in (2, 3):
        hist, hits = search(L)
        print("L=%d (number of C' factors): nnz histogram %s" % (L, dict(sorted(hist.items()))))
        for ds, P in hits:
            print("  hit: D's =", ds, " product =", P)

# ---- L >= 4: random sampling (no numpy on this Mac). Fraction of GL_3(16) with nnz = 4 is
#      36*15^4 / |GL_3(16)| ~ 2.8e-5, so ~3.6e4 samples per hit if words equidistribute.
def sample(L, n, seed=1):
    import random
    rnd = random.Random(seed)
    hist = {}; hits = []
    for _ in range(n):
        ds = [rnd.choice(DIAGS) for _ in range(L - 1)]
        P = Cp
        for d in ds:
            P = mm(mm(P, diag(d)), Cp)
        z = nnz(P)
        hist[z] = hist.get(z, 0) + 1
        if z <= 5: hits.append((tuple(ds), P))
    return hist, hits

if __name__ == "__main__" and len(sys.argv) > 2:
    L, n = int(sys.argv[1]), int(sys.argv[2])
    hist, hits = sample(L, n)
    print("L=%d sampled %d: nnz histogram %s" % (L, n, dict(sorted(hist.items()))))
    for h in hits[:10]: print("  hit:", h)
