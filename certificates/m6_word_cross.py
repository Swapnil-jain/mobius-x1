# m6_word_cross.py -- (1) verify a 14-XOR F_2 program for C' on F_4^3 (so 28 XORs on F_16^3 via
# F_16 = F_4 + F_4*beta, C' having F_4 entries); (2) recompute eps' of the flipped gadget; (3) end-to-end crossover k
# at which the X1 pipeline (w = 12 explicit slots, m6_word_verify.py) beats Yates for M_k over F_2.
from decimal import Decimal as Dm, getcontext
from math import comb, log, log10
getcontext().prec = 60

# ---- (1) F_4 = {a + b w}, w^2 = w + 1.  mult by w: (a,b) -> (b, a^b) [1 XOR]; by w^2: (a,b) -> (a^b, a) [1 XOR]
def f4mul(x, y):  # x,y as 2-bit ints (bit0 = a, bit1 = b)
    a, b = x & 1, x >> 1; c, d = y & 1, y >> 1
    # (a+bw)(c+dw) = ac + (ad+bc)w + bd(w+1)
    return ((a & c) ^ (b & d)) | (((a & d) ^ (b & c) ^ (b & d)) << 1)
W, W2 = 2, 3
Cp = [[1, W2, W2], [W2, 1, W2], [W2, W2, 1]]
xors = 0
def prog(x):
    """x: list of 3 (a,b) pairs.  y_i = w x_i + w^2 s,  s = x1+x2+x3.  Counts XORs."""
    global xors; xors = 0
    def X(p, q):
        global xors; xors += 1; return p ^ q
    s = (X(X(x[0][0], x[1][0]), x[2][0]), X(X(x[0][1], x[1][1]), x[2][1]))     # 4
    w2s = (X(s[0], s[1]), s[0])                                                # 1
    out = []
    for (a, b) in x:
        wx = (b, X(a, b))                                                      # 1 each
        out.append((X(wx[0], w2s[0]), X(wx[1], w2s[1])))                       # 2 each
    return out
ok = True
for v in range(64):
    xs = [(v >> (2 * i)) & 3 for i in range(3)]
    want = [0, 0, 0]
    for i in range(3):
        for j in range(3): want[i] ^= f4mul(Cp[i][j], xs[j])
    got = prog([(x & 1, x >> 1) for x in xs])
    ok &= [g[0] | (g[1] << 1) for g in got] == want
print("14-XOR program for C' on F_4^3 correct on all 64 inputs:", ok, " XORs =", xors)
cC_F16 = 2 * xors   # XORs per C' application on F_16^3

# ---- (2) eps' of the flipped gadget at h = 92
h = 92
v = comb(h, 4); c = 1 + h + comb(h, 2); m = h ** 3
Dp = v * v * (v - 6 * c * h)
# W* = 3^w with w minimal such that 3^w >= W (wires); W from the closed form of proofs/PROOF.md is not recomputed here:
# use the stated W* = 3^55 and check eps' against the value 2.48e-14 of proofs/PROOF.md Thm 2.6'.
Wst = 3 ** 55
eps = Dm(Dp) / (Dm(Wst) * Dm(m))
print("h=92: v=%d c=%d m=%d Delta'=%d ; eps' = Delta'/(W* m) = %.4e" % (v, c, m, Dp, eps))

# ---- (3) crossover.  Per entry of N = 4^t (k = 2t):
#   Yates: k/2 = t XORs.
#   pipeline: w slots * E_r[ (cC/3) * r * (1-eps')^d ],  r ~ Bin(t, 3/4)  ->  w*(cC/3)*(3t/4)*(1-eps')^d
#   ratio = w*cC/4 * (1-eps')^d ; beats Yates iff d > ln(w*cC/4)/eps'  (d = gadget levels, r ~ K m^d)
#   monomial slots (<= (w+1)*12 XORs per entry) and gadget pointwise work are O(1) per entry: negligible.
w = 12
for label, cc in (("F_4-componentwise descent (28 XORs per C' on F_16^3)", cC_F16),
                  ("28-XOR-per-F_16-gate descent (5 gates per C')", 5 * 28)):
    R = w * cc / 4
    d = log(R) / float(eps)
    K = 56 * m
    lk = d * log10(m) + log10(K * 8 / 3)
    print("%s: ratio const w*cC/4 = %.1f, levels d = %.4e, log10 k = %.4e" % (label, R, d, lk))
