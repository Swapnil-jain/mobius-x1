#!/usr/bin/env python3
"""Check of the two-sided monomial pre-pass (PROOF.md, Prop 2.4', exceptional route; Lemma 6.1).

Claim. For u in F_3^m with u.u = 1 and U = <u>, the exceptional route ratio R_u = Phi_{U^perp} Phi_U^{-1}
(per column, f columns) equals M1 . C'^{(x)mf} . M2 with M1, M2 monomial:
    A   = an orthogonal map with A u = e_1, built from at most two reflections (Lemma 6.1),
    P_A = the address permutation (P_A g)(x) = g(A^{-1} x), applied in every column,
    D   = diag(1, w^2, w^2), P23 = the swap of addresses 1 and 2, both on the first trit of every column
          (Lemma 3.4: Frob(C') = D P23 C' D),
    M1  = P_A^{-1} (D P23 (x) I),   M2 = (D (x) I) P_A.

What is computed independently. Every frame is built on the Fourier side from its definition:
F diag(w^{q(y)}) F^{-1}, with q(y) = Q(P_{U^perp} y) - Q(P_U y) evaluated from the projections, over F_4, as an
explicit 3^{mf} x 3^{mf} matrix. C'^{(x)mf} is built as a Kronecker power of the 3 x 3 kernel, and is also checked
to equal Phi_A (Lemma 3.3). Every norm-1 vector u is tried, for (m, f) in {(1,1), (2,1), (3,1), (4,1), (1,2), (2,2)};
m = 4 includes non-coordinate vectors such as (1,1,1,1).

Refuted control. With a one-sided adapter (output monomial only), R_u . C'^{-(x)mf} would have to be monomial.
It never is: the script counts how many u admit it and expects 0.

Usage: python3 x1_prepass_check.py     (stdlib only, about 1 minute, under 50 MB)
"""
import itertools
import sys

# F_4 = {0, 1, w = 2, w^2 = 3}; addition is XOR.
EXP = [1, 2, 3]
LOG = {1: 0, 2: 1, 3: 2}


def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[(LOG[a] + LOG[b]) % 3]


def wpow(s):
    return EXP[s % 3]


def mm(A, B):
    n, k = len(A), len(B[0])
    R = [[0] * k for _ in range(n)]
    for i in range(n):
        Ri = R[i]
        for t, a in enumerate(A[i]):
            if a:
                Bt = B[t]
                for j in range(k):
                    if Bt[j]:
                        Ri[j] ^= mul(a, Bt[j])
    return R


def kron(A, B):
    return [[mul(a, b) for a in Ar for b in Br] for Ar in A for Br in B]


def is_monomial(M):
    return all(sum(1 for x in row if x) == 1 for row in M) and \
        all(sum(1 for row in M if row[j]) == 1 for j in range(len(M)))


def dot(a, b):
    return sum(p * q for p, q in zip(a, b)) % 3


def reflection(v):
    """x -> x - 2 (x.v)/(v.v) v, an isometry of F_3^m for v.v != 0."""
    inv = 1 if dot(v, v) == 1 else 2       # (v.v)^{-1} in F_3
    return lambda x: tuple((a - 2 * dot(x, v) * inv * b) % 3 for a, b in zip(x, v))


def orth_to_e1(u):
    """Lemma 6.1: an orthogonal A with A u = e_1, from at most two reflections."""
    m = len(u)
    e1 = tuple([1] + [0] * (m - 1))
    if u == e1:
        return lambda x: x
    a = tuple((p - q) % 3 for p, q in zip(u, e1))
    if dot(a, a) != 0:                      # reflection in u - e1 swaps u and e1
        return reflection(a)
    b = tuple((p + q) % 3 for p, q in zip(u, e1))
    assert dot(b, b) != 0                   # (u-e1).(u-e1) + (u+e1).(u+e1) = 4 = 1
    r1, r2 = reflection(b), reflection(e1)  # u -> -e1 -> e1
    return lambda x: r2(r1(x))


def run(m, f):
    n = m * f
    V = list(itertools.product(range(3), repeat=n))
    N = len(V)
    ix = {x: i for i, x in enumerate(V)}
    F = [[wpow(dot(x, y)) for y in V] for x in V]
    Fi = [[wpow(-dot(x, y)) for y in V] for x in V]
    cols = lambda y: [y[c * m:(c + 1) * m] for c in range(f)]

    def frame(q):
        Dg = [[wpow(q(y)) if i == j else 0 for j in range(N)] for i, y in enumerate(V)]
        return mm(mm(F, Dg), Fi)

    one = [[1 if i == j else 3 for j in range(3)] for i in range(3)]     # C' = w I + w^2 J
    Cp = [[1]]
    for _ in range(n):
        Cp = kron(Cp, one)
    assert frame(lambda y: sum(t * t for t in y)) == Cp, "Phi_A != C'^(x)mf (Lemma 3.3)"
    Cp_inv = mm(Cp, Cp)                                                   # C'^3 = I
    d, p = [1, 3, 3], [0, 2, 1]                                           # D = diag(1,w^2,w^2), P23
    Dm = [[0] * N for _ in range(N)]
    DPm = [[0] * N for _ in range(N)]
    for y in V:
        s, z = 1, list(y)
        for c in range(f):
            s = mul(s, d[y[c * m]])
            z[c * m] = p[y[c * m]]
        Dm[ix[y]][ix[y]] = s
        DPm[ix[y]][ix[tuple(z)]] = s                                      # (D P23)_{y, P23 y}
    ok = one_sided = tot = 0
    for u in itertools.product(range(3), repeat=m):
        if dot(u, u) != 1:
            continue
        tot += 1

        def q(y):
            s = 0
            for c in cols(y):
                pu = [(dot(u, c) * a) % 3 for a in u]                     # P_U c (u.u = 1)
                pp = [(a - b) % 3 for a, b in zip(c, pu)]                 # P_{U^perp} c
                s += dot(pp, pp) - dot(pu, pu)
            return s
        R = frame(q)
        A = orth_to_e1(u)
        for x in itertools.product(range(3), repeat=m):                  # A is an isometry
            for y in itertools.product(range(3), repeat=m):
                assert dot(A(x), A(y)) == dot(x, y)
        assert A(u) == tuple([1] + [0] * (m - 1))
        Afull = lambda y: tuple(sum((A(c) for c in cols(y)), ()))
        PA = [[0] * N for _ in range(N)]                                  # (P_A g)(x) = g(A^{-1} x)
        for y in V:
            PA[ix[Afull(y)]][ix[y]] = 1
        PAi = [list(r) for r in zip(*PA)]
        M1, M2 = mm(PAi, DPm), mm(Dm, PA)
        assert is_monomial(M1) and is_monomial(M2)
        if mm(mm(M1, Cp), M2) == R:
            ok += 1
        if is_monomial(mm(R, Cp_inv)):
            one_sided += 1
    return ok, one_sided, tot


def main():
    all_ok = True
    grand = 0
    for m, f in ((1, 1), (2, 1), (3, 1), (4, 1), (1, 2), (2, 2)):
        ok, one, tot = run(m, f)
        grand += tot
        good = ok == tot and one == 0
        all_ok &= good
        print(f"m={m} f={f}: R_u = M1 C'^(x){m * f} M2 for {ok}/{tot} norm-1 u; "
              f"one-sided control (R_u C'^-1 monomial) {one}/{tot}  {'OK' if good else 'FAIL'}")
    print(f"total norm-1 lines checked: {grand}")
    if not all_ok:
        sys.exit("FAIL")
    print("PASS: two-sided pre-pass holds for every u; one-sided adapters fail for every u")


if __name__ == '__main__':
    main()
