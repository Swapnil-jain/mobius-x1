#!/usr/bin/env python3
"""X1 real-array test: one recursion level (f >= 2 columns) of the flipped network on actual arrays.

What is executed (Prop 2.4' of PROOF.md, nothing replaced by a scalar stand-in):
  * every wire is a real array of F_4 values indexed by (F_3^m)^f  (f columns of m trits);
  * every gate is the real scalar map (pointwise XOR combinations, coefficients in F_2);
  * every edge U -> V is: check nesting, compute the residual V cap U^perp by F_3 linear algebra,
    find an orthogonal basis z_j (norms n_j = +-1), and for each z_j run ONE directional step:
       address change x -> M x in every column (M e_1 = z_j),
       C'^{(+-n_j)} on the f selected trits (one per column)  = the inner C'^{tensor f} call,
       inverse address change;
    Frob(C') is executed as the monomial form D P23 C' D, so only the forward C' is ever applied;
  * at the Y_d sinks one correction step K_{u_d}^{-1};
  * every role (banks AND auxiliaries, all with random initial values) is compared with the exact
    transform C'^{tensor mf} of its routed input, computed independently by Yates.

The genuine network (4-subsets of [h], m = h^3) is infeasible on real arrays: the smallest case with a
non-trivial bank (h = 5) has m = 125, so one column alone is 3^125 entries.  We therefore run the same
construction with per-factor label spaces D_1 (x) D_2 (x) D_3 of small dimension (see PROOF.md, Remark on
generalised families).  Config A puts the genuine 4-subset family of [6] with the genuine Lucas centre in
factor 1; config B puts neighbour and non-neighbour families with B != 0 in factor 2.

Dependency: numpy (the only non-stdlib dependency of the certificates; tested with numpy 2.0.2 under macOS /usr/bin/python3).
Run it WITHOUT -I if numpy lives in user site-packages.  Every other x1 script is stdlib-only.

Usage: python3 x1_real_arrays.py A|B [f] [bad]
  bad=1: drop the Y_d correction kernel (Y_d roles must fail);
  bad=2: row-5 label uses another entry's t-perp (nesting must fail);
  bad=3: (config A) Lucas centre of size <= 1 (scalar network wrong, banks must fail);
  bad=4: the two-sided monomial pre-pass in place of the correction kernel (PROOF.md Prop 2.4', Lemma 6.1):
         X_d is fed M2^{-1} x and Y_d is read through M1^{-1}; every role must pass, with s' - N0 steps;
  bad=5: refuted control for bad=4: the output monomial M1^{-1} only, no input monomial (Y_d roles must fail).
"""
import sys, itertools, random, time, resource
import numpy as np

# F_4 = {0, 1, w = 2, w^2 = 3}; addition is XOR.
MUL = np.array([[0, 0, 0, 0], [0, 1, 2, 3], [0, 2, 3, 1], [0, 3, 1, 2]], dtype=np.uint8)
W, W2 = 2, 3
CP = [[1, W2, W2], [W2, 1, W2], [W2, W2, 1]]          # C' = w I + w^2 J  (diag w + w^2 = 1)
FROB = [[1, W, W], [W, 1, W], [W, W, 1]]               # Frob(C') = C'^2 = C'^{-1}


def mat_mul4(A, B):
    return [[int(np.bitwise_xor.reduce([MUL[A[i][k]][B[k][j]] for k in range(3)])) for j in range(3)] for i in range(3)]


def self_checks():
    I = [[1 if i == j else 0 for j in range(3)] for i in range(3)]
    C2 = mat_mul4(CP, CP)
    assert C2 == FROB, "C'^2 != Frob(C')"
    assert mat_mul4(C2, CP) == I, "C'^3 != I"
    # omega^{n s^2} = 1 + omega^{2n}(omega^s + omega^{-s})  (gives K_{z,n} = I + w^{2n}(R_z + R_{-z}))
    wp = [1, W, W2]
    for n in (1, 2):
        for s in range(3):
            lhs = wp[(n * s * s) % 3]
            rhs = 1 ^ MUL[wp[(2 * n) % 3]][wp[s] ^ wp[(-s) % 3]]
            assert lhs == rhs
    # Frob(C') = D P23 C' D with D = diag(1, w^2, w^2)
    D = [[1, 0, 0], [0, W2, 0], [0, 0, W2]]
    P = [[1, 0, 0], [0, 0, 1], [0, 1, 0]]
    assert mat_mul4(D, mat_mul4(P, mat_mul4(CP, D))) == FROB
    return D, P


DM, PM = self_checks()


def apply3_axis(g, A, ax, nax):
    """apply 3x3 matrix A over F_4 along axis ax of an array of shape (3,)*nax (returns new array)."""
    pre = 3 ** ax
    post = 3 ** (nax - ax - 1)
    v = g.reshape(pre, 3, post)
    s = [v[:, 0, :], v[:, 1, :], v[:, 2, :]]
    out = np.empty_like(v)
    for i in range(3):
        acc = np.zeros_like(s[0])
        for j in range(3):
            if A[i][j]:
                acc ^= s[j] if A[i][j] == 1 else MUL[A[i][j]][s[j]]
        out[:, i, :] = acc
    return out.reshape(g.shape)


# ---------------- F_3 linear algebra (tiny dims)

def rref3(rows, n):
    A = [list(r) for r in rows]
    piv = []
    r = 0
    for c in range(n):
        p = next((i for i in range(r, len(A)) if A[i][c] % 3), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        inv = A[r][c] % 3  # 1 or 2, self-inverse
        A[r] = [(x * inv) % 3 for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] % 3:
                f = A[i][c]
                A[i] = [(A[i][k] - f * A[r][k]) % 3 for k in range(n)]
        piv.append(c)
        r += 1
    return A[:r], piv


def dot3(a, b):
    return sum(x * y for x, y in zip(a, b)) % 3


def perp(basis, n):
    B, piv = rref3(basis, n)
    free = [c for c in range(n) if c not in piv]
    out = []
    for f in free:
        x = [0] * n
        x[f] = 1
        for i, p in enumerate(piv):
            x[p] = (-B[i][f]) % 3
        out.append(x)
    return out


class Label:
    def __init__(self, span, n):
        self.n = n
        self.basis, _ = rref3(span, n)
        self.d = len(self.basis)
        self.key = tuple(tuple(r) for r in self.basis)
        self.perp = perp(self.basis, n) if self.d else [[1 if i == j else 0 for i in range(n)] for j in range(n)]
        g = [[dot3(a, b) for b in self.basis] for a in self.basis]
        self.nondeg = (len(rref3(g, self.d)[0]) == self.d) if self.d else True


def orth_basis(vecs):
    """orthogonal basis with norms in {1,2} of a nondegenerate span; None if degenerate."""
    R = [list(v) for v in vecs]
    out = []
    while R:
        i = next((a for a in range(len(R)) if dot3(R[a], R[a])), None)
        if i is None:
            pr = next(((a, b) for a in range(len(R)) for b in range(a + 1, len(R)) if dot3(R[a], R[b])), None)
            if pr is None:
                return None
            a, b = pr
            R[a] = [(x + y) % 3 for x, y in zip(R[a], R[b])]
            i = a
        z = R.pop(i)
        nz = dot3(z, z)
        for q in range(len(R)):
            g = dot3(R[q], z)
            if g:
                c = (g * nz) % 3  # nz^{-1} = nz
                R[q] = [(x - c * y) % 3 for x, y in zip(R[q], z)]
        out.append((z, nz))
    return out


def residual(sm, bg):
    """bg cap sm^perp, as a list of vectors (requires sm subset bg)."""
    # x = sum c_i b_i in bg with x . s_k = 0 for all s_k in sm
    if sm.d == 0:
        return [list(b) for b in bg.basis]
    G = [[dot3(s, b) for b in bg.basis] for s in sm.basis]
    sol = perp(G, bg.d) if G else [[1 if i == j else 0 for i in range(bg.d)] for j in range(bg.d)]
    out = []
    for c in sol:
        x = [0] * bg.n
        for ci, b in zip(c, bg.basis):
            if ci:
                x = [(xx + ci * bb) % 3 for xx, bb in zip(x, b)]
        out.append(x)
    return out


# ---------------- configuration

def kron(*vs):
    out = [1]
    for v in vs:
        out = [a * b % 3 for a in out for b in v]
    return out


def unit(n, i):
    return [1 if j == i else 0 for j in range(n)]


def config(name, bad):
    if name == 'A':
        hs = (6, 1, 1)
        fam1 = []
        for S in itertools.combinations(range(6), 4):
            fam1.append([1 if i in S else 0 for i in range(6)])
        fam23 = [[1], [2]]
        fams = [fam1, fam23, fam23]
        lucas = [True, False, False]
    else:
        hs = (2, 2, 1)
        f2 = [[1, 0], [0, 1], [2, 0]]
        fams = [f2, f2, [[1], [2]]]
        lucas = [False, False, False]
    gadgets = []
    rng = random.Random(7)
    for j in range(3):
        fam = fams[j]
        v = len(fam)
        nb = [[i != k and dot3(fam[i], fam[k]) == 0 for k in range(v)] for i in range(v)]
        if lucas[j]:
            h = hs[j]
            supp = [set(i for i in range(h) if t[i]) for t in fam]
            cen = [()] + [(a,) for a in range(h)]
            if bad != 3:
                cen += list(itertools.combinations(range(h), 2))
            G = [[1 if set(P) <= supp[T] else 0 for T in range(v)] for P in cen]
            R = [[G[p][S] for p in range(len(cen))] for S in range(v)]
        else:
            # generic valid centre: G = I, R = I + N with N random on neighbour pairs
            G = [[1 if p == T else 0 for T in range(v)] for p in range(v)]
            R = [[(1 if S == p else 0) ^ (rng.randrange(2) if nb[S][p] else 0) for p in range(v)] for S in range(v)]
        c = len(G)
        RG = [[sum(R[S][p] & G[p][T] for p in range(c)) % 2 for T in range(v)] for S in range(v)]
        J = [[RG[S][T] if nb[S][T] else 0 for T in range(v)] for S in range(v)]
        ok = all(((RG[S][T] ^ J[S][T]) == (1 if S == T else 0)) for S in range(v) for T in range(v))
        if bad != 3:
            assert ok, "gadget identity RG + JV = I fails"
        gadgets.append(dict(v=v, nb=nb, G=G, R=R, J=J, c=c, ok=ok))
    return hs, fams, gadgets


# ---------------- arrays

class Ctx:
    pass


def make_perm(z, m):
    """index map for (Pi g)(x) = g(M x) with M e_1 = z, and its inverse."""
    cols = [list(z)]
    for i in range(m):
        cand = cols + [unit(m, i)]
        if len(rref3(cand, m)[0]) == len(cand):
            cols = cand
        if len(cols) == m:
            break
    assert len(cols) == m
    # M has columns cols: M x = sum_i x_i cols[i]
    N3 = 3 ** m
    idx = np.empty(N3, dtype=np.int64)
    for xi in range(N3):
        x = [(xi // 3 ** (m - 1 - i)) % 3 for i in range(m)]
        y = [sum(x[i] * cols[i][r] for i in range(m)) % 3 for r in range(m)]
        idx[xi] = sum(y[r] * 3 ** (m - 1 - r) for r in range(m))
    inv = np.argsort(idx)
    return idx, inv


def _dot(a, b):
    return sum(p * q for p, q in zip(a, b)) % 3


def _reflection(v):
    inv = 1 if _dot(v, v) == 1 else 2
    return lambda x: [(a - 2 * _dot(x, v) * inv * b) % 3 for a, b in zip(x, v)]


def orth_to_e1(u):
    """Lemma 6.1: an orthogonal map A of F_3^m with A u = e_1 (at most two reflections)."""
    m = len(u)
    e1 = [1] + [0] * (m - 1)
    if list(u) == e1:
        return lambda x: list(x)
    a = [(p - q) % 3 for p, q in zip(u, e1)]
    if _dot(a, a):
        return _reflection(a)
    b = [(p + q) % 3 for p, q in zip(u, e1)]
    r1, r2 = _reflection(b), _reflection(e1)
    return lambda x: r2(r1(x))


DINV = [[1, 0, 0], [0, W, 0], [0, 0, W]]               # D^{-1} = diag(1, w, w)


def prepass_maps(ctx, u):
    """index maps of P_A and P_A^{-1}, (P_A g)(x) = g(A^{-1} x), for A u = e_1 (A orthogonal)."""
    m = ctx.m
    A = orth_to_e1(u)
    assert A(u) == [1] + [0] * (m - 1)
    N3 = 3 ** m
    img = np.empty(N3, dtype=np.int64)            # img[x] = index of A x
    for xi in range(N3):
        x = [(xi // 3 ** (m - 1 - i)) % 3 for i in range(m)]
        y = A(x)
        img[xi] = sum(y[r] * 3 ** (m - 1 - r) for r in range(m))
    return np.argsort(img), img                   # P_A takes g at A^{-1} x; P_A^{-1} takes g at A x


def _per_column(ctx, g, idx):
    a = g.reshape((3 ** ctx.m,) * ctx.f)
    for c in range(ctx.f):
        a = np.take(a, idx, axis=c)
    return a


def _first_trits(ctx, a, mats):
    b = a.reshape((3,) * (ctx.m * ctx.f))
    for c in range(ctx.f):
        for Mt in mats:
            b = apply3_axis(b, Mt, c * ctx.m, ctx.m * ctx.f)
    return b


def apply_M2inv(ctx, g, u):
    """M2 = (D (x) I) P_A, so M2^{-1} = P_A^{-1} (D^{-1} (x) I): one F_4 scalar per entry and a free relabeling."""
    pA, pAinv = prepass_maps(ctx, u)
    b = _first_trits(ctx, g, [DINV])
    return _per_column(ctx, b.reshape(-1), pAinv).reshape(-1)


def apply_M1inv(ctx, g, u):
    """M1 = P_A^{-1} (D P23 (x) I), so M1^{-1} = (P23 D^{-1} (x) I) P_A: relabel by P_A FIRST, then the
    first-trit monomial (applying the monomial first is wrong for every u other than +-e_1)."""
    pA, pAinv = prepass_maps(ctx, u)
    a = _per_column(ctx, g, pA)
    return _first_trits(ctx, a, [DINV, PM]).reshape(-1)


def directional_step(ctx, g, z, n):
    """apply K_{z,n} in every column: address change, C'^{(n)} on the f selected trits, inverse change."""
    key = tuple(z)
    if key not in ctx.perm:
        ctx.perm[key] = make_perm(z, ctx.m)
    idx, inv = ctx.perm[key]
    f, m = ctx.f, ctx.m
    a = g.reshape((3 ** m,) * f)
    for c in range(f):
        a = np.take(a, idx, axis=c)
    b = a.reshape((3,) * (m * f))
    axes = [c * m for c in range(f)]
    if n == 1:
        for ax in axes:
            b = apply3_axis(b, CP, ax, m * f)
    else:  # Frob(C') = D P23 C' D, forward C' plus monomials
        for ax in axes:
            b = apply3_axis(b, DM, ax, m * f)
            b = apply3_axis(b, CP, ax, m * f)
            b = apply3_axis(b, PM, ax, m * f)
            b = apply3_axis(b, DM, ax, m * f)
    a = b.reshape((3 ** m,) * f)
    for c in range(f):
        a = np.take(a, inv, axis=c)
    ctx.steps += 1
    return a.reshape(-1)


def yates(ctx, g):
    b = g.reshape((3,) * (ctx.m * ctx.f))
    for ax in range(ctx.m * ctx.f):
        b = apply3_axis(b, CP, ax, ctx.m * ctx.f)
    return b.reshape(-1)


class Wire:
    __slots__ = ('val', 'init', 'lab')


def touch(ctx, w, L):
    cur = w.lab
    if cur.key == L.key:
        return
    if not L.nondeg:
        ctx.fail['nondeg'] += 1
    if cur.d <= L.d:
        sm, bg, inc = cur, L, True
    else:
        sm, bg, inc = L, cur, False
    nested = all(dot3(s, p) == 0 for s in sm.basis for p in bg.perp) if sm.d and bg.d < bg.n else True
    if not nested:
        ctx.fail['nest'] += 1
        w.lab = L
        return
    res = residual(sm, bg)
    if len(res) != bg.d - sm.d:
        ctx.fail['resdim'] += 1
    ob = orth_basis(res)
    if ob is None:
        ctx.fail['degres'] += 1
        w.lab = L
        return
    for z, nz in ob:
        n = nz if inc else (3 - nz) % 3
        w.val = directional_step(ctx, w.val, z, n)
    if not inc:
        ctx.decr += len(ob)
    w.lab = L


def main():
    name = sys.argv[1] if len(sys.argv) > 1 else 'A'
    f = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    bad = int(sys.argv[3]) if len(sys.argv) > 3 else 0
    t0 = time.time()
    hs, fams, gad = config(name, bad)
    m = hs[0] * hs[1] * hs[2]
    ctx = Ctx()
    ctx.m, ctx.f, ctx.steps, ctx.decr, ctx.perm = m, f, 0, 0, {}
    ctx.fail = dict(nondeg=0, nest=0, resdim=0, degres=0)
    NA = 3 ** (m * f)
    rng = np.random.default_rng(12345 + 17 * bad)
    vs = [g['v'] for g in gad]
    print(f"config {name}: factor dims {hs}, m={m}, f={f}, array length 3^{m*f}={NA}, family sizes {vs}, "
          f"centres {[g['c'] for g in gad]}, bad={bad}")
    ZERO = Label([], m)
    FULL = Label([unit(m, i) for i in range(m)], m)
    banks = list(itertools.product(*[range(v) for v in vs]))
    X, Y = {}, {}
    for d in banks:
        for B in (X, Y):
            w = Wire()
            w.val = rng.integers(0, 4, NA, dtype=np.uint8)
            w.init = w.val.copy()
            w.lab = ZERO
            B[d] = w
        u = kron(*[fams[j][d[j]] for j in range(3)])
        X[d].lab = Label([u], m)
        if bad == 4:   # two-sided pre-pass: the network reads M2^{-1} x in role X_d
            X[d].val = apply_M2inv(ctx, X[d].init, u)
    nwires = 2 * len(banks)
    aux_fail = 0
    sum_ch = 0
    for st in range(3):
        g = gad[st]
        v, nb, Gm, Rm, Jm, c = g['v'], g['nb'], g['G'], g['R'], g['J'], g['c']
        others = [j for j in range(3) if j != st]
        hE = 1
        for j in range(st):
            hE *= hs[j]
        hD = hs[st]
        hF = m // (hE * hD)
        for fixed in itertools.product(*[range(vs[j]) for j in others]):
            def bank(t):
                d = [0, 0, 0]
                d[st] = t
                for j, val in zip(others, fixed):
                    d[j] = val
                return tuple(d)
            dd = {j: val for j, val in zip(others, fixed)}
            P = kron(*[fams[j][dd[j]] for j in range(st)]) if st > 0 else [1]
            Q = kron(*[fams[j][dd[j]] for j in range(st + 1, 3)]) if st < 2 else [1]
            Bv = perp([P], hE)  # B = P^perp in E (empty when E is one-dimensional)
            Dv = [unit(hD, i) for i in range(hD)]
            Ev = [unit(hE, i) for i in range(hE)]
            BD = [kron(b, dv, Q) for b in Bv for dv in Dv]
            L1 = Label(BD, m)
            L3 = Label([kron(e, dv, Q) for e in Ev for dv in Dv], m)
            fam = fams[st]
            L0, L2, L5 = [], [], []
            for t in range(v):
                L0.append(Label([kron(b, fam[t], Q) for b in Bv], m))
                L2.append(Label(BD + [kron(P, fam[t], Q)], m))
                tt = (t + 1) % v if bad == 2 else t
                tp = perp([fam[tt]], hD)
                L5.append(Label(BD + [kron(P, x, Q) for x in tp], m))
            # auxiliaries with random initial values
            A = {}
            for S in range(v):
                for T in range(v):
                    if nb[S][T]:
                        w = Wire(); w.val = rng.integers(0, 4, NA, dtype=np.uint8); w.init = w.val.copy(); w.lab = ZERO
                        A[(S, T)] = w
            Cw = []
            for _ in range(c):
                w = Wire(); w.val = rng.integers(0, 4, NA, dtype=np.uint8); w.init = w.val.copy(); w.lab = ZERO
                Cw.append(w)
            nwires += len(A) + c
            sum_ch += c * hD
            xs = [X[bank(t)] for t in range(v)]
            ys = [Y[bank(t)] for t in range(v)]
            if st != 1:  # forward X -> Y: target y = Y, source x = X; side A[(S,T)], S = Y entry, T = X entry
                tg, src = ys, xs
            else:        # stage 2: inverse forward Y -> X; physical touch order is the same
                tg, src = xs, ys
            # The physical touch sequence (rows 0..7) is: Y-side, Y-centre, X-side, X-centre, Y-centre, Y-side,
            # X-centre, X-side, in every stage.  Stage 1/3 gates: y ^= JA, y ^= Rc, A ^= Vx, c ^= Gx, y ^= Rc,
            # y ^= JA, c ^= Gx, A ^= Vx.  Stage 2 runs the reversed rows with source Y and target X:
            # A ^= Vy, c ^= Gy, x ^= JA, x ^= Rc, c ^= Gy, A ^= Vy, x ^= Rc, x ^= JA.
            Yw, Xw = ys, xs
            def side_gate_Y(lab_of, op):
                # Y-entry gate: Y_S with side wires A[(S,T)] (stages 1/3: y ^= JA) or A ^= V y (stage 2)
                for S in range(v):
                    touch(ctx, Yw[S], lab_of(S))
                    for T in range(v):
                        if nb[S][T]:
                            touch(ctx, A[(S, T)], lab_of(S))
                            if op == 'yJA' and Jm[S][T]:
                                Yw[S].val ^= A[(S, T)].val
                            if op == 'AVy':
                                A[(S, T)].val ^= Yw[S].val
            def side_gate_X(lab_of, op):
                for T in range(v):
                    touch(ctx, Xw[T], lab_of(T))
                    for S in range(v):
                        if nb[S][T]:
                            touch(ctx, A[(S, T)], lab_of(T))
                            if op == 'AVx':
                                A[(S, T)].val ^= Xw[T].val
                            if op == 'xJA' and Jm[T][S]:
                                Xw[T].val ^= A[(S, T)].val
            def centre_gate(wires, lab, op):
                for w in wires:
                    touch(ctx, w, lab)
                for w in Cw:
                    touch(ctx, w, lab)
                if op == 'Rc':   # target ^= R c
                    for S in range(v):
                        for p in range(c):
                            if Rm[S][p]:
                                wires[S].val ^= Cw[p].val
                else:            # c ^= G source
                    for p in range(c):
                        for T in range(v):
                            if Gm[p][T]:
                                Cw[p].val ^= wires[T].val
            # In stage 2 the side wire A[(S,T)] joins X entry T... we index side wires by (Y entry, X entry)
            # in every stage, so J is applied as J[target][source].
            if st != 1:
                side_gate_Y(lambda S: L0[S], 'yJA')
                centre_gate(Yw, L1, 'Rc')
                side_gate_X(lambda T: L2[T], 'AVx')
                centre_gate(Xw, L3, 'Gc')
                centre_gate(Yw, L1, 'Rc')
                side_gate_Y(lambda S: L5[S], 'yJA')
                centre_gate(Xw, L3, 'Gc')
                side_gate_X(lambda T: L3, 'AVx')
            else:
                side_gate_Y(lambda S: L0[S], 'AVy')
                centre_gate(Yw, L1, 'Gc')
                side_gate_X(lambda T: L2[T], 'xJA')
                centre_gate(Xw, L3, 'Rc')
                centre_gate(Yw, L1, 'Gc')
                side_gate_Y(lambda S: L5[S], 'AVy')
                centre_gate(Xw, L3, 'Rc')
                side_gate_X(lambda T: L3, 'xJA')
            # auxiliary sinks: label FULL; must equal C'^{(x)mf} of own initial value
            for w in list(A.values()) + Cw:
                touch(ctx, w, FULL)
                if not np.array_equal(w.val, yates(ctx, w.init)):
                    aux_fail += 1
    # bank sinks
    xfail = yfail = 0
    for d in banks:
        touch(ctx, X[d], FULL)
        if not np.array_equal(X[d].val, yates(ctx, Y[d].init)):
            xfail += 1
        u = kron(*[fams[j][d[j]] for j in range(3)])
        touch(ctx, Y[d], Label(perp([u], m), m))
        if bad in (4, 5):
            Y[d].val = apply_M1inv(ctx, Y[d].val, u)            # output monomial of the pre-pass
        elif bad != 1:
            Y[d].val = directional_step(ctx, Y[d].val, u, 2)   # correction K_u^{-1}
        if not np.array_equal(Y[d].val, yates(ctx, X[d].init)):
            yfail += 1
    N0 = len(banks)
    pred = nwires * m - N0 + 2 * sum_ch
    if bad in (1, 4, 5):
        pred -= N0
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 20
    print(f"wires W={nwires} banks N0={N0} directional steps={ctx.steps} predicted Wm-mu*N0+2*sum(c*h_j)={pred} (mu={2 if bad in (1, 4, 5) else 1}) "
          f"match={'YES' if ctx.steps == pred else 'NO'} decrease={ctx.decr} (pred sum c*h_j={sum_ch})")
    print(f"failures: nondeg {ctx.fail['nondeg']} nesting {ctx.fail['nest']} residual-dim {ctx.fail['resdim']} "
          f"degenerate-residual {ctx.fail['degres']}")
    print(f"role checks vs exact C'^(x){m*f} (Yates): aux {aux_fail} fail / {nwires - 2 * N0}, "
          f"X_d {xfail} fail / {N0}, Y_d {yfail} fail / {N0}")
    print(f"time {time.time() - t0:.1f}s  maxRSS {rss:.0f} MB")


if __name__ == '__main__':
    main()
