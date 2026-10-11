#!/usr/bin/env python3
"""X1 exponent check: exact step count of the flipped network at h = 79..92 (and h = 6..10 for validation).

What this is, honestly: a RE-DERIVATION of the count from the cell tables of PROOF.md Lemma 5.1 / 2.3'.
The label sequences below are transcribed from that lemma, so this script cannot catch an error in the
lemma's label table at large h. Its independent parts are: v, d_nbr and c by enumeration; the walk itself
(nesting is checked, residuals are summed edge by edge rather than via the closed form); and the comparison,
at h = 6..10, with the brute-force F_3 linear algebra of x1_e2e_rep.c, read from the logs run_rep_h*_bad0.txt.
The labels are defined uniformly in h (same isometry types of cells at every h), which is why agreement at
h = 6..10 is evidence for h = 79..92; it is not a proof of it.

The count is an edge-by-edge sum, not the closed form:
  * v (number of 4-subsets), d_nbr (ordered neighbours of one 4-subset) and c (centre size) are counted by
    enumerating the actual 4-subsets / centre subsets;
  * every wire of a representative invocation is walked through its label sequence; each label is the
    orthogonal sum of "cells"  X (x) Y (x) Z  with X in {B, P} (E = B _|_ P), Y in a refinement of D
    (<t> _|_ t-perp, or <t_X> _|_ <t_Y> _|_ <t_X,t_Y>-perp on side wires) and Z in {Q, Q-perp};
    nesting is cell inclusion, the residual is the cell difference and its dimension the sum of cell
    dimensions (PROOF.md Lemma 2.3', the orthogonal-cell decomposition);
  * invocations are weighted by v^2 per stage and bank paths by N0 (isometry orbits, PROOF.md Remark 2.3'.4).
The per-stage numbers are compared at h = 6..10 with the brute-force F_3 linear algebra of x1_e2e_rep.c.
Brute force at h >= 79 is impossible: m = h^3 >= 493039, and a single label basis has ~ m^2/4 trits.

Usage: /usr/bin/python3 x1_exponent_count.py
"""
import os
import re
import sys
from itertools import combinations
from decimal import Decimal, getcontext
from math import comb, log10, log

getcontext().prec = 60


def enumerate_counts(h):
    """v, d_nbr of T0 = {0,1,2,3}, c, by enumeration (no binomial formulas)."""
    T0 = {0, 1, 2, 3}
    v = 0
    dn = 0
    for S in combinations(range(h), 4):
        v += 1
        n = len(T0.intersection(S))
        if n != 4 and n % 3 == 0:  # orthogonal over F_3, distinct
            dn += 1
    c = sum(1 for r in range(3) for _ in combinations(range(h), r))
    return v, dn, c


def stage_steps(h, j, nside, c, v):
    """exact residual-dimension sum over one stage-j invocation (j = 1, 2, 3), by cell bookkeeping."""
    e = h ** (j - 1)          # dim E
    q = h ** (3 - j)          # dim of the future space
    dimE = {'B': e - 1, 'P': 1}
    dimZ = {'Q': 1, 'Qp': q - 1}

    def lab(cells, dimD):
        return {(x, y, z): dimE[x] * dimD[y] * dimZ[z] for (x, y, z) in cells}

    def walk(seq, dimD):
        steps = dec = 0
        cur = seq[0]
        for nxt in seq[1:]:
            a, b = set(cur), set(nxt)
            if a == b:
                continue
            if a <= b:
                steps += sum(dimE[x] * dimD[y] * dimZ[z] for (x, y, z) in b - a)
            elif b <= a:
                r = sum(dimE[x] * dimD[y] * dimZ[z] for (x, y, z) in a - b)
                steps += r
                dec += r
            else:
                raise AssertionError('labels not nested')
            cur = nxt
        return steps, dec

    # entry wires: D = <t> _|_ t-perp
    dE = {'t': 1, 'tp': h - 1}
    allD = ['t', 'tp']
    L0 = {('B', 't', 'Q')}
    L1 = {('B', y, 'Q') for y in allD}
    L2 = L1 | {('P', 't', 'Q')}
    L3 = {(x, y, 'Q') for x in 'BP' for y in allD}
    L5 = L1 | {('P', 'tp', 'Q')}
    FULL = {(x, y, z) for x in 'BP' for y in allD for z in ('Q', 'Qp')}
    ZERO = set()
    sx, dx = walk([L2, L3, L3, L3], dE)
    sy, dy = walk([L0, L1, L1, L5], dE)
    sc, dc = walk([ZERO, L1, L3, L1, L3, FULL], dE)
    # side wires: D = <tX> _|_ <tY> _|_ N, tX _|_ tY
    dS = {'X': 1, 'Y': 1, 'N': h - 2}
    sD = ['X', 'Y', 'N']
    S0 = {('B', 'Y', 'Q')}
    S2 = {('B', y, 'Q') for y in sD} | {('P', 'X', 'Q')}
    S5 = {('B', y, 'Q') for y in sD} | {('P', 'X', 'Q'), ('P', 'N', 'Q')}   # t_Y-perp = <t_X> + N
    S3 = {(x, y, 'Q') for x in 'BP' for y in sD}
    SF = {(x, y, z) for x in 'BP' for y in sD for z in ('Q', 'Qp')}
    ss, ds = walk([ZERO, S0, S2, S5, S3, SF], dS)
    total = v * (sx + sy) + nside * ss + c * sc
    dec = v * (dx + dy) + nside * ds + c * dc
    return total, dec


def bank_outside(h):
    """d* path edges outside invocations: source, stage boundaries, sinks (+1 correction counted by caller)."""
    m = h ** 3
    out = 0
    for j in (1, 2, 3):
        e = h ** (j - 1)
        # X enters stage j with label E (x) <t> (x) Q and first touches L2 = B(x)D + P(x)<t>: residual B (x) t-perp
        out += (e - 1) * (h - 1)
        # Y enters with B (x) <t> (x) Q = L0: residual 0
    out += 0   # X last label stage 3 = E (x) D = full space: residual 0
    out += 0   # Y last label stage 3 = (P(x)<t>)^perp = U_d^perp: residual 0
    return out


def count(h):
    v, dn, c = enumerate_counts(h)
    m = h ** 3
    nside = v * dn
    per = [stage_steps(h, j, nside, c, v) for j in (1, 2, 3)]
    N0 = v ** 3
    I0v = v * v
    W = 2 * N0 + 3 * I0v * (nside + c)
    steps = I0v * sum(p[0] for p in per) + N0 * (bank_outside(h) + 1)
    dec = I0v * sum(p[1] for p in per)
    return dict(h=h, v=v, dn=dn, c=c, m=m, W=W, steps=steps, dec=dec, per=[p[0] for p in per])


def main():
    print("validation against brute force (x1_e2e_rep.c logs: per-stage invocation steps, d* path, total):")
    here = os.path.dirname(os.path.abspath(__file__))
    ok_all = True
    for h in (6, 7, 8, 9, 10):
        r = count(h)
        I0 = 3 * r['v'] ** 2
        closed = r['W'] * r['m'] - r['v'] ** 3 + 2 * I0 * r['c'] * h
        logtxt = open(os.path.join(here, f'run_rep_h{h}_bad0.txt')).read()
        brute = [int(x) for x in re.findall(r'stage \d representative invocation: \d+ labels, steps (\d+)', logtxt)]
        bx = int(re.search(r'edges outside invocations X (\d+), Y (\d+)', logtxt).group(1))
        btot = int(re.search(r'orbit-weighted exact steps = (\d+)', logtxt).group(1))
        ok = (r['per'] == brute and bank_outside(h) == bx and r['steps'] == btot == closed)
        ok_all &= ok
        print(f"  h={h}: per-stage {r['per']} brute {brute}; d* outside X {bank_outside(h)} brute {bx}; "
              f"total {r['steps']} brute {btot} closed {closed}  match={ok}")
    if not ok_all:
        sys.exit("FAIL: cell bookkeeping disagrees with brute force")
    print()
    print(" h |        v | d_nbr |    c |  exact steps == closed form | Delta' = Wm - steps (exact) | sign | "
          "W*=3^w | eps' = Delta'/(W* m) | 1-theta'")
    best = None
    for h in range(79, 93):
        r = count(h)
        m, W, v, c = r['m'], r['W'], r['v'], r['c']
        I0 = 3 * v * v
        closed = W * m - v ** 3 + 2 * I0 * c * h
        delta = W * m - r['steps']
        assert r['dn'] == comb(h - 4, 4) + 4 * (h - 4)
        w = 0
        while 3 ** w < W:
            w += 1
        eps = Decimal(delta) / (Decimal(3) ** w * m)
        lam_over_m = 1 - eps
        one_minus_theta = -(lam_over_m.ln()) / Decimal(m).ln()
        print(f"{h:3d} | {v:8d} | {r['dn']:5d} | {c:4d} | {str(r['steps'] == closed):>27} | {delta:27d} | "
              f"{'+' if delta > 0 else '-':>4} | 3^{w:2d} | {float(eps):.4e} | {float(one_minus_theta):.4e}")
        assert delta == v * v * (v - 6 * c * h)
        if delta > 0 and (best is None or one_minus_theta > best[1]):
            best = (h, one_minus_theta, eps, w)
    r78 = count(78)
    print(f"h=78: Delta' = {r78['W'] * r78['m'] - r78['steps']} (negative: the saving starts at h = 79)")
    h, omt, eps, w = best
    print(f"\nbest h = {h}: W* = 3^{w}, eps' = {float(eps):.6e}, 1 - theta' = {float(omt):.6e}")
    # crossover: the pipeline beats Yates once (1-eps')^d < 1/c0, d = number of recursion levels, log10 k ~ d log10 m
    m = h ** 3
    print("crossover log10 k ~ log10(m) * ln(c0) / eps'  for an overhead ratio c0:")
    for c0 in (2, 84, 420, 1e4, 1e6):
        d = log(c0) / float(eps)
        print(f"  c0 = {c0:>8}: levels d = {d:.3e}, log10 k ~ {d * log10(m):.3e}")


if __name__ == '__main__':
    main()
