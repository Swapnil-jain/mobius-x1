#!/usr/bin/env python3
"""The three headline exponents of X1, each under the PROVED recursion of PROOF.md Thm 2.6' (one directional step
per kernel, roles padded to W* = 3^w), with exact integers and 60-digit Decimal.

  Theorem 1  : 4-subset labels, Lucas centre |P| <= 2, correction kernel (mu = 1).       1 - theta' = 1.83e-15
  Theorem 1' : the same gadget with the two-sided monomial pre-pass (mu = 2, Prop 2.4').   1 - theta' = 4.22e-13
  Theorem 2  : E1, 7-subset labels, centre |P| = 3, side wires on J-supported pairs only,
               with the pre-pass (mu = 2, PROOF.md §10).                                 1 - theta' = 4.37e-11

For each row the script
  * computes v, c and the side wires per entry, and checks the closed form Delta = mu N0 - 6 v^2 c h
    (= 2 v^2 (v - 3ch) at mu = 2) against the edge-by-edge cell walk of x1_exponent_count.py (Lemma 5.1);
  * finds the sign threshold (Delta > 0 from h_min on, scanned to the end of the range, negative at h_min - 1);
  * scans h, pads to W* = 3^w, and reports the best 1 - theta' = -ln(1 - eps)/ln m, eps = Delta/(W* m);
  * prints the crossover with Yates by PROOF.md §8's formula: log10 k ~ log10(m) * ln(c0) / eps.

`--conjecture` also prints the value under the UNPROVED whole-residual batching recurrence (README, "Open"):
theta solves sum_e (rho_e/m)^theta = W over the residual histogram of one level, no padding. It is not a theorem.

Usage: python3 x1_theorems.py [--conjecture]     (stdlib only, about 20 s)
"""
import os
import sys
from decimal import Decimal, getcontext
from math import comb, log, log10

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))   # run with -I: import the sibling script
import x1_exponent_count as xc  # noqa: E402

getcontext().prec = 60


def family(name, h):
    """v, c, side wires per entry (d), for the label family `name` at h."""
    if name == '4':
        return comb(h, 4), 1 + h + comb(h, 2), comb(h - 4, 4) + 4 * (h - 4)
    # E1: J = C(n,3) mod 2 on neighbours is nonzero only at |S cap T| = 3, so side wires sit only there
    return comb(h, 7), comb(h, 3), 35 * comb(h - 7, 4)


def params(name, h, mu):
    v, c, d = family(name, h)
    m, N0 = h ** 3, v ** 3
    W = 2 * N0 + 3 * v * v * (v * d + c)
    delta = mu * N0 - 6 * v * v * c * h
    w = 0
    while 3 ** w < W:
        w += 1
    return dict(h=h, v=v, c=c, d=d, m=m, N0=N0, W=W, w=w, delta=delta)


def cell_walk_delta(name, h, mu):
    """Wm - s' from the edge-by-edge walk of Lemma 5.1 (x1_exponent_count.stage_steps), banks included."""
    p = params(name, h, mu)
    v, c, m = p['v'], p['c'], p['m']
    nside = v * p['d']
    steps = v * v * sum(xc.stage_steps(h, j, nside, c, v)[0] for j in (1, 2, 3))
    steps += p['N0'] * (xc.bank_outside(h) + (1 if mu == 1 else 0))   # mu = 1: one correction kernel per Y_d
    return p['W'] * m - steps


def exponent(p):
    eps = Decimal(p['delta']) / (Decimal(3) ** p['w'] * p['m'])
    return eps, -(1 - eps).ln() / Decimal(p['m']).ln()


ROWS = [
    ('Theorem 1  (4-sets, mu=1)', '4', 1, range(60, 201)),
    ("Theorem 1' (4-sets, pre-pass, mu=2)", '4', 2, range(30, 201)),
    ('Theorem 2  (E1 7-sets, pre-pass, mu=2)', '7', 2, range(14, 121)),
]
EXPECT = {('4', 1): (79, 92), ('4', 2): (43, 51), ('7', 2): (20, 23)}


def main():
    ok = True
    # spot values from the referee's report, and the closed form at mu = 2
    ok &= params('7', 21, 2)['delta'] == 878597075232000
    ok &= params('4', 49, 2)['delta'] == 2841987244015808
    ok &= params('4', 92, 1)['delta'] == 3373902208276911675
    for name, h in (('4', 49), ('7', 21)):
        p = params(name, h, 2)
        ok &= p['delta'] == 2 * p['v'] ** 2 * (p['v'] - 3 * p['c'] * h)
    print(f"spot values (Delta at E1 h=21, 4-sets h=49 mu=2, 4-sets h=92 mu=1) and 2v^2(v-3ch): {ok}")
    # closed form against the cell walk
    for name, mu, hs in (('4', 1, (6, 7, 8, 79, 92)), ('4', 2, (6, 7, 8, 43, 51)), ('7', 2, (11, 12, 20, 23))):
        good = all(cell_walk_delta(name, h, mu) == params(name, h, mu)['delta'] for h in hs)
        ok &= good
        print(f"family {name}-sets mu={mu}: cell walk == closed form at h in {hs}: {good}")
    print()
    for title, name, mu, hr in ROWS:
        ds = {h: params(name, h, mu) for h in hr}
        pos = [h for h in hr if ds[h]['delta'] > 0]
        hmin = pos[0]
        ok &= pos == list(range(hmin, hr[-1] + 1)) and ds[hmin - 1]['delta'] < 0
        best = max(pos, key=lambda h: exponent(ds[h])[1])
        p = ds[best]
        eps, omt = exponent(p)
        ok &= (hmin, best) == EXPECT[(name, mu)]
        print(f"{title}: Delta > 0 exactly for h >= {hmin} (scanned to {hr[-1]}); best h = {best}, m = {p['m']}, "
              f"v = {p['v']}, c = {p['c']}, d = {p['d']}")
        print(f"    W = {p['W']}, W* = 3^{p['w']}, Delta = {p['delta']}")
        print(f"    eps = {eps:.10e}, 1 - theta' = {omt:.10e}")
        for c0 in (2, 84, 10 ** 6):
            levels = log(c0) / float(eps)
            print(f"    crossover, c0 = {c0:>7}: log10 k ~ {levels * log10(p['m']):.3e}")
    if '--conjecture' in sys.argv:
        print()
        print("OPEN, NOT PROVED: whole-residual batching (one C'^(x)(rho f) call per residual, no padding)")
        best = max((batched('7', h, 2), h) for h in range(20, 41))
        print(f"    E1 + pre-pass: 1 - theta = {best[0]:.4e} at h = {best[1]}  [conjecture only]")
    if not ok:
        sys.exit("FAIL")
    print("\nPASS")


def batched(name, h, mu):
    """theta solving sum_e n_e (rho_e/m)^theta = W (residual histogram of PROOF.md Lemma 2.3'); returns 1 - theta."""
    p = params(name, h, mu)
    v, c, d, m, N0 = p['v'], p['c'], p['d'], p['m'], p['N0']
    I = v * v
    hist = {}

    def add(r, k):
        if r > 0:
            hist[r] = hist.get(r, 0) + k
    for j in (1, 2, 3):
        e = h ** (j - 1)
        for r in ((e - 1) * (h - 1), h - 1):
            add(r, 2 * I * v)                      # X and Y entries
        for r in (e - 1, (e - 1) * (h - 1) + 1, h - 2, 1, m - e * h):
            add(r, I * v * d)                      # side wires
        for r in ((e - 1) * h, h, h, h, m - e * h):
            add(r, I * c)                          # centre wires
    if mu == 1:
        add(1, N0)
    assert p['W'] * m - sum(r * k for r, k in hist.items()) == p['delta']
    terms = [(k, (Decimal(r) / m).ln()) for r, k in hist.items()]
    f = lambda th: sum(k * (th * L).exp() for k, L in terms) - p['W']
    lo, hi = Decimal('0.99'), Decimal(1)
    for _ in range(120):
        mid = (lo + hi) / 2
        if f(mid) > 0:
            lo = mid
        else:
            hi = mid
    return 1 - lo


if __name__ == '__main__':
    main()
