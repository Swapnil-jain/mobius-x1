#!/usr/bin/env python3
"""Check of the E1 gadget (PROOF.md §10, Theorem 2): 7-subsets of [h] as F_3 labels, centre = all 3-subsets.

What is checked, by enumeration (no binomial formulas are trusted):
  * the Lucas table: (RG)_{ST} = #{P subset S cap T : |P| = 3} = C(n,3), n = |S cap T|, is odd exactly at n in {3, 7}
    (so 1 on the diagonal, 0 on the non-neighbours n in {1, 2, 4, 5}, and 0 on the neighbours n in {0, 6});
  * hence J = RG on neighbours is supported on the pairs with |S cap T| = 3 only, and the number of such ordered
    pairs per entry is 35 C(h-7, 4); v = C(h,7) and c = C(h,3);
  * one forward invocation over F_4, with random values on every wire and side wires ONLY on the J-supported pairs,
    run through the eight rows of PROOF.md §1: it must give y -> y + x and restore every auxiliary, at h = 11, 12.
Refuted controls (each must fail):
  * a centre of 2-subsets at h = 12: C(n,2) is odd at the non-neighbour size n = 2, so y -> y + x fails.
    (At h = 11 two 7-sets always meet in at least 3 points, n = 2 never occurs and this control would pass:
    it must be run at h >= 12.);
  * the 3-subset centre with J dropped (no side wires): RG is odd on the |S cap T| = 3 neighbours, so it fails.

Usage: python3 x1_e1_check.py      (stdlib only; about 1 minute, under 200 MB)
"""
import itertools
import random
import sys
from math import comb

EXP = [1, 2, 3]
LOG = {1: 0, 2: 1, 3: 2}


def lucas_table():
    ok = True
    for n in range(8):
        odd = comb(n, 3) % 2 == 1
        ok &= odd == (n in (3, 7))
    return ok


def invocation(h, centre_sizes, use_J=True, trials=2, seed=1):
    rnd = random.Random(seed)
    T = [frozenset(s) for s in itertools.combinations(range(h), 7)]
    C = [frozenset(p) for s in centre_sizes for p in itertools.combinations(range(h), s)]
    v = len(T)
    sub = [[j for j, P in enumerate(C) if P <= S] for S in T]          # R row S, and G column S
    Cset = set(C)
    rg = lambda a, b: sum(1 for k in centre_sizes for P in itertools.combinations(sorted(T[a] & T[b]), k)
                          if frozenset(P) in Cset) & 1
    # J = RG on neighbours (|S cap T| = 0 mod 3); side wires only where J is nonzero
    pairs = [(a, b) for a in range(v) for b in range(v)
             if a != b and len(T[a] & T[b]) % 3 == 0 and rg(a, b)] if use_J else []
    per_entry = sum(1 for (a, b) in pairs if a == 0)
    sizes = {len(T[a] & T[b]) for a, b in pairs}
    fails = 0
    for _ in range(trials):
        x = [rnd.randrange(4) for _ in range(v)]
        y = [rnd.randrange(4) for _ in range(v)]
        A = {p: rnd.randrange(4) for p in pairs}
        c = [rnd.randrange(4) for _ in C]
        y0, A0, c0 = y[:], dict(A), c[:]

        def JA():                                   # y_S += A_{ST}   (J = 1 on its support)
            for (S, U) in pairs:
                y[S] ^= A[(S, U)]

        def Rc():
            for S in range(v):
                for j in sub[S]:
                    y[S] ^= c[j]

        def Vx():
            for (S, U) in pairs:
                A[(S, U)] ^= x[U]

        def Gx():
            for U in range(v):
                for j in sub[U]:
                    c[j] ^= x[U]
        for row in (JA, Rc, Vx, Gx, Rc, JA, Gx, Vx):  # rows 0..7 of the forward invocation
            row()
        fails += sum(y[i] != (y0[i] ^ x[i]) for i in range(v)) + (A != A0) + (c != c0)
    return v, len(C), per_entry, sizes, fails


def main():
    ok = lucas_table()
    print(f"Lucas table: C(n,3) odd exactly at n in {{3,7}} for n = 0..7: {ok}")
    for h in (11, 12):
        v, c, pe, sizes, fails = invocation(h, (3,))
        good = (v == comb(h, 7) and c == comb(h, 3) and pe == 35 * comb(h - 7, 4) and sizes == {3} and fails == 0)
        ok &= good
        print(f"h={h}: v={v} c={c} J-supported side wires per entry={pe} (35 C(h-7,4) = {35 * comb(h - 7, 4)}), "
              f"|S cap T| on side wires {sorted(sizes)}, failures={fails}  {'OK' if good else 'FAIL'}")
    v, c, pe, sizes, fails = invocation(12, (2,))   # h >= 12, so that |S cap T| = 2 occurs
    ok &= fails > 0
    print(f"control h=12, centre = 2-subsets: failures={fails}  {'refuted as expected' if fails else 'FAIL: control passed'}")
    v, c, pe, sizes, fails = invocation(11, (3,), use_J=False)
    ok &= fails > 0
    print(f"control h=11, 3-subset centre without J: failures={fails}  "
          f"{'refuted as expected' if fails else 'FAIL: control passed'}")
    if not ok:
        sys.exit("FAIL")
    print("PASS: E1 invocation correct at h = 11, 12; both controls refuted")


if __name__ == '__main__':
    main()
