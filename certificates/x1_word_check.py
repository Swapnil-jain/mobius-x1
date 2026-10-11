#!/usr/bin/env python3
"""X1-b: independent check of the explicit transfer word of proofs/WORD.md.

Written from scratch (does not import m6_word_*.py).  F_16 = F_2[x]/(x^4 + x + 1), elements as integers
(bit i = coefficient of x^i); w = x^5 = 6, w^2 = 7, C' = w I + w^2 J_3.

Checks:
  1. C'^3 = I, w has order 3, and C' commutes with every 3x3 permutation matrix.
  2. The three 3x3 transvection words of WORD.md (4 forward C' slots each) evaluate to the stated matrices.
  3. Embedded on the coordinate triples (0,1,2), (0,2,3), (1,2,3) of F_16^4 (identity on the fourth), their
     product is exactly S (x) S, S = [[1,0],[1,1]], coordinates 00,01,10,11 -> 0,1,2,3.
  4. Every slot is either a monomial matrix or a permutation conjugate of C' (+) 1, so S (x) S is a positive
     word with exactly 12 slots (C' (+) 1) and monomials, which is all the transfer (PROOF.md section 5) needs.
  5. Mixed product at t = 2: the product of the slot tensor squares equals S^{(x)4} (16 x 16).
"""
from itertools import permutations


def gmul(a, b):
    r = 0
    while b:
        if b & 1:
            r ^= a
        b >>= 1
        a <<= 1
        if a & 16:
            a ^= 0b10011
    return r


def mm(A, B):
    n, k, p = len(A), len(B), len(B[0])
    out = []
    for i in range(n):
        row = []
        for j in range(p):
            s = 0
            for t in range(k):
                s ^= gmul(A[i][t], B[t][j])
            row.append(s)
        out.append(row)
    return out


def eye(n):
    return [[1 if i == j else 0 for j in range(n)] for i in range(n)]


def diag(d):
    return [[d[i] if i == j else 0 for j in range(len(d))] for i in range(len(d))]


def kron(A, B):
    return [[gmul(A[i // len(B)][j // len(B[0])], B[i % len(B)][j % len(B[0])])
             for j in range(len(A[0]) * len(B[0]))] for i in range(len(A) * len(B))]


def is_monomial(A):
    n = len(A)
    return all(sum(1 for x in row if x) == 1 for row in A) and \
        all(sum(1 for i in range(n) if A[i][j]) == 1 for j in range(n))


W, W2 = 6, 7
assert gmul(W, W) == W2 and gmul(W, W2) == 1, "w is not a primitive cube root of 1"
CP = [[W ^ W2 if i == j else W2 for j in range(3)] for i in range(3)]   # w I + w^2 J
assert CP == [[1, 7, 7], [7, 1, 7], [7, 7, 1]]
assert mm(mm(CP, CP), CP) == eye(3), "C'^3 != I"
for p in permutations(range(3)):
    P = [[1 if p[i] == j else 0 for j in range(3)] for i in range(3)]
    assert mm(P, CP) == mm(CP, P)
print("1. C'^3 = I, w of order 3, C' commutes with all 3x3 permutations: OK")


def word(M0, Ds, M1):
    """M0 . C' D1 C' D2 C' D3 C' . M1"""
    X = M0
    X = mm(X, CP)
    for d in Ds:
        X = mm(X, diag(d))
        X = mm(X, CP)
    return mm(X, M1)


DA = [(1, 2, 7), (1, 5, 6), (1, 5, 5)]
core = word(eye(3), DA, eye(3))
assert core == [[0, 5, 0], [8, 0, 0], [8, 13, 10]], core
T1 = word([[0, 0, 12], [0, 4, 0], [15, 0, 0]], DA[::-1], [[0, 6, 0], [0, 0, 1], [1, 0, 0]])
T2a = word([[0, 15, 0], [2, 0, 0], [0, 0, 15]], DA, diag((1, 12, 10)))
T2b = word([[0, 15, 0], [13, 0, 0], [0, 0, 15]], DA, diag((1, 10, 10)))
assert T1 == [[1, 0, 0], [1, 1, 0], [1, 0, 1]], T1
assert T2a == [[1, 0, 0], [0, 1, 0], [1, 2, 1]], T2a
assert T2b == [[1, 0, 0], [0, 1, 0], [1, 3, 1]], T2b
print("2. the three 4-slot transvection words evaluate as stated: OK")


def embed(A, coords):
    E = eye(4)
    for a, i in enumerate(coords):
        for b, j in enumerate(coords):
            E[i][j] = A[a][b]
    return E


S = [[1, 0], [1, 1]]
SS = kron(S, S)
prod = mm(mm(embed(T1, (0, 1, 2)), embed(T2a, (0, 2, 3))), embed(T2b, (1, 2, 3)))
assert prod == SS, prod
print("3. T1(0,1,2) . T2a(0,2,3) . T2b(1,2,3) = S (x) S exactly over F_16: OK")

# 4. slot list: every factor is monomial or a permutation conjugate of C' (+) 1
slots = []


def slots_of(M0, Ds, M1, coords):
    rest = [i for i in range(4) if i not in coords][0]
    order = list(coords) + [rest]
    Pm = [[1 if order[j] == i else 0 for j in range(4)] for i in range(4)]   # Pm e_j = e_{order[j]}
    Pinv = [list(r) for r in zip(*Pm)]
    C4 = embed(CP, (0, 1, 2))
    out = [('mono', embed(M0, coords))]
    out.append(('C', mm(mm(Pm, C4), Pinv)))
    for d in Ds:
        out.append(('mono', embed(diag(d), coords)))
        out.append(('C', mm(mm(Pm, C4), Pinv)))
    out.append(('mono', embed(M1, coords)))
    return out, Pm, Pinv


allslots = []
for (M0, Ds, M1, co) in [([[0, 0, 12], [0, 4, 0], [15, 0, 0]], DA[::-1], [[0, 6, 0], [0, 0, 1], [1, 0, 0]], (0, 1, 2)),
                         ([[0, 15, 0], [2, 0, 0], [0, 0, 15]], DA, diag((1, 12, 10)), (0, 2, 3)),
                         ([[0, 15, 0], [13, 0, 0], [0, 0, 15]], DA, diag((1, 10, 10)), (1, 2, 3))]:
    sl, Pm, Pinv = slots_of(M0, Ds, M1, co)
    allslots += sl
    # the conjugating permutation is absorbed into the neighbouring monomial slots
    assert mm(mm(Pinv, sl[1][1]), Pm) == embed(CP, (0, 1, 2))
X = eye(4)
for kind, A in allslots:
    assert kind == 'C' or is_monomial(A)
    X = mm(X, A)
assert X == SS
nC = sum(1 for k, _ in allslots if k == 'C')
print(f"4. slot list: {nC} C'-slots (permutation conjugates of C' (+) 1), {len(allslots) - nC} monomial slots; "
      f"product = S (x) S: OK")

# 5. mixed product at t = 2
X2 = eye(16)
for kind, A in allslots:
    X2 = mm(X2, kron(A, A))
assert X2 == kron(SS, SS)
print("5. mixed product at t = 2: prod of slot tensor squares = S^(x)4: OK")
