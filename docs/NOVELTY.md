# X1 novelty check: is o(N log N) known for the GF(2) Möbius/zeta transform? (2026-10-11)

Question: is there a known GF(2)-linear (XOR, fan-in 2, cancellation allowed) circuit for M_k = S^{⊗k},
S = [[1,0],[1,1]], N = 2^k, with o(N log N) gates? Yates' algorithm uses (1/2) N log2 N.
Tags: [verified] means I read the passage in the source during this run; [secondhand] means it comes from earlier
notes, a search snippet, or a citing paper.

**Headline being checked (2026-10-11).** L_{F₂}(M_k) = O(N (log N)^{θ′}) in three proved versions: Theorem 1,
1 − θ′ = 1.83·10⁻¹⁵ (refereed twice by AI agents); Theorem 1′ with the two-sided pre-pass, 4.22·10⁻¹³; Theorem 2 with
the E1 gadget and the pre-pass, 4.37·10⁻¹¹ (each refereed once by an AI agent). A faster batching recurrence is only a conjecture
(PROOF.md §11). The novelty question below is the same for all three: any
o(N log N) bound for M_k with cancellation.

## 1. Verdict

**Not known. Confidence about 90%.**
- No source I could reach claims fewer than (1/2) N log2 N XORs for M_k, asymptotically or at any fixed k > 3.
- The most recent specialist statement (Sergeev, 2024 slides) lists "is L(D_n) < n·2^{n−1}?" as open.
  This asks for any improvement at all, not even o(N log N).
- The openai/math repository has no Möbius, zeta, Sierpinski, Yates or Reed–Muller content.
  Its DFT preprint explicitly excludes finite fields.
- Remaining risk:
  - Russian-language papers I could not get (Zykov 1993, Chashkin 1994, the Sergeev 2025 and 2026 bodies);
  - a preprint posted in the last few days;
  - an unindexed note applying the openai/math method in characteristic 2.

## 2. Is beating Yates stated as open for circuits with cancellation?

Yes, in several places.
- **Sergeev, 2024 slides** (`igorssergeev.github.io/papers/lowerlin2024eng.pdf`) [verified, rendered images].
  - Slide 17, "Open problems": **"4. Is it true that L(D_n) < n2^{n−1} as n → ∞?"**
  - Slide 15: **"Hypothesis: L(D_n) = ω(2^n)"**, and the best lower bound **"L(D_n) ≥ (3 − o(1))2^n"**.
  - D_n is the disjointness matrix over GF(2), which equals M_n up to a row reversal. L is the fan-in-2 XOR count
    with cancellation.
- **Boyar–Find, arXiv 1305.3041, §7** [verified, pdftotext]:
  > "If a cancellation-free or an OR circuit computes the Sierpinski matrix correctly, it has size at least ½ n log n.
  > For this particular family of matrices, it is not obvious to what extent cancellation can help. It would be very
  > interesting to determine this, since it would automatically provide a converse to Theorem 4."
  - Also from 1305.3041 [verified]: "we hope that our proof can be strengthened to give an ω(n) lower bound for XOR
    circuits for the Sierpinski matrix".
  - Also [verified]: they "experimentally verified that even for circuits where cancellation is allowed, the matrices
    S2, S4, S8 do not admit circuits smaller than the lower bound".
- **Jukna–Sergeev survey (FnT-TCS 9(1), 2013)** [verified, pdftotext of the author PDF].
  - §4.3 gives OR(D) ∼ ½ n log n and SUM(D) ≥ ½ n log n (Boyar–Find; Selezneva).
  - It gives no XOR(D) bound with cancellation other than the Yates upper bound.
  - Problem 7.11: "Do matrices A with XOR(A)/OR(A) → ∞ exist? Intersection matrix Ðn could be again a natural
    candidate to try." This is about the complement of D, so it bears on our question only indirectly.
  - There is no explicit sentence saying "Yates is open for XOR circuits" for D itself.
- **Sergeev, arXiv 2212.01776** [verified, grep]: "the question about existence of substantially more efficient
  XOR-coverings for matrices D_N is still open". This is about depth 2.

## 3. Has anyone claimed o(N log N), or any improvement, for M_k over GF(2)?

**No.**
- **Literature.** No result below n·2^{n−1}.
  - The Möbius-hardware paper (ePrint 2023/948) takes "around n·2^(n−1) bit xors" as the cost [secondhand, snippet].
  - BHKK, "Fast zeta transforms for lattices with few irreducibles" (SODA 2012) [verified]: "the circuit given by
    Yates's algorithm for the subset lattice is thus optimal". That rests on Kennes' Ω(e) bound, which holds in
    Kennes' path-factorisation (cancellation-free) model, so it does not cover XOR circuits with cancellation.
- **openai/math** (checked by `gh api` GET, HEAD fd4aeeb of 2026-10-08) [verified].
  - The repository has 3 commits, 1 PR and 0 issues, and discussions are disabled.
  - Issue and PR search for Moebius, Mobius, Möbius, zeta, Sierpinski, Yates, Reed-Muller and "characteristic 2"
    returns 0 hits.
  - Code search for Yates, Reed-Muller and zeta-transform returns 0 hits. The Sierpinski hits are only an Ashkin–Teller
    physics paper. The Mobius and Walsh hits are unrelated Lean files, plus the DFT preprint's own references.
  - Problem 130 (CONTENTS.md) states its model as "exact complex arithmetic, unrestricted coefficients and a supplied
    root of unity".
  - The explicit-DFT preprint, introduction [verified, TeX]: the result "is not a result about integer bit
    complexity, bounded-coefficient circuits, numerical stability, **finite fields**, or formal power-series
    algorithms". That sentence is about its convolution corollary, but it reflects the paper's scope.
  - Its only mention of characteristic two is network.tex:340, a remark that alternating forms occur in
    characteristic 2 (about labels, not about the field of the data).
  - "Finite tensor savings and exact Fourier circuits" [verified, pdftotext]:
    - It is complex-only.
    - Its generation step uses "In characteristic zero" (Zariski-open image in GL_q(C)).
    - It cites Alman–Rao for the WHT but claims nothing for it.
  - **Nobody in the repository claims the characteristic-2 consequence, or says it fails to transfer.**
- **Third-party follow-ups** (READMEs read via WebFetch) [verified README; contents not checked].
  - jacobalansussman/wht-power-saving-lean (2026-10-09) claims the **complex** Walsh–Hadamard transform in
    O(n (log n)^{1−7.47e-4}) in OpenAI's RAM model. It does not mention GF(2), Möbius or zeta.
  - shea256/fourier-transform-below-nlogn: complex DFT only.
  - Earlier sweeps of other public GitHub repositories on this method [secondhand, our earlier notes]: nothing for M_k.
- **arXiv API**, newest first, on "disjointness matrix", "Kronecker power" ∧ circuit, "Walsh-Hadamard" ∧
  "linear circuit", "XOR circuits", "Mobius transform" ∧ XOR, "zeta transform" ∧ circuit [verified listing]:
  - every hit is depth-2 or rigidity work (2603.15565, 2509.14489, 2607.27014) or unrelated;
  - there is no arXiv version of either OpenAI DFT preprint;
  - ECCC 2025–26 was swept earlier [secondhand]: nothing.

## 4. Closest known results and how they differ

| Result | Model | Relation to X1 |
|---|---|---|
| Boyar–Find 1207.5321 / 1305.3041; Kennes 1992; Selezneva 2013 | cancellation-free / OR / separated variables | (1/2) N log N is tight. X1 must use cancellation (it does: F4/F16 data with 2-torsion). [verified BF; secondhand Kennes, Selezneva] |
| Sergeev 2025, Math. Notes 118 | XOR with cancellation, lower bound | (3 − o(1))N. Linear, so no conflict. [verified on slide; body not read] |
| Alman 2102.11992 (STOC'21) | unbounded fan-in, wire count, any field | Depth-d N^{1+O(1/d)}; unbounded depth only constant factors, for H_n (1.81 N log N wires). Verbatim [verified]: "it would be much more exciting to design a circuit of size o(N log N) for Hn, but that is currently beyond our techniques". |
| Alman–Guan–Padaki 2211.05217 (SODA'23); Alman–Li 2509.14489; Ye 2603.15565 | depth 2 | Depth-2 exponents for disjointness (best 1.2448). Nothing below N log N at unbounded depth. [verified AGP intro; others secondhand] |
| Alman–Rao 2211.06459 (STOC'23) | fan-in-2 arithmetic count, char ≠ 2 | (23/24) N log N for the WHT. Verbatim [verified]: "We focus on F whose characteristic is not 2, since the problem is trivial in such fields"; "it remains an open question to prove that an algorithm using o(N log N) operations is impossible". |
| Alman 2211.04643 | bit operations with lookup tables (not a linear circuit) | O(2^n·n/log n) bit operations for exactly this transform (multilinear evaluation over F2). Not a gate count. [secondhand, our earlier literature notes] |
| openai/math #130 (both preprints) | complex linear circuits / RAM, unrestricted coefficients | o(n log n) for the complex DFT. X1 is the char-2 transplant. The source excludes finite fields and its existence proof uses char 0. [verified] |
| WHT analogue | complex | Before 2026-09: o(N log N) open (Alman, Alman–Rao). The GF(2) case is not covered: the source's generation step is characteristic 0. |

## 5. References

1. J. Boyar, M. G. Find, "Cancellation-free circuits in unbounded and bounded depth", arXiv 1305.3041 (FCT 2013;
   TCS 2015). https://arxiv.org/abs/1305.3041
2. J. Boyar, M. G. Find, "Cancellation-free circuits: an approach for proving superlinear lower bounds for linear
   Boolean operators", arXiv 1207.5321. https://arxiv.org/abs/1207.5321
3. S. Jukna, I. Sergeev, "Complexity of linear Boolean operators", FnT-TCS 9(1), 2013, DOI 10.1561/0400000063.
   https://web.vu.lt/mif/s.jukna/Knizka/linear.pdf
4. I. S. Sergeev, slides "Lower bounds for linear circuits" (2024).
   https://igorssergeev.github.io/papers/lowerlin2024eng.pdf
   Paper: Math. Notes 118 (2025) 848–862, DOI 10.1134/S0001434625605143.
5. I. S. Sergeev, "Notes on the complexity of coverings for Kronecker powers of symmetric matrices", arXiv 2212.01776.
6. I. S. Sergeev, CC2026 lecture slides. https://igorssergeev.github.io/papers/CC2026eng.pdf
   Slide 17 lists only the general open problem "L(A_n) = ω(n) over GF(2)".
7. J. Alman, "Kronecker products, low-depth circuits, and matrix rigidity", arXiv 2102.11992 (STOC 2021).
8. J. Alman, Y. Guan, A. Padaki, "Smaller low-depth circuits for Kronecker powers", arXiv 2211.05217 (SODA 2023).
9. J. Alman, K. Rao, "Faster Walsh–Hadamard and discrete Fourier transforms from matrix non-rigidity",
   arXiv 2211.06459 (STOC 2023).
10. J. Alman, B. Li, arXiv 2509.14489. Ye, arXiv 2603.15565.
11. A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto, J. Nederlof, P. Parviainen, "Fast zeta transforms for lattices
    with few irreducibles", SODA 2012. https://thorehusfeldt.com/wp-content/uploads/2010/08/7c52e3293a74298f.pdf
12. R. Kennes, IEEE Trans. SMC 22(2) (1992); Kennes–Smets, arXiv 1304.1122.
13. openai/math, problem 130:
    - "An explicit power saving for the exact discrete Fourier transform" and "Finite tensor savings and exact Fourier
      circuits" (2026-09-25);
    - repository https://github.com/openai/math at fd4aeeb.
14. jacobalansussman/wht-power-saving-lean; shea256/fourier-transform-below-nlogn (GitHub READMEs).
15. Find, Göös, Järvisalo, Kaski, Koivisto, Korhonen, "Separating OR, SUM, and XOR circuits", arXiv 1304.0513
    [secondhand, our earlier literature notes].
16. ePrint 2023/948, "Compact circuits for efficient Möbius transform" (TCHES) [secondhand, snippet].

## 6. Not accessed

- Bodies of Sergeev 2025 (Math. Notes) and Sergeev 2026 (Diskr. Mat. 38(1)): paywall, and mathnet is blocked.
- Zykov 1993; Chashkin 1994; Find's PhD thesis (SDU 2015).
- The Selezneva papers: only the earlier abstracts.
- Gashkov–Sergeev Russian work on the complexity of the Zhegalkin transform: no full texts. I found no claim of a
  sub-Yates bound in any abstract or snippet.
- Kennes 1992 (IEEE): only the BHKK citation and the UAI precursor were seen.
- GitHub code search was rate-limited after about 10 queries, so the "characteristic Walsh", "subset sum transform"
  and "disjointness" searches in openai/math did not run. Issue and PR searches all completed (0 hits).
- I did not run a Google Scholar "cited by" sweep after 2026-10-10. Semantic Scholar citers were checked earlier
  [secondhand].
