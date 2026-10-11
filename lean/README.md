# Lean 4 kernel checks for X1

Lean v4.34.1 with Mathlib (`lakefile.toml`, `lake-manifest.json`). Every theorem is `decide +kernel` or a short proof.
There is no `sorry`, no `native_decide` and no added axiom; `axioms_audit.sh` prints the axioms of every theorem and
fails on anything beyond `propext`, `Classical.choice` and `Quot.sound`.

```sh
lake exe cache get        # once: the Mathlib build cache
./build_watch.sh build    # every module, one at a time, nice -n 19, one thread, optional RSS abort (set LIMIT_MB=3072 on an 8 GB machine) of RSS
./axioms_audit.sh         # the axioms of every theorem in MobiusLean/Axioms.lean
```

| Module | What it checks |
|---|---|
| `Basic` | Rigorous rational bounds on `Real.log`, from Mathlib's series bound |
| `Defs`, `Numeric` | Theorem 1: the parameters at h = 92, W* = 3⁵⁵, the sign of Δ′, the ε′ bounds, θ′ < 1 and the 1 − θ′ enclosure |
| `Lucas`, `Brute` | Lemma 1.2 for every h; RG + JV = I on bitmasks at h = 6, 7; counts by enumeration at h = 8–10 |
| `Word` | The F₁₆ word for S ⊗ S |
| `DefsPrepass`, `Prepass` | Theorems 1′ and 2: Δ = 2v²(v − 3ch) for the 4-subset and E1 families, the sign thresholds (43 and 20), W* = 3⁴⁶ and 3⁴⁵, the ε bounds, θ′ < 1, θ′ > 0, and the 1 − θ′ enclosures |
| `LucasE1` | Lemma 10.1: the E1 centre C(n,3) mod 2 for 7-subsets of any finite type |
| `Controls`, `ControlsLight`, `ControlsPrepass` | Refuted controls: each perturbed statement is proved false |
| `Axioms` | `#print axioms` for every theorem above |

Not in Lean: the network lemmas of `proofs/PROOF.md` §§2–6 and §10's cell structure, the recurrence of Thm 2.6′ and the
transfer steps T2–T6. These are checked by written proof and by the scripts in `certificates/`.
