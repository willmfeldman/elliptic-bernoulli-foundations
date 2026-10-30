module

-- challenge-prep: split vocabulary (aux-proof reuse: a merged file fails the fingerprint diff)
-- One module per library file. Concatenating them lets later definitions reuse earlier auxiliary
-- `_proof_k` constants that the library mints per module, so the values would no longer match
-- (`scripts/fingerprint-challenges.sh`).
public import Vocabulary.Setting
public import Vocabulary.Sobolev
public import Vocabulary.Variational
public import Vocabulary.TwoPhase

@[expose] public section

/-!
# Challenge: classification of global two-phase minimizers

Trusted statement surface for the classification of global minimizers of the two-phase problem
(after Alt–Caffarelli–Friedman (1984)). Let `u : ℝᵈ → ℝ` be Lipschitz and a local minimizer
(`IsLocalEnergyMinimizer univ (fun _ ↦ 1) u`) of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` on `ℝᵈ`: for some
weak gradient, `u ∈ H¹_loc(ℝᵈ)`, and on every ball `B`, `J(u; B) ≤ J(v; B)` for every
`v ∈ H¹_loc(ℝᵈ)` with `v = u` a.e. off `B`. Only the positive phase is penalized, and `u` may
change sign. If `u` takes a positive and a negative value, then there are a unit vector `e`,
`c ∈ ℝ` and `a, b > 0` with `a² - b² = 1` such that
`u(x) = a (x·e + c)⁺ - b (x·e + c)⁻` for every `x`. The statement covers every dimension `d`.

Alt–Caffarelli–Friedman work with continuous functions; here `u` is Lipschitz. The proof combines
the Alt–Caffarelli–Friedman monotonicity formula, the Friedland–Hayman inequality (Friedland–Hayman
(1976)), Weiss monotonicity (Weiss (1999)) and the classification of `1`-homogeneous two-phase
functions (after De Philippis–Spolaor–Velichkov, Lemma 2.2).

The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Defs/Variational.lean`, `Defs/TwoPhase.lean`), with
the library's names, definitions and order. Every file imports Mathlib modules only (the same ones
as the library file it restates). The conclusion is written out without the vocabulary's
`twoPlane`.

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* G. De Philippis, L. Spolaor, B. Velichkov, *Regularity of the free boundary for the two-phase
  Bernoulli problem*, Invent. Math. 225 (2021), 347–394; arXiv:1911.02165.
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.
-/

noncomputable section

open Set
open scoped NNReal

namespace EllipticBernoulli

/-- Challenge: a Lipschitz local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` on `ℝᵈ` that takes a
positive and a negative value is a two-plane function `a (x·e + c)⁺ - b (x·e + c)⁻` with
`‖e‖ = 1`, `a, b > 0` and `a² - b² = 1` (after Alt–Caffarelli–Friedman (1984)). -/
theorem challenge_twoPhaseClassification {d : ℕ} {u : E d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hpos : ∃ x, 0 < u x)
    (hneg : ∃ x, u x < 0) :
    ∃ (e : E d) (c a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = 1 ∧
      ∀ x, u x = a * max (inner ℝ x e + c) 0 - b * max (-(inner ℝ x e + c)) 0 := by
  sorry

end EllipticBernoulli

end
