module

-- challenge-prep: split vocabulary (aux-proof reuse: a merged file fails the fingerprint diff)
-- One module per library file. Concatenating them lets later definitions reuse earlier auxiliary
-- `_proof_k` constants that the library mints per module, so the values would no longer match
-- (`scripts/fingerprint-challenges.sh`).
public import Vocabulary.Setting
public import Vocabulary.Sobolev
public import Vocabulary.Touching
public import Vocabulary.Viscosity
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

@[expose] public section

/-!
# Challenge: the Lipschitz estimate for viscosity supersolutions

Trusted statement surface for the Lipschitz estimate of the one-phase problem (Caffarelli–Salsa,
Lemma 11.19). Viscosity super/subsolutions are those of Abedin–Feldman–Stinson, Definition 2.1
(`IsViscSuper`, `IsViscSub`, `IsViscSolution`): tests are globally smooth functions touching
non-strictly, and at a free boundary point either `Δφ ≤ 0` or `φ = 0` and `|∇φ| ≤ Q`
(supersolution). A viscosity supersolution which is harmonic in `{u > 0}` is Lipschitz,
quantitatively on balls and locally on `U`.

The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Basic/Touching.lean`,
`Defs/Viscosity.lean`), with the library's names, definitions and order. Every file imports Mathlib
modules only (the same ones as the library file it restates).

## References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped NNReal

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: the quantitative Lipschitz estimate (Caffarelli–Salsa Lemma 11.19): for `1 ≤ d`
there is `C` such that a viscosity supersolution in `U ⊇ B_{2r}(x₀)`, harmonic in `{u > 0}`, with
`Q ≤ Qmax` and `u ≤ M` on `B_{2r}(x₀)`, is `C (Qmax + M / r)`-Lipschitz on `B_r(x₀)`. -/
theorem challenge_lipschitzOnWith_of_isViscSuper (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) (r Qmax M : ℝ),
      IsOpen U → 0 < r → ball x₀ (2 * r) ⊆ U → IsViscSuper U Q u →
      HarmonicOnNhd u (posSet u U) → (∀ y ∈ ball x₀ (2 * r), Q y ≤ Qmax) → 0 ≤ Qmax →
      (∀ y ∈ ball x₀ (2 * r), u y ≤ M) →
      LipschitzOnWith (C * (Qmax + M / r)).toNNReal u (ball x₀ r) := by
  sorry

/-- Challenge: local Lipschitz regularity of viscosity supersolutions harmonic in `{u > 0}`, for
continuous `Q`. -/
theorem challenge_locallyLipschitzOn_of_isViscSuper {U : Set (E d)} {Q u : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) (hharm : HarmonicOnNhd u (posSet u U)) (hQ : ContinuousOn Q U) :
    LocallyLipschitzOn U u := by
  sorry

end EllipticBernoulli
