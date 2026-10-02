module

public import EllipticBernoulli.Lipschitz.Estimate

/-!
# Solution: the Lipschitz estimate for viscosity supersolutions

Discharges the challenge through the library modules imported above:
`lipschitzOnWith_of_isViscSuper` and `locallyLipschitzOn_of_isViscSuper`.
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped NNReal

namespace EllipticBernoulli

variable {d : ℕ}

theorem challenge_lipschitzOnWith_of_isViscSuper (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) (r Qmax M : ℝ),
      IsOpen U → 0 < r → ball x₀ (2 * r) ⊆ U → IsViscSuper U Q u →
      HarmonicOnNhd u (posSet u U) → (∀ y ∈ ball x₀ (2 * r), Q y ≤ Qmax) → 0 ≤ Qmax →
      (∀ y ∈ ball x₀ (2 * r), u y ≤ M) →
      LipschitzOnWith (C * (Qmax + M / r)).toNNReal u (ball x₀ r) :=
  lipschitzOnWith_of_isViscSuper hd

theorem challenge_locallyLipschitzOn_of_isViscSuper {U : Set (E d)} {Q u : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) (hharm : HarmonicOnNhd u (posSet u U)) (hQ : ContinuousOn Q U) :
    LocallyLipschitzOn U u :=
  locallyLipschitzOn_of_isViscSuper hU hu hharm hQ

end EllipticBernoulli
