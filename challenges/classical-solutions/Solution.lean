import EllipticBernoulli.Classical.Viscosity
import EllipticBernoulli.Classical.InnerVariation
import EllipticBernoulli.Classical.GradientBound

/-!
# Solution: classical solutions

Discharges the challenge through the library modules imported above:
`IsClassicalSolution.isViscSolution`, `IsClassicalSolution.integral_innerVarIntegrand_eq_zero` and
`classical_lipschitz_bound`.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace EllipticBernoulli

variable {d : ℕ}

theorem challenge_isClassicalSolution_isViscSolution {U : Set (E d)} {Q u : E d → ℝ}
    (hu : IsClassicalSolution U Q u) (hQ : ContinuousOn Q U) : IsViscSolution U Q u :=
  IsClassicalSolution.isViscSolution hu hQ

theorem challenge_isClassicalSolution_integral_innerVarIntegrand_eq_zero {U : Set (E d)}
    {Q u : E d → ℝ} {ξ : E d → E d}
    (hu : IsClassicalSolution U Q u) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ y ∈ U, c ≤ Q y) (hξ : ∃ K, LipschitzWith K ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ U) :
    ∫ x in U, innerVarIntegrand Q u ((posSet u U).indicator 1) ξ x = 0 :=
  IsClassicalSolution.integral_innerVarIntegrand_eq_zero hu hQ hQpos hξ hξc hξU

theorem challenge_classical_lipschitz_bound (L : ℝ≥0) :
    ∃ w : ℝ → ℝ, ContinuousOn w (Ico 0 1) ∧ MonotoneOn w (Ico 0 1) ∧
      Tendsto w (𝓝[>] 0) (𝓝 0) ∧
      ∀ u : E d → ℝ, IsClassicalSolution (ball 0 1) (fun _ ↦ 1) u →
        LipschitzOnWith L u (ball 0 1) →
        u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r) :=
  classical_lipschitz_bound L

end EllipticBernoulli
