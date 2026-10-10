module

public import EllipticBernoulli.Hodograph.Chart

/-!
# Solution: smooth one-sided charts at flat free-boundary points

Discharges the challenge through the library module imported above: `flat_chart`.

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
-/

@[expose] public noncomputable section

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

namespace EllipticBernoulli

variable {d : ℕ}

theorem challenge_flat_chart (hd : 2 ≤ d) {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d}
    (hU : IsOpen U) (hc : ContinuousOn u U) (hnn : ∀ x ∈ U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) (hx₀ : x₀ ∈ freeBoundary u U) (he : ‖e‖ = 1)
    (hblow : IsBlowupLimit u x₀ (fun y ↦ max (inner ℝ y e) 0)) :
    ∃ ρ > 0, ball x₀ ρ ⊆ U ∧ ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ) ∧
      (∀ x ∈ ball x₀ ρ, u x = max (F x) 0) ∧ (∀ x ∈ ball x₀ ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ, F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ ball x₀ ρ, 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ | 0 < F x} :=
  flat_chart hd hU hc hnn hmin hx₀ he hblow

end EllipticBernoulli
