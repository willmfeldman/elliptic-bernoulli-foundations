module

public import EllipticBernoulli.Flatness.Classical

/-!
# Solution: flat free boundaries are regular (De Silva)

Discharges the challenge through the library modules imported above:
`isC1GammaHypersurfaceNear_of_flat` and `isClassicalNear_of_flat`.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

@[expose] public noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace EllipticBernoulli

variable {d : ℕ}

theorem challenge_isC1GammaHypersurfaceNear_of_flat (hd : 2 ≤ d) (L : ℝ≥0) (qmin qmax : ℝ)
    (hqmin : 0 < qmin) :
    ∃ εbar > 0, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsC1GammaHypersurfaceNear (freeBoundary u U) x₀ (r / 2) :=
  isC1GammaHypersurfaceNear_of_flat hd L qmin qmax hqmin

theorem challenge_isClassicalNear_of_flat (hd : 2 ≤ d) (L : ℝ≥0) (qmin qmax : ℝ)
    (hqmin : 0 < qmin) :
    ∃ εbar > 0, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsClassicalNear U Q u x₀ :=
  isClassicalNear_of_flat hd L qmin qmax hqmin

end EllipticBernoulli
