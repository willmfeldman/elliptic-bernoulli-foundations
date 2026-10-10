module

public import EllipticBernoulli.Variational.EnergyMinimizer

/-!
# Solution: regularity of local energy minimizers

Discharges the challenge through the library module imported above:
`IsLocalEnergyMinimizer.exists_regular_representative`.

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Laplacian

namespace EllipticBernoulli

variable {d : ℕ}

theorem challenge_isLocalEnergyMinimizer_exists_regular_representative {U : Set (E d)}
    {Q u : E d → ℝ} (hU : IsOpen U) (hQc : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U Q u) :
    ∃ v : E d → ℝ, (∀ᵐ x ∂volume.restrict U, v x = u x) ∧ IsLocalEnergyMinimizer U Q v ∧
      LocallyLipschitzOn U v ∧ (∀ x ∈ U, 0 ≤ v x) ∧ IsOpen (posSet v U) ∧
      ContDiffOn ℝ ∞ v (posSet v U) ∧ ∀ x ∈ posSet v U, Δ v x = 0 :=
  IsLocalEnergyMinimizer.exists_regular_representative hU hQc hQ0 hQb hu0 hmin

end EllipticBernoulli
