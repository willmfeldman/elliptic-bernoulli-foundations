module

public import EllipticBernoulli.Variational.OneSided

/-!
# Solution: minimizers are viscosity solutions

Discharges the challenge through the library module imported above, by the library's one-sided
and obstacle-minimizer theorems.
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

namespace EllipticBernoulli

variable {d : ℕ}

theorem challenge_isUpwardMinimizer_isViscSuper {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ y ∈ U, 0 ≤ Q y) (hu : ContinuousOn u U)
    (hu0 : ∀ y ∈ U, 0 ≤ u y) (hmin : IsUpwardMinimizer U Q u) : IsViscSuper U Q u :=
  IsUpwardMinimizer.isViscSuper hU hQ hQ0 hu hu0 hmin

theorem challenge_isDownwardMinimizer_isViscSub {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hu : ContinuousOn u U) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    (hmin : IsDownwardMinimizer U Q u) : IsViscSub U Q u :=
  IsDownwardMinimizer.isViscSub hU hQ hu hu0 hmin

theorem challenge_isLocalEnergyMinimizer_isViscSolution {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ y ∈ U, 0 ≤ Q y) (hu : ContinuousOn u U)
    (hu0 : ∀ y ∈ U, 0 ≤ u y) (hmin : IsLocalEnergyMinimizer U Q u) : IsViscSolution U Q u :=
  IsLocalEnergyMinimizer.isViscSolution hU hQ hQ0 hu hu0 hmin

theorem challenge_isObstacleMinimizer_isViscSuper_of_upper {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : IsViscSuper U Q u) (hr : closedBall x₀ r ⊆ U)
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Icc 0 (u y)) w Gw)
    (hwc : ContinuousOn w U) : IsViscSuper U Q w :=
  IsObstacleMinimizer.isViscSuper_of_upper hU hQ hQpos hQb hu hr hw hwc

theorem challenge_isObstacleMinimizer_isViscSub_of_lower {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : IsViscSub U Q u) (hr : closedBall x₀ r ⊆ U)
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Ici (u y)) w Gw)
    (hwc : ContinuousOn w U) : IsViscSub U Q w :=
  IsObstacleMinimizer.isViscSub_of_lower hU hQ hQpos hQb hu hr hw hwc

end EllipticBernoulli
