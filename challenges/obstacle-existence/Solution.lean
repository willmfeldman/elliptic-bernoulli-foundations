module

public import EllipticBernoulli.Variational.Existence
public import EllipticBernoulli.Variational.Continuity

/-!
# Solution: existence and continuity for the obstacle problem

Discharges the challenge through the library modules imported above, by `exists_isObstacleMinimizer`
and `IsObstacleMinimizer.exists_continuousOn`.
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory Metric

namespace EllipticBernoulli

variable {d : ℕ}

theorem challenge_exists_isObstacleMinimizer {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d}
    {K : E d → Set ℝ} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ C, ∀ x ∈ U, |Q x| ≤ C)
    (hQm : Measurable Q)
    (hu : MemH1Loc U u Gu) (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) (hK : ∀ y, IsClosed (K y))
    (huK : ∀ y ∈ U, u y ∈ K y) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), IsObstacleMinimizer U (ball x₀ r) Q u K w Gw :=
  exists_isObstacleMinimizer hU hQ hQm hu hr hB hK huK

theorem challenge_isObstacleMinimizer_exists_continuousOn {U : Set (E d)} {Q u : E d → ℝ}
    {K : E d → Set ℝ} {w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U)
    (hQ : ∃ L, LipschitzOnWith L Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y) (hB : closedBall x₀ r ⊆ U)
    (hr : 0 < r) (hK : K = (fun y ↦ Icc 0 (u y)) ∨ K = (fun y ↦ Ici (u y)))
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u K w Gw) :
    ∃ w' : E d → ℝ, (∀ᵐ y ∂volume.restrict U, w' y = w y) ∧
      IsObstacleMinimizer U (ball x₀ r) Q u K w' Gw ∧ ContinuousOn w' U :=
  IsObstacleMinimizer.exists_continuousOn hU hQ hQpos hQb hu hu0 hB hr hK hw

end EllipticBernoulli
