/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Defs.Variational

/-!
# Headline statements: obstacle problems and energy perturbations

One `def …Statement : Prop` per headline result. The theorems proving them live in
`EllipticBernoulli/Variational/*`.

* `ObstacleExistenceStatement` (direct method).
* `ObstacleContinuityStatement` (interior and boundary continuity, De Giorgi).
* `EnergyDecreaseSuperStatement`, `EnergyDecreaseSubStatement`, `OneSidedViscStatement`,
  `ObstacleViscStatement`.

The obstacle constraint is the pointwise constraint set `K : E d → Set ℝ` of `IsObstacleMinimizer`.

The energy is `J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}`, so the free boundary condition is `|∇u| = Q`.
Feldman–Kim–Požár write the energy with `Q 1_{v>0}` and the condition `|∇u|² = Q`; their results
are used here with `Q` replaced by `Q²` in the energy.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace EllipticBernoulli

/-! ### Existence -/

/-- **Existence for the obstacle problem** (direct method). For bounded measurable `Q`,
`u ∈ H¹_loc(U)`, a ball `B = B_r(x₀)` with `B̄ ⊆ U`, and closed constraint sets `K y` containing
`u y` for `y ∈ U`, there is an obstacle minimizer (a good representative satisfying the constraint
and the boundary condition pointwise). Proved by `exists_isObstacleMinimizer`
(`Variational/Existence.lean`). -/
def ObstacleExistenceStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d} {K : E d → Set ℝ} {x₀ : E d}
    {r : ℝ}, IsOpen U → (∃ C, ∀ x ∈ U, |Q x| ≤ C) → Measurable Q → MemH1Loc U u Gu → 0 < r →
    closedBall x₀ r ⊆ U → (∀ y, IsClosed (K y)) → (∀ y ∈ U, u y ∈ K y) →
    ∃ (w : E d → ℝ) (Gw : E d → E d), IsObstacleMinimizer U (ball x₀ r) Q u K w Gw

/-! ### Continuity -/

/-- **Continuity of obstacle minimizers.** Let `Q` be Lipschitz with `0 < c ≤ Q ≤ C` on `U`, and
`u ≥ 0` locally Lipschitz. For the two obstacles `K = Icc 0 u` and `K = Ici u`, every obstacle
minimizer has an a.e.-equal representative which is still an obstacle minimizer (with the same
gradient) and is continuous on all of `U`, including across `∂B`.

The proof of Abedin–Feldman–Stinson, Lemma 6.3 needs this continuity on all of `U`. The interior
argument is new here: a De Giorgi argument for the obstacle problem, in which the obstacle's
Lipschitz bound controls the oscillation whenever a truncation level is not admissible. The proof
uses only `Q² ≤ C` and that `u` is locally Lipschitz. Proved by
`IsObstacleMinimizer.exists_continuousOn` (`Variational/Continuity.lean`). -/
def ObstacleContinuityStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ} {K : E d → Set ℝ} {w : E d → ℝ} {Gw : E d → E d}
    {x₀ : E d} {r : ℝ}, IsOpen U → (∃ L, LipschitzOnWith L Q U) →
    (∃ c > 0, ∀ x ∈ U, c ≤ Q x) → (∃ C, ∀ x ∈ U, Q x ≤ C) → LocallyLipschitzOn U u →
    (∀ y ∈ U, 0 ≤ u y) → closedBall x₀ r ⊆ U → 0 < r →
    (K = (fun y ↦ Icc 0 (u y)) ∨ K = (fun y ↦ Ici (u y))) →
    IsObstacleMinimizer U (ball x₀ r) Q u K w Gw →
    ∃ w' : E d → ℝ, (∀ᵐ y ∂volume.restrict U, w' y = w y) ∧
      IsObstacleMinimizer U (ball x₀ r) Q u K w' Gw ∧ ContinuousOn w' U

/-! ### Energy perturbations -/

/-- **Energy decrease when the supersolution test fails** at a strict touching point
(Feldman–Kim–Požár, proof of Lemma 3.3, and Lemma A.1). No harmonicity of `w` is assumed:
Feldman–Kim–Požár use harmonicity of `u` in `{u > 0}` and treat only test functions with
`∇φ(x₀) ≠ 0`; the proof here uses neither, only the sign of `Δφ`. The statement holds for
continuous `Q ≥ 0` (`energy_decrease_of_not_super_of_continuousOn`). Proved by
`energy_decrease_of_not_super` (`Variational/Perturbation.lean`). -/
def EnergyDecreaseSuperStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d},
    IsOpen U → (∃ K, LipschitzOnWith K Q U) → (∃ c > 0, ∀ x ∈ U, c ≤ Q x) →
    (∃ C, ∀ x ∈ U, Q x ≤ C) → ContinuousOn w U → (∀ x ∈ U, 0 ≤ w x) →
    MemH1Loc U w Gw → ∀ {B : Set (E d)}, IsOpen B → CompactlyContained B U →
    ∀ {φ : E d → ℝ}, ContDiff ℝ ∞ φ → ∀ {x₀ : E d}, x₀ ∈ B →
    (φ x₀ = w x₀ ∧ ∀ᶠ y in 𝓝[≠] x₀, φ y < w y) →
    (0 < Δ φ x₀ ∧ (φ x₀ = 0 → Q x₀ < ‖∇ φ x₀‖)) →
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, w y ≤ w' y ∧ w' y ≤ max (w y) (φ y + η)) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw

/-- **Energy decrease when the subsolution test fails** at a strict touching point
(Feldman–Kim–Požár, proof of Lemma 3.3, and Lemma A.1). As for `EnergyDecreaseSuperStatement`, no
harmonicity is used; the statement holds for continuous `Q`, without `w ≥ 0`
(`energy_decrease_of_not_sub_of_continuousOn`). Proved by `energy_decrease_of_not_sub`
(`Variational/Perturbation.lean`). -/
def EnergyDecreaseSubStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d},
    IsOpen U → (∃ K, LipschitzOnWith K Q U) → (∃ c > 0, ∀ x ∈ U, c ≤ Q x) →
    (∃ C, ∀ x ∈ U, Q x ≤ C) → ContinuousOn w U → (∀ x ∈ U, 0 ≤ w x) →
    MemH1Loc U w Gw → ∀ {B : Set (E d)}, IsOpen B → CompactlyContained B U →
    ∀ {φ : E d → ℝ}, ContDiff ℝ ∞ φ → ∀ {x₀ : E d}, x₀ ∈ B →
    x₀ ∈ closure (posSet w U) →
    (max (φ x₀) 0 = w x₀ ∧
      ∀ᶠ y in 𝓝[(closure (posSet w U) ∩ U) \ {x₀}] x₀, w y < max (φ y) 0) →
    (Δ φ x₀ < 0 ∧ (φ x₀ = 0 → ‖∇ φ x₀‖ < Q x₀)) →
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, min (w y) (max (φ y - η) 0) ≤ w' y ∧ w' y ≤ w y) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw

/-! ### One-sided minimizers are viscosity sub/supersolutions -/

/-- **Upward minimizers are supersolutions** (Feldman–Kim–Požár, Lemma 3.3; Velichkov,
Proposition 7.1). Continuous `Q ≥ 0`: the energy only sees `Q²`, while the viscosity test sees `Q`,
so without `Q ≥ 0` the statement is false (e.g. `u = y₊` in `d = 1` with `Q ≡ -1`);
Feldman–Kim–Požár take a constant positive coefficient. Proved by `IsUpwardMinimizer.isViscSuper`
(`Variational/OneSided.lean`). -/
def UpwardViscSuperStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}, IsOpen U → ContinuousOn Q U →
    (∀ y ∈ U, 0 ≤ Q y) → ContinuousOn u U → (∀ y ∈ U, 0 ≤ u y) →
    IsUpwardMinimizer U Q u → IsViscSuper U Q u

/-- **Downward minimizers are subsolutions** (Feldman–Kim–Požár, Lemma 3.3; Velichkov,
Proposition 7.1). No sign condition on `Q` is needed. Proved by `IsDownwardMinimizer.isViscSub`
(`Variational/OneSided.lean`). -/
def DownwardViscSubStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}, IsOpen U → ContinuousOn Q U →
    ContinuousOn u U → (∀ y ∈ U, 0 ≤ u y) → IsDownwardMinimizer U Q u → IsViscSub U Q u

/-- **Continuous local energy minimizers are viscosity solutions** (Velichkov, Proposition 7.1),
with `Q ≥ 0` continuous (see `UpwardViscSuperStatement`). Proved by
`IsLocalEnergyMinimizer.isViscSolution` (`Variational/OneSided.lean`). -/
def EnergyMinimizerViscStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}, IsOpen U → ContinuousOn Q U →
    (∀ y ∈ U, 0 ≤ Q y) → ContinuousOn u U → (∀ y ∈ U, 0 ≤ u y) →
    IsLocalEnergyMinimizer U Q u → IsViscSolution U Q u

/-- The three one-sided statements. -/
def OneSidedViscStatement : Prop :=
  UpwardViscSuperStatement ∧ DownwardViscSubStatement ∧ EnergyMinimizerViscStatement

/-- **Obstacle minimizers below a supersolution are supersolutions** (Abedin–Feldman–Stinson,
proof of Lemma 6.3, Step 1). If `u` is a supersolution and `w` minimizes `J_Q(·; B_r(x₀))` under
`0 ≤ w ≤ u` and is continuous on `U`, then `w` is a supersolution in `U`. Proved by
`IsObstacleMinimizer.isViscSuper_of_upper` (`Variational/OneSided.lean`). -/
def ObstacleViscSuperStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ},
    IsOpen U → (∃ K, LipschitzOnWith K Q U) → (∃ c > 0, ∀ x ∈ U, c ≤ Q x) →
    (∃ C, ∀ x ∈ U, Q x ≤ C) → IsViscSuper U Q u → closedBall x₀ r ⊆ U →
    IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Icc 0 (u y)) w Gw → ContinuousOn w U →
    IsViscSuper U Q w

/-- **Obstacle minimizers above a subsolution are subsolutions** (Abedin–Feldman–Stinson, proof
of Lemma 6.3, Step 2), dual of `ObstacleViscSuperStatement` with the constraint `u ≤ w`. Proved by
`IsObstacleMinimizer.isViscSub_of_lower` (`Variational/OneSided.lean`). -/
def ObstacleViscSubStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ},
    IsOpen U → (∃ K, LipschitzOnWith K Q U) → (∃ c > 0, ∀ x ∈ U, c ≤ Q x) →
    (∃ C, ∀ x ∈ U, Q x ≤ C) → IsViscSub U Q u → closedBall x₀ r ⊆ U →
    IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Ici (u y)) w Gw → ContinuousOn w U →
    IsViscSub U Q w

/-- Both obstacle statements. -/
def ObstacleViscStatement : Prop :=
  ObstacleViscSuperStatement ∧ ObstacleViscSubStatement

end EllipticBernoulli
