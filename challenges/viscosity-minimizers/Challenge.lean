import Challenge.Setting
import Challenge.Sobolev
import Challenge.Touching
import Challenge.Viscosity
import Challenge.Variational

/-!
# Challenge: minimizers are viscosity solutions

Trusted statement surface for the passage from energy minimality to the viscosity sense of the
one-phase problem `Δu = 0` in `{u > 0}`, `|∇u| = Q` on `∂{u > 0}`, for the Alt–Caffarelli energy
`J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}`.

* One-sided minimizers (Feldman–Kim–Požár, Lemma 3.3; Velichkov, Proposition 7.1): for continuous
  `Q ≥ 0` and continuous `u ≥ 0`, upward minimizers are viscosity supersolutions, downward
  minimizers are viscosity subsolutions, and local energy minimizers are viscosity solutions. Upward
  and downward minimizers are harmonic and `C²` in `{u > 0}` by definition.
* Obstacle minimizers (Abedin–Feldman–Stinson, Lemma 6.3, Steps 1–2): for `Q` Lipschitz with
  `0 < c ≤ Q ≤ C`, a continuous minimizer of `J_Q(·; B_r(x₀))` under the constraint `0 ≤ w ≤ u`
  below a supersolution `u` is a supersolution in `U`, and a continuous minimizer under `u ≤ w`
  above a subsolution `u` is a subsolution in `U`.

The project vocabulary is restated in `Challenge/*.lean`, one file per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Basic/Touching.lean`, `Defs/Viscosity.lean`,
`Defs/Variational.lean`), with the library's names, definitions and order. Every file imports
Mathlib modules only (the same ones as the library file it restates).

## References

* W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: upward minimizers are viscosity supersolutions (Feldman–Kim–Požár, Lemma 3.3).
`Q ≥ 0` is needed: the energy sees only `Q²`, while the viscosity test sees `Q`. -/
theorem challenge_isUpwardMinimizer_isViscSuper {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ y ∈ U, 0 ≤ Q y) (hu : ContinuousOn u U)
    (hu0 : ∀ y ∈ U, 0 ≤ u y) (hmin : IsUpwardMinimizer U Q u) : IsViscSuper U Q u := by
  sorry

/-- Challenge: downward minimizers are viscosity subsolutions (Feldman–Kim–Požár,
Lemma 3.3). -/
theorem challenge_isDownwardMinimizer_isViscSub {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hu : ContinuousOn u U) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    (hmin : IsDownwardMinimizer U Q u) : IsViscSub U Q u := by
  sorry

/-- Challenge: continuous local energy minimizers are viscosity solutions (Velichkov,
Proposition 7.1). -/
theorem challenge_isLocalEnergyMinimizer_isViscSolution {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ y ∈ U, 0 ≤ Q y) (hu : ContinuousOn u U)
    (hu0 : ∀ y ∈ U, 0 ≤ u y) (hmin : IsLocalEnergyMinimizer U Q u) : IsViscSolution U Q u := by
  sorry

/-- Challenge: a continuous obstacle minimizer below a supersolution, under the constraint
`0 ≤ w ≤ u`, is a supersolution (Abedin–Feldman–Stinson, Lemma 6.3, Step 1). -/
theorem challenge_isObstacleMinimizer_isViscSuper_of_upper {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : IsViscSuper U Q u) (hr : closedBall x₀ r ⊆ U)
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Icc 0 (u y)) w Gw)
    (hwc : ContinuousOn w U) : IsViscSuper U Q w := by
  sorry

/-- Challenge: a continuous obstacle minimizer above a subsolution, under the constraint
`u ≤ w`, is a subsolution (Abedin–Feldman–Stinson, Lemma 6.3, Step 2). -/
theorem challenge_isObstacleMinimizer_isViscSub_of_lower {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : IsViscSub U Q u) (hr : closedBall x₀ r ⊆ U)
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Ici (u y)) w Gw)
    (hwc : ContinuousOn w U) : IsViscSub U Q w := by
  sorry

end EllipticBernoulli
