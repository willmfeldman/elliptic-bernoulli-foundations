/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Variational
public import EllipticBernoulli.Regularity.InteriorObstacle
public import EllipticBernoulli.Regularity.Representative
public import EllipticBernoulli.Sobolev.Energy

/-!
# Continuity of obstacle minimizers

Proves `ObstacleContinuityStatement` (`IsObstacleMinimizer.exists_continuousOn`): for the two
obstacle problems (6.1) and (6.3) in the proof of Abedin–Feldman–Stinson, Lemma 6.3,
`K = Icc 0 u` and `K = Ici u`, every obstacle minimizer has an a.e.-equal representative which is
still an obstacle minimizer (same gradient) and is continuous on all of `U`. The paper uses this
continuity, including across `∂B`, and cites only an interior result for it; the interior argument
here is new, and continuity across `∂B` is proved separately.

## Proof

* **Interior** (`Regularity/InteriorObstacle.lean`): at every `y ∈ B = B_r(x₀)` the essential
  oscillation of `w` on small balls centred at `y` tends to zero (De Giorgi, with the obstacle
  alternative).
* **Representative** (`Regularity/Representative.lean`): `w' = lim ⨍_{B̄_s(x)} w` on `B`, `w' = w`
  off `B`. It is continuous on `B`, equal to `w` a.e. (Lebesgue differentiation), and still
  satisfies the constraint pointwise (`ballLimit_mem`, continuity of `u`); the minimality transfers
  through `energyJ_congr_ae`.
* **Across `∂B`**: the boundary argument (`Regularity/ObstacleBoundary.lean`,
  `obstacle_below_continuousOn`, `obstacle_above_continuousOn`) applied to `w'`.
* `d = 0`: `E 0` is a point, and `w' = w`.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- `w` is integrable on `B` for `w ∈ H¹_loc(U)`, `B̄ ⊆ U`. -/
theorem integrableOn_ball_of_memH1Loc {U : Set (E d)} {w : E d → ℝ} {G : E d → E d}
    (hw : MemH1Loc U w G) {x₀ : E d} {r : ℝ} (hB : closedBall x₀ r ⊆ U) :
    IntegrableOn w (ball x₀ r) := by
  haveI : IsFiniteMeasure (volume.restrict (closedBall x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  have h : IntegrableOn w (closedBall x₀ r) :=
    (hw.2 _ hB (isCompact_closedBall x₀ r)).1.integrable (by norm_num)
  exact h.mono_set ball_subset_closedBall

/-- **The continuous representative in `B`.** If the essential oscillation of an obstacle
minimizer `w` vanishes at every point of `B = B_r(x₀)` and the ball limits of `w` satisfy the
constraint there, then `w' = ballLimit w` on `B`, `w' = w` off `B`, is an a.e.-equal obstacle
minimizer, continuous on `B`. -/
theorem IsObstacleMinimizer.exists_rep_continuousOn_ball {U : Set (E d)}
    {Q u : E d → ℝ} {K : E d → Set ℝ} {w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ}
    (hmin : IsObstacleMinimizer U (ball x₀ r) Q u K w Gw) (hB : closedBall x₀ r ⊆ U)
    (hosc : ∀ y ∈ ball x₀ r, EssOscVanishes w y)
    (hK : ∀ y ∈ ball x₀ r, ballLimit w y ∈ K y) :
    ∃ w' : E d → ℝ, (∀ᵐ y ∂volume.restrict U, w' y = w y) ∧
      IsObstacleMinimizer U (ball x₀ r) Q u K w' Gw ∧ ContinuousOn w' (ball x₀ r) := by
  classical
  obtain ⟨hGw, hwout, hwK, hwmin⟩ := hmin
  set w' : E d → ℝ := fun x ↦ if x ∈ ball x₀ r then ballLimit w x else w x with hw'
  have hint := integrableOn_ball_of_memH1Loc hGw hB
  have hBU : ball x₀ r ⊆ U := ball_subset_closedBall.trans hB
  have hae_ball : ∀ᵐ x ∂volume, x ∈ ball x₀ r → ballLimit w x = w x :=
    (ae_restrict_iff' measurableSet_ball).1 (ballLimit_ae_eq isOpen_ball hint)
  have hae : ∀ᵐ x ∂volume.restrict U, w' x = w x := by
    filter_upwards [ae_restrict_of_ae hae_ball] with x hx
    by_cases hxB : x ∈ ball x₀ r
    · simp only [hw', if_pos hxB]; exact hx hxB
    · simp only [hw', if_neg hxB]
  have hGw' : MemH1Loc U w' Gw := by
    refine ⟨hGw.1.congr_fun_ae (hae.mono fun x hx ↦ hx.symm), fun L hL hLc ↦
      ⟨(hGw.2 L hL hLc).1.ae_eq ?_, (hGw.2 L hL hLc).2⟩⟩
    exact (ae_restrict_of_ae_restrict_of_subset hL hae).mono fun x hx ↦ hx.symm
  refine ⟨w', hae, ⟨hGw', fun y hy ↦ ?_, fun y hy ↦ ?_, fun v Gv hv hvout hvK ↦ ?_⟩, ?_⟩
  · simp only [hw', if_neg hy.2]; exact hwout y hy
  · by_cases hyB : y ∈ ball x₀ r
    · simp only [hw', if_pos hyB]; exact hK y hyB
    · simp only [hw', if_neg hyB]; exact hwK y hy
  · rw [energyJ_congr_ae measurableSet_ball (ae_restrict_of_ae_restrict_of_subset hBU hae)
      (ae_of_all _ fun _ ↦ rfl)]
    exact hwmin v Gv hv hvout hvK
  · exact (continuousOn_ballLimit isOpen_ball hint hosc).congr fun x hx ↦ by
      simp only [hw', if_pos hx]

/-- The ball limits of a two-sided obstacle minimizer satisfy `0 ≤ w' ≤ u` in `B`. -/
theorem ballLimit_mem_Icc_of_twoSided {U : Set (E d)} (hU : IsOpen U) {u w : E d → ℝ}
    (hu : ContinuousOn u U) (hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y) {x₀ : E d} {r : ℝ}
    (hB : closedBall x₀ r ⊆ U) (hint : IntegrableOn w (ball x₀ r)) {y : E d}
    (hy : y ∈ ball x₀ r) (hosc : EssOscVanishes w y) :
    ballLimit w y ∈ Icc 0 (u y) := by
  have hyU : y ∈ U := hB (ball_subset_closedBall hy)
  have key : ∀ ε > 0, ballLimit w y ∈ Icc 0 (u y + ε) := by
    intro ε hε
    obtain ⟨δ, hδ, hδu⟩ := Metric.mem_nhds_iff.1 ((hu.continuousAt (hU.mem_nhds hyU)).eventually
      (gt_mem_nhds (show u y < u y + ε by linarith)))
    have hW : ball y δ ∩ ball x₀ r ∈ 𝓝 y :=
      inter_mem (ball_mem_nhds y hδ) (isOpen_ball.mem_nhds hy)
    refine ballLimit_mem hW (hint.mono_set inter_subset_right) hosc (convex_Icc _ _) isClosed_Icc
      ((ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)).2
        (Eventually.of_forall fun z hz ↦ ?_))
    have h1 := hwu z (hB (ball_subset_closedBall hz.2))
    exact ⟨h1.1, h1.2.trans (hδu hz.1).le⟩
  exact ⟨(key 1 one_pos).1, le_of_forall_pos_le_add fun ε hε ↦ (key ε hε).2⟩

/-- The ball limits of a lower-obstacle minimizer satisfy `u ≤ w'` in `B`. -/
theorem ballLimit_mem_Ici_of_lower {U : Set (E d)} (hU : IsOpen U) {u w : E d → ℝ}
    (hu : ContinuousOn u U) (hwu : ∀ y ∈ U, u y ≤ w y) {x₀ : E d} {r : ℝ}
    (hB : closedBall x₀ r ⊆ U) (hint : IntegrableOn w (ball x₀ r)) {y : E d}
    (hy : y ∈ ball x₀ r) (hosc : EssOscVanishes w y) :
    ballLimit w y ∈ Ici (u y) := by
  have hyU : y ∈ U := hB (ball_subset_closedBall hy)
  have key : ∀ ε > 0, ballLimit w y ∈ Ici (u y - ε) := by
    intro ε hε
    obtain ⟨δ, hδ, hδu⟩ := Metric.mem_nhds_iff.1 ((hu.continuousAt (hU.mem_nhds hyU)).eventually
      (lt_mem_nhds (show u y - ε < u y by linarith)))
    have hW : ball y δ ∩ ball x₀ r ∈ 𝓝 y :=
      inter_mem (ball_mem_nhds y hδ) (isOpen_ball.mem_nhds hy)
    refine ballLimit_mem hW (hint.mono_set inter_subset_right) hosc (convex_Ici _) isClosed_Ici
      ((ae_restrict_iff' (measurableSet_ball.inter measurableSet_ball)).2
        (Eventually.of_forall fun z hz ↦ ?_))
    exact (hδu hz.1).le.trans (hwu z (hB (ball_subset_closedBall hz.2)))
  refine mem_Ici.2 (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  have := mem_Ici.1 (key ε hε)
  linarith

/-- In dimension `0` every function is continuous. -/
theorem continuousOn_of_dim_zero (f : E 0 → ℝ) (s : Set (E 0)) : ContinuousOn f s := by
  have h : ∀ x y : E 0, x = y := fun x y ↦ by ext i; exact Fin.elim0 i
  exact (continuousOn_const (c := f 0)).congr fun x _ ↦ by rw [h x 0]

/-- Continuous representatives of obstacle minimizers (`ObstacleContinuityStatement`). -/
theorem IsObstacleMinimizer.exists_continuousOn : ObstacleContinuityStatement := by
  intro d U Q u K w Gw x₀ r hU hQL hQpos hQb hu hu0 hB hr hK hmin
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨w, ae_of_all _ fun _ ↦ rfl, hmin, continuousOn_of_dim_zero w U⟩
  obtain ⟨Cq, hCq, hQq⟩ := sq_le_of_bounds hQpos hQb
  have hint := integrableOn_ball_of_memH1Loc hmin.1 hB
  rcases hK with rfl | rfl
  · -- two-sided obstacle `0 ≤ w ≤ u`
    have hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y := hmin.2.2.1
    have hosc : ∀ y ∈ ball x₀ r, EssOscVanishes w y := fun y hy ↦
      essOscVanishes_twoSided hd hU hCq hQq hu hB hmin.1 hmin.2.1 hwu hmin.2.2.2 hy
    obtain ⟨w', hae, hmin', hwc⟩ := hmin.exists_rep_continuousOn_ball hB hosc fun y hy ↦
      ballLimit_mem_Icc_of_twoSided hU hu.continuousOn hwu hB hint hy (hosc y hy)
    exact ⟨w', hae, hmin', obstacle_below_continuousOn hU hQL hQpos hQb hu hu0 hr hB hmin'.1
      hwc hmin'.2.1 hmin'.2.2.1 hmin'.2.2.2⟩
  · -- lower obstacle `u ≤ w`
    have hwu : ∀ y ∈ U, u y ≤ w y := hmin.2.2.1
    have hosc : ∀ y ∈ ball x₀ r, EssOscVanishes w y := fun y hy ↦
      essOscVanishes_lower hd hU hCq hQq hu hB hmin.1 hmin.2.1 hwu hmin.2.2.2 hy
    obtain ⟨w', hae, hmin', hwc⟩ := hmin.exists_rep_continuousOn_ball hB hosc fun y hy ↦
      ballLimit_mem_Ici_of_lower hU hu.continuousOn hwu hB hint hy (hosc y hy)
    exact ⟨w', hae, hmin', obstacle_above_continuousOn hU hQL hQpos hQb hu hu0 hr hB hmin'.1
      hwc hmin'.2.1 hmin'.2.2.1 hmin'.2.2.2⟩

end EllipticBernoulli
