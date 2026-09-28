/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Flatness.Barriers
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import EllipticBernoulli.Harmonic.Harnack
import EllipticBernoulli.Viscosity.Harmonic

/-!
# De Silva's one-step lemma (Lemma 3.3)

De Silva (2011), Lemma 3.3, with `f = 0`, `a_{ij} = δ_{ij}`, `g = Q`.

* `flat_lower_step`: if `u ≥ (⟪y, e⟫ + σ)₊` on `B_1` and `u(e/5) ≥ ⟪e/5, e⟫ + σ + ε/2`, then
  `u ≥ (⟪y, e⟫ + σ + cε)₊` on `B̄_{1/2}`;
* `flat_upper_step`: if moreover `u ≤ (⟪y, e⟫ + σ + ε)₊` on `B_1` and
  `u(e/5) ≤ ⟪e/5, e⟫ + σ + ε/2`, then `u ≤ (⟪y, e⟫ + σ + (1 - c)ε)₊` on `B̄_{1/2}`.

Both use the globally `C^∞` Gaussian barrier `deSilvaBarrier` (`Flatness/Barriers.lean`) in
place of De Silva's `|x - x̄|^{-γ}`, the Harnack inequality `harnack_ball_explicit` on
`B_{1/10}(e/5)`, and the viscosity definition (`IsViscSolution`, after Abedin–Feldman–Stinson,
Definition 2.1) directly at the touching point in place of De Silva's Lemma 2.4. The "first
touching" is the minimum of a continuous function on a compact set.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Preliminaries -/

theorem harmonicAt_inner_add (e : E d) (σ : ℝ) (x : E d) :
    HarmonicAt (fun y ↦ ⟪y, e⟫ + σ) x := by
  refine ⟨(contDiffAt_id.inner ℝ contDiffAt_const).add contDiffAt_const, ?_⟩
  refine Filter.Eventually.of_forall fun y ↦ ?_
  have := laplacian_mul_inner_add e 1 σ y
  simp only [one_mul] at this
  simpa using this

/-- Harnack lower bound on `B_{1/20}(x)` from `B_{1/10}(x)` with the constant `(3^d)^8` of
`harnack_ball_explicit`. -/
theorem harnack_ball_tenth {h : E d → ℝ} {x : E d}
    (hh : HarmonicOnNhd h (ball x (1 / 10))) (h0 : ∀ y ∈ ball x (1 / 10), 0 ≤ h y) {δ : ℝ}
    (hx : δ ≤ h x) : ∀ y ∈ ball x (1 / 20), δ / ((3 : ℝ) ^ d) ^ 8 ≤ h y := by
  have h2 : ball x (2 * (1 / 20)) = ball x (1 / 10) := by norm_num
  intro y hy
  have := harnack_ball_explicit h x (1 / 20) (by norm_num) (h2 ▸ hh)
    (fun z hz ↦ h0 z (h2 ▸ hz)) x (mem_ball_self (by norm_num)) y hy
  have hC : (0 : ℝ) < ((3 : ℝ) ^ d) ^ 8 := by positivity
  rw [div_le_iff₀ hC]
  linarith [mul_comm (h y) (((3 : ℝ) ^ d) ^ 8)]

theorem one_le_harnackConst : (1 : ℝ) ≤ ((3 : ℝ) ^ d) ^ 8 :=
  one_le_pow₀ (one_le_pow₀ (by norm_num))

private theorem inner_fifth {e : E d} (he : ‖e‖ = 1) : ⟪(1 / 5 : ℝ) • e, e⟫ = 1 / 5 := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]; norm_num

private theorem norm_fifth {e : E d} (he : ‖e‖ = 1) : ‖(1 / 5 : ℝ) • e‖ = 1 / 5 := by
  rw [norm_smul, he]; norm_num

/-- `⟪y, e⟫ ≥ ⟪x, e⟫ - ‖y - x‖` for a unit `e`. -/
private theorem inner_ge_sub_norm {e : E d} (he : ‖e‖ = 1) (x y : E d) :
    ⟪x, e⟫ - ‖y - x‖ ≤ ⟪y, e⟫ := by
  have h := neg_le_of_abs_le (abs_real_inner_le_norm (y - x) e)
  rw [he, mul_one, inner_sub_left] at h
  linarith

private theorem closedBall_fifth_subset {e : E d} (he : ‖e‖ = 1) {ρ : ℝ} (hρ : ρ < 4 / 5) :
    closedBall ((1 / 5 : ℝ) • e) ρ ⊆ ball (0 : E d) 1 := by
  intro y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  rw [mem_ball, dist_zero_right]
  calc ‖y‖ = ‖(y - (1 / 5 : ℝ) • e) + (1 / 5 : ℝ) • e‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - (1 / 5 : ℝ) • e‖ + ‖(1 / 5 : ℝ) • e‖ := norm_add_le _ _
    _ < 1 := by rw [norm_fifth he]; linarith

/-- On `B_{1/10}(e/5)` the flat lower bound `(⟪y, e⟫ + σ)₊ ≤ u` forces `u > 0` (`|σ| < 1/10`). -/
private theorem ball_tenth_subset_posSet {U : Set (E d)} {u : E d → ℝ} {e : E d} {σ : ℝ}
    (he : ‖e‖ = 1) (hB : ball (0 : E d) 1 ⊆ U) (hσ : |σ| < 1 / 10)
    (hlow : ∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ + σ) 0 ≤ u y) :
    ball ((1 / 5 : ℝ) • e) (1 / 10) ⊆ posSet u U := by
  intro y hy
  have hy1 : y ∈ ball (0 : E d) 1 :=
    closedBall_fifth_subset he (by norm_num : (1 / 10 : ℝ) < 4 / 5) (ball_subset_closedBall hy)
  refine ⟨hB hy1, ?_⟩
  rw [mem_ball, dist_eq_norm] at hy
  have h1 := inner_ge_sub_norm he ((1 / 5 : ℝ) • e) y
  rw [inner_fifth he] at h1
  have := (le_max_left _ _).trans (hlow y hy1)
  have := (abs_lt.1 hσ).1
  linarith

/-- The arithmetic contradiction at a free-boundary touching point of the lower barrier:
`1 + c₀ ε k/20 ≤ |∇φ| ≤ Q ≤ 1 + ε²` is impossible when `ε ≤ c₀ k_min / 40`. -/
private theorem slope_contra {c₀ ε kmin k t q : ℝ} (hc₀ : 0 < c₀) (hε : 0 < ε)
    (hεk : ε ≤ c₀ * kmin / 40) (hkmin : 0 < kmin) (hk : kmin ≤ k) (ht : t ≤ -(1 / 20))
    (hG : 1 - c₀ * ε * k * t ≤ q) (hq : q ≤ 1 + ε ^ 2) : False := by
  have h1 : 0 ≤ c₀ * ε * k := by have : 0 ≤ k := hkmin.le.trans hk; positivity
  have h2 := mul_le_mul_of_nonneg_left ht h1
  have h3 : c₀ * ε * kmin ≤ c₀ * ε * k := mul_le_mul_of_nonneg_left hk (by positivity)
  have h4 : c₀ * ε * kmin / 20 ≤ ε ^ 2 := by linarith
  have h5 : ε * (c₀ * kmin / 20) ≤ ε * ε := by linarith
  have := le_of_mul_le_mul_left h5 hε
  linarith

/-! ### The lower step -/

/-- **De Silva (2011), Lemma 3.3, first statement (lower step).** There are `ε̄ > 0` and
`c ∈ (0, 1)` (depending on `d` only) such that: if `u` is a viscosity solution in `U ⊇ B_1` with
`Q ≤ 1 + ε²` on `B_1`, `0 < ε ≤ ε̄`, `(⟪y, e⟫ + σ)₊ ≤ u` on `B_1` with `|σ| < 1/10`, and at
`x̄ = e/5`, `u(x̄) ≥ ⟪x̄, e⟫ + σ + ε/2`, then `u ≥ (⟪y, e⟫ + σ + cε)₊` on `B̄_{1/2}`.

De Silva also assumes the upper bound `u ≤ (⟪y, e⟫ + σ + ε)₊` and `|Q - 1| ≤ ε²`; the lower step
uses neither. Touching can only occur in the open annulus `1/20 ≤ |x - x̄| < 3/4`, where it
contradicts the supersolution property. -/
theorem flat_lower_step (hd : 2 ≤ d) : ∃ εbar > 0, ∃ c ∈ Ioo (0 : ℝ) 1,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (σ ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
    IsViscSolution U Q u → ‖e‖ = 1 → 0 < ε → ε ≤ εbar →
    (∀ y ∈ ball (0 : E d) 1, Q y ≤ 1 + ε ^ 2) → |σ| < 1 / 10 →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ + σ) 0 ≤ u y) →
    1 / 5 + σ + ε / 2 ≤ u ((1 / 5 : ℝ) • e) →
    ∀ y ∈ closedBall (0 : E d) (1 / 2), max (⟪y, e⟫ + σ + c * ε) 0 ≤ u y := by
  have hd0 : 0 < d := by omega
  set CH : ℝ := ((3 : ℝ) ^ d) ^ 8 with hCH
  have hCH1 : 1 ≤ CH := one_le_harnackConst
  set c₀ : ℝ := 1 / (2 * CH) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hc₀half : c₀ ≤ 1 / 2 := by
    rw [hc₀, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set kmin : ℝ := 2 * deSilvaBarrierConst d * deSilvaRate d *
    Real.exp (-(deSilvaRate d * (3 / 4) ^ 2)) with hkmin_def
  have hkmin : 0 < kmin := by
    have := deSilvaBarrierConst_pos hd0; have := deSilvaRate_pos hd0; positivity
  set c₂ := deSilvaBarrierInner d with hc₂_def
  have hc₂ : 0 < c₂ := deSilvaBarrierInner_pos hd0
  have hc₂1 : c₂ ≤ 1 := deSilvaBarrierInner_le_one hd0
  refine ⟨min (1 / 20) (c₀ * kmin / 40), lt_min (by norm_num) (by positivity), c₀ * c₂,
    ⟨by positivity, (mul_le_mul hc₀half hc₂1 hc₂.le (by norm_num)).trans_lt (by norm_num)⟩, ?_⟩
  intro U Q u e σ ε hU hB hu he hε hεbar hQ hσ hlow hx0
  clear_value c₂ kmin c₀ CH
  have hε20 : ε ≤ 1 / 20 := hεbar.trans (min_le_left _ _)
  have hεk : ε ≤ c₀ * kmin / 40 := hεbar.trans (min_le_right _ _)
  have hσ' := abs_lt.1 hσ
  set xbar : E d := (1 / 5 : ℝ) • e with hxbar
  set W := deSilvaBarrier xbar with hW
  set p : E d → ℝ := fun y ↦ ⟪y, e⟫ + σ with hp
  set K := closedBall xbar (3 / 4) with hK
  have hK1 : K ⊆ ball 0 1 := closedBall_fifth_subset he (by norm_num)
  have hpu : ∀ y ∈ ball (0 : E d) 1, p y ≤ u y := fun y hy ↦ (le_max_left _ _).trans (hlow y hy)
  -- Harnack in `B_{1/10}(x̄) ⊆ {u > 0}`: `u - p ≥ c₀ ε` on `B_{1/20}(x̄)`.
  have hpos := ball_tenth_subset_posSet he hB hσ hlow
  have huH := IsViscSolution.harmonicOnNhd_posSet hU hu
  have hHar : ∀ y ∈ ball xbar (1 / 20), c₀ * ε ≤ u y - p y := by
    have hh : HarmonicOnNhd (fun y ↦ u y - p y) (ball xbar (1 / 10)) :=
      fun y hy ↦ (huH y (hpos hy)).sub (harmonicAt_inner_add e σ y)
    have h0 : ∀ y ∈ ball xbar (1 / 10), 0 ≤ u y - p y := fun y hy ↦
      sub_nonneg.2 (hpu y ((closedBall_fifth_subset he (by norm_num : (1 / 10 : ℝ) < 4 / 5))
        (ball_subset_closedBall hy)))
    have hx : ε / 2 ≤ u xbar - p xbar := by
      simp only [hp, hxbar, inner_fifth he]; linarith
    intro y hy
    have := harnack_ball_tenth hh h0 hx y hy
    calc c₀ * ε = ε / 2 / CH := by rw [hc₀]; field_simp
      _ ≤ u y - p y := by rw [hCH]; exact this
  -- The comparison function and its minimum on `K`.
  set v : E d → ℝ := fun y ↦ p y + c₀ * ε * (min (W y) 1 - 1) with hv
  have hvp : ∀ y, v y ≤ p y := fun y ↦ by
    have : min (W y) 1 - 1 ≤ 0 := by linarith [min_le_right (W y) 1]
    have : c₀ * ε * (min (W y) 1 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hc₀pos hε).le this
    simp only [hv]; linarith
  have hcont : ContinuousOn (fun y ↦ u y - v y) K := by
    refine (hu.1.1.mono (hK1.trans hB)).sub (Continuous.continuousOn ?_)
    have := continuous_deSilvaBarrier xbar
    simp only [hv, hp]; fun_prop
  obtain ⟨xt, hxtK, hmin⟩ := (isCompact_closedBall xbar (3 / 4)).exists_isMinOn
    ⟨xbar, mem_closedBall_self (by norm_num)⟩ hcont
  set m := u xt - v xt with hm
  have hm0 : 0 ≤ m := by
    have := hpu xt (hK1 hxtK); have := hvp xt; simp only [hm]; linarith
  have hmin' : ∀ y ∈ K, m ≤ u y - v y := fun y hy ↦ hmin hy
  by_cases hmc : c₀ * ε ≤ m
  · -- `t̄ ≥ c₀ ε`: the conclusion.
    intro y hy
    rw [mem_closedBall, dist_zero_right] at hy
    have hyx : ‖y - xbar‖ ≤ 7 / 10 := by
      calc ‖y - xbar‖ ≤ ‖y‖ + ‖xbar‖ := norm_sub_le _ _
        _ ≤ 7 / 10 := by rw [hxbar, norm_fifth he]; linarith
    have hyK : y ∈ K := by rw [hK, mem_closedBall, dist_eq_norm]; linarith
    have h1 := hmin' y hyK
    have h2 : c₂ ≤ min (W y) 1 := le_min (by rw [hc₂_def]; exact le_deSilvaBarrier hd0 hyx) hc₂1
    have h3 : c₀ * ε * c₂ ≤ c₀ * ε * min (W y) 1 :=
      mul_le_mul_of_nonneg_left h2 (mul_pos hc₀pos hε).le
    refine max_le ?_ (hu.1.2.1 y (hB (hK1 hyK)))
    simp only [hv, hp] at h1
    linarith
  exfalso
  replace hmc := not_le.1 hmc
  have hxtU : xt ∈ U := hB (hK1 hxtK)
  have hxtK' : ‖xt - xbar‖ ≤ 3 / 4 := by rwa [mem_closedBall, dist_eq_norm] at hxtK
  -- (1) inner ball: excluded by Harnack.
  rcases lt_or_ge ‖xt - xbar‖ (1 / 20) with hin | hout
  · have := hHar xt (by rwa [mem_ball, dist_eq_norm])
    have := hvp xt
    simp only [hm] at hmc; linarith
  -- (2) outer sphere: excluded since the barrier vanishes there.
  rcases eq_or_lt_of_le hxtK' with heq | hlt
  · have hW0 : W xt = 0 := deSilvaBarrier_eq_zero heq
    have := hpu xt (hK1 hxtK)
    simp only [hm, hv, hW0] at hmc
    norm_num at hmc
    linarith
  -- (3) open annulus: the smooth barrier touches from below.
  have hWlt : ∀ y, 1 / 25 < ‖y - xbar‖ → min (W y) 1 = W y := fun y hy ↦
    min_eq_left (deSilvaBarrier_lt_one hd0 hy).le
  set φ : E d → ℝ := fun y ↦ 1 * ⟪y, e⟫ + (σ - c₀ * ε + m) + c₀ * ε * W y with hφ
  have hφv : ∀ y, 1 / 25 < ‖y - xbar‖ → φ y = v y + m := fun y hy ↦ by
    simp only [hφ, hv, hp, hWlt y hy]; ring
  have hφs : ContDiff ℝ ∞ φ := by
    have := contDiff_deSilvaBarrier xbar (n := ∞)
    exact ((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).add contDiff_const).add
      (contDiff_const.mul this)
  set N : Set (E d) := ball xbar (3 / 4) ∩ {y | 1 / 25 < ‖y - xbar‖} with hN
  have hNo : IsOpen N :=
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have hxtN : xt ∈ N := ⟨by rwa [mem_ball, dist_eq_norm], show 1 / 25 < ‖xt - xbar‖ by linarith⟩
  have htouch : TouchesBelow φ u U xt := by
    refine ⟨hxtU, by rw [hφv xt hxtN.2, hm]; ring, ?_⟩
    refine eventually_nhdsWithin_of_eventually_nhds (eventually_of_mem (hNo.mem_nhds hxtN) ?_)
    intro y hy
    rw [hφv y hy.2]
    have := hmin' y (ball_subset_closedBall hy.1)
    linarith
  rcases hu.1.2.2 φ hφs xt hxtU htouch with hlap | ⟨hφ0, hgrad⟩
  · rw [hφ, laplacian_mul_inner_add_mul (contDiff_deSilvaBarrier xbar)] at hlap
    have := laplacian_deSilvaBarrier_pos (xbar := xbar) hd0 hxtN.2
    have : 0 < c₀ * ε * Δ (deSilvaBarrier xbar) xt := mul_pos (mul_pos hc₀pos hε) this
    linarith
  · -- the free-boundary alternative: the slope is too large.
    obtain ⟨hk1, -⟩ := deSilvaBarrierSlope_mem (xbar := xbar) (z := xt) hd0 hxtK'
    set k := deSilvaBarrierSlope xbar xt with hk
    replace hk1 : kmin ≤ k := by rw [hkmin_def]; exact hk1
    have hgr : ∇ φ xt = (1 : ℝ) • e + (c₀ * ε) • (-k • (xt - xbar)) :=
      (hasGradientAt_mul_inner_add_mul (hasGradientAt_deSilvaBarrier xbar xt) 1 _ _).gradient
    have hinner : ⟪∇ φ xt, e⟫ = 1 - c₀ * ε * k * (⟪xt, e⟫ - 1 / 5) := by
      rw [hgr, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left, inner_sub_left,
        real_inner_self_eq_norm_sq, he, hxbar, inner_fifth he]
      simp only [RCLike.conj_to_real]
      ring
    have hWt : 0 ≤ W xt := deSilvaBarrier_nonneg hd0 hxtK'
    have hc₀ε : c₀ * ε ≤ 1 / 40 := by
      have := mul_le_mul hc₀half hε20 hε.le (by norm_num); linarith
    have hxte : ⟪xt, e⟫ - 1 / 5 ≤ -(1 / 20) := by
      have h0 : 0 ≤ c₀ * ε * W xt := mul_nonneg (mul_pos hc₀pos hε).le hWt
      simp only [hφ] at hφ0
      linarith
    have hnorm : ⟪∇ φ xt, e⟫ ≤ ‖∇ φ xt‖ := by
      simpa [he] using real_inner_le_norm (∇ φ xt) e
    exact slope_contra hc₀pos hε hεk hkmin hk1 hxte (by rw [← hinner]; exact hnorm.trans hgrad)
      (hQ xt (hK1 hxtK))

/-! ### The upper step -/

/-- The arithmetic contradiction at a free-boundary touching point of the upper barrier:
`(1 - ε²)² ≤ Q² ≤ |∇φ|² = 1 + 2at + a²ρ ≤ 1 - a/20` is impossible when `ε ≤ c₀ k_min / 80`. -/
private theorem slope_contra_upper {c₀ ε kmin k t ρ q G : ℝ} (hc₀ : 0 < c₀) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 20) (hεk : ε ≤ c₀ * kmin / 80) (hkmin : 0 < kmin) (hk : kmin ≤ k)
    (ha : c₀ * ε * k ≤ 1 / 20) (ht : t ≤ -(1 / 20)) (hρ : ρ ≤ 1)
    (hG : G ^ 2 = 1 + 2 * (c₀ * ε * k) * t + (c₀ * ε * k) ^ 2 * ρ) (hqG : q ≤ G)
    (hq : 1 - ε ^ 2 ≤ q) : False := by
  set a := c₀ * ε * k with ha_def
  have ha0 : 0 ≤ a := by have : 0 ≤ k := hkmin.le.trans hk; positivity
  have hε2 : ε ^ 2 ≤ 1 := by
    have := pow_le_pow_left₀ hε.le hε1 2
    norm_num at this
    linarith
  have hq0 : 0 ≤ q := by linarith
  have hq2 : q ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hq0 hqG 2
  have h1 : (1 - ε ^ 2) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ (by linarith) hq 2
  have h2 : 2 * a * t ≤ -(a / 10) := by linarith [mul_le_mul_of_nonneg_left ht ha0]
  have h3 : a ^ 2 * ρ ≤ a / 20 := by
    have : a ^ 2 * ρ ≤ a ^ 2 := mul_le_of_le_one_right (sq_nonneg a) hρ
    linarith [mul_le_mul_of_nonneg_left ha ha0]
  have h4 : a ≤ 40 * ε ^ 2 := by linarith [sq_nonneg (ε ^ 2)]
  have h5 : c₀ * ε * kmin ≤ a := mul_le_mul_of_nonneg_left hk (by positivity)
  have h6 : ε * (c₀ * kmin) ≤ ε * (40 * ε) := by linarith
  have := le_of_mul_le_mul_left h6 hε
  linarith

/-- **De Silva (2011), Lemma 3.3, second statement (upper step).** There are `ε̄ > 0` and
`c ∈ (0, 1)` (depending on `d` only) such that: if `u` is a viscosity solution in `U ⊇ B_1` with
`Q ≥ 1 - ε²` on `B_1`, `0 < ε ≤ ε̄`, `(⟪y, e⟫ + σ)₊ ≤ u ≤ (⟪y, e⟫ + σ + ε)₊` on `B_1` with
`|σ| < 1/10`, and at `x̄ = e/5`, `u(x̄) ≤ ⟪x̄, e⟫ + σ + ε/2`, then
`u ≤ (⟪y, e⟫ + σ + (1 - c)ε)₊` on `B̄_{1/2}`.

The comparison is carried out on the compact set `B̄_{3/4}(x̄) ∩ closure {u > 0}`; touching in the
open annulus is touching of `φ⁺` from above relative to `closure {u > 0} ∩ U`, exactly the
subsolution test of `IsViscSub`, and contradicts the subsolution property. -/
theorem flat_upper_step (hd : 2 ≤ d) : ∃ εbar > 0, ∃ c ∈ Ioo (0 : ℝ) 1,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (σ ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
    IsViscSolution U Q u → ‖e‖ = 1 → 0 < ε → ε ≤ εbar →
    (∀ y ∈ ball (0 : E d) 1, 1 - ε ^ 2 ≤ Q y) → |σ| < 1 / 10 →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ + σ) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + σ + ε) 0) →
    u ((1 / 5 : ℝ) • e) ≤ 1 / 5 + σ + ε / 2 →
    ∀ y ∈ closedBall (0 : E d) (1 / 2), u y ≤ max (⟪y, e⟫ + σ + (1 - c) * ε) 0 := by
  have hd0 : 0 < d := by omega
  set CH : ℝ := ((3 : ℝ) ^ d) ^ 8 with hCH
  have hCH1 : 1 ≤ CH := one_le_harnackConst
  set c₀ : ℝ := 1 / (2 * CH) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hc₀half : c₀ ≤ 1 / 2 := by
    rw [hc₀, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set kmin : ℝ := 2 * deSilvaBarrierConst d * deSilvaRate d *
    Real.exp (-(deSilvaRate d * (3 / 4) ^ 2)) with hkmin_def
  set kmax : ℝ := 2 * deSilvaBarrierConst d * deSilvaRate d with hkmax_def
  have hkmin : 0 < kmin := by
    have := deSilvaBarrierConst_pos hd0; have := deSilvaRate_pos hd0; positivity
  have hkmax : 0 < kmax := by
    have := deSilvaBarrierConst_pos hd0; have := deSilvaRate_pos hd0; positivity
  set c₂ := deSilvaBarrierInner d with hc₂_def
  have hc₂ : 0 < c₂ := deSilvaBarrierInner_pos hd0
  have hc₂1 : c₂ ≤ 1 := deSilvaBarrierInner_le_one hd0
  refine ⟨min (min (1 / 20) (c₀ * kmin / 80)) (1 / (20 * (c₀ * kmax))),
    lt_min (lt_min (by norm_num) (by positivity)) (by positivity), c₀ * c₂,
    ⟨by positivity, (mul_le_mul hc₀half hc₂1 hc₂.le (by norm_num)).trans_lt (by norm_num)⟩, ?_⟩
  intro U Q u e σ ε hU hB hu he hε hεbar hQ hσ htrap hx0
  clear_value c₂ kmin kmax c₀ CH
  have hε20 : ε ≤ 1 / 20 := hεbar.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεk : ε ≤ c₀ * kmin / 80 := hεbar.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεK : ε ≤ 1 / (20 * (c₀ * kmax)) := hεbar.trans (min_le_right _ _)
  have hc₀ε : c₀ * ε ≤ 1 / 40 := by
    have := mul_le_mul hc₀half hε20 hε.le (by norm_num); linarith
  have hσ' := abs_lt.1 hσ
  have hlow : ∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ + σ) 0 ≤ u y := fun y hy ↦ (htrap y hy).1
  set xbar : E d := (1 / 5 : ℝ) • e with hxbar
  set W := deSilvaBarrier xbar with hW
  set p : E d → ℝ := fun y ↦ ⟪y, e⟫ + σ with hp
  set K := closedBall xbar (3 / 4) with hK
  have hK1 : K ⊆ ball 0 1 := closedBall_fifth_subset he (by norm_num)
  have hcu : ContinuousOn u U := hu.1.1
  -- `u ≤ p + ε` on `{u > 0} ∩ B_1`, hence on its closure.
  have hup_pos : ∀ y ∈ ball (0 : E d) 1, 0 < u y → u y ≤ p y + ε := fun y hy hy0 ↦ by
    have h := (htrap y hy).2
    rcases le_total (⟪y, e⟫ + σ + ε) 0 with h' | h'
    · rw [max_eq_right h'] at h; linarith
    · rw [max_eq_left h'] at h; exact h
  have hup : ∀ y ∈ closure (posSet u U) ∩ ball (0 : E d) 1, u y ≤ p y + ε := by
    rintro y ⟨hyc, hy1⟩
    have hyc' : y ∈ closure (ball (0 : E d) 1 ∩ posSet u U) := isOpen_ball.inter_closure ⟨hy1, hyc⟩
    refine ContinuousWithinAt.closure_le hyc' ((hcu y (hB hy1)).mono fun z hz ↦ hB hz.1)
      (by change ContinuousWithinAt (fun y ↦ ⟪y, e⟫ + σ + ε) _ y; fun_prop) ?_
    rintro z ⟨hz1, hz⟩
    exact hup_pos z hz1 hz.2
  -- Harnack for `p + ε - u ≥ 0` in `B_{1/10}(x̄) ⊆ {u > 0}`.
  have hpos := ball_tenth_subset_posSet he hB hσ hlow
  have huH := IsViscSolution.harmonicOnNhd_posSet hU hu
  have hHar : ∀ y ∈ ball xbar (1 / 20), c₀ * ε ≤ p y + ε - u y := by
    have hfun : (fun y ↦ p y + ε - u y) = (fun y ↦ ⟪y, e⟫ + (σ + ε)) - u := by
      funext z
      change ⟪z, e⟫ + σ + ε - u z = ⟪z, e⟫ + (σ + ε) - u z
      ring
    have hh : HarmonicOnNhd (fun y ↦ p y + ε - u y) (ball xbar (1 / 10)) := fun y hy ↦ by
      rw [hfun]
      exact (harmonicAt_inner_add e (σ + ε) y).sub (huH y (hpos hy))
    have h0 : ∀ y ∈ ball xbar (1 / 10), 0 ≤ p y + ε - u y := fun y hy ↦ by
      have hy1 : y ∈ ball (0 : E d) 1 :=
        closedBall_fifth_subset he (by norm_num : (1 / 10 : ℝ) < 4 / 5)
          (ball_subset_closedBall hy)
      have := hup_pos y hy1 (hpos hy).2
      linarith
    have hx : ε / 2 ≤ p xbar + ε - u xbar := by
      simp only [hp, hxbar, inner_fifth he]; linarith
    intro y hy
    have := harnack_ball_tenth hh h0 hx y hy
    calc c₀ * ε = ε / 2 / CH := by rw [hc₀]; field_simp
      _ ≤ p y + ε - u y := by rw [hCH]; exact this
  -- The comparison function and its minimum on `S = K ∩ closure {u > 0}`.
  set S := K ∩ closure (posSet u U) with hS
  have hxbarS : xbar ∈ S :=
    ⟨mem_closedBall_self (by norm_num), subset_closure (hpos (mem_ball_self (by norm_num)))⟩
  set v : E d → ℝ := fun y ↦ p y + ε + c₀ * ε * (1 - min (W y) 1) with hv
  have hvp : ∀ y, p y + ε ≤ v y := fun y ↦ by
    have : 0 ≤ 1 - min (W y) 1 := by linarith [min_le_right (W y) 1]
    have : 0 ≤ c₀ * ε * (1 - min (W y) 1) := mul_nonneg (mul_pos hc₀pos hε).le this
    simp only [hv]; linarith
  have hcont : ContinuousOn (fun y ↦ v y - u y) S := by
    refine (Continuous.continuousOn ?_).sub (hcu.mono fun y hy ↦ hB (hK1 hy.1))
    have := continuous_deSilvaBarrier xbar
    simp only [hv, hp]; fun_prop
  obtain ⟨xt, hxtS, hmin⟩ :=
    ((isCompact_closedBall xbar (3 / 4)).inter_right isClosed_closure).exists_isMinOn
      ⟨xbar, hxbarS⟩ hcont
  set m := v xt - u xt with hm
  have hmin' : ∀ y ∈ S, m ≤ v y - u y := fun y hy ↦ hmin hy
  have hxtK : xt ∈ K := hxtS.1
  have hxt1 : xt ∈ ball (0 : E d) 1 := hK1 hxtK
  have hupxt := hup xt ⟨hxtS.2, hxt1⟩
  by_cases hmc : c₀ * ε ≤ m
  · intro y hy
    rw [mem_closedBall, dist_zero_right] at hy
    rcases le_or_gt (u y) 0 with hu0 | hu0
    · exact hu0.trans (le_max_right _ _)
    have hyx : ‖y - xbar‖ ≤ 7 / 10 := by
      calc ‖y - xbar‖ ≤ ‖y‖ + ‖xbar‖ := norm_sub_le _ _
        _ ≤ 7 / 10 := by rw [hxbar, norm_fifth he]; linarith
    have hyK : y ∈ K := by rw [hK, mem_closedBall, dist_eq_norm]; linarith
    have hyS : y ∈ S := ⟨hyK, subset_closure ⟨hB (hK1 hyK), hu0⟩⟩
    have h1 := hmin' y hyS
    have h2 : c₂ ≤ min (W y) 1 :=
      le_min (by rw [hc₂_def]; exact le_deSilvaBarrier hd0 hyx) hc₂1
    have h3 : c₀ * ε * c₂ ≤ c₀ * ε * min (W y) 1 :=
      mul_le_mul_of_nonneg_left h2 (mul_pos hc₀pos hε).le
    refine le_max_of_le_left ?_
    simp only [hv, hp] at h1
    linarith
  exfalso
  replace hmc := not_le.1 hmc
  have hxtU : xt ∈ U := hB hxt1
  have hxtK' : ‖xt - xbar‖ ≤ 3 / 4 := by rwa [mem_closedBall, dist_eq_norm] at hxtK
  -- (1) inner ball: excluded by Harnack.
  rcases lt_or_ge ‖xt - xbar‖ (1 / 20) with hin | hout
  · have := hHar xt (by rwa [mem_ball, dist_eq_norm])
    have := hvp xt
    simp only [hm] at hmc; linarith
  -- (2) outer sphere: excluded since the barrier vanishes there.
  rcases eq_or_lt_of_le hxtK' with heq | hlt
  · have hW0 : W xt = 0 := deSilvaBarrier_eq_zero heq
    simp only [hm, hv, hW0] at hmc
    norm_num at hmc
    linarith
  -- (3) open annulus: `φ⁺` touches from above relative to `closure {u > 0} ∩ U`.
  have hWlt : ∀ y, 1 / 25 < ‖y - xbar‖ → min (W y) 1 = W y := fun y hy ↦
    min_eq_left (deSilvaBarrier_lt_one hd0 hy).le
  set φ : E d → ℝ := fun y ↦ 1 * ⟪y, e⟫ + (σ + ε + c₀ * ε - m) + -(c₀ * ε) * W y with hφ
  have hφv : ∀ y, 1 / 25 < ‖y - xbar‖ → φ y = v y - m := fun y hy ↦ by
    simp only [hφ, hv, hp, hWlt y hy]; ring
  have hφs : ContDiff ℝ ∞ φ := by
    have := contDiff_deSilvaBarrier xbar (n := ∞)
    exact ((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).add contDiff_const).add
      (contDiff_const.mul this)
  set N : Set (E d) := ball xbar (3 / 4) ∩ {y | 1 / 25 < ‖y - xbar‖} with hN
  have hNo : IsOpen N :=
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have hxtN : xt ∈ N := ⟨by rwa [mem_ball, dist_eq_norm], show 1 / 25 < ‖xt - xbar‖ by linarith⟩
  have hφxt : φ xt = u xt := by rw [hφv xt hxtN.2, hm]; ring
  have htouch : TouchesAbove (fun y ↦ max (φ y) 0) u (closure (posSet u U) ∩ U) xt := by
    refine ⟨⟨hxtS.2, hxtU⟩, ?_, ?_⟩
    · change max (φ xt) 0 = u xt
      rw [hφxt, max_eq_left (hu.1.2.1 xt hxtU)]
    refine eventually_of_mem (inter_mem_nhdsWithin _ (hNo.mem_nhds hxtN)) ?_
    rintro y ⟨⟨hyc, -⟩, hyN⟩
    have := hmin' y ⟨ball_subset_closedBall hyN.1, hyc⟩
    refine le_max_of_le_left ?_
    rw [hφv y hyN.2]
    linarith
  rcases hu.2.2.2 φ hφs xt htouch with hlap | ⟨hφ0, hgrad⟩
  · rw [hφ, laplacian_mul_inner_add_mul (contDiff_deSilvaBarrier xbar)] at hlap
    have := laplacian_deSilvaBarrier_pos (xbar := xbar) hd0 hxtN.2
    have : 0 < c₀ * ε * Δ (deSilvaBarrier xbar) xt := mul_pos (mul_pos hc₀pos hε) this
    linarith
  · obtain ⟨hk1, hk2⟩ := deSilvaBarrierSlope_mem (xbar := xbar) (z := xt) hd0 hxtK'
    set k := deSilvaBarrierSlope xbar xt with hk
    replace hk1 : kmin ≤ k := by rw [hkmin_def, hkmax_def]; exact hk1
    replace hk2 : k ≤ kmax := by rw [hkmax_def]; exact hk2
    have hgr : ∇ φ xt = (1 : ℝ) • e + (-(c₀ * ε)) • (-k • (xt - xbar)) :=
      (hasGradientAt_mul_inner_add_mul (hasGradientAt_deSilvaBarrier xbar xt) 1 _ _).gradient
    have hgr' : ∇ φ xt = e + (c₀ * ε * k) • (xt - xbar) := by
      rw [hgr, one_smul, smul_smul]; congr 2; ring
    have hte : ⟪e, xt - xbar⟫ = ⟪xt, e⟫ - 1 / 5 := by
      rw [inner_sub_right, real_inner_comm xt e, real_inner_comm xbar e, hxbar, inner_fifth he]
    have hG : ‖∇ φ xt‖ ^ 2 = 1 + 2 * (c₀ * ε * k) * (⟪xt, e⟫ - 1 / 5) +
        (c₀ * ε * k) ^ 2 * ‖xt - xbar‖ ^ 2 := by
      rw [hgr', norm_add_sq_real, he, inner_smul_right, hte, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs]
      ring
    have hWt1 : W xt ≤ 1 := (deSilvaBarrier_lt_one hd0 hxtN.2).le
    have hxte : ⟪xt, e⟫ - 1 / 5 ≤ -(1 / 20) := by
      have h0 : 0 ≤ c₀ * ε * (1 - W xt) := mul_nonneg (mul_pos hc₀pos hε).le (by linarith)
      have hφ0' : v xt - m = 0 := by rw [← hφv xt hxtN.2]; exact hφ0
      have hvx : v xt = ⟪xt, e⟫ + σ + ε + c₀ * ε * (1 - W xt) := by
        simp only [hv, hp, hWlt xt hxtN.2]
      linarith
    have ha : c₀ * ε * k ≤ 1 / 20 := by
      have h1 : c₀ * ε * k ≤ c₀ * ε * kmax := mul_le_mul_of_nonneg_left hk2 (mul_pos hc₀pos hε).le
      have h2 : ε * (20 * (c₀ * kmax)) ≤ 1 := by
        rw [le_div_iff₀ (by positivity)] at hεK; linarith
      have h3 : c₀ * ε * kmax = ε * (20 * (c₀ * kmax)) / 20 := by ring
      linarith
    have hρ : ‖xt - xbar‖ ^ 2 ≤ 1 :=
      (pow_le_pow_left₀ (norm_nonneg _) hxtK' 2).trans (by norm_num)
    exact slope_contra_upper hc₀pos hε hε20 hεk hkmin hk1 ha hxte hρ hG hgrad
      (hQ xt hxt1)

end EllipticBernoulli
