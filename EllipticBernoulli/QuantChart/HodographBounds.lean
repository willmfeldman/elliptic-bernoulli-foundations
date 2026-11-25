/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Field
public import BasicElliptic.Basic.HalfSpace
public import BasicElliptic.Defs.Div
import EllipticBernoulli.Hodograph.Boundary
import EllipticBernoulli.Hodograph.Equation
import EllipticBernoulli.QuantChart.FieldBounds
import BasicElliptic.Div.Quasilinear.Main
import BasicElliptic.Div.Boundary.StrongToWeak
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Second and third derivatives of the hodograph transform

`exists_hodograph_derivative_bounds`: there are `η₀ > 0` and `C ≥ 0` (depending on `d` only)
with the following property. Let `w` be `C¹` on the half ball `B_r⁺ = halfBall e 0 r`, `C²`
inside, with `|∇w - e| ≤ η ≤ η₀`, solving the hodograph equation `div Φ(∇w) = 0` inside with the
conormal condition `Φ(∇w) · e = 0` on the flat part (`Φ = field e`). Then `w` is smooth at every
point `z` of `B_{r/2} ∩ {z · e > 0}`, and there
`‖D²w(z)‖ ≤ C η / r` and `‖D³w(z)‖ ≤ C η / r²`.

## Proof

For such `z`, apply the scaled third-order conormal estimate on `halfBall e z (r/2) ⊆ B_r⁺` to
`w̃ = w - (· · e)`. It solves the conormal problem for the shifted flux `Φ̃(p) = Φ(p + e)`, which
is elliptic, symmetric and has `C³` bounds on `B_{1/16}` uniform in `e`
(`exists_bound_iteratedFDeriv_field`), and `|∇w̃| ≤ η`. The oscillation of `w̃` on a half ball of
radius `r/2` is at most `η r`, by the mean value theorem. The half ball is a neighbourhood of `z`,
so the derivatives within it are the derivatives of `w`, of order `≥ 2`.

The scaled estimate is `BasicElliptic.Div.quasilinear_conormal_estimate_three`.
-/

open Set Filter Topology Metric InnerProductSpace MeasureTheory
open scoped ContDiff Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli

open Hodograph BasicElliptic

variable {d : ℕ}

/-- Iterated derivatives of order `≥ 2` ignore a linear term. -/
private theorem iteratedFDeriv_sub_inner {w : E d → ℝ} {e z : E d} {k : ℕ} (hk : 2 ≤ k)
    (hw : ContDiffAt ℝ k w z) :
    iteratedFDeriv ℝ k (fun y ↦ w y - ⟪y, e⟫) z = iteratedFDeriv ℝ k w z := by
  have hfd : fderiv ℝ (fun y : E d ↦ innerSL ℝ e y) = fun _ ↦ innerSL ℝ e := by
    funext y; exact (innerSL ℝ e).fderiv
  have h0 : iteratedFDeriv ℝ k (fun y : E d ↦ innerSL ℝ e y) z = 0 := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, hfd,
      iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]
  rw [show (fun y ↦ w y - ⟪y, e⟫) = fun y ↦ w y - innerSL ℝ e y by
      funext y; rw [innerSL_apply_apply, real_inner_comm]]
  change iteratedFDeriv ℝ k (w - (innerSL ℝ e : E d → ℝ)) z = _
  rw [iteratedFDeriv_sub_apply hw (innerSL ℝ e).contDiff.contDiffAt, h0, sub_zero]

/-- The half ball `halfBall e z s` has unique derivatives. -/
private theorem uniqueDiffOn_halfBall {e z : E d} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s)
    (hz : 0 ≤ ⟪z, e⟫) : UniqueDiffOn ℝ (halfBall e z s) := by
  have hconv : Convex ℝ (halfBall e z s) :=
    (convex_closedBall z s).inter (convex_halfSpace_ge (f := fun y : E d ↦ ⟪y, e⟫)
      ⟨fun x y ↦ inner_add_left x y e, fun c x ↦ real_inner_smul_left x e c⟩ 0)
  refine uniqueDiffOn_convex hconv ⟨z + (s / 2) • e, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  have hopen : IsOpen (ball z s ∩ openHalfSpace e) :=
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨?_, ?_⟩) fun y hy ↦
    ⟨ball_subset_closedBall hy.1, (show 0 ≤ ⟪y, e⟫ from le_of_lt hy.2)⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_of_nonneg (by positivity)]
    linarith
  · change 0 < ⟪z + (s / 2) • e, e⟫
    rw [inner_add_left, real_inner_smul_left, inner_self_of_norm he]
    nlinarith

/-- **Second and third derivatives of the hodograph transform.** -/
theorem exists_hodograph_derivative_bounds : ∃ η₀ > 0, ∃ C ≥ 0,
    ∀ {e : E d} {r : ℝ} {w : E d → ℝ} {η : ℝ}, ‖e‖ = 1 → 0 < r → 0 ≤ η → η ≤ η₀ →
    ContDiffOn ℝ 1 w (halfBall e 0 r) → ContDiffOn ℝ 2 w (ball 0 r ∩ openHalfSpace e) →
    (∀ z ∈ halfBall e 0 r, ‖gradientWithin w (halfBall e 0 r) z - e‖ ≤ η) →
    (∀ z ∈ ball 0 r ∩ openHalfSpace e, divergence (fun p ↦ field e (∇ w p)) z = 0) →
    (∀ z ∈ ball 0 r ∩ flatPart e, ⟪field e (gradientWithin w (halfBall e 0 r) z), e⟫ = 0) →
    ∀ z ∈ ball 0 (r / 2) ∩ openHalfSpace e, ContDiffAt ℝ ∞ w z ∧
      ‖iteratedFDeriv ℝ 2 w z‖ ≤ C * η / r ∧ ‖iteratedFDeriv ℝ 3 w z‖ ≤ C * η / r ^ 2 := by
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv_field (d := d)
  have hS0 := BasicElliptic.Div.quasilinear_conormal_estimate_three (E d)
  unfold BasicElliptic.Div.QuasilinearConormalEstimateThreeStatement at hS0
  obtain ⟨ηs, hηs, Cs, hS⟩ := hS0 (1 / 2) M (1 / 16) (by norm_num) (by norm_num)
  obtain ⟨ηr, hηr, hreg⟩ := hodograph_regularity (d := d)
  refine ⟨min ηs (min ηr (1 / 16)), lt_min hηs (lt_min hηr (by norm_num)), 8 * |Cs|,
    by positivity, ?_⟩
  intro e r w η he hr hη0 hη h1 h2 hgrad hdiv hbc z hz
  have hηs' : η ≤ ηs := hη.trans (min_le_left _ _)
  have hηr' : η ≤ ηr := hη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη16 : η ≤ 1 / 16 := hη.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hzt : 0 < ⟪z, e⟫ := hz.2
  have hzn : ‖z‖ < r / 2 := by simpa using hz.1
  -- smoothness of `w` at `z`
  have hsmooth := hreg he hr h1 h2 (fun y hy ↦ (hgrad y hy).trans hηr') hdiv hbc
  have hOo : IsOpen (ball (0 : E d) (r / 2) ∩ openHalfSpace e) :=
    isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have hwz : ContDiffAt ℝ ∞ w z :=
    (hsmooth.mono fun y (hy : y ∈ ball (0 : E d) (r / 2) ∩ openHalfSpace e) ↦
      ⟨ball_subset_closedBall hy.1, (show 0 ≤ ⟪y, e⟫ from le_of_lt hy.2)⟩).contDiffAt
      (hOo.mem_nhds hz)
  refine ⟨hwz, ?_⟩
  -- the small half ball `s` around `z`
  set s := halfBall e z (r / 2) with hs
  have hsub : s ⊆ halfBall e 0 r := fun y hy ↦ by
    refine ⟨?_, hy.2⟩
    have h1' : ‖y - z‖ ≤ r / 2 := by simpa [dist_eq_norm] using hy.1
    rw [mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' y z
    linarith
  have hzs : z ∈ s := ⟨mem_closedBall_self (by positivity), (show 0 ≤ ⟪z, e⟫ from hzt.le)⟩
  have hsn : s ∈ 𝓝 z := by
    refine Filter.mem_of_superset (ball_mem_nhds z (lt_min (by positivity : 0 < r / 2) hzt))
      fun y hy ↦ ?_
    rw [mem_ball, dist_eq_norm] at hy
    have hm1 := min_le_left (r / 2) ⟪z, e⟫
    refine ⟨ball_subset_closedBall (mem_ball.2 (by rw [dist_eq_norm]; linarith)), ?_⟩
    change 0 ≤ ⟪y, e⟫
    have h3 : ⟪y, e⟫ = ⟪z, e⟫ + ⟪y - z, e⟫ := by rw [inner_sub_left]; ring
    have h4 := abs_real_inner_le_norm (y - z) e
    rw [he, mul_one] at h4
    linarith [neg_abs_le ⟪y - z, e⟫, min_le_right (r / 2) ⟪z, e⟫]
  have hUs : UniqueDiffOn ℝ s := uniqueDiffOn_halfBall he (by positivity) hzt.le
  have hd1 : DifferentiableOn ℝ w (halfBall e 0 r) := h1.differentiableOn (by norm_num)
  have hgw : ∀ y ∈ s, gradientWithin w s y = gradientWithin w (halfBall e 0 r) y := fun y hy ↦ by
    rw [gradientWithin, gradientWithin, fderivWithin_subset hsub (hUs y hy) (hd1 y (hsub hy))]
  have hsub2 : ball z (r / 2) ∩ openHalfSpace e ⊆ ball 0 r ∩ openHalfSpace e := fun y hy ↦
    ⟨by
      have := hsub ⟨ball_subset_closedBall hy.1, (show 0 ≤ ⟪y, e⟫ from le_of_lt hy.2)⟩
      have hyz : ‖y - z‖ < r / 2 := by simpa [dist_eq_norm] using hy.1
      rw [mem_ball, dist_zero_right]
      have := norm_le_norm_add_norm_sub' y z
      linarith, hy.2⟩
  -- the weak form on `s`
  have hweak : Div.IsQuasilinearConormalSolOn e (field e) z (r / 2) w := by
    refine Div.isQuasilinearConormalSolOn_of_strong (E d) e z (r / 2) (field e) (ball e (1 / 8)) w
      he (by positivity) isOpen_ball (h1.mono hsub) (h2.mono hsub2)
      ((contDiffOn_field he).of_le (by simp)) (fun y hy ↦ ?_) (fun y hy ↦ hdiv y (hsub2 hy))
      (fun y hy ↦ ?_)
    · rw [hgw y hy, mem_ball, dist_eq_norm]
      linarith [hgrad y (hsub hy)]
    · have hys : y ∈ s := ⟨ball_subset_closedBall hy.1, (show 0 ≤ ⟪y, e⟫ from hy.2.symm.le)⟩
      rw [hgw y hys]
      refine hbc y ⟨?_, hy.2⟩
      have := hsub hys
      have hyz : ‖y - z‖ < r / 2 := by simpa [dist_eq_norm] using hy.1
      rw [mem_ball, dist_zero_right]
      have := norm_le_norm_add_norm_sub' y z
      linarith
  -- the shifted problem
  set wt : E d → ℝ := fun y ↦ w y - ⟪y, e⟫ with hwt
  set Φt : E d → E d := fun p ↦ field e (p + e) with hΦt
  have hlin : ∀ y, HasFDerivAt (fun y : E d ↦ ⟪y, e⟫) (toDual ℝ (E d) e) y := fun y ↦ by
    have : (fun y : E d ↦ ⟪y, e⟫) = fun y ↦ toDual ℝ (E d) e y := by
      funext y; rw [toDual_apply_apply, real_inner_comm]
    rw [this]; exact (toDual ℝ (E d) e).hasFDerivAt
  have hgwt : ∀ y ∈ s, gradientWithin wt s y = gradientWithin w s y - e := fun y hy ↦ by
    have hw' : HasFDerivWithinAt w (fderivWithin ℝ w s y) s y :=
      ((hd1 y (hsub hy)).mono hsub).hasFDerivWithinAt
    have hh : HasFDerivWithinAt wt (fderivWithin ℝ w s y - toDual ℝ (E d) e) s y :=
      hw'.sub (hlin y).hasFDerivWithinAt
    have := hh.fderivWithin (hUs y hy)
    rw [gradientWithin, gradientWithin, this, map_sub, LinearIsometryEquiv.symm_apply_apply]
  have hsc : IsClosed s := isClosed_closedBall.inter (isClosed_le continuous_const (by fun_prop))
  have hweak' : Div.IsQuasilinearConormalSolOn e Φt z (r / 2) wt := by
    refine ⟨(h1.mono hsub).sub (contDiff_id.inner ℝ contDiff_const).contDiffOn, fun φ hφ ↦ ?_⟩
    rw [← hweak.2 φ hφ]
    refine setIntegral_congr_fun hsc.measurableSet fun y hy ↦ ?_
    rw [show gradientWithin wt (halfBall e z (r / 2)) y =
      gradientWithin w (halfBall e z (r / 2)) y - e from hgwt y hy, hΦt]
    simp only [sub_add_cancel]
  have hmem : ∀ p ∈ ball (0 : E d) (1 / 16), p + e ∈ ball e (1 / 8) := fun p hp ↦ by
    rw [mem_ball, dist_zero_right] at hp
    rw [mem_ball, dist_eq_norm, add_sub_cancel_right]; linarith
  have hfd : ∀ p, fderiv ℝ Φt p = fderiv ℝ (field e) (p + e) := fun p ↦
    fderiv_comp_add_right (f := field e) e
  have hΦ3 : ContDiffOn ℝ 3 Φt (ball 0 (1 / 16)) :=
    ((contDiffOn_field he).comp (contDiff_id.add contDiff_const).contDiffOn
      (fun p hp ↦ hmem p hp)).of_le (by simp)
  obtain ⟨-, hk2, hk3⟩ := hS e Φt he hΦ3
    (fun p hp ξ ↦ by rw [hfd]; exact half_mul_norm_sq_le_inner_fderiv_field he (hmem p hp) ξ)
    (fun p hp ↦ by
      rw [hfd]
      exact isSymmetric_fderiv_field he (by linarith [(inner_e_of_mem_ball he (hmem p hp)).1]))
    (fun p hp ↦ by
      have hp' : p ∈ closedBall (0 : E d) (1 / 16) := ball_subset_closedBall hp
      refine ⟨?_, hM e he p hp' 2 (by norm_num), hM e he p hp' 3 le_rfl⟩
      rw [← norm_iteratedFDeriv_one]; exact hM e he p hp' 1 (by norm_num))
    z (r / 2) wt (by positivity) (by linarith) hweak' (fun y hy ↦ by
      rw [hgwt y hy, hgw y hy]; exact (hgrad y (hsub hy)).trans hηs')
  -- the oscillation of `wt` on `s`
  have hdwt : DifferentiableOn ℝ wt s := fun y hy ↦
    ((hd1 y (hsub hy)).mono hsub).sub (hlin y).differentiableAt.differentiableWithinAt
  have hconv : Convex ℝ s :=
    (convex_closedBall z (r / 2)).inter (convex_halfSpace_ge (f := fun y : E d ↦ ⟪y, e⟫)
      ⟨fun x y ↦ inner_add_left x y e, fun c x ↦ real_inner_smul_left x e c⟩ 0)
  have hlip : ∀ y ∈ s, |wt y - wt z| ≤ η * (r / 2) := fun y hy ↦ by
    have := Convex.norm_image_sub_le_of_norm_fderivWithin_le hdwt (C := η) (fun x hx ↦ by
      have h := hgwt x hx
      rw [hgw x hx] at h
      have hn : ‖fderivWithin ℝ wt s x‖ = ‖gradientWithin wt s x‖ := by
        rw [gradientWithin, LinearIsometryEquiv.norm_map]
      rw [hn, h]; exact hgrad x (hsub hx)) hconv hzs hy
    rw [Real.norm_eq_abs] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hη0)
    simpa [dist_eq_norm] using hy.1
  have hosc : regionOsc wt s ≤ η * r := by
    rw [regionOsc_def]
    have hne : (wt '' s).Nonempty := ⟨wt z, z, hzs, rfl⟩
    have hup : sSup (wt '' s) ≤ wt z + η * (r / 2) := csSup_le hne fun b ⟨y, hy, hb⟩ ↦ by
      rw [← hb]; linarith [(abs_le.1 (hlip y hy)).2]
    have hlo : wt z - η * (r / 2) ≤ sInf (wt '' s) := le_csInf hne fun b ⟨y, hy, hb⟩ ↦ by
      rw [← hb]; linarith [(abs_le.1 (hlip y hy)).1]
    linarith
  have hosc0 : 0 ≤ regionOsc wt s := by
    rw [regionOsc_def]
    have hne : (wt '' s).Nonempty := ⟨wt z, z, hzs, rfl⟩
    have hb : BddAbove (wt '' s) := ⟨wt z + η * (r / 2), fun b ⟨y, hy, hb⟩ ↦ by
      rw [← hb]; linarith [(abs_le.1 (hlip y hy)).2]⟩
    have hb' : BddBelow (wt '' s) := ⟨wt z - η * (r / 2), fun b ⟨y, hy, hb⟩ ↦ by
      rw [← hb]; linarith [(abs_le.1 (hlip y hy)).1]⟩
    linarith [csInf_le hb' ⟨z, hzs, rfl⟩, le_csSup hb ⟨z, hzs, rfl⟩]
  have hCosc : Cs * regionOsc wt s ≤ |Cs| * (η * r) :=
    (mul_le_mul_of_nonneg_right (le_abs_self Cs) hosc0).trans
      (mul_le_mul_of_nonneg_left hosc (abs_nonneg Cs))
  -- derivatives within `s` at `z` are the derivatives of `w`
  have hwtz : ∀ k : ℕ, ContDiffAt ℝ k wt z := fun k ↦
    ((hwz.of_le (by exact_mod_cast le_top)).sub (contDiff_id.inner ℝ contDiff_const).contDiffAt)
  have hD : ∀ k : ℕ, 2 ≤ k → ‖iteratedFDerivWithin ℝ k wt s z‖ = ‖iteratedFDeriv ℝ k w z‖ :=
    fun k hk ↦ by
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hUs (hwtz k) hzs,
        iteratedFDeriv_sub_inner hk (hwz.of_le (by exact_mod_cast le_top))]
  have hD2 : ‖fderivWithin ℝ (fderivWithin ℝ wt s) s z‖ = ‖iteratedFDeriv ℝ 2 w z‖ := by
    rw [← norm_iteratedFDerivWithin_one _ (hUs z hzs),
      norm_iteratedFDerivWithin_fderivWithin hUs hzs, hD 2 le_rfl]
  rw [hD2] at hk2
  rw [hD 3 (by norm_num)] at hk3
  have hr2 : 0 < (r / 2) ^ 2 := by positivity
  have hr3 : 0 < (r / 2) ^ 3 := by positivity
  constructor
  · rw [le_div_iff₀ hr]
    have := hk2.trans hCosc
    nlinarith [norm_nonneg (iteratedFDeriv ℝ 2 w z), abs_nonneg Cs]
  · rw [le_div_iff₀ (by positivity)]
    have := hk3.trans hCosc
    nlinarith [norm_nonneg (iteratedFDeriv ℝ 3 w z), abs_nonneg Cs]

end EllipticBernoulli
