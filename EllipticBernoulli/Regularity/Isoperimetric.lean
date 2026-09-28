/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.DeGiorgi
public import EllipticBernoulli.Sobolev.Mollify
public import EllipticBernoulli.Sobolev.ZeroExtension
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# The De Giorgi isoperimetric lemma on balls

For `g` with weak gradient `G` near the closed ball `B̄ = B̄_ρ(z)`
(`lintegral_lintegral_enorm_sub_le`):
`∫_B ∫_B |g(x) - g(y)| dy dx ≤ 2ρ 2ᵈ |B| ∫_B |G|`,
and hence (`measure_zero_mul_lintegral_le`) `|{g = 0} ∩ B| ∫_B |g| ≤ 2ρ 2ᵈ |B| ∫_B |G|`.
This is the interior replacement for the boundary Poincaré inequality (`BoundaryPoincare.lean`)
in the De Giorgi measure-shrinking step.

## Proof

For `φ ∈ C¹` (`lintegral_lintegral_enorm_sub_le_of_contDiff`):
`|φ(x) - φ(y)| ≤ |x - y| ∫₀¹ |∇φ((1-t)x + ty)| dt` with `|x - y| ≤ 2ρ`, and `(1-t)x + ty ∈ B` by
convexity. By Tonelli, for each `t` the double integral `∫_B∫_B |∇φ|((1-t)x + ty)` is at most
`2ᵈ |B| ∫_B |∇φ|`: for `t ≥ 1/2` integrate in `y` first (the map `y ↦ (1-t)x + ty` has Jacobian
`tᵈ ≥ 2⁻ᵈ`), for `t < 1/2` integrate in `x` first. No polar coordinates are needed.

For `g` with a weak gradient: multiply by a cutoff equal to `1` on `B̄`, extend by zero, mollify
(`Sobolev/Mollify.lean`), use `|∇(h ⋆ ψ)| ≤ |H| ⋆ ψ`, and pass to the limit in `L¹`.
-/

open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped ContDiff ENNReal NNReal Gradient Convolution

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Smooth functions -/

/-- **Fundamental theorem of calculus on a segment**, in `ℝ≥0∞` form. -/
theorem enorm_sub_le_lintegral_segment {φ : E d → ℝ} (hφ : ContDiff ℝ 1 φ) (x y : E d) :
    ‖φ y - φ x‖ₑ ≤ ‖y - x‖ₑ * ∫⁻ t in Ioc (0 : ℝ) 1, ‖fderiv ℝ φ (x + t • (y - x))‖ₑ := by
  set γ : ℝ → ℝ := fun t ↦ φ (x + t • (y - x)) with hγ
  have hderiv : ∀ t, HasDerivAt γ (fderiv ℝ φ (x + t • (y - x)) (y - x)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ ↦ x + t • (y - x)) (y - x) t := by
      simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    exact ((hφ.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t h1
  have hcont : Continuous fun t : ℝ ↦ fderiv ℝ φ (x + t • (y - x)) (y - x) :=
    ((hφ.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable 0 1)
  have e : γ 1 - γ 0 = φ y - φ x := by simp [hγ]
  rw [← e, ← hFTC, intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  refine lintegral_mono fun t ↦ ?_
  rw [mul_comm]
  exact ContinuousLinearMap.le_opENorm _ _

/-- Dilation of a lintegral: `∫⁻ g(a + t y) dy = |t|⁻ᵈ ∫⁻ g`. -/
theorem lintegral_comp_add_smul {g : E d → ℝ≥0∞} (hg : Measurable g) (a : E d) {t : ℝ}
    (ht : t ≠ 0) :
    ∫⁻ y, g (a + t • y) = ENNReal.ofReal (|t ^ d|⁻¹) * ∫⁻ y, g y := by
  have hmeas : Measurable fun y : E d ↦ g (a + y) := hg.comp (measurable_const_add a)
  have h1 : ∫⁻ y, g (a + t • y) = ∫⁻ y, g (a + y) ∂(Measure.map (t • ·) volume) := by
    rw [lintegral_map hmeas (measurable_const_smul t)]
  rw [h1, Measure.map_addHaar_smul volume ht, lintegral_smul_measure, finrank_euclideanSpace_fin,
    lintegral_add_left_eq_self (fun y ↦ g y) a, smul_eq_mul, abs_inv]

/-- For `1/2 ≤ t`, `∫⁻ g(a + t y) dy ≤ 2ᵈ ∫⁻ g`. -/
theorem lintegral_comp_add_smul_le {g : E d → ℝ≥0∞} (hg : Measurable g) (a : E d) {t : ℝ}
    (ht : 1 / 2 ≤ t) :
    ∫⁻ y, g (a + t • y) ≤ 2 ^ d * ∫⁻ y, g y := by
  have ht0 : 0 < t := by linarith
  rw [lintegral_comp_add_smul hg a ht0.ne']
  gcongr
  rw [abs_of_pos (pow_pos ht0 d), ← inv_pow]
  have : t⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
  calc ENNReal.ofReal (t⁻¹ ^ d) ≤ ENNReal.ofReal (2 ^ d) :=
        ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (inv_nonneg.2 ht0.le) this d)
    _ = 2 ^ d := by rw [ENNReal.ofReal_pow (by norm_num)]; simp

/-- The inner double integral at a fixed `t ∈ [0, 1]`. -/
theorem lintegral_lintegral_comp_convex_le {g : E d → ℝ≥0∞} (hg : Measurable g) (S : Set (E d))
    (t : ℝ) :
    ∫⁻ x in S, ∫⁻ y in S, g ((1 - t) • x + t • y) ≤ 2 ^ d * volume S * ∫⁻ y, g y := by
  have hF : Measurable (Function.uncurry fun x y : E d ↦ g ((1 - t) • x + t • y)) := by
    change Measurable fun p : E d × E d ↦ g ((1 - t) • p.1 + t • p.2)
    exact hg.comp ((continuous_fst.const_smul _).add (continuous_snd.const_smul _)).measurable
  rcases le_or_gt (1 / 2) t with h | h
  · calc ∫⁻ x in S, ∫⁻ y in S, g ((1 - t) • x + t • y)
        ≤ ∫⁻ x in S, 2 ^ d * ∫⁻ y, g y := by
          refine lintegral_mono fun x ↦ ?_
          exact (setLIntegral_le_lintegral _ _).trans (lintegral_comp_add_smul_le hg _ h)
      _ = 2 ^ d * volume S * ∫⁻ y, g y := by
          rw [setLIntegral_const]; ring
  · rw [lintegral_lintegral_swap hF.aemeasurable]
    calc ∫⁻ y in S, ∫⁻ x in S, g ((1 - t) • x + t • y)
        ≤ ∫⁻ y in S, 2 ^ d * ∫⁻ y, g y := by
          refine lintegral_mono fun y ↦ ?_
          refine (setLIntegral_le_lintegral _ _).trans ?_
          have := lintegral_comp_add_smul_le hg (t • y) (t := 1 - t) (by linarith)
          simpa only [add_comm] using this
      _ = 2 ^ d * volume S * ∫⁻ y, g y := by
          rw [setLIntegral_const]; ring

/-- **The double-integral Poincaré inequality for `C¹` functions** on a ball:
`∫_B ∫_B |φ(x) - φ(y)| ≤ 2ρ 2ᵈ |B| ∫_B |Dφ|`. -/
theorem lintegral_lintegral_enorm_sub_le_of_contDiff {φ : E d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (z : E d) (ρ : ℝ) :
    ∫⁻ x in ball z ρ, ∫⁻ y in ball z ρ, ‖φ x - φ y‖ₑ ≤
      ENNReal.ofReal (2 * ρ) * (2 ^ d * volume (ball z ρ)) *
        ∫⁻ x in ball z ρ, ‖fderiv ℝ φ x‖ₑ := by
  set B := ball z ρ with hBdef
  set g : E d → ℝ≥0∞ := B.indicator fun p ↦ ‖fderiv ℝ φ p‖ₑ with hgdef
  have hg : Measurable g :=
    ((hφ.continuous_fderiv one_ne_zero).measurable.enorm).indicator measurableSet_ball
  set F : E d → E d → ℝ → ℝ≥0∞ := fun x y t ↦ g ((1 - t) • x + t • y) with hFdef
  have hFm : Measurable fun p : (E d × E d) × ℝ ↦ F p.1.1 p.1.2 p.2 := by
    change Measurable fun p : (E d × E d) × ℝ ↦ g ((1 - p.2) • p.1.1 + p.2 • p.1.2)
    exact hg.comp (((continuous_const.sub continuous_snd).smul
      (continuous_fst.comp continuous_fst)).add
      (continuous_snd.smul (continuous_snd.comp continuous_fst))).measurable
  clear_value F g
  -- pointwise
  have hpt : ∀ x ∈ B, ∀ y ∈ B,
      ‖φ x - φ y‖ₑ ≤ ENNReal.ofReal (2 * ρ) * ∫⁻ t in Ioc (0 : ℝ) 1, F x y t := by
    intro x hx y hy
    rw [enorm_sub_rev]
    refine (enorm_sub_le_lintegral_segment hφ x y).trans ?_
    gcongr ?_ * ?_
    · rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← dist_eq_norm]
      have := dist_triangle y z x
      rw [mem_ball] at hx hy
      rw [dist_comm z x] at this
      linarith
    · refine le_of_eq (setLIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_)
      have hmem : (1 - t) • x + t • y ∈ B :=
        convex_ball z ρ hx hy (by linarith [ht.2]) ht.1.le (by ring)
      have e : x + t • (y - x) = (1 - t) • x + t • y := by
        rw [smul_sub, sub_smul, one_smul]; abel
      simp only [hFdef, hgdef, indicator_of_mem hmem, e]
  -- integrate and swap
  have h1 : ∫⁻ x in B, ∫⁻ y in B, ‖φ x - φ y‖ₑ ≤
      ∫⁻ x in B, ∫⁻ y in B, ENNReal.ofReal (2 * ρ) * ∫⁻ t in Ioc (0 : ℝ) 1, F x y t := by
    refine setLIntegral_mono' measurableSet_ball fun x hx ↦ ?_
    exact setLIntegral_mono' measurableSet_ball fun y hy ↦ hpt x hx y hy
  have h2 : ∀ x, ∫⁻ y in B, ∫⁻ t in Ioc (0 : ℝ) 1, F x y t =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in B, F x y t := fun x ↦
    lintegral_lintegral_swap (by
      have : Measurable fun p : E d × ℝ ↦ F x p.1 p.2 :=
        hFm.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
      exact this.aemeasurable)
  have hGm : Measurable fun p : E d × ℝ ↦ ∫⁻ y in B, F p.1 y p.2 := by
    have : Measurable fun q : (E d × ℝ) × E d ↦ F q.1.1 q.2 q.1.2 :=
      hFm.comp (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
        (measurable_snd.comp measurable_fst))
    exact this.lintegral_prod_right'
  have h3 : ∫⁻ x in B, ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in B, F x y t =
      ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in B, ∫⁻ y in B, F x y t :=
    lintegral_lintegral_swap hGm.aemeasurable
  have h4 : ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in B, ∫⁻ y in B, F x y t ≤
      ∫⁻ _t in Ioc (0 : ℝ) 1, 2 ^ d * volume B * ∫⁻ y, g y :=
    setLIntegral_mono' measurableSet_Ioc fun t _ ↦ by
      simpa only [hFdef] using lintegral_lintegral_comp_convex_le hg B t
  have hg' : ∫⁻ y, g y = ∫⁻ x in B, ‖fderiv ℝ φ x‖ₑ := by
    rw [hgdef]; exact lintegral_indicator measurableSet_ball _
  calc ∫⁻ x in B, ∫⁻ y in B, ‖φ x - φ y‖ₑ
      ≤ ∫⁻ x in B, ∫⁻ y in B, ENNReal.ofReal (2 * ρ) * ∫⁻ t in Ioc (0 : ℝ) 1, F x y t := h1
    _ = ENNReal.ofReal (2 * ρ) * ∫⁻ x in B, ∫⁻ y in B, ∫⁻ t in Ioc (0 : ℝ) 1, F x y t := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1; funext x
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal (2 * ρ) * ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ x in B, ∫⁻ y in B, F x y t := by
        simp_rw [h2]; rw [h3]
    _ ≤ ENNReal.ofReal (2 * ρ) * ∫⁻ _t in Ioc (0 : ℝ) 1, 2 ^ d * volume B * ∫⁻ y, g y := by
        gcongr
    _ = ENNReal.ofReal (2 * ρ) * (2 ^ d * volume B) * ∫⁻ x in B, ‖fderiv ℝ φ x‖ₑ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one, hg']
        ring

/-! ### Functions with a weak gradient -/

/-- The gradient of a mollification is dominated by the mollification of `|H|`. -/
theorem norm_fderiv_convolution_le {h : E d → ℝ} {H : E d → E d}
    (hw : HasWeakGradient univ h H) (hh : Integrable h) (hH : Integrable H)
    (ψ : ContDiffBump (0 : E d)) (x : E d) :
    ‖fderiv ℝ (h ⋆[lsmul ℝ ℝ, volume] ψ.normed volume) x‖ ≤
      ((fun y ↦ ‖H y‖) ⋆[lsmul ℝ ℝ, volume] ψ.normed volume) x := by
  have hwhole : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ univ →
      ∀ v : E d, ∫ x, h x * fderiv ℝ φ x v = -∫ x, inner ℝ (H x) v * φ x :=
    fun φ h1 h2 h3 v ↦ hw.integral_eq h1 h2 h3 v
  have hK : 0 ≤ ((fun y ↦ ‖H y‖) ⋆[lsmul ℝ ℝ, volume] ψ.normed volume) x := by
    rw [convolution_def]
    exact integral_nonneg fun t ↦ by
      simp only [lsmul_apply, smul_eq_mul]
      exact mul_nonneg (norm_nonneg _) (ψ.nonneg_normed (μ := volume) _)
  have hex := ψ.hasCompactSupport_normed.convolutionExists_right (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    hH.norm.locallyIntegrable (ψ.contDiff_normed (μ := volume) (n := 0)).continuous x
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun v ↦ ?_
  have hder := fderiv_convolution_indicator_eq MeasurableSet.univ hh.integrableOn hwhole ψ v
    (subset_univ (closedBall x ψ.rOut))
  rw [indicator_univ, indicator_univ] at hder
  rw [hder, convolution_def, convolution_def, ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans
    (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) ?_ (ae_of_all _ fun t ↦ ?_))
  · exact hex.mul_const _
  · simp only [lsmul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (ψ.nonneg_normed _)]
    have := abs_real_inner_le_norm (H t) v
    have h0 := ψ.nonneg_normed (μ := volume) (x - t)
    nlinarith

/-- Pointwise: `ofReal a ≤ ofReal b + ‖a - b‖ₑ`. -/
theorem ofReal_le_add_enorm_sub (a b : ℝ) (hb : 0 ≤ b) :
    ENNReal.ofReal a ≤ ENNReal.ofReal b + ‖a - b‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add hb (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (a - b)])

/-- **The double-integral Poincaré inequality on a ball** for a function with a weak gradient
near the closed ball: `∫_B ∫_B |g(x) - g(y)| ≤ 2ρ 2ᵈ |B| ∫_B |G|`. -/
theorem lintegral_lintegral_enorm_sub_le {U : Set (E d)} (hU : IsOpen U) {g : E d → ℝ}
    {G : E d → E d} (hw : HasWeakGradient U g G) {z : E d} {ρ : ℝ} (hρ : 0 < ρ)
    (hzU : closedBall z ρ ⊆ U) :
    ∫⁻ x in ball z ρ, ∫⁻ y in ball z ρ, ‖g x - g y‖ₑ ≤
      ENNReal.ofReal (2 * ρ) * (2 ^ d * volume (ball z ρ)) * ∫⁻ x in ball z ρ, ‖G x‖ₑ := by
  set B := ball z ρ with hBdef
  -- a cutoff equal to `1` on `B̄`
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall z ρ).exists_cthickening_subset_open hU hzU
  rw [cthickening_closedBall hδ.le hρ.le, add_comm] at hδU
  obtain ⟨χ, hχ, hχ01, hχ1, hχ0, -, -, -⟩ :=
    exists_cutoff z hρ.le (show ρ < ρ + δ / 2 by linarith)
  set h : E d → ℝ := fun x ↦ χ x * g x with hhdef
  set H : E d → E d := fun x ↦ χ x • G x + g x • ∇ χ x with hHdef
  have hwU : HasWeakGradient U h H := hw.mul_smooth hU hχ
  have hwu : HasWeakGradient univ h H :=
    hwU.univ_of_vanish (by positivity) (show ρ + δ / 2 < ρ + δ by linarith) hδU
      (fun x hx ↦ by simp [hhdef, (hχ0 x hx).1]) (fun x hx ↦ by
        simp [hHdef, (hχ0 x hx).1, (hχ0 x hx).2])
  have hc : IsCompact (closedBall z (ρ + δ)) := isCompact_closedBall _ _
  have hsub : ball z (ρ + δ / 2) ⊆ closedBall z (ρ + δ) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hhi : Integrable h := by
    refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1
      (hwU.1.integrableOn_compact_subset hδU hc)
    by_contra hx'
    exact hx (by simp [hhdef, (hχ0 x fun h' ↦ hx' (hsub h')).1])
  have hHi : Integrable H := by
    refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1
      (hwU.2.1.integrableOn_compact_subset hδU hc)
    by_contra hx'
    have := hχ0 x fun h' ↦ hx' (hsub h')
    exact hx (by simp [hHdef, this.1, this.2])
  -- on `B`, `h = g` and `H = G`
  have hχB : ∀ x ∈ closedBall z ρ, χ x = 1 := hχ1
  have hhB : ∀ x ∈ B, h x = g x := fun x hx ↦ by
    simp [hhdef, hχB x (ball_subset_closedBall hx)]
  have hHB : ∀ x ∈ B, H x = G x := fun x hx ↦ by
    have h1 := hχB x (ball_subset_closedBall hx)
    have h2 : ∇ χ x = 0 := gradient_eq_zero_of_eq_one (fun y ↦ (hχ01 y).2) h1
    simp [hHdef, h1, h2]
  -- mollifiers
  set ψ : ℕ → ContDiffBump (0 : E d) := fun n ↦
    ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hψdef
  have hψ : Tendsto (fun n ↦ (ψ n).rOut) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ ↦ (2 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h1 := tendsto_natCast_atTop_atTop (R := ℝ)
      have h2 : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 h1
      exact tendsto_const_nhds.div_atTop h2
    exact this
  set hn : ℕ → E d → ℝ := fun n ↦ h ⋆[lsmul ℝ ℝ, volume] (ψ n).normed volume with hndef
  set k : E d → ℝ := fun y ↦ ‖H y‖ with hkdef
  have hsmooth : ∀ n, ContDiff ℝ 1 (hn n) := fun n ↦
    (ψ n).hasCompactSupport_normed.contDiff_convolution_right _ hhi.locallyIntegrable
      (ψ n).contDiff_normed
  have hm1 : ∀ {f : E d → ℝ}, Integrable f → MemLp f (ENNReal.ofReal 1) volume := fun hf ↦ by
    rw [ENNReal.ofReal_one]; exact memLp_one_iff_integrable.2 hf
  have hlim1 := tendsto_eLpNorm_convolution_sub (p := 1) le_rfl (hm1 hhi) hψ
  have hlim2 := tendsto_eLpNorm_convolution_sub (p := 1) le_rfl (hm1 hHi.norm) hψ
  simp only [ENNReal.ofReal_one] at hlim1 hlim2
  set ε₁ : ℕ → ℝ≥0∞ := fun n ↦ eLpNorm (hn n - h) 1 volume with hε₁
  set ε₂ : ℕ → ℝ≥0∞ := fun n ↦
    eLpNorm (k ⋆[lsmul ℝ ℝ, volume] (ψ n).normed volume - k) 1 volume with hε₂
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * ρ) * (2 ^ d * volume B) with hcdef
  have hc : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) measure_ball_lt_top.ne)
  set X : ℝ≥0∞ := ∫⁻ x in B, ‖G x‖ₑ with hX
  have hGm : AEMeasurable (fun x ↦ ‖G x‖ₑ) (volume.restrict B) :=
    ((hw.2.1.integrableOn_compact_subset hzU (isCompact_closedBall z ρ)).1.mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)).enorm
  -- the estimate for each `n`
  have hstep : ∀ n, ∫⁻ x in B, ∫⁻ y in B, ‖g x - g y‖ₑ ≤
      c * (X + ε₂ n) + 2 * volume B * ε₁ n := by
    intro n
    set e : E d → ℝ := fun x ↦ h x - hn n x with hedef
    have hem : AEMeasurable (fun x ↦ ‖e x‖ₑ) volume :=
      (hhi.aestronglyMeasurable.sub (hsmooth n).continuous.aestronglyMeasurable).enorm
    have heB : ∫⁻ x in B, ‖e x‖ₑ ≤ ε₁ n := by
      rw [hε₁]; dsimp only; rw [eLpNorm_one_eq_lintegral_enorm]
      refine (setLIntegral_le_lintegral _ _).trans (le_of_eq (lintegral_congr fun x ↦ ?_))
      simp only [hedef, Pi.sub_apply]; rw [enorm_sub_rev]
    -- the double integral
    have hA : ∫⁻ x in B, ∫⁻ y in B, ‖g x - g y‖ₑ ≤
        (∫⁻ x in B, ∫⁻ y in B, ‖hn n x - hn n y‖ₑ) + 2 * volume B * ε₁ n := by
      have hpt : ∀ x ∈ B, ∀ y ∈ B,
          ‖g x - g y‖ₑ ≤ ‖hn n x - hn n y‖ₑ + (‖e x‖ₑ + ‖e y‖ₑ) := by
        intro x hx y hy
        rw [← hhB x hx, ← hhB y hy]
        have : h x - h y = (hn n x - hn n y) + (e x - e y) := by simp only [hedef]; ring
        rw [this]
        exact (enorm_add_le _ _).trans (add_le_add le_rfl enorm_sub_le)
      have hmeas2 : ∀ x, AEMeasurable (fun y ↦ ‖e x‖ₑ + ‖e y‖ₑ) (volume.restrict B) :=
        fun x ↦ (aemeasurable_const.add hem).restrict
      calc ∫⁻ x in B, ∫⁻ y in B, ‖g x - g y‖ₑ
          ≤ ∫⁻ x in B, ∫⁻ y in B, (‖hn n x - hn n y‖ₑ + (‖e x‖ₑ + ‖e y‖ₑ)) :=
            setLIntegral_mono' measurableSet_ball fun x hx ↦
              setLIntegral_mono' measurableSet_ball fun y hy ↦ hpt x hx y hy
        _ = ∫⁻ x in B, ((∫⁻ y in B, ‖hn n x - hn n y‖ₑ) +
              (‖e x‖ₑ * volume B + ∫⁻ y in B, ‖e y‖ₑ)) := by
            refine lintegral_congr fun x ↦ ?_
            rw [lintegral_add_right' _ (hmeas2 x), lintegral_add_left' aemeasurable_const,
              setLIntegral_const]
        _ = (∫⁻ x in B, ∫⁻ y in B, ‖hn n x - hn n y‖ₑ) +
              ((∫⁻ x in B, ‖e x‖ₑ) * volume B + volume B * ∫⁻ y in B, ‖e y‖ₑ) := by
            rw [lintegral_add_right' _ ((hem.mul_const _).add aemeasurable_const).restrict,
              lintegral_add_right' _ aemeasurable_const.restrict, lintegral_mul_const' _ _
                measure_ball_lt_top.ne, setLIntegral_const]
            ring
        _ ≤ (∫⁻ x in B, ∫⁻ y in B, ‖hn n x - hn n y‖ₑ) + 2 * volume B * ε₁ n := by
            gcongr
            calc (∫⁻ x in B, ‖e x‖ₑ) * volume B + volume B * ∫⁻ y in B, ‖e y‖ₑ
                ≤ ε₁ n * volume B + volume B * ε₁ n := by gcongr
              _ = 2 * volume B * ε₁ n := by ring
    -- the gradient
    have hG : ∫⁻ x in B, ‖fderiv ℝ (hn n) x‖ₑ ≤ X + ε₂ n := by
      have hpt : ∀ x ∈ B, ‖fderiv ℝ (hn n) x‖ₑ ≤ ‖G x‖ₑ +
          ‖(k ⋆[lsmul ℝ ℝ, volume] (ψ n).normed volume - k) x‖ₑ := by
        intro x hx
        calc ‖fderiv ℝ (hn n) x‖ₑ = ENNReal.ofReal ‖fderiv ℝ (hn n) x‖ := (ofReal_norm _).symm
          _ ≤ ENNReal.ofReal ((k ⋆[lsmul ℝ ℝ, volume] (ψ n).normed volume) x) :=
              ENNReal.ofReal_le_ofReal (norm_fderiv_convolution_le hwu hhi hHi (ψ n) x)
          _ ≤ ENNReal.ofReal (k x) + ‖(k ⋆[lsmul ℝ ℝ, volume] (ψ n).normed volume) x - k x‖ₑ :=
              ofReal_le_add_enorm_sub _ _ (norm_nonneg _)
          _ = ‖G x‖ₑ + ‖(k ⋆[lsmul ℝ ℝ, volume] (ψ n).normed volume - k) x‖ₑ := by
              simp only [hkdef, Pi.sub_apply, ofReal_norm, hHB x hx]
      calc ∫⁻ x in B, ‖fderiv ℝ (hn n) x‖ₑ
          ≤ ∫⁻ x in B, (‖G x‖ₑ + ‖(k ⋆[lsmul ℝ ℝ, volume] (ψ n).normed volume - k) x‖ₑ) :=
            setLIntegral_mono' measurableSet_ball hpt
        _ ≤ X + ∫⁻ x, ‖(k ⋆[lsmul ℝ ℝ, volume] (ψ n).normed volume - k) x‖ₑ := by
            rw [lintegral_add_left' hGm]
            exact add_le_add le_rfl (setLIntegral_le_lintegral _ _)
        _ = X + ε₂ n := by rw [hε₂]; dsimp only; rw [eLpNorm_one_eq_lintegral_enorm]
    calc ∫⁻ x in B, ∫⁻ y in B, ‖g x - g y‖ₑ
        ≤ (∫⁻ x in B, ∫⁻ y in B, ‖hn n x - hn n y‖ₑ) + 2 * volume B * ε₁ n := hA
      _ ≤ c * (∫⁻ x in B, ‖fderiv ℝ (hn n) x‖ₑ) + 2 * volume B * ε₁ n :=
          add_le_add (lintegral_lintegral_enorm_sub_le_of_contDiff (hsmooth n) z ρ) le_rfl
      _ ≤ c * (X + ε₂ n) + 2 * volume B * ε₁ n := add_le_add (mul_le_mul' le_rfl hG) le_rfl
  -- the limit
  have hlim : Tendsto (fun n ↦ c * (X + ε₂ n) + 2 * volume B * ε₁ n) atTop
      (𝓝 (c * (X + 0) + 2 * volume B * 0)) := by
    refine Tendsto.add (ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hlim2) (Or.inr hc))
      (ENNReal.Tendsto.const_mul hlim1 (Or.inr (ENNReal.mul_ne_top (by norm_num)
        measure_ball_lt_top.ne)))
  rw [add_zero, mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim hstep

/-- **De Giorgi's isoperimetric lemma on a ball**:
`|{g = 0} ∩ B| ∫_B |g| ≤ 2ρ 2ᵈ |B| ∫_B |G|`. -/
theorem measure_zero_mul_lintegral_le {U : Set (E d)} (hU : IsOpen U) {g : E d → ℝ}
    {G : E d → E d} (hw : HasWeakGradient U g G) {z : E d} {ρ : ℝ} (hρ : 0 < ρ)
    (hzU : closedBall z ρ ⊆ U) :
    volume ({y | g y = 0} ∩ ball z ρ) * ∫⁻ x in ball z ρ, ‖g x‖ₑ ≤
      ENNReal.ofReal (2 * ρ) * (2 ^ d * volume (ball z ρ)) * ∫⁻ x in ball z ρ, ‖G x‖ₑ := by
  set B := ball z ρ with hBdef
  have hgm : AEStronglyMeasurable g (volume.restrict B) :=
    (hw.1.integrableOn_compact_subset hzU (isCompact_closedBall z ρ)).1.mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hZ : NullMeasurableSet {y | g y = 0} (volume.restrict B) :=
    hgm.aemeasurable.nullMeasurable (measurableSet_singleton 0)
  refine le_trans ?_ (lintegral_lintegral_enorm_sub_le hU hw hρ hzU)
  rw [mul_comm, ← lintegral_mul_const' _ _ (measure_ne_top_of_subset inter_subset_right
    measure_ball_lt_top.ne)]
  refine lintegral_mono fun x ↦ ?_
  calc ‖g x‖ₑ * volume ({y | g y = 0} ∩ B)
      = ∫⁻ y in B, {y | g y = 0}.indicator (fun _ ↦ ‖g x‖ₑ) y := by
        rw [lintegral_indicator_const₀ hZ,
          Measure.restrict_apply₀' measurableSet_ball.nullMeasurableSet, mul_comm]
    _ ≤ ∫⁻ y in B, ‖g x - g y‖ₑ := by
        refine lintegral_mono fun y ↦ ?_
        by_cases hy : g y = 0
        · rw [indicator_of_mem (show y ∈ {y | g y = 0} from hy), hy, sub_zero]
        · rw [indicator_of_notMem (show y ∉ {y | g y = 0} from hy)]; exact bot_le

/-- **De Giorgi's isoperimetric lemma on a ball**, real form:
`|{g = 0} ∩ B| ∫_B |g| ≤ 2ρ 2ᵈ |B| ∫_B |G|`. -/
theorem measure_zero_mul_integral_le {U : Set (E d)} (hU : IsOpen U) {g : E d → ℝ}
    {G : E d → E d} (hw : HasWeakGradient U g G) {z : E d} {ρ : ℝ} (hρ : 0 < ρ)
    (hzU : closedBall z ρ ⊆ U) :
    (volume ({y | g y = 0} ∩ ball z ρ)).toReal * ∫ x in ball z ρ, ‖g x‖ ≤
      2 * ρ * (2 ^ d * (volume (ball z ρ)).toReal) * ∫ x in ball z ρ, ‖G x‖ := by
  have hc := isCompact_closedBall z ρ
  have hgi : IntegrableOn g (ball z ρ) :=
    (hw.1.integrableOn_compact_subset hzU hc).mono_set ball_subset_closedBall
  have hGi : IntegrableOn G (ball z ρ) :=
    (hw.2.1.integrableOn_compact_subset hzU hc).mono_set ball_subset_closedBall
  have h := measure_zero_mul_lintegral_le hU hw hρ hzU
  rw [← ofReal_integral_norm_eq_lintegral_enorm hgi,
    ← ofReal_integral_norm_eq_lintegral_enorm hGi] at h
  have hfin : ENNReal.ofReal (2 * ρ) * (2 ^ d * volume (ball z ρ)) *
      ENNReal.ofReal (∫ x in ball z ρ, ‖G x‖) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) measure_ball_lt_top.ne))
      ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono hfin h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h2
  rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)] at h2

end EllipticBernoulli
