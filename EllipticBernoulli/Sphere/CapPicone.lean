/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.TwoPhase
public import EllipticBernoulli.Sphere.CapShoot
import EllipticBernoulli.Sphere.CapODE
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Weighted Picone inequality and the characterization of `Λ_d(θ)`

A *solution with flux* of the colatitude equation on `[0, θ]` (`IsCapSolution m λ θ g H`) is a
pair `(g, H)` with `H = sin^m g'` and `H' = -λ sin^m g` on `(0, θ)`, `H(0) = 0`, and `g`, `H`,
`g'` continuous on `[0, θ]`.

* `le_capEigenvalue_of_pos`: **Picone** (case `g(θ) > 0`). If `g > 0` on
  `[0, θ]`, then `λ ≤ Λ_d(θ)` (with `m = d - 2`).
* `le_capEigenvalue_of_eq_zero`: Picone in the case `g > 0` on `[0, θ)`, `g(θ) = 0`, `g'(θ) < 0`.
* `capEigenvalue_le_of_eq_zero`: if `g(θ) = 0` and `g(0) ≠ 0`, the Rayleigh quotient of `g` is
  `λ`, so `Λ_d(θ) ≤ λ`.
* `capEigenvalue_eq_of_isCapSolution`: the characterization of `Λ_d(θ)`:
  a positive solution on `[0, θ)` vanishing at `θ` with `g'(θ) < 0` has `λ = Λ_d(θ)`.
* `capEigenvalue_pi_div_two`: `Λ_d(π/2) = d - 1`, with `g = cos`.
* `isCapSolution_capShoot`: the shooting solution is a solution with flux on `[0, θ]`, `θ < π`.
-/

open Set Filter Topology MeasureTheory Real
open scoped NNReal

public section

namespace EllipticBernoulli

/-- `(g, H)` solves the colatitude equation `(sin^m g')' = -λ sin^m g` on `[0, θ]` with flux
`H = sin^m g'`: `g`, `H` and `g' = H / sin^m` are continuous on `[0, θ]`, `H(0) = 0`, and the
two first-order equations hold on `(0, θ)`. -/
structure IsCapSolution (m : ℕ) (lam θ : ℝ) (g H : ℝ → ℝ) : Prop where
  continuousOn : ContinuousOn g (Icc 0 θ)
  continuousOn_flux : ContinuousOn H (Icc 0 θ)
  flux_zero : H 0 = 0
  continuousOn_deriv : ContinuousOn (fun x ↦ H x / sin x ^ m) (Icc 0 θ)
  hasDerivAt : ∀ x ∈ Ioo 0 θ, HasDerivAt g (H x / sin x ^ m) x
  hasDerivAt_flux : ∀ x ∈ Ioo 0 θ, HasDerivAt H (-(lam * sin x ^ m * g x)) x

namespace IsCapSolution

variable {m : ℕ} {lam θ θ' : ℝ} {g H : ℝ → ℝ}

theorem mono (h : IsCapSolution m lam θ g H) (hθ' : θ' ≤ θ) : IsCapSolution m lam θ' g H where
  continuousOn := h.continuousOn.mono (Icc_subset_Icc le_rfl hθ')
  continuousOn_flux := h.continuousOn_flux.mono (Icc_subset_Icc le_rfl hθ')
  flux_zero := h.flux_zero
  continuousOn_deriv := h.continuousOn_deriv.mono (Icc_subset_Icc le_rfl hθ')
  hasDerivAt x hx := h.hasDerivAt x ⟨hx.1, hx.2.trans_le hθ'⟩
  hasDerivAt_flux x hx := h.hasDerivAt_flux x ⟨hx.1, hx.2.trans_le hθ'⟩

end IsCapSolution

/-! ### A mean-value Lipschitz bound -/

/-- A function continuous on `[a, b]` whose derivative on `(a, b)` is bounded by `C` is
`C`-Lipschitz on `[a, b]`. -/
theorem lipschitzOnWith_of_hasDerivAt_Ioo {f f' : ℝ → ℝ} {a b C : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hC : ∀ x ∈ Ioo a b, |f' x| ≤ C) : LipschitzOnWith (Real.toNNReal C) f (Icc a b) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have key : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, u < v → |f v - f u| ≤ C * (v - u) := by
    intro u hu v hv huv
    obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' huv
      (hf.mono (Icc_subset_Icc hu.1 hv.2))
      fun x hx ↦ hf' x ⟨hu.1.trans_lt hx.1, hx.2.trans_le hv.2⟩
    have hcC := hC c ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩
    rw [hslope, abs_div, abs_of_pos (sub_pos.2 huv), div_le_iff₀ (sub_pos.2 huv)] at hcC
    exact hcC
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · rw [abs_sub_comm, abs_sub_comm x, abs_of_pos (sub_pos.2 hxy)]
    exact (key x hx y hy hxy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (sub_pos.2 hxy).le)
  · simp
  · rw [abs_of_pos (sub_pos.2 hxy)]
    exact (key y hy x hx hxy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (sub_pos.2 hxy).le)

/-! ### Picone -/

section Picone

variable {d : ℕ} {lam θ : ℝ} {g H : ℝ → ℝ}

/-- **Weighted Picone inequality on `[0, b]`.** If `(g, H)` solves the
colatitude equation on `[0, θ]`, `0 < b ≤ θ ≤ π`, `g > 0` on `[0, b]`, and `F` is Lipschitz on
`[0, b]`, then
`λ ∫_0^b F² sin^m + F(b)² H(b) / g(b) ≤ ∫_0^b F'² sin^m`. -/
theorem picone_integral_le (hθπ : θ ≤ π) (hsol : IsCapSolution (d - 2) lam θ g H) {b : ℝ}
    (hb : 0 < b) (hbθ : b ≤ θ) (hg : ∀ x ∈ Icc 0 b, 0 < g x) {F : ℝ → ℝ} {K : ℝ≥0}
    (hF : LipschitzOnWith K F (Icc 0 b)) :
    lam * (∫ φ in 0..b, F φ ^ 2 * sin φ ^ (d - 2)) + F b ^ 2 * (H b / g b) ≤
      ∫ φ in 0..b, deriv F φ ^ 2 * sin φ ^ (d - 2) := by
  set m := d - 2
  have hsol' := hsol.mono hbθ
  -- bounds on `[0, b]`
  obtain ⟨c, hc0, hc⟩ : ∃ c > 0, ∀ x ∈ Icc 0 b, c ≤ g x := by
    obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hb.le)
      hsol'.continuousOn
    exact ⟨g x₀, hg x₀ hx₀, fun x hx ↦ hmin hx⟩
  obtain ⟨MD, hMD⟩ := isCompact_Icc.exists_bound_of_continuousOn hsol'.continuousOn_deriv
  have hsinpos : ∀ x ∈ Ioo 0 b, 0 < sin x := fun x hx ↦
    sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans_le (hbθ.trans hθπ))
  -- `Ψ = H / g` is Lipschitz on `[0, b]`
  set Ψ : ℝ → ℝ := fun x ↦ H x / g x
  set Ψ' : ℝ → ℝ := fun x ↦ -(lam * sin x ^ m) - (H x / sin x ^ m) ^ 2 * sin x ^ m / g x ^ 2
  have hΨd : ∀ x ∈ Ioo 0 b, HasDerivAt Ψ (Ψ' x) x := by
    intro x hx
    have hgx : g x ≠ 0 := (hg x (Ioo_subset_Icc_self hx)).ne'
    have hs : sin x ^ m ≠ 0 := (pow_pos (hsinpos x hx) m).ne'
    have h := (hsol'.hasDerivAt_flux x hx).div (hsol'.hasDerivAt x hx) hgx
    convert h using 1
    simp only [Ψ']
    field_simp
  have hΨc : ContinuousOn Ψ (Icc 0 b) :=
    hsol'.continuousOn_flux.div hsol'.continuousOn fun x hx ↦ (hg x hx).ne'
  have hΨb : ∀ x ∈ Ioo 0 b, |Ψ' x| ≤ |lam| + MD ^ 2 / c ^ 2 := by
    intro x hx
    have hs := hsinpos x hx
    have hs1 : sin x ^ m ≤ 1 := pow_le_one₀ hs.le (sin_le_one x)
    have hD : (H x / sin x ^ m) ^ 2 ≤ MD ^ 2 := by
      have := hMD x (Ioo_subset_Icc_self hx)
      rw [Real.norm_eq_abs] at this
      exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
    have hgx : c ^ 2 ≤ g x ^ 2 := pow_le_pow_left₀ hc0.le (hc x (Ioo_subset_Icc_self hx)) 2
    have h1 : |lam * sin x ^ m| ≤ |lam| := by
      rw [abs_mul, abs_of_pos (pow_pos hs m)]
      exact mul_le_of_le_one_right (abs_nonneg _) hs1
    have h2 : |(H x / sin x ^ m) ^ 2 * sin x ^ m / g x ^ 2| ≤ MD ^ 2 / c ^ 2 := by
      rw [abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) (pow_pos hs m).le)
        (sq_nonneg _))]
      calc (H x / sin x ^ m) ^ 2 * sin x ^ m / g x ^ 2 ≤ MD ^ 2 * 1 / c ^ 2 := by
            gcongr
      _ = MD ^ 2 / c ^ 2 := by ring
    calc |Ψ' x| ≤ |lam * sin x ^ m| + |(H x / sin x ^ m) ^ 2 * sin x ^ m / g x ^ 2| := by
          simp only [Ψ']
          rw [sub_eq_add_neg, ← abs_neg (lam * sin x ^ m), ← abs_neg (_ / g x ^ 2)]
          exact (abs_add_le _ _).trans (by rw [abs_neg, abs_neg])
      _ ≤ |lam| + MD ^ 2 / c ^ 2 := add_le_add h1 h2
  have hΨL := lipschitzOnWith_of_hasDerivAt_Ioo hΨc hΨd hΨb
  -- absolute continuity and FTC for `Φ = F² Ψ`
  have hFu : LipschitzOnWith K F (uIcc 0 b) := by rwa [uIcc_of_le hb.le]
  have hΨu : LipschitzOnWith (Real.toNNReal (|lam| + MD ^ 2 / c ^ 2)) Ψ (uIcc 0 b) := by
    rwa [uIcc_of_le hb.le]
  have hFac := hFu.absolutelyContinuousOnInterval
  have hΦac := (hFac.fun_mul hFac).fun_mul hΨu.absolutelyContinuousOnInterval
  have hFTC := hΦac.integral_deriv_eq_sub
  simp only [hsol.flux_zero, zero_div, mul_zero, Ψ] at hFTC
  -- pointwise Picone
  have hFc : ContinuousOn F (Icc 0 b) := hF.continuousOn
  have hsin_c : Continuous fun φ : ℝ ↦ sin φ ^ m := continuous_sin.pow m
  have hint₁ := hΦac.intervalIntegrable_deriv
  have hint₂ : IntervalIntegrable
      (fun φ ↦ deriv F φ ^ 2 * sin φ ^ m - lam * (F φ ^ 2 * sin φ ^ m)) volume 0 b :=
    ((intervalIntegrable_deriv_sq_of_lipschitzOnWith hb.le hF).mul_continuousOn
      hsin_c.continuousOn).sub
      (((hFc.pow 2).mul hsin_c.continuousOn).intervalIntegrable_of_Icc hb.le |>.const_mul lam)
  have hmono : ∫ φ in 0..b, deriv (fun x ↦ F x * F x * Ψ x) φ ≤
      ∫ φ in 0..b, deriv F φ ^ 2 * sin φ ^ m - lam * (F φ ^ 2 * sin φ ^ m) := by
    refine intervalIntegral.integral_mono_ae_restrict hb.le hint₁ hint₂ ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hFac.ae_differentiableAt,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ)), ae_restrict_of_ae (volume.ae_ne b)]
      with x hx hxd hx0 hxb
    have hxI : x ∈ Ioo 0 b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxb⟩
    have hxu : x ∈ uIcc 0 b := by rw [uIcc_of_le hb.le]; exact hx
    have hFd := (hxd hxu).hasDerivAt
    have hΦd : HasDerivAt (fun x ↦ F x * F x * Ψ x)
        ((deriv F x * F x + F x * deriv F x) * Ψ x + F x * F x * Ψ' x) x :=
      (hFd.mul hFd).mul (hΨd x hxI)
    rw [hΦd.deriv]
    have hs := pow_pos (hsinpos x hxI) m
    have hgx := hg x hx
    simp only [Ψ, Ψ']
    have key : deriv F x ^ 2 * sin x ^ m - lam * (F x ^ 2 * sin x ^ m) -
        ((deriv F x * F x + F x * deriv F x) * (H x / g x) + F x * F x *
          (-(lam * sin x ^ m) - (H x / sin x ^ m) ^ 2 * sin x ^ m / g x ^ 2)) =
        sin x ^ m * (deriv F x - F x * (H x / sin x ^ m) / g x) ^ 2 := by
      field_simp
      ring
    nlinarith [mul_nonneg hs.le (sq_nonneg (deriv F x - F x * (H x / sin x ^ m) / g x))]
  have hA : IntervalIntegrable (fun φ ↦ deriv F φ ^ 2 * sin φ ^ m) volume 0 b :=
    (intervalIntegrable_deriv_sq_of_lipschitzOnWith hb.le hF).mul_continuousOn hsin_c.continuousOn
  have hB : IntervalIntegrable (fun φ ↦ lam * (F φ ^ 2 * sin φ ^ m)) volume 0 b :=
    (((hFc.pow 2).mul hsin_c.continuousOn).intervalIntegrable_of_Icc hb.le).const_mul lam
  rw [hFTC, intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul] at hmono
  have e : F b * F b * (H b / g b) = F b ^ 2 * (H b / g b) := by ring
  rw [e] at hmono
  linarith

/-- **Picone, positive case** (`g(θ) > 0`). If `(g, H)` solves the
colatitude equation on `[0, θ]`, `0 < θ ≤ π`, and `g > 0` on `[0, θ]`, then `λ ≤ Λ_d(θ)`. -/
theorem le_capEigenvalue_of_pos (hθ : 0 < θ) (hθπ : θ ≤ π)
    (hsol : IsCapSolution (d - 2) lam θ g H) (hg : ∀ x ∈ Icc 0 θ, 0 < g x) :
    lam ≤ capEigenvalue d θ := by
  refine le_capEigenvalue_of_forall hθ hθπ fun F hF ↦ ?_
  obtain ⟨K, hK⟩ := hF.lipschitzOn
  have h := picone_integral_le hθπ hsol hθ le_rfl hg hK
  rw [hF.apply_right_eq_zero] at h
  simpa using h

/-- **Picone, vanishing case** (`g(θ) = 0`). If `(g, H)` solves the
colatitude equation on `[0, θ]`, `0 < θ < π`, `g > 0` on `[0, θ)`, `g(θ) = 0`, and `g` has
derivative `H(θ) / sin^m θ` at `θ` with `H(θ) < 0`, then `λ ≤ Λ_d(θ)`. -/
theorem le_capEigenvalue_of_eq_zero (hθ : 0 < θ) (hθπ : θ < π)
    (hsol : IsCapSolution (d - 2) lam θ g H) (hg : ∀ x ∈ Ico 0 θ, 0 < g x) (hgθ : g θ = 0)
    (hgd : HasDerivAt g (H θ / sin θ ^ (d - 2)) θ) (hH : H θ < 0) :
    lam ≤ capEigenvalue d θ := by
  set m := d - 2
  refine le_capEigenvalue_of_forall hθ hθπ.le fun F hF ↦ ?_
  obtain ⟨K, hK⟩ := hF.lipschitzOn
  have hFθ := hF.apply_right_eq_zero
  have hsθ : 0 < sin θ ^ m := pow_pos (sin_pos_of_pos_of_lt_pi hθ hθπ) m
  set g' := H θ / sin θ ^ m
  have hg' : g' < 0 := div_neg_of_neg_of_pos hH hsθ
  obtain ⟨MH, hMH⟩ := isCompact_Icc.exists_bound_of_continuousOn hsol.continuousOn_flux
  -- `g(b) ≥ (-g'/2) (θ - b)` for `b` close to `θ` from the left
  have hslope := hgd.tendsto_slope
  have hev : ∀ᶠ b in 𝓝[<] θ, -g' / 2 * (θ - b) ≤ g b := by
    have h1 : ∀ᶠ b in 𝓝[<] θ, slope g θ b < g' / 2 :=
      (hslope.mono_left (nhdsWithin_mono _ fun x hx ↦ ne_of_lt hx)).eventually
        (gt_mem_nhds (by linarith))
    filter_upwards [h1, self_mem_nhdsWithin] with b hb hbθ
    rw [slope_def_field, hgθ, sub_zero, div_lt_iff_of_neg (sub_neg.2 hbθ)] at hb
    linarith
  -- the boundary term tends to `0`
  have hbdry : Tendsto (fun b ↦ F b ^ 2 * (H b / g b)) (𝓝[<] θ) (𝓝 0) := by
    have hlin : Tendsto (fun b ↦ (K : ℝ) ^ 2 * MH * (θ - b) / (-g' / 2)) (𝓝[<] θ)
        (𝓝 ((K : ℝ) ^ 2 * MH * (θ - θ) / (-g' / 2))) :=
      ((continuous_const.mul (continuous_const.sub continuous_id)).div_const _).tendsto θ
        |>.mono_left nhdsWithin_le_nhds
    rw [sub_self, mul_zero, zero_div] at hlin
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [hev, self_mem_nhdsWithin, Ioo_mem_nhdsLT hθ] with b hb hbθ hb0
    have hθb : 0 < θ - b := sub_pos.2 hbθ
    have hgb : 0 < g b := lt_of_lt_of_le (by nlinarith) hb
    have hbI : b ∈ Icc 0 θ := ⟨hb0.1.le, hbθ.le⟩
    have hFb : |F b| ≤ K * (θ - b) := by
      have := hK.dist_le_mul b hbI θ ⟨hθ.le, le_rfl⟩
      rwa [Real.dist_eq, hFθ, sub_zero, Real.dist_eq, abs_of_neg (sub_neg.2 hbθ), neg_sub]
        at this
    have hHb : |H b| ≤ MH := by simpa using hMH b hbI
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hgb, abs_pow]
    have hF2 : |F b| ^ 2 ≤ (K : ℝ) ^ 2 * (θ - b) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hFb 2
    rw [le_div_iff₀ (by linarith)]
    have hMH0 : 0 ≤ MH := (abs_nonneg _).trans hHb
    calc |F b| ^ 2 * (|H b| / g b) * (-g' / 2) ≤ (K : ℝ) ^ 2 * (θ - b) ^ 2 * (MH / g b) *
          (-g' / 2) := by gcongr; linarith
      _ = (K : ℝ) ^ 2 * MH * (θ - b) * ((θ - b) * (-g' / 2) / g b) := by ring
      _ ≤ (K : ℝ) ^ 2 * MH * (θ - b) * 1 := by
          gcongr
          rw [div_le_one hgb]; linarith
      _ = (K : ℝ) ^ 2 * MH * (θ - b) := mul_one _
  -- continuity of the integrals in the upper limit
  have hprim : ∀ f : ℝ → ℝ, IntervalIntegrable f volume 0 θ →
      Tendsto (fun b ↦ ∫ φ in 0..b, f φ) (𝓝[<] θ) (𝓝 (∫ φ in 0..θ, f φ)) := by
    intro f hf
    have hc := intervalIntegral.continuousOn_primitive_interval' hf (left_mem_uIcc (a := 0))
    rw [uIcc_of_le hθ.le] at hc
    refine (hc θ ⟨hθ.le, le_rfl⟩).mono_of_mem_nhdsWithin ?_
    exact mem_of_superset (Ioo_mem_nhdsLT hθ) fun x hx ↦ ⟨hx.1.le, hx.2.le⟩
  have hsin_c : Continuous fun φ : ℝ ↦ sin φ ^ m := continuous_sin.pow m
  have hI₁ := hprim (fun φ ↦ F φ ^ 2 * sin φ ^ m)
    (((hK.continuousOn.pow 2).mul hsin_c.continuousOn).intervalIntegrable_of_Icc hθ.le)
  have hI₂ := hprim (fun φ ↦ deriv F φ ^ 2 * sin φ ^ m)
    ((intervalIntegrable_deriv_sq_of_lipschitzOnWith hθ.le hK).mul_continuousOn
      hsin_c.continuousOn)
  refine le_of_tendsto_of_tendsto (by simpa using (hI₁.const_mul lam).add hbdry) hI₂ ?_
  filter_upwards [Ioo_mem_nhdsLT hθ] with b hb
  exact picone_integral_le hθπ.le hsol hb.1 hb.2.le (fun x hx ↦ hg x ⟨hx.1, hx.2.trans_lt hb.2⟩)
    (hK.mono (Icc_subset_Icc le_rfl hb.2.le))

/-- **Upper bound by a solution vanishing at `θ`.** If `(g, H)` solves the colatitude equation on
`[0, θ]`, `0 < θ ≤ π`, `g(θ) = 0` and `g(0) ≠ 0`, then `Λ_d(θ) ≤ λ`: the Rayleigh quotient of `g`
is `λ`. -/
theorem capEigenvalue_le_of_eq_zero (hθ : 0 < θ) (hθπ : θ ≤ π)
    (hsol : IsCapSolution (d - 2) lam θ g H) (hgθ : g θ = 0) (hg0 : g 0 ≠ 0) :
    capEigenvalue d θ ≤ lam := by
  set m := d - 2
  set D : ℝ → ℝ := fun x ↦ H x / sin x ^ m
  obtain ⟨MD, hMD⟩ := isCompact_Icc.exists_bound_of_continuousOn hsol.continuousOn_deriv
  have hL := lipschitzOnWith_of_hasDerivAt_Ioo hsol.continuousOn hsol.hasDerivAt
    fun x hx ↦ by
      have := hMD x (Ioo_subset_Icc_self hx)
      rwa [Real.norm_eq_abs] at this
  have hadm : IsCapAdmissible θ g := ⟨⟨_, hL⟩, hgθ, ⟨0, ⟨le_rfl, hθ.le⟩, hg0⟩⟩
  have hsinpos : ∀ x ∈ Ioo 0 θ, 0 < sin x := fun x hx ↦
    sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans_le hθπ)
  have hsin_c : Continuous fun φ : ℝ ↦ sin φ ^ m := continuous_sin.pow m
  -- `∫ D H - λ ∫ g² sin^m = [g H]_0^θ = 0`
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.le
    (hsol.continuousOn.mul hsol.continuousOn_flux)
    (fun x hx ↦ (hsol.hasDerivAt x hx).mul (hsol.hasDerivAt_flux x hx))
    ((hsol.continuousOn_deriv.mul hsol.continuousOn_flux |>.add
      (hsol.continuousOn.mul (((continuousOn_const.mul hsin_c.continuousOn).mul
        hsol.continuousOn).neg))).intervalIntegrable_of_Icc hθ.le)
  simp only [Pi.mul_apply, hgθ, hsol.flux_zero, zero_mul, mul_zero, sub_zero] at hFTC
  have hnum : ∫ φ in 0..θ, deriv g φ ^ 2 * sin φ ^ m =
      lam * ∫ φ in 0..θ, g φ ^ 2 * sin φ ^ m := by
    have h1 : ∫ φ in 0..θ, deriv g φ ^ 2 * sin φ ^ m =
        ∫ φ in 0..θ, (D φ * H φ + g φ * -(lam * sin φ ^ m * g φ)) +
          lam * (g φ ^ 2 * sin φ ^ m) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [volume.ae_ne θ] with x hxθ hx
      rw [uIoc_of_le hθ.le] at hx
      have hxI : x ∈ Ioo 0 θ := ⟨hx.1, lt_of_le_of_ne hx.2 hxθ⟩
      rw [(hsol.hasDerivAt x hxI).deriv]
      have hs := (pow_pos (hsinpos x hxI) m).ne'
      simp only [D]
      field_simp
      ring
    rw [h1, intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
    · simp only [D] at hFTC ⊢
      rw [hFTC, zero_add]
    · exact (hsol.continuousOn_deriv.mul hsol.continuousOn_flux |>.add
        (hsol.continuousOn.mul (((continuousOn_const.mul hsin_c.continuousOn).mul
          hsol.continuousOn).neg))).intervalIntegrable_of_Icc hθ.le
    · exact (((hsol.continuousOn.pow 2).mul hsin_c.continuousOn).intervalIntegrable_of_Icc
        hθ.le).const_mul lam
  have hR : capRayleigh d θ g = lam := by
    rw [capRayleigh, hnum, mul_div_assoc, div_self (integral_sq_mul_sin_pow_pos hθ hθπ hadm _).ne',
      mul_one]
  rw [← hR]
  exact csInf_le (bddBelow_capRayleigh hθ.le hθπ) ⟨g, hadm, rfl⟩

/-- **Characterization of `Λ_d(θ)`.** If `(g, H)` solves the colatitude
equation on `[0, θ]`, `0 < θ < π`, `g > 0` on `[0, θ)`, `g(θ) = 0`, and `g` has derivative
`H(θ) / sin^m θ` at `θ` with `H(θ) < 0`, then `Λ_d(θ) = λ`. -/
theorem capEigenvalue_eq_of_isCapSolution (hθ : 0 < θ) (hθπ : θ < π)
    (hsol : IsCapSolution (d - 2) lam θ g H) (hg : ∀ x ∈ Ico 0 θ, 0 < g x) (hgθ : g θ = 0)
    (hgd : HasDerivAt g (H θ / sin θ ^ (d - 2)) θ) (hH : H θ < 0) :
    capEigenvalue d θ = lam :=
  le_antisymm (capEigenvalue_le_of_eq_zero hθ hθπ.le hsol hgθ (hg 0 ⟨le_rfl, hθ⟩).ne')
    (le_capEigenvalue_of_eq_zero hθ hθπ hsol hg hgθ hgd hH)

/-- **`Λ_d(π/2) = d - 1`**: the solution `g = cos` with flux
`H = -sin^{d-1}`. -/
theorem capEigenvalue_pi_div_two (hd : 2 ≤ d) : capEigenvalue d (π / 2) = d - 1 := by
  set m := d - 2
  have hdm : ((d : ℝ) - 1) = (m : ℝ) + 1 := by
    simp only [m]; push_cast [Nat.cast_sub hd]; ring
  have hD : ∀ x, -sin x ^ (m + 1) / sin x ^ m = -sin x := fun x ↦ by
    rcases eq_or_ne (sin x) 0 with h | h
    · simp [h]
    · field_simp; ring
  have hsol : IsCapSolution m ((d : ℝ) - 1) (π / 2) cos fun x ↦ -sin x ^ (m + 1) := by
    refine ⟨continuous_cos.continuousOn, (continuous_sin.pow _).neg.continuousOn, by simp,
      ?_, fun x _ ↦ ?_, fun x _ ↦ ?_⟩
    · simp only [hD]; exact continuous_sin.neg.continuousOn
    · rw [hD]; exact hasDerivAt_cos x
    · convert ((hasDerivAt_sin x).pow (m + 1)).neg using 1
      rw [hdm]; push_cast; ring
  rw [capEigenvalue_eq_of_isCapSolution (by positivity) (by linarith [pi_pos]) hsol
    (fun x hx ↦ cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hx.1], hx.2⟩) cos_pi_div_two
    (by rw [hD]; exact hasDerivAt_cos _) (by simp)]

end Picone

/-! ### The shooting solution -/

/-- The shooting solution `y(·, λ)` with its flux solves the colatitude equation on `[0, θ]` for
`θ < π`. -/
theorem isCapSolution_capShoot (m : ℕ) (lam : ℝ) {θ : ℝ} (hθπ : θ < π) :
    IsCapSolution m lam θ (capShoot m lam) (capShootFlux m lam) where
  continuousOn := (continuousOn_capShoot_left m lam).mono fun x hx ↦ ⟨hx.1, hx.2.trans_lt hθπ⟩
  continuousOn_flux := by
    have := (continuousOn_capShootFlux m).comp (continuous_id.prodMk continuous_const).continuousOn
      (s := Icc 0 θ) fun x hx ↦ ⟨⟨hx.1, hx.2.trans_lt hθπ⟩, mem_univ lam⟩
    exact this
  flux_zero := capShootFlux_zero_right m lam
  continuousOn_deriv := (continuousOn_capShootDeriv_left m lam).mono
    fun x hx ↦ ⟨hx.1, hx.2.trans_lt hθπ⟩
  hasDerivAt x hx := hasDerivAt_capShoot m lam ⟨hx.1, hx.2.trans hθπ⟩
  hasDerivAt_flux x hx := hasDerivAt_capShootFlux m lam ⟨hx.1, hx.2.trans hθπ⟩

end EllipticBernoulli

end
