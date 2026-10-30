/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Defs
import EllipticBernoulli.Common.FTCLip
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Explicit cap eigenvalues in dimensions two and four

This file proves the lower bounds `Λ₂(θ) ≥ (π/2θ)²` and `Λ₄(θ) ≥ π²/θ² - 1` for the radial cap
eigenvalue `Λ_d(θ) = capEigenvalue d θ`, and from them the cap inequality
`ᾱ_d(θ) + ᾱ_d(π - θ) ≥ 2` for `d = 2` and `d = 4`.

## Method

The lower bounds come from the one-dimensional Picone identity with the
positive supersolution `g(φ) = cos (k (φ - c))` of `-g'' = k² g`, written in Riccati form: with
`P = g'/g = -k tan (k (φ - c))`,
`F'² - k² F² - (F² P)' = (F' - F P)² ≥ 0`.
Integrating over `[a, b]` (`integral_sq_le_of_tan`) gives the mixed Wirtinger inequality
`∫_a^b F'² ≥ (π / 2(b - a))² ∫_a^b F²` when `F` vanishes at one endpoint
(`integral_sq_le_integral_deriv_sq_of_right`, `…_of_left`), after letting `k ↑ π / 2(b - a)`;
working with `k < π / 2(b - a)` keeps `P` smooth on the closed interval, so no boundary limit is
needed. For `d = 4` the substitution `G = F sin` turns the weighted quotient into
`∫ F'² sin² = ∫ G'² - ∫ G²` and `∫ F² sin² = ∫ G²` (`integral_deriv_sq_mul_sin_sq`), and `G`
vanishes at both endpoints, so the Dirichlet Wirtinger inequality on two half intervals applies.

For `d = 4`, the substitution `G = F sin` is the same computation as Picone's identity with the
supersolution `g = sin(πφ/θ) / sin φ` (`(s² g')' = s (h'' + h)` with `h = s g`), arranged so that
only the cosine supersolution is needed.

## Main results

* `capEigenvalue_le_of_le`: `θ ↦ Λ_d(θ)` is nonincreasing on `(0, π]`.
* `charExponent_mono`, `charExponent_mul_add_sub_two`: monotonicity of `κ_d` and
  `κ_d(β (β + d - 2)) = β`.
* `capEigenvalue_two_ge`, `capEigenvalue_four_ge`, `capExponent_two_ge`, `capExponent_four_ge`.
* `capInequality_two`, `capInequality_four`.
-/

open Set Filter Topology MeasureTheory Real
open scoped NNReal

public section

namespace EllipticBernoulli

section Calculus

variable {F : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}

/-- The derivative of a function Lipschitz on `[a, b]` is bounded by the Lipschitz constant at
interior points. -/
private theorem abs_deriv_le_of_lipschitzOnWith (hF : LipschitzOnWith K F (Icc a b)) {x : ℝ}
    (hx : x ∈ Ioo a b) : |deriv F x| ≤ K := by
  simpa using norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx.1 hx.2) hF

/-- The squared derivative of a function Lipschitz on `[a, b]` is interval integrable. -/
theorem intervalIntegrable_deriv_sq_of_lipschitzOnWith (hab : a ≤ b)
    (hF : LipschitzOnWith K F (Icc a b)) :
    IntervalIntegrable (fun x ↦ deriv F x ^ 2) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ ↦ (K : ℝ) ^ 2) intervalIntegrable_const
    ((measurable_deriv F).pow_const 2).aestronglyMeasurable ?_
  rw [uIoc_of_le hab]
  have hb : ∀ᵐ x ∂(volume.restrict (Ioc a b)), x ≠ b := ae_restrict_of_ae (volume.ae_ne b)
  filter_upwards [ae_restrict_mem measurableSet_Ioc, hb] with x hx hxb
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_deriv_le_of_lipschitzOnWith hF ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩) 2

/-- The product of two bounded Lipschitz functions on a set is Lipschitz on it. -/
private theorem exists_lipschitzOnWith_mul {s : Set ℝ} {f g : ℝ → ℝ} {Kf Kg : ℝ≥0} {Mf Mg : ℝ}
    (hf : LipschitzOnWith Kf f s) (hg : LipschitzOnWith Kg g s) (hfM : ∀ x ∈ s, |f x| ≤ Mf)
    (hgM : ∀ x ∈ s, |g x| ≤ Mg) : ∃ K', LipschitzOnWith K' (fun x ↦ f x * g x) s := by
  refine ⟨Kf * Mg.toNNReal + Mf.toNNReal * Kg, LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  have h1 := hf.dist_le_mul x hx y hy
  have h2 := hg.dist_le_mul x hx y hy
  rw [Real.dist_eq] at h1 h2 ⊢
  have hMg : Mg ≤ Mg.toNNReal := Real.le_coe_toNNReal Mg
  have hMf : Mf ≤ Mf.toNNReal := Real.le_coe_toNNReal Mf
  have hd : 0 ≤ dist x y := dist_nonneg
  calc |f x * g x - f y * g y| = |(f x - f y) * g x + f y * (g x - g y)| := by ring_nf
    _ ≤ |f x - f y| * |g x| + |f y| * |g x - g y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (Kf * dist x y) * Mg.toNNReal + Mf.toNNReal * (Kg * dist x y) := by
        gcongr
        · exact (hgM x hx).trans hMg
        · exact (hfM y hy).trans hMf
    _ = ↑(Kf * Mg.toNNReal + Mf.toNNReal * Kg) * dist x y := by push_cast; ring

end Calculus

/-! ### Picone with the cosine supersolution -/

section Picone

variable {F : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}

/-- `tan' = 1 + tan²`, in the form used for the Riccati variable `P = -k tan (k (x - c))`. -/
private theorem hasDerivAt_neg_mul_tan {k c x : ℝ} (hx : |k * (x - c)| < π / 2) :
    HasDerivAt (fun y ↦ -(k * tan (k * (y - c))))
      (-(k ^ 2 * (1 + tan (k * (x - c)) ^ 2))) x := by
  have hcos : 0 < cos (k * (x - c)) := cos_pos_of_mem_Ioo (abs_lt.1 hx)
  have hlin : HasDerivAt (fun y ↦ k * (y - c)) k x := by
    simpa using ((hasDerivAt_id x).sub_const c).const_mul k
  have h := ((Real.hasDerivAt_tan hcos.ne').comp x hlin).const_mul k |>.neg
  convert h using 1
  · funext y; simp only [Pi.neg_apply, Function.comp_apply]
  rw [tan_eq_sin_div_cos]
  field_simp
  have := sin_sq_add_cos_sq (k * (x - c))
  linear_combination (-k ^ 2) * this

/-- **One-dimensional Picone inequality** (with the supersolution
`g = cos (k (x - c))` and `P = g'/g`). If `F` is Lipschitz on `[a, b]` and `|k (x - c)| < π/2` on
`[a, b]`, then
`k² ∫_a^b F² ≤ ∫_a^b F'² + F(b)² k tan (k (b - c)) - F(a)² k tan (k (a - c))`. -/
theorem integral_sq_le_of_tan (hab : a ≤ b) (hF : LipschitzOnWith K F (Icc a b)) {k c : ℝ}
    (hk : ∀ x ∈ Icc a b, |k * (x - c)| < π / 2) :
    k ^ 2 * ∫ x in a..b, F x ^ 2 ≤ (∫ x in a..b, deriv F x ^ 2) +
      F b ^ 2 * (k * tan (k * (b - c))) - F a ^ 2 * (k * tan (k * (a - c))) := by
  set P : ℝ → ℝ := fun y ↦ -(k * tan (k * (y - c)))
  have hF' : LipschitzOnWith K F (uIcc a b) := by rwa [uIcc_of_le hab]
  have hFac := hF'.absolutelyContinuousOnInterval
  have hFF := hFac.fun_mul hFac
  have hP : ContDiffOn ℝ 1 P (uIcc a b) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    refine ContDiffAt.contDiffWithinAt ?_
    have hcos : cos (k * (x - c)) ≠ 0 := (cos_pos_of_mem_Ioo (abs_lt.1 (hk x hx))).ne'
    have hlin : ContDiffAt ℝ 1 (fun y ↦ k * (y - c)) x := by fun_prop
    exact (contDiffAt_const.mul ((Real.contDiffAt_tan.2 hcos).comp x hlin)).neg
  have hPac := hP.absolutelyContinuousOnInterval
  have hIBP := hFF.integral_deriv_mul_eq_sub hPac
  have hint₁ : IntervalIntegrable
      (fun x ↦ deriv (fun y ↦ F y * F y) x * P x + F x * F x * deriv P x) volume a b :=
    (hFF.intervalIntegrable_deriv.mul_continuousOn hPac.continuousOn).add
      (hPac.intervalIntegrable_deriv.continuousOn_mul hFF.continuousOn)
  have hFc : ContinuousOn F (uIcc a b) := hFac.continuousOn
  have hsq : IntervalIntegrable (fun x ↦ F x ^ 2) volume a b := (hFc.pow 2).intervalIntegrable
  have hdsq := intervalIntegrable_deriv_sq_of_lipschitzOnWith hab hF
  have hint₂ : IntervalIntegrable (fun x ↦ deriv F x ^ 2 - k ^ 2 * F x ^ 2) volume a b :=
    hdsq.sub (hsq.const_mul _)
  have hmono : ∫ x in a..b, deriv (fun y ↦ F y * F y) x * P x + F x * F x * deriv P x ≤
      ∫ x in a..b, deriv F x ^ 2 - k ^ 2 * F x ^ 2 := by
    refine intervalIntegral.integral_mono_ae_restrict hab hint₁ hint₂ ?_
    have hdiff := hFac.ae_differentiableAt
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hdiff,
      ae_restrict_of_ae (volume.ae_ne a), ae_restrict_of_ae (volume.ae_ne b)]
      with x hx hxd hxa hxb
    have hxu : x ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hFd := (hxd hxu).hasDerivAt
    have hFF' : HasDerivAt (fun y ↦ F y * F y) (deriv F x * F x + F x * deriv F x) x :=
      hFd.mul hFd
    rw [hFF'.deriv, (hasDerivAt_neg_mul_tan (hk x hx)).deriv]
    simp only [P]
    nlinarith [sq_nonneg (deriv F x + k * tan (k * (x - c)) * F x)]
  rw [hIBP, intervalIntegral.integral_sub hdsq (hsq.const_mul _),
    intervalIntegral.integral_const_mul] at hmono
  simp only [P] at hmono
  linarith

/-- If `k₀ > 0` and `k² A ≤ B` for every `k ∈ [0, k₀)`, then `k₀² A ≤ B`. -/
private theorem sq_mul_le_of_forall_lt {k₀ A B : ℝ} (hk₀ : 0 < k₀)
    (h : ∀ k, 0 ≤ k → k < k₀ → k ^ 2 * A ≤ B) : k₀ ^ 2 * A ≤ B := by
  have ht : Tendsto (fun k : ℝ ↦ k ^ 2 * A) (𝓝[<] k₀) (𝓝 (k₀ ^ 2 * A)) :=
    (((continuous_pow 2).mul continuous_const).tendsto k₀).mono_left nhdsWithin_le_nhds
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsLT hk₀] with k hk
  exact h k hk.1.le hk.2

/-- **Wirtinger inequality, Dirichlet condition on the right.** If `F` is Lipschitz on `[a, b]`
and `F b = 0`, then `(π / 2(b - a))² ∫_a^b F² ≤ ∫_a^b F'²`. -/
theorem integral_sq_le_integral_deriv_sq_of_right (hab : a < b)
    (hF : LipschitzOnWith K F (Icc a b)) (hFb : F b = 0) :
    (π / (2 * (b - a))) ^ 2 * ∫ x in a..b, F x ^ 2 ≤ ∫ x in a..b, deriv F x ^ 2 := by
  have hba : 0 < b - a := sub_pos.2 hab
  refine sq_mul_le_of_forall_lt (by positivity) fun k hk0 hk ↦ ?_
  have h := integral_sq_le_of_tan hab.le hF (k := k) (c := a) fun x hx ↦ by
    rw [abs_of_nonneg (mul_nonneg hk0 (sub_nonneg.2 hx.1))]
    calc k * (x - a) ≤ k * (b - a) := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hk0
      _ < π / (2 * (b - a)) * (b - a) := mul_lt_mul_of_pos_right hk hba
      _ = π / 2 := by field_simp
  simpa [hFb] using h

/-- **Wirtinger inequality, Dirichlet condition on the left.** If `F` is Lipschitz on `[a, b]`
and `F a = 0`, then `(π / 2(b - a))² ∫_a^b F² ≤ ∫_a^b F'²`. -/
theorem integral_sq_le_integral_deriv_sq_of_left (hab : a < b)
    (hF : LipschitzOnWith K F (Icc a b)) (hFa : F a = 0) :
    (π / (2 * (b - a))) ^ 2 * ∫ x in a..b, F x ^ 2 ≤ ∫ x in a..b, deriv F x ^ 2 := by
  have hba : 0 < b - a := sub_pos.2 hab
  refine sq_mul_le_of_forall_lt (by positivity) fun k hk0 hk ↦ ?_
  have h := integral_sq_le_of_tan hab.le hF (k := k) (c := b) fun x hx ↦ by
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hk0 (sub_nonpos.2 hx.2))]
    calc -(k * (x - b)) ≤ k * (b - a) := by nlinarith [hx.1]
      _ < π / (2 * (b - a)) * (b - a) := mul_lt_mul_of_pos_right hk hba
      _ = π / 2 := by field_simp
  simpa [hFa] using h

/-- **Wirtinger inequality, Dirichlet conditions at both ends.** If `F` is Lipschitz on `[a, b]`
and `F a = F b = 0`, then `(π / (b - a))² ∫_a^b F² ≤ ∫_a^b F'²`. -/
theorem integral_sq_le_integral_deriv_sq_of_left_right (hab : a < b)
    (hF : LipschitzOnWith K F (Icc a b)) (hFa : F a = 0) (hFb : F b = 0) :
    (π / (b - a)) ^ 2 * ∫ x in a..b, F x ^ 2 ≤ ∫ x in a..b, deriv F x ^ 2 := by
  set m := (a + b) / 2
  have ham : a < m := by simp only [m]; linarith
  have hmb : m < b := by simp only [m]; linarith
  have h₁ := integral_sq_le_integral_deriv_sq_of_left ham
    (hF.mono (Icc_subset_Icc le_rfl hmb.le)) hFa
  have h₂ := integral_sq_le_integral_deriv_sq_of_right hmb
    (hF.mono (Icc_subset_Icc ham.le le_rfl)) hFb
  have hk₁ : π / (2 * (m - a)) = π / (b - a) := by simp only [m]; ring_nf
  have hk₂ : π / (2 * (b - m)) = π / (b - a) := by simp only [m]; ring_nf
  rw [hk₁] at h₁
  rw [hk₂] at h₂
  have hL₁ := hF.mono (Icc_subset_Icc le_rfl hmb.le)
  have hL₂ := hF.mono (Icc_subset_Icc ham.le le_rfl)
  have hi₁ : IntervalIntegrable (fun x ↦ F x ^ 2) volume a m :=
    (hL₁.continuousOn.pow 2).intervalIntegrable_of_Icc (μ := volume) ham.le
  have hi₂ : IntervalIntegrable (fun x ↦ F x ^ 2) volume m b :=
    (hL₂.continuousOn.pow 2).intervalIntegrable_of_Icc (μ := volume) hmb.le
  have hd₁ := intervalIntegrable_deriv_sq_of_lipschitzOnWith ham.le hL₁
  have hd₂ := intervalIntegrable_deriv_sq_of_lipschitzOnWith hmb.le hL₂
  rw [← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂,
    ← intervalIntegral.integral_add_adjacent_intervals hd₁ hd₂, mul_add]
  linarith

end Picone

/-! ### The characteristic exponent -/

section CharExponent

variable {d : ℕ}

/-- `κ_d` is monotone. -/
theorem charExponent_mono : Monotone (charExponent d) := fun x y h ↦ by
  unfold charExponent
  gcongr

/-- `κ_d(β (β + d - 2)) = β` when `d - 2 + 2β ≥ 0`. -/
theorem charExponent_mul_add_sub_two {β : ℝ} (h : 0 ≤ (d : ℝ) - 2 + 2 * β) :
    charExponent d (β * (β + d - 2)) = β := by
  unfold charExponent
  rw [show ((d : ℝ) - 2) ^ 2 + 4 * (β * (β + d - 2)) = ((d : ℝ) - 2 + 2 * β) ^ 2 by ring,
    Real.sqrt_sq h]
  ring

end CharExponent

/-! ### The radial cap eigenvalue: basic properties -/

section Cap

variable {d : ℕ} {θ θ' : ℝ}

/-- Cap Rayleigh quotients on `[0, θ] ⊆ [0, π]` are nonnegative. -/
theorem capRayleigh_nonneg (hθ : 0 ≤ θ) (hθπ : θ ≤ π) (F : ℝ → ℝ) : 0 ≤ capRayleigh d θ F := by
  refine div_nonneg (intervalIntegral.integral_nonneg hθ fun φ hφ ↦ ?_)
    (intervalIntegral.integral_nonneg hθ fun φ hφ ↦ ?_) <;>
    exact mul_nonneg (sq_nonneg _)
      (pow_nonneg (sin_nonneg_of_nonneg_of_le_pi hφ.1 (hφ.2.trans hθπ)) _)

theorem bddBelow_capRayleigh (hθ : 0 ≤ θ) (hθπ : θ ≤ π) :
    BddBelow (capRayleigh d θ '' {F | IsCapAdmissible θ F}) :=
  ⟨0, by rintro _ ⟨F, -, rfl⟩; exact capRayleigh_nonneg hθ hθπ F⟩

theorem capEigenvalue_nonneg (hθ : 0 ≤ θ) (hθπ : θ ≤ π) : 0 ≤ capEigenvalue d θ :=
  Real.sInf_nonneg (by rintro _ ⟨F, -, rfl⟩; exact capRayleigh_nonneg hθ hθπ F)

/-- For `θ > 0` the function `φ ↦ θ - φ` is admissible, so the set of cap Rayleigh quotients is
nonempty. -/
theorem nonempty_capRayleigh (hθ : 0 < θ) :
    (capRayleigh d θ '' {F | IsCapAdmissible θ F}).Nonempty := by
  refine ⟨_, fun φ ↦ θ - φ, ⟨⟨1, ?_⟩, by simp, ⟨0, ⟨le_rfl, hθ.le⟩, by simp [hθ.ne']⟩⟩, rfl⟩
  refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y ↦ ?_)
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
    show θ - x - (θ - y) = -(x - y) by ring, abs_neg]

/-- The denominator of the cap Rayleigh quotient of an admissible function is positive. -/
theorem integral_sq_mul_sin_pow_pos (hθ : 0 < θ) (hθπ : θ ≤ π) {F : ℝ → ℝ}
    (hF : IsCapAdmissible θ F) (n : ℕ) : 0 < ∫ φ in 0..θ, F φ ^ 2 * sin φ ^ n := by
  obtain ⟨K, hK⟩ := hF.lipschitzOn
  have hcont : ContinuousOn F (Icc 0 θ) := hK.continuousOn
  set U := Ioo 0 θ ∩ F ⁻¹' {0}ᶜ
  have hUo : IsOpen U :=
    (hcont.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_compl_singleton
  have hUne : U.Nonempty := by
    by_contra hU
    rw [not_nonempty_iff_eq_empty] at hU
    have h0 : EqOn F 0 (Ioo 0 θ) := fun φ hφ ↦ by
      by_contra hne
      have : φ ∈ U := ⟨hφ, hne⟩
      rw [hU] at this
      exact this
    have h0' : EqOn F 0 (Icc 0 θ) :=
      h0.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
        (by rw [closure_Ioo hθ.ne])
    obtain ⟨φ₀, hφ₀, hne⟩ := hF.exists_ne_zero
    exact hne (h0' hφ₀)
  have hint : IntervalIntegrable (fun φ ↦ F φ ^ 2 * sin φ ^ n) volume 0 θ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hθ.le]
    exact (hcont.pow 2).mul (continuous_sin.pow _).continuousOn
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' ?_ hint]
  · refine ⟨hθ, lt_of_lt_of_le (hUo.measure_pos volume hUne) (measure_mono ?_)⟩
    rintro φ ⟨hφ, hFφ⟩
    refine ⟨?_, Ioo_subset_Ioc_self hφ⟩
    have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans_le hθπ)
    simp only [Function.mem_support]
    exact mul_ne_zero (pow_ne_zero 2 hFφ) (pow_ne_zero _ hs.ne')
  · rw [uIoc_of_le hθ.le]
    refine ae_restrict_of_forall_mem measurableSet_Ioc fun φ hφ ↦ ?_
    exact mul_nonneg (sq_nonneg _)
      (pow_nonneg (sin_nonneg_of_nonneg_of_le_pi hφ.1.le (hφ.2.trans hθπ)) _)

/-- **Lower bounds for `Λ_d`.** If `μ ∫_0^θ F² sin^{d-2} ≤ ∫_0^θ F'² sin^{d-2}` for every admissible
`F`, then `μ ≤ Λ_d(θ)`. -/
theorem le_capEigenvalue_of_forall (hθ : 0 < θ) (hθπ : θ ≤ π) {μ : ℝ}
    (h : ∀ F, IsCapAdmissible θ F → μ * (∫ φ in 0..θ, F φ ^ 2 * sin φ ^ (d - 2)) ≤
      ∫ φ in 0..θ, deriv F φ ^ 2 * sin φ ^ (d - 2)) : μ ≤ capEigenvalue d θ := by
  refine le_csInf (nonempty_capRayleigh hθ) ?_
  rintro _ ⟨F, hF, rfl⟩
  rw [capRayleigh, le_div_iff₀ (integral_sq_mul_sin_pow_pos hθ hθπ hF _)]
  exact h F hF

/-- An integral over `0..θ'` of a function vanishing on `(θ, ∞)` is an integral over `0..θ`. -/
private theorem intervalIntegral_eq_of_eqOn_of_vanish {G H : ℝ → ℝ} (hθ : 0 ≤ θ)
    (hθθ' : θ ≤ θ') (hG : ∀ φ, θ < φ → G φ = 0) (hGH : EqOn G H (Ioo 0 θ)) :
    ∫ φ in 0..θ', G φ = ∫ φ in 0..θ, H φ := by
  rw [intervalIntegral.integral_of_le (hθ.trans hθθ'), intervalIntegral.integral_of_le hθ,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
      (Ioo_subset_Ioo_right hθθ')]
  · exact setIntegral_congr_fun measurableSet_Ioo hGH
  filter_upwards [volume.ae_ne θ] with φ hφ hmem
  exact hG φ (lt_of_le_of_ne (not_lt.1 fun h ↦ hmem.2 ⟨hmem.1.1, h⟩) (Ne.symm hφ))

/-- **`Λ_d` is nonincreasing**, by extending an admissible function
by zero. For `0 < θ ≤ θ' ≤ π`, `Λ_d(θ') ≤ Λ_d(θ)`. -/
theorem capEigenvalue_le_of_le (hθ : 0 < θ) (hθθ' : θ ≤ θ') (hθ' : θ' ≤ π) :
    capEigenvalue d θ' ≤ capEigenvalue d θ := by
  refine le_csInf (nonempty_capRayleigh hθ) ?_
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨K, hK⟩ := hF.lipschitzOn
  set G : ℝ → ℝ := fun φ ↦ F (min φ θ)
  have hGF : ∀ φ, φ ≤ θ → G φ = F φ := fun φ h ↦ by simp [G, min_eq_left h]
  have hG0 : ∀ φ, θ ≤ φ → G φ = 0 := fun φ h ↦ by
    simp [G, min_eq_right h, hF.apply_right_eq_zero]
  have hdG : ∀ φ ∈ Ioo 0 θ, deriv G φ = deriv F φ := fun φ hφ ↦
    Filter.EventuallyEq.deriv_eq (by
      filter_upwards [Iio_mem_nhds hφ.2] with x hx using hGF x (le_of_lt hx))
  have hdG0 : ∀ φ, θ < φ → deriv G φ = 0 := fun φ hφ ↦ by
    rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)), deriv_const]
    filter_upwards [lt_mem_nhds hφ] with x hx using hG0 x hx.le
  have hGadm : IsCapAdmissible θ' G := by
    refine ⟨⟨K * 1, hK.comp (LipschitzWith.id.min_const θ).lipschitzOnWith ?_⟩, hG0 θ' hθθ', ?_⟩
    · intro φ hφ
      exact ⟨le_min hφ.1 hθ.le, min_le_right _ _⟩
    · obtain ⟨φ, hφ, hne⟩ := hF.exists_ne_zero
      exact ⟨φ, ⟨hφ.1, hφ.2.trans hθθ'⟩, by rwa [hGF φ hφ.2]⟩
  have hR : capRayleigh d θ' G = capRayleigh d θ F := by
    rw [capRayleigh, capRayleigh,
      intervalIntegral_eq_of_eqOn_of_vanish (H := fun φ ↦ deriv F φ ^ 2 * sin φ ^ (d - 2))
        hθ.le hθθ' (fun φ hφ ↦ by simp [hdG0 φ hφ])
        (fun φ hφ ↦ by simp [hdG φ hφ]),
      intervalIntegral_eq_of_eqOn_of_vanish (H := fun φ ↦ F φ ^ 2 * sin φ ^ (d - 2))
        hθ.le hθθ' (fun φ hφ ↦ by simp [hG0 φ hφ.le])
        (fun φ hφ ↦ by simp [hGF φ hφ.2.le])]
  rw [← hR]
  exact csInf_le (bddBelow_capRayleigh (hθ.le.trans hθθ') hθ') ⟨G, hGadm, rfl⟩

/-- `ᾱ_d` is nonincreasing on `(0, π]`. -/
theorem capExponent_le_of_le (hθ : 0 < θ) (hθθ' : θ ≤ θ') (hθ' : θ' ≤ π) :
    capExponent d θ' ≤ capExponent d θ :=
  charExponent_mono (capEigenvalue_le_of_le hθ hθθ' hθ')

end Cap

/-! ### Explicit caps: `d = 2` and `d = 4` -/

section Explicit

variable {θ : ℝ}

/-- **`Λ₂(θ) ≥ (π / 2θ)²`** (`d = 2`). -/
theorem capEigenvalue_two_ge (hθ : 0 < θ) (hθπ : θ ≤ π) :
    (π / (2 * θ)) ^ 2 ≤ capEigenvalue 2 θ := by
  refine le_capEigenvalue_of_forall hθ hθπ fun F hF ↦ ?_
  obtain ⟨K, hK⟩ := hF.lipschitzOn
  simpa using integral_sq_le_integral_deriv_sq_of_right hθ hK hF.apply_right_eq_zero

/-- **The substitution `G = F sin`.** If `F` is Lipschitz on `[0, θ]` and `F θ = 0`, then
`∫_0^θ F'² sin² = ∫_0^θ (F sin)'² - ∫_0^θ (F sin)²`. -/
theorem integral_deriv_sq_mul_sin_sq {F : ℝ → ℝ} {K : ℝ≥0} (hθ : 0 ≤ θ)
    (hF : LipschitzOnWith K F (Icc 0 θ)) (hFθ : F θ = 0) :
    ∫ φ in 0..θ, deriv F φ ^ 2 * sin φ ^ 2 =
      (∫ φ in 0..θ, deriv (fun x ↦ F x * sin x) φ ^ 2) - ∫ φ in 0..θ, (F φ * sin φ) ^ 2 := by
  have hF' : LipschitzOnWith K F (uIcc 0 θ) := by rwa [uIcc_of_le hθ]
  have hFac := hF'.absolutelyContinuousOnInterval
  have hFF := hFac.fun_mul hFac
  have hSac : AbsolutelyContinuousOnInterval (fun x ↦ sin x * cos x) 0 θ :=
    (show ContDiff ℝ 1 (fun x ↦ sin x * cos x) by fun_prop).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hIBP : ∫ x in 0..θ, (deriv (fun y ↦ F y * F y) x * (sin x * cos x) +
      F x * F x * deriv (fun y ↦ sin y * cos y) x) = 0 := by
    rw [hFF.integral_deriv_mul_eq_sub hSac]
    simp [hFθ]
  have hint₁ : IntervalIntegrable (fun x ↦ deriv (fun y ↦ F y * F y) x * (sin x * cos x) +
      F x * F x * deriv (fun y ↦ sin y * cos y) x) volume 0 θ :=
    (hFF.intervalIntegrable_deriv.mul_continuousOn hSac.continuousOn).add
      (hSac.intervalIntegrable_deriv.continuousOn_mul hFF.continuousOn)
  have hFc : ContinuousOn F (uIcc 0 θ) := hFac.continuousOn
  have hint₂ : IntervalIntegrable (fun φ ↦ deriv F φ ^ 2 * sin φ ^ 2) volume 0 θ :=
    (intervalIntegrable_deriv_sq_of_lipschitzOnWith hθ hF).mul_continuousOn
      (continuous_sin.pow 2).continuousOn
  have hint₃ : IntervalIntegrable (fun φ ↦ (F φ * sin φ) ^ 2) volume 0 θ :=
    ((hFc.mul continuous_sin.continuousOn).pow 2).intervalIntegrable
  have hcongr : ∫ φ in 0..θ, deriv (fun x ↦ F x * sin x) φ ^ 2 =
      ∫ φ in 0..θ, ((deriv F φ ^ 2 * sin φ ^ 2 +
        (deriv (fun y ↦ F y * F y) φ * (sin φ * cos φ) +
          F φ * F φ * deriv (fun y ↦ sin y * cos y) φ)) + (F φ * sin φ) ^ 2) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hFac.ae_differentiableAt] with x hxd hx
    have hFd := (hxd (uIoc_subset_uIcc hx)).hasDerivAt
    have h₁ : HasDerivAt (fun y ↦ F y * F y) (deriv F x * F x + F x * deriv F x) x :=
      hFd.mul hFd
    have h₂ : HasDerivAt (fun y ↦ F y * sin y) (deriv F x * sin x + F x * cos x) x :=
      hFd.mul (hasDerivAt_sin x)
    have h₃ : HasDerivAt (fun y ↦ sin y * cos y) (cos x * cos x + sin x * -sin x) x :=
      (hasDerivAt_sin x).mul (hasDerivAt_cos x)
    rw [h₁.deriv, h₂.deriv, h₃.deriv]
    ring
  rw [hcongr, intervalIntegral.integral_add (hint₂.add hint₁) hint₃,
    intervalIntegral.integral_add hint₂ hint₁, hIBP]
  ring

/-- **`Λ₄(θ) ≥ π²/θ² - 1`** (`d = 4`). -/
theorem capEigenvalue_four_ge (hθ : 0 < θ) (hθπ : θ ≤ π) :
    (π / θ) ^ 2 - 1 ≤ capEigenvalue 4 θ := by
  refine le_capEigenvalue_of_forall hθ hθπ fun F hF ↦ ?_
  obtain ⟨K, hK⟩ := hF.lipschitzOn
  have hFθ := hF.apply_right_eq_zero
  have h4 : (4 : ℕ) - 2 = 2 := rfl
  have hsq : ∫ φ in 0..θ, F φ ^ 2 * sin φ ^ 2 = ∫ φ in 0..θ, (F φ * sin φ) ^ 2 := by
    congr 1; funext φ; ring
  rw [h4, integral_deriv_sq_mul_sin_sq hθ.le hK hFθ, hsq]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hK.continuousOn
  obtain ⟨K', hK'⟩ := exists_lipschitzOnWith_mul hK (lipschitzWith_sin.lipschitzOnWith)
    (fun x hx ↦ by simpa using hM x hx) (fun x _ ↦ abs_sin_le_one x)
  have hW := integral_sq_le_integral_deriv_sq_of_left_right hθ hK' (by simp) (by simp [hFθ])
  rw [sub_zero] at hW
  linarith

/-- `ᾱ₂(θ) ≥ π / 2θ`. -/
theorem capExponent_two_ge (hθ : 0 < θ) (hθπ : θ ≤ π) : π / (2 * θ) ≤ capExponent 2 θ := by
  have h := charExponent_mono (d := 2) (capEigenvalue_two_ge hθ hθπ)
  rwa [show (π / (2 * θ)) ^ 2 = π / (2 * θ) * (π / (2 * θ) + ((2 : ℕ) : ℝ) - 2) by
      push_cast; ring,
    charExponent_mul_add_sub_two (by push_cast; positivity)] at h

/-- `ᾱ₄(θ) ≥ π / θ - 1` (from `(κ₄(λ) + 1)² = λ + 1`). -/
theorem capExponent_four_ge (hθ : 0 < θ) (hθπ : θ ≤ π) : π / θ - 1 ≤ capExponent 4 θ := by
  have h := charExponent_mono (d := 4) (capEigenvalue_four_ge hθ hθπ)
  have h1 : 1 ≤ π / θ := (one_le_div hθ).2 hθπ
  rwa [show (π / θ) ^ 2 - 1 = (π / θ - 1) * (π / θ - 1 + ((4 : ℕ) : ℝ) - 2) by
      push_cast; ring,
    charExponent_mul_add_sub_two (by push_cast; linarith)] at h

/-- `π / θ + π / (π - θ) ≥ 4` for `θ ∈ (0, π)` (AM–HM). -/
private theorem four_le_pi_div_add_pi_div (hθ : 0 < θ) (hθπ : θ < π) :
    4 ≤ π / θ + π / (π - θ) := by
  have h1 : 0 < π - θ := sub_pos.2 hθπ
  rw [div_add_div _ _ hθ.ne' h1.ne', le_div_iff₀ (mul_pos hθ h1)]
  nlinarith [sq_nonneg (π - 2 * θ)]

/-- **The cap inequality in dimension two**: `ᾱ₂(θ) + ᾱ₂(π - θ) ≥ 2` for `θ ∈ (0, π)`. -/
theorem capInequality_two : ∀ θ ∈ Ioo 0 π, 2 ≤ capExponent 2 θ + capExponent 2 (π - θ) := by
  rintro θ ⟨hθ, hθπ⟩
  have h₁ := capExponent_two_ge hθ hθπ.le
  have h₂ := capExponent_two_ge (sub_pos.2 hθπ) (sub_le_self π hθ.le)
  have h := four_le_pi_div_add_pi_div hθ hθπ
  have e₁ : π / (2 * θ) = π / θ / 2 := by rw [div_div, mul_comm]
  have e₂ : π / (2 * (π - θ)) = π / (π - θ) / 2 := by rw [div_div, mul_comm]
  linarith

/-- **The cap inequality in dimension four**: `ᾱ₄(θ) + ᾱ₄(π - θ) ≥ 2` for `θ ∈ (0, π)`. -/
theorem capInequality_four : ∀ θ ∈ Ioo 0 π, 2 ≤ capExponent 4 θ + capExponent 4 (π - θ) := by
  rintro θ ⟨hθ, hθπ⟩
  have h₁ := capExponent_four_ge hθ hθπ.le
  have h₂ := capExponent_four_ge (sub_pos.2 hθπ) (sub_le_self π hθ.le)
  have h := four_le_pi_div_add_pi_div hθ hθπ
  linarith

end Explicit

end EllipticBernoulli

end
