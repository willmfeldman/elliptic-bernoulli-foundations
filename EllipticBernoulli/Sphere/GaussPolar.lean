/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Defs
public import EllipticBernoulli.Sobolev.GaussianPoincare.Weight
import EllipticBernoulli.Sphere.HomogeneousExt
import EllipticBernoulli.Harmonic.Polar
import EllipticBernoulli.Sobolev.Lipschitz
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The Gaussian polar identity

Let `d ≥ 2`, `β > 0`, and let `g` be Lipschitz on the unit sphere `𝕊 ⊆ ℝᵈ`. Its `β`-homogeneous
extension `V(x) = |x|^β ĝ(x)` (`homogExt β g`) satisfies

* `∫ V² e^{-|x|²/2} dx = M_{2β+d-1} ∫_𝕊 g²` (`integral_homogExt_sq_mul_gaussWeight`),
* `∫ |∇V|² e^{-|x|²/2} dx = M_{2β+d-3} (β² ∫_𝕊 g² + ∫_𝕊 |∇_𝕊 g|²)`
  (`integral_norm_gradient_homogExt_sq_mul_gaussWeight`),

where `M_k = ∫_0^∞ t^k e^{-t²/2} dt` (`gaussMoment k`) satisfies `M_{k+2} = (k + 1) M_k`
(`gaussMoment_add_two`). Hence the Gaussian Rayleigh quotient of `V` is
`(β² + R(g)) / (2β + d - 2)`. We work with the unnormalized weight `gaussWeight`, so no Gaussian
normalization appears.

Both identities are instances of `integral_mul_gaussWeight_of_homogeneous`: if `F ≥ 0` satisfies
`F(tω) = t^γ a(ω)` for every `t > 0` and `σ`-a.e. `ω`, then
`∫ F e^{-|x|²/2} = M_{γ+d-1} ∫_𝕊 a` (polar coordinates, Tonelli). The same lemma gives the
integrability of `|x|^k e^{-|x|²/2}` for `k > -d` (`integrable_norm_rpow_mul_gaussWeight`).
-/

open Set Filter Topology MeasureTheory Metric Real Module InnerProductSpace
open scoped ENNReal NNReal Gradient

public section

namespace EllipticBernoulli

/-! ### Gaussian moments -/

/-- The Gaussian moment `M_k = ∫_0^∞ t^k e^{-t²/2} dt`. -/
@[expose] noncomputable def gaussMoment (k : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), t ^ k * exp (-(t ^ 2 / 2))

private theorem neg_sq_div_two (t : ℝ) : -(t ^ 2 / 2) = -(1 / 2) * t ^ 2 := by ring

theorem integrableOn_gaussMoment {k : ℝ} (hk : -1 < k) :
    IntegrableOn (fun t : ℝ ↦ t ^ k * exp (-(t ^ 2 / 2))) (Ioi 0) := by
  simp_rw [neg_sq_div_two]
  exact integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num) hk

theorem gaussMoment_eq_Gamma {k : ℝ} (hk : -1 < k) :
    gaussMoment k = (1 / 2 : ℝ) ^ (-(k + 1) / 2) * (1 / 2) * Gamma ((k + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := k) (b := 1 / 2) two_pos hk
    (by norm_num)
  simp_rw [Real.rpow_two] at h
  rw [gaussMoment]
  simp_rw [neg_sq_div_two]
  exact h

theorem gaussMoment_pos {k : ℝ} (hk : -1 < k) : 0 < gaussMoment k := by
  rw [gaussMoment_eq_Gamma hk]
  have : 0 < (k + 1) / 2 := by linarith
  have := Gamma_pos_of_pos this
  positivity

/-- **The moment recursion** `M_{k+2} = (k + 1) M_k`. -/
theorem gaussMoment_add_two {k : ℝ} (hk : -1 < k) :
    gaussMoment (k + 2) = (k + 1) * gaussMoment k := by
  rw [gaussMoment_eq_Gamma (by linarith), gaussMoment_eq_Gamma hk,
    show (k + 2 + 1) / 2 = (k + 1) / 2 + 1 by ring,
    Gamma_add_one (by linarith : (k + 1) / 2 ≠ 0),
    show -(k + 2 + 1) / 2 = -(k + 1) / 2 + -1 by ring,
    rpow_add (by norm_num : (0 : ℝ) < 1 / 2), rpow_neg_one]
  ring

theorem ofReal_gaussMoment {k : ℝ} (hk : -1 < k) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ k * exp (-(t ^ 2 / 2))) =
      ENNReal.ofReal (gaussMoment k) := by
  rw [gaussMoment, ofReal_integral_eq_lintegral_ofReal (integrableOn_gaussMoment hk)]
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦
    mul_nonneg (rpow_nonneg (le_of_lt ht) _) (exp_pos _).le

/-! ### Polar coordinates against the Gaussian weight -/

/-- If `f ≥ 0` is a.e. strongly measurable and `∫⁻ f = c` with `c ≥ 0`, then `f` is integrable
and `∫ f = c`. -/
theorem integrable_and_integral_eq_of_lintegral_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : AEStronglyMeasurable f μ) {c : ℝ}
    (hc : 0 ≤ c) (h : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal c) :
    Integrable f μ ∧ ∫ x, f x ∂μ = c := by
  refine ⟨⟨hfm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hf0), h]
    exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf0) hfm, h, ENNReal.toReal_ofReal hc]

variable {d : ℕ}

private theorem norm_smul_coe {t : ℝ} (ht : 0 < t) (ω : sphere (0 : E d) 1) :
    ‖t • (ω : E d)‖ = t := by
  rw [norm_smul, norm_eq_of_mem_sphere ω, mul_one, Real.norm_of_nonneg ht.le]

/-- **Homogeneous functions against the Gaussian weight.** Let `d ≥ 1`, let `F ≥ 0` be measurable
on `ℝᵈ`, and let `a ≥ 0` be integrable on the sphere. If `γ > -d` and, for every `t > 0`,
`F(tω) = t^γ a(ω)` for `σ`-a.e. `ω`, then `F e^{-|x|²/2}` is integrable and
`∫ F e^{-|x|²/2} = M_{γ+d-1} ∫_𝕊 a`. -/
theorem integral_mul_gaussWeight_of_homogeneous (hd : 1 ≤ d) {F : E d → ℝ} (hFm : Measurable F)
    (hF0 : ∀ x, 0 ≤ F x) {a : sphere (0 : E d) 1 → ℝ} (ha0 : ∀ ω, 0 ≤ a ω)
    (hai : Integrable a (volume : Measure (E d)).toSphere) {γ : ℝ} (hγ : -(d : ℝ) < γ)
    (hF : ∀ t : ℝ, 0 < t → ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
      F (t • (ω : E d)) = t ^ γ * a ω) :
    Integrable (fun x ↦ F x * gaussWeight x) ∧
      ∫ x, F x * gaussWeight x =
        gaussMoment (γ + d - 1) * ∫ ω, a ω ∂(volume : Measure (E d)).toSphere := by
  have := nontrivial_E hd
  set σ := (volume : Measure (E d)).toSphere
  set A := ∫ ω, a ω ∂σ
  have hA : 0 ≤ A := integral_nonneg ha0
  have hk : -1 < γ + d - 1 := by linarith
  have hM := (gaussMoment_pos hk).le
  refine integrable_and_integral_eq_of_lintegral_eq
    (fun x ↦ mul_nonneg (hF0 x) (gaussWeight_nonneg x))
    (hFm.mul continuous_gaussWeight.measurable).aestronglyMeasurable (mul_nonneg hM hA) ?_
  rw [lintegral_eq_lintegral_Ioi_lintegral_toSphere
    (h := fun x ↦ ENNReal.ofReal (F x * gaussWeight x))
    ((hFm.mul continuous_gaussWeight.measurable).ennreal_ofReal), finrank_euclideanSpace_fin]
  have hinner : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ (d - 1)) * ∫⁻ ω, ENNReal.ofReal (F (t • (ω : E d)) *
        gaussWeight (t • (ω : E d))) ∂σ =
      ENNReal.ofReal (t ^ (γ + d - 1) * exp (-(t ^ 2 / 2))) * ENNReal.ofReal A := by
    intro t ht
    have ht : 0 < t := ht
    have hcongr : ∫⁻ ω, ENNReal.ofReal (F (t • (ω : E d)) * gaussWeight (t • (ω : E d))) ∂σ =
        ∫⁻ ω, ENNReal.ofReal (t ^ γ * exp (-(t ^ 2 / 2))) * ENNReal.ofReal (a ω) ∂σ := by
      refine lintegral_congr_ae ?_
      filter_upwards [hF t ht] with ω hω
      rw [hω, gaussWeight, norm_smul_coe ht ω, ← ENNReal.ofReal_mul
        (mul_nonneg (rpow_nonneg ht.le _) (exp_pos _).le)]
      ring_nf
    rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← ofReal_integral_eq_lintegral_ofReal hai (ae_of_all _ ha0), ← mul_assoc,
      ← ENNReal.ofReal_mul (pow_nonneg ht.le _)]
    congr 2
    rw [← rpow_natCast, Nat.cast_sub hd, Nat.cast_one, show γ + d - 1 = (d - 1 : ℝ) + γ by ring,
      rpow_add ht]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    ofReal_gaussMoment hk, ← ENNReal.ofReal_mul hM]

/-- `|x|^k e^{-|x|²/2}` is integrable on `ℝᵈ` for `k > -d`. -/
theorem integrable_norm_rpow_mul_gaussWeight (hd : 1 ≤ d) {k : ℝ} (hk : -(d : ℝ) < k) :
    Integrable (fun x : E d ↦ ‖x‖ ^ k * gaussWeight x) :=
  (integral_mul_gaussWeight_of_homogeneous hd (F := fun x ↦ ‖x‖ ^ k)
    (measurable_norm.pow_const k) (fun x ↦ rpow_nonneg (norm_nonneg x) k) (a := fun _ ↦ 1)
    (fun _ ↦ zero_le_one) (integrable_const 1) hk
    (fun t ht ↦ ae_of_all _ fun ω ↦ by simp [norm_smul_coe ht ω])).1

/-! ### The `β`-homogeneous extension -/

/-- The `β`-homogeneous extension `x ↦ |x|^β ĝ(x)` of a function `g` on the unit sphere. -/
@[expose] noncomputable def homogExt (β : ℝ) (g : sphere (0 : E d) 1 → ℝ) (x : E d) : ℝ :=
  ‖x‖ ^ β * homogExt0 g x

theorem homogExt_smul_coe (β : ℝ) (g : sphere (0 : E d) 1 → ℝ) {t : ℝ} (ht : 0 < t)
    (ω : sphere (0 : E d) 1) : homogExt β g (t • (ω : E d)) = t ^ β * g ω := by
  rw [homogExt, norm_smul_coe ht ω, homogExt0_smul g ht, homogExt0_coe]

/-- For Lipschitz `g`, `ĝ` is measurable. -/
theorem measurable_homogExt0 {g : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    Measurable (homogExt0 g) :=
  measurable_of_continuousOn_compl_singleton 0 (locallyLipschitzOn_homogExt0 hg).continuousOn

theorem measurable_homogExt {g : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (β : ℝ) : Measurable (homogExt β g) :=
  (measurable_norm.pow_const β).mul (measurable_homogExt0 hg)

/-- The gradient of `x ↦ |x|^β` at `x ≠ 0`, as a functional: `β |x|^{β-2} ⟨x, ·⟩`. -/
private theorem hasFDerivAt_norm_rpow_of_ne_zero {x : E d} (hx : x ≠ 0) (β : ℝ) :
    HasFDerivAt (fun y : E d ↦ ‖y‖ ^ β)
      ((β / 2 * (‖x‖ ^ 2) ^ (β / 2 - 1)) • (2 • innerSL ℝ x)) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).rpow_const (p := β / 2)
    (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.2 hx)))
  convert h using 1
  funext y
  rw [← rpow_natCast, ← rpow_mul (norm_nonneg y)]
  norm_num
  ring_nf

/-- **The gradient of `|x|^β ĝ` on rays.** If `ĝ` is differentiable at `ω ∈ 𝕊` and `t > 0`, then
`|∇V(tω)|² = t^{2β-2} (β² g(ω)² + |∇ĝ(ω)|²)` for `V = homogExt β g`. -/
theorem norm_gradient_homogExt_smul_sq (β : ℝ) (g : sphere (0 : E d) 1 → ℝ) {t : ℝ} (ht : 0 < t)
    (ω : sphere (0 : E d) 1) (hg : DifferentiableAt ℝ (homogExt0 g) (ω : E d)) :
    ‖∇ (homogExt β g) (t • (ω : E d))‖ ^ 2 =
      t ^ (2 * β - 2) * (β ^ 2 * g ω ^ 2 + ‖∇ (homogExt0 g) (ω : E d)‖ ^ 2) := by
  set x := t • (ω : E d)
  have hxn : ‖x‖ = t := norm_smul_coe ht ω
  have hx : x ≠ 0 := by rw [← norm_ne_zero_iff, hxn]; exact ht.ne'
  have hgx : DifferentiableAt ℝ (homogExt0 g) x :=
    (differentiableAt_homogExt0_smul_iff g ht _).2 hg
  have hn := hasFDerivAt_norm_rpow_of_ne_zero hx β
  set c := β / 2 * (‖x‖ ^ 2) ^ (β / 2 - 1)
  have hinner : (toDual ℝ (E d)).symm (innerSL ℝ x) = x := by
    have : innerSL ℝ x = toDual ℝ (E d) x := by ext y; simp [toDual_apply_apply]
    rw [this, LinearIsometryEquiv.symm_apply_apply]
  have hgrad : ∇ (homogExt β g) x =
      ‖x‖ ^ β • ∇ (homogExt0 g) x + (homogExt0 g x * (2 * c)) • x := by
    have hW : homogExt β g = fun y ↦ ‖y‖ ^ β * homogExt0 g y := rfl
    rw [hW, gradient, fderiv_fun_mul hn.differentiableAt hgx, hn.fderiv, map_add, map_smul,
      map_smul, map_smul, map_nsmul, hinner]
    simp only [gradient]
    module
  have horth : inner ℝ (∇ (homogExt0 g) x) x = 0 := inner_gradient_homogExt0_self g x
  have hgω : homogExt0 g x = g ω := by rw [homogExt0_smul g ht, homogExt0_coe]
  have hgr : ‖∇ (homogExt0 g) x‖ = t⁻¹ * ‖∇ (homogExt0 g) (ω : E d)‖ :=
    norm_gradient_homogExt0_smul g ht _
  rw [hgrad, norm_add_sq_real, inner_smul_left, inner_smul_right, horth]
  simp only [norm_smul, hxn, hgr, hgω, c, Real.norm_eq_abs, mul_zero, add_zero]
  rw [abs_of_nonneg (rpow_nonneg ht.le _)]
  have e1 : (t ^ 2) ^ (β / 2 - 1) = t ^ (β - 2) := by
    rw [← rpow_natCast, ← rpow_mul ht.le]; norm_num; ring_nf
  have e2 : t ^ β = t ^ (β - 1) * t := by
    rw [← rpow_add_one ht.ne']; ring_nf
  have e3 : t ^ (β - 2) = t ^ (β - 1) * t⁻¹ := by
    rw [← rpow_neg_one, ← rpow_add ht]; ring_nf
  have e4 : t ^ (2 * β - 2) = (t ^ (β - 1)) ^ 2 := by
    rw [← rpow_natCast, ← rpow_mul ht.le]; ring_nf
  rw [e1, e3, e2, e4, mul_pow _ t, sq_abs]
  field_simp
  ring

/-! ### The Gaussian polar identity -/

variable {β : ℝ} {g : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0}

private theorem integrable_sq_toSphere (hd : 1 ≤ d) (hg : LipschitzWith K g) :
    Integrable (fun ω ↦ g ω ^ 2) (volume : Measure (E d)).toSphere := by
  have := nontrivial_E hd
  obtain ⟨C, hC⟩ := (isCompact_univ.image hg.continuous).isBounded.exists_norm_le
  refine Integrable.of_bound (hg.continuous.pow 2).aestronglyMeasurable (C ^ 2)
    (ae_of_all _ fun ω ↦ ?_)
  have h := hC _ ⟨ω, mem_univ _, rfl⟩
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem integrable_norm_gradient_sq_toSphere (hg : LipschitzWith K g) :
    Integrable (fun ω : sphere (0 : E d) 1 ↦ ‖∇ (homogExt0 g) (ω : E d)‖ ^ 2)
      (volume : Measure (E d)).toSphere := by
  refine Integrable.of_bound
    (((measurable_gradient _).norm.pow_const 2).comp measurable_subtype_coe).aestronglyMeasurable
    ((4 * K) ^ 2) (ae_of_all _ fun ω ↦ ?_)
  rw [norm_pow, norm_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_homogExt0_le hg ω) 2

/-- **Gaussian polar identity, `L²` part.** For `d ≥ 1`, `β > 0`
and Lipschitz `g`, `V² e^{-|x|²/2}` is integrable and `∫ V² e^{-|x|²/2} = M_{2β+d-1} ∫_𝕊 g²`,
where `V = homogExt β g`. -/
theorem integral_homogExt_sq_mul_gaussWeight (hd : 1 ≤ d) (hβ : 0 < β) (hg : LipschitzWith K g) :
    Integrable (fun x ↦ homogExt β g x ^ 2 * gaussWeight x) ∧
      ∫ x, homogExt β g x ^ 2 * gaussWeight x = gaussMoment (2 * β + d - 1) * sphL2Sq g := by
  have h := integral_mul_gaussWeight_of_homogeneous hd (F := fun x ↦ homogExt β g x ^ 2)
    ((measurable_homogExt hg β).pow_const 2) (fun x ↦ sq_nonneg _) (a := fun ω ↦ g ω ^ 2)
    (fun ω ↦ sq_nonneg _) (integrable_sq_toSphere hd hg) (γ := 2 * β)
    (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
    (fun t ht ↦ ae_of_all _ fun ω ↦ by
      rw [homogExt_smul_coe β g ht, mul_pow, ← rpow_natCast, ← rpow_mul ht.le]
      ring_nf)
  exact ⟨h.1, h.2⟩

/-- **Gaussian polar identity, gradient part.** For `d ≥ 2`,
`β > 0` and Lipschitz `g`, `|∇V|² e^{-|x|²/2}` is integrable and
`∫ |∇V|² e^{-|x|²/2} = M_{2β+d-3} (β² ∫_𝕊 g² + ∫_𝕊 |∇_𝕊 g|²)`, where `V = homogExt β g`. -/
theorem integral_norm_gradient_homogExt_sq_mul_gaussWeight (hd : 2 ≤ d) (hβ : 0 < β)
    (hg : LipschitzWith K g) :
    Integrable (fun x ↦ ‖∇ (homogExt β g) x‖ ^ 2 * gaussWeight x) ∧
      ∫ x, ‖∇ (homogExt β g) x‖ ^ 2 * gaussWeight x =
        gaussMoment (2 * β + d - 3) * (β ^ 2 * sphL2Sq g + sphDirichlet g) := by
  have hd1 : 1 ≤ d := by omega
  have hint := ((integrable_sq_toSphere hd1 hg).const_mul (β ^ 2)).add
    (integrable_norm_gradient_sq_toSphere hg)
  have h := integral_mul_gaussWeight_of_homogeneous hd1
    (F := fun x ↦ ‖∇ (homogExt β g) x‖ ^ 2) ((measurable_gradient _).norm.pow_const 2)
    (fun x ↦ sq_nonneg _) (a := fun ω ↦ β ^ 2 * g ω ^ 2 + ‖∇ (homogExt0 g) (ω : E d)‖ ^ 2)
    (fun ω ↦ by positivity) hint (γ := 2 * β - 2)
    (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    (fun t ht ↦ by
      filter_upwards [ae_differentiableAt_homogExt0 hd1 hg] with ω hω
      exact norm_gradient_homogExt_smul_sq β g ht ω hω)
  refine ⟨h.1, ?_⟩
  rw [h.2, integral_add ((integrable_sq_toSphere hd1 hg).const_mul _)
    (integrable_norm_gradient_sq_toSphere hg), integral_const_mul]
  congr 1
  ring_nf

end EllipticBernoulli

end
