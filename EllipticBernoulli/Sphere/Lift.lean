/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.GaussPolar
import EllipticBernoulli.Sphere.HomogeneousExt
import EllipticBernoulli.Sphere.CapODE
import EllipticBernoulli.Sphere.Measure
import EllipticBernoulli.Common.Calculus
import EllipticBernoulli.Sobolev.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lifting test functions to a higher-dimensional sphere

Write `ℝ^{n+1} = ℝ × ℝⁿ ∋ z = (s, x)` with `x = tailE z` the last `n` coordinates. For
`Γ ⊆ 𝕊^{n-1}` the *lifted set* `Γ↑ = liftSet Γ ⊆ 𝕊ⁿ` consists of the `ω` with `tailE ω ≠ 0` and
`tailE ω / |tailE ω| ∈ Γ`. The lifting lemma is
`κ_{n+1}(λ₁(Γ↑)) ≤ κ_n(R(f))` for every `f` admissible for `Γ` with `R(f) > 0`
(`charExponent_sphEigenvalue_liftSet_le`).

## Proof

Let `β = κ_n(R(f)) > 0`, `V = |x|^β f̂(x)` on `ℝⁿ` and `Ṽ(s, x) = V(x)`. By the Gaussian polar
identity (`GaussPolar.lean`) and Fubini in `z = (s, x)`, the Gaussian Rayleigh quotient of `Ṽ` on
`ℝ^{n+1}` equals that of `V` on `ℝⁿ`, which is `β`. The trace of `Ṽ` on `𝕊ⁿ` need not be Lipschitz
near `{x = 0}`, so we use the approximations
`g_ε(ω) = max(|x|, ε)^{β-1} · |x| f̂(x)` (`liftApprox`), whose `β`-homogeneous extensions are
`W_ε(z) = |x| f̂(x) · max(|x|, ε|z|)^{β-1}`. As `ε → 0⁺`, dominated convergence gives
`∫ W_ε² e^{-|z|²/2} → ∫ Ṽ² e^{-|z|²/2}` and `∫ |∇W_ε|² e^{-|z|²/2} → ∫ |∇Ṽ|² e^{-|z|²/2}`, with
dominating functions `C |z|^{2β}` and `C (|x|^{2β-2} + |z|^{2β-2})` times the weight. The Gaussian
polar identity in dimension `n + 1` then gives `R(g_ε) → β (β + n - 1)`.

Comparing spherical Rayleigh quotients through Gaussian Rayleigh quotients of homogeneous
extensions, and adding variables on which the extension does not depend, is the device of
Beck–Jerison (arXiv:2102.00571, Proposition 1.3). We lift one dimension at a time, which is all
that the dimension-monotonicity argument needs.

## References

* T. Beck, D. Jerison, *The Friedland–Hayman inequality and Caffarelli's contraction theorem*,
  arXiv:2102.00571.
-/

open Set Filter Topology MeasureTheory Metric Real Module InnerProductSpace
open scoped ENNReal NNReal Gradient

public section

namespace EllipticBernoulli

variable {n : ℕ}

/-! ### Splitting `ℝ^{n+1} = ℝ × ℝⁿ` -/

/-- The last `n` coordinates `ℝ^{n+1} → ℝⁿ`. -/
noncomputable def tailCLM (n : ℕ) : E (n + 1) →L[ℝ] E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ WithLp.toLp 2 fun i ↦ z.ofLp i.succ
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The embedding `ℝⁿ → ℝ^{n+1}`, `x ↦ (0, x)`. -/
noncomputable def consCLM (n : ℕ) : E n →L[ℝ] E (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x ↦ WithLp.toLp 2 (Fin.cons 0 x.ofLp)
      map_add' := fun x y ↦ by
        ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      map_smul' := fun c x ↦ by
        ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp }

@[simp] theorem tailCLM_apply_ofLp (z : E (n + 1)) (i : Fin n) :
    (tailCLM n z).ofLp i = z.ofLp i.succ := by
  simp only [tailCLM]; rfl

@[simp] theorem tailCLM_consCLM (x : E n) : tailCLM n (consCLM n x) = x := by
  ext i; simp only [tailCLM, consCLM]; rfl

theorem norm_sq_eq_head_add_tail (z : E (n + 1)) :
    ‖z‖ ^ 2 = z.ofLp 0 ^ 2 + ‖tailCLM n z‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp

theorem norm_tailCLM_le (z : E (n + 1)) : ‖tailCLM n z‖ ≤ ‖z‖ := by
  have h := norm_sq_eq_head_add_tail z
  nlinarith [norm_nonneg z, norm_nonneg (tailCLM n z), sq_nonneg (z.ofLp 0)]

theorem norm_consCLM (x : E n) : ‖consCLM n x‖ = ‖x‖ := by
  have h := norm_sq_eq_head_add_tail (consCLM n x)
  simp only [tailCLM_consCLM] at h
  have h0 : (consCLM n x).ofLp 0 = 0 := by simp [consCLM]
  rw [h0] at h
  nlinarith [norm_nonneg (consCLM n x), norm_nonneg x, sq_nonneg (‖consCLM n x‖ - ‖x‖),
    sq_nonneg (‖consCLM n x‖ + ‖x‖)]

theorem opNorm_tailCLM_le : ‖tailCLM n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z ↦ by simpa using norm_tailCLM_le z

theorem opNorm_consCLM_le : ‖consCLM n‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by simp [norm_consCLM]

/-- Splitting `E (n + 1) = ℝ × E n` (Tonelli). -/
private theorem lintegral_head_tail {H : ℝ × E n → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z : E (n + 1), H (z.ofLp 0, tailCLM n z) = ∫⁻ s : ℝ, ∫⁻ y : E n, H (s, y) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin (n + 1))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin n))
  have hΦ := (h3.comp h2).comp h1
  rw [← Measure.volume_eq_prod] at hΦ
  have := hΦ.lintegral_comp hH
  rw [← lintegral_prod _ hH.aemeasurable, ← Measure.volume_eq_prod, ← this]
  rfl

/-- The one-dimensional Gaussian mass `c₁ = ∫_ℝ e^{-s²/2} ds`. -/
noncomputable def gaussMassOne : ℝ := ∫ s : ℝ, exp (-(1 / 2) * s ^ 2)

theorem gaussMassOne_pos : 0 < gaussMassOne := by
  rw [gaussMassOne, integral_gaussian]
  positivity

private theorem lintegral_gaussOne :
    ∫⁻ s : ℝ, ENNReal.ofReal (exp (-(1 / 2) * s ^ 2)) = ENNReal.ofReal gaussMassOne := by
  rw [gaussMassOne, ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq (by norm_num))
    (ae_of_all _ fun _ ↦ (exp_pos _).le)]

/-- **Fubini for functions of the last `n` coordinates.** -/
theorem lintegral_comp_tailCLM_mul_gaussWeight {H : E n → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ z : E (n + 1), H (tailCLM n z) * ENNReal.ofReal (gaussWeight z) =
      ENNReal.ofReal gaussMassOne * ∫⁻ x : E n, H x * ENNReal.ofReal (gaussWeight x) := by
  have hG : Measurable fun p : ℝ × E n ↦
      H p.2 * (ENNReal.ofReal (exp (-(1 / 2) * p.1 ^ 2)) * ENNReal.ofReal (gaussWeight p.2)) :=
    (hH.comp measurable_snd).mul
      ((by fun_prop : Measurable fun p : ℝ × E n ↦ ENNReal.ofReal (exp (-(1 / 2) * p.1 ^ 2))).mul
        (continuous_gaussWeight.measurable.comp measurable_snd).ennreal_ofReal)
  have hw : ∀ z : E (n + 1), ENNReal.ofReal (gaussWeight z) =
      ENNReal.ofReal (exp (-(1 / 2) * z.ofLp 0 ^ 2)) *
        ENNReal.ofReal (gaussWeight (tailCLM n z)) := by
    intro z
    rw [← ENNReal.ofReal_mul (exp_pos _).le, gaussWeight, gaussWeight, ← exp_add,
      norm_sq_eq_head_add_tail]
    ring_nf
  simp_rw [hw]
  rw [lintegral_head_tail (H := fun p : ℝ × E n ↦
    H p.2 * (ENNReal.ofReal (exp (-(1 / 2) * p.1 ^ 2)) * ENNReal.ofReal (gaussWeight p.2))) hG,
    ← lintegral_gaussOne]
  have hinner : ∀ s : ℝ, ∫⁻ y : E n,
      H y * (ENNReal.ofReal (exp (-(1 / 2) * s ^ 2)) * ENNReal.ofReal (gaussWeight y)) =
      ENNReal.ofReal (exp (-(1 / 2) * s ^ 2)) *
        ∫⁻ y : E n, H y * ENNReal.ofReal (gaussWeight y) := by
    intro s
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr fun y ↦ by ring
  simp_rw [hinner]
  exact lintegral_mul_const _ (by fun_prop)

/-- **Fubini for functions of the last `n` coordinates** (Bochner version, `h ≥ 0`). -/
theorem integral_comp_tailCLM_mul_gaussWeight {h : E n → ℝ} (hm : Measurable h)
    (h0 : ∀ x, 0 ≤ h x) (hi : Integrable fun x ↦ h x * gaussWeight x) :
    Integrable (fun z : E (n + 1) ↦ h (tailCLM n z) * gaussWeight z) ∧
      ∫ z, h (tailCLM n z) * gaussWeight z = gaussMassOne * ∫ x, h x * gaussWeight x := by
  refine integrable_and_integral_eq_of_lintegral_eq
    (fun z ↦ mul_nonneg (h0 _) (gaussWeight_nonneg z))
    ((hm.comp (tailCLM n).continuous.measurable).mul
      continuous_gaussWeight.measurable).aestronglyMeasurable
    (mul_nonneg gaussMassOne_pos.le
      (integral_nonneg fun x ↦ mul_nonneg (h0 x) (gaussWeight_nonneg x))) ?_
  have e₁ : ∀ z : E (n + 1), ENNReal.ofReal (h (tailCLM n z) * gaussWeight z) =
      ENNReal.ofReal (h (tailCLM n z)) * ENNReal.ofReal (gaussWeight z) :=
    fun z ↦ ENNReal.ofReal_mul (h0 _)
  have e₂ : ∀ x : E n, ENNReal.ofReal (h x * gaussWeight x) =
      ENNReal.ofReal (h x) * ENNReal.ofReal (gaussWeight x) :=
    fun x ↦ ENNReal.ofReal_mul (h0 _)
  simp_rw [e₁]
  rw [lintegral_comp_tailCLM_mul_gaussWeight hm.ennreal_ofReal,
    ENNReal.ofReal_mul gaussMassOne_pos.le,
    ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun x ↦ mul_nonneg (h0 x) (gaussWeight_nonneg x))]
  simp_rw [e₂]

/-- For `n ≥ 1`, `tailCLM n z ≠ 0` for a.e. `z`. -/
theorem ae_tailCLM_ne_zero (hn : 1 ≤ n) : ∀ᵐ z : E (n + 1), tailCLM n z ≠ 0 := by
  set S := LinearMap.ker ((tailCLM n : E (n + 1) →L[ℝ] E n) : E (n + 1) →ₗ[ℝ] E n)
  have hS : S ≠ ⊤ := by
    intro h
    set x : E n := EuclideanSpace.single ⟨0, hn⟩ 1
    have hx : x ≠ 0 := by
      intro h0
      have := congrArg (fun v : E n ↦ v.ofLp ⟨0, hn⟩) h0
      simp [x] at this
    have : consCLM n x ∈ S := h ▸ Submodule.mem_top
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, tailCLM_consCLM] at this
    exact hx this
  have h0 := Measure.addHaar_submodule (volume : Measure (E (n + 1))) S hS
  rw [ae_iff]
  convert h0 using 2
  ext z
  simp [S]

/-- **Gradients of functions of the last `n` coordinates**:
`|∇(u ∘ tail)(z)| = |∇u(tail z)|`. -/
theorem norm_gradient_comp_tailCLM (u : E n → ℝ) (z : E (n + 1)) :
    ‖∇ (fun z ↦ u (tailCLM n z)) z‖ = ‖∇ u (tailCLM n z)‖ := by
  rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv]
  by_cases hu : DifferentiableAt ℝ u (tailCLM n z)
  · have hc : fderiv ℝ (fun z ↦ u (tailCLM n z)) z =
        (fderiv ℝ u (tailCLM n z)).comp (tailCLM n) := by
      rw [show (fun z ↦ u (tailCLM n z)) = u ∘ tailCLM n from rfl,
        fderiv_comp z hu (tailCLM n).differentiableAt, ContinuousLinearMap.fderiv]
    rw [hc]
    refine le_antisymm ?_ ?_
    · calc _ ≤ ‖fderiv ℝ u (tailCLM n z)‖ * ‖tailCLM n‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) opNorm_tailCLM_le
    · have e : fderiv ℝ u (tailCLM n z) =
          ((fderiv ℝ u (tailCLM n z)).comp (tailCLM n)).comp (consCLM n) := by
        ext x; simp
      calc ‖fderiv ℝ u (tailCLM n z)‖
          = ‖((fderiv ℝ u (tailCLM n z)).comp (tailCLM n)).comp (consCLM n)‖ := by rw [← e]
        _ ≤ ‖(fderiv ℝ u (tailCLM n z)).comp (tailCLM n)‖ * ‖consCLM n‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) opNorm_consCLM_le
  · have hu' : ¬DifferentiableAt ℝ (fun z ↦ u (tailCLM n z)) z := by
      intro hd
      apply hu
      set A : E n → E (n + 1) := fun x ↦ consCLM n x + (z - consCLM n (tailCLM n z))
      have hA : DifferentiableAt ℝ A (tailCLM n z) := by fun_prop
      have hz : A (tailCLM n z) = z := by simp [A]
      have hd' : DifferentiableAt ℝ (fun z ↦ u (tailCLM n z)) (A (tailCLM n z)) := by
        rw [hz]; exact hd
      have h := hd'.comp (tailCLM n z) hA
      have e : (fun z ↦ u (tailCLM n z)) ∘ A = u := by
        funext x; simp [A, map_add, map_sub]
      rwa [e] at h
    rw [fderiv_zero_of_not_differentiableAt hu', fderiv_zero_of_not_differentiableAt hu]
    simp

/-! ### The lifted set -/

/-- The lift `Γ↑ ⊆ 𝕊ⁿ` of `Γ ⊆ 𝕊^{n-1}`: the `ω` whose last `n` coordinates are a positive
multiple of a point of `Γ`. -/
def liftSet (Γ : Set (sphere (0 : E n) 1)) : Set (sphere (0 : E (n + 1)) 1) :=
  {ω | ∃ γ ∈ Γ, ∃ r : ℝ, 0 < r ∧ tailCLM n ω = r • (γ : E n)}

private theorem norm_inv_smul_self {x : E n} (hx : x ≠ 0) : ‖‖x‖⁻¹ • x‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- `ω ∈ Γ↑` iff `tail ω ≠ 0` and `tail ω / |tail ω| ∈ Γ`. -/
theorem mem_liftSet_iff {Γ : Set (sphere (0 : E n) 1)} {ω : sphere (0 : E (n + 1)) 1} :
    ω ∈ liftSet Γ ↔ ∃ h : tailCLM n ω ≠ 0,
      (⟨‖tailCLM n ω‖⁻¹ • tailCLM n ω, by
        rw [mem_sphere_zero_iff_norm]; exact norm_inv_smul_self h⟩ : sphere (0 : E n) 1) ∈ Γ := by
  constructor
  · rintro ⟨γ, hγ, r, hr, he⟩
    have hγn : ‖(γ : E n)‖ = 1 := norm_eq_of_mem_sphere γ
    have hn : ‖tailCLM n ω‖ = r := by rw [he, norm_smul, hγn, mul_one, Real.norm_of_nonneg hr.le]
    have h0 : tailCLM n ω ≠ 0 := by rw [← norm_ne_zero_iff, hn]; exact hr.ne'
    refine ⟨h0, ?_⟩
    convert hγ using 1
    ext1
    simp only
    rw [hn, he, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · rintro ⟨h0, hΓ⟩
    refine ⟨_, hΓ, ‖tailCLM n ω‖, norm_pos_iff.2 h0, ?_⟩
    simp only
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]

theorem liftSet_disjoint {Γ₁ Γ₂ : Set (sphere (0 : E n) 1)} (h : Disjoint Γ₁ Γ₂) :
    Disjoint (liftSet Γ₁) (liftSet Γ₂) := by
  rw [Set.disjoint_left]
  intro ω h₁ h₂
  obtain ⟨h0, hΓ₁⟩ := mem_liftSet_iff.1 h₁
  obtain ⟨_, hΓ₂⟩ := mem_liftSet_iff.1 h₂
  exact Set.disjoint_left.1 h hΓ₁ hΓ₂

theorem liftSet_nonempty {Γ : Set (sphere (0 : E n) 1)} (h : Γ.Nonempty) :
    (liftSet Γ).Nonempty := by
  obtain ⟨γ, hγ⟩ := h
  have hγ1 : consCLM n γ ∈ sphere (0 : E (n + 1)) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_consCLM]
    exact norm_eq_of_mem_sphere γ
  refine ⟨⟨consCLM n γ, hγ1⟩, γ, hγ, 1, one_pos, ?_⟩
  simp

theorem isOpen_liftSet {Γ : Set (sphere (0 : E n) 1)} (hΓ : IsOpen Γ) : IsOpen (liftSet Γ) := by
  obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hΓ
  rw [isOpen_iff_mem_nhds]
  intro ω₀ hω₀
  obtain ⟨h0, hΓ₀⟩ := mem_liftSet_iff.1 hω₀
  set T : sphere (0 : E (n + 1)) 1 → E n := fun ω ↦ tailCLM n ω
  have hT : Continuous T := (tailCLM n).continuous.comp continuous_subtype_val
  set φ : sphere (0 : E (n + 1)) 1 → E n := fun ω ↦ ‖T ω‖⁻¹ • T ω
  have hφ : ContinuousAt φ ω₀ :=
    ((hT.norm.continuousAt).inv₀ (norm_ne_zero_iff.2 h0)).smul hT.continuousAt
  have h₁ : {ω | T ω ≠ 0} ∈ 𝓝 ω₀ := (isOpen_ne_fun hT continuous_const).mem_nhds h0
  have h₂ : φ ⁻¹' O ∈ 𝓝 ω₀ := hφ.preimage_mem_nhds (hO.mem_nhds hΓ₀)
  filter_upwards [h₁, h₂] with ω hω hωO
  exact mem_liftSet_iff.2 ⟨hω, hωO⟩

/-! ### Lipschitz helpers -/

/-- The product of two bounded Lipschitz functions is Lipschitz. -/
private theorem exists_lipschitzWith_mul {X : Type*} [PseudoMetricSpace X] {u v : X → ℝ}
    {Ku Kv : ℝ≥0} (hu : LipschitzWith Ku u) (hv : LipschitzWith Kv v) {Mu Mv : ℝ}
    (huM : ∀ x, |u x| ≤ Mu) (hvM : ∀ x, |v x| ≤ Mv) :
    ∃ K, LipschitzWith K fun x ↦ u x * v x := by
  refine ⟨Ku * Mv.toNNReal + Mu.toNNReal * Kv, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have h1 := hu.dist_le_mul x y
  have h2 := hv.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have hMv : Mv ≤ Mv.toNNReal := Real.le_coe_toNNReal Mv
  have hMu : Mu ≤ Mu.toNNReal := Real.le_coe_toNNReal Mu
  have hd : 0 ≤ dist x y := dist_nonneg
  calc |u x * v x - u y * v y| = |(u x - u y) * v x + u y * (v x - v y)| := by ring_nf
    _ ≤ |u x - u y| * |v x| + |u y| * |v x - v y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (Ku * dist x y) * Mv.toNNReal + Mu.toNNReal * (Kv * dist x y) := by
        gcongr
        · exact (hvM x).trans hMv
        · exact (huM y).trans hMu
    _ = ↑(Ku * Mv.toNNReal + Mu.toNNReal * Kv) * dist x y := by push_cast; ring

/-- `‖x/|x| - y/|y|‖ ≤ 2 ‖x - y‖ / |y|`. -/
private theorem norm_normalize_sub_le' {x y : E n} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖y‖ := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have e : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y = ‖y‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • x := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_inv, norm_norm, Real.norm_eq_abs,
    show ‖x‖⁻¹ - ‖y‖⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) by field_simp, abs_div,
    abs_of_pos (mul_pos hxn hyn)]
  have h := abs_norm_sub_norm_le y x
  rw [norm_sub_rev y x] at h
  have : |‖y‖ - ‖x‖| / (‖x‖ * ‖y‖) * ‖x‖ = |‖y‖ - ‖x‖| / ‖y‖ := by field_simp
  rw [this]
  calc ‖y‖⁻¹ * ‖x - y‖ + |‖y‖ - ‖x‖| / ‖y‖ ≤ ‖y‖⁻¹ * ‖x - y‖ + ‖x - y‖ / ‖y‖ := by gcongr
    _ = 2 * ‖x - y‖ / ‖y‖ := by field_simp; ring

/-- `ĝ` is bounded by any bound of `g`. -/
theorem abs_homogExt0_le {f : sphere (0 : E n) 1 → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ω, |f ω| ≤ M) (x : E n) : |homogExt0 f x| ≤ M := by
  by_cases hx : x = 0
  · simp [hx, hM0]
  · rw [homogExt0_of_ne_zero f hx]; exact hM _

theorem homogExt_one_apply (f : sphere (0 : E n) 1 → ℝ) (x : E n) :
    homogExt 1 f x = ‖x‖ * homogExt0 f x := by
  simp [homogExt, rpow_one]

/-- The `1`-homogeneous extension `|x| f̂(x)` of a bounded Lipschitz `f` is Lipschitz. -/
theorem lipschitzWith_homogExt_one {f : sphere (0 : E n) 1 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ ω, |f ω| ≤ M) :
    LipschitzWith (M.toNNReal + 2 * K) (homogExt 1 f) := by
  have hb := abs_homogExt0_le hM0 hM
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, dist_eq_norm, homogExt_one_apply, homogExt_one_apply]
  push_cast
  rw [Real.coe_toNNReal _ hM0]
  have hK : (0 : ℝ) ≤ K := K.coe_nonneg
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [norm_zero, zero_mul, sub_zero, abs_mul, abs_norm]
    refine le_trans (mul_le_mul_of_nonneg_left (hb x) (norm_nonneg x)) ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [norm_zero, zero_mul, zero_sub, abs_neg, abs_mul, abs_norm, norm_neg]
    refine le_trans (mul_le_mul_of_nonneg_left (hb y) (norm_nonneg y)) ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg y)
  have hdiff : |homogExt0 f x - homogExt0 f y| ≤ K * (2 * ‖x - y‖ / ‖y‖) := by
    rw [homogExt0_of_ne_zero f hx, homogExt0_of_ne_zero f hy]
    have h := hf.dist_le_mul
      ⟨‖x‖⁻¹ • x, by rw [mem_sphere_zero_iff_norm]; exact norm_inv_smul_self hx⟩
      ⟨‖y‖⁻¹ • y, by rw [mem_sphere_zero_iff_norm]; exact norm_inv_smul_self hy⟩
    rw [Real.dist_eq, Subtype.dist_eq, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_left (norm_normalize_sub_le' hx hy) hK)
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
  calc |‖x‖ * homogExt0 f x - ‖y‖ * homogExt0 f y|
      = |(‖x‖ - ‖y‖) * homogExt0 f x + ‖y‖ * (homogExt0 f x - homogExt0 f y)| := by ring_nf
    _ ≤ |‖x‖ - ‖y‖| * |homogExt0 f x| + ‖y‖ * |homogExt0 f x - homogExt0 f y| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_norm]
    _ ≤ ‖x - y‖ * M + ‖y‖ * (K * (2 * ‖x - y‖ / ‖y‖)) := by
        gcongr
        · exact abs_norm_sub_norm_le x y
        · exact hb x
    _ = (M + 2 * K) * ‖x - y‖ := by field_simp

theorem lipschitzWith_tailCLM : LipschitzWith 1 (tailCLM n) :=
  LipschitzWith.of_dist_le_mul fun z w ↦ by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    exact norm_tailCLM_le _

/-- A continuous real function on the unit sphere is bounded by some `M ≥ 0`. -/
private theorem exists_abs_le_of_continuous {d : ℕ} {u : sphere (0 : E d) 1 → ℝ}
    (hu : Continuous u) : ∃ M, 0 ≤ M ∧ ∀ ω, |u ω| ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_univ.image hu).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun ω ↦ (hC _ ⟨ω, mem_univ _, rfl⟩).trans (le_max_left _ _)⟩

/-! ### The approximations `g_ε` and their homogeneous extensions -/

variable {f : sphere (0 : E n) 1 → ℝ} {β ε : ℝ}

/-- The approximation `g_ε(ω) = |x| f̂(x) · max(|x|, ε)^{β-1}` on `𝕊ⁿ`, with `x = tail ω`. -/
noncomputable def liftApprox (β ε : ℝ) (f : sphere (0 : E n) 1 → ℝ)
    (ω : sphere (0 : E (n + 1)) 1) : ℝ :=
  homogExt 1 f (tailCLM n ω) * max ‖tailCLM n ω‖ ε ^ (β - 1)

/-- The `β`-homogeneous extension of `g_ε`: `W_ε(z) = |x| f̂(x) · max(|x|, ε |z|)^{β-1}`. -/
noncomputable def liftExt (β ε : ℝ) (f : sphere (0 : E n) 1 → ℝ) (z : E (n + 1)) : ℝ :=
  homogExt 1 f (tailCLM n z) * max ‖tailCLM n z‖ (ε * ‖z‖) ^ (β - 1)

theorem homogExt_smul (β : ℝ) (f : sphere (0 : E n) 1 → ℝ) {c : ℝ} (hc : 0 < c) (x : E n) :
    homogExt β f (c • x) = c ^ β * homogExt β f x := by
  rw [homogExt, homogExt, norm_smul, Real.norm_of_nonneg hc.le, mul_rpow hc.le (norm_nonneg _),
    homogExt0_smul f hc]
  ring

@[simp] theorem homogExt_zero (hβ : 0 < β) (f : sphere (0 : E n) 1 → ℝ) : homogExt β f 0 = 0 := by
  simp [homogExt, zero_rpow hβ.ne']

/-- `homogExt β g_ε = W_ε`. -/
theorem homogExt_liftApprox (hβ : 0 < β) : homogExt β (liftApprox β ε f) = liftExt β ε f := by
  funext z
  rcases eq_or_ne z 0 with rfl | hz
  · simp [liftExt, hβ]
  set r := ‖z‖ with hr_def
  have hr : 0 < r := norm_pos_iff.2 hz
  rw [homogExt, homogExt0_of_ne_zero _ hz, liftApprox, liftExt]
  simp only
  rw [map_smul, homogExt_smul 1 f (inv_pos.2 hr), norm_smul,
    Real.norm_of_nonneg (inv_nonneg.2 hr.le), ← hr_def]
  have hmax : max (r⁻¹ * ‖tailCLM n z‖) ε = r⁻¹ * max ‖tailCLM n z‖ (ε * r) := by
    rw [mul_max_of_nonneg _ _ (inv_nonneg.2 hr.le)]
    congr 1
    field_simp
  rw [hmax, mul_rpow (inv_nonneg.2 hr.le) (le_max_of_le_left (norm_nonneg _)), rpow_one]
  have h1 : r ^ β * r⁻¹ * r⁻¹ ^ (β - 1) = 1 := by
    rw [inv_rpow hr.le, rpow_sub_one hr.ne']
    have : 0 < r ^ β := rpow_pos_of_pos hr β
    field_simp
  calc r ^ β * (r⁻¹ * homogExt 1 f (tailCLM n z) *
        (r⁻¹ ^ (β - 1) * max ‖tailCLM n z‖ (ε * r) ^ (β - 1)))
      = homogExt 1 f (tailCLM n z) * max ‖tailCLM n z‖ (ε * r) ^ (β - 1) *
          (r ^ β * r⁻¹ * r⁻¹ ^ (β - 1)) := by ring
    _ = _ := by rw [h1, mul_one]

/-- For `0 < ε ≤ 1`, `g_ε` is Lipschitz. -/
theorem exists_lipschitzWith_liftApprox {K : ℝ≥0} (hf : LipschitzWith K f) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : ∃ K', LipschitzWith K' (liftApprox β ε f) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_continuous hf.continuous
  set T : sphere (0 : E (n + 1)) 1 → E n := fun ω ↦ tailCLM n ω
  have hT : LipschitzWith 1 T := by
    have := lipschitzWith_tailCLM.comp (LipschitzWith.subtype_val (sphere (0 : E (n + 1)) 1))
    rwa [mul_one] at this
  have hTn : ∀ ω, ‖T ω‖ ≤ 1 := fun ω ↦
    (norm_tailCLM_le _).trans (norm_eq_of_mem_sphere ω).le
  -- the first factor
  have hu := (lipschitzWith_homogExt_one hf hM0 hM).comp hT
  have huM : ∀ ω, |homogExt 1 f (T ω)| ≤ M := fun ω ↦ by
    rw [homogExt_one_apply, abs_mul, abs_norm]
    calc ‖T ω‖ * |homogExt0 f (T ω)| ≤ 1 * M :=
          mul_le_mul (hTn ω) (abs_homogExt0_le hM0 hM _) (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  -- the second factor
  have hm : LipschitzWith 1 fun ω ↦ max ‖T ω‖ ε := by
    simpa using (lipschitzWith_one_norm.comp hT).max_const ε
  have hmI : ∀ ω, max ‖T ω‖ ε ∈ Icc ε 1 := fun ω ↦
    ⟨le_max_right _ _, max_le (hTn ω) hε1⟩
  have hcd : ContDiffOn ℝ 1 (fun u : ℝ ↦ u ^ (β - 1)) (Icc ε 1) := fun u hu ↦
    (Real.contDiffAt_rpow_const_of_ne (hε.trans_le hu.1).ne').contDiffWithinAt
  obtain ⟨Kr, hKr⟩ := hcd.exists_lipschitzOnWith one_ne_zero (convex_Icc ε 1) isCompact_Icc
  have hv : LipschitzWith Kr fun ω ↦ max ‖T ω‖ ε ^ (β - 1) :=
    LipschitzWith.of_dist_le_mul fun ω ω' ↦ by
      refine (hKr.dist_le_mul _ (hmI ω) _ (hmI ω')).trans ?_
      have := hm.dist_le_mul ω ω'
      rw [NNReal.coe_one, one_mul] at this
      exact mul_le_mul_of_nonneg_left this Kr.coe_nonneg
  obtain ⟨C, -, hC⟩ := exists_abs_le_of_continuous hv.continuous
  exact exists_lipschitzWith_mul hu hv huM hC

/-- `g_ε` vanishes off `Γ↑` when `f` vanishes off `Γ`. -/
theorem liftApprox_eq_zero {Γ : Set (sphere (0 : E n) 1)} (hf : ∀ γ ∉ Γ, f γ = 0)
    {ω : sphere (0 : E (n + 1)) 1} (hω : ω ∉ liftSet Γ) : liftApprox β ε f ω = 0 := by
  suffices h : homogExt 1 f (tailCLM n ω) = 0 by rw [liftApprox, h, zero_mul]
  rw [homogExt_one_apply]
  by_cases h0 : tailCLM n ω = 0
  · rw [h0, norm_zero, zero_mul]
  · rw [homogExt0_of_ne_zero f h0, hf _ fun hΓ ↦ hω (mem_liftSet_iff.2 ⟨h0, hΓ⟩), mul_zero]

/-! ### Convergence of `W_ε` as `ε → 0⁺` -/

/-- Away from `{x = 0}`, `W_ε = Ṽ` near `z` for small `ε`. -/
theorem eventually_liftExt_eventuallyEq {z : E (n + 1)} (hz : tailCLM n z ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), liftExt β ε f =ᶠ[𝓝 z] fun z' ↦ homogExt β f (tailCLM n z') := by
  have hz0 : z ≠ 0 := fun h ↦ hz (by rw [h, map_zero])
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hc : 0 < ‖tailCLM n z‖ / ‖z‖ := div_pos (norm_pos_iff.2 hz) hzn
  filter_upwards [Ioo_mem_nhdsGT hc] with ε hε
  have hU : IsOpen {z' : E (n + 1) | ε * ‖z'‖ < ‖tailCLM n z'‖} :=
    isOpen_lt (continuous_const.mul continuous_norm) ((tailCLM n).continuous.norm)
  have hzU : ε * ‖z‖ < ‖tailCLM n z‖ := by
    have := hε.2
    rwa [lt_div_iff₀ hzn] at this
  filter_upwards [hU.mem_nhds hzU] with z' hz'
  have hpos : 0 < ‖tailCLM n z'‖ :=
    lt_of_le_of_lt (mul_nonneg hε.1.le (norm_nonneg _)) hz'
  rw [liftExt, max_eq_left hz'.le, homogExt_one_apply, homogExt]
  have : ‖tailCLM n z'‖ ^ β = ‖tailCLM n z'‖ * ‖tailCLM n z'‖ ^ (β - 1) := by
    rw [rpow_sub_one hpos.ne']; field_simp
  rw [this]
  ring

/-- **Gradient bound for `W_ε`.** For `0 < ε ≤ 1` and a.e. `z = (s, x)`,
`|∇W_ε(z)| ≤ C (|x|^{β-1} + |z|^{β-1})` with `C` independent of `ε`. -/
theorem ae_norm_gradient_liftExt_le (hn : 1 ≤ n) {K : ℝ≥0} (hf : LipschitzWith K f) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ ω, |f ω| ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᵐ z : E (n + 1), ‖∇ (liftExt β ε f) z‖ ≤
      (M * |β - 1| + (M.toNNReal + 2 * K : ℝ≥0)) *
        (‖tailCLM n z‖ ^ (β - 1) + ‖z‖ ^ (β - 1)) := by
  set Lh : ℝ≥0 := M.toNNReal + 2 * K
  set D : E (n + 1) → ℝ := fun z ↦ homogExt 1 f (tailCLM n z)
  set m : E (n + 1) → ℝ := fun z ↦ max ‖tailCLM n z‖ (ε * ‖z‖)
  have hD : LipschitzWith Lh D := by
    have := (lipschitzWith_homogExt_one hf hM0 hM).comp lipschitzWith_tailCLM
    rwa [mul_one] at this
  have hm : LipschitzWith 1 m := LipschitzWith.of_dist_le_mul fun z w ↦ by
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
    · refine (abs_norm_sub_norm_le _ _).trans ?_
      rw [← map_sub]; exact norm_tailCLM_le _
    · rw [← mul_sub, abs_mul, abs_of_pos hε]
      calc ε * |‖z‖ - ‖w‖| ≤ 1 * ‖z - w‖ :=
            mul_le_mul hε1 (abs_norm_sub_norm_le z w) (abs_nonneg _) zero_le_one
        _ = ‖z - w‖ := one_mul _
  have hDb : ∀ z, |D z| ≤ M * ‖tailCLM n z‖ := fun z ↦ by
    simp only [D]
    rw [homogExt_one_apply, abs_mul, abs_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_homogExt0_le hM0 hM _) (norm_nonneg _)
  filter_upwards [ae_tailCLM_ne_zero hn, hD.ae_differentiableAt, hm.ae_differentiableAt]
    with z hz hDd hmd
  have hTpos : 0 < ‖tailCLM n z‖ := norm_pos_iff.2 hz
  have hmT : ‖tailCLM n z‖ ≤ m z := le_max_left _ _
  have hmpos : 0 < m z := hTpos.trans_le hmT
  have hmz : m z ≤ ‖z‖ := max_le (norm_tailCLM_le z)
    (by nlinarith [norm_nonneg z] : ε * ‖z‖ ≤ ‖z‖)
  have hpow := hmd.hasFDerivAt.rpow_const (p := β - 1) (Or.inl hmpos.ne')
  have hprod : HasFDerivAt (fun z ↦ D z * m z ^ (β - 1))
      (D z • ((β - 1) * m z ^ (β - 1 - 1)) • fderiv ℝ m z + m z ^ (β - 1) • fderiv ℝ D z) z :=
    hDd.hasFDerivAt.mul hpow
  have hW : liftExt β ε f = fun z ↦ D z * m z ^ (β - 1) := rfl
  rw [hW, norm_gradient_eq_norm_fderiv, hprod.fderiv]
  have hfm : ‖fderiv ℝ m z‖ ≤ 1 := by simpa using norm_fderiv_le_of_lipschitz ℝ hm
  have hfD : ‖fderiv ℝ D z‖ ≤ Lh := norm_fderiv_le_of_lipschitz ℝ hD
  have hmm : m z * m z ^ (β - 1 - 1) = m z ^ (β - 1) := by
    rw [rpow_sub_one hmpos.ne']; field_simp
  have hbound : m z ^ (β - 1) ≤ ‖tailCLM n z‖ ^ (β - 1) + ‖z‖ ^ (β - 1) := by
    rcases le_total β 1 with hβ1 | hβ1
    · exact le_add_of_le_of_nonneg (rpow_le_rpow_of_nonpos hTpos hmT (by linarith))
        (rpow_nonneg (norm_nonneg _) _)
    · exact le_add_of_nonneg_of_le (rpow_nonneg (norm_nonneg _) _)
        (rpow_le_rpow hmpos.le hmz (by linarith))
  have hC : 0 ≤ M * |β - 1| + Lh := add_nonneg (mul_nonneg hM0 (abs_nonneg _)) Lh.coe_nonneg
  calc ‖D z • ((β - 1) * m z ^ (β - 1 - 1)) • fderiv ℝ m z + m z ^ (β - 1) • fderiv ℝ D z‖
      ≤ |D z| * (|β - 1| * m z ^ (β - 1 - 1) * ‖fderiv ℝ m z‖) +
          m z ^ (β - 1) * ‖fderiv ℝ D z‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_mul, abs_of_pos (rpow_pos_of_pos hmpos _), abs_of_pos (rpow_pos_of_pos hmpos _)]
    _ ≤ (M * m z) * (|β - 1| * m z ^ (β - 1 - 1) * 1) + m z ^ (β - 1) * Lh := by
        gcongr
        exact (hDb z).trans (mul_le_mul_of_nonneg_left hmT hM0)
    _ = (M * |β - 1| + Lh) * m z ^ (β - 1) := by
        rw [← hmm]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound hC

/-- **Value bound for `W_ε`.** For `0 < ε ≤ 1`, `|W_ε(z)| ≤ M |z|^β`. -/
theorem abs_liftExt_le (hβ : 0 < β) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ ω, |f ω| ≤ M)
    (hε1 : ε ≤ 1) (z : E (n + 1)) : |liftExt β ε f z| ≤ M * ‖z‖ ^ β := by
  rw [liftExt, homogExt_one_apply, abs_mul, abs_mul, abs_norm]
  set m := max ‖tailCLM n z‖ (ε * ‖z‖)
  rcases eq_or_ne (tailCLM n z) 0 with h0 | h0
  · rw [h0, norm_zero, zero_mul, zero_mul]
    exact mul_nonneg hM0 (rpow_nonneg (norm_nonneg _) _)
  have hTpos : 0 < ‖tailCLM n z‖ := norm_pos_iff.2 h0
  have hmT : ‖tailCLM n z‖ ≤ m := le_max_left _ _
  have hmpos : 0 < m := hTpos.trans_le hmT
  have hmz : m ≤ ‖z‖ := max_le (norm_tailCLM_le z) (by nlinarith [norm_nonneg z])
  rw [abs_of_pos (rpow_pos_of_pos hmpos _)]
  have h1 : ‖tailCLM n z‖ * m ^ (β - 1) ≤ m ^ β := by
    calc ‖tailCLM n z‖ * m ^ (β - 1) ≤ m * m ^ (β - 1) :=
          mul_le_mul_of_nonneg_right hmT (rpow_nonneg hmpos.le _)
      _ = m ^ β := by rw [rpow_sub_one hmpos.ne']; field_simp
  have h2 : m ^ β ≤ ‖z‖ ^ β := rpow_le_rpow hmpos.le hmz hβ.le
  calc ‖tailCLM n z‖ * |homogExt0 f (tailCLM n z)| * m ^ (β - 1)
      = |homogExt0 f (tailCLM n z)| * (‖tailCLM n z‖ * m ^ (β - 1)) := by ring
    _ ≤ M * ‖z‖ ^ β :=
        mul_le_mul (abs_homogExt0_le hM0 hM _) (h1.trans h2)
          (mul_nonneg (norm_nonneg _) (rpow_nonneg hmpos.le _)) hM0

/-! ### Dominated convergence -/

theorem measurable_liftExt {K : ℝ≥0} (hf : LipschitzWith K f) (β ε : ℝ) :
    Measurable (liftExt β ε f) :=
  ((measurable_homogExt hf 1).comp (tailCLM n).continuous.measurable).mul
    ((((tailCLM n).continuous.norm).max (continuous_const.mul continuous_norm)).measurable.pow_const
      _)

/-- `∫ W_ε² e^{-|z|²/2} → ∫ Ṽ² e^{-|z|²/2}` as `ε → 0⁺`. -/
theorem tendsto_integral_liftExt_sq (hn : 1 ≤ n) (hβ : 0 < β) {K : ℝ≥0} (hf : LipschitzWith K f)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ ω, |f ω| ≤ M) :
    Tendsto (fun ε ↦ ∫ z, liftExt β ε f z ^ 2 * gaussWeight z) (𝓝[>] 0)
      (𝓝 (∫ z, homogExt β f (tailCLM n z) ^ 2 * gaussWeight z)) := by
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun z ↦ M ^ 2 * (‖z‖ ^ (2 * β) * gaussWeight z))
    (Eventually.of_forall fun ε ↦
      (((measurable_liftExt hf β ε).pow_const 2).mul
        continuous_gaussWeight.measurable).aestronglyMeasurable) ?_
    ((integrable_norm_rpow_mul_gaussWeight (d := n + 1) (by omega) (k := 2 * β)
      (by have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)).const_mul _) ?_
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    refine ae_of_all _ fun z ↦ ?_
    have h := abs_liftExt_le hβ hM0 hM hε.2.le z (f := f)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (gaussWeight_nonneg z)), ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (gaussWeight_nonneg z)
    calc liftExt β ε f z ^ 2 = |liftExt β ε f z| ^ 2 := (sq_abs _).symm
      _ ≤ (M * ‖z‖ ^ β) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = M ^ 2 * ‖z‖ ^ (2 * β) := by
          have e : (‖z‖ ^ β) ^ 2 = ‖z‖ ^ (2 * β) := by
            rw [← rpow_natCast, ← rpow_mul (norm_nonneg _)]; ring_nf
          rw [mul_pow, e]
  · filter_upwards [ae_tailCLM_ne_zero hn] with z hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_liftExt_eventuallyEq (f := f) (β := β) hz] with ε hε
    rw [hε.eq_of_nhds]

/-- `∫ |∇W_ε|² e^{-|z|²/2} → ∫ |∇Ṽ|² e^{-|z|²/2}` as `ε → 0⁺`. -/
theorem tendsto_integral_norm_gradient_liftExt_sq (hn : 2 ≤ n) (hβ : 0 < β) {K : ℝ≥0}
    (hf : LipschitzWith K f) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ ω, |f ω| ≤ M) :
    Tendsto (fun ε ↦ ∫ z, ‖∇ (liftExt β ε f) z‖ ^ 2 * gaussWeight z) (𝓝[>] 0)
      (𝓝 (∫ z, ‖∇ (fun z ↦ homogExt β f (tailCLM n z)) z‖ ^ 2 * gaussWeight z)) := by
  set C : ℝ := M * |β - 1| + (M.toNNReal + 2 * K : ℝ≥0)
  have hk₁ : -(n : ℝ) < 2 * β - 2 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hk₂ : -((n + 1 : ℕ) : ℝ) < 2 * β - 2 := by push_cast; linarith
  have hi₁ := (integral_comp_tailCLM_mul_gaussWeight (h := fun x : E n ↦ ‖x‖ ^ (2 * β - 2))
    (measurable_norm.pow_const _) (fun x ↦ rpow_nonneg (norm_nonneg x) _)
    (integrable_norm_rpow_mul_gaussWeight (by omega) hk₁)).1
  have hi₂ := integrable_norm_rpow_mul_gaussWeight (d := n + 1) (by omega) hk₂
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun z ↦ 2 * C ^ 2 * (‖tailCLM n z‖ ^ (2 * β - 2) * gaussWeight z +
      ‖z‖ ^ (2 * β - 2) * gaussWeight z))
    (Eventually.of_forall fun ε ↦
      (((measurable_gradient _).norm.pow_const 2).mul
        continuous_gaussWeight.measurable).aestronglyMeasurable) ?_
    ((hi₁.add hi₂).const_mul _) ?_
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [ae_norm_gradient_liftExt_le (β := β) (by omega) hf hM0 hM hε.1 hε.2.le]
      with z hz
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (gaussWeight_nonneg z))]
    set a := ‖tailCLM n z‖ ^ (β - 1)
    set b := ‖z‖ ^ (β - 1)
    have ha : ‖tailCLM n z‖ ^ (2 * β - 2) = a ^ 2 := by
      rw [← rpow_natCast, ← rpow_mul (norm_nonneg _)]; ring_nf
    have hb : ‖z‖ ^ (2 * β - 2) = b ^ 2 := by
      rw [← rpow_natCast, ← rpow_mul (norm_nonneg _)]; ring_nf
    rw [ha, hb, ← add_mul, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (gaussWeight_nonneg z)
    have h0 : 0 ≤ ‖∇ (liftExt β ε f) z‖ := norm_nonneg _
    calc ‖∇ (liftExt β ε f) z‖ ^ 2 ≤ (C * (a + b)) ^ 2 := pow_le_pow_left₀ h0 hz 2
      _ ≤ 2 * C ^ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b), sq_nonneg C]
  · filter_upwards [ae_tailCLM_ne_zero (by omega : 1 ≤ n)] with z hz
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_liftExt_eventuallyEq (f := f) (β := β) hz] with ε hε
    simp only [gradient]
    rw [hε.fderiv_eq]

/-! ### The Gaussian quantities of `Ṽ` -/

theorem integral_homogExt_comp_tailCLM_sq (hn : 2 ≤ n) (hβ : 0 < β) {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∫ z, homogExt β f (tailCLM n z) ^ 2 * gaussWeight z =
      gaussMassOne * (gaussMoment (2 * β + n - 1) * sphL2Sq f) := by
  have h := integral_homogExt_sq_mul_gaussWeight (by omega) hβ hf
  rw [(integral_comp_tailCLM_mul_gaussWeight (h := fun x ↦ homogExt β f x ^ 2)
    ((measurable_homogExt hf β).pow_const 2) (fun x ↦ sq_nonneg _) h.1).2, h.2]

theorem integral_norm_gradient_homogExt_comp_tailCLM_sq (hn : 2 ≤ n) (hβ : 0 < β) {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∫ z, ‖∇ (fun z ↦ homogExt β f (tailCLM n z)) z‖ ^ 2 * gaussWeight z =
      gaussMassOne * (gaussMoment (2 * β + n - 3) * (β ^ 2 * sphL2Sq f + sphDirichlet f)) := by
  have h := integral_norm_gradient_homogExt_sq_mul_gaussWeight hn hβ hf
  simp_rw [norm_gradient_comp_tailCLM]
  rw [(integral_comp_tailCLM_mul_gaussWeight (h := fun x ↦ ‖∇ (homogExt β f) x‖ ^ 2)
    ((measurable_gradient _).norm.pow_const 2) (fun x ↦ sq_nonneg _) h.1).2, h.2]

/-! ### The lifting lemma -/

/-- **Lifting lemma** (from `𝕊^{n-1}` to `𝕊ⁿ`). Let `n ≥ 2`, let `f` be
admissible for `Γ ⊆ 𝕊^{n-1}` with `R(f) > 0`, and let `β = κ_n(R(f))`. Then
`λ₁(Γ↑) ≤ β (β + (n + 1) - 2)`. -/
theorem sphEigenvalue_liftSet_le (hn : 2 ≤ n) {Γ : Set (sphere (0 : E n) 1)}
    (hf : IsSphAdmissible Γ f) (hR : 0 < sphRayleigh f) :
    sphEigenvalue (liftSet Γ) ≤ charExponent n (sphRayleigh f) *
      (charExponent n (sphRayleigh f) + ((n + 1 : ℕ) : ℝ) - 2) := by
  obtain ⟨K, hK⟩ := hf.lipschitz
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_continuous hK.continuous
  set R := sphRayleigh f with hR_def
  set β := charExponent n R
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq := charExponent_sq_add (d := n) hR.le
  have hβ : 0 < β := by
    rcases (charExponent_nonneg (d := n) hR.le).eq_or_lt with h | h
    · exfalso
      rw [← h] at hsq
      simp at hsq
      linarith
    · exact h
  have hRβ : R = β * (β + n - 2) := by linear_combination (-1 : ℝ) * hsq
  set L := sphL2Sq f
  set D := sphDirichlet f
  have hL : 0 < L := hf.sphL2Sq_pos
  have hD : D = R * L := by rw [hR_def]; exact (div_mul_cancel₀ _ hL.ne').symm
  -- the Gaussian moments
  have hk3 : -1 < 2 * β + n - 3 := by linarith
  have hk2 : -1 < 2 * β + n - 2 := by linarith
  have hM3 := gaussMoment_pos hk3
  have hM2 := gaussMoment_pos hk2
  have hM1 : gaussMoment (2 * β + n - 1) = (2 * β + n - 2) * gaussMoment (2 * β + n - 3) := by
    have h := gaussMoment_add_two hk3
    rwa [show 2 * β + n - 3 + 2 = 2 * β + n - 1 by ring,
      show 2 * β + n - 3 + 1 = 2 * β + n - 2 by ring] at h
  have hM0' : gaussMoment (2 * β + n) = (2 * β + n - 1) * gaussMoment (2 * β + n - 2) := by
    have h := gaussMoment_add_two hk2
    rwa [show 2 * β + n - 2 + 2 = 2 * β + n by ring,
      show 2 * β + n - 2 + 1 = 2 * β + n - 1 by ring] at h
  -- the limits
  set A₀ := gaussMassOne * (gaussMoment (2 * β + n - 3) * (β ^ 2 * L + D))
  set B₀ := gaussMassOne * (gaussMoment (2 * β + n - 1) * L)
  have hc₁ := gaussMassOne_pos
  have hB₀ : 0 < B₀ := by
    simp only [B₀]
    rw [hM1]
    have : 0 < 2 * β + n - 2 := by linarith
    positivity
  have hA₀ : A₀ = β * B₀ := by
    simp only [A₀, B₀]
    rw [hM1, hD, hRβ]
    ring
  have hlimA := tendsto_integral_norm_gradient_liftExt_sq hn hβ hK hM0 hM
  rw [integral_norm_gradient_homogExt_comp_tailCLM_sq hn hβ hK] at hlimA
  have hlimB := tendsto_integral_liftExt_sq (by omega) hβ hK hM0 hM
  rw [integral_homogExt_comp_tailCLM_sq hn hβ hK] at hlimB
  have hlimR := ((hlimA.div hlimB hB₀.ne').const_mul (2 * β + n - 1)).sub_const (β ^ 2)
  have hval : (2 * β + n - 1) * (A₀ / B₀) - β ^ 2 = β * (β + ((n + 1 : ℕ) : ℝ) - 2) := by
    rw [hA₀, mul_div_cancel_right₀ _ hB₀.ne']
    push_cast
    ring
  rw [hval] at hlimR
  refine ge_of_tendsto hlimR ?_
  filter_upwards [hlimB.eventually (lt_mem_nhds hB₀), Ioo_mem_nhdsGT one_pos] with ε hBε hε
  simp only [Pi.div_apply] at hBε ⊢
  obtain ⟨Kε, hKε⟩ := exists_lipschitzWith_liftApprox (β := β) hK hε.1 hε.2.le
  set g := liftApprox β ε f
  have hgB := integral_homogExt_sq_mul_gaussWeight (d := n + 1) (by omega) hβ hKε
  have hgA := integral_norm_gradient_homogExt_sq_mul_gaussWeight (d := n + 1) (by omega) hβ hKε
  rw [homogExt_liftApprox hβ] at hgB hgA
  have e₁ : 2 * β + ((n + 1 : ℕ) : ℝ) - 1 = 2 * β + n := by push_cast; ring
  have e₃ : 2 * β + ((n + 1 : ℕ) : ℝ) - 3 = 2 * β + n - 2 := by push_cast; ring
  rw [e₁, hM0'] at hgB
  rw [e₃] at hgA
  rw [hgB.2] at hBε ⊢
  rw [hgA.2]
  have hpos : 0 < (2 * β + n - 1) * gaussMoment (2 * β + n - 2) := by
    have : 0 < 2 * β + n - 1 := by linarith
    positivity
  have hLg : 0 < sphL2Sq g := (mul_pos_iff_of_pos_left hpos).1 hBε
  have hadm : IsSphAdmissible (liftSet Γ) g :=
    ⟨⟨Kε, hKε⟩, fun ω hω ↦ liftApprox_eq_zero hf.eq_zero hω, hLg⟩
  have hbdd : BddBelow (sphRayleigh '' {g | IsSphAdmissible (liftSet Γ) g}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨g, -, rfl⟩
    exact div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
  have hne₁ : 2 * β + n - 1 ≠ 0 := by linarith
  have hne₂ := hM2.ne'
  have hne₃ := hLg.ne'
  calc sphEigenvalue (liftSet Γ) ≤ sphRayleigh g := csInf_le hbdd ⟨g, hadm, rfl⟩
    _ = _ := by
      rw [sphRayleigh]
      field_simp
      ring

/-- **Lifting lemma, exponent form**: `κ_{n+1}(λ₁(Γ↑)) ≤ κ_n(R(f))`. -/
theorem charExponent_sphEigenvalue_liftSet_le (hn : 2 ≤ n) {Γ : Set (sphere (0 : E n) 1)}
    (hf : IsSphAdmissible Γ f) (hR : 0 < sphRayleigh f) :
    charExponent (n + 1) (sphEigenvalue (liftSet Γ)) ≤ charExponent n (sphRayleigh f) := by
  have hβ := charExponent_nonneg (d := n) hR.le
  have h := charExponent_mono (d := n + 1) (sphEigenvalue_liftSet_le hn hf hR)
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rwa [charExponent_mul_add_sub_two (by push_cast; linarith)] at h

end EllipticBernoulli

end
