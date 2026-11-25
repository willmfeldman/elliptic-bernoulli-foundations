/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Transform
public import EllipticBernoulli.Hodograph.Field
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivative bounds through the hodograph map

Let `u` be smooth on an open `O`, and suppose that on `O` the gradient factors through the
hodograph map `Ψ(y) = P(y - x₀) + u(y) e` (`hodoMap`): `∇u = K ∘ Ψ` with `K` smooth on an open
`T ⊇ Ψ(O)`.
If `‖D^i K‖ ≤ A` on `T` for `i ≤ 2`, then on `O`
* `‖D²u‖ ≤ A (2 + A)` and
* `‖D³u‖ ≤ 2 A (2 + A)⁴`

(`norm_iteratedFDeriv_le_of_gradient_eq_comp`). This is the chain rule (Faà di Bruno,
`norm_iteratedFDerivWithin_comp_le`) with `‖DΨ‖ ≤ 2 + ‖∇u‖` and `‖D²Ψ‖ ≤ ‖D²u‖`.

In the hodograph picture, `K = gradVec e ∘ ∇w` for the hodograph transform `w`, and the bounds on
`K` come from bounds on `D^{≤3} w`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli.Hodograph

variable {d : ℕ}

/-- The orthogonal projection onto `e^⊥` has norm at most `2` (for a unit `e`). -/
theorem norm_perpCLM_le {e : E d} (he : ‖e‖ = 1) : ‖perpCLM e‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun h ↦ ?_
  rw [perpCLM_apply, perpProj]
  calc ‖h - ⟪h, e⟫ • e‖ ≤ ‖h‖ + ‖⟪h, e⟫ • e‖ := norm_sub_le _ _
    _ = ‖h‖ + |⟪h, e⟫| := by rw [norm_smul, he, mul_one, Real.norm_eq_abs]
    _ ≤ ‖h‖ + ‖h‖ := by
        gcongr
        have := abs_real_inner_le_norm h e
        rwa [he, mul_one] at this
    _ = 2 * ‖h‖ := by ring

/-- `t ↦ t • e` as a continuous linear map. -/
private noncomputable def smulE (e : E d) : ℝ →L[ℝ] E d :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight e

private theorem smulE_apply (e : E d) (t : ℝ) : smulE e t = t • e := rfl

private theorem norm_smulE {e : E d} (he : ‖e‖ = 1) : ‖smulE e‖ ≤ 1 := by
  rw [smulE, ContinuousLinearMap.norm_smulRight_apply, he, mul_one]
  exact ContinuousLinearMap.norm_id_le

/-- The affine part of the hodograph map. -/
private theorem perpProj_sub_eq (e x₀ y : E d) :
    perpProj e (y - x₀) = perpCLM e y - perpCLM e x₀ := by
  rw [← map_sub, perpCLM_apply]

private theorem hodoMap_eq (u : E d → ℝ) (x₀ e : E d) :
    hodoMap u x₀ e = (fun y ↦ perpCLM e y - perpCLM e x₀) + smulE e ∘ u := by
  funext y
  simp only [hodoMap, Pi.add_apply, Function.comp_apply, smulE_apply, perpProj_sub_eq]

private theorem contDiff_affine (e x₀ : E d) :
    ContDiff ℝ ∞ (fun y ↦ perpCLM e y - perpCLM e x₀) :=
  (perpCLM e).contDiff.sub contDiff_const

private theorem iteratedFDeriv_two_affine (e x₀ y : E d) :
    iteratedFDeriv ℝ 2 (fun y ↦ perpCLM e y - perpCLM e x₀) y = 0 := by
  have hf : fderiv ℝ (fun y ↦ perpCLM e y - perpCLM e x₀) = fun _ ↦ perpCLM e := by
    funext z; exact ((perpCLM e).hasFDerivAt.sub_const _).fderiv
  rw [← norm_eq_zero, ← norm_iteratedFDeriv_fderiv, hf, iteratedFDeriv_const_of_ne one_ne_zero,
    Pi.zero_apply, norm_zero]

/-- `fderiv u = innerSL ℝ ∘ ∇u`. -/
private theorem fderiv_eq_innerSL_gradient (f : E d → ℝ) (x : E d) :
    fderiv ℝ f x = innerSL ℝ (∇ f x) := by
  ext v; simp [gradient]

/-- **Derivative bounds through the hodograph map.** -/
theorem norm_iteratedFDeriv_le_of_gradient_eq_comp {O T : Set (E d)} (hO : IsOpen O)
    (hT : IsOpen T) {u : E d → ℝ} (hu : ContDiffOn ℝ ∞ u O) {x₀ e : E d} (he : ‖e‖ = 1)
    {K : E d → E d} (hK : ContDiffOn ℝ ∞ K T) (hmaps : MapsTo (hodoMap u x₀ e) O T)
    (hgrad : ∀ y ∈ O, ∇ u y = K (hodoMap u x₀ e y)) {A : ℝ}
    (hA : ∀ i ≤ 2, ∀ z ∈ T, ‖iteratedFDeriv ℝ i K z‖ ≤ A) {y : E d} (hy : y ∈ O) :
    ‖iteratedFDeriv ℝ 2 u y‖ ≤ A * (2 + A) ∧ ‖iteratedFDeriv ℝ 3 u y‖ ≤ 2 * A * (2 + A) ^ 4 := by
  set Ψ := hodoMap u x₀ e with hΨdef
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by norm_num) _ (hmaps hy))
  have hΨ : ContDiffOn ℝ ∞ Ψ O := by
    rw [hΨdef, hodoMap_eq]
    exact (contDiff_affine e x₀).contDiffOn.add ((smulE e).contDiff.comp_contDiffOn hu)
  have hKΨ : ContDiffOn ℝ ∞ (K ∘ Ψ) O := hK.comp hΨ hmaps
  -- `fderiv u = innerSL ∘ K ∘ Ψ` near `y`
  have hfu : fderiv ℝ u =ᶠ[𝓝 y] (innerSL ℝ : E d →L[ℝ] E d →L[ℝ] ℝ) ∘ (K ∘ Ψ) :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hy) fun z hz ↦ by
      simp only [Function.comp_apply, fderiv_eq_innerSL_gradient, hgrad z hz]
  have hnorm : ∀ n : ℕ, ‖iteratedFDeriv ℝ (n + 1) u y‖ ≤ ‖iteratedFDeriv ℝ n (K ∘ Ψ) y‖ := by
    intro n
    rw [← norm_iteratedFDeriv_fderiv, (hfu.iteratedFDeriv ℝ n).self_of_nhds]
    refine ((innerSL ℝ).norm_iteratedFDeriv_comp_left
      ((hKΨ.contDiffAt (hO.mem_nhds hy)).of_le le_rfl) (by exact_mod_cast le_top)).trans ?_
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_innerSL_le ℝ)
  -- `‖DΨ‖ ≤ 2 + A` on `O`
  have hDΨ : ∀ z ∈ O, ‖fderiv ℝ Ψ z‖ ≤ 2 + A := by
    intro z hz
    have hud : DifferentiableAt ℝ u z :=
      (hu.contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
    have hd : HasFDerivAt Ψ (perpCLM e + (smulE e).comp (fderiv ℝ u z)) z := by
      rw [hΨdef, hodoMap_eq]
      exact ((perpCLM e).hasFDerivAt.sub_const _).add
        ((smulE e).hasFDerivAt.comp z hud.hasFDerivAt)
    rw [hd.fderiv]
    have h1 : ‖fderiv ℝ u z‖ ≤ A := by
      rw [fderiv_eq_innerSL_gradient, hgrad z hz]
      refine (ContinuousLinearMap.le_of_opNorm_le _ (norm_innerSL_le ℝ) _).trans ?_
      rw [one_mul, ← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := K)]
      exact hA 0 (by norm_num) _ (hmaps hz)
    have e1 : ‖perpCLM e + (smulE e).comp (fderiv ℝ u z)‖ ≤
        ‖perpCLM e‖ + ‖(smulE e).comp (fderiv ℝ u z)‖ := norm_add_le _ _
    have e2 : ‖(smulE e).comp (fderiv ℝ u z)‖ ≤ ‖smulE e‖ * ‖fderiv ℝ u z‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    have e3 := norm_perpCLM_le he
    have e4 := norm_smulE he
    have e5 : ‖smulE e‖ * ‖fderiv ℝ u z‖ ≤ A :=
      (mul_le_of_le_one_left (norm_nonneg _) e4).trans h1
    linarith
  -- open-set conversions
  have hOu : UniqueDiffOn ℝ O := hO.uniqueDiffOn
  have hTu : UniqueDiffOn ℝ T := hT.uniqueDiffOn
  have hC : ∀ i, i ≤ 2 → ‖iteratedFDerivWithin ℝ i K T (Ψ y)‖ ≤ A := fun i hi ↦ by
    rw [iteratedFDerivWithin_of_isOpen i hT (hmaps hy)]; exact hA i hi _ (hmaps hy)
  -- the second derivative
  have h2 : ‖iteratedFDeriv ℝ 2 u y‖ ≤ A * (2 + A) := by
    refine (hnorm 1).trans ?_
    rw [← iteratedFDerivWithin_of_isOpen 1 hO hy]
    have := norm_iteratedFDerivWithin_comp_le (n := 1) hK hΨ (by exact_mod_cast le_top) hTu hOu
      hmaps hy (fun i hi ↦ hC i (hi.trans (by norm_num))) (D := 2 + A) fun i hi1 hi2 ↦ by
        have : i = 1 := le_antisymm hi2 hi1
        subst this
        rw [iteratedFDerivWithin_of_isOpen 1 hO hy, norm_iteratedFDeriv_one, pow_one]
        exact hDΨ y hy
    simpa using this
  refine ⟨h2, (hnorm 2).trans ?_⟩
  -- `‖D²Ψ‖ ≤ ‖D²u‖`
  have hD2Ψ : ‖iteratedFDeriv ℝ 2 Ψ y‖ ≤ A * (2 + A) := by
    have hud : ContDiffAt ℝ 2 u y := (hu.contDiffAt (hO.mem_nhds hy)).of_le (by simp)
    rw [hΨdef, hodoMap_eq, iteratedFDeriv_add_apply ((contDiff_affine e x₀).contDiffAt.of_le
      (by simp)) ((smulE e).contDiff.contDiffAt.comp y hud), iteratedFDeriv_two_affine, zero_add]
    refine ((smulE e).norm_iteratedFDeriv_comp_left hud le_rfl).trans ?_
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_smulE he)).trans h2
  rw [← iteratedFDerivWithin_of_isOpen 2 hO hy]
  have := norm_iteratedFDerivWithin_comp_le (n := 2) hK hΨ (by simp) hTu hOu
    hmaps hy hC (D := (2 + A) ^ 2) fun i hi1 hi2 ↦ by
      rw [iteratedFDerivWithin_of_isOpen i hO hy]
      interval_cases i
      · rw [norm_iteratedFDeriv_one, pow_one]
        refine (hDΨ y hy).trans ?_
        nlinarith
      · refine hD2Ψ.trans ?_
        nlinarith [sq_nonneg (2 + A), pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ 2 + A)
          (show 2 + A ≤ (2 + A) ^ 2 by nlinarith) 2]
  calc ‖iteratedFDerivWithin ℝ 2 (K ∘ Ψ) O y‖ ≤ (Nat.factorial 2) * A * ((2 + A) ^ 2) ^ 2 := this
    _ = 2 * A * (2 + A) ^ 4 := by rw [Nat.factorial_two]; push_cast; ring

end EllipticBernoulli.Hodograph
