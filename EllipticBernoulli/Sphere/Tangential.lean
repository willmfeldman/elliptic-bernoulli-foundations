/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.HomogeneousExt
public import EllipticBernoulli.Sphere.Radial
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The tangential gradient of a restriction

Let `w : E d → ℝ`, `x₀ ∈ E d`, `r > 0`, and let `f(ω') = w(x₀ + rω')` on the unit sphere. If `w` is
differentiable at `x₀ + rω`, then

`∇f̂(ω) = r (I - ω ⊗ ω) ∇w(x₀ + rω)` and `|∇f̂(ω)|² = r² (|∇w(x₀ + rω)|² - (∂ᵣw(x₀ + rω))²)`,

where `∂ᵣw` is the radial derivative about `x₀` (`radialDeriv`).

* `gradient_homogExt0_of_eq`, `norm_sq_gradient_homogExt0_of_eq`.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped Gradient

namespace EllipticBernoulli

variable {d : ℕ}

public section

/-- The derivative of the norm at a unit vector `ν` is `v ↦ ⟨ν, v⟩`. -/
private theorem hasFDerivAt_norm_of_norm_eq_one {ν : E d} (hν : ‖ν‖ = 1) :
    HasFDerivAt (fun x : E d ↦ ‖x‖) (innerSL ℝ ν) ν := by
  have hsq := (hasStrictFDerivAt_norm_sq ν).hasFDerivAt
  have h := hsq.sqrt (by rw [hν]; norm_num)
  have hfun : (fun x : E d ↦ √(‖x‖ ^ 2)) = fun x ↦ ‖x‖ := by
    funext x; exact Real.sqrt_sq (norm_nonneg x)
  rw [hfun] at h
  refine h.congr_fderiv ?_
  ext v
  simp [hν]

/-- **The tangential gradient.** If `f(ω') = w(x₀ + rω')` on the
sphere and `w` is differentiable at `x₀ + rω`, then
`∇f̂(ω) = r (∇w(x₀ + rω) - ⟨∇w(x₀ + rω), ω⟩ ω)`. -/
theorem gradient_homogExt0_of_eq {w : E d → ℝ} {f : sphere (0 : E d) 1 → ℝ} (x₀ : E d) {r : ℝ}
    (hf : ∀ ω : sphere (0 : E d) 1, f ω = w (x₀ + r • (ω : E d)))
    (ω : sphere (0 : E d) 1) (hw : DifferentiableAt ℝ w (x₀ + r • (ω : E d))) :
    ∇ (homogExt0 f) ω = r • (∇ w (x₀ + r • (ω : E d)) -
      inner ℝ (∇ w (x₀ + r • (ω : E d))) (ω : E d) • (ω : E d)) := by
  set ν : E d := (ω : E d)
  have hν : ‖ν‖ = 1 := norm_eq_of_mem_sphere ω
  have hν0 : ν ≠ 0 := norm_ne_zero_iff.mp (by rw [hν]; exact one_ne_zero)
  set g : E d → E d := fun x ↦ x₀ + r • (‖x‖⁻¹ • x) with hg
  have hgν : g ν = x₀ + r • ν := by simp [hg, hν]
  -- `f̂ = w ∘ g` near `ν`
  have heq : homogExt0 f =ᶠ[𝓝 ν] w ∘ g := by
    filter_upwards [isOpen_ne.mem_nhds hν0] with x hx
    rw [homogExt0_of_ne_zero f hx, hf]
    rfl
  -- the derivative of `g` at `ν`
  have hI := (hasFDerivAt_inv (𝕜 := ℝ) (x := ‖ν‖) (by rw [hν]; exact one_ne_zero)).comp ν
    (hasFDerivAt_norm_of_norm_eq_one hν)
  have hS := (hI.smul (hasFDerivAt_id ν)).const_smul r |>.const_add x₀
  have hw' : HasFDerivAt w (fderiv ℝ w (x₀ + r • ν)) (g ν) := by
    rw [hgν]; exact hw.hasFDerivAt
  have hcomp := (hw'.comp ν hS).congr_of_eventuallyEq heq
  set G := ∇ w (x₀ + r • ν)
  have hgrad : HasGradientAt (homogExt0 f) (r • (G - inner ℝ G ν • ν)) ν := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine hcomp.congr_fderiv ?_
    ext v
    have hG : ∀ u, fderiv ℝ w (x₀ + r • ν) u = inner ℝ G u := fun u ↦ by
      rw [show G = ∇ w (x₀ + r • ν) from rfl, gradient, toDual_symm_apply]
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      add_apply, ContinuousLinearMap.smulRight_apply, Function.comp_apply,
      ContinuousLinearMap.coe_id', id, hG, toDual_apply_apply, hν]
    simp only [innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply, inner_smul_right,
      inner_add_right, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
    norm_num
    left
    ring
  exact hgrad.gradient

/-- `|∇f̂(ω)|² = r² (|∇w(x₀ + rω)|² - (∂ᵣw(x₀ + rω))²)` under the hypotheses of
`gradient_homogExt0_of_eq` and `r > 0`. -/
theorem norm_sq_gradient_homogExt0_of_eq {w : E d → ℝ} {f : sphere (0 : E d) 1 → ℝ} (x₀ : E d)
    {r : ℝ} (hr : 0 < r) (hf : ∀ ω : sphere (0 : E d) 1, f ω = w (x₀ + r • (ω : E d)))
    (ω : sphere (0 : E d) 1) (hw : DifferentiableAt ℝ w (x₀ + r • (ω : E d))) :
    ‖∇ (homogExt0 f) ω‖ ^ 2 = r ^ 2 * (‖∇ w (x₀ + r • (ω : E d))‖ ^ 2 -
      radialDeriv w x₀ (x₀ + r • (ω : E d)) ^ 2) := by
  rw [gradient_homogExt0_of_eq x₀ hf ω hw, radialDeriv_add_smul w x₀ hr ω, norm_smul,
    mul_pow, Real.norm_of_nonneg hr.le, norm_sub_sq_real, inner_smul_right, norm_smul,
    norm_eq_of_mem_sphere ω, Real.norm_eq_abs, mul_one, sq_abs]
  ring

end

end EllipticBernoulli
