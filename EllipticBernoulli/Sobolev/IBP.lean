/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.Uniqueness
public import EllipticBernoulli.Sobolev.Cutoff
public import EllipticBernoulli.Sobolev.Lipschitz
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# Integration by parts against compactly supported `H¹` functions

`HasWeakGradient.integral_inner_gradient_eq_neg`: if `G` is a weak gradient of `h` on
the open set `U`, `h = 0` a.e. on `U \ K` for a compact `K ⊆ U`, and `φ ∈ C^∞(ℝᵈ)`, then
`∫_U ⟪G, ∇φ⟫ = -∫_U h Δφ`.

Proof: `G = 0` a.e. on `U \ K` (`HasWeakGradient.ae_eq_zero_of_ae_eq_zero_on`). Test the weak
gradient identity in direction `eᵢ` against `ζ ∂ᵢφ`, with a cut-off `ζ = 1` on a neighbourhood of
`K` supported in `U`; on `K` the test function coincides with `∂ᵢφ` near every point, and off `K`
both `h` and `G` vanish a.e. Sum over an orthonormal basis.

This is the identity behind the energy-decrease computation for perturbations of minimizers
(`∫ ⟪∇φ, ∇h⟫ = -∫ Δφ h` with `h = (φ + δ - w)₊`).
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff Gradient Laplacian

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The second directional derivative as an iterated derivative. -/
theorem fderiv_fderiv_apply_eq_iteratedFDeriv {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) (x v : E d) :
    fderiv ℝ (fun y ↦ fderiv ℝ φ y v) x v = iteratedFDeriv ℝ 2 φ x ![v, v] := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- **Integration by parts against a compactly supported `H¹` function.** -/
theorem HasWeakGradient.integral_inner_gradient_eq_neg {U : Set (E d)} (hU : IsOpen U)
    {h : E d → ℝ} {G : E d → E d} (hh : HasWeakGradient U h G) {K : Set (E d)}
    (hK : IsCompact K) (hKU : K ⊆ U) (h0 : ∀ᵐ x ∂(volume.restrict (U \ K)), h x = 0)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∫ x in U, inner ℝ (G x) (∇ φ x) = -∫ x in U, h x * Δ φ x := by
  obtain ⟨K', hK', hKK', hK'U⟩ := exists_compact_between hK hU hKU
  obtain ⟨ζ, hζ, hζc, hζU, -, hζ1⟩ := exists_smooth_cutoff hK' hU hK'U
  have hUK : MeasurableSet (U \ K) := hU.measurableSet.diff hK.measurableSet
  have hG0 : ∀ᵐ x ∂(volume.restrict (U \ K)), G x = 0 :=
    hh.ae_eq_zero_of_ae_eq_zero_on (hU.sdiff hK.isClosed) sdiff_subset h0
  rw [ae_restrict_iff' hUK] at h0 hG0
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hdφ : ContDiff ℝ ∞ (fderiv ℝ φ) := hφ.fderiv_right (m := ∞) (by norm_cast)
  -- the test functions `ψ i = ζ ∂ᵢφ`
  set ψ : Fin d → E d → ℝ := fun i x ↦ ζ x * fderiv ℝ φ x (b i) with hψ
  have hψs : ∀ i, ContDiff ℝ ∞ (ψ i) := fun i ↦ hζ.mul (hdφ.clm_apply contDiff_const)
  have hψc : ∀ i, HasCompactSupport (ψ i) := fun i ↦ hζc.mul_right
  have hψU : ∀ i, tsupport (ψ i) ⊆ U := fun i ↦ (tsupport_mul_subset_left).trans hζU
  -- near `K`, `ψ i = ∂ᵢφ`
  have hloc : ∀ i, ∀ x ∈ K, ψ i =ᶠ[𝓝 x] fun y ↦ fderiv ℝ φ y (b i) := by
    intro i x hx
    filter_upwards [mem_interior_iff_mem_nhds.1 (hKK' hx)] with y hy
    simp [hψ, hζ1 y hy]
  -- the two a.e. identities on `U`
  have hA : ∀ i, (fun x ↦ h x * fderiv ℝ (ψ i) x (b i)) =ᵐ[volume.restrict U]
      fun x ↦ h x * iteratedFDeriv ℝ 2 φ x ![b i, b i] := by
    intro i
    filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem hU.measurableSet] with x hx hxU
    by_cases hxK : x ∈ K
    · rw [(hloc i x hxK).fderiv_eq, fderiv_fderiv_apply_eq_iteratedFDeriv hφ]
    · rw [hx ⟨hxU, hxK⟩, zero_mul, zero_mul]
  have hB : ∀ i, (fun x ↦ inner ℝ (G x) (b i) * ψ i x) =ᵐ[volume.restrict U]
      fun x ↦ inner ℝ (G x) (b i) * fderiv ℝ φ x (b i) := by
    intro i
    filter_upwards [ae_restrict_of_ae hG0, ae_restrict_mem hU.measurableSet] with x hx hxU
    by_cases hxK : x ∈ K
    · rw [(hloc i x hxK).eq_of_nhds]
    · rw [hx ⟨hxU, hxK⟩, inner_zero_left, zero_mul, zero_mul]
  -- integrability
  have hiA : ∀ i, IntegrableOn (fun x ↦ h x * iteratedFDeriv ℝ 2 φ x ![b i, b i]) U := by
    intro i
    exact ((integrable_fderiv_apply_mul hh.1 (hψs i) (hψc i) (hψU i) (b i)).integrableOn).congr
      (hA i)
  have hiB : ∀ i, IntegrableOn (fun x ↦ inner ℝ (G x) (b i) * fderiv ℝ φ x (b i)) U := by
    intro i
    exact ((integrable_inner_mul hh.2.1 (hψs i).continuous (hψc i) (hψU i)
      (b i)).integrableOn).congr (hB i)
  -- pointwise sums
  have hsumB : ∀ x, inner ℝ (G x) (∇ φ x) =
      ∑ i, inner ℝ (G x) (b i) * fderiv ℝ φ x (b i) := by
    intro x
    rw [← b.sum_inner_mul_inner (G x) (∇ φ x)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [real_inner_comm (∇ φ x) (b i), inner_gradient_left_eq_fderiv]
  have hsumA : ∀ x, h x * Δ φ x = ∑ i, h x * iteratedFDeriv ℝ 2 φ x ![b i, b i] := by
    intro x
    rw [← Finset.mul_sum, InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ b]
  simp_rw [hsumB, hsumA]
  rw [integral_finsetSum _ fun i _ ↦ hiB i, integral_finsetSum _ fun i _ ↦ hiA i,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← integral_congr_ae (hB i), ← integral_congr_ae (hA i)]
  have := hh.2.2 (ψ i) (hψs i) (hψc i) (hψU i) (b i)
  linarith

end EllipticBernoulli
