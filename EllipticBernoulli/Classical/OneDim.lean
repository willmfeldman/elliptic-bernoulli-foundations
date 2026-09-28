/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Setting
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
import EllipticBernoulli.Viscosity.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Harmonic functions on a connected open subset of the line

* `norm_gradient_eq_of_ray_one`: in `E 1`, a function harmonic on a connected open set `S`
  has constant derivative there; if `S` contains the ray `x₀ + t e`, `0 < t < t₀`, and the
  one-sided difference quotient of `u` at `x₀` along `e` tends to `q`, then `‖∇u‖ = |q|` on `S`.

This is the free boundary gradient condition in dimension one, where the flatness theory
(`isClassicalNear_of_flat`, `2 ≤ d`) is not available and not needed.

## Proof

`Δu = D²u(e, e)` in dimension one, so `D²u = 0` on `S` and `Du ≡ g` on `S`
(`IsOpen.is_const_of_fderiv_eq_zero`). Along the ray, `t ↦ u(x₀ + t e) - t g(e)` has zero
derivative on `(0, t₀)`, hence is constant there; its limit as `t → 0+` is `u(x₀)`, because the
difference quotient converges. So the difference quotient equals `g(e)` on `(0, t₀)`, whence
`g(e) = q`, and `‖∇u‖ = |g(e)|` in dimension one.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

namespace EllipticBernoulli

/-- In `E 1`, every vector is a multiple of a unit vector `e`. -/
private theorem eq_inner_smul_of_one {e : E 1} (he : ‖e‖ = 1) (v : E 1) : v = ⟪v, e⟫ • e := by
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' (K := ℝ) e he0).1
    finrank_euclideanSpace_fin v
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]
  simp

/-- In `E 1`, a harmonic function has vanishing second derivative. -/
private theorem fderiv_fderiv_eq_zero_of_one {u : E 1 → ℝ} {y : E 1} (hu : HarmonicAt u y) :
    fderiv ℝ (fderiv ℝ u) y = 0 := by
  -- a unit vector
  set e : E 1 := EuclideanSpace.single 0 1 with he_def
  have he : ‖e‖ = 1 := by simp [he_def]
  have hΔ : Δ u y = 0 := hu.2.self_of_nhds
  set B := fderiv ℝ (fderiv ℝ u) y with hB
  have hbil : ∀ v w : E 1, B v w = ⟪v, e⟫ * ⟪w, e⟫ * B e e := fun v w ↦ by
    rw [eq_inner_smul_of_one he v, eq_inner_smul_of_one he w]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, real_inner_smul_left,
      real_inner_self_eq_norm_sq, he]
    ring
  have hbasis : ∀ i, B (stdOrthonormalBasis ℝ (E 1) i) (stdOrthonormalBasis ℝ (E 1) i) =
      B e e := fun i ↦ by
    have hn : ‖stdOrthonormalBasis ℝ (E 1) i‖ = 1 := (stdOrthonormalBasis ℝ (E 1)).orthonormal.1 i
    have hsq : ⟪stdOrthonormalBasis ℝ (E 1) i, e⟫ ^ 2 = 1 := by
      have h := congrArg norm (eq_inner_smul_of_one he (stdOrthonormalBasis ℝ (E 1) i))
      rw [norm_smul, he, mul_one, hn, Real.norm_eq_abs] at h
      rw [← sq_abs, ← h, one_pow]
    rw [hbil, ← sq, hsq, one_mul]
  have hBee : B e e = 0 := by
    rw [laplacian_eq_sum_fderiv_fderiv] at hΔ
    rw [← hB] at hΔ
    simp only [hbasis, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      finrank_euclideanSpace_fin, one_smul] at hΔ
    exact hΔ
  ext v w
  rw [ContinuousLinearMap.zero_apply, ContinuousLinearMap.zero_apply, hbil, hBee, mul_zero]

public section

/-- **Dimension one.** A function harmonic on a connected open set
`S ⊆ E 1` which contains the ray `x₀ + t e` for small `t > 0`, and whose difference quotient at
`x₀` along `e` tends to `q`, satisfies `‖∇u‖ = |q|` on `S`. -/
theorem norm_gradient_eq_of_ray_one {S : Set (E 1)} {u : E 1 → ℝ} (hS : IsOpen S)
    (hSc : IsPreconnected S) (hharm : ∀ y ∈ S, HarmonicAt u y) {x₀ e : E 1} (he : ‖e‖ = 1)
    (hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • e ∈ S) {q : ℝ}
    (hq : Tendsto (fun t : ℝ ↦ (u (x₀ + t • e) - u x₀) / t) (𝓝[>] 0) (𝓝 q)) :
    ∀ y ∈ S, ‖∇ u y‖ = |q| := by
  have hdiff : ∀ y ∈ S, DifferentiableAt ℝ u y := fun y hy ↦
    (hharm y hy).1.differentiableAt (by norm_num)
  have hdiff2 : DifferentiableOn ℝ (fderiv ℝ u) S := fun y hy ↦
    (((hharm y hy).1.fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero).differentiableWithinAt
  -- `Du` is constant on `S`
  have hconst : ∀ y ∈ S, ∀ z ∈ S, fderiv ℝ u y = fderiv ℝ u z := fun y hy z hz ↦
    hS.is_const_of_fderiv_eq_zero hSc hdiff2
      (fun w hw ↦ fderiv_fderiv_eq_zero_of_one (hharm w hw)) hy hz
  -- the ray
  obtain ⟨t₀, ht₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hray
  have ht₀' : (0 : ℝ) < t₀ := ht₀
  have hy₁ : x₀ + (t₀ / 2) • e ∈ S := hsub ⟨by linarith, by linarith⟩
  set g := fderiv ℝ u (x₀ + (t₀ / 2) • e) with hg
  set c := g e with hc
  -- `k t = u(x₀ + t e) - t c` is constant on `(0, t₀)`
  set k : ℝ → ℝ := fun t ↦ u (x₀ + t • e) - t * c with hk
  have hkd : ∀ t ∈ Ioo 0 t₀, HasDerivAt k 0 t := fun t ht ↦ by
    have hl : HasDerivAt (fun t : ℝ ↦ x₀ + t • e) e t := by
      simpa using ((hasDerivAt_id t).smul_const e).const_add x₀
    have h1 := (hdiff _ (hsub ht)).hasFDerivAt.comp_hasDerivAt t hl
    have h2 := h1.sub ((hasDerivAt_id t).mul_const c)
    rw [hconst _ (hsub ht) _ hy₁] at h2
    simpa [hk, ← hg, ← hc] using h2
  have hkconst : ∀ s ∈ Ioo 0 t₀, ∀ t ∈ Ioo 0 t₀, k s = k t := fun s hs t ht ↦
    isOpen_Ioo.is_const_of_fderiv_eq_zero isPreconnected_Ioo
      (fun r hr ↦ (hkd r hr).differentiableAt.differentiableWithinAt)
      (fun r hr ↦ by simp [(hkd r hr).hasFDerivAt.fderiv]) hs ht
  -- `u(x₀ + t e) → u(x₀)` along the ray
  have hlimu : Tendsto (fun t : ℝ ↦ u (x₀ + t • e) - u x₀) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).mul hq
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t ≠ 0 := ne_of_gt ht
    simp only [id]
    field_simp
  have hlimk : Tendsto k (𝓝[>] 0) (𝓝 (u x₀)) := by
    have h1 := hlimu.sub ((tendsto_nhdsWithin_of_tendsto_nhds
      (tendsto_id (x := 𝓝 (0 : ℝ)))).mul_const c)
    rw [zero_mul, sub_zero] at h1
    have h2 := (h1.const_add (u x₀))
    rw [add_zero] at h2
    refine h2.congr' (Eventually.of_forall fun t ↦ ?_)
    simp only [hk, id]
    ring
  -- hence `k ≡ u x₀` on `(0, t₀)`
  have hkval : ∀ t ∈ Ioo 0 t₀, k t = u x₀ := fun t ht ↦ by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), k s = k t := by
      filter_upwards [Ioo_mem_nhdsGT ht₀'] with s hs
      exact hkconst s hs t ht
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' (hev.mono fun s hs ↦ hs.symm)) hlimk
  -- the difference quotient equals `c` on `(0, t₀)`
  have hqc : q = c := by
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (u (x₀ + t • e) - u x₀) / t = c := by
      filter_upwards [Ioo_mem_nhdsGT ht₀'] with t ht
      have h := hkval t ht
      simp only [hk] at h
      have ht' : t ≠ 0 := ne_of_gt ht.1
      field_simp
      linarith
    exact tendsto_nhds_unique hq (tendsto_const_nhds.congr' (hev.mono fun s hs ↦ hs.symm))
  -- conclusion
  intro y hy
  have hdec := eq_inner_smul_of_one he (∇ u y)
  rw [hdec, norm_smul, he, mul_one, Real.norm_eq_abs, ← fderiv_apply_eq_inner_gradient,
    hconst y hy _ hy₁, ← hg, ← hc, hqc]

end

end EllipticBernoulli
