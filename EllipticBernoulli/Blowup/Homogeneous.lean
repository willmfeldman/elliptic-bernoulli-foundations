/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
public import Mathlib.Analysis.InnerProductSpace.Laplacian
import EllipticBernoulli.Viscosity.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Planar 1-homogeneous harmonic functions on their positivity set

Let `v : ℝ² → ℝ` be continuous, nonnegative, `C²` and harmonic on `{v > 0}`, and positively
1-homogeneous (`v (t • y) = t * v y` for `t > 0`). Then `v ≡ 0`, or there are a unit vector `e` and
constants `a > 0`, `b ≥ 0` with `v y = a (y·e)₊ + b (y·e)₋` for all `y`
(`eq_halfPlanes_of_homogeneous`). This is the first step of the classification of planar
1-homogeneous inner variational solutions (`Blowup/PlanarClassification.lean`).

## Proof

On `{v > 0}` the Euler identity `Dv(y) y = v(y)` holds, and `Dv` is 0-homogeneous, so
`D²v(y)(y, ·) = 0`. In the plane a symmetric trace-free `2 × 2` matrix with a nonzero kernel vector
vanishes, so `D²v = 0` on `{v > 0}` (`fderiv_fderiv_eq_zero`): `Dv` is locally constant there.
A clopen argument in the half-plane `{Dv(y₀) y > 0}` then shows `v = Dv(y₀)` on that whole
half-plane (`eq_on_halfPlane`). Two such half-planes are disjoint or equal, which forces the
second one (if any) to be the opposite half-plane.

This avoids the usual route through the ODE `g'' + g = 0` for `g(θ) = v(cos θ, sin θ)`: it needs
no polar coordinates and no arc decomposition of `{g > 0}`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient Laplacian RealInnerProductSpace ContDiff

public section

namespace EllipticBernoulli

namespace PlanarHomogeneous

variable {v : E 2 → ℝ}

/-- The hypotheses: `v` continuous, nonnegative, `C²` and harmonic on `{v > 0}`, and
positively 1-homogeneous. -/
structure Hyp (v : E 2 → ℝ) : Prop where
  cont : Continuous v
  nonneg : ∀ y, 0 ≤ v y
  c2 : ContDiffOn ℝ 2 v {y | 0 < v y}
  harmonic : ∀ y, 0 < v y → Δ v y = 0
  hom : ∀ t : ℝ, 0 < t → ∀ y, v (t • y) = t * v y

variable (h : Hyp v)
include h

theorem isOpen_pos : IsOpen {y | 0 < v y} := isOpen_lt continuous_const h.cont

theorem apply_zero : v 0 = 0 := by
  have := h.hom 2 two_pos 0
  rw [smul_zero] at this
  linarith

theorem contDiffAt {y : E 2} (hy : 0 < v y) : ContDiffAt ℝ 2 v y :=
  h.c2.contDiffAt ((isOpen_pos h).mem_nhds hy)

theorem hasFDerivAt {y : E 2} (hy : 0 < v y) : HasFDerivAt v (fderiv ℝ v y) y :=
  ((contDiffAt h hy).differentiableAt (by norm_num)).hasFDerivAt

theorem apply_smul_pos {y : E 2} (hy : 0 < v y) {t : ℝ} (ht : 0 < t) : 0 < v (t • y) := by
  rw [h.hom t ht]; positivity

/-- **Euler identity**: `Dv(y) y = v(y)` on `{v > 0}`. -/
theorem fderiv_apply_self {y : E 2} (hy : 0 < v y) : fderiv ℝ v y y = v y := by
  have hc : HasDerivAt (fun t : ℝ ↦ t • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have h1 : HasFDerivAt v (fderiv ℝ v y) ((fun t : ℝ ↦ t • y) 1) := by
    simpa using hasFDerivAt h hy
  have hcomp := h1.comp_hasDerivAt (1 : ℝ) hc
  have heq : (v ∘ fun t : ℝ ↦ t • y) =ᶠ[𝓝 1] fun t ↦ t * v y := by
    filter_upwards [lt_mem_nhds one_pos] with t ht
    exact h.hom t ht y
  have h2 : HasDerivAt (fun t : ℝ ↦ t * v y) (v y) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (v y)
  exact hcomp.unique (h2.congr_of_eventuallyEq heq)

/-- `Dv` is 0-homogeneous on `{v > 0}`. -/
theorem fderiv_smul {y : E 2} (hy : 0 < v y) {t : ℝ} (ht : 0 < t) :
    fderiv ℝ v (t • y) = fderiv ℝ v y := by
  have h1 : HasFDerivAt (fun z ↦ v (t • z))
      ((fderiv ℝ v (t • y)).comp (t • ContinuousLinearMap.id ℝ (E 2))) y := by
    have hl : HasFDerivAt (fun z : E 2 ↦ t • z) (t • ContinuousLinearMap.id ℝ (E 2)) y :=
      (hasFDerivAt_id y).const_smul t
    exact (hasFDerivAt h (apply_smul_pos h hy ht)).comp y hl
  have hfun : (fun z ↦ v (t • z)) = fun z ↦ t * v z := funext (h.hom t ht)
  rw [hfun] at h1
  have h2 : HasFDerivAt (fun z ↦ t * v z) (t • fderiv ℝ v y) y := (hasFDerivAt h hy).const_mul t
  have huniq := h1.unique h2
  ext w
  have := congrArg (fun L ↦ L w) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at this
  exact mul_left_cancel₀ ht.ne' this

/-- `D²v(y)(y, ·) = 0` on `{v > 0}`. -/
theorem fderiv_fderiv_apply_self {y : E 2} (hy : 0 < v y) :
    fderiv ℝ (fderiv ℝ v) y y = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) y :=
    ((contDiffAt h hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasDerivAt (fun t : ℝ ↦ t • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have h1 : HasFDerivAt (fderiv ℝ v) (fderiv ℝ (fderiv ℝ v) y) ((fun t : ℝ ↦ t • y) 1) := by
    simpa using hd.hasFDerivAt
  have hcomp := h1.comp_hasDerivAt (1 : ℝ) hc
  have heq : (fderiv ℝ v ∘ fun t : ℝ ↦ t • y) =ᶠ[𝓝 1] fun _ ↦ fderiv ℝ v y := by
    filter_upwards [lt_mem_nhds one_pos] with t ht
    exact fderiv_smul h hy ht
  exact hcomp.unique ((hasDerivAt_const (1 : ℝ) (fderiv ℝ v y)).congr_of_eventuallyEq heq)

omit h in
private theorem eq_single (x : E 2) :
    x = x 0 • EuclideanSpace.single 0 1 + x 1 • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp

omit h in
private theorem clm_eq_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : E 2 →L[ℝ] F} (h0 : L (EuclideanSpace.single 0 1) = 0)
    (h1 : L (EuclideanSpace.single 1 1) = 0) : L = 0 := by
  ext x
  rw [eq_single x]
  simp [h0, h1]

/-- **The Hessian vanishes on `{v > 0}`.** A symmetric trace-free `2 × 2` matrix with a nonzero
kernel vector is zero. -/
theorem fderiv_fderiv_eq_zero {y : E 2} (hy : 0 < v y) : fderiv ℝ (fderiv ℝ v) y = 0 := by
  set H := fderiv ℝ (fderiv ℝ v) y with hH
  set b0 : E 2 := EuclideanSpace.single 0 1
  set b1 : E 2 := EuclideanSpace.single 1 1
  have hsymm : IsSymmSndFDerivAt ℝ v y := (contDiffAt h hy).isSymmSndFDerivAt (by simp)
  have htr : H b0 b0 + H b1 b1 = 0 := by
    have := h.harmonic y hy
    rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis v
      (EuclideanSpace.basisFun (Fin 2) ℝ)) y] at this
    simpa [Fin.sum_univ_two, iteratedFDeriv_two_apply, hH, b0, b1] using this
  have h01 : H b0 b1 = H b1 b0 := hsymm b0 b1
  have hker := fderiv_fderiv_apply_self h hy
  have hyeq : y = y 0 • b0 + y 1 • b1 := eq_single y
  rw [← hH, hyeq] at hker
  have e0 := congrArg (fun L ↦ L b0) hker
  have e1 := congrArg (fun L ↦ L b1) hker
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, ContinuousLinearMap.zero_apply] at e0 e1
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [apply_zero h] at hy
    exact lt_irrefl _ hy
  have hsq : H b0 b0 ^ 2 + H b0 b1 ^ 2 = 0 := by
    have hA : y 0 * (H b0 b0 ^ 2 + H b0 b1 ^ 2) = 0 := by
      linear_combination H b0 b0 * e0 + H b0 b1 * e1 + (y 1 * H b0 b0) * h01 -
        (y 1 * H b0 b1) * htr
    have hB : y 1 * (H b0 b0 ^ 2 + H b0 b1 ^ 2) = 0 := by
      linear_combination H b0 b1 * e0 - H b0 b0 * e1 + (y 1 * H b0 b1) * h01 +
        (y 1 * H b0 b0) * htr
    by_contra hne
    apply hy0
    ext i
    fin_cases i
    · simpa [hne] using hA
    · simpa [hne] using hB
  have h2 := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 hsq
  have ha : H b0 b0 = 0 := (pow_eq_zero_iff two_ne_zero).1 h2.1
  have hb : H b0 b1 = 0 := (pow_eq_zero_iff two_ne_zero).1 h2.2
  refine clm_eq_zero (clm_eq_zero (F := ℝ) ?_ ?_) (clm_eq_zero (F := ℝ) ?_ ?_)
  · exact ha
  · exact hb
  · rw [← h01]; exact hb
  · linarith

/-- `Dv` is locally constant on `{v > 0}`. -/
theorem eventually_fderiv_eq {y : E 2} (hy : 0 < v y) :
    ∀ᶠ z in 𝓝 y, fderiv ℝ v z = fderiv ℝ v y := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_pos h) y hy
  have hC1 : ContDiffOn ℝ 1 (fderiv ℝ v) {y | 0 < v y} :=
    h.c2.fderiv_of_isOpen (isOpen_pos h) (by norm_num)
  filter_upwards [ball_mem_nhds y hr] with z hz
  refine isOpen_ball.is_const_of_fderiv_eq_zero (𝕜 := ℝ) (convex_ball y r).isPreconnected ?_ ?_
    hz (mem_ball_self hr)
  · exact (hC1.mono hball).differentiableOn (by norm_num)
  · intro w hw
    exact fderiv_fderiv_eq_zero h (hball hw)

/-- **Half-plane propagation.** If `v(y₀) > 0` and `p = Dv(y₀)`, then on the whole half-plane
`{p > 0}` we have `v = p` and `Dv = p`. -/
theorem eq_on_halfPlane {y₀ : E 2} (hy₀ : 0 < v y₀) {y : E 2}
    (hy : 0 < fderiv ℝ v y₀ y) : v y = fderiv ℝ v y₀ y ∧ fderiv ℝ v y = fderiv ℝ v y₀ := by
  set p := fderiv ℝ v y₀ with hp
  set u : Set (E 2) := {z | 0 < v z ∧ fderiv ℝ v z = p} with hu
  have hC1 : ContDiffOn ℝ 1 (fderiv ℝ v) {y | 0 < v y} :=
    h.c2.fderiv_of_isOpen (isOpen_pos h) (by norm_num)
  have hvu : ∀ z ∈ u, v z = p z := by
    rintro z ⟨hz, hzp⟩
    rw [← fderiv_apply_self h hz, hzp]
  have hopen : IsOpen u := by
    refine isOpen_iff_mem_nhds.2 fun z ⟨hz, hzp⟩ ↦ ?_
    filter_upwards [(isOpen_pos h).mem_nhds hz, eventually_fderiv_eq h hz] with w hw hwz
    exact ⟨hw, hwz.trans hzp⟩
  have hconv : Convex ℝ {w : E 2 | 0 < p w} := convex_halfSpace_gt p.toLinearMap.isLinear 0
  have hsub : {w : E 2 | 0 < p w} ⊆ u := by
    refine hconv.isPreconnected.subset_of_closure_inter_subset hopen ?_ ?_
    · refine ⟨y₀, ?_, hy₀, rfl⟩
      change 0 < p y₀
      rw [hp, fderiv_apply_self h hy₀]
      exact hy₀
    · rintro z ⟨hzc, hzp⟩
      have hclosed : IsClosed {w : E 2 | v w = p w} := isClosed_eq h.cont p.continuous
      have hvz : v z = p z := closure_minimal hvu hclosed hzc
      have hz : 0 < v z := hvz ▸ hzp
      refine ⟨hz, ?_⟩
      have hcont : ContinuousAt (fderiv ℝ v) z :=
        (hC1.continuousOn.continuousAt ((isOpen_pos h).mem_nhds hz))
      have hmem := hcont.continuousWithinAt.mem_closure_image hzc
      have himg : fderiv ℝ v '' u ⊆ {p} := by
        rintro _ ⟨w, ⟨-, hw⟩, rfl⟩
        exact hw
      have := closure_mono himg hmem
      rwa [closure_singleton] at this
  obtain ⟨hvy, hdy⟩ := hsub hy
  exact ⟨hvu y (hsub hy), hdy⟩

omit h in
/-- `Dv(y) w = ⟪∇v(y), w⟫`. -/
private theorem fderiv_eq_inner (y w : E 2) : fderiv ℝ v y w = ⟪∇ v y, w⟫ :=
  fderiv_apply_eq_inner_gradient v y w

/-- Gradient form of `eq_on_halfPlane`. -/
theorem eq_on_halfPlane' {y₀ : E 2} (hy₀ : 0 < v y₀) {y : E 2}
    (hy : 0 < ⟪∇ v y₀, y⟫) : v y = ⟪∇ v y₀, y⟫ ∧ ∇ v y = ∇ v y₀ := by
  rw [← fderiv_eq_inner] at hy ⊢
  obtain ⟨h1, h2⟩ := eq_on_halfPlane h hy₀ hy
  refine ⟨h1, ?_⟩
  simp only [gradient, h2]

/-- Euler identity, gradient form. -/
theorem inner_gradient_self {y : E 2} (hy : 0 < v y) : ⟪∇ v y, y⟫ = v y := by
  rw [← fderiv_eq_inner, fderiv_apply_self h hy]

/-- **Opposite half-plane.** Let `v = a⟪·, e⟫` with `Dv = a e` on `{⟪·, e⟫ > 0}` (`a > 0`, `e`
a unit vector). If `v(z) > 0` and `⟪z, e⟫ ≤ 0`, then `∇v(z) = -‖∇v(z)‖ e`. -/
theorem gradient_eq_neg_of_nonpos {e : E 2} (he : ‖e‖ = 1) {a : ℝ} (ha : 0 < a)
    (hplane : ∀ y, 0 < ⟪y, e⟫ → ∇ v y = a • e) {z : E 2} (hz : 0 < v z)
    (hze : ⟪z, e⟫ ≤ 0) : ∇ v z = -‖∇ v z‖ • e := by
  set Q := ∇ v z with hQ
  set b := ‖Q‖ with hb
  have hQz : ⟪Q, z⟫ = v z := inner_gradient_self h hz
  by_contra hne
  set w : E 2 := b • e + Q with hw
  have hwne : w ≠ 0 := by
    intro h0
    apply hne
    rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]
    exact h0
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hQQ : ⟪Q, Q⟫ = b ^ 2 := real_inner_self_eq_norm_sq Q
  have hnorm : ‖w‖ ^ 2 = 2 * b * (b + ⟪e, Q⟫) := by
    rw [← real_inner_self_eq_norm_sq, hw]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hee, hQQ, real_inner_comm e Q]
    ring
  have hbpos : 0 < b := by
    rw [hb, norm_pos_iff]
    rintro h0
    rw [h0, inner_zero_left] at hQz
    linarith
  have hpos : 0 < b + ⟪e, Q⟫ := by
    have : 0 < ‖w‖ ^ 2 := by positivity
    rw [hnorm] at this
    exact pos_of_mul_pos_right this (by positivity)
  have hwe : 0 < ⟪w, e⟫ := by
    rw [hw, inner_add_left, real_inner_smul_left, hee, real_inner_comm]
    linarith
  have hQw : 0 < ⟪Q, w⟫ := by
    rw [hw, inner_add_right, real_inner_smul_right, hQQ, real_inner_comm]
    linarith [mul_pos hbpos hpos]
  have h1 := hplane w hwe
  have h2 := (eq_on_halfPlane' h hz hQw).2
  rw [← hQ] at h2
  rw [h1] at h2
  -- `Q = a e`, so `v z = a ⟪e, z⟫ ≤ 0`.
  rw [← h2, real_inner_smul_left, real_inner_comm] at hQz
  linarith [mul_nonpos_of_nonneg_of_nonpos ha.le hze]

end PlanarHomogeneous

open PlanarHomogeneous in
/-- **Planar 1-homogeneous harmonic functions.** A continuous, nonnegative, positively 1-homogeneous
`v : ℝ² → ℝ` that is `C²` and harmonic on `{v > 0}` is `≡ 0`, or `v = a (y·e)₊ + b (y·e)₋` for a
unit vector `e`, `a > 0` and `b ≥ 0`. -/
theorem eq_halfPlanes_of_homogeneous {v : E 2 → ℝ} (hcont : Continuous v)
    (hnn : ∀ y, 0 ≤ v y) (hc2 : ContDiffOn ℝ 2 v {y | 0 < v y})
    (hΔ : ∀ y, 0 < v y → Δ v y = 0) (hhom : ∀ t : ℝ, 0 < t → ∀ y, v (t • y) = t * v y) :
    (∀ y, v y = 0) ∨ ∃ e : E 2, ‖e‖ = 1 ∧ ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧
      ∀ y, v y = a * max ⟪y, e⟫ 0 + b * max (-⟪y, e⟫) 0 := by
  have h : Hyp v := ⟨hcont, hnn, hc2, hΔ, hhom⟩
  by_cases hex : ∃ y₀, 0 < v y₀
  swap
  · push Not at hex
    exact Or.inl fun y ↦ le_antisymm (hex y) (hnn y)
  right
  obtain ⟨y₀, hy₀⟩ := hex
  set P := ∇ v y₀ with hP
  set a := ‖P‖ with ha
  have hPy₀ : ⟪P, y₀⟫ = v y₀ := inner_gradient_self h hy₀
  have hapos : 0 < a := by
    rw [ha, norm_pos_iff]
    rintro h0
    rw [h0, inner_zero_left] at hPy₀
    linarith
  set e : E 2 := a⁻¹ • P with he_def
  have hPe : P = a • e := by rw [he_def, smul_smul, mul_inv_cancel₀ hapos.ne', one_smul]
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, norm_inv, norm_norm, ← ha, inv_mul_cancel₀ hapos.ne']
  have hPy : ∀ y, ⟪P, y⟫ = a * ⟪y, e⟫ := fun y ↦ by
    rw [hPe, real_inner_smul_left, real_inner_comm]
  have hplus : ∀ y, 0 < ⟪y, e⟫ → v y = a * ⟪y, e⟫ ∧ ∇ v y = a • e := by
    intro y hy
    have hy' : 0 < ⟪∇ v y₀, y⟫ := by rw [← hP, hPy]; positivity
    obtain ⟨h1, h2⟩ := eq_on_halfPlane' h hy₀ hy'
    exact ⟨by rw [h1, ← hP, hPy], by rw [h2, ← hP, hPe]⟩
  have hopp := fun z hz hze ↦
    gradient_eq_neg_of_nonpos h he hapos (fun y hy ↦ (hplus y hy).2) (z := z) hz hze
  -- On the line, `v = 0`.
  have hline : ∀ y, ⟪y, e⟫ = 0 → v y = 0 := by
    intro y hy
    by_contra hne
    have hpos : 0 < v y := lt_of_le_of_ne (hnn y) (Ne.symm hne)
    have := inner_gradient_self h hpos
    rw [hopp y hpos hy.le, real_inner_smul_left, real_inner_comm, hy, mul_zero] at this
    linarith
  refine ⟨e, he, a, ?_⟩
  by_cases hz : ∃ z, 0 < v z ∧ ⟪z, e⟫ ≤ 0
  · obtain ⟨z, hz, hze⟩ := hz
    set b := ‖∇ v z‖ with hb
    have hQ := hopp z hz hze
    have hbpos : 0 < b := by
      rw [hb, norm_pos_iff]
      rintro h0
      have := inner_gradient_self h hz
      rw [h0, inner_zero_left] at this
      linarith
    refine ⟨b, hapos, hbpos.le, fun y ↦ ?_⟩
    rcases lt_trichotomy ⟪y, e⟫ 0 with hy | hy | hy
    · have hy' : 0 < ⟪∇ v z, y⟫ := by
        rw [hQ, real_inner_smul_left, real_inner_comm, ← hb]
        linarith [mul_pos hbpos (neg_pos.2 hy)]
      have h1 := (eq_on_halfPlane' h hz hy').1
      rw [h1, hQ, real_inner_smul_left, real_inner_comm, ← hb, max_eq_right hy.le,
        max_eq_left (by linarith)]
      ring
    · rw [hline y hy, hy]; simp
    · rw [(hplus y hy).1, max_eq_left hy.le, max_eq_right (by linarith)]
      ring
  · push Not at hz
    refine ⟨0, hapos, le_rfl, fun y ↦ ?_⟩
    rcases le_or_gt ⟪y, e⟫ 0 with hy | hy
    · have : v y ≤ 0 := by
        by_contra hne
        exact absurd (hz y (lt_of_not_ge hne)) (not_lt.2 hy)
      rw [le_antisymm this (hnn y), max_eq_right hy]
      ring
    · rw [(hplus y hy).1, max_eq_left hy.le]
      ring

end EllipticBernoulli
