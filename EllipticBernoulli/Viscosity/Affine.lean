/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Viscosity.Basic

/-!
# Translation and scaling invariance of the viscosity notions

For `x₀ : E d`, `r > 0` and `s > 0`, put `A y = x₀ + r • y`. If `u` is a viscosity
super/sub/solution (Abedin–Feldman–Stinson, Definition 2.1) in `U` with coefficient `Q`, then
`u' y = u (A y) / (r * s)` is one in `A ⁻¹' U` with coefficient `Q' y = Q (A y) / s`
(`IsViscSuper.rescale`, `IsViscSub.rescale`, `IsViscSolution.rescale`, and
`IsRelaxedSub.rescale` with `Eset ↦ A ⁻¹' Eset`; the names `…comp_affine` are aliases).

Taking `x₀ = 0`, `r = 1`, `s = q` gives the normalization `Q ≡ q ↦ Q ≡ 1`, `u ↦ u / q`.

**Proof.** If `φ'` is a test function at `y` for `u'`, then
`φ z = r s φ' (r⁻¹ • (z - x₀))` is a test function at `A y` for `u`, with
`∇φ (A y) = s ∇φ' y` and `Δφ (A y) = (s / r) Δφ' y`. The sign of `Δ` is preserved, `φ (A y) = 0`
iff `φ' y = 0`, and `‖∇φ (A y)‖ ≤ Q (A y) ↔ ‖∇φ' y‖ ≤ Q (A y) / s`. The touching sets correspond
because `A` is a homeomorphism (`posSet_rescale`, `closure_posSet_rescale`,
`freeBoundary_rescale`).

Calculus: `laplacian_comp_add_left`, `laplacian_comp_smul` (`Δ(f ∘ (c • ·)) = c² (Δf) ∘ (c • ·)`),
`gradient_comp_add_left`, `gradient_comp_smul`, on any finite-dimensional real inner product
space.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology InnerProductSpace
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

/-! ### Laplacian and gradient under translations and dilations -/

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The Laplacian commutes with translations. -/
theorem laplacian_comp_add_left (f : F → ℝ) (a x : F) :
    Δ (fun z ↦ f (a + z)) x = Δ f (a + x) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis _) x,
    congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) (a + x)]
  simp only [iteratedFDeriv_comp_add_left]

/-- **Laplacian under dilations**: `Δ(f ∘ (c • ·)) = c² (Δf) ∘ (c • ·)` for `f ∈ C²`. -/
theorem laplacian_comp_smul {f : F → ℝ} (hf : ContDiff ℝ 2 f) (c : ℝ) (x : F) :
    Δ (fun z ↦ f (c • z)) x = c ^ 2 * Δ f (c • x) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis _) x,
    congrFun (laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) (c • x),
    iteratedFDeriv_comp_const_smul (i := 2) c hf, Finset.mul_sum]
  simp

/-- The gradient commutes with translations. -/
theorem gradient_comp_add_left (f : F → ℝ) (a x : F) :
    ∇ (fun z ↦ f (a + z)) x = ∇ f (a + x) := by
  simp only [gradient, fderiv_comp_add_left]

/-- **Gradient under dilations**: `∇(f ∘ (c • ·)) = c • (∇f) ∘ (c • ·)`. -/
theorem gradient_comp_smul (f : F → ℝ) (c : ℝ) (x : F) :
    ∇ (fun z ↦ f (c • z)) x = c • ∇ f (c • x) := by
  have := fderiv_comp_smul (𝕜 := ℝ) (f := f) (x := x) c
  simp only [gradient]
  rw [show (fun z ↦ f (c • z)) = (f <| c • ·) from rfl, this, map_smul]

/-- The gradient of a constant multiple. -/
theorem gradient_const_mul {f : F → ℝ} {x : F} (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    ∇ (fun z ↦ c * f z) x = c • ∇ f x := by
  simp only [gradient]
  rw [show (fun z ↦ c * f z) = fun z ↦ c • f z from rfl, fderiv_fun_const_smul hf, map_smul]

end Calculus

/-! ### The affine change of variables -/

variable {d : ℕ}

/-- The affine map `y ↦ x₀ + r • y` as a homeomorphism (`r ≠ 0`). -/
private noncomputable def affineHomeomorph (x₀ : E d) {r : ℝ} (hr : r ≠ 0) : E d ≃ₜ E d where
  toFun y := x₀ + r • y
  invFun z := r⁻¹ • (-x₀ + z)
  left_inv y := by simp [smul_smul, inv_mul_cancel₀ hr]
  right_inv z := by simp [smul_smul, mul_inv_cancel₀ hr]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem affine_inv_apply (x₀ : E d) {r : ℝ} (hr : r ≠ 0) (z : E d) :
    x₀ + r • (r⁻¹ • (-x₀ + z)) = z :=
  (affineHomeomorph x₀ hr).right_inv z

private theorem inv_affine_apply (x₀ : E d) {r : ℝ} (hr : r ≠ 0) (y : E d) :
    r⁻¹ • (-x₀ + (x₀ + r • y)) = y :=
  (affineHomeomorph x₀ hr).left_inv y

/-- The inverse affine map sends `𝓝[S] (x₀ + r • y)` to `𝓝[A ⁻¹' S] y`. -/
private theorem tendsto_inv_affine (x₀ : E d) {r : ℝ} (hr : r ≠ 0) (S : Set (E d)) (y : E d) :
    Tendsto (fun z ↦ r⁻¹ • (-x₀ + z)) (𝓝[S] (x₀ + r • y))
      (𝓝[(fun y ↦ x₀ + r • y) ⁻¹' S] y) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun z : E d ↦ r⁻¹ • (-x₀ + z) := by fun_prop
    have := hc.tendsto (x₀ + r • y)
    rw [inv_affine_apply x₀ hr] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    change x₀ + r • (r⁻¹ • (-x₀ + z)) ∈ S
    rwa [affine_inv_apply x₀ hr]

/-- Positivity sets transform by preimage. -/
theorem posSet_rescale {U : Set (E d)} {u : E d → ℝ} (x₀ : E d) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    posSet (fun y ↦ u (x₀ + r • y) / (r * s)) ((fun y ↦ x₀ + r • y) ⁻¹' U) =
      (fun y ↦ x₀ + r • y) ⁻¹' posSet u U := by
  ext y
  simp only [posSet, mem_ofPred_eq, mem_preimage, div_pos_iff_of_pos_right (mul_pos hr hs)]

/-- Closures commute with preimages under `y ↦ x₀ + r • y`, `r ≠ 0`. -/
theorem closure_preimage_affine (x₀ : E d) {r : ℝ} (hr : r ≠ 0) (S : Set (E d)) :
    closure ((fun y ↦ x₀ + r • y) ⁻¹' S) = (fun y ↦ x₀ + r • y) ⁻¹' closure S :=
  ((affineHomeomorph x₀ hr).preimage_closure S).symm

/-- Closures of positivity sets transform by preimage. -/
theorem closure_posSet_rescale {U : Set (E d)} {u : E d → ℝ} (x₀ : E d) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    closure (posSet (fun y ↦ u (x₀ + r • y) / (r * s)) ((fun y ↦ x₀ + r • y) ⁻¹' U)) =
      (fun y ↦ x₀ + r • y) ⁻¹' closure (posSet u U) := by
  rw [posSet_rescale x₀ hr hs, closure_preimage_affine x₀ hr.ne']

/-- Free boundaries transform by preimage. -/
theorem freeBoundary_rescale {U : Set (E d)} {u : E d → ℝ} (x₀ : E d) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) :
    freeBoundary (fun y ↦ u (x₀ + r • y) / (r * s)) ((fun y ↦ x₀ + r • y) ⁻¹' U) =
      (fun y ↦ x₀ + r • y) ⁻¹' freeBoundary u U := by
  rw [freeBoundary, freeBoundary, posSet_rescale x₀ hr hs, preimage_inter]
  congr 1
  exact ((affineHomeomorph x₀ hr.ne').preimage_frontier _).symm

/-- The 2-jet of the lifted test function `φ z = r s φ' (r⁻¹ • (z - x₀))` at `x₀ + r • y`. -/
private theorem lift_jet {φ' : E d → ℝ} (hφ' : ContDiff ℝ ∞ φ') (x₀ : E d) {r s : ℝ}
    (hr : r ≠ 0) (y : E d) :
    ContDiff ℝ ∞ (fun z ↦ (r * s) * φ' (r⁻¹ • (-x₀ + z))) ∧
      ∇ (fun z ↦ (r * s) * φ' (r⁻¹ • (-x₀ + z))) (x₀ + r • y) = s • ∇ φ' y ∧
      Δ (fun z ↦ (r * s) * φ' (r⁻¹ • (-x₀ + z))) (x₀ + r • y) = (s / r) * Δ φ' y := by
  set f₁ : E d → ℝ := fun w ↦ φ' (r⁻¹ • w) with hf₁
  have hf₁s : ContDiff ℝ ∞ f₁ := hφ'.comp (contDiff_const_smul _)
  have hg : ContDiff ℝ ∞ fun z ↦ f₁ (-x₀ + z) := hf₁s.comp (contDiff_const.add contDiff_id)
  have hx : -x₀ + (x₀ + r • y) = r • y := by abel
  have hry : r⁻¹ • (r • y) = y := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
  refine ⟨contDiff_const.mul hg, ?_, ?_⟩
  · rw [gradient_const_mul ((hg.differentiable (by simp)) _), gradient_comp_add_left, hx,
      hf₁, gradient_comp_smul, hry, smul_smul]
    congr 1
    field_simp
  · have h2 : Δ (fun z ↦ (r * s) * f₁ (-x₀ + z)) (x₀ + r • y) =
        (r * s) * Δ (fun z ↦ f₁ (-x₀ + z)) (x₀ + r • y) := by
      exact laplacian_smul (r * s) (contDiff_two_of_smooth hg).contDiffAt
    rw [h2, laplacian_comp_add_left, hx, hf₁,
      laplacian_comp_smul (contDiff_two_of_smooth hφ') r⁻¹, hry]
    field_simp

/-- Touching data pulled back along `B z = r⁻¹ • (z - x₀)`: a relative-neighbourhood property at
`y` in `A ⁻¹' S` gives one at `A y` in `S`. -/
private theorem eventually_rescale {S : Set (E d)} (x₀ : E d) {r : ℝ} (hr : r ≠ 0) {y : E d}
    {P : E d → Prop} (h : ∀ᶠ y' in 𝓝[(fun y ↦ x₀ + r • y) ⁻¹' S] y, P y') :
    ∀ᶠ z in 𝓝[S] (x₀ + r • y), P (r⁻¹ • (-x₀ + z)) :=
  tendsto_inv_affine x₀ hr S y |>.eventually h

private theorem continuousOn_rescale {U : Set (E d)} {u : E d → ℝ} (hu : ContinuousOn u U)
    (x₀ : E d) (r s : ℝ) :
    ContinuousOn (fun y ↦ u (x₀ + r • y) / (r * s)) ((fun y ↦ x₀ + r • y) ⁻¹' U) :=
  (hu.comp (by fun_prop : Continuous fun y : E d ↦ x₀ + r • y).continuousOn
    fun _ hy ↦ hy).div_const _

/-- **Invariance of Definition 2.1(i) under translation and scaling.** With `A y = x₀ + r • y`,
`r, s > 0`: if `u` is a viscosity supersolution in `U` with coefficient `Q`, then
`u (A ·) / (r s)` is one in `A ⁻¹' U` with coefficient `Q (A ·) / s`. -/
theorem IsViscSuper.rescale {U : Set (E d)} {Q u : E d → ℝ} (hu : IsViscSuper U Q u)
    (x₀ : E d) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IsViscSuper ((fun y ↦ x₀ + r • y) ⁻¹' U) (fun y ↦ Q (x₀ + r • y) / s)
      (fun y ↦ u (x₀ + r • y) / (r * s)) := by
  have hrs : 0 < r * s := mul_pos hr hs
  refine ⟨continuousOn_rescale hu.1 x₀ r s, fun y hy ↦ div_nonneg (hu.2.1 _ hy) hrs.le, ?_⟩
  intro φ' hφ' y hy htouch
  obtain ⟨hφs, hgrad, hlap⟩ := lift_jet hφ' x₀ (s := s) hr.ne' y
  set φ : E d → ℝ := fun z ↦ (r * s) * φ' (r⁻¹ • (-x₀ + z)) with hφ
  have hφy : φ (x₀ + r • y) = (r * s) * φ' y := by
    simp only [hφ, inv_affine_apply x₀ hr.ne']
  have htouchφ : TouchesBelow φ u U (x₀ + r • y) := by
    refine ⟨hy, ?_, ?_⟩
    · rw [hφy, htouch.2.1]; field_simp
    · filter_upwards [eventually_rescale x₀ hr.ne' htouch.2.2] with z hz
      simp only [affine_inv_apply x₀ hr.ne'] at hz
      have := mul_le_mul_of_nonneg_left hz hrs.le
      rwa [mul_div_cancel₀ _ hrs.ne'] at this
  rcases hu.2.2 φ hφs (x₀ + r • y) hy htouchφ with h | ⟨h0, hg⟩
  · left
    rw [hlap] at h
    exact nonpos_of_mul_nonpos_right h (div_pos hs hr)
  · right
    refine ⟨?_, ?_⟩
    · rw [hφy] at h0
      exact (mul_eq_zero.1 h0).resolve_left hrs.ne'
    · rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hg
      rw [le_div_iff₀ hs]
      linarith

/-- **Invariance of Definition 2.1(ii) under translation and scaling.** With `A y = x₀ + r • y`,
`r, s > 0`: if `u` is a viscosity subsolution in `U` with coefficient `Q`, then
`u (A ·) / (r s)` is one in `A ⁻¹' U` with coefficient `Q (A ·) / s`. -/
theorem IsViscSub.rescale {U : Set (E d)} {Q u : E d → ℝ} (hu : IsViscSub U Q u)
    (x₀ : E d) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IsViscSub ((fun y ↦ x₀ + r • y) ⁻¹' U) (fun y ↦ Q (x₀ + r • y) / s)
      (fun y ↦ u (x₀ + r • y) / (r * s)) := by
  have hrs : 0 < r * s := mul_pos hr hs
  refine ⟨continuousOn_rescale hu.1 x₀ r s, fun y hy ↦ div_nonneg (hu.2.1 _ hy) hrs.le, ?_⟩
  intro φ' hφ' y htouch
  rw [closure_posSet_rescale x₀ hr hs, ← preimage_inter] at htouch
  obtain ⟨hφs, hgrad, hlap⟩ := lift_jet hφ' x₀ (s := s) hr.ne' y
  set φ : E d → ℝ := fun z ↦ (r * s) * φ' (r⁻¹ • (-x₀ + z)) with hφ
  have hφy : φ (x₀ + r • y) = (r * s) * φ' y := by
    simp only [hφ, inv_affine_apply x₀ hr.ne']
  have hmax : ∀ z, max (φ z) 0 = (r * s) * max (φ' (r⁻¹ • (-x₀ + z))) 0 := fun z ↦ by
    rw [mul_max_of_nonneg _ _ hrs.le, mul_zero]
  have htouchφ : TouchesAbove (fun z ↦ max (φ z) 0) u (closure (posSet u U) ∩ U)
      (x₀ + r • y) := by
    refine ⟨htouch.1, ?_, ?_⟩
    · have h1 : max (φ' y) 0 = u (x₀ + r • y) / (r * s) := htouch.2.1
      change max (φ (x₀ + r • y)) 0 = u (x₀ + r • y)
      rw [hmax, inv_affine_apply x₀ hr.ne', h1]
      field_simp
    · filter_upwards [eventually_rescale x₀ hr.ne' htouch.2.2] with z hz
      simp only [affine_inv_apply x₀ hr.ne'] at hz
      rw [hmax]
      have := mul_le_mul_of_nonneg_left hz hrs.le
      rwa [mul_div_cancel₀ _ hrs.ne'] at this
  rcases hu.2.2 φ hφs (x₀ + r • y) htouchφ with h | ⟨h0, hg⟩
  · left
    rw [hlap] at h
    exact (mul_nonneg_iff_of_pos_left (div_pos hs hr)).1 h
  · right
    refine ⟨?_, ?_⟩
    · rw [hφy] at h0
      exact (mul_eq_zero.1 h0).resolve_left hrs.ne'
    · rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hg
      rw [div_le_iff₀ hs]
      linarith

/-- **Invariance of Definition 2.1(iii) under translation and scaling** (see
`IsViscSuper.rescale`). -/
theorem IsViscSolution.rescale {U : Set (E d)} {Q u : E d → ℝ} (hu : IsViscSolution U Q u)
    (x₀ : E d) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IsViscSolution ((fun y ↦ x₀ + r • y) ⁻¹' U) (fun y ↦ Q (x₀ + r • y) / s)
      (fun y ↦ u (x₀ + r • y) / (r * s)) :=
  ⟨hu.1.rescale x₀ hr hs, hu.2.rescale x₀ hr hs⟩

/-- **Invariance of Definition 2.3 (relaxed subsolutions) under translation and scaling.** With
`A y = x₀ + r • y`, `r, s > 0`: if `(u, Eset)` is a relaxed subsolution in `U` with coefficient `Q`,
then `(u (A ·) / (r s), A ⁻¹' Eset)` is one in `A ⁻¹' U` with coefficient `Q (A ·) / s`. -/
theorem IsRelaxedSub.rescale {U : Set (E d)} {Q u : E d → ℝ} {Eset : Set (E d)}
    (hu : IsRelaxedSub U Q u Eset) (x₀ : E d) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IsRelaxedSub ((fun y ↦ x₀ + r • y) ⁻¹' U) (fun y ↦ Q (x₀ + r • y) / s)
      (fun y ↦ u (x₀ + r • y) / (r * s)) ((fun y ↦ x₀ + r • y) ⁻¹' Eset) := by
  have hrs : 0 < r * s := mul_pos hr hs
  obtain ⟨hc, hnn, hcl, hsub, hpos, htest⟩ := hu
  refine ⟨continuousOn_rescale hc x₀ r s, fun y hy ↦ div_nonneg (hnn _ hy) hrs.le,
    hcl.preimage (by fun_prop), ?_, ?_, ?_⟩
  · rw [closure_preimage_affine x₀ hr.ne']
    exact preimage_mono hsub
  · rw [posSet_rescale x₀ hr hs]
    exact preimage_mono hpos
  intro φ' hφ' y htouch
  rw [← preimage_inter] at htouch
  obtain ⟨hφs, hgrad, hlap⟩ := lift_jet hφ' x₀ (s := s) hr.ne' y
  set φ : E d → ℝ := fun z ↦ (r * s) * φ' (r⁻¹ • (-x₀ + z)) with hφ
  have hφy : φ (x₀ + r • y) = (r * s) * φ' y := by
    simp only [hφ, inv_affine_apply x₀ hr.ne']
  have htouchφ : TouchesAbove φ u (Eset ∩ U) (x₀ + r • y) := by
    refine ⟨htouch.1, ?_, ?_⟩
    · rw [hφy, htouch.2.1]; field_simp
    · filter_upwards [eventually_rescale x₀ hr.ne' htouch.2.2] with z hz
      simp only [affine_inv_apply x₀ hr.ne'] at hz
      have := mul_le_mul_of_nonneg_left hz hrs.le
      rwa [mul_div_cancel₀ _ hrs.ne'] at this
  rcases htest φ hφs (x₀ + r • y) htouchφ with h | ⟨h0, hg⟩
  · left
    rw [hlap] at h
    exact (mul_nonneg_iff_of_pos_left (div_pos hs hr)).1 h
  · right
    refine ⟨?_, ?_⟩
    · rw [hφy] at h0
      exact (mul_eq_zero.1 h0).resolve_left hrs.ne'
    · rw [hgrad, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hg
      rw [div_le_iff₀ hs]
      linarith

/-- Alias of `IsViscSuper.rescale`. -/
alias IsViscSuper.comp_affine := IsViscSuper.rescale
/-- Alias of `IsViscSub.rescale`. -/
alias IsViscSub.comp_affine := IsViscSub.rescale
/-- Alias of `IsViscSolution.rescale`. -/
alias IsViscSolution.comp_affine := IsViscSolution.rescale
/-- Alias of `IsRelaxedSub.rescale`. -/
alias IsRelaxedSub.comp_affine := IsRelaxedSub.rescale
/-- Alias of `posSet_rescale`. -/
alias posSet_comp_affine := posSet_rescale
/-- Alias of `freeBoundary_rescale`. -/
alias freeBoundary_comp_affine := freeBoundary_rescale

end EllipticBernoulli

end
