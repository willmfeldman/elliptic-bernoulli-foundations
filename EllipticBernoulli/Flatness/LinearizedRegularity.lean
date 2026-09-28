/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import EllipticBernoulli.Flatness.Linearized
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import EllipticBernoulli.Flatness.Barriers
import EllipticBernoulli.Harmonic.Comparison
import EllipticBernoulli.Harmonic.GradientEstimate
import EllipticBernoulli.Harmonic.ViscosityHarmonic
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Calculus
import EllipticBernoulli.Viscosity.Jet
import EllipticBernoulli.Viscosity.Stability

/-!
# Regularity of the linearized (Neumann) problem

De Silva (2011), Lemma 2.6 (even reflection) and Lemma 4.1, Step 3 (the `C²` bound at the
origin).

* `laplacian_comp_linearIsometryEquiv`: `Δ (f ∘ l) = (Δ f) ∘ l` for a linear isometry equivalence
  `l` (no differentiability hypothesis).
* `planeReflection e`: the reflection `x ↦ x - 2⟪x, e⟫ e` across `e^⊥`; `fold e`: the fold
  `x ↦ x - 2 min(⟪x, e⟫, 0) e` onto the half-space `{⟪x, e⟫ ≥ 0}`. The even reflection of `w` is
  `w ∘ fold e`.
* `IsLinearizedSolution.neg`: `-w` solves the linearized problem.
* `IsLinearizedSolution.isViscSuperharmonicOn_fold`: De Silva's Lemma 2.6. The even reflection of
  a solution is viscosity superharmonic in `B_ρ` (and, by `neg`, subharmonic), hence harmonic
  (`IsLinearizedSolution.harmonicOnNhd_fold`, via `harmonicOnNhd_of_isViscHarmonic`).
  At reflection-plane points De Silva's perturbation `S + ε x_n` of the symmetrized test function
  `S = (P + P ∘ R)/2` is used; the touching point of the perturbation is found as the minimum
  point of `w* - S - ε x_n` on a small closed ball (a single `ε` suffices, no sequence).
* `linearized_C2_at_origin`: the first-order Taylor bound `|w x - w 0 - ⟪p, x⟫| ≤ C r²` on
  `H⁺ ∩ B_r`, `r < 1/4`, with `⟪p, e⟫ = 0`, from the interior Hessian estimate
  `norm_hessian_le_of_harmonic` and the mean value inequality.

## Provenance

`iteratedFDeriv_comp_linearIsometryEquiv_apply` and `laplacian_comp_linearIsometryEquiv` are
adapted (unchanged up to namespace and name) from viscosity-solution-theory v0.2.0 (commit 3a93109),
`ViscositySolns/Applications/Laplace/Weyl/LaplacianInvariance.lean`
(`iteratedFDeriv_comp_linearIsometryEquiv_apply`, `laplacian_comp_linearIsometryEquiv_right`),
which ports TauCeti, https://github.com/TauCetiProject/TauCeti,
`TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`, commit
91f66a0514e6523efdccddb9e35fb82c96dd6405 (Apache-2.0;
`Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`). Changes: namespace
`ViscositySolns.Analysis` → `EllipticBernoulli`, `laplacian_comp_linearIsometryEquiv_right` renamed
`laplacian_comp_linearIsometryEquiv`, variable names `E, E', F` → `F, F', G`, module form.
They are copied rather than imported so that `ViscositySolns.*` imports stay confined to
`Harmonic/`.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

public section

namespace EllipticBernoulli

/-! ### Invariance of the Laplacian under linear isometries -/

section Invariance

variable
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] in
/-- The iterated derivative transforms under a linear isometry equivalence on the right by
pulling the directions through the isometry. (Adapted from viscosity-solution-theory / TauCeti.) -/
theorem iteratedFDeriv_comp_linearIsometryEquiv_apply (l : F ≃ₗᵢ[ℝ] F') (f : F' → G)
    (i : ℕ) (x : F) (m : Fin i → F) :
    iteratedFDeriv ℝ i (f ∘ l) x m = iteratedFDeriv ℝ i f (l x) (fun j ↦ l (m j)) := by
  have h := l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv l]
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- **Invariance of the Laplacian under isometries.** `Δ (f ∘ l) = (Δ f) ∘ l` for a linear
isometry equivalence `l`; no differentiability hypothesis is needed. (Adapted from
viscosity-solution-theory / TauCeti, `laplacian_comp_linearIsometryEquiv_right`.) -/
theorem laplacian_comp_linearIsometryEquiv (l : F ≃ₗᵢ[ℝ] F') (f : F' → G) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  simp only [Function.comp_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l) (stdOrthonormalBasis ℝ F),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ F).map l)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_linearIsometryEquiv_apply l f 2 x]
  congr 1
  funext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

end Invariance

variable {d : ℕ}

/-! ### The reflection across `e^⊥` and the fold onto the half-space -/

/-- The reflection across the hyperplane `e^⊥`; for `‖e‖ = 1` it is `x ↦ x - 2⟪x, e⟫ e`
(`planeReflection_apply`). -/
noncomputable def planeReflection (e : E d) : E d ≃ₗᵢ[ℝ] E d := (ℝ ∙ e)ᗮ.reflection

theorem planeReflection_apply {e : E d} (he : ‖e‖ = 1) (x : E d) :
    planeReflection e x = x - (2 * ⟪x, e⟫) • e := by
  rw [planeReflection, Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
    he, real_inner_comm]
  simp only [RCLike.ofReal_real_eq_id, id_eq, one_pow, div_one]
  module

theorem planeReflection_planeReflection (e x : E d) :
    planeReflection e (planeReflection e x) = x :=
  Submodule.reflection_reflection _ x

theorem inner_planeReflection {e : E d} (he : ‖e‖ = 1) (x : E d) :
    ⟪planeReflection e x, e⟫ = -⟪x, e⟫ := by
  rw [planeReflection_apply he, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    he]
  ring

theorem planeReflection_eq_self {e x : E d} (he : ‖e‖ = 1) (hx : ⟪x, e⟫ = 0) :
    planeReflection e x = x := by
  rw [planeReflection_apply he, hx]
  simp

theorem planeReflection_self {e : E d} (he : ‖e‖ = 1) : planeReflection e e = -e := by
  rw [planeReflection_apply he, real_inner_self_eq_norm_sq, he]
  module

/-- The fold `x ↦ x - 2 min(⟪x, e⟫, 0) e` onto the half-space `{⟪x, e⟫ ≥ 0}`: the identity on
the half-space and `planeReflection e` below it. The even reflection of `w` is `w ∘ fold e`. -/
noncomputable def fold (e x : E d) : E d := x - (2 * min ⟪x, e⟫ 0) • e

theorem fold_of_nonneg {e x : E d} (hx : 0 ≤ ⟪x, e⟫) : fold e x = x := by
  simp [fold, min_eq_right hx]

theorem fold_of_nonpos {e x : E d} (he : ‖e‖ = 1) (hx : ⟪x, e⟫ ≤ 0) :
    fold e x = planeReflection e x := by
  rw [fold, min_eq_left hx, planeReflection_apply he]

theorem continuous_fold (e : E d) : Continuous (fold e) := by
  unfold fold
  fun_prop

theorem inner_fold_nonneg {e : E d} (he : ‖e‖ = 1) (x : E d) : 0 ≤ ⟪fold e x, e⟫ := by
  rcases le_total 0 ⟪x, e⟫ with h | h
  · rwa [fold_of_nonneg h]
  · rw [fold_of_nonpos he h, inner_planeReflection he]
    linarith

theorem norm_fold {e : E d} (he : ‖e‖ = 1) (x : E d) : ‖fold e x‖ = ‖x‖ := by
  rcases le_total 0 ⟪x, e⟫ with h | h
  · rw [fold_of_nonneg h]
  · rw [fold_of_nonpos he h, LinearIsometryEquiv.norm_map]

theorem fold_mem_halfBall {e x : E d} {ρ : ℝ} (he : ‖e‖ = 1) (hx : x ∈ ball (0 : E d) ρ) :
    fold e x ∈ halfBall e ρ :=
  ⟨inner_fold_nonneg he x, by rw [mem_ball_zero_iff, norm_fold he]; exact mem_ball_zero_iff.1 hx⟩

theorem fold_planeReflection {e : E d} (he : ‖e‖ = 1) (x : E d) :
    fold e (planeReflection e x) = fold e x := by
  rcases le_total 0 ⟪x, e⟫ with h | h
  · rw [fold_of_nonpos he (by rw [inner_planeReflection he]; linarith),
      planeReflection_planeReflection, fold_of_nonneg h]
  · rw [fold_of_nonneg (by rw [inner_planeReflection he]; linarith), fold_of_nonpos he h]

/-! ### Calculus under the reflection -/

/-- `Δ (φ ∘ R) = (Δ φ) ∘ R` for the reflection `R` across `e^⊥`. -/
theorem laplacian_comp_planeReflection (e : E d) (φ : E d → ℝ) (x : E d) :
    Δ (fun y ↦ φ (planeReflection e y)) x = Δ φ (planeReflection e x) := by
  have := congrFun (laplacian_comp_linearIsometryEquiv (planeReflection e) φ) x
  simpa [Function.comp_def] using this

/-- A function invariant under the reflection across `e^⊥` has vanishing normal derivative on
the plane `e^⊥`. -/
theorem fderiv_apply_eq_zero_of_comp_planeReflection {e : E d} (he : ‖e‖ = 1) {S : E d → ℝ}
    (hS : ∀ y, S (planeReflection e y) = S y) {x : E d} (hx : ⟪x, e⟫ = 0) :
    fderiv ℝ S x e = 0 := by
  have h1 : S ∘ planeReflection e = S := funext hS
  have h2 := (planeReflection e).toContinuousLinearEquiv.comp_right_fderiv (f := S) (x := x)
  have h3 := congrArg (fun L : E d →L[ℝ] ℝ ↦ L e) h2
  simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, h1,
    ContinuousLinearMap.coe_comp', Function.comp_apply] at h3
  have h4 : ((planeReflection e).toContinuousLinearEquiv : E d →L[ℝ] E d) e = -e := by
    rw [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      planeReflection_self he]
  rw [h4, map_neg, planeReflection_eq_self he hx] at h3
  linarith

/-! ### The linearized problem under `w ↦ -w` -/

/-- `-w` solves the linearized problem whenever `w` does (touching from below and above are
exchanged by `φ ↦ -φ`). -/
theorem IsLinearizedSolution.neg {w : E d → ℝ} {e : E d} {ρ : ℝ}
    (hw : IsLinearizedSolution w e ρ) : IsLinearizedSolution (-w) e ρ := by
  obtain ⟨hc, hbelow, habove⟩ := hw
  have hg : ∀ φ : E d → ℝ, ∀ x, ⟪∇ (-φ) x, e⟫ = -⟪∇ φ x, e⟫ := fun φ x ↦ by
    rw [← fderiv_apply_eq_inner_gradient, ← fderiv_apply_eq_inner_gradient, fderiv_neg]
    rfl
  refine ⟨hc.neg, fun φ hφ x hx ↦ ?_, fun φ hφ x hx ↦ ?_⟩
  · have h := habove (-φ) hφ.neg x ⟨hx.1, by simp [hx.2.1], hx.2.2.mono fun y hy ↦ by
      simp only [Pi.neg_apply] at hy ⊢
      linarith⟩
    rw [laplacian_neg, Pi.neg_apply, hg] at h
    exact ⟨fun h0 ↦ by linarith [h.1 h0], fun h0 ↦ by linarith [h.2 h0]⟩
  · have h := hbelow (-φ) hφ.neg x ⟨hx.1, by simp [hx.2.1], hx.2.2.mono fun y hy ↦ by
      simp only [Pi.neg_apply] at hy ⊢
      linarith⟩
    rw [laplacian_neg, Pi.neg_apply, hg] at h
    exact ⟨fun h0 ↦ by linarith [h.1 h0], fun h0 ↦ by linarith [h.2 h0]⟩

/-! ### De Silva's Lemma 2.6: the even reflection is harmonic -/

/-- The even reflection `w ∘ fold e` of a solution is continuous on `B_ρ`. -/
theorem IsLinearizedSolution.continuousOn_fold {w : E d → ℝ} {e : E d} {ρ : ℝ} (he : ‖e‖ = 1)
    (hw : IsLinearizedSolution w e ρ) : ContinuousOn (fun x ↦ w (fold e x)) (ball 0 ρ) :=
  hw.1.comp (continuous_fold e).continuousOn fun _ hz ↦ fold_mem_halfBall he hz

/-- Interior case of Lemma 2.6 (upper half): a smooth `ψ` touching `w ∘ fold e` from below on a
full neighbourhood of `y`, `⟪y, e⟫ > 0`, has `Δψ(y) ≤ 0`. -/
private theorem laplacian_nonpos_of_touch_pos {w : E d → ℝ} {e : E d} {ρ : ℝ}
    (hw : IsLinearizedSolution w e ρ) {ψ : E d → ℝ} (hψ : ContDiff ℝ ∞ ψ) {y : E d}
    (hyB : y ∈ ball (0 : E d) ρ) (hy : 0 < ⟪y, e⟫) (heq : ψ y = w (fold e y))
    (hle : ∀ᶠ z in 𝓝 y, ψ z ≤ w (fold e z)) : Δ ψ y ≤ 0 := by
  refine (hw.2.1 ψ hψ y ⟨⟨hy.le, hyB⟩, by rw [heq, fold_of_nonneg hy.le], ?_⟩).1 hy
  filter_upwards [nhdsWithin_le_nhds hle, self_mem_nhdsWithin] with z hz hzH
  rwa [fold_of_nonneg hzH.1] at hz

/-- Interior case of Lemma 2.6 (lower half), by reflecting the test function. -/
private theorem laplacian_nonpos_of_touch_neg {w : E d → ℝ} {e : E d} {ρ : ℝ} (he : ‖e‖ = 1)
    (hw : IsLinearizedSolution w e ρ) {ψ : E d → ℝ} (hψ : ContDiff ℝ ∞ ψ) {y : E d}
    (hyB : y ∈ ball (0 : E d) ρ) (hy : ⟪y, e⟫ < 0) (heq : ψ y = w (fold e y))
    (hle : ∀ᶠ z in 𝓝 y, ψ z ≤ w (fold e z)) : Δ ψ y ≤ 0 := by
  set R := planeReflection e with hR
  have hRy : 0 < ⟪R y, e⟫ := by rw [inner_planeReflection he]; linarith
  have hRB : R y ∈ ball (0 : E d) ρ := by
    rw [mem_ball_zero_iff, LinearIsometryEquiv.norm_map]; exact mem_ball_zero_iff.1 hyB
  have hψR : ContDiff ℝ ∞ (fun z ↦ ψ (R z)) := hψ.comp R.contDiff
  have ht : Tendsto R (𝓝 (R y)) (𝓝 y) := by
    have := R.continuous.tendsto (R y)
    rwa [hR, planeReflection_planeReflection] at this
  have h := laplacian_nonpos_of_touch_pos hw hψR hRB hRy
    (by rw [hR, planeReflection_planeReflection, fold_planeReflection he, heq]) (by
      filter_upwards [ht.eventually hle] with z hz
      rwa [hR, fold_planeReflection he] at hz)
  rwa [hR, laplacian_comp_planeReflection, planeReflection_planeReflection] at h

/-- Boundary case: a smooth `ψ` touching `w ∘ fold e` from below near a plane point `y` has
`⟪∇ψ(y), e⟫ ≤ 0` (Definition 2.5(ii)). -/
private theorem inner_gradient_nonpos_of_touch_zero {w : E d → ℝ} {e : E d} {ρ : ℝ}
    (hw : IsLinearizedSolution w e ρ) {ψ : E d → ℝ} (hψ : ContDiff ℝ ∞ ψ) {y : E d}
    (hyB : y ∈ ball (0 : E d) ρ) (hy : ⟪y, e⟫ = 0) (heq : ψ y = w (fold e y))
    (hle : ∀ᶠ z in 𝓝 y, ψ z ≤ w (fold e z)) : ⟪∇ ψ y, e⟫ ≤ 0 := by
  refine (hw.2.1 ψ hψ y ⟨⟨hy.ge, hyB⟩, by rw [heq, fold_of_nonneg hy.ge], ?_⟩).2 hy
  filter_upwards [nhdsWithin_le_nhds hle, self_mem_nhdsWithin] with z hz hzH
  rwa [fold_of_nonneg hzH.1] at hz

/-- **The reflection-plane case of Lemma 2.6.** A smooth reflection-invariant `S` lying strictly
below `w* = w ∘ fold e` on `B̄_δ(x)` (by `‖· - x‖⁴`), touching at the plane point `x`, cannot be
strictly subharmonic on `B̄_δ(x)`. De Silva's perturbation `S + ε ⟪·, e⟫`, `ε = δ³/2`, touches
`w*` from below (after adding a constant) at a point `x_ε` of the open ball `B_δ(x)`; each
position of `x_ε` (above, on, below the plane) contradicts the linearized problem.

This fills a gap in De Silva's proof, which ends "`x_ε ∈ B_ρ \ {x_n = 0}` and hence
`ΔS = ΔP ≤ 0`": the viscosity property gives `ΔS(x_ε) ≤ 0` only at the moving point `x_ε`, and
concluding at `x̄` needs `x_ε → x̄` and continuity of `ΔS`; when `x_ε` lies below the plane, the
reflected test function touching at `R x_ε` is left implicit. Here a single `ε` with a strict
`‖· - x‖⁴` margin and `ΔS > 0` on a whole ball give a contradiction directly. -/
private theorem plane_case {w : E d → ℝ} {e : E d} {ρ : ℝ} (he : ‖e‖ = 1)
    (hw : IsLinearizedSolution w e ρ) {S : E d → ℝ} (hSc : ContDiff ℝ ∞ S)
    (hSR : ∀ y, S (planeReflection e y) = S y) {x : E d} (hx : ⟪x, e⟫ = 0) {δ : ℝ} (hδ : 0 < δ)
    (hSx : S x = w (fold e x))
    (hcb : ∀ z ∈ closedBall x δ, 0 < Δ S z ∧ S z + (‖z - x‖ ^ 2) ^ 2 ≤ w (fold e z) ∧
      z ∈ ball (0 : E d) ρ) : False := by
  set ε : ℝ := δ ^ 3 / 2 with hεdef
  have hε : 0 < ε := by positivity
  set g : E d → ℝ := fun z ↦ w (fold e z) - S z - ε * ⟪z, e⟫ with hg
  have hgc : ContinuousOn g (closedBall x δ) :=
    (((hw.continuousOn_fold he).mono fun z hz ↦ (hcb z hz).2.2).sub
      hSc.continuous.continuousOn).sub (by fun_prop)
  obtain ⟨xε, hxε, hmin⟩ :=
    (isCompact_closedBall x δ).exists_isMinOn (nonempty_closedBall.2 hδ.le) hgc
  set m := g xε with hm
  have hm0 : m ≤ 0 := by
    have h := hmin (mem_closedBall_self hδ.le)
    simp only [mem_setOf_eq] at h
    have : g x = 0 := by simp only [hg, hSx, hx]; ring
    linarith
  have hlow : ∀ z ∈ closedBall x δ, (‖z - x‖ ^ 2) ^ 2 - ε * ‖z - x‖ ≤ g z := by
    intro z hz
    have hi : ⟪z, e⟫ ≤ ‖z - x‖ := by
      have h1 : ⟪z, e⟫ = ⟪z - x, e⟫ := by rw [inner_sub_left, hx, sub_zero]
      rw [h1]
      calc ⟪z - x, e⟫ ≤ ‖z - x‖ * ‖e‖ := real_inner_le_norm _ _
        _ = ‖z - x‖ := by rw [he, mul_one]
    have h2 := (hcb z hz).2.1
    simp only [hg]
    nlinarith
  have hxεin : xε ∈ ball x δ := by
    rw [mem_ball]
    rw [mem_closedBall] at hxε
    by_contra hc
    replace hc := not_lt.1 hc
    have ht : dist xε x = δ := le_antisymm hxε hc
    have h := (hlow xε hxε).trans hm0
    rw [← dist_eq_norm, ht, hεdef] at h
    nlinarith [pow_pos hδ 4]
  have hxεcb : xε ∈ closedBall x δ := hxε
  -- the test function `ψ = ε ⟪·, e⟫ + m + S`
  set ψ : E d → ℝ := fun z ↦ ε * ⟪z, e⟫ + m + 1 * S z with hψ
  have hψc : ContDiff ℝ ∞ ψ :=
    ((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).add contDiff_const).add
      (contDiff_const.mul hSc)
  have hψeq : ψ xε = w (fold e xε) := by simp only [hψ, hm, hg]; ring
  have hψle : ∀ᶠ z in 𝓝 xε, ψ z ≤ w (fold e z) := by
    filter_upwards [isOpen_ball.mem_nhds hxεin] with z hz
    have h := hmin (ball_subset_closedBall hz)
    simp only [mem_setOf_eq] at h
    simp only [hψ, hm, hg] at h ⊢
    linarith
  have hΔψ : Δ ψ xε = Δ S xε := by
    rw [hψ, laplacian_mul_inner_add_mul (contDiff_two_of_smooth hSc) e ε m 1 xε, one_mul]
  have hxεB : xε ∈ ball (0 : E d) ρ := (hcb xε hxεcb).2.2
  have hΔS : 0 < Δ S xε := (hcb xε hxεcb).1
  rcases lt_trichotomy ⟪xε, e⟫ 0 with h | h | h
  · have := laplacian_nonpos_of_touch_neg he hw hψc hxεB h hψeq hψle
    linarith
  · have h1 := inner_gradient_nonpos_of_touch_zero hw hψc hxεB h hψeq hψle
    have hgS : HasGradientAt S (∇ S xε) xε :=
      ((hSc.differentiable (by simp)) xε).hasGradientAt
    have h2 := (hasGradientAt_mul_inner_add_mul (e := e) hgS ε m 1).gradient
    have h3 : ⟪∇ S xε, e⟫ = 0 := by
      rw [← fderiv_apply_eq_inner_gradient]
      exact fderiv_apply_eq_zero_of_comp_planeReflection he hSR h
    have h4 : ⟪∇ ψ xε, e⟫ = ε := by
      rw [hψ, h2, inner_add_left, real_inner_smul_left, real_inner_smul_left, h3,
        real_inner_self_eq_norm_sq, he]
      ring
    linarith
  · have := laplacian_nonpos_of_touch_pos hw hψc hxεB h hψeq hψle
    linarith

/-- **De Silva (2011), Lemma 2.6, superharmonic half.** The even reflection `w ∘ fold e` of a
solution of the linearized problem is viscosity superharmonic in `B_ρ`. -/
theorem IsLinearizedSolution.isViscSuperharmonicOn_fold {w : E d → ℝ} {e : E d} {ρ : ℝ}
    (he : ‖e‖ = 1) (hw : IsLinearizedSolution w e ρ) :
    IsViscSuperharmonicOn (fun x ↦ w (fold e x)) (ball 0 ρ) := by
  intro φ hφ x hxB hT
  have hB : ball (0 : E d) ρ ∈ 𝓝 x := isOpen_ball.mem_nhds hxB
  have hloc : ∀ᶠ z in 𝓝 x, φ z ≤ w (fold e z) := by
    have := hT.2.2
    rwa [nhdsWithin_eq_nhds.2 hB] at this
  rcases lt_trichotomy ⟪x, e⟫ 0 with hneg | hzero | hpos
  · exact laplacian_nonpos_of_touch_neg he hw hφ hxB hneg hT.2.1 hloc
  swap
  · exact laplacian_nonpos_of_touch_pos hw hφ hxB hpos hT.2.1 hloc
  by_contra hΔ
  replace hΔ := not_le.1 hΔ
  obtain ⟨hφ'c, -, hΔ', -, hstrict⟩ := touchesBelow_strict_perturb hφ hT
  rw [nhdsWithin_eq_nhds.2 hB] at hstrict
  set φ' : E d → ℝ := fun y ↦ φ y - (‖y - x‖ ^ 2) ^ 2 with hφ'
  set R := planeReflection e with hR
  have hRx : R x = x := planeReflection_eq_self he hzero
  set S : E d → ℝ := fun y ↦ (φ' y + φ' (R y)) / 2 with hS
  have hRc : ContDiff ℝ ∞ (fun y ↦ φ' (R y)) := hφ'c.comp R.contDiff
  have hSc : ContDiff ℝ ∞ S := (hφ'c.add hRc).div_const 2
  have hSR : ∀ y, S (planeReflection e y) = S y := fun y ↦ by
    simp only [hS, hR, planeReflection_planeReflection]
    ring
  have hΔS : ∀ y, Δ S y = (Δ φ' y + Δ φ' (R y)) / 2 := by
    intro y
    have hc1 : ContDiffAt ℝ 2 φ' y := (contDiff_two_of_smooth hφ'c).contDiffAt
    have hc2 : ContDiffAt ℝ 2 (fun z ↦ φ' (R z)) y := (contDiff_two_of_smooth hRc).contDiffAt
    have hS' : S = (1 / 2 : ℝ) • (φ' + fun z ↦ φ' (R z)) := by
      funext z
      simp only [hS, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [hS', laplacian_smul (1 / 2 : ℝ) (f := φ' + fun z ↦ φ' (R z)) (hc1.add hc2),
      hc1.laplacian_add hc2, hR,
      laplacian_comp_planeReflection]
    simp only [smul_eq_mul]
    ring
  have hΔSx : 0 < Δ S x := by
    rw [hΔS, hRx, hΔ']
    linarith
  have hΔSc : Continuous (Δ S) := continuous_laplacian (contDiff_two_of_smooth hSc)
  have hev : ∀ᶠ z in 𝓝 x, 0 < Δ S z ∧ φ' z + (‖z - x‖ ^ 2) ^ 2 ≤ w (fold e z) ∧
      z ∈ ball (0 : E d) ρ :=
    (hΔSc.continuousAt.eventually (lt_mem_nhds hΔSx)).and (hstrict.and hB)
  obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.eventually_nhds_iff.1 hev
  have hδ : 0 < δ₀ / 2 := by positivity
  have hcb : ∀ z ∈ closedBall x (δ₀ / 2), 0 < Δ S z ∧
      φ' z + (‖z - x‖ ^ 2) ^ 2 ≤ w (fold e z) ∧ z ∈ ball (0 : E d) ρ := fun z hz ↦
    hδ₀sub (lt_of_le_of_lt (mem_closedBall.1 hz) (by linarith))
  have hRn : ∀ z, ‖R z - x‖ = ‖z - x‖ := fun z ↦ by
    conv_lhs => rw [← hRx]
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  have hRcb : ∀ z ∈ closedBall x (δ₀ / 2), R z ∈ closedBall x (δ₀ / 2) := fun z hz ↦ by
    rw [mem_closedBall, dist_eq_norm, hRn, ← dist_eq_norm]
    exact hz
  refine plane_case he hw hSc hSR hzero hδ ?_ fun z hz ↦ ⟨(hcb z hz).1, ?_, (hcb z hz).2.2⟩
  · simp only [hS, hRx, hφ', sub_self, norm_zero]
    rw [hT.2.1]
    ring
  · have h1 := (hcb z hz).2.1
    have h2 := (hcb (R z) (hRcb z hz)).2.1
    rw [hRn, hR, fold_planeReflection he] at h2
    simp only [hS]
    linarith

/-- **De Silva (2011), Lemma 2.6.** The even reflection `w ∘ fold e` of a solution of the linearized
problem is harmonic in `B_ρ` (viscosity harmonic by `isViscSuperharmonicOn_fold` applied to `w`
and `-w`, then `harmonicOnNhd_of_isViscHarmonic`). -/
theorem IsLinearizedSolution.harmonicOnNhd_fold {w : E d → ℝ} {e : E d} {ρ : ℝ} (he : ‖e‖ = 1)
    (hw : IsLinearizedSolution w e ρ) : HarmonicOnNhd (fun x ↦ w (fold e x)) (ball 0 ρ) := by
  have hsup := hw.isViscSuperharmonicOn_fold he
  have hsub : IsViscSubharmonicOn (fun x ↦ w (fold e x)) (ball 0 ρ) := by
    have h := (hw.neg.isViscSuperharmonicOn_fold he).neg
    have heq : (-fun x ↦ (-w) (fold e x)) = fun x ↦ w (fold e x) := by
      funext x
      simp
    rwa [heq] at h
  exact harmonicOnNhd_of_isViscHarmonic isOpen_ball (hw.continuousOn_fold he) hsub hsup

/-! ### The `C²` bound at the origin -/

/-- **Regularity of the linearized problem** (De Silva (2011), Lemma 2.6 and Lemma 4.1, Step 3). A
solution of the linearized problem on `B_{1/2}` with `|w| ≤ 1` has a tangential gradient `p` at the
origin (`⟪p, e⟫ = 0`, i.e. `w_n(0) = 0`) with `|w x - w 0 - ⟪p, x⟫| ≤ C r²` on `H⁺ ∩ B_r`,
`0 < r < 1/4`, `C = C(d)`.

Proof: the even reflection `h = w ∘ fold e` is harmonic in `B_{1/2}`
(`IsLinearizedSolution.harmonicOnNhd_fold`, Lemma 2.6), so the interior estimate
`norm_hessian_le_of_harmonic` at radius `1/4` bounds `‖D²h‖ ≤ 16 C_H` on `B_{1/4}`; the mean value
inequality, applied to `Dh` and then to `h - Dh(0)`, gives `|h x - h 0 - Dh(0) x| ≤ 16 C_H r²` on
`B_r`. The gradient `p = ∇h(0)` is tangential since `h` is reflection-invariant. Of `2 ≤ d` only
`1 ≤ d` is used, by the Hessian estimate. -/
theorem linearized_C2_at_origin (hd : 2 ≤ d) : ∃ C > 0, ∀ {w : E d → ℝ} {e : E d}, ‖e‖ = 1 →
    IsLinearizedSolution w e (1 / 2) →
    (∀ x, ⟪x, e⟫ ≥ 0 → x ∈ ball (0 : E d) (1 / 2) → |w x| ≤ 1) →
    ∃ p : E d, ⟪p, e⟫ = 0 ∧ ∀ r ∈ Ioo (0 : ℝ) (1 / 4), ∀ x ∈ ball (0 : E d) r, ⟪x, e⟫ ≥ 0 →
      |w x - w 0 - ⟪p, x⟫| ≤ C * r ^ 2 := by
  obtain ⟨CH, hCH, hhess⟩ := norm_hessian_le_of_harmonic (d := d) (by omega)
  refine ⟨16 * CH + 1, by positivity, fun {w e} he hw hbd ↦ ?_⟩
  set h : E d → ℝ := fun x ↦ w (fold e x) with hh
  have hharm : HarmonicOnNhd h (ball 0 (1 / 2)) := hw.harmonicOnNhd_fold he
  have hRh : ∀ y, h (planeReflection e y) = h y := fun y ↦ by
    simp only [hh, fold_planeReflection he]
  refine ⟨∇ h 0, ?_, fun r hr x hx hxe ↦ ?_⟩
  · rw [← fderiv_apply_eq_inner_gradient]
    exact fderiv_apply_eq_zero_of_comp_planeReflection he hRh (inner_zero_left _)
  have h14 : ball (0 : E d) (1 / 4) ⊆ ball 0 (1 / 2) := ball_subset_ball (by norm_num)
  have hr4 : ball (0 : E d) r ⊆ ball 0 (1 / 4) := ball_subset_ball hr.2.le
  have hHess : ∀ y ∈ ball (0 : E d) (1 / 4), ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ 16 * CH := by
    intro y hy
    have hsub : closedBall y (1 / 4) ⊆ ball (0 : E d) (1 / 2) := by
      intro z hz
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball_zero_iff] at hy ⊢
      calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
        _ < 1 / 2 := by linarith
    have := hhess h y (1 / 4) 1 (by norm_num) (hharm.mono hsub) fun z hz ↦
      hbd _ (inner_fold_nonneg he z) (by
        rw [mem_ball_zero_iff, norm_fold he]; exact mem_ball_zero_iff.1 (hsub hz))
    calc _ ≤ CH * 1 / (1 / 4) ^ 2 := this
      _ = 16 * CH := by ring
  have hdiff2 : ∀ y ∈ ball (0 : E d) (1 / 2), DifferentiableAt ℝ (fderiv ℝ h) y := fun y hy ↦
    ((hharm y hy).1.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdiff1 : ∀ y ∈ ball (0 : E d) (1 / 2), DifferentiableAt ℝ h y := fun y hy ↦
    (hharm y hy).1.differentiableAt (by norm_num)
  have hgrad : ∀ y ∈ ball (0 : E d) r, ‖fderiv ℝ h y - fderiv ℝ h 0‖ ≤ 16 * CH * r := by
    intro y hy
    have := (convex_ball (0 : E d) (1 / 4)).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ hdiff2 z (h14 hz)) hHess (mem_ball_self (by norm_num)) (hr4 hy)
    rw [sub_zero] at this
    calc _ ≤ 16 * CH * ‖y‖ := this
      _ ≤ 16 * CH * r := by gcongr; exact (mem_ball_zero_iff.1 hy).le
  have hmv := (convex_ball (0 : E d) r).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz ↦ hdiff1 z (h14 (hr4 hz))) hgrad (mem_ball_self hr.1) hx
  rw [sub_zero, Real.norm_eq_abs, fderiv_apply_eq_inner_gradient] at hmv
  have hx0 : h x = w x := by simp only [hh, fold_of_nonneg hxe]
  have h00 : h 0 = w 0 := by simp only [hh, fold_of_nonneg (inner_zero_left e).ge]
  rw [hx0, h00] at hmv
  have hxr : ‖x‖ ≤ r := (mem_ball_zero_iff.1 hx).le
  calc |w x - w 0 - ⟪∇ h 0, x⟫| ≤ 16 * CH * r * ‖x‖ := hmv
    _ ≤ 16 * CH * r * r := mul_le_mul_of_nonneg_left hxr (by have := hr.1; positivity)
    _ ≤ (16 * CH + 1) * r ^ 2 := by nlinarith [hr.1]

end EllipticBernoulli
