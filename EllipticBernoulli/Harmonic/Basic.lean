/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import ViscositySolns.Applications.Laplace.Weyl.Weyl
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import EllipticBernoulli.Basic.Setting
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Harmonic functions: Green's identity, weak harmonicity, smoothness

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`.

* `integral_laplacian_mul_eq_integral_mul_laplacian`: Green's second identity against a test
  function, `∫ Δχ · u = ∫ χ · Δu` for `u ∈ C²(U)` and `χ ∈ C^∞_c(U)`.
* `HarmonicOnNhd.weaklyHarmonicOn`: a harmonic function on an open set is weakly harmonic there,
  in the sense of `ViscositySolns.Analysis.WeaklyHarmonicOn`.
* `HarmonicOnNhd.contDiffOn_top`: by Weyl's lemma
  (`ViscositySolns.Analysis.weyl_of_weaklyHarmonicOn`) a harmonic function on an open set is
  `C^∞` there; `harmonicOnNhd_of_weaklyHarmonicOn` is the converse direction.
* `harmonicOnNhd_iff_contDiffOn_laplacian_eq_zero`: on an open set, `HarmonicOnNhd` is the same as
  `C²` with vanishing Laplacian (the encoding of harmonicity used in the definitions).

Dot notation caveat: the declarations `EllipticBernoulli.HarmonicOnNhd.*` live in our namespace,
so they are called as `HarmonicOnNhd.weaklyHarmonicOn hU hu` (not `hu.weaklyHarmonicOn`).

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, Berlin, 2001 (reprint of the 1998 edition), Theorem 2.1.

## Provenance

* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti, paths
  `TauCeti/Analysis/Sobolev/WeakDeriv/Laplacian.lean` (Green's identity, weak harmonicity),
  commit 90cca67c0c8e91cd30b0d46cb58101f8c5c59236. License: Apache-2.0. Upstream notice:
  `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`
* Extent: `integral_laplacian_mul_eq_integral_mul_laplacian` and
  `HarmonicOnNhd.weaklyHarmonicOn` (adapted).
* Changes: namespace changed to `EllipticBernoulli`; the weak-harmonicity API replaced by
  `ViscositySolns.Analysis.` names from the `viscosity_solns` dependency; module form
  (`module`, `public import`, `public section`). `HarmonicOnNhd.contDiffOn_top` and the bridge
  `harmonicOnNhd_iff_contDiffOn_laplacian_eq_zero` are new.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology
open scoped ContDiff Laplacian
open ViscositySolns.Analysis (WeaklyHarmonicOn weyl_of_weaklyHarmonicOn
  laplacian_eq_sum_fderiv_fderiv)

public section

namespace EllipticBernoulli

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Green

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **Green's second identity against a test function.** For `u` of class `C²` on an open set
`U` and a smooth `χ` with compact support in `U`, `∫ Δχ · u = ∫ χ · Δu`. -/
theorem integral_laplacian_mul_eq_integral_mul_laplacian {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ x, Δ χ x * u x ∂μ = ∫ x, χ x * Δ u x ∂μ := by
  set b := stdOrthonormalBasis ℝ E
  have hu1 : ContDiffOn ℝ 1 (fderiv ℝ u) U := hu.fderiv_of_isOpen hU (by norm_num)
  have hdu : ∀ v, ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ u y v) U := fun v ↦
    hu1.clm_apply contDiffOn_const
  have hu_diff : ∀ x ∈ U, DifferentiableAt ℝ u x := fun x hx ↦
    (hu.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)
  have hdu_diff : ∀ v, ∀ x ∈ U, DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y v) x := fun v x hx ↦
    ((hdu v).differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hddu_cont : ∀ v, ContinuousOn (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ u z v) y v) U :=
    fun v ↦ ((hdu v).continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hΔu : ∀ x ∈ U, Δ u x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) := by
    intro x hx
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [iteratedFDeriv_two_apply, fderiv_clm_apply
      ((hu1.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hx))
      (differentiableAt_const _)]
    simp
  have hΔχ : ∀ x, Δ χ x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) :=
    laplacian_eq_sum_fderiv_fderiv b (hχ.of_le (by norm_cast))
  -- smooth directional derivatives of `χ`, supported in `tsupport χ`
  have hDχ : ∀ v, ContDiff ℝ ∞ (fun y ↦ fderiv ℝ χ y v) ∧
      tsupport (fun y ↦ fderiv ℝ χ y v) ⊆ tsupport χ := fun v ↦
    ⟨(hχ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const, tsupport_fderiv_apply_subset ℝ v⟩
  have hDDχ : ∀ v, ContDiff ℝ ∞ (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ χ z v) y v) ∧
      tsupport (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ χ z v) y v) ⊆ tsupport χ := fun v ↦
    ⟨(((hDχ v).1).fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const,
      (tsupport_fderiv_apply_subset ℝ v).trans (hDχ v).2⟩
  -- integrability of the products
  have hint : ∀ φ g : E → ℝ, Continuous φ → tsupport φ ⊆ tsupport χ → ContinuousOn g U →
      Integrable (fun x ↦ φ x * g x) μ := by
    intro φ g hφ hφs hg
    have hφc : HasCompactSupport φ := hχc.mono' (subset_tsupport φ |>.trans hφs)
    exact ((hφ.continuousOn.mul hg).continuous_of_tsupport_subset hU
      ((tsupport_mul_subset_left).trans (hφs.trans hχU))).integrable_of_hasCompactSupport
      hφc.mul_right
  have hucont : ContinuousOn u U := hu.continuousOn
  have hdu_cont : ∀ v, ContinuousOn (fun y ↦ fderiv ℝ u y v) U := fun v ↦ (hdu v).continuousOn
  -- one direction
  have hdir : ∀ v, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y v) x v * u x ∂μ =
      ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v ∂μ := by
    intro v
    have e1 : ∫ x, fderiv ℝ χ x v * fderiv ℝ u x v ∂μ =
        -∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y v) x v * u x ∂μ :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hint _ _ (hDDχ v).1.continuous (hDDχ v).2 hucont)
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 (hdu_cont v))
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 hucont)
        (fun x _ ↦ ((hDχ v).1.differentiable (by simp)) x)
        (fun x hx ↦ hu_diff x (hχU ((hDχ v).2 hx)))
    have e2 : ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y v) x v ∂μ =
        -∫ x, fderiv ℝ χ x v * fderiv ℝ u x v ∂μ :=
      integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (hint _ _ (hDχ v).1.continuous (hDχ v).2 (hdu_cont v))
        (hint _ _ hχ.continuous le_rfl (hddu_cont v))
        (hint _ _ hχ.continuous le_rfl (hdu_cont v))
        (fun x _ ↦ (hχ.differentiable (by simp)) x)
        (fun x hx ↦ hdu_diff v x (hχU hx))
    linarith
  calc ∫ x, Δ χ x * u x ∂μ
      = ∑ i, ∫ x, fderiv ℝ (fun y ↦ fderiv ℝ χ y (b i)) x (b i) * u x ∂μ := by
        simp_rw [hΔχ, Finset.sum_mul]
        exact integral_finsetSum _ fun i _ ↦
          hint _ _ (hDDχ (b i)).1.continuous (hDDχ (b i)).2 hucont
    _ = ∑ i, ∫ x, χ x * fderiv ℝ (fun y ↦ fderiv ℝ u y (b i)) x (b i) ∂μ :=
        Finset.sum_congr rfl fun i _ ↦ hdir (b i)
    _ = ∫ x, χ x * Δ u x ∂μ := by
        rw [← integral_finsetSum _ fun i _ ↦ hint _ _ hχ.continuous le_rfl (hddu_cont (b i))]
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        by_cases hx : x ∈ U
        · simp only [hΔu x hx, Finset.mul_sum]
        · have : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU h)
          simp [this]

/-- **A harmonic function is weakly harmonic.** -/
theorem HarmonicOnNhd.weaklyHarmonicOn {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : HarmonicOnNhd u U) : WeaklyHarmonicOn μ u U := by
  intro χ hχ hχc hχU
  simp_rw [smul_eq_mul]
  rw [integral_laplacian_mul_eq_integral_mul_laplacian hU hu.contDiffOn hχ hχc hχU]
  refine integral_eq_zero_of_ae (ae_of_all _ fun x ↦ ?_)
  by_cases hx : x ∈ U
  · simp [(hu x hx).2.eq_of_nhds]
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hχU h)]

end Green

/-- A continuous weakly harmonic function (for some additive Haar measure) on an open set is
harmonic there (Weyl's lemma). -/
theorem harmonicOnNhd_of_weaklyHarmonicOn [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hcont : ContinuousOn u U)
    (hu : WeaklyHarmonicOn μ u U) : HarmonicOnNhd u U := by
  obtain ⟨hsmooth, hΔ⟩ := weyl_of_weaklyHarmonicOn hU hcont hu
  exact fun x hx ↦ ⟨(hsmooth.contDiffAt (hU.mem_nhds hx)).of_le (by norm_cast),
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy ↦ hΔ y hy⟩

/-- **Weyl: harmonic functions are smooth.** A harmonic function on an open set is `C^∞`
there. -/
theorem HarmonicOnNhd.contDiffOn_top {U : Set E} (hU : IsOpen U) {u : E → ℝ}
    (hu : HarmonicOnNhd u U) : ContDiffOn ℝ ∞ u U := by
  borelize E
  exact (weyl_of_weaklyHarmonicOn (μ := Measure.addHaar) hU hu.contDiffOn.continuousOn
    (HarmonicOnNhd.weaklyHarmonicOn hU hu)).1

/-- A harmonic function on a neighbourhood of a point is `C^∞` at that point. -/
theorem HarmonicAt.contDiffAt_top {u : E → ℝ} {x : E} (hu : HarmonicAt u x) :
    ContDiffAt ℝ ∞ u x := by
  have hU : IsOpen {y : E | HarmonicAt u y} := isOpen_setOf_harmonicAt u
  exact (HarmonicOnNhd.contDiffOn_top hU fun y hy ↦ hy).contDiffAt (hU.mem_nhds hu)

/-- **Dilation.** `Δ (f (c • ·)) x = c² Δ f (c • x)`. No differentiability hypothesis. (Private
to avoid a clash with `laplacian_comp_smul` in `Viscosity/Jet.lean`; use
`laplacian_comp_add_smul`.) -/
private theorem laplacian_comp_smul' (f : E → ℝ) (c : ℝ) (x : E) :
    Δ (fun y ↦ f (c • y)) x = c ^ 2 * Δ f (c • x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  set g : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E c hc).toContinuousLinearEquiv
  have hfg : (fun y ↦ f (c • y)) = f ∘ g := rfl
  set b := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    laplacian_eq_iteratedFDeriv_orthonormalBasis _ b, hfg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := g.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at this
  rw [this, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have h2 : (fun j ↦ (g : E →L[ℝ] E) (![b i, b i] j)) = fun j ↦ (fun _ ↦ c) j • ![b i, b i] j := by
    ext j; rfl
  rw [h2, ContinuousMultilinearMap.map_smul_univ]
  simp [g]

/-- **Affine change of variables.** `Δ (f (a + c • ·)) x = c² Δ f (a + c • x)`. -/
theorem laplacian_comp_add_smul (f : E → ℝ) (a : E) (c : ℝ) (x : E) :
    Δ (fun y ↦ f (a + c • y)) x = c ^ 2 * Δ f (a + c • x) := by
  have h : (fun y ↦ f (a + c • y)) = fun y ↦ (fun w ↦ f (w + a)) (c • y) := by
    ext y; rw [add_comm]
  rw [h, laplacian_comp_smul' (fun w ↦ f (w + a)), ViscositySolns.Analysis.laplacian_comp_add_right,
    add_comm]

/-- Harmonicity is invariant under the affine maps `z ↦ a + c • z`. -/
theorem HarmonicAt.comp_add_smul {u : E → ℝ} {a : E} {c : ℝ} {y : E}
    (hu : HarmonicAt u (a + c • y)) : HarmonicAt (fun z ↦ u (a + c • z)) y := by
  have hcont : Continuous fun z : E ↦ a + c • z := by fun_prop
  refine ⟨hu.1.comp y (by fun_prop), ?_⟩
  have := hu.2.comp_tendsto (hcont.tendsto y)
  filter_upwards [this] with z hz
  simp only [Function.comp_apply, Pi.zero_apply] at hz
  rw [laplacian_comp_add_smul, hz, mul_zero, Pi.zero_apply]

/-- Harmonicity on a set is invariant under the affine maps `z ↦ a + c • z`. -/
theorem HarmonicOnNhd.comp_add_smul {u : E → ℝ} {S : Set E} (hu : HarmonicOnNhd u S) (a : E)
    (c : ℝ) : HarmonicOnNhd (fun z ↦ u (a + c • z)) ((fun z ↦ a + c • z) ⁻¹' S) :=
  fun _ hz ↦ HarmonicAt.comp_add_smul (hu _ hz)

/-- `E d` is nontrivial as soon as `1 ≤ d`. -/
theorem nontrivial_E_of_one_le {d : ℕ} (hd : 1 ≤ d) : Nontrivial (EllipticBernoulli.E d) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  infer_instance

/-- **Bridge to the `C²` encoding of harmonicity.** On an open set, `u` is
harmonic iff it is `C²` with vanishing Laplacian. -/
theorem harmonicOnNhd_iff_contDiffOn_laplacian_eq_zero {V : Set E} (hV : IsOpen V)
    {u : E → ℝ} : HarmonicOnNhd u V ↔ ContDiffOn ℝ 2 u V ∧ ∀ x ∈ V, Δ u x = 0 := by
  refine ⟨fun hu ↦ ⟨hu.contDiffOn, fun x hx ↦ (hu x hx).2.eq_of_nhds⟩, fun ⟨hu, hΔ⟩ x hx ↦
    ⟨hu.contDiffAt (hV.mem_nhds hx), Filter.eventuallyEq_of_mem (hV.mem_nhds hx) hΔ⟩⟩

end EllipticBernoulli
