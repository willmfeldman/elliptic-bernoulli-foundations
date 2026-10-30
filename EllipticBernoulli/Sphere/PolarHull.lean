/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.Polarization
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# The closure of the polarization orbit

Fix a unit vector `N` and `f : 𝕊 → ℝ`. The polarization orbit `PolarOrbit N f` is the set of
functions obtained from `f` by finitely many polarizations `(·)^e` with `|e| = 1` and
`⟨N, e⟩ > 0`, and `polarHull N f` is the closure of the orbit in `C(𝕊, ℝ)` (sup norm). This file
proves the properties of the hull used in the polarization proof of the Pólya–Szegő inequality
(`Sphere/PolyaSzego.lean`), for `f` that is `L`-Lipschitz with values in `[0, M]`:

* `isCompact_polarHull`: the hull is compact (Arzelà–Ascoli,
  `ArzelaAscoli.isCompact_of_equicontinuous`);
* `lipschitzWith_of_mem_polarHull`, `mem_Icc_of_mem_polarHull`: every element of the hull is
  `L`-Lipschitz with values in `[0, M]`;
* `map_eq_of_mem_polarHull`: every element of the hull is equimeasurable with `f`. The set of
  equimeasurable continuous functions is closed because `∫ Ψ ∘ g dσ` depends continuously on `g`
  for bounded continuous `Ψ`, and finite measures on `ℝ` are determined by these integrals;
* `polarizeCM_mem_polarHull`: the hull is invariant under every admissible polarization, since
  polarization is `1`-Lipschitz in the sup norm (`dist_polarizeCM_le`).

Elements of the orbit also have the Dirichlet energy of `f` (`PolarOrbit.sphDirichlet_eq`, for
`d ≥ 2`).
-/

open MeasureTheory Metric Set Filter Topology
open scoped NNReal BoundedContinuousFunction

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public noncomputable section

/-- The polarization orbit of `f`: the functions obtained from `f` by finitely many polarizations
`(·)^e` with `|e| = 1` and `⟨N, e⟩ > 0`. -/
inductive PolarOrbit (N : E d) (f : sphere (0 : E d) 1 → ℝ) : (sphere (0 : E d) 1 → ℝ) → Prop
  | self : PolarOrbit N f f
  | polarize {g : sphere (0 : E d) 1 → ℝ} {e : E d} :
      PolarOrbit N f g → ‖e‖ = 1 → 0 < inner ℝ N e → PolarOrbit N f (polarize e g)

/-- The closure in `C(𝕊, ℝ)` (sup norm) of the polarization orbit of `f`. -/
def polarHull (N : E d) (f : sphere (0 : E d) 1 → ℝ) : Set C(sphere (0 : E d) 1, ℝ) :=
  closure {g | PolarOrbit N f g}

/-- Polarization of a continuous function, as a continuous function. -/
def polarizeCM (e : E d) (g : C(sphere (0 : E d) 1, ℝ)) : C(sphere (0 : E d) 1, ℝ) :=
  ⟨polarize e g, continuous_polarize g.continuous⟩

end

public section

@[simp]
theorem coe_polarizeCM (e : E d) (g : C(sphere (0 : E d) 1, ℝ)) :
    (polarizeCM e g : sphere (0 : E d) 1 → ℝ) = polarize e g := rfl

/-! ### The orbit -/

namespace PolarOrbit

variable {N : E d} {f g : sphere (0 : E d) 1 → ℝ}

theorem lipschitzWith {L : ℝ≥0} (hf : LipschitzWith L f) (hg : PolarOrbit N f g) :
    LipschitzWith L g := by
  induction hg with
  | self => exact hf
  | polarize _ he _ ih => exact lipschitzWith_polarize he ih

theorem mem_Icc {M : ℝ} (hf : ∀ ω, f ω ∈ Icc 0 M) (hg : PolarOrbit N f g) (ω) :
    g ω ∈ Icc 0 M := by
  induction hg generalizing ω with
  | self => exact hf ω
  | polarize _ _ _ ih =>
    exact ⟨polarize_nonneg (fun ω ↦ (ih ω).1) ω, polarize_le (fun ω ↦ (ih ω).2) ω⟩

theorem measurable (hf : Measurable f) (hg : PolarOrbit N f g) : Measurable g := by
  induction hg with
  | self => exact hf
  | polarize _ _ _ ih => exact measurable_polarize _ ih

theorem map_eq (hf : Measurable f) (hg : PolarOrbit N f g) :
    ((volume : Measure (E d)).toSphere).map g = ((volume : Measure (E d)).toSphere).map f := by
  induction hg with
  | self => rfl
  | polarize hg' he _ ih => rw [map_polarize he (hg'.measurable hf), ih]

theorem sphDirichlet_eq (hd : 2 ≤ d) {L : ℝ≥0} (hf : LipschitzWith L f)
    (hg : PolarOrbit N f g) : sphDirichlet g = sphDirichlet f := by
  induction hg with
  | self => rfl
  | polarize hg' he _ ih => rw [sphDirichlet_polarize hd he (hg'.lipschitzWith hf), ih]

end PolarOrbit

/-! ### Closed conditions in `C(𝕊, ℝ)` -/

section Closed

private theorem isClosed_setOf_lipschitzWith (L : ℝ≥0) :
    IsClosed {g : C(sphere (0 : E d) 1, ℝ) | LipschitzWith L g} :=
  (isClosed_setOfPred_lipschitzWith L).preimage
    (continuous_pi fun ω ↦ continuous_eval_const ω)

private theorem isClosed_setOf_mem_Icc (M : ℝ) :
    IsClosed {g : C(sphere (0 : E d) 1, ℝ) | ∀ ω, g ω ∈ Icc 0 M} := by
  rw [ofPred_forall]
  exact isClosed_iInter fun ω ↦ isClosed_Icc.preimage (continuous_eval_const ω)

/-- `∫ Ψ ∘ g dσ` depends continuously on `g ∈ C(𝕊, ℝ)` for bounded continuous `Ψ`. -/
theorem tendsto_integral_comp_of_tendsto (Ψ : ℝ →ᵇ ℝ) {g : ℕ → C(sphere (0 : E d) 1, ℝ)}
    {g₀ : C(sphere (0 : E d) 1, ℝ)} (hg : Tendsto g atTop (𝓝 g₀)) :
    Tendsto (fun n ↦ ∫ ω, Ψ (g n ω) ∂(volume : Measure (E d)).toSphere) atTop
      (𝓝 (∫ ω, Ψ (g₀ ω) ∂(volume : Measure (E d)).toSphere)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖Ψ‖) (fun n ↦ ?_)
    (integrable_const _) (fun n ↦ ae_of_all _ fun ω ↦ Ψ.norm_coe_le_norm _) ?_
  · exact (Ψ.continuous.comp (g n).continuous).aestronglyMeasurable
  · refine ae_of_all _ fun ω ↦ ?_
    exact (Ψ.continuous.tendsto _).comp ((continuous_eval_const ω).tendsto g₀ |>.comp hg)

/-- The continuous functions with a prescribed distribution form a closed set. -/
private theorem isClosed_setOf_map_eq (ν : Measure ℝ) [IsFiniteMeasure ν] :
    IsClosed {g : C(sphere (0 : E d) 1, ℝ) |
      ((volume : Measure (E d)).toSphere).map g = ν} := by
  refine isSeqClosed_iff_isClosed.1 fun g g₀ hg hlim ↦ ?_
  simp only [mem_ofPred_eq] at hg ⊢
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun Ψ ↦ ?_
  rw [integral_map g₀.continuous.aemeasurable Ψ.continuous.aestronglyMeasurable]
  have hconst : ∀ n, ∫ ω, Ψ (g n ω) ∂(volume : Measure (E d)).toSphere = ∫ x, Ψ x ∂ν :=
    fun n ↦ by
      rw [← hg n, integral_map (g n).continuous.aemeasurable Ψ.continuous.aestronglyMeasurable]
  have h := tendsto_integral_comp_of_tendsto Ψ hlim
  simp_rw [hconst] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end Closed

/-! ### The hull -/

section Hull

variable {N : E d} {f : sphere (0 : E d) 1 → ℝ}

theorem lipschitzWith_of_mem_polarHull {L : ℝ≥0} (hf : LipschitzWith L f)
    {g : C(sphere (0 : E d) 1, ℝ)} (hg : g ∈ polarHull N f) : LipschitzWith L g :=
  closure_minimal (fun _ h ↦ PolarOrbit.lipschitzWith hf h) (isClosed_setOf_lipschitzWith L) hg

theorem mem_Icc_of_mem_polarHull {M : ℝ} (hf : ∀ ω, f ω ∈ Icc 0 M)
    {g : C(sphere (0 : E d) 1, ℝ)} (hg : g ∈ polarHull N f) (ω : sphere (0 : E d) 1) :
    g ω ∈ Icc 0 M :=
  closure_minimal (fun _ h ↦ PolarOrbit.mem_Icc hf h) (isClosed_setOf_mem_Icc M) hg ω

/-- **Equimeasurability on the hull.** -/
theorem map_eq_of_mem_polarHull (hf : Measurable f) {g : C(sphere (0 : E d) 1, ℝ)}
    (hg : g ∈ polarHull N f) :
    ((volume : Measure (E d)).toSphere).map g = ((volume : Measure (E d)).toSphere).map f :=
  closure_minimal (fun _ h ↦ PolarOrbit.map_eq hf h) (isClosed_setOf_map_eq _) hg

theorem mem_polarHull_self {L : ℝ≥0} (hf : LipschitzWith L f) :
    (⟨f, hf.continuous⟩ : C(sphere (0 : E d) 1, ℝ)) ∈ polarHull N f :=
  subset_closure PolarOrbit.self

/-- Polarization is `1`-Lipschitz in the sup norm. -/
theorem dist_polarizeCM_le (e : E d) (g h : C(sphere (0 : E d) 1, ℝ)) :
    dist (polarizeCM e g) (polarizeCM e h) ≤ dist g h := by
  refine (ContinuousMap.dist_le dist_nonneg).2 fun ω ↦ ?_
  rw [Real.dist_eq]
  exact abs_polarize_sub_polarize_le e
    (fun ω ↦ by rw [← Real.dist_eq]; exact ContinuousMap.dist_apply_le_dist ω) ω

theorem continuous_polarizeCM (e : E d) :
    Continuous (polarizeCM e : C(sphere (0 : E d) 1, ℝ) → C(sphere (0 : E d) 1, ℝ)) :=
  (LipschitzWith.of_dist_le_mul fun g h ↦ by
    rw [NNReal.coe_one, one_mul]; exact dist_polarizeCM_le e g h).continuous

/-- **Invariance of the hull.** -/
theorem polarizeCM_mem_polarHull {e : E d} (he : ‖e‖ = 1) (hNe : 0 < inner ℝ N e)
    {g : C(sphere (0 : E d) 1, ℝ)} (hg : g ∈ polarHull N f) :
    polarizeCM e g ∈ polarHull N f := by
  refine closure_mono ?_ (image_closure_subset_closure_image (continuous_polarizeCM e)
    (mem_image_of_mem _ hg))
  rintro _ ⟨h, hh, rfl⟩
  exact PolarOrbit.polarize hh he hNe

/-- **Compactness of the hull**, by Arzelà–Ascoli. -/
theorem isCompact_polarHull {L : ℝ≥0} (hf : LipschitzWith L f) {M : ℝ}
    (hfM : ∀ ω, f ω ∈ Icc 0 M) : IsCompact (polarHull N f) := by
  set A : Set C(sphere (0 : E d) 1, ℝ) := {g | LipschitzWith L g ∧ ∀ ω, g ω ∈ Icc 0 M}
  have hsub : polarHull N f ⊆ A := fun g hg ↦
    ⟨lipschitzWith_of_mem_polarHull hf hg, mem_Icc_of_mem_polarHull hfM hg⟩
  refine IsCompact.of_isClosed_subset ?_ isClosed_closure hsub
  refine ArzelaAscoli.isCompact_of_equicontinuous A ?_ ?_
  · have himg : ContinuousMap.toFun '' A =
        {F : sphere (0 : E d) 1 → ℝ | LipschitzWith L F ∧ ∀ ω, F ω ∈ Icc 0 M} := by
      ext F
      constructor
      · rintro ⟨g, hg, rfl⟩; exact hg
      · intro hF; exact ⟨⟨F, hF.1.continuous⟩, hF, rfl⟩
    have hIcc : IsClosed {F : sphere (0 : E d) 1 → ℝ | ∀ ω, F ω ∈ Icc 0 M} := by
      rw [ofPred_forall]
      exact isClosed_iInter fun ω ↦ isClosed_Icc.preimage (continuous_apply ω)
    rw [himg]
    exact IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ ↦ isCompact_Icc)
      ((isClosed_setOfPred_lipschitzWith L).inter hIcc) fun F hF ω _ ↦ hF.2 ω
  · exact (LipschitzWith.uniformEquicontinuous _ L fun g ↦ g.2.1).equicontinuous

end Hull

end

end EllipticBernoulli
