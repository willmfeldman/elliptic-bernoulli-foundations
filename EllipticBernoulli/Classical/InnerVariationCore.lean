/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Classical
import EllipticBernoulli.Classical.InnerVariationCalculus
import EllipticBernoulli.Harmonic.Basic
import EllipticBernoulli.Sobolev.Cutoff
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Viscosity.Calculus
import EllipticBernoulli.Common.Calculus
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The inner-variation identity for classical solutions, given the gradient limit

`IsClassicalSolution.integral_innerVarIntegrand_eq_zero_of_tendsto`: if `u` is a classical
solution on `U` with `Q` Lipschitz on `U` and `Q ≥ c > 0`, and `‖∇u(x)‖ → Q(x₀)` as `x → x₀`
inside `{u > 0}` at every free boundary point `x₀` (proved in `Classical/Gradient.lean`),
then for every Lipschitz field `ξ` with compact support in `U`
`∫_U ((|∇u|² + Q²χ) div ξ − 2⟪∇u, Dξ ∇u⟫ + D(Q²)(ξ) χ) = 0`, `χ = 1_{{u>0} ∩ U}`.

## Proof

Let `Ω = {u > 0} ∩ U` and `f = (|∇u|² + Q²) div ξ − 2⟪∇u, Dξ∇u⟫ + D(Q²)(ξ)`. On `U \ Ω` the
integrand vanishes (`u` has a local minimum there, so `∇u = 0`, and `χ = 0`), so the integral is
`∫_Ω f`. Let `η = cutη` (smooth, `0` on `(-∞, 1/2]`, `1` on `[1, ∞)`, `η' ≥ 0`).

* **Identity 1.** With `V = (|∇u|² + Q²) ξ − 2⟪∇u, ξ⟫ ∇u`, `div V = f` a.e. on `Ω` (the `D²u`
  terms cancel by symmetry, `Δu = 0`), and `⟪∇u, V⟫ = ⟪∇u, ξ⟫ (Q² − |∇u|²)`. The cut-off
  divergence identity (`integral_cutoff_divergence_eq_zero`) gives
  `∫_Ω η(u/ε) f = −∫_Ω η'(u/ε) ε⁻¹ ⟪∇u, ξ⟫ (Q² − |∇u|²)`.
* **Identity 2** (replaces a measure bound for `{0 < u < ε}`). With a smooth cut-off `ψ = 1` on
  `spt ξ`, the same identity for `V = ψ ∇u` gives
  `∫_Ω η'(u/ε) ε⁻¹ ψ |∇u|² = −∫_Ω η(u/ε) ⟪∇ψ, ∇u⟫ ≤ L ∫ |∇ψ|`, uniformly in `ε`.
* **Boundary term.** By the gradient limit and compactness of `spt ξ`, `| |∇u| − Q | < δ` on
  `spt ξ ∩ {0 < u < ε₀}`; there `|∇u| ≥ c/2`, so `|⟪∇u, ξ⟫ (Q² − |∇u|²)| ≤ C δ ψ |∇u|²`, and
  Identity 2 bounds the boundary term by `C' δ`.
* **Main term.** `∫_Ω η(u/ε) f → ∫_Ω f` by dominated convergence, so `|∫_Ω f| ≤ C' δ` for
  every small `δ > 0`.

No dimension hypothesis is needed.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient Laplacian RealInnerProductSpace NNReal ContDiff

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Pointwise identities -/

/-- The divergence of `V = (|∇u|² + Q²) ξ − 2⟪∇u, ξ⟫ ∇u` at a point where `u` is `C²` and
harmonic and `Q`, `ξ` are differentiable. -/
private theorem divergence_stressField {u Q : E d → ℝ} {ξ : E d → E d} {x : E d}
    (hu : ContDiffAt ℝ 2 u x) (hlap : Δ u x = 0) (hQ : DifferentiableAt ℝ Q x)
    (hξ : DifferentiableAt ℝ ξ x) :
    divergence (fun y ↦ (‖∇ u y‖ ^ 2 + Q y ^ 2) • ξ y - (2 * ⟪∇ u y, ξ y⟫) • ∇ u y) x =
      (‖∇ u x‖ ^ 2 + Q x ^ 2) * divergence ξ x - 2 * ⟪∇ u x, fderiv ℝ ξ x (∇ u x)⟫ +
        fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x) := by
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hg : DifferentiableAt ℝ (∇ u) x := differentiableAt_gradient hDu
  have hsymm : IsSymmSndFDerivAt ℝ u x := hu.isSymmSndFDerivAt (by simp)
  have hn2 : DifferentiableAt ℝ (fun y ↦ ‖∇ u y‖ ^ 2) x := hg.norm_sq ℝ
  have hQ2 : DifferentiableAt ℝ (fun y ↦ Q y ^ 2) x := hQ.pow 2
  have hA : DifferentiableAt ℝ (fun y ↦ ‖∇ u y‖ ^ 2 + Q y ^ 2) x := hn2.add hQ2
  have hi : DifferentiableAt ℝ (fun y ↦ ⟪∇ u y, ξ y⟫) x := hg.inner ℝ hξ
  have hB : DifferentiableAt ℝ (fun y ↦ 2 * ⟪∇ u y, ξ y⟫) x := hi.const_mul 2
  rw [divergence_sub (V := fun y ↦ (‖∇ u y‖ ^ 2 + Q y ^ 2) • ξ y)
    (W := fun y ↦ (2 * ⟪∇ u y, ξ y⟫) • ∇ u y) (hA.smul hξ) (hB.smul hg),
    divergence_smul hA hξ, divergence_smul hB hg,
    divergence_gradient hDu, hlap, fderiv_fun_add hn2 hQ2, fderiv_const_mul hi]
  have e1 : fderiv ℝ (fun y ↦ ‖∇ u y‖ ^ 2) x (ξ x) = 2 * ⟪∇ u x, fderiv ℝ (∇ u) x (ξ x)⟫ := by
    rw [(hg.hasFDerivAt.norm_sq).fderiv]
    simp
  have e2 : fderiv ℝ (fun y ↦ ⟪∇ u y, ξ y⟫) x (∇ u x) =
      ⟪∇ u x, fderiv ℝ ξ x (∇ u x)⟫ + ⟪fderiv ℝ (∇ u) x (∇ u x), ξ x⟫ :=
    fderiv_inner_apply ℝ hg hξ _
  have e3 : ⟪∇ u x, fderiv ℝ (∇ u) x (ξ x)⟫ = ⟪fderiv ℝ (∇ u) x (∇ u x), ξ x⟫ := by
    rw [real_inner_comm, inner_fderiv_gradient hDu, inner_fderiv_gradient hDu, hsymm]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [e1, e2, e3]
  ring

/-! ### The gradient limit, uniformly on compact sets -/

/-- From the gradient limit at free boundary points: on a compact `K ⊆ U`,
`| |∇u| − Q | < δ` at points of `{0 < u < ε₀} ∩ K`. -/
private theorem exists_eps_abs_norm_gradient_sub_lt {U K : Set (E d)} {u Q : E d → ℝ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hucont : ContinuousOn u U)
    (hQcont : ContinuousOn Q U)
    (hgrad : ∀ x₀ ∈ freeBoundary u U,
      Tendsto (fun x ↦ ‖∇ u x‖) (𝓝[posSet u U] x₀) (𝓝 (Q x₀))) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ > 0, ∀ x ∈ posSet u U ∩ K, u x < ε₀ → |‖∇ u x‖ - Q x| < δ := by
  by_contra hcon
  push Not at hcon
  choose x hx hxu hxδ using fun n : ℕ ↦ hcon (1 / (n + 1)) Nat.one_div_pos_of_nat
  obtain ⟨z, hzK, φ, hφ, hlim⟩ := hK.tendsto_subseq fun n ↦ (hx n).2
  have hzU : z ∈ U := hKU hzK
  have hΩ : IsOpen (posSet u U) := hucont.isOpen_inter_preimage hU isOpen_Ioi
  -- `u z = 0`
  have huz : u z = 0 := by
    have h1 : Tendsto (fun n ↦ u (x (φ n))) atTop (𝓝 (u z)) :=
      ((hucont.continuousAt (hU.mem_nhds hzU)).tendsto).comp hlim
    have h2 : Tendsto (fun n ↦ u (x (φ n))) atTop (𝓝 0) := by
      refine squeeze_zero (fun n ↦ (hx (φ n)).1.2.le) (fun n ↦ (hxu (φ n)).le) ?_
      exact (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  -- `z` is a free boundary point
  have hzfb : z ∈ freeBoundary u U := by
    refine ⟨⟨mem_closure_of_tendsto hlim (Eventually.of_forall fun n ↦ (hx (φ n)).1), ?_⟩, hzU⟩
    rw [hΩ.interior_eq]
    exact fun h ↦ (lt_irrefl (0 : ℝ)) (huz ▸ h.2)
  have hlimΩ : Tendsto (x ∘ φ) atTop (𝓝[posSet u U] z) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n ↦ (hx (φ n)).1⟩
  have h3 : Tendsto (fun n ↦ |‖∇ u (x (φ n))‖ - Q (x (φ n))|) atTop (𝓝 |Q z - Q z|) :=
    (((hgrad z hzfb).comp hlimΩ).sub
      (((hQcont.continuousAt (hU.mem_nhds hzU)).tendsto).comp hlim)).abs
  rw [sub_self, abs_zero] at h3
  exact absurd (ge_of_tendsto h3 (Eventually.of_forall fun n ↦ hxδ (φ n))) (not_le.2 hδ)

/-! ### Measurability and integrability helpers -/

private theorem measurable_divergence (ξ : E d → E d) : Measurable (divergence ξ) := by
  have : Continuous fun T : E d →L[ℝ] E d ↦ LinearMap.trace ℝ (E d) T.toLinearMap :=
    ((LinearMap.trace ℝ (E d)).comp (ContinuousLinearMap.coeLM ℝ)).continuous_of_finiteDimensional
  exact this.measurable.comp (measurable_fderiv ℝ ξ)

private theorem abs_divergence_le (ξ : E d → E d) (x : E d) :
    |divergence ξ x| ≤ Module.finrank ℝ (E d) * ‖fderiv ℝ ξ x‖ := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (E d))]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |⟪stdOrthonormalBasis ℝ (E d) i,
        (fderiv ℝ ξ x : E d →ₗ[ℝ] E d) (stdOrthonormalBasis ℝ (E d) i)⟫|
      ≤ ∑ _i : Fin (Module.finrank ℝ (E d)), ‖fderiv ℝ ξ x‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        refine (abs_real_inner_le_norm _ _).trans ?_
        rw [(stdOrthonormalBasis ℝ (E d)).orthonormal.1 i, one_mul]
        refine ((fderiv ℝ ξ x).le_opNorm _).trans ?_
        rw [(stdOrthonormalBasis ℝ (E d)).orthonormal.1 i, mul_one]
    _ = _ := by simp

/-- A function continuous on the measurable set `Ω` and vanishing on `Ω` off a compact `C ⊆ Ω`
is integrable on `Ω`. -/
private theorem integrableOn_of_continuousOn_of_eq_zero {Ω C : Set (E d)} {g : E d → ℝ}
    (hΩ : MeasurableSet Ω) (hC : IsCompact C) (hCΩ : C ⊆ Ω) (hg : ContinuousOn g Ω)
    (h0 : ∀ x ∈ Ω, x ∉ C → g x = 0) : IntegrableOn g Ω :=
  ((hg.mono hCΩ).integrableOn_compact hC).of_forall_sdiff_eq_zero hΩ fun x hx ↦ h0 x hx.1 hx.2

/-! ### The main theorem -/

/-- **The inner-variation identity, given the gradient limit.** For a classical
solution `u` on `U` with `Q` Lipschitz on `U` and `Q ≥ c > 0`, such that `‖∇u(x)‖ → Q(x₀)` as
`x → x₀` in `{u > 0}` at every free boundary point `x₀`, the inner-variation identity holds for
every Lipschitz field `ξ` compactly supported in `U`. -/
theorem IsClassicalSolution.integral_innerVarIntegrand_eq_zero_of_tendsto {d : ℕ}
    {U : Set (E d)} {Q u : E d → ℝ} {ξ : E d → E d}
    (hu : IsClassicalSolution U Q u) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ y ∈ U, c ≤ Q y) (hξ : ∃ K, LipschitzWith K ξ)
    (hξc : HasCompactSupport ξ) (hξU : tsupport ξ ⊆ U)
    (hgrad : ∀ x₀ ∈ freeBoundary u U,
      Tendsto (fun x ↦ ‖∇ u x‖) (𝓝[posSet u U] x₀) (𝓝 (Q x₀))) :
    ∫ x in U, innerVarIntegrand Q u ((posSet u U).indicator 1) ξ x = 0 := by
  obtain ⟨L, hL⟩ := hu.lipschitzOnWith
  obtain ⟨KQ, hQL⟩ := hQ
  obtain ⟨c, hc, hcQ⟩ := hQpos
  obtain ⟨Kξ, hξL⟩ := hξ
  have hU : IsOpen U := hu.isOpen
  have hucont : ContinuousOn u U := hL.continuousOn
  have hQcont : ContinuousOn Q U := hQL.continuousOn
  set Ω := posSet u U with hΩdef
  have hΩ : IsOpen Ω := hucont.isOpen_inter_preimage hU isOpen_Ioi
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hΩU : Ω ⊆ U := fun x hx ↦ hx.1
  set K := tsupport ξ with hKdef
  have hK : IsCompact K := hξc
  -- regularity of `u` in `Ω`
  have huH : HarmonicOnNhd u Ω := fun x hx ↦ hu.harmonicAt x hx.1 hx.2
  have huC : ContDiffOn ℝ ∞ u Ω := HarmonicOnNhd.contDiffOn_top hΩ huH
  have hu2 : ∀ x ∈ Ω, ContDiffAt ℝ 2 u x := fun x hx ↦
    (huC.contDiffAt (hΩ.mem_nhds hx)).of_le (by norm_cast)
  have hu1 : ContDiffOn ℝ 1 u Ω := huC.of_le (by norm_cast)
  have hlap : ∀ x ∈ Ω, Δ u x = 0 := fun x hx ↦ (huH x hx).2.self_of_nhds
  have hgC1 : ∀ x ∈ Ω, ContDiffAt ℝ 1 (∇ u) x := fun x hx ↦
    contDiffAt_gradient (n := 1) (hu2 x hx)
  have hgcont : ContinuousOn (∇ u) Ω := fun x hx ↦ (hgC1 x hx).continuousAt.continuousWithinAt
  have hgL : ∀ x ∈ U, ‖∇ u x‖ ≤ L := fun x hx ↦ by
    rw [norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hx) hL
  have hg0 : ∀ x ∈ U, x ∉ Ω → ∇ u x = 0 := by
    intro x hx hxΩ
    have hux : u x = 0 := le_antisymm (not_lt.1 fun h ↦ hxΩ ⟨hx, h⟩) (hu.nonneg x hx)
    have hmin : IsLocalMin u x := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [hux]; exact hu.nonneg y hy
    rw [gradient, hmin.fderiv_eq_zero, LinearIsometryEquiv.map_zero]
  -- bounds on `Q` and `ξ`
  obtain ⟨MQ₀, hMQ₀⟩ := hK.exists_bound_of_continuousOn (hQcont.mono hξU)
  set MQ := max MQ₀ 0
  have hMQ : ∀ x ∈ K, |Q x| ≤ MQ := fun x hx ↦ (hMQ₀ x hx).trans (le_max_left _ _)
  have hMQ0 : 0 ≤ MQ := le_max_right _ _
  obtain ⟨Mξ₀, hMξ₀⟩ := hK.exists_bound_of_continuousOn hξL.continuous.continuousOn
  set Mξ := max Mξ₀ 0
  have hMξ0 : 0 ≤ Mξ := le_max_right _ _
  have hMξ : ∀ x, ‖ξ x‖ ≤ Mξ := fun x ↦ by
    by_cases hx : x ∈ K
    · exact (hMξ₀ x hx).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hx, norm_zero]; exact hMξ0
  -- the integrand on `Ω`
  set f : E d → ℝ := fun x ↦ (‖∇ u x‖ ^ 2 + Q x ^ 2) * divergence ξ x -
    2 * ⟪∇ u x, fderiv ℝ ξ x (∇ u x)⟫ + fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x) with hf_def
  have hf0 : ∀ x, x ∉ K → f x = 0 := fun x hx ↦ by
    simp [hf_def, divergence, fderiv_of_notMem_tsupport ℝ hx, image_eq_zero_of_notMem_tsupport hx]
  have hred : ∫ x in U, innerVarIntegrand Q u ((posSet u U).indicator 1) ξ x =
      ∫ x in Ω, f x := by
    have h : EqOn (fun x ↦ innerVarIntegrand Q u ((posSet u U).indicator 1) ξ x)
        (Ω.indicator f) U := by
      intro x hx
      by_cases hxΩ : x ∈ Ω
      · simp [innerVarIntegrand, hf_def, hxΩ, ← hΩdef]
      · simp [innerVarIntegrand, hxΩ, hg0 x hx hxΩ, ← hΩdef]
    rw [setIntegral_congr_fun hU.measurableSet h, setIntegral_indicator hΩm,
      inter_eq_self_of_subset_right hΩU]
  -- measurability of `f` on `Ω`
  have hgm : Measurable (∇ u) := measurable_gradient u
  have hfm : AEStronglyMeasurable f (volume.restrict Ω) := by
    have hQm : AEStronglyMeasurable Q (volume.restrict Ω) :=
      (hQcont.mono hΩU).aestronglyMeasurable hΩm
    have h1 : Measurable fun x ↦ ⟪∇ u x, fderiv ℝ ξ x (∇ u x)⟫ :=
      continuous_inner.measurable.comp (hgm.prodMk
        ((continuous_fst.clm_apply continuous_snd).measurable.comp
          ((measurable_fderiv ℝ ξ).prodMk hgm)))
    have h2 : Measurable fun x ↦ fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x) :=
      (continuous_fst.clm_apply continuous_snd).measurable.comp
        ((measurable_fderiv ℝ _).prodMk hξL.continuous.measurable)
    exact ((((hgm.norm.pow_const 2).aestronglyMeasurable.add (hQm.pow 2)).mul
      (measurable_divergence ξ).aestronglyMeasurable).sub
        (aestronglyMeasurable_const.mul h1.aestronglyMeasurable)).add h2.aestronglyMeasurable
  -- the bound on `f`
  set B : ℝ := (L ^ 2 + MQ ^ 2) * (Module.finrank ℝ (E d) * Kξ) + 2 * (L * (Kξ * L)) +
    2 * MQ * KQ * Mξ with hB
  have hfB : ∀ x ∈ Ω ∩ K, DifferentiableAt ℝ Q x → |f x| ≤ B := by
    intro x hx hQx
    have hxU : x ∈ U := hΩU hx.1
    have hgx : ‖∇ u x‖ ≤ L := hgL x hxU
    have hQx' : |Q x| ≤ MQ := hMQ x hx.2
    have hDξ : ‖fderiv ℝ ξ x‖ ≤ Kξ := norm_fderiv_le_of_lipschitz ℝ hξL
    have hDQ : ‖fderiv ℝ Q x‖ ≤ KQ := norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hxU) hQL
    have hL0 : (0 : ℝ) ≤ L := L.2
    have t1 : |(‖∇ u x‖ ^ 2 + Q x ^ 2) * divergence ξ x| ≤
        (L ^ 2 + MQ ^ 2) * (Module.finrank ℝ (E d) * Kξ) := by
      rw [abs_mul]
      refine mul_le_mul ?_ ((abs_divergence_le ξ x).trans ?_) (abs_nonneg _)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
      · rw [abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
        have : Q x ^ 2 ≤ MQ ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hQx' 2
        have : ‖∇ u x‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hgx 2
        linarith
      · exact mul_le_mul_of_nonneg_left hDξ (Nat.cast_nonneg _)
    have t2 : |2 * ⟪∇ u x, fderiv ℝ ξ x (∇ u x)⟫| ≤ 2 * (L * (Kξ * L)) := by
      rw [abs_mul, abs_two]
      refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans ?_) (by norm_num)
      refine mul_le_mul hgx (((fderiv ℝ ξ x).le_opNorm _).trans ?_) (norm_nonneg _) hL0
      exact mul_le_mul hDξ hgx (norm_nonneg _) (Kξ.2)
    have t3 : |fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x)| ≤ 2 * MQ * KQ * Mξ := by
      have hD2 : fderiv ℝ (fun y ↦ Q y ^ 2) x = (2 * Q x) • fderiv ℝ Q x := by
        rw [(hQx.hasFDerivAt.pow 2).fderiv]; simp
      rw [hD2, smul_apply, smul_eq_mul, abs_mul, abs_mul, abs_two]
      have h4 : |fderiv ℝ Q x (ξ x)| ≤ KQ * Mξ :=
        (((fderiv ℝ Q x).le_opNorm _).trans
          (mul_le_mul hDQ (hMξ x) (norm_nonneg _) KQ.2))
      calc 2 * |Q x| * |fderiv ℝ Q x (ξ x)| ≤ 2 * MQ * (KQ * Mξ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hQx' zero_le_two) h4 (abs_nonneg _)
              (mul_nonneg zero_le_two hMQ0)
        _ = 2 * MQ * KQ * Mξ := by ring
    calc |f x| ≤ |(‖∇ u x‖ ^ 2 + Q x ^ 2) * divergence ξ x| +
          |2 * ⟪∇ u x, fderiv ℝ ξ x (∇ u x)⟫| + |fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x)| := by
          simp only [hf_def]
          exact (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
      _ ≤ B := by rw [hB]; linarith
  have hQae : ∀ᵐ x, x ∈ U → DifferentiableAt ℝ Q x := by
    filter_upwards [hQL.ae_differentiableWithinAt_of_mem] with x hx hxU
    exact (hx hxU).differentiableAt (hU.mem_nhds hxU)
  have hfint : IntegrableOn f Ω := by
    have hΩK : MeasurableSet (Ω ∩ K) := hΩm.inter hK.measurableSet
    have h1 : IntegrableOn f (Ω ∩ K) := by
      refine IntegrableOn.of_bound ((measure_mono inter_subset_right).trans_lt
        hK.measure_lt_top) (hfm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
        B ?_
      rw [ae_restrict_iff' hΩK]
      filter_upwards [hQae] with x hx hxΩK
      exact hfB x hxΩK (hx (hΩU hxΩK.1))
    exact h1.of_forall_sdiff_eq_zero hΩm fun x hx ↦ hf0 x fun h ↦ hx.2 ⟨hx.1, h⟩
  -- the smooth cut-off `ψ = 1` on `spt ξ`
  obtain ⟨ψ, hψ, hψc, hψU, hψ01, hψ1⟩ := exists_smooth_cutoff hK hU hξU
  have hKψ : K ⊆ tsupport ψ := fun x hx ↦
    subset_tsupport _ (by rw [Function.mem_support, hψ1 x hx]; exact one_ne_zero)
  have hψC1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_cast)
  have hDψc : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by norm_cast)
  -- the compact sets `{ε/2 ≤ u} ∩ spt ψ ⊆ Ω`
  have hC : ∀ ε > 0, IsCompact (tsupport ψ ∩ u ⁻¹' Ici (ε / 2)) ∧
      tsupport ψ ∩ u ⁻¹' Ici (ε / 2) ⊆ Ω := fun ε hε ↦
    ⟨hψc.isCompact.of_isClosed_subset ((hucont.mono hψU).preimage_isClosed_of_isClosed
      (isClosed_tsupport ψ) isClosed_Ici) inter_subset_left,
      fun x hx ↦ ⟨hψU hx.1, lt_of_lt_of_le (by positivity) hx.2⟩⟩
  have hηc : ∀ ε, ContinuousOn (fun x ↦ cutη (u x / ε)) Ω := fun ε ↦
    contDiff_cutη.continuous.comp_continuousOn ((hucont.mono hΩU).div_const ε)
  have hη'c : ∀ ε, ContinuousOn (fun x ↦ deriv cutη (u x / ε) / ε) Ω := fun ε ↦
    (continuous_deriv_cutη.comp_continuousOn ((hucont.mono hΩU).div_const ε)).div_const ε
  have hη'0 : ∀ ε > 0, ∀ x, u x < ε / 2 → deriv cutη (u x / ε) = 0 := fun ε hε x hx ↦
    deriv_cutη_eq_zero (Or.inl (by rw [div_lt_iff₀ hε]; linarith))
  have hη0 : ∀ ε > 0, ∀ x, u x < ε / 2 → cutη (u x / ε) = 0 := fun ε hε x hx ↦
    cutη_eq_zero (by rw [div_le_iff₀ hε]; linarith)
  -- the boundary integrands
  set bd : ℝ → E d → ℝ := fun ε x ↦
    deriv cutη (u x / ε) / ε * (⟪∇ u x, ξ x⟫ * (Q x ^ 2 - ‖∇ u x‖ ^ 2)) with hbd
  set w : ℝ → E d → ℝ := fun ε x ↦ deriv cutη (u x / ε) / ε * (ψ x * ‖∇ u x‖ ^ 2) with hw
  have hbdint : ∀ ε > 0, IntegrableOn (bd ε) Ω := by
    intro ε hε
    refine integrableOn_of_continuousOn_of_eq_zero hΩm (hC ε hε).1 (hC ε hε).2
      ((hη'c ε).mul ((hgcont.inner hξL.continuous.continuousOn).mul
        (((hQcont.mono hΩU).pow 2).sub (hgcont.norm.pow 2)))) fun x _ hx ↦ ?_
    rcases not_and_or.1 hx with hx | hx
    · rw [hbd]; simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hKψ h)]
    · rw [hbd]; simp [hη'0 ε hε x (not_le.1 hx)]
  have hwint : ∀ ε > 0, IntegrableOn (w ε) Ω := by
    intro ε hε
    refine integrableOn_of_continuousOn_of_eq_zero hΩm (hC ε hε).1 (hC ε hε).2
      ((hη'c ε).mul (hψ.continuous.continuousOn.mul (hgcont.norm.pow 2))) fun x _ hx ↦ ?_
    rcases not_and_or.1 hx with hx | hx
    · rw [hw]; simp [image_eq_zero_of_notMem_tsupport hx]
    · rw [hw]; simp [hη'0 ε hε x (not_le.1 hx)]
  have hψint : ∀ ε > 0, IntegrableOn (fun x ↦ cutη (u x / ε) * fderiv ℝ ψ x (∇ u x)) Ω := by
    intro ε hε
    refine integrableOn_of_continuousOn_of_eq_zero hΩm (hC ε hε).1 (hC ε hε).2
      ((hηc ε).mul ((hDψc.continuousOn).clm_apply hgcont)) fun x _ hx ↦ ?_
    rcases not_and_or.1 hx with hx | hx
    · simp [fderiv_of_notMem_tsupport ℝ hx]
    · simp [hη0 ε hε x (not_le.1 hx)]
  have hηfint : ∀ ε, IntegrableOn (fun x ↦ cutη (u x / ε) * f x) Ω := fun ε ↦
    hfint.norm.mono' (((hηc ε).aestronglyMeasurable hΩm).mul hfm) (Eventually.of_forall fun x ↦ by
      rw [norm_mul, Real.norm_of_nonneg (cutη_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg (f x)) (cutη_le_one _))
  -- Identity 1
  have hid1 : ∀ ε > 0, ∫ x in Ω, cutη (u x / ε) * f x = -∫ x in Ω, bd ε x := by
    intro ε hε
    set V : E d → E d := fun y ↦ (‖∇ u y‖ ^ 2 + Q y ^ 2) • ξ y - (2 * ⟪∇ u y, ξ y⟫) • ∇ u y
      with hV
    have hsupp : Function.support V ⊆ tsupport ξ := fun y hy ↦ subset_tsupport _ fun h ↦
      hy (by simp [hV, show ξ y = 0 from h])
    have hVc : HasCompactSupport V := hξc.mono' hsupp
    have hVU : tsupport V ⊆ U := (closure_minimal hsupp (isClosed_tsupport ξ)).trans hξU
    have hG : ContDiff ℝ 1 (fun p : E d × ℝ × E d ↦
        (‖p.1‖ ^ 2 + p.2.1 ^ 2) • p.2.2 - (2 * ⟪p.1, p.2.2⟫) • p.1) := by
      have h1 : ContDiff ℝ 1 (fun p : E d × ℝ × E d ↦ p.1) := contDiff_fst
      have h2 : ContDiff ℝ 1 (fun p : E d × ℝ × E d ↦ p.2.1) := contDiff_fst.comp contDiff_snd
      have h3 : ContDiff ℝ 1 (fun p : E d × ℝ × E d ↦ p.2.2) := contDiff_snd.comp contDiff_snd
      exact (((h1.norm_sq ℝ).add (h2.pow 2)).smul h3).sub
        ((contDiff_const.mul (h1.inner ℝ h3)).smul h1)
    have hVlip : ∀ x ∈ Ω, ∃ K', ∃ t ∈ 𝓝 x, LipschitzOnWith K' V t := by
      intro x hx
      have hT := lipAt_prodMk (hgC1 x hx).exists_lipschitzOnWith
        (lipAt_prodMk (f := Q) (g := ξ) ⟨KQ, U, hU.mem_nhds (hΩU hx), hQL⟩
          ⟨Kξ, univ, univ_mem, hξL.lipschitzOnWith⟩)
      have h := lipAt_comp_contDiff hG hT
      exact h
    have hVd : ∀ᵐ x, x ∈ Ω → DifferentiableAt ℝ V x := by
      filter_upwards [hQae, hξL.ae_differentiableAt] with x hQx hξx hxΩ
      have hg := (hgC1 x hxΩ).differentiableAt one_ne_zero
      exact (((hg.norm_sq ℝ).add ((hQx (hΩU hxΩ)).pow 2)).smul hξx).sub
        (((hg.inner ℝ hξx).const_mul 2).smul hg)
    have I := integral_cutoff_divergence_eq_zero hU hucont hu.nonneg hu1 hVc hVU hVlip hVd hε
    have hae : ∀ᵐ x, x ∈ Ω → cutη (u x / ε) * divergence V x +
        deriv cutη (u x / ε) / ε * ⟪∇ u x, V x⟫ = cutη (u x / ε) * f x + bd ε x := by
      filter_upwards [hQae, hξL.ae_differentiableAt] with x hQx hξx hxΩ
      rw [divergence_stressField (hu2 x hxΩ) (hlap x hxΩ) (hQx (hΩU hxΩ)) hξx]
      simp only [hV, hbd, hf_def, inner_sub_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      ring
    rw [setIntegral_congr_ae hΩm hae, integral_add (hηfint ε) (hbdint ε hε)] at I
    linarith
  -- Identity 2
  have hid2 : ∀ ε > 0, ∫ x in Ω, w ε x = -∫ x in Ω, cutη (u x / ε) * fderiv ℝ ψ x (∇ u x) := by
    intro ε hε
    set V : E d → E d := fun y ↦ ψ y • ∇ u y with hV
    have hVc : HasCompactSupport V := hψc.smul_right
    have hVU : tsupport V ⊆ U := (tsupport_smul_subset_left _ _).trans hψU
    have hVC : ∀ x ∈ Ω, ContDiffAt ℝ 1 V x := fun x hx ↦ hψC1.contDiffAt.smul (hgC1 x hx)
    have I := integral_cutoff_divergence_eq_zero hU hucont hu.nonneg hu1 hVc hVU
      (fun x hx ↦ (hVC x hx).exists_lipschitzOnWith)
      (Eventually.of_forall fun x hx ↦ (hVC x hx).differentiableAt one_ne_zero) hε
    have hae : ∀ x ∈ Ω, cutη (u x / ε) * divergence V x +
        deriv cutη (u x / ε) / ε * ⟪∇ u x, V x⟫ =
          cutη (u x / ε) * fderiv ℝ ψ x (∇ u x) + w ε x := by
      intro x hxΩ
      have hDu : DifferentiableAt ℝ (fderiv ℝ u) x :=
        ((hu2 x hxΩ).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
      rw [hV, divergence_smul (hψ.differentiable (by norm_cast) x)
        (differentiableAt_gradient hDu), divergence_gradient hDu, hlap x hxΩ]
      simp only [hw, real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring
    rw [setIntegral_congr_fun hΩm hae, integral_add (hψint ε hε) (hwint ε hε)] at I
    linarith
  -- the bound for Identity 2, uniform in `ε`
  set C₂ : ℝ := ∫ x in Ω, ‖fderiv ℝ ψ x‖ * L with hC₂
  have hC₂int : Integrable (fun x ↦ ‖fderiv ℝ ψ x‖ * (L : ℝ)) :=
    (hDψc.norm.mul continuous_const).integrable_of_hasCompactSupport
      ((hψc.fderiv (𝕜 := ℝ)).norm.mul_right)
  have hw_le : ∀ ε > 0, ∫ x in Ω, w ε x ≤ C₂ := by
    intro ε hε
    rw [hid2 ε hε]
    refine (neg_le_abs _).trans ?_
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hC₂int.integrableOn ?_
    rw [ae_restrict_iff' hΩm]
    refine Eventually.of_forall fun x hx ↦ ?_
    rw [norm_mul, Real.norm_of_nonneg (cutη_nonneg _)]
    refine (mul_le_of_le_one_left (norm_nonneg _) (cutη_le_one _)).trans ?_
    exact ((fderiv ℝ ψ x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hgL x (hΩU hx)) (norm_nonneg _))
  have hC₂0 : 0 ≤ C₂ := setIntegral_nonneg hΩm fun x _ ↦ mul_nonneg (norm_nonneg _) L.2
  -- the boundary term
  set C₁ : ℝ := 2 * Mξ * (2 * MQ + c) / c with hC₁
  have hMQc : 0 ≤ 2 * MQ + c := add_nonneg (mul_nonneg zero_le_two hMQ0) hc.le
  have hC₁0 : 0 ≤ C₁ := div_nonneg (mul_nonneg (mul_nonneg zero_le_two hMξ0) hMQc) hc.le
  have hbdry : ∀ δ, 0 < δ → δ ≤ c / 2 → ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ →
      |∫ x in Ω, cutη (u x / ε) * f x| ≤ C₁ * δ * C₂ := by
    intro δ hδ hδc
    obtain ⟨ε₀, hε₀, hε₀δ⟩ :=
      exists_eps_abs_norm_gradient_sub_lt hU hK hξU hucont hQcont hgrad hδ
    refine ⟨ε₀, hε₀, fun ε hε hεε₀ ↦ ?_⟩
    have hw0 : ∀ x, 0 ≤ w ε x := fun x ↦
      mul_nonneg (div_nonneg (deriv_cutη_nonneg _) hε.le) (mul_nonneg (hψ01 x).1 (sq_nonneg _))
    have hpt : ∀ x ∈ Ω, ‖bd ε x‖ ≤ C₁ * δ * w ε x := by
      intro x hxΩ
      rw [Real.norm_eq_abs]
      by_cases hxK : x ∈ K
      · by_cases hD : deriv cutη (u x / ε) = 0
        · simp only [hbd, hD, zero_div, zero_mul, abs_zero]
          exact mul_nonneg (mul_nonneg hC₁0 hδ.le) (hw0 x)
        · have hux : u x < ε₀ := by
            have : u x / ε ≤ 1 := not_lt.1 fun h ↦ hD (deriv_cutη_eq_zero (Or.inr h))
            rw [div_le_one hε] at this
            linarith
          have hclose := hε₀δ x ⟨hxΩ, hxK⟩ hux
          set a := ‖∇ u x‖ with ha
          have hQx : c ≤ Q x := hcQ x (hΩU hxΩ)
          have hQM : |Q x| ≤ MQ := hMQ x hxK
          have ha1 : c / 2 ≤ a := by
            have := (abs_lt.1 hclose).1; linarith
          have ha0 : 0 < a := by linarith
          have hin : |⟪∇ u x, ξ x⟫| ≤ a * Mξ :=
            (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hMξ x) ha0.le)
          have hsq : |Q x ^ 2 - a ^ 2| ≤ δ * (2 * MQ + c) := by
            have h1 : Q x ^ 2 - a ^ 2 = (Q x - a) * (Q x + a) := by ring
            rw [h1, abs_mul]
            have h2 : |Q x - a| ≤ δ := by rw [abs_sub_comm]; exact hclose.le
            have h3 : |Q x + a| ≤ 2 * MQ + c := by
              refine (abs_add_le _ _).trans ?_
              rw [abs_of_pos ha0]
              have := (abs_lt.1 hclose).2
              have := le_abs_self (Q x)
              linarith
            exact mul_le_mul h2 h3 (abs_nonneg _) hδ.le
          have hac : a ≤ 2 / c * a ^ 2 := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hc]
            linarith [mul_le_mul_of_nonneg_left ha1 ha0.le]
          have hkey : |⟪∇ u x, ξ x⟫ * (Q x ^ 2 - a ^ 2)| ≤ C₁ * δ * a ^ 2 := by
            rw [abs_mul]
            calc |⟪∇ u x, ξ x⟫| * |Q x ^ 2 - a ^ 2| ≤ a * Mξ * (δ * (2 * MQ + c)) :=
                  mul_le_mul hin hsq (abs_nonneg _) (mul_nonneg ha0.le hMξ0)
              _ = a * (Mξ * δ * (2 * MQ + c)) := by ring
              _ ≤ 2 / c * a ^ 2 * (Mξ * δ * (2 * MQ + c)) :=
                  mul_le_mul_of_nonneg_right hac (mul_nonneg (mul_nonneg hMξ0 hδ.le) hMQc)
              _ = C₁ * δ * a ^ 2 := by rw [hC₁]; field_simp
          have hDε : 0 ≤ deriv cutη (u x / ε) / ε := div_nonneg (deriv_cutη_nonneg _) hε.le
          simp only [hbd, hw]
          rw [abs_mul, abs_of_nonneg hDε, hψ1 x hxK, one_mul]
          calc deriv cutη (u x / ε) / ε * |⟪∇ u x, ξ x⟫ * (Q x ^ 2 - ‖∇ u x‖ ^ 2)| ≤
                deriv cutη (u x / ε) / ε * (C₁ * δ * a ^ 2) :=
                mul_le_mul_of_nonneg_left hkey hDε
            _ = C₁ * δ * (deriv cutη (u x / ε) / ε * ‖∇ u x‖ ^ 2) := by ring
      · simp only [hbd, image_eq_zero_of_notMem_tsupport hxK, inner_zero_right, zero_mul,
          mul_zero, abs_zero]
        exact mul_nonneg (mul_nonneg hC₁0 hδ.le) (hw0 x)
    rw [hid1 ε hε, abs_neg, ← Real.norm_eq_abs]
    calc ‖∫ x in Ω, bd ε x‖ ≤ ∫ x in Ω, C₁ * δ * w ε x := by
          refine norm_integral_le_of_norm_le ((hwint ε hε).const_mul _) ?_
          rw [ae_restrict_iff' hΩm]
          exact Eventually.of_forall hpt
      _ = C₁ * δ * ∫ x in Ω, w ε x := integral_const_mul _ _
      _ ≤ C₁ * δ * C₂ := mul_le_mul_of_nonneg_left (hw_le ε hε) (mul_nonneg hC₁0 hδ.le)
  -- dominated convergence for the main term
  have hdct : Tendsto (fun n : ℕ ↦ ∫ x in Ω, cutη (u x / (1 / ((n : ℝ) + 1))) * f x) atTop
      (𝓝 (∫ x in Ω, f x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖f x‖)
      (fun n ↦ ((hηc _).aestronglyMeasurable hΩm).mul hfm) hfint.norm
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) ?_
    · rw [norm_mul, Real.norm_of_nonneg (cutη_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg (f x)) (cutη_le_one _)
    · rw [ae_restrict_iff' hΩm]
      refine Eventually.of_forall fun x hx ↦ tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / u x)
      filter_upwards [eventually_ge_atTop N] with n hn
      have hux : 0 < u x := hx.2
      rw [cutη_eq_one, one_mul]
      rw [div_div_eq_mul_div, div_one]
      have : 1 / u x ≤ (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      rw [div_le_iff₀ hux] at this
      linarith
  -- conclusion
  have hkey : ∀ δ, 0 < δ → δ ≤ c / 2 → |∫ x in Ω, f x| ≤ C₁ * δ * C₂ := by
    intro δ hδ hδc
    obtain ⟨ε₀, hε₀, hb⟩ := hbdry δ hδ hδc
    have hev : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ε₀ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat).eventually (gt_mem_nhds hε₀)
    refine le_of_tendsto hdct.abs ?_
    filter_upwards [hev] with n hn
    exact hb _ (by positivity) hn
  have hlim : Tendsto (fun δ ↦ C₁ * δ * C₂) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun δ : ℝ ↦ C₁ * δ * C₂) (𝓝 0) (𝓝 (C₁ * 0 * C₂)) :=
      ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
    rw [mul_zero, zero_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : |∫ x in Ω, f x| ≤ 0 := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < c / 2 by positivity)] with δ hδ
    exact hkey δ hδ.1 hδ.2.le
  rw [hred]
  exact abs_nonpos_iff.1 hle

end EllipticBernoulli
