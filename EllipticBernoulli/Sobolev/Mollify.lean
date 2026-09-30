/-
Copyright (c) 2026 William M. Feldman, Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman, Alejandro Soto Franco
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Mollification

Imports only `Basic/*` and Mathlib.

* `integral_norm_normed_convolution_le`, `tendsto_integral_norm_normed_convolution_sub`:
  `L¹` contraction and `L¹` convergence of mollifications, bump on the left.
* `eLpNorm_convolution_le`, `tendsto_eLpNorm_convolution_sub`: Young's inequality for a
  probability kernel and `Lᵖ` convergence of mollifications `h ⋆ ρ_i → h`, bump on the right.
  Adapted from `EllipticPdes.Embedding.Convolution` (EllipticPDE, A. Soto Franco, Apache-2.0).
* `fderiv_convolution_indicator_eq`: the `v`-derivative of the mollification of a function with
  a weak gradient `G` is the mollification of `⟪G, v⟫` (adapted from EllipticPDE's
  `partialD_convolution_eq_of_hasWeakGradOn`).

## Provenance

* Upstream: EllipticPDE, https://github.com/alejandro-soto-franco/EllipticPDE
* Paths: `lean/EllipticPdes/Embedding/Convolution.lean`, `lean/EllipticPdes/Embedding/Morrey.lean`
* Commit: eaf821d31b200bb6ea235f19eecc50cf0f38c294 (2026-09-22)
* License: Apache-2.0. Upstream `NOTICE`: none.
* Upstream notice: `Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.`;
  upstream authors: Alejandro Soto Franco.
* Extent: `eLpNorm_convolution_le`, `tendsto_eLpNorm_convolution_sub` (from `Convolution.lean`) and
  `fderiv_convolution_indicator_eq` (from
  `partialD_convolution_eq_of_hasWeakGradOn`, `Morrey.lean`).
* Changes: restated for `HasWeakGradient` (weak gradients tested against arbitrary directions `v`)
  and `E d`; ported to Lean/Mathlib v4.30.0; proofs adapted.
-/

open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal NNReal Pointwise

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

section Mollifier

/-! The `L¹` lemmas hold on any finite-dimensional real normed space with an additive Haar
`volume`; they apply on `E d` and on `ℝ`. -/

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasureSpace G] [BorelSpace G] [(volume : Measure G).IsAddHaarMeasure]

/-- `L¹` contraction: `∫ |ρ ⋆ k| ≤ ∫ |k|` for a normalized bump `ρ`. -/
theorem integral_norm_normed_convolution_le (ρ : ContDiffBump (0 : G)) {k : G → ℝ}
    (hk : Integrable k) :
    ∫ x, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] k) x‖ ≤ ∫ x, ‖k x‖ := by
  have hρ := ρ.integrable_normed (μ := volume)
  have h1 : Integrable (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] k) := hρ.integrable_convolution _ hk
  have h2 : Integrable (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun x ↦ ‖k x‖) :=
    hρ.integrable_convolution _ hk.norm
  calc ∫ x, ‖(ρ.normed volume ⋆[lsmul ℝ ℝ, volume] k) x‖
      ≤ ∫ x, (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] fun x ↦ ‖k x‖) x := by
        refine integral_mono h1.norm h2 fun x ↦ ?_
        simp only [convolution_def, lsmul_apply, smul_eq_mul]
        refine (norm_integral_le_integral_norm _).trans_eq ?_
        congr 1; funext t
        rw [norm_mul, Real.norm_of_nonneg (ρ.nonneg_normed t)]
    _ = ∫ x, ‖k x‖ := by
        rw [integral_convolution _ hρ hk.norm, ρ.integral_normed]
        simp

/-- Mollifications of a continuous compactly supported function converge in `L¹`. -/
theorem tendsto_integral_norm_normed_convolution_sub_of_continuous {ρ : ℕ → ContDiffBump (0 : G)}
    (hρ : Tendsto (fun n ↦ (ρ n).rOut) atTop (𝓝 0)) {h : G → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) :
    Tendsto (fun n ↦ ∫ x, ‖((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] h) x - h x‖) atTop
      (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  set S := cthickening 1 (tsupport h)
  have hS : IsCompact S := hcs.isCompact.cthickening
  have hbound : ∀ n, ∀ x, ‖((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] h) x‖ ≤ C := by
    intro n x
    simp only [convolution_def, lsmul_apply, smul_eq_mul]
    refine (norm_integral_le_of_norm_le ((ρ n).integrable_normed.mul_const C)
      (Eventually.of_forall fun t ↦ ?_)).trans_eq ?_
    · rw [norm_mul, Real.norm_of_nonneg ((ρ n).nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left (hC _) ((ρ n).nonneg_normed t)
    · rw [integral_mul_const, (ρ n).integral_normed, one_mul]
  have hzero : ∀ n, (ρ n).rOut ≤ 1 → ∀ x ∉ S,
      ((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] h) x = 0 := by
    intro n hn x hx
    simp only [convolution_def, lsmul_apply, smul_eq_mul]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
    by_cases ht : (ρ n).normed volume t = 0
    · simp [ht]
    · have ht' : t ∈ ball (0 : G) (ρ n).rOut := by
        rw [← (ρ n).support_normed_eq (μ := volume)]; exact ht
      have hxt : h (x - t) = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem ↦ hx ?_
        refine mem_cthickening_of_dist_le x (x - t) 1 _ hmem ?_
        rw [mem_ball, dist_zero_right] at ht'
        simpa [dist_eq_norm] using (ht'.le.trans hn)
      simp [hxt]
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun n x ↦ ‖((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] h) x - h x‖) (f := fun _ ↦ 0)
    (S.indicator fun _ ↦ 2 * C) ?_ ?_ ?_ ?_
  · simpa using this
  · refine Eventually.of_forall fun n ↦ ?_
    exact ((((ρ n).hasCompactSupport_normed).continuous_convolution_left _
      (ρ n).continuous_normed (hc.locallyIntegrable)).sub hc).norm.aestronglyMeasurable
  · filter_upwards [(tendsto_order.1 hρ).2 1 one_pos] with n hn
    refine Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, norm_norm]
      refine (norm_sub_le _ _).trans ?_
      linarith [hbound n x, hC x]
    · rw [indicator_of_notMem hx, hzero n hn.le x hx, image_eq_zero_of_notMem_tsupport
        fun h' ↦ hx (self_subset_cthickening _ h')]
      simp
  · exact (integrableOn_const hS.measure_lt_top.ne).integrable_indicator hS.measurableSet
  · refine Eventually.of_forall fun x ↦ ?_
    have := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) hρ hc x
    simpa using (this.sub_const (h x)).norm

/-- **Mollifications converge in `L¹`.** If `k` is integrable and `ρ n` are bump functions with
`rOut → 0`, then `∫ |ρ n ⋆ k - k| → 0`. -/
theorem tendsto_integral_norm_normed_convolution_sub {ρ : ℕ → ContDiffBump (0 : G)}
    (hρ : Tendsto (fun n ↦ (ρ n).rOut) atTop (𝓝 0)) {k : G → ℝ} (hk : Integrable k) :
    Tendsto (fun n ↦ ∫ x, ‖((ρ n).normed volume ⋆[lsmul ℝ ℝ, volume] k) x - k x‖) atTop
      (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨h, hcs, hkh, hc, hhi⟩ :=
    hk.exists_hasCompactSupport_integral_sub_le (by positivity : 0 < ε / 3)
  have hlim := tendsto_integral_norm_normed_convolution_sub_of_continuous hρ hc hcs
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 3) (by positivity)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hN' := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)] at hN' ⊢
  set c := (ρ n).normed volume
  have hcc : HasCompactSupport c := (ρ n).hasCompactSupport_normed
  have hcont : Continuous c := (ρ n).continuous_normed
  have hci : Integrable c := (ρ n).integrable_normed
  have hkh' : Integrable (k - h) := hk.sub hhi
  have e1 : ConvolutionExists c (k - h) (lsmul ℝ ℝ) volume :=
    hcc.convolutionExists_left _ hcont hkh'.locallyIntegrable
  have e2 : ConvolutionExists c h (lsmul ℝ ℝ) volume :=
    hcc.convolutionExists_left _ hcont hhi.locallyIntegrable
  have hsplit : ∀ x, (c ⋆[lsmul ℝ ℝ, volume] k) x - k x =
      (c ⋆[lsmul ℝ ℝ, volume] (k - h)) x + ((c ⋆[lsmul ℝ ℝ, volume] h) x - h x) + (h x - k x) := by
    intro x
    have : k = (k - h) + h := by abel
    conv_lhs => rw [this]
    rw [(e1 x).distrib_add (e2 x)]
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  have i1 : Integrable (c ⋆[lsmul ℝ ℝ, volume] (k - h)) := hci.integrable_convolution _ hkh'
  have i2 : Integrable fun x ↦ (c ⋆[lsmul ℝ ℝ, volume] h) x - h x :=
    (hci.integrable_convolution _ hhi).sub hhi
  have i3 : Integrable fun x ↦ h x - k x := hhi.sub hk
  calc ∫ x, ‖(c ⋆[lsmul ℝ ℝ, volume] k) x - k x‖
      ≤ ∫ x, (‖(c ⋆[lsmul ℝ ℝ, volume] (k - h)) x‖ + ‖(c ⋆[lsmul ℝ ℝ, volume] h) x - h x‖ +
          ‖h x - k x‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
          ((i1.norm.add i2.norm).add i3.norm) (Eventually.of_forall fun x ↦ ?_)
        simp only [hsplit x]
        exact norm_add₃_le
    _ = (∫ x, ‖(c ⋆[lsmul ℝ ℝ, volume] (k - h)) x‖) +
          (∫ x, ‖(c ⋆[lsmul ℝ ℝ, volume] h) x - h x‖) + ∫ x, ‖h x - k x‖ := by
        rw [integral_add (f := fun x ↦ ‖(c ⋆[lsmul ℝ ℝ, volume] (k - h)) x‖ +
            ‖(c ⋆[lsmul ℝ ℝ, volume] h) x - h x‖) (i1.norm.add i2.norm) i3.norm,
          integral_add i1.norm i2.norm]
    _ < ε := by
        have a1 : ∫ x, ‖(c ⋆[lsmul ℝ ℝ, volume] (k - h)) x‖ ≤ ∫ x, ‖(k - h) x‖ :=
          integral_norm_normed_convolution_le (ρ n) hkh'
        have a3 : ∫ x, ‖h x - k x‖ = ∫ x, ‖k x - h x‖ := by
          congr 1; funext x; exact norm_sub_rev _ _
        have a1' : ∫ x, ‖(k - h) x‖ = ∫ x, ‖k x - h x‖ := rfl
        linarith


/-! ### `Lᵖ` convergence of mollifications

Adapted from `EllipticPdes.Embedding.Convolution` (EllipticPDE, A. Soto Franco, Apache-2.0,
`github.com/alejandro-soto-franco/EllipticPDE`). Convention: the bump is on the **right**,
`h ⋆ ρ`. -/

/-- **Young's `Lᵖ` inequality for a probability kernel.** -/
theorem eLpNorm_convolution_le {p : ℝ} (hp : 1 ≤ p) {ρ : E d → ℝ}
    (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume) (hρ1 : ∫ y, ρ y ∂volume = 1)
    {h : E d → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume) :
    eLpNorm (h ⋆[lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p) volume
      ≤ eLpNorm h (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hPreal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hhen : AEMeasurable (fun z ↦ ‖h z‖ₑ) volume := hh.aestronglyMeasurable.enorm
  have hρen : AEMeasurable (fun z ↦ ‖ρ z‖ₑ) volume := hρm.enorm
  have hρint : Integrable ρ volume := by
    by_contra hcon
    rw [integral_undef hcon] at hρ1
    exact one_ne_zero hρ1.symm
  have hmass : ∫⁻ z, ‖ρ z‖ₑ ∂volume = 1 := by
    have h1 : ∫⁻ z, ‖ρ z‖ₑ ∂volume = ∫⁻ z, ENNReal.ofReal (ρ z) ∂volume :=
      lintegral_congr fun z ↦ Real.enorm_of_nonneg (hρ0 z)
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ fun z ↦ hρ0 z), hρ1,
      ENNReal.ofReal_one]
  have hswapmeas : AEMeasurable
      (fun q : E d × E d ↦ ‖h q.2‖ₑ ^ p * ‖ρ (q.1 - q.2)‖ₑ) (volume.prod volume) :=
    ((hhen.pow_const p).comp_snd).mul
      (hρen.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  have key : ∀ x, ‖(h ⋆[lsmul ℝ ℝ, volume] ρ) x‖ₑ ^ p
      ≤ ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume := by
    intro x
    have hρxen : AEMeasurable (fun t ↦ ‖ρ (x - t)‖ₑ) volume :=
      hρen.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
    have hwmass : ∫⁻ t, ‖ρ (x - t)‖ₑ ∂volume = 1 :=
      (lintegral_sub_left_eq_self (fun z ↦ ‖ρ z‖ₑ) x).trans hmass
    have hbound : ‖(h ⋆[lsmul ℝ ℝ, volume] ρ) x‖ₑ
        ≤ ∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume := by
      rw [convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun t ↦ ?_
      rw [lsmul_apply, smul_eq_mul, enorm_mul]
    refine le_trans (ENNReal.rpow_le_rpow hbound hp0.le) ?_
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · rw [← hp1, ENNReal.rpow_one]
      exact le_of_eq (lintegral_congr fun t ↦ by rw [ENNReal.rpow_one])
    · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
      set q := Real.conjExponent p with hq_def
      have hq_pos : 0 < q := hpq.symm.pos
      have hsum : 1 / p + 1 / q = 1 := by simpa using hpq.one_div_add_one_div
      have e1 : ∀ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ^ (1 / p) * ‖ρ (x - t)‖ₑ ^ (1 / q)
          = ‖h t‖ₑ * ‖ρ (x - t)‖ₑ := by
        intro t
        rw [mul_assoc,
          ← ENNReal.rpow_add_of_nonneg _ _ hpq.one_div_nonneg hpq.symm.one_div_nonneg, hsum,
          ENNReal.rpow_one]
      have e2 : ∀ t, (‖h t‖ₑ * ‖ρ (x - t)‖ₑ ^ (1 / p)) ^ p
          = ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ := by
        intro t
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div,
          inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
      have e3 : ∀ t, (‖ρ (x - t)‖ₑ ^ (1 / q)) ^ q = ‖ρ (x - t)‖ₑ := by
        intro t
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_pos.ne', ENNReal.rpow_one]
      have hol : ∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume
          ≤ (∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume) ^ (1 / p) := by
        have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
          (hhen.mul (hρxen.pow_const (1 / p))) (hρxen.pow_const (1 / q))
        simp only [Pi.mul_apply] at hH
        rwa [lintegral_congr e1, lintegral_congr e2, lintegral_congr e3, hwmass,
          ENNReal.one_rpow, mul_one] at hH
      calc (∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume) ^ p
          ≤ ((∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume) ^ (1 / p)) ^ p :=
            ENNReal.rpow_le_rpow hol hp0.le
        _ = ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume := by
            rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop
      (hh.aestronglyMeasurable.convolution (L := lsmul ℝ ℝ) hρm),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hh.aestronglyMeasurable, hPreal]
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr hp0.le)
  calc ∫⁻ x, ‖(h ⋆[lsmul ℝ ℝ, volume] ρ) x‖ₑ ^ p ∂volume
      ≤ ∫⁻ x, ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume ∂volume := lintegral_mono key
    _ = ∫⁻ t, ∫⁻ x, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume ∂volume :=
        lintegral_lintegral_swap hswapmeas
    _ = ∫⁻ t, ‖h t‖ₑ ^ p * ∫⁻ x, ‖ρ (x - t)‖ₑ ∂volume ∂volume := by
        refine lintegral_congr fun t ↦ ?_
        have hmt : AEMeasurable (fun x ↦ ‖ρ (x - t)‖ₑ) volume :=
          hρen.comp_quasiMeasurePreserving
            (measurePreserving_sub_right volume t).quasiMeasurePreserving
        exact lintegral_const_mul'' (‖h t‖ₑ ^ p) hmt
    _ = ∫⁻ t, ‖h t‖ₑ ^ p * 1 ∂volume := by
        refine lintegral_congr fun t ↦ ?_
        rw [lintegral_sub_right_eq_self (fun z ↦ ‖ρ z‖ₑ) t, hmass]
    _ = ∫⁻ x, ‖h x‖ₑ ^ p ∂volume := by simp

/-- Mollifications of a continuous compactly supported function converge in `Lᵖ`. -/
theorem tendsto_eLpNorm_bump_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {w : E d → ℝ} (hwc : Continuous w) (hwcs : HasCompactSupport w)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E d)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - w)
      (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    refine ContinuousLinearMap.ext fun a ↦ ContinuousLinearMap.ext fun b ↦ ?_
    simp only [flip_apply, lsmul_apply, smul_eq_mul]
    exact mul_comm b a
  have hunif : UniformContinuous w := hwcs.uniformContinuous_of_continuous hwc
  set S1 := closedBall (0 : E d) 1 + tsupport w with hS1def
  have hS1cpt : IsCompact S1 := (isCompact_closedBall _ _).add hwcs
  have hS1fin : volume S1 ≠ ⊤ := hS1cpt.measure_lt_top.ne
  have hAtop : volume S1 ^ p⁻¹ ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hS1fin
  have htsuppS1 : tsupport w ⊆ S1 := by
    intro y hy
    rw [hS1def]
    have h0 : (0 : E d) ∈ closedBall (0 : E d) 1 := mem_closedBall_self zero_le_one
    simpa using Set.add_mem_add h0 hy
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact Eventually.of_forall fun _ ↦ le_top
  have hA1top : volume S1 ^ p⁻¹ + 1 ≠ ⊤ := by simp [hAtop]
  have hA1pos : volume S1 ^ p⁻¹ + 1 ≠ 0 := by positivity
  set ε := (η / (volume S1 ^ p⁻¹ + 1)).toReal with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact ENNReal.toReal_pos (ENNReal.div_pos hη.ne' hA1top).ne'
      (ENNReal.div_ne_top hηtop hA1pos)
  have hofε : ENNReal.ofReal ε = η / (volume S1 ^ p⁻¹ + 1) := by
    rw [hεdef, ENNReal.ofReal_toReal (ENNReal.div_ne_top hηtop hA1pos)]
  have hAε : volume S1 ^ p⁻¹ * ENNReal.ofReal ε ≤ η := by
    rw [hofε]
    calc volume S1 ^ p⁻¹ * (η / (volume S1 ^ p⁻¹ + 1))
        ≤ (volume S1 ^ p⁻¹ + 1) * (η / (volume S1 ^ p⁻¹ + 1)) := by gcongr; exact le_self_add
      _ ≤ η := ENNReal.mul_div_le
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hunif ε hε0
  filter_upwards [Metric.tendsto_nhds.mp hφ δ hδ0, Metric.tendsto_nhds.mp hφ 1 one_pos]
    with i hiδ hi1
  have hrδ : (φ i).rOut < δ := by
    rwa [Real.dist_0_eq_abs, abs_of_pos (φ i).rOut_pos] at hiδ
  have hr1 : (φ i).rOut < 1 := by
    rwa [Real.dist_0_eq_abs, abs_of_pos (φ i).rOut_pos] at hi1
  have hcomm : w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)
      = ((φ i).normed volume) ⋆[lsmul ℝ ℝ, volume] w := by
    rw [← convolution_flip, hflip]
  have hpt : ∀ x₀, dist ((((φ i).normed volume) ⋆[lsmul ℝ ℝ, volume] w) x₀) (w x₀) ≤ ε := by
    intro x₀
    refine (φ i).dist_normed_convolution_le hwc.aestronglyMeasurable ?_
    intro x hx
    rw [mem_ball] at hx
    exact (hδ (lt_trans hx hrδ)).le
  have hsuppconv : Function.support (((φ i).normed volume) ⋆[lsmul ℝ ℝ, volume] w) ⊆ S1 := by
    refine (support_convolution_subset _).trans ?_
    rw [hS1def]
    refine Set.add_subset_add ?_ (subset_tsupport w)
    rw [(φ i).support_normed_eq]
    exact ball_subset_closedBall.trans (closedBall_subset_closedBall hr1.le)
  have hsupp : Function.support ((((φ i).normed volume) ⋆[lsmul ℝ ℝ, volume] w) - w) ⊆ S1 := by
    intro x hx
    by_contra hxS1
    refine Function.mem_support.mp hx ?_
    have hwx : w x = 0 := image_eq_zero_of_notMem_tsupport fun hxt ↦ hxS1 (htsuppS1 hxt)
    have hcx : (((φ i).normed volume) ⋆[lsmul ℝ ℝ, volume] w) x = 0 :=
      Function.notMem_support.mp fun hxs ↦ hxS1 (hsuppconv hxs)
    rw [Pi.sub_apply, hwx, hcx, sub_zero]
  rw [hcomm]
  have hdm : AEStronglyMeasurable ((((φ i).normed volume) ⋆[lsmul ℝ ℝ, volume] w) - w) volume :=
    ((φ i).continuous_normed.aestronglyMeasurable.convolution (L := lsmul ℝ ℝ)
      hwc.aestronglyMeasurable).sub hwc.aestronglyMeasurable
  calc eLpNorm ((((φ i).normed volume) ⋆[lsmul ℝ ℝ, volume] w) - w) (ENNReal.ofReal p) volume
      = eLpNorm ((((φ i).normed volume) ⋆[lsmul ℝ ℝ, volume] w) - w)
          (ENNReal.ofReal p) (volume.restrict S1) :=
        (eLpNorm_restrict_eq_of_support_subset hdm hsupp).symm
    _ ≤ (volume.restrict S1) Set.univ ^ ((ENNReal.ofReal p).toReal⁻¹) * ENNReal.ofReal ε :=
        eLpNorm_le_of_ae_bound hdm.restrict (Eventually.of_forall fun x ↦ by
          rw [Pi.sub_apply, ← dist_eq_norm]; exact hpt x)
    _ = volume S1 ^ p⁻¹ * ENNReal.ofReal ε := by
        rw [Measure.restrict_apply_univ, ENNReal.toReal_ofReal hp0.le]
    _ ≤ η := hAε

/-- **`Lᵖ` convergence of mollifications.** For `1 ≤ p`, `h ∈ Lᵖ` and bumps with `rOut → 0`,
`h ⋆ ρ_i → h` in `Lᵖ`. -/
theorem tendsto_eLpNorm_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {h : E d → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : E d)}
    (hφ : Tendsto (fun i ↦ (φ i).rOut) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (h ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - h)
      (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hqtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact Eventually.of_forall fun _ ↦ le_top
  set δ : ℝ := η.toReal / 3 with hδdef
  have hηpos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  have hδ0 : 0 < δ := by positivity
  obtain ⟨w, hwcs, hwsmooth, hwle⟩ := hh.exist_eLpNorm_sub_le hqtop hq1 hδ0
  have hwc : Continuous w := hwsmooth.continuous
  have hwml : MemLp w (ENNReal.ofReal p) volume := hwc.memLp_of_hasCompactSupport hwcs
  have hlocw : LocallyIntegrable w volume := hwml.locallyIntegrable hq1
  have hlochw : LocallyIntegrable (h - w) volume := (hh.sub hwml).locallyIntegrable hq1
  have ha3 : eLpNorm (w - h) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal δ := by
    rw [eLpNorm_sub_comm]; exact hwle
  have hmid := tendsto_eLpNorm_bump_convolution_sub hp hwc hwcs hφ
  have hmid_ev : ∀ᶠ i in l,
      eLpNorm (w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - w)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal δ :=
    ENNReal.tendsto_nhds_zero.mp hmid (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ0)
  filter_upwards [hmid_ev] with i hi
  have hρnn : (0 : E d → ℝ) ≤ (φ i).normed volume := fun x ↦ (φ i).nonneg_normed x
  have hρcont : Continuous ((φ i).normed volume) := ((φ i).contDiff_normed (n := 1)).continuous
  have hρm : AEStronglyMeasurable ((φ i).normed volume) volume := hρcont.aestronglyMeasurable
  have hρ1 : ∫ y, (φ i).normed volume y ∂volume = 1 := (φ i).integral_normed
  have hρcs : HasCompactSupport ((φ i).normed volume) := (φ i).hasCompactSupport_normed
  have ha1 : eLpNorm ((h - w) ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume))
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal δ :=
    le_trans (eLpNorm_convolution_le hp hρnn hρm hρ1 (hh.sub hwml)) hwle
  have hCE1 : ConvolutionExists (h - w) ((φ i).normed volume) (lsmul ℝ ℝ) volume :=
    HasCompactSupport.convolutionExists_right (L := lsmul ℝ ℝ) hρcs hlochw hρcont
  have hCE2 : ConvolutionExists w ((φ i).normed volume) (lsmul ℝ ℝ) volume :=
    HasCompactSupport.convolutionExists_right (L := lsmul ℝ ℝ) hρcs hlocw hρcont
  have key_add : h ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)
      = (h - w) ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)
        + w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) := by
    have hd := ConvolutionExists.add_distrib hCE1 hCE2
    rwa [show (h - w) + w = h from by funext x; simp] at hd
  have hfun : h ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - h
      = (h - w) ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)
        + ((w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - w) + (w - h)) := by
    funext x
    have hpt := congrFun key_add x
    simp only [Pi.sub_apply, Pi.add_apply] at hpt ⊢
    rw [hpt]; ring
  have ha1m : AEStronglyMeasurable ((h - w) ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)) volume :=
    (HasCompactSupport.continuous_convolution_right (L := lsmul ℝ ℝ)
      hρcs hlochw hρcont).aestronglyMeasurable
  have hwconvm : AEStronglyMeasurable (w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)) volume :=
    (HasCompactSupport.continuous_convolution_right (L := lsmul ℝ ℝ)
      hρcs hlocw hρcont).aestronglyMeasurable
  have ha2m : AEStronglyMeasurable (w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - w) volume :=
    hwconvm.sub hwc.aestronglyMeasurable
  have ha3m : AEStronglyMeasurable (w - h) volume :=
    hwc.aestronglyMeasurable.sub hh.aestronglyMeasurable
  rw [hfun]
  calc eLpNorm ((h - w) ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)
        + ((w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - w) + (w - h)))
        (ENNReal.ofReal p) volume
      ≤ eLpNorm ((h - w) ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)) (ENNReal.ofReal p) volume
        + eLpNorm ((w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - w) + (w - h))
            (ENNReal.ofReal p) volume :=
        eLpNorm_add_le hq1
    _ ≤ eLpNorm ((h - w) ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume)) (ENNReal.ofReal p) volume
        + (eLpNorm (w ⋆[lsmul ℝ ℝ, volume] ((φ i).normed volume) - w) (ENNReal.ofReal p) volume
          + eLpNorm (w - h) (ENNReal.ofReal p) volume) := by
        gcongr
        exact eLpNorm_add_le hq1
    _ ≤ ENNReal.ofReal δ + (ENNReal.ofReal δ + ENNReal.ofReal δ) := by
        gcongr
    _ = η := by
        rw [← ENNReal.ofReal_add hδ0.le (by positivity),
          ← ENNReal.ofReal_add hδ0.le (by positivity : (0 : ℝ) ≤ δ + δ),
          show δ + (δ + δ) = η.toReal from by rw [hδdef]; ring, ENNReal.ofReal_toReal hηtop]

/-! ### Derivatives of mollifications of functions with a weak gradient -/

/-- If `ρ` is supported in `closedBall 0 r` and `closedBall x r ⊆ B`, then the convolution of
`B.indicator w` with `ρ` at `x` is the whole-space integral `∫ w y ρ(x - y)`. -/
theorem convolution_indicator_eq_integral {B : Set (E d)}
    (w f : E d → ℝ) {x : E d} {r : ℝ} (hf : ∀ y, r < ‖y‖ → f y = 0)
    (hx : closedBall x r ⊆ B) :
    (B.indicator w ⋆[lsmul ℝ ℝ, volume] f) x = ∫ y, w y * f (x - y) := by
  rw [convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp only [lsmul_apply, smul_eq_mul]
  by_cases hy : y ∈ B
  · rw [indicator_of_mem hy]
  · rw [indicator_of_notMem hy, zero_mul]
    have : r < ‖x - y‖ := by
      by_contra hle
      rw [not_lt] at hle
      exact hy (hx (by rw [mem_closedBall, dist_comm, dist_eq_norm]; exact hle))
    rw [hf _ this, mul_zero]

/-- **Derivative of a mollification.** If `∫ u ∂ᵥφ = -∫ ⟪G, v⟫ φ` for all test functions `φ`
supported in `B`, and `closedBall x ρ.rOut ⊆ B`, then the `v`-derivative of the mollification
`(B.indicator u) ⋆ ρ` at `x` is the mollification of `⟪G, v⟫`. -/
theorem fderiv_convolution_indicator_eq {B : Set (E d)} (hB : MeasurableSet B)
    {u : E d → ℝ} {G : E d → E d} (hu : IntegrableOn u B)
    (hw : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ B → ∀ v : E d,
      ∫ x, u x * fderiv ℝ φ x v = -∫ x, inner ℝ (G x) v * φ x)
    (ρ : ContDiffBump (0 : E d)) (v : E d) {x : E d} (hx : closedBall x ρ.rOut ⊆ B) :
    fderiv ℝ (B.indicator u ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) x v =
      (B.indicator (fun y ↦ inner ℝ (G y) v) ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) x := by
  set L := (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) with hL_def
  set k := ρ.normed volume with hk_def
  have hk_cs : HasCompactSupport k := ρ.hasCompactSupport_normed
  have hk_cd : ContDiff ℝ ∞ k := ρ.contDiff_normed
  have hk_cd1 : ContDiff ℝ 1 k := hk_cd.of_le (by exact_mod_cast le_top)
  have hk_diff : Differentiable ℝ k := hk_cd.differentiable (by simp)
  have huB_li : LocallyIntegrable (B.indicator u) volume :=
    (hu.integrable_indicator hB).locallyIntegrable
  have hk_zero : ∀ y, ρ.rOut < ‖y‖ → k y = 0 := by
    intro y hy
    refine image_eq_zero_of_notMem_tsupport ?_
    rw [hk_def, ρ.tsupport_normed_eq, mem_closedBall, dist_zero_right]
    exact not_le.2 hy
  have hdk_zero : ∀ y, ρ.rOut < ‖y‖ → fderiv ℝ k y v = 0 := by
    intro y hy
    have : y ∉ tsupport k := by
      rw [hk_def, ρ.tsupport_normed_eq, mem_closedBall, dist_zero_right]
      exact not_le.2 hy
    have h0 : fderiv ℝ k y = 0 :=
      Function.notMem_support.1 fun h ↦ this (support_fderiv_subset ℝ h)
    rw [h0, zero_apply]
  have hderiv := hk_cs.hasFDerivAt_convolution_right (L := L) huB_li hk_cd1 x
  have step2 : fderiv ℝ (B.indicator u ⋆[L, volume] k) x v
      = (B.indicator u ⋆[L, volume] fun a ↦ fderiv ℝ k a v) x := by
    rw [hderiv.fderiv]
    exact convolution_precompR_apply (𝕜 := ℝ) (L := L) huB_li (hk_cs.fderiv (𝕜 := ℝ))
      (hk_cd.continuous_fderiv (by simp)) x v
  set ψ : E d → ℝ := fun y ↦ k (x - y) with hψ_def
  have hψ_cd : ContDiff ℝ ∞ ψ := hk_cd.comp (contDiff_const.sub contDiff_id)
  have hsupp_sub : Function.support ψ ⊆ closedBall x ρ.rOut := by
    intro y hy
    by_contra hy'
    rw [mem_closedBall, dist_comm, dist_eq_norm, not_le] at hy'
    exact hy (hk_zero _ hy')
  have hsub_tsup : tsupport ψ ⊆ closedBall x ρ.rOut :=
    closure_minimal hsupp_sub isClosed_closedBall
  have hψ_cs : HasCompactSupport ψ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall x ρ.rOut) (isClosed_tsupport ψ) hsub_tsup
  have hψ_partial : ∀ y, fderiv ℝ ψ y v = -fderiv ℝ k (x - y) v := by
    intro y
    have hfd : HasFDerivAt ψ ((fderiv ℝ k (x - y)).comp (-ContinuousLinearMap.id ℝ (E d))) y :=
      (hk_diff (x - y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    rw [hfd.fderiv]
    simp
  have hibp := hw ψ hψ_cd hψ_cs (hsub_tsup.trans hx) v
  simp only [hψ_partial, mul_neg, integral_neg, neg_inj] at hibp
  rw [step2, convolution_indicator_eq_integral u _ hdk_zero hx,
    convolution_indicator_eq_integral _ _ hk_zero hx]
  exact hibp

end Mollifier

end EllipticBernoulli
