/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sobolev.Uniqueness
import EllipticBernoulli.Harmonic.Basic
import EllipticBernoulli.Classical.InnerVariationCalculus
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# The energy identity

For `w ≥ 0` Lipschitz on `ℝᵈ` and harmonic on `{w > 0}`, and every Lipschitz `η` with compact
support,
`∫ |∇w|² η = -∫ w ∇w · ∇η`
(`integral_norm_sq_gradient_mul_eq_neg`). Formally `Δ(w²/2) = |∇w|²`, because `w Δw = 0`.

## Proof

Testing the harmonicity of `w` on `{w > 0}` with the Lipschitz function `ψ_ε = (w - ε)⁺ η`,
whose support is a compact subset of `{w > 0}`, gives
`∫ 1_{w > ε} |∇w|² η + ∫ (w - ε)⁺ ∇w · ∇η = 0`. Let `ε ↓ 0` by dominated convergence, and use
`∇w = 0` a.e. on `{w = 0}` (Stampacchia).

Two auxiliary results are of independent use:

* `integral_fderiv_mul_eq_neg_of_lipschitzWith`: integration by parts `∫ ∂ᵥf ψ = -∫ f ∂ᵥψ` for
  `f` locally Lipschitz on an open `U` and `ψ` Lipschitz with compact support in `U` (the
  `C¹` version is `integral_fderiv_mul_eq_neg`);
* `integral_inner_gradient_eq_zero_of_harmonicOnNhd`: a function harmonic on an open `Ω` satisfies
  `∫ ∇w · ∇ψ = 0` for every Lipschitz `ψ` with compact support in `Ω`.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient Laplacian NNReal ContDiff

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Integrability of bounded functions supported in a compact set -/

/-- A bounded a.e.-strongly measurable function vanishing off a compact set is integrable. -/
theorem integrable_of_isCompact_of_bound {f : E d → ℝ} {K : Set (E d)} (hK : IsCompact K)
    (hf : AEStronglyMeasurable f) (hsupp : ∀ x ∉ K, f x = 0) {C : ℝ}
    (hC : ∀ x ∈ K, ‖f x‖ ≤ C) : Integrable f := by
  have hon : IntegrableOn f K :=
    Measure.integrableOn_of_bounded (M := C) hK.measure_lt_top.ne hf
      ((ae_restrict_mem hK.measurableSet).mono hC)
  refine (integrableOn_iff_integrable_of_support_subset fun x hx ↦ ?_).1 hon
  by_contra h
  exact hx (hsupp x h)

/-! ### Integration by parts against a Lipschitz test function -/

/-- **Integration by parts** for `f` locally Lipschitz on the open set `U` and `ψ` Lipschitz with
compact support in `U`: `∫ ∂ᵥf ψ = -∫ f ∂ᵥψ`. The derivatives are pointwise Fréchet derivatives
(`0` where they do not exist); `ψ` is differentiable a.e. by Rademacher's theorem. -/
theorem integral_fderiv_mul_eq_neg_of_lipschitzWith {U : Set (E d)} (hU : IsOpen U)
    {f : E d → ℝ} (hf : LocallyLipschitzOn U f) {ψ : E d → ℝ} {Kψ : ℝ≥0}
    (hψ : LipschitzWith Kψ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (v : E d) :
    ∫ x, fderiv ℝ f x v * ψ x = -∫ x, f x * fderiv ℝ ψ x v := by
  obtain ⟨δ, hδ, hδU⟩ := hψc.isCompact.exists_cthickening_subset_open hU hψU
  set V := cthickening δ (tsupport ψ)
  have hVc : IsCompact V := hψc.isCompact.cthickening
  obtain ⟨K, hK⟩ := (hf.mono hδU).exists_lipschitzOnWith_of_compact hVc
  obtain ⟨g, hg, hfg⟩ := hK.extend_real
  have hW : thickening δ (tsupport ψ) ⊆ V := thickening_subset_cthickening _ _
  have hfd : ∀ x ∈ tsupport ψ, fderiv ℝ f x = fderiv ℝ g x := fun x hx ↦
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem
      (isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx)) (hfg.mono hW))
  have e1 : ∫ x, fderiv ℝ f x v * ψ x = ∫ x, lineDeriv ℝ g x v * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [hg.ae_differentiableAt] with x hx
    by_cases hxs : x ∈ tsupport ψ
    · rw [hx.lineDeriv_eq_fderiv, hfd x hxs]
    · simp [image_eq_zero_of_notMem_tsupport hxs]
  have e2 : ∫ x, f x * fderiv ℝ ψ x v = ∫ x, g x * fderiv ℝ ψ x v := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hxs : x ∈ tsupport ψ
    · simp only
      rw [hfg (self_subset_cthickening _ hxs)]
    · simp [fderiv_of_notMem_tsupport ℝ hxs]
  rw [e1, e2, LipschitzWith.integral_lineDeriv_mul_eq hg hψ hψc v, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hψ.ae_differentiableAt] with x hd
  simp only [hd.lineDeriv_eq_fderiv, map_neg]
  ring

/-! ### Harmonic functions tested with Lipschitz functions -/

/-- The Laplacian as the sum of the second directional derivatives along an orthonormal basis, for
`f` of class `C²` near `x`. -/
theorem laplacian_eq_sum_fderiv_fderiv_of_contDiffAt {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (E d)) {f : E d → ℝ} {x : E d} (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- `⟨∇f(x), ∇g(x)⟩ = ∑ᵢ ∂ᵢf(x) ∂ᵢg(x)` along an orthonormal basis (no differentiability
needed: both sides vanish where a derivative does not exist). -/
theorem inner_gradient_eq_sum_fderiv_mul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (E d))
    (f g : E d → ℝ) (x : E d) :
    inner ℝ (∇ f x) (∇ g x) = ∑ i, fderiv ℝ f x (b i) * fderiv ℝ g x (b i) := by
  rw [← b.sum_inner_mul_inner (∇ f x) (∇ g x)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm (∇ g x) (b i), inner_gradient_left_eq_fderiv,
    inner_gradient_left_eq_fderiv]

/-- **Weak harmonicity against Lipschitz test functions.** If `w` is harmonic on the open set `Ω`
and `ψ` is Lipschitz with compact support in `Ω`, then `∫ ∇w · ∇ψ = 0`. -/
theorem integral_inner_gradient_eq_zero_of_harmonicOnNhd {Ω : Set (E d)} (hΩ : IsOpen Ω)
    {w : E d → ℝ} (hw : HarmonicOnNhd w Ω) {ψ : E d → ℝ} {Kψ : ℝ≥0}
    (hψ : LipschitzWith Kψ ψ) (hψc : HasCompactSupport ψ) (hψΩ : tsupport ψ ⊆ Ω) :
    ∫ x, inner ℝ (∇ w x) (∇ ψ x) = 0 := by
  set b := stdOrthonormalBasis ℝ (E d)
  have hsm : ContDiffOn ℝ ∞ w Ω := HarmonicOnNhd.contDiffOn_top hΩ hw
  set f : _ → E d → ℝ := fun i y ↦ fderiv ℝ w y (b i) with hf_def
  have hfs : ∀ i, ContDiffOn ℝ ∞ (f i) Ω := fun i ↦
    (hsm.fderiv_of_isOpen hΩ (m := ∞) le_rfl).clm_apply contDiffOn_const
  have hfL : ∀ i, LocallyLipschitzOn Ω (f i) := fun i x hx ↦ by
    obtain ⟨K, t, ht, hK⟩ :=
      (((hfs i).contDiffAt (hΩ.mem_nhds hx)).of_le (by norm_cast) :
        ContDiffAt ℝ 1 (f i) x).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  have hT : IsCompact (tsupport ψ) := hψc.isCompact
  -- integrability of the two families of products
  have hint1 : ∀ i, Integrable fun x ↦ f i x * fderiv ℝ ψ x (b i) := by
    intro i
    obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn ((hfs i).continuousOn.mono hψΩ)
    refine integrable_of_isCompact_of_bound hT
      ((measurable_fderiv_apply_const ℝ w (b i)).mul
        (measurable_fderiv_apply_const ℝ ψ (b i))).aestronglyMeasurable
      (fun x hx ↦ by simp [fderiv_of_notMem_tsupport ℝ hx]) (C := C * Kψ) fun x hx ↦ ?_
    rw [norm_mul]
    have h1 : ‖fderiv ℝ ψ x (b i)‖ ≤ Kψ := by
      refine ((fderiv ℝ ψ x).le_opNorm _).trans ?_
      rw [b.orthonormal.1 i, mul_one]
      exact norm_fderiv_le_of_lipschitz ℝ hψ
    exact mul_le_mul (hC x hx) h1 (norm_nonneg _) ((norm_nonneg _).trans (hC x hx))
  have hint2 : ∀ i, Integrable fun x ↦ fderiv ℝ (f i) x (b i) * ψ x := by
    intro i
    have hc : ContinuousOn (fun x ↦ fderiv ℝ (f i) x (b i)) Ω :=
      (((hfs i).continuousOn_fderiv_of_isOpen hΩ (by simp))).clm_apply continuousOn_const
    obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn ((hc.mul hψ.continuous.continuousOn).mono
      hψΩ)
    exact integrable_of_isCompact_of_bound hT
      ((measurable_fderiv_apply_const ℝ (f i) (b i)).mul
        hψ.continuous.measurable).aestronglyMeasurable
      (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]) hC
  calc ∫ x, inner ℝ (∇ w x) (∇ ψ x)
      = ∑ i, ∫ x, f i x * fderiv ℝ ψ x (b i) := by
        rw [← integral_finsetSum _ fun i _ ↦ hint1 i]
        exact integral_congr_ae (Eventually.of_forall fun x ↦
          inner_gradient_eq_sum_fderiv_mul b w ψ x)
    _ = -∑ i, ∫ x, fderiv ℝ (f i) x (b i) * ψ x := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [integral_fderiv_mul_eq_neg_of_lipschitzWith hΩ (hfL i) hψ hψc hψΩ, neg_neg]
    _ = -∫ x, Δ w x * ψ x := by
        rw [← integral_finsetSum _ fun i _ ↦ hint2 i]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only
        by_cases hx : x ∈ Ω
        · rw [← Finset.sum_mul, laplacian_eq_sum_fderiv_fderiv_of_contDiffAt b
            ((hw x hx).1)]
        · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hψΩ h)]
    _ = 0 := by
        rw [neg_eq_zero]
        refine integral_eq_zero_of_ae (Eventually.of_forall fun x ↦ ?_)
        by_cases hx : x ∈ Ω
        · simp [(hw x hx).2.eq_of_nhds]
        · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hψΩ h)]

/-! ### The energy identity -/

/-- Step 1 of the energy identity: testing with `ψ_ε = (w - ε)⁺ η`,
`∫ 1_{w > ε} |∇w|² η + (w - ε)⁺ ∇w · ∇η = 0`. -/
private theorem integral_cutoff_eq_zero {w : E d → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    (hharm : HarmonicOnNhd w {x | 0 < w x}) {η : E d → ℝ} {Kη : ℝ≥0}
    (hη : LipschitzWith Kη η) (hηc : HasCompactSupport η) {ε : ℝ} (hε : 0 < ε) :
    ∫ x, ({y | ε < w y}.indicator (fun y ↦ ‖∇ w y‖ ^ 2) x * η x +
      max (w x - ε) 0 * inner ℝ (∇ w x) (∇ η x)) = 0 := by
  set ψ : E d → ℝ := fun x ↦ max (w x - ε) 0 * η x with hψ_def
  have hΩ : IsOpen {x | 0 < w x} := isOpen_lt continuous_const hw.continuous
  have hm : LipschitzWith K fun x ↦ max (w x - ε) 0 := by
    simpa using (hw.sub (LipschitzWith.const ε)).max (LipschitzWith.const (0 : ℝ))
  have hψc : HasCompactSupport ψ := hηc.mul_left
  have hψL : ∃ Kψ, LipschitzWith Kψ ψ := by
    refine lipschitzWith_of_locallyLipschitz_of_hasCompactSupport ?_ hψc
    have hmul : LocallyLipschitz fun p : ℝ × ℝ ↦ p.1 * p.2 :=
      (contDiff_fst.mul contDiff_snd : ContDiff ℝ 1 fun p : ℝ × ℝ ↦ p.1 * p.2).locallyLipschitz
    exact hmul.comp (hm.locallyLipschitz.prodMk hη.locallyLipschitz)
  obtain ⟨Kψ, hψL⟩ := hψL
  have hψΩ : tsupport ψ ⊆ {x | 0 < w x} := by
    refine (closure_minimal (fun x hx ↦ ?_) (isClosed_le continuous_const hw.continuous)).trans
      fun x (hx : ε ≤ w x) ↦ (show 0 < w x from hε.trans_le hx)
    by_contra h
    exact hx (by simp [ψ, max_eq_right (by linarith [not_le.1 h] : w x - ε ≤ 0)])
  have h0 := integral_inner_gradient_eq_zero_of_harmonicOnNhd hΩ hharm hψL hψc hψΩ
  have hG : HasWeakGradient univ w (∇ w) :=
    (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hw.locallyLipschitz.locallyLipschitzOn).1
  have hst := hG.ae_eq_zero_of_eq_const isOpen_univ ε
  rw [Measure.restrict_univ] at hst
  refine (integral_congr_ae ?_).trans h0
  filter_upwards [hw.ae_differentiableAt, hη.ae_differentiableAt, hst] with x hwx hηx hstx
  rw [real_inner_comm (∇ ψ x) (∇ w x), inner_gradient_left_eq_fderiv ψ]
  rcases lt_trichotomy (w x) ε with hlt | heq | hgt
  · have hloc : ψ =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [(isOpen_lt hw.continuous continuous_const).mem_nhds hlt] with y hy
      simp [ψ, max_eq_right (by linarith [show w y < ε from hy] : w y - ε ≤ 0)]
    rw [hloc.fderiv_eq]
    simp [indicator, not_lt.2 hlt.le, max_eq_right (by linarith : w x - ε ≤ 0)]
  · simp [hstx heq]
  · have hloc : ψ =ᶠ[𝓝 x] fun y ↦ (w y - ε) * η y := by
      filter_upwards [(isOpen_lt continuous_const hw.continuous).mem_nhds hgt] with y hy
      simp [ψ, max_eq_left (by linarith [show ε < w y from hy] : 0 ≤ w y - ε)]
    rw [hloc.fderiv_eq, fderiv_fun_mul (hwx.sub_const ε) hηx, fderiv_sub_const]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [← inner_gradient_left_eq_fderiv, ← inner_gradient_left_eq_fderiv,
      real_inner_self_eq_norm_sq, real_inner_comm]
    simp [indicator, hgt, max_eq_left (by linarith : 0 ≤ w x - ε)]
    ring

/-- **The energy identity.** Let `w ≥ 0` be Lipschitz on `ℝᵈ`
and harmonic on `{w > 0}`. Then for every Lipschitz `η` with compact support,
`∫ |∇w|² η = -∫ w ∇w · ∇η`. Gradients are pointwise (`0` where `w` or `η` is not
differentiable). The function `w` is assumed globally Lipschitz,
which covers `w = u⁺` and `w = u⁻` for a Lipschitz two-phase minimizer `u`. -/
theorem integral_norm_sq_gradient_mul_eq_neg {w : E d → ℝ} {K : ℝ≥0} (hw : LipschitzWith K w)
    (hw0 : ∀ x, 0 ≤ w x) (hharm : HarmonicOnNhd w {x | 0 < w x}) {η : E d → ℝ} {Kη : ℝ≥0}
    (hη : LipschitzWith Kη η) (hηc : HasCompactSupport η) :
    ∫ x, ‖∇ w x‖ ^ 2 * η x = -∫ x, w x * inner ℝ (∇ w x) (∇ η x) := by
  set T := tsupport η
  have hT : IsCompact T := hηc.isCompact
  obtain ⟨Mη, hMη⟩ := hT.exists_bound_of_continuousOn hη.continuous.continuousOn
  obtain ⟨Mw, hMw⟩ := hT.exists_bound_of_continuousOn hw.continuous.continuousOn
  have hgw : ∀ x, ‖∇ w x‖ ≤ K := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hw
  have hgη : ∀ x, ‖∇ η x‖ ≤ Kη := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hη
  have hη0 : ∀ x ∉ T, η x = 0 ∧ ∇ η x = 0 := fun x hx ↦
    ⟨image_eq_zero_of_notMem_tsupport hx, by
      rw [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]⟩
  -- the integrands
  set F : ℝ → E d → ℝ := fun ε x ↦ {y | ε < w y}.indicator (fun y ↦ ‖∇ w y‖ ^ 2) x * η x +
      max (w x - ε) 0 * inner ℝ (∇ w x) (∇ η x) with hF_def
  set C : ℝ := (K : ℝ) ^ 2 * Mη + Mw * (K * Kη)
  have hFmeas : ∀ ε, AEStronglyMeasurable (F ε) := fun ε ↦ by
    have h1 : Measurable ({y | ε < w y}.indicator fun y ↦ ‖∇ w y‖ ^ 2) :=
      ((measurable_gradient w).norm.pow_const 2).indicator
        (measurableSet_lt measurable_const hw.continuous.measurable)
    exact ((h1.mul hη.continuous.measurable).add
      (((hw.continuous.measurable.sub_const ε).max measurable_const).mul
        (Measurable.inner (measurable_gradient w) (measurable_gradient η)))).aestronglyMeasurable
  have hFbound : ∀ ε, 0 ≤ ε → ∀ x ∈ T, ‖F ε x‖ ≤ C := by
    intro ε hε x hx
    have hi : ‖{y | ε < w y}.indicator (fun y ↦ ‖∇ w y‖ ^ 2) x‖ ≤ (K : ℝ) ^ 2 := by
      refine (norm_indicator_le_norm_self _ _).trans ?_
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hgw x) 2
    have hmx : ‖max (w x - ε) 0‖ ≤ Mw := by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine (max_le (by linarith [hw0 x]) (hw0 x)).trans ?_
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMw x hx)
    have hin : ‖inner ℝ (∇ w x) (∇ η x)‖ ≤ K * Kη :=
      (norm_inner_le_norm _ _).trans (mul_le_mul (hgw x) (hgη x) (norm_nonneg _) K.2)
    calc ‖F ε x‖ ≤ ‖{y | ε < w y}.indicator (fun y ↦ ‖∇ w y‖ ^ 2) x‖ * ‖η x‖ +
          ‖max (w x - ε) 0‖ * ‖inner ℝ (∇ w x) (∇ η x)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ (K : ℝ) ^ 2 * Mη + Mw * (K * Kη) := by
          gcongr
          · exact hMη x hx
          · exact (norm_nonneg _).trans (hMw x hx)
  have hFzero : ∀ ε x, x ∉ T → F ε x = 0 := fun ε x hx ↦ by
    simp only [F, (hη0 x hx).1, (hη0 x hx).2, inner_zero_right, mul_zero, add_zero]
  -- dominated convergence along `ε = 1 / (n + 1)`
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set F₀ : E d → ℝ := fun x ↦ {y | 0 < w y}.indicator (fun y ↦ ‖∇ w y‖ ^ 2) x * η x +
      w x * inner ℝ (∇ w x) (∇ η x) with hF₀_def
  have hlim : Tendsto (fun n ↦ ∫ x, F (ε n) x) atTop (𝓝 (∫ x, F₀ x)) := by
    refine tendsto_integral_of_dominated_convergence (T.indicator fun _ ↦ C)
      (fun n ↦ hFmeas (ε n)) ?_ (fun n ↦ Eventually.of_forall fun x ↦ ?_)
      (Eventually.of_forall fun x ↦ ?_)
    · exact (integrable_indicator_iff hT.measurableSet).2
        (integrableOn_const hT.measure_lt_top.ne)
    · by_cases hx : x ∈ T
      · rw [indicator_of_mem hx]; exact hFbound _ (hεpos n).le x hx
      · rw [indicator_of_notMem hx, hFzero _ _ hx, norm_zero]
    · have h2 : Tendsto (fun n ↦ max (w x - ε n) 0 * inner ℝ (∇ w x) (∇ η x)) atTop
          (𝓝 (w x * inner ℝ (∇ w x) (∇ η x))) := by
        have : Tendsto (fun n ↦ max (w x - ε n) 0) atTop (𝓝 (max (w x - 0) 0)) :=
          ((tendsto_const_nhds.sub hεlim).max tendsto_const_nhds)
        rw [sub_zero, max_eq_left (hw0 x)] at this
        exact this.mul_const _
      have h1 : Tendsto (fun n ↦ {y | ε n < w y}.indicator (fun y ↦ ‖∇ w y‖ ^ 2) x * η x)
          atTop (𝓝 ({y | 0 < w y}.indicator (fun y ↦ ‖∇ w y‖ ^ 2) x * η x)) := by
        by_cases hpos : 0 < w x
        · refine tendsto_const_nhds.congr' ?_
          filter_upwards [hεlim.eventually (gt_mem_nhds hpos)] with n hn
          simp [indicator, hpos, hn]
        · refine tendsto_const_nhds.congr fun n ↦ ?_
          have : ¬ ε n < w x := fun h ↦ hpos ((hεpos n).trans h)
          simp [indicator, hpos, this]
      exact h1.add h2
  have hF₀ : ∫ x, F₀ x = 0 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n ↦
      (integral_cutoff_eq_zero hw hharm hη hηc (hεpos n)).symm)
  -- remove the indicator (Stampacchia) and split the integral
  have hG : HasWeakGradient univ w (∇ w) :=
    (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hw.locallyLipschitz.locallyLipschitzOn).1
  have hst := hG.ae_eq_zero_of_eq_zero isOpen_univ
  rw [Measure.restrict_univ] at hst
  have hind : (fun x ↦ ‖∇ w x‖ ^ 2 * η x) =ᵐ[volume]
      fun x ↦ {y | 0 < w y}.indicator (fun y ↦ ‖∇ w y‖ ^ 2) x * η x := by
    filter_upwards [hst] with x hx
    by_cases hpos : 0 < w x
    · simp [indicator, hpos]
    · simp [indicator, hpos, hx (le_antisymm (not_lt.1 hpos) (hw0 x))]
  have hint1 : Integrable fun x ↦ ‖∇ w x‖ ^ 2 * η x :=
    integrable_of_isCompact_of_bound hT
      (((measurable_gradient w).norm.pow_const 2).mul
        hη.continuous.measurable).aestronglyMeasurable
      (fun x hx ↦ by simp [(hη0 x hx).1]) (C := (K : ℝ) ^ 2 * Mη) fun x hx ↦ by
        rw [norm_mul, norm_pow, norm_norm]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hgw x) 2) (hMη x hx)
          (norm_nonneg _) (by positivity)
  have hint2 : Integrable fun x ↦ w x * inner ℝ (∇ w x) (∇ η x) :=
    integrable_of_isCompact_of_bound hT
      (hw.continuous.measurable.mul
        (Measurable.inner (measurable_gradient w) (measurable_gradient η))).aestronglyMeasurable
      (fun x hx ↦ by simp [(hη0 x hx).2]) (C := Mw * (K * Kη)) fun x hx ↦ by
        rw [norm_mul]
        exact mul_le_mul (hMw x hx)
          ((norm_inner_le_norm _ _).trans (mul_le_mul (hgw x) (hgη x) (norm_nonneg _) K.2))
          (norm_nonneg _) ((norm_nonneg _).trans (hMw x hx))
  have hsplit : ∫ x, F₀ x =
      (∫ x, ‖∇ w x‖ ^ 2 * η x) + ∫ x, w x * inner ℝ (∇ w x) (∇ η x) := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae ?_
    filter_upwards [hind] with x hx
    simp only [F₀]
    rw [hx]
  linarith

end EllipticBernoulli
