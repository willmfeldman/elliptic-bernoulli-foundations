/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import EllipticBernoulli.TwoPhase.Rescaling.Compact
import EllipticBernoulli.TwoPhase.EnergyIdentity
import EllipticBernoulli.Sobolev.Closure
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sobolev.Uniqueness
import EllipticBernoulli.Sphere.Radial
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Strong convergence of the gradients of rescalings

Let `f k : ℝᵈ → ℝ` be `L`-Lipschitz, harmonic on `{f k > 0}` and on `{f k < 0}`, and let
`f k → f₀` locally uniformly.

* `tendsto_setIntegral_norm_sq_gradient_sub`: for every compact `K`,
  `∫_K |∇f_k - ∇f₀|² → 0`, and the same for the positive parts `f_k⁺ = max(f_k, 0)` and the negative
  parts `f_k⁻ = max(-f_k, 0)`. The whole sequence converges: no subsequence is needed.
* `exists_subseq_ae_tendsto_gradient`: consequently, every subsequence has a further subsequence
  along which `∇f_k → ∇f₀` a.e. on `K`.
* `tendsto_integral_of_forall_subseq_ae`: dominated convergence along subsequences, the form in
  which the strong convergence is used for the Weiss defect, the Weiss functional and the ACF
  functional (`TwoPhase/Rescaling/Limits.lean`).

## Proof

For one phase `w_k = f_k^±` (nonnegative, Lipschitz, harmonic on `{w_k > 0}`) with limit `w₀`
(harmonic on `{w₀ > 0}` by `harmonicOnNhd_posSet_of_tendstoLocallyUniformly`), and a Lipschitz
`η` with compact support, the energy identity (`integral_norm_sq_gradient_mul_eq_neg`) gives
`∫ |∇w_k|² η = -∫ w_k ∇w_k · ∇η`. Along a subsequence with `∇w_k ⇀ ∇w₀` weakly in `L²(spt η)`
(`exists_subseq_tendstoWeakL2_gradient`), the right side tends to `-∫ w₀ ∇w₀ · ∇η = ∫ |∇w₀|² η`
(uniform times weak convergence), and `∫ ∇w_k · ∇w₀ η → ∫ |∇w₀|² η`. Expanding the square,
`∫ |∇w_k - ∇w₀|² η → 0`. Every subsequence has such a further subsequence, so the whole sequence
converges (`Filter.tendsto_of_subseq_tendsto`). Taking `η ≥ 1_K` gives the statement on `K`.
For `f_k` itself, `∇f = ∇f⁺ - ∇f⁻` a.e. (`ae_gradient_eq_sub_posPart_negPart`, Stampacchia).
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient NNReal ENNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### One phase, with a cutoff -/

/-- **Strong convergence of one phase, along a weakly convergent sequence.** Let `w k ≥ 0` be
`L`-Lipschitz and harmonic on `{w k > 0}`, `w₀ ≥ 0` be `L`-Lipschitz and harmonic on `{w₀ > 0}`,
`w k → w₀` locally uniformly, and `∇w_k ⇀ ∇w₀` weakly in `L²(K)` for every compact `K`. Then
`∫ |∇w_k - ∇w₀|² η → 0` for every Lipschitz `η` with compact support. -/
theorem tendsto_integral_norm_sq_gradient_sub_mul_of_tendstoWeakL2 {w : ℕ → E d → ℝ}
    {w₀ : E d → ℝ} {L : ℝ≥0} (hw : ∀ k, LipschitzWith L (w k)) (hw0 : ∀ k x, 0 ≤ w k x)
    (hH : ∀ k, HarmonicOnNhd (w k) {x | 0 < w k x}) (hw₀ : LipschitzWith L w₀)
    (hw₀0 : ∀ x, 0 ≤ w₀ x) (hH₀ : HarmonicOnNhd w₀ {x | 0 < w₀ x})
    (hconv : TendstoLocallyUniformly w w₀ atTop)
    (hweak : ∀ K, IsCompact K → TendstoWeakL2 volume K (fun k ↦ ∇ (w k)) (∇ w₀) atTop)
    {η : E d → ℝ} {Kη : ℝ≥0} (hη : LipschitzWith Kη η) (hηc : HasCompactSupport η) :
    Tendsto (fun k ↦ ∫ x, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 * η x) atTop (𝓝 0) := by
  set T := tsupport η with hTdef
  have hT : IsCompact T := hηc.isCompact
  have hTm : MeasurableSet T := hT.measurableSet
  have : IsFiniteMeasure (volume.restrict T) := isFiniteMeasure_restrict.2 hT.measure_lt_top.ne
  -- global bounds for `η` and for `w₀` on `T`
  have hη0 : ∀ x ∉ T, η x = 0 ∧ ∇ η x = 0 := fun x hx ↦
    ⟨image_eq_zero_of_notMem_tsupport hx, by
      rw [gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero]⟩
  obtain ⟨Mη, hMη0, hMη⟩ : ∃ C, 0 ≤ C ∧ ∀ x, ‖η x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hη.continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
    by_cases hx : x ∈ T
    · exact (hC x hx).trans (le_max_left _ _)
    · rw [(hη0 x hx).1, norm_zero]; exact le_max_right _ _
  obtain ⟨Mw, hMw0, hMw⟩ : ∃ C, 0 ≤ C ∧ ∀ x ∈ T, ‖w₀ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hw₀.continuous.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx ↦ (hC x hx).trans (le_max_left _ _)⟩
  have hga : ∀ k x, ‖∇ (w k) x‖ ≤ L := fun k x ↦ norm_gradient_le_of_lipschitzWith (hw k) x
  have hgb : ∀ x, ‖∇ w₀ x‖ ≤ L := fun x ↦ norm_gradient_le_of_lipschitzWith hw₀ x
  have hgη : ∀ x, ‖∇ η x‖ ≤ Kη := fun x ↦ norm_gradient_le_of_lipschitzWith hη x
  have hma : ∀ k, Measurable (∇ (w k)) := fun k ↦ measurable_gradient _
  have hmb : Measurable (∇ w₀) := measurable_gradient _
  have hmg : Measurable (∇ η) := measurable_gradient _
  have hmη : Measurable η := hη.continuous.measurable
  -- integrals over `ℝᵈ` of functions vanishing off `T` are integrals over `T`
  have hUT : ∀ F : E d → ℝ, (∀ x ∉ T, F x = 0) → ∫ x, F x = ∫ x in T, F x := fun F hF ↦
    (setIntegral_eq_integral_of_forall_compl_eq_zero hF).symm
  -- an integrability criterion
  have hint : ∀ F : E d → ℝ, AEStronglyMeasurable F → (∀ x ∉ T, F x = 0) →
      ∀ C, (∀ x ∈ T, ‖F x‖ ≤ C) → Integrable F := fun F hF hs C hC ↦
    integrable_of_isCompact_of_bound hT hF hs hC
  -- the three integrals
  set I1 : ℕ → ℝ := fun k ↦ ∫ x, ‖∇ (w k) x‖ ^ 2 * η x
  set I2 : ℕ → ℝ := fun k ↦ ∫ x, inner ℝ (∇ (w k) x) (∇ w₀ x) * η x
  set I3 : ℝ := ∫ x, ‖∇ w₀ x‖ ^ 2 * η x
  have hint1 : ∀ k, Integrable fun x ↦ ‖∇ (w k) x‖ ^ 2 * η x := fun k ↦
    hint _ (((hma k).norm.pow_const 2).mul hmη).aestronglyMeasurable
      (fun x hx ↦ by simp [(hη0 x hx).1]) ((L : ℝ) ^ 2 * Mη) fun x hx ↦ by
        rw [norm_mul, norm_pow, norm_norm]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hga k x) 2) (hMη x)
          (norm_nonneg _) (by positivity)
  have hint2 : ∀ k, Integrable fun x ↦ inner ℝ (∇ (w k) x) (∇ w₀ x) * η x := fun k ↦
    hint _ (((hma k).inner hmb).mul hmη).aestronglyMeasurable
      (fun x hx ↦ by simp [(hη0 x hx).1]) ((L : ℝ) * L * Mη) fun x hx ↦ by
        rw [norm_mul]
        refine mul_le_mul ((norm_inner_le_norm _ _).trans
          (mul_le_mul (hga k x) (hgb x) (norm_nonneg _) (by positivity))) (hMη x)
          (norm_nonneg _) (by positivity)
  have hint3 : Integrable fun x ↦ ‖∇ w₀ x‖ ^ 2 * η x :=
    hint _ ((hmb.norm.pow_const 2).mul hmη).aestronglyMeasurable
      (fun x hx ↦ by simp [(hη0 x hx).1]) ((L : ℝ) ^ 2 * Mη) fun x hx ↦ by
        rw [norm_mul, norm_pow, norm_norm]
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hgb x) 2) (hMη x)
          (norm_nonneg _) (by positivity)
  -- the square expanded
  have hexp : ∀ k, ∫ x, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 * η x = I1 k - 2 * I2 k + I3 := by
    intro k
    have e : (fun x ↦ ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 * η x) = fun x ↦
        ‖∇ (w k) x‖ ^ 2 * η x - 2 * (inner ℝ (∇ (w k) x) (∇ w₀ x) * η x) +
          ‖∇ w₀ x‖ ^ 2 * η x := by
      funext x; rw [norm_sub_sq_real]; ring
    rw [e, integral_add (f := fun x ↦ ‖∇ (w k) x‖ ^ 2 * η x -
      2 * (inner ℝ (∇ (w k) x) (∇ w₀ x) * η x)) ((hint1 k).sub ((hint2 k).const_mul 2)) hint3,
      integral_sub (hint1 k) ((hint2 k).const_mul 2), integral_const_mul]
  -- weak convergence on `T`, tested with bounded functions
  have hweakT : ∀ φ : E d → E d, Measurable φ → ∀ C, (∀ x, ‖φ x‖ ≤ C) →
      Tendsto (fun k ↦ ∫ x in T, inner ℝ (∇ (w k) x) (φ x)) atTop
        (𝓝 (∫ x in T, inner ℝ (∇ w₀ x) (φ x))) := fun φ hφ C hC ↦
    (hweak T hT).2.2 φ (MemLp.of_bound hφ.aestronglyMeasurable C (Eventually.of_forall hC))
  -- `I2 → I3`
  have hI2 : Tendsto I2 atTop (𝓝 I3) := by
    have e : ∀ k, I2 k = ∫ x in T, inner ℝ (∇ (w k) x) (η x • ∇ w₀ x) := fun k ↦ by
      change ∫ x, inner ℝ (∇ (w k) x) (∇ w₀ x) * η x = _
      rw [hUT _ fun x hx ↦ by simp [(hη0 x hx).1]]
      refine setIntegral_congr_fun hTm fun x _ ↦ ?_
      simp only [inner_smul_right]; ring
    have e3 : I3 = ∫ x in T, inner ℝ (∇ w₀ x) (η x • ∇ w₀ x) := by
      change ∫ x, ‖∇ w₀ x‖ ^ 2 * η x = _
      rw [hUT _ fun x hx ↦ by simp [(hη0 x hx).1]]
      refine setIntegral_congr_fun hTm fun x _ ↦ ?_
      simp only [inner_smul_right, real_inner_self_eq_norm_sq]; ring
    rw [show I2 = _ from funext e, e3]
    exact hweakT _ (hmη.smul hmb) (Mη * L) fun x ↦ by
      rw [norm_smul]; exact mul_le_mul (hMη x) (hgb x) (norm_nonneg _) hMη0
  -- `∫ w_k ∇w_k · ∇η → ∫ w₀ ∇w₀ · ∇η`: uniform times weak convergence
  have hJ : Tendsto (fun k ↦ ∫ x, w k x * inner ℝ (∇ (w k) x) (∇ η x)) atTop
      (𝓝 (∫ x, w₀ x * inner ℝ (∇ w₀ x) (∇ η x))) := by
    have hintJ : ∀ (v : E d → ℝ) (G : E d → E d), Continuous v → Measurable G →
        (∀ x, ‖G x‖ ≤ L) → Integrable fun x ↦ v x * inner ℝ (G x) (∇ η x) := by
      intro v G hv hG hGb
      obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn hv.continuousOn
      exact hint _ (hv.measurable.mul (hG.inner hmg)).aestronglyMeasurable
        (fun x hx ↦ by simp [(hη0 x hx).2]) (C * (L * Kη)) fun x hx ↦ by
          rw [norm_mul]
          exact mul_le_mul (hC x hx) ((norm_inner_le_norm _ _).trans
            (mul_le_mul (hGb x) (hgη x) (norm_nonneg _) (by positivity))) (norm_nonneg _)
            ((norm_nonneg _).trans (hC x hx))
    have hsplit : ∀ k, ∫ x, w k x * inner ℝ (∇ (w k) x) (∇ η x) =
        (∫ x, (w k x - w₀ x) * inner ℝ (∇ (w k) x) (∇ η x)) +
          ∫ x in T, inner ℝ (∇ (w k) x) (w₀ x • ∇ η x) := by
      intro k
      have hi : Integrable fun x ↦ inner ℝ (∇ (w k) x) (w₀ x • ∇ η x) := by
        convert hintJ w₀ (∇ (w k)) hw₀.continuous (hma k) (hga k) using 2 with x
        rw [inner_smul_right]
      have hA : Integrable fun x ↦ (w k x - w₀ x) * inner ℝ (∇ (w k) x) (∇ η x) :=
        hintJ (fun x ↦ w k x - w₀ x) _ ((hw k).continuous.sub hw₀.continuous) (hma k) (hga k)
      rw [← hUT (fun x ↦ inner ℝ (∇ (w k) x) (w₀ x • ∇ η x))
        (fun x hx ↦ by simp [(hη0 x hx).2]), ← integral_add hA hi]
      congr 1; funext x; rw [inner_smul_right]; ring
    have hlim0 : ∫ x, w₀ x * inner ℝ (∇ w₀ x) (∇ η x) =
        0 + ∫ x in T, inner ℝ (∇ w₀ x) (w₀ x • ∇ η x) := by
      rw [zero_add, hUT _ (fun x hx ↦ by simp [(hη0 x hx).2])]
      refine setIntegral_congr_fun hTm fun x _ ↦ ?_
      rw [inner_smul_right]
    rw [hlim0, show (fun k ↦ ∫ x, w k x * inner ℝ (∇ (w k) x) (∇ η x)) = _ from funext hsplit]
    refine Tendsto.add ?_ (hweakT _ (hw₀.continuous.measurable.smul hmg) (Mw * Kη) fun x ↦ ?_)
    · have hunif := Metric.tendstoUniformlyOn_iff.1
        ((tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) T hT) 1 one_pos
      have h := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
        (T.indicator fun _ ↦ (L : ℝ) * Kη)
        (F := fun k x ↦ (w k x - w₀ x) * inner ℝ (∇ (w k) x) (∇ η x)) (f := fun _ ↦ 0)
        (Eventually.of_forall fun k ↦ (((hw k).continuous.sub hw₀.continuous).measurable.mul
          ((hma k).inner hmg)).aestronglyMeasurable) ?_
        ((integrableOn_const hT.measure_lt_top.ne).integrable_indicator hTm) ?_
      · simpa using h
      · filter_upwards [hunif] with k hk
        refine Eventually.of_forall fun x ↦ ?_
        by_cases hx : x ∈ T
        · rw [indicator_of_mem hx, norm_mul]
          have h1 := hk x hx
          rw [Real.dist_eq, abs_sub_comm] at h1
          calc ‖w k x - w₀ x‖ * ‖inner ℝ (∇ (w k) x) (∇ η x)‖ ≤ 1 * (L * Kη) :=
                mul_le_mul h1.le ((norm_inner_le_norm _ _).trans
                  (mul_le_mul (hga k x) (hgη x) (norm_nonneg _) (by positivity)))
                  (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
        · simp [indicator_of_notMem hx, (hη0 x hx).2]
      · refine Eventually.of_forall fun x ↦ ?_
        have hx := (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ x)
        have h0 : Tendsto (fun k ↦ ‖w k x - w₀ x‖ * ((L : ℝ) * Kη)) atTop (𝓝 0) := by
          simpa using (tendsto_sub_nhds_zero_iff.2 hx).norm.mul_const ((L : ℝ) * Kη)
        refine squeeze_zero_norm (fun k ↦ ?_) h0
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
          (mul_le_mul (hga k x) (hgη x) (norm_nonneg _) (by positivity))) (norm_nonneg _)
    · by_cases hx : x ∈ T
      · rw [norm_smul]
        exact mul_le_mul (hMw x hx) (hgη x) (norm_nonneg _) hMw0
      · rw [(hη0 x hx).2, smul_zero, norm_zero]; positivity
  -- `I1 → I3`, by the energy identity
  have hI1 : Tendsto I1 atTop (𝓝 I3) := by
    have e1 : I1 = fun k ↦ -∫ x, w k x * inner ℝ (∇ (w k) x) (∇ η x) := funext fun k ↦
      integral_norm_sq_gradient_mul_eq_neg (hw k) (hw0 k) (hH k) hη hηc
    have e3 : I3 = -∫ x, w₀ x * inner ℝ (∇ w₀ x) (∇ η x) :=
      integral_norm_sq_gradient_mul_eq_neg hw₀ hw₀0 hH₀ hη hηc
    rw [e1, e3]
    exact hJ.neg
  rw [show (fun k ↦ ∫ x, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 * η x) = fun k ↦ I1 k - 2 * I2 k + I3 from
    funext hexp]
  have h := (hI1.sub (hI2.const_mul 2)).add_const I3
  rwa [show I3 - 2 * I3 + I3 = 0 by ring] at h

/-- **Strong convergence of one phase with a cutoff.** Let `w k ≥ 0` be
`L`-Lipschitz and harmonic on `{w k > 0}`, with `w k → w₀` locally uniformly. Then
`∫ |∇w_k - ∇w₀|² η → 0` for every Lipschitz `η` with compact support. Every subsequence has a
further subsequence with `∇w_k ⇀ ∇w₀` weakly (`exists_subseq_tendstoWeakL2_gradient`), along
which `tendsto_integral_norm_sq_gradient_sub_mul_of_tendstoWeakL2` applies; so the whole sequence
converges. -/
theorem tendsto_integral_norm_sq_gradient_sub_mul {w : ℕ → E d → ℝ} {w₀ : E d → ℝ} {L : ℝ≥0}
    (hw : ∀ k, LipschitzWith L (w k)) (hw0 : ∀ k x, 0 ≤ w k x)
    (hH : ∀ k, HarmonicOnNhd (w k) {x | 0 < w k x}) (hconv : TendstoLocallyUniformly w w₀ atTop)
    {η : E d → ℝ} {Kη : ℝ≥0} (hη : LipschitzWith Kη η) (hηc : HasCompactSupport η) :
    Tendsto (fun k ↦ ∫ x, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 * η x) atTop (𝓝 0) := by
  have hw₀ := lipschitzWith_of_tendstoLocallyUniformly hw hconv
  have hw₀0 : ∀ x, 0 ≤ w₀ x := fun x ↦ ge_of_tendsto'
    ((tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ x)) fun k ↦ hw0 k x
  have hH₀ := harmonicOnNhd_posSet_of_tendstoLocallyUniformly hH hw₀.continuous hconv
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  have hconv' := TendstoLocallyUniformly.comp_tendsto hconv hns
  obtain ⟨φ, hφ, hweak⟩ := exists_subseq_tendstoWeakL2_gradient (fun k ↦ hw (ns k)) hconv'
  exact ⟨φ, tendsto_integral_norm_sq_gradient_sub_mul_of_tendstoWeakL2 (fun _ ↦ hw _)
    (fun _ ↦ hw0 _) (fun _ ↦ hH _) hw₀ hw₀0 hH₀
    (TendstoLocallyUniformly.comp_tendsto (F := fun k ↦ w (ns k)) hconv' hφ.tendsto_atTop)
    hweak hη hηc⟩

/-- A Lipschitz cutoff with compact support that is `≥ 1` on a compact set `K`. -/
theorem exists_lipschitzWith_hasCompactSupport_one_le {K : Set (E d)} (hK : IsCompact K) :
    ∃ (η : E d → ℝ) (Kη : ℝ≥0), LipschitzWith Kη η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧
      ∀ x ∈ K, 1 ≤ η x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 0, LipschitzWith.const 0, HasCompactSupport.zero, fun _ ↦ le_rfl,
      fun _ hx ↦ hx.elim⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : E d)
  refine ⟨fun x ↦ max (1 - infDist x K) 0, _,
    ((LipschitzWith.const (1 : ℝ)).sub (Metric.lipschitz_infDist_pt K)).max_const 0,
    HasCompactSupport.intro (isCompact_closedBall (0 : E d) (R + 1)) fun x hx ↦ ?_,
    fun _ ↦ le_max_right _ _, fun x hx ↦ ?_⟩
  · refine max_eq_right (sub_nonpos.2 (not_lt.1 fun h ↦ hx ?_))
    obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff hne).1 h
    have := mem_closedBall.1 (hR hy)
    rw [dist_zero_right] at this
    rw [mem_closedBall, dist_zero_right]
    rw [dist_eq_norm] at hxy
    linarith [norm_le_insert' x y]
  · simp only [Metric.infDist_zero_of_mem hx, sub_zero]
    exact le_max_left _ _

/-- A bounded measurable function is integrable on a compact set. -/
theorem integrableOn_of_isCompact_of_norm_le {F : E d → ℝ} {K : Set (E d)} (hK : IsCompact K)
    (hF : Measurable F) {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) : IntegrableOn F K :=
  Measure.integrableOn_of_bounded (M := C) hK.measure_lt_top.ne hF.aestronglyMeasurable
    (Eventually.of_forall hC)

/-- **Strong convergence of one phase on a compact set.** Under the
hypotheses of `tendsto_integral_norm_sq_gradient_sub_mul`, `∫_K |∇w_k - ∇w₀|² → 0` for every
compact `K`. -/
theorem tendsto_setIntegral_norm_sq_gradient_sub_of_nonneg {w : ℕ → E d → ℝ} {w₀ : E d → ℝ}
    {L : ℝ≥0} (hw : ∀ k, LipschitzWith L (w k)) (hw0 : ∀ k x, 0 ≤ w k x)
    (hH : ∀ k, HarmonicOnNhd (w k) {x | 0 < w k x}) (hconv : TendstoLocallyUniformly w w₀ atTop)
    {K : Set (E d)} (hK : IsCompact K) :
    Tendsto (fun k ↦ ∫ x in K, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2) atTop (𝓝 0) := by
  have hw₀ := lipschitzWith_of_tendstoLocallyUniformly hw hconv
  obtain ⟨η, Kη, hη, hηc, hη0, hη1⟩ := exists_lipschitzWith_hasCompactSupport_one_le hK
  have hlim := tendsto_integral_norm_sq_gradient_sub_mul hw hw0 hH hconv hη hηc
  have hbd : ∀ k x, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 ≤ (2 * L) ^ 2 := fun k x ↦
    pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by
      linarith [norm_gradient_le_of_lipschitzWith (hw k) x,
        norm_gradient_le_of_lipschitzWith hw₀ x])) 2
  have hm : ∀ k, Measurable fun x ↦ ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 := fun k ↦
    ((measurable_gradient _).sub (measurable_gradient _)).norm.pow_const 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k ↦ setIntegral_nonneg hK.measurableSet fun x _ ↦ sq_nonneg _) fun k ↦ ?_
  have hTc : IsCompact (tsupport η) := hηc.isCompact
  obtain ⟨Mη, hMη⟩ := hTc.exists_bound_of_continuousOn hη.continuous.continuousOn
  have hint : Integrable fun x ↦ ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 * η x :=
    integrable_of_isCompact_of_bound hTc ((hm k).mul hη.continuous.measurable).aestronglyMeasurable
      (fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx]) (C := (2 * L) ^ 2 * Mη)
      fun x hx ↦ by
        rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
        exact mul_le_mul (hbd k x) (hMη x hx) (norm_nonneg _) (sq_nonneg _)
  calc ∫ x in K, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2
      ≤ ∫ x in K, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 * η x :=
        setIntegral_mono_on (integrableOn_of_isCompact_of_norm_le hK (hm k)
          (C := (2 * L) ^ 2) fun x ↦ by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hbd k x)
          hint.integrableOn hK.measurableSet fun x hx ↦
            le_mul_of_one_le_right (sq_nonneg _) (hη1 x hx)
    _ ≤ ∫ x, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2 * η x :=
        setIntegral_le_integral hint (Eventually.of_forall fun x ↦
          mul_nonneg (sq_nonneg _) (hη0 x))

/-! ### Both phases -/

/-- The positive part of a function harmonic on its positivity set is harmonic on its own
positivity set. -/
theorem harmonicOnNhd_max_zero_of_harmonicOnNhd {w : E d → ℝ} (hw : Continuous w)
    (hH : HarmonicOnNhd w {x | 0 < w x}) :
    HarmonicOnNhd (fun x ↦ max (w x) 0) {x | 0 < max (w x) 0} := by
  intro x hx
  have hx' : 0 < w x := by
    rw [mem_ofPred_eq] at hx
    rcases lt_max_iff.1 hx with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  have hloc : (fun y ↦ max (w y) 0) =ᶠ[𝓝 x] w := by
    filter_upwards [(isOpen_lt continuous_const hw).mem_nhds hx'] with y hy
    exact max_eq_left (le_of_lt hy)
  exact (harmonicAt_congr_nhds hloc).2 (hH x hx')

/-- **`∇f = ∇f⁺ - ∇f⁻` a.e.** for Lipschitz `f`, with `f⁺ = max(f, 0)` and `f⁻ = max(-f, 0)`.
Off `{f = 0}` this is local; on `{f = 0}` all three gradients vanish a.e. (Stampacchia,
`HasWeakGradient.ae_eq_zero_of_eq_zero`). -/
theorem ae_gradient_eq_sub_posPart_negPart {f : E d → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    ∀ᵐ x, ∇ f x = ∇ (fun y ↦ max (f y) 0) x - ∇ (fun y ↦ max (-f y) 0) x := by
  have stamp : ∀ (g : E d → ℝ) (K : ℝ≥0), LipschitzWith K g → ∀ᵐ x, g x = 0 → ∇ g x = 0 := by
    intro g K hg
    have hW := (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hg.locallyLipschitz.locallyLipschitzOn).1
    have := hW.ae_eq_zero_of_eq_zero isOpen_univ
    rwa [Measure.restrict_univ] at this
  have hcongr : ∀ {g h : E d → ℝ} {x : E d}, g =ᶠ[𝓝 x] h → ∇ g x = ∇ h x := fun h ↦ by
    rw [gradient, gradient, h.fderiv_eq]
  have hzero : ∀ {g : E d → ℝ} {x : E d}, g =ᶠ[𝓝 x] (fun _ ↦ 0) → ∇ g x = 0 := fun h ↦ by
    rw [hcongr h, gradient, fderiv_const_apply, map_zero]
  filter_upwards [stamp f L hf, stamp _ L (hf.max_const 0), stamp _ L (hf.neg.max_const 0)]
    with x h1 h2 h3
  rcases lt_trichotomy (f x) 0 with hlt | heq | hgt
  · have hU : ∀ᶠ y in 𝓝 x, f y < 0 := (isOpen_lt hf.continuous continuous_const).mem_nhds hlt
    have ep : (fun y ↦ max (f y) 0) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hU] with y hy; exact max_eq_right hy.le
    have en : (fun y ↦ max (-f y) 0) =ᶠ[𝓝 x] fun y ↦ -f y := by
      filter_upwards [hU] with y hy; exact max_eq_left (by linarith)
    rw [hzero ep, hcongr en, gradient, gradient, fderiv_fun_neg, map_neg, zero_sub, neg_neg]
  · have h3' : ∇ (fun y ↦ max (-f y) 0) x = 0 := h3 (by simp [heq])
    rw [h1 heq, h2 (by simp [heq]), h3', sub_zero]
  · have hU : ∀ᶠ y in 𝓝 x, 0 < f y := (isOpen_lt continuous_const hf.continuous).mem_nhds hgt
    have ep : (fun y ↦ max (f y) 0) =ᶠ[𝓝 x] f := by
      filter_upwards [hU] with y hy; exact max_eq_left hy.le
    have en : (fun y ↦ max (-f y) 0) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hU] with y hy; exact max_eq_right (by linarith)
    rw [hcongr ep, hzero en, sub_zero]

/-- **Strong convergence of the gradients.** Let `f k` be `L`-Lipschitz,
harmonic on `{f k > 0}` and on `{f k < 0}`, with `f k → f₀` locally uniformly. Then for every
compact `K`, `∫_K |∇f_k - ∇f₀|² → 0`, and the same holds for the positive parts
`f_k⁺ = max(f_k, 0)` and the negative parts `f_k⁻ = max(-f_k, 0)`. The whole sequence
converges, not only a subsequence, since every subsequence has a further convergent
subsequence. -/
theorem tendsto_setIntegral_norm_sq_gradient_sub {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hpos : ∀ k, HarmonicOnNhd (f k) {x | 0 < f k x})
    (hneg : ∀ k, HarmonicOnNhd (f k) {x | f k x < 0})
    (hconv : TendstoLocallyUniformly f f₀ atTop) {K : Set (E d)} (hK : IsCompact K) :
    Tendsto (fun k ↦ ∫ x in K, ‖∇ (f k) x - ∇ f₀ x‖ ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun k ↦ ∫ x in K,
      ‖∇ (fun y ↦ max (f k y) 0) x - ∇ (fun y ↦ max (f₀ y) 0) x‖ ^ 2) atTop (𝓝 0) ∧
    Tendsto (fun k ↦ ∫ x in K,
      ‖∇ (fun y ↦ max (-f k y) 0) x - ∇ (fun y ↦ max (-f₀ y) 0) x‖ ^ 2) atTop (𝓝 0) := by
  have hf₀ := lipschitzWith_of_tendstoLocallyUniformly hf hconv
  have hmax : UniformContinuous fun t : ℝ ↦ max t 0 :=
    (LipschitzWith.id.max_const 0).uniformContinuous
  have hP := tendsto_setIntegral_norm_sq_gradient_sub_of_nonneg (w := fun k y ↦ max (f k y) 0)
    (w₀ := fun y ↦ max (f₀ y) 0) (fun k ↦ (hf k).max_const 0) (fun _ _ ↦ le_max_right _ _)
    (fun k ↦ harmonicOnNhd_max_zero_of_harmonicOnNhd (hf k).continuous (hpos k))
    (hmax.comp_tendstoLocallyUniformly hconv) hK
  have hN := tendsto_setIntegral_norm_sq_gradient_sub_of_nonneg (w := fun k y ↦ max (-f k y) 0)
    (w₀ := fun y ↦ max (-f₀ y) 0) (fun k ↦ (hf k).neg.max_const 0) (fun _ _ ↦ le_max_right _ _)
    (fun k ↦ harmonicOnNhd_max_zero_of_harmonicOnNhd (w := -f k) (hf k).continuous.neg
      fun x hx ↦ (hneg k x (show f k x < 0 by simpa using hx)).neg)
    (hmax.comp_tendstoLocallyUniformly hconv.neg) hK
  refine ⟨?_, hP, hN⟩
  -- `|∇f_k - ∇f₀|² ≤ 2 |∇f_k⁺ - ∇f₀⁺|² + 2 |∇f_k⁻ - ∇f₀⁻|²` a.e.
  have hae : ∀ᵐ x, ∀ k, ‖∇ (f k) x - ∇ f₀ x‖ ^ 2 ≤
      2 * ‖∇ (fun y ↦ max (f k y) 0) x - ∇ (fun y ↦ max (f₀ y) 0) x‖ ^ 2 +
        2 * ‖∇ (fun y ↦ max (-f k y) 0) x - ∇ (fun y ↦ max (-f₀ y) 0) x‖ ^ 2 := by
    filter_upwards [ae_all_iff.2 fun k ↦ ae_gradient_eq_sub_posPart_negPart (hf k),
      ae_gradient_eq_sub_posPart_negPart hf₀] with x hx hx₀ k
    rw [hx k, hx₀]
    set a := ∇ (fun y ↦ max (f k y) 0) x - ∇ (fun y ↦ max (f₀ y) 0) x
    set b := ∇ (fun y ↦ max (-f k y) 0) x - ∇ (fun y ↦ max (-f₀ y) 0) x
    have e : ∇ (fun y ↦ max (f k y) 0) x - ∇ (fun y ↦ max (-f k y) 0) x -
        (∇ (fun y ↦ max (f₀ y) 0) x - ∇ (fun y ↦ max (-f₀ y) 0) x) = a - b := by
      simp only [a, b]; abel
    rw [e]
    have h1 := norm_sub_le a b
    nlinarith [norm_nonneg (a - b), norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]
  have hgL : ∀ (g : E d → ℝ) (K' : ℝ≥0), LipschitzWith K' g → ∀ x, ‖∇ g x‖ ≤ K' :=
    fun g K' hg x ↦ norm_gradient_le_of_lipschitzWith hg x
  have hint : ∀ (g h : E d → ℝ) (K' : ℝ≥0), LipschitzWith K' g → LipschitzWith K' h →
      IntegrableOn (fun x ↦ ‖∇ g x - ∇ h x‖ ^ 2) K := fun g h K' hg hh ↦
    integrableOn_of_isCompact_of_norm_le hK
      (((measurable_gradient g).sub (measurable_gradient h)).norm.pow_const 2)
      (C := (2 * K') ^ 2) fun x ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by
          linarith [hgL g K' hg x, hgL h K' hh x])) 2
  have hlim := (hP.const_mul 2).add (hN.const_mul 2)
  rw [mul_zero, add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k ↦ setIntegral_nonneg hK.measurableSet fun x _ ↦ sq_nonneg _) fun k ↦ ?_
  have hiP := (hint _ _ L ((hf k).max_const 0) (hf₀.max_const 0)).const_mul 2
  have hiN := (hint _ _ L ((hf k).neg.max_const 0) (hf₀.neg.max_const 0)).const_mul 2
  refine (setIntegral_mono_ae_restrict (hint _ _ L (hf k) hf₀) (hiP.add hiN)
    (ae_restrict_of_ae (hae.mono fun x hx ↦ hx k))).trans (le_of_eq ?_)
  rw [integral_add' hiP hiN, integral_const_mul, integral_const_mul]
  rfl

/-! ### Consequences: a.e. convergence along subsequences, dominated convergence -/

/-- **Strong `L²(K)` convergence gives a.e. convergence along a subsequence.** If bounded
measurable `g k` satisfy `∫_K |g_k - g₀|² → 0`, then `g_{n_k} → g₀` a.e. on `K` along some
subsequence (via convergence in measure). -/
theorem exists_subseq_ae_tendsto_of_tendsto_setIntegral {g : ℕ → E d → E d} {g₀ : E d → E d}
    {K : Set (E d)} (hK : IsCompact K) (hg : ∀ k, Measurable (g k)) (hg₀ : Measurable g₀)
    {C : ℝ} (hC : ∀ k x, ‖g k x - g₀ x‖ ≤ C)
    (h : Tendsto (fun k ↦ ∫ x in K, ‖g k x - g₀ x‖ ^ 2) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂volume.restrict K, Tendsto (fun k ↦ g (ns k) x) atTop (𝓝 (g₀ x)) := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hmem : ∀ k, MemLp (g k - g₀) 2 (volume.restrict K) := fun k ↦
    MemLp.of_bound ((hg k).sub hg₀).aestronglyMeasurable C (Eventually.of_forall (hC k))
  have hL : Tendsto (fun k ↦ eLpNorm (g k - g₀) 2 (volume.restrict K)) atTop (𝓝 0) := by
    have e : ∀ k, eLpNorm (g k - g₀) 2 (volume.restrict K) =
        ENNReal.ofReal ((∫ x in K, ‖g k x - g₀ x‖ ^ 2) ^ (2 : ℝ)⁻¹) := fun k ↦ by
      rw [(hmem k).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
      simp [ENNReal.toReal_ofNat]
    simp_rw [e]
    have h2 := h.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
    rw [Real.zero_rpow (by norm_num)] at h2
    simpa using ENNReal.tendsto_ofReal h2
  exact (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hL).exists_seq_tendsto_ae

/-- **Dominated convergence along subsequences.** If `|F k| ≤ bound` with `bound` integrable,
and every subsequence of `F k` has a further subsequence converging a.e. to `F₀`, then
`∫ F k → ∫ F₀`. -/
theorem tendsto_integral_of_forall_subseq_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : ℕ → α → ℝ} {F₀ : α → ℝ} {bound : α → ℝ} (hFm : ∀ k, AEStronglyMeasurable (F k) μ)
    (hbound : Integrable bound μ) (hle : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ bound x)
    (hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      ∀ᵐ x ∂μ, Tendsto (fun k ↦ F (ns (ms k)) x) atTop (𝓝 (F₀ x))) :
    Tendsto (fun k ↦ ∫ x, F k x ∂μ) atTop (𝓝 (∫ x, F₀ x ∂μ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
  obtain ⟨ms, hms⟩ := hsub ns hns
  exact ⟨ms, tendsto_integral_of_dominated_convergence (F := fun k ↦ F (ns (ms k))) bound
    (fun k ↦ hFm (ns (ms k))) hbound (fun k ↦ hle (ns (ms k))) hms⟩

/-- **A.e. convergence of gradients along subsequences.** If `∫_K |∇f_k - ∇f₀|² → 0` for
`L`-Lipschitz `f k` and `f₀`, then every subsequence `f_{n_k}` has a further subsequence along
which `∇f → ∇f₀` a.e. on `K`. -/
theorem exists_subseq_ae_tendsto_gradient {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hf₀ : LipschitzWith L f₀) {K : Set (E d)}
    (hK : IsCompact K) (h : Tendsto (fun k ↦ ∫ x in K, ‖∇ (f k) x - ∇ f₀ x‖ ^ 2) atTop (𝓝 0))
    {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      ∀ᵐ x ∂volume.restrict K, Tendsto (fun k ↦ ∇ (f (ns (ms k))) x) atTop (𝓝 (∇ f₀ x)) :=
  exists_subseq_ae_tendsto_of_tendsto_setIntegral (g := fun k ↦ ∇ (f (ns k))) (g₀ := ∇ f₀) hK
    (fun _ ↦ measurable_gradient _) (measurable_gradient _) (C := 2 * L)
    (fun k x ↦ (norm_sub_le _ _).trans (by
      linarith [norm_gradient_le_of_lipschitzWith (hf (ns k)) x,
        norm_gradient_le_of_lipschitzWith hf₀ x])) (h.comp hns)

end EllipticBernoulli
