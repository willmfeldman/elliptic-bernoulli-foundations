/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Setting
public import EllipticBernoulli.Common.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Smooth cutoff functions with gradient bounds

`exists_cutoff`: there is a universal constant `C` such that for every ball `B_t(z)` and every
`0 ≤ s < t` there is a smooth `η` with `0 ≤ η ≤ 1`, `η = 1` on `closedBall z s`, `η = 0` (with
zero gradient) off `ball z t`, and `‖∇η‖ ≤ C / (t - s)`.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The derivative of `Real.smoothTransition` is bounded. -/
theorem exists_bound_deriv_smoothTransition :
    ∃ C > 0, ∀ x, |deriv Real.smoothTransition x| ≤ C := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hcs : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx ↦ ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ 0 :=
        (gt_mem_nhds hx).mono fun y hy ↦ Real.smoothTransition.zero_of_nonpos hy.le
      rw [this.deriv_eq, deriv_const]
    · have : Real.smoothTransition =ᶠ[𝓝 x] fun _ ↦ 1 :=
        (lt_mem_nhds hx).mono fun y hy ↦ Real.smoothTransition.one_of_one_le hy.le
      rw [this.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨max C 1, by positivity, fun x ↦ (Real.norm_eq_abs _ ▸ hC x).trans (le_max_left _ _)⟩

private theorem gradient_eq_zero_of_notMem_tsupport' {η : E d → ℝ} {x : E d} (hx : x ∉ tsupport η) :
    ∇ η x = 0 := by
  have : fderiv ℝ η x = 0 := Function.notMem_support.1 fun h ↦ hx (support_fderiv_subset ℝ h)
  simp [gradient, this]

/-- The universal constant of the cutoff functions of `exists_cutoff`. -/
noncomputable def cutoffConst : ℝ := 8 * Classical.choose exists_bound_deriv_smoothTransition

theorem cutoffConst_pos : 0 < cutoffConst :=
  mul_pos (by norm_num) (Classical.choose_spec exists_bound_deriv_smoothTransition).1

/-- **Smooth cutoff functions.** For `0 ≤ s < t` there is a smooth `η`, `0 ≤ η ≤ 1`, `η = 1` on
`closedBall z s`, `η = 0` with `∇η = 0` off `ball z t`, and `‖∇η‖ ≤ cutoffConst / (t - s)`. -/
theorem exists_cutoff (z : E d) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ∃ η : E d → ℝ, ContDiff ℝ ∞ η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x ∈ closedBall z s, η x = 1) ∧ (∀ x ∉ ball z t, η x = 0 ∧ ∇ η x = 0) ∧
      HasCompactSupport η ∧ tsupport η ⊆ ball z t ∧ ∀ x, ‖∇ η x‖ ≤ cutoffConst / (t - s) := by
  obtain ⟨hC₀, hC₀b⟩ := Classical.choose_spec exists_bound_deriv_smoothTransition
  set C₀ := Classical.choose exists_bound_deriv_smoothTransition with hC₀def
  rw [cutoffConst, ← hC₀def]
  set m : ℝ := (s + t) / 2 with hm
  set a : ℝ := s ^ 2 with ha
  set b : ℝ := m ^ 2 with hb
  have hsm : s < m := by rw [hm]; linarith
  have hmt : m < t := by rw [hm]; linarith
  have hab : 0 < b - a := by
    rw [ha, hb]; nlinarith
  set q : E d → ℝ := fun x ↦ (b - ‖x - z‖ ^ 2) / (b - a) with hq
  set η : E d → ℝ := fun x ↦ Real.smoothTransition (q x) with hη
  have hqc : ContDiff ℝ ∞ q := by
    have h1 : ContDiff ℝ ∞ (fun x : E d ↦ ‖x - z‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact (contDiff_const.sub h1).div_const _
  have hηc : ContDiff ℝ ∞ η := (Real.smoothTransition.contDiff (n := ⊤)).comp hqc
  have hzero : ∀ x, m ≤ ‖x - z‖ → η x = 0 := by
    intro x hx
    refine Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg ?_ hab.le)
    have : b ≤ ‖x - z‖ ^ 2 := by
      rw [hb]; exact pow_le_pow_left₀ (by linarith) hx 2
    linarith
  have htsupp : tsupport η ⊆ closedBall z m := by
    refine closure_minimal (fun x hx ↦ ?_) isClosed_closedBall
    rw [mem_closedBall, dist_eq_norm]
    by_contra h
    exact hx (hzero x (not_le.1 h).le)
  have htsupp' : tsupport η ⊆ ball z t :=
    htsupp.trans (closedBall_subset_ball hmt)
  refine ⟨η, hηc, fun x ↦ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩,
    fun x hx ↦ ?_, fun x hx ↦ ?_, ?_, htsupp', fun x ↦ ?_⟩
  · refine Real.smoothTransition.one_of_one_le ?_
    rw [one_le_div hab]
    have : ‖x - z‖ ^ 2 ≤ a := by
      rw [ha]
      exact pow_le_pow_left₀ (norm_nonneg _) (by rwa [mem_closedBall, dist_eq_norm] at hx) 2
    linarith
  · have hxt : x ∉ tsupport η := fun h ↦ hx (htsupp' h)
    exact ⟨image_eq_zero_of_notMem_tsupport hxt, gradient_eq_zero_of_notMem_tsupport' hxt⟩
  · exact (isCompact_closedBall z m).of_isClosed_subset (isClosed_tsupport _) htsupp
  · by_cases hx : x ∈ ball z t
    · rw [norm_gradient_eq_norm_fderiv]
      have hd1 := ((hasFDerivAt_id x).sub_const z).norm_sq
      set L : E d →L[ℝ] ℝ := 2 • (innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ (E d))
        with hL
      have hd2 : HasFDerivAt q ((b - a)⁻¹ • -L) x := by
        have := (hd1.const_sub b).const_mul (b - a)⁻¹
        refine this.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
        simp only [hq, div_eq_inv_mul, id]
      have hd3 : HasFDerivAt η (deriv Real.smoothTransition (q x) • ((b - a)⁻¹ • -L)) x :=
        ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero (q x)).hasDerivAt
          |>.comp_hasFDerivAt x hd2
      rw [hd3.fderiv, norm_smul, norm_smul, norm_neg]
      have hnorm : ‖(innerSL ℝ (x - z)).comp (ContinuousLinearMap.id ℝ (E d))‖ ≤ ‖x - z‖ := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [innerSL_apply_norm]
        exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
      have hxz : ‖x - z‖ < t := by rwa [mem_ball, dist_eq_norm] at hx
      have hLb : ‖L‖ ≤ 2 * t := by
        rw [hL]
        refine norm_nsmul_le.trans ?_
        push_cast
        linarith
      have hba : (t - s) * t ≤ 4 * (b - a) := by
        rw [hb, ha, hm]; linarith [mul_nonneg (sub_nonneg.2 hst.le) hs]
      have h1 : ‖deriv Real.smoothTransition (q x)‖ ≤ C₀ := by
        rw [Real.norm_eq_abs]; exact hC₀b _
      have h2 : ‖(b - a)⁻¹‖ = (b - a)⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hab)]
      rw [h2]
      have hts : 0 < t - s := by linarith
      have ht0 : 0 < t := by linarith
      calc ‖deriv Real.smoothTransition (q x)‖ * ((b - a)⁻¹ * ‖L‖)
          ≤ C₀ * ((b - a)⁻¹ * (2 * t)) :=
            mul_le_mul h1 (mul_le_mul_of_nonneg_left hLb (inv_nonneg.2 hab.le))
              (mul_nonneg (inv_nonneg.2 hab.le) (norm_nonneg _)) hC₀.le
        _ = 2 * C₀ * t / (b - a) := by field_simp
        _ ≤ 8 * C₀ / (t - s) := by
            rw [div_le_div_iff₀ hab hts]
            linarith [mul_le_mul_of_nonneg_left hba (by positivity : (0 : ℝ) ≤ 2 * C₀)]
    · rw [(show ∇ η x = 0 from gradient_eq_zero_of_notMem_tsupport' fun h ↦ hx (htsupp' h)),
        norm_zero]
      have : 0 < t - s := by linarith
      positivity

end EllipticBernoulli
