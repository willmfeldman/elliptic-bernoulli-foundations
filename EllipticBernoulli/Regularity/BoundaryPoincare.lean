/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.DeGiorgi
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A boundary Poincaré inequality

Let `B = B_r(x₀)`, `z ∈ ∂B`, and let `g ≥ 0` have a weak gradient `G` near `B̄_ρ(z)` and vanish on
`B_ρ(z) \ B`. Then (`integral_le_boundary_poincare`)
`∫_{B_{ρ/8}(z)} g ≤ (ρ/4) ∫_{B_{ρ/2}(z)} |G|`.

Proof by duality, which needs neither the ACL characterization of Sobolev functions nor a shifted
mollification. Let `ν = (z - x₀)/r` be the outer normal, `T = ρ/4`, and `ψ` a smooth cutoff with
`ψ = 1` on `B_{ρ/8}(z)` and support in `B_{ρ/4}(z)`. The function
`h(s) = ∫ g(x) ψ(x - sν) dx` has derivative `h'(s) = ∫ ⟨G, ν⟩ ψ(x - sν) dx` (differentiation
under the integral sign, then the weak-gradient identity), so `|h'| ≤ ∫_{B_{ρ/2}} |G|` on `[0, T]`.
Moreover `h(T) = 0`, since `ψ(· - Tν)` is supported in `B_{ρ/2}(z) \ B` (convexity of `B`), and
`h(0) ≥ ∫_{B_{ρ/8}} g`. The mean value inequality concludes.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient RealInnerProductSpace

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- Geometry: if `z ∈ ∂B_r(x₀)`, `ν = (z - x₀)/r` and `T > 0`, then `B_T(z + Tν)` lies outside
`B_r(x₀)`. -/
theorem notMem_ball_of_shift {x₀ z x : E d} {r T : ℝ} (hr : 0 < r) (hz : dist z x₀ = r)
    (hx : dist (x - T • (r⁻¹ • (z - x₀))) z < T) : x ∉ ball x₀ r := by
  set ν : E d := r⁻¹ • (z - x₀) with hν
  have hzx : ‖z - x₀‖ = r := by rw [← dist_eq_norm]; exact hz
  have hν1 : ‖ν‖ = 1 := by
    rw [hν, norm_smul, hzx, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  have hzν : z - x₀ = r • ν := by rw [hν, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  set e : E d := x - T • ν - z with he
  have hen : ‖e‖ < T := by rw [he, ← dist_eq_norm]; exact hx
  have hxe : x - x₀ = (r + T) • ν + e := by
    rw [he, add_smul, ← hzν]; abel
  have hinner : ⟪x - x₀, ν⟫ = r + T + ⟪e, ν⟫ := by
    rw [hxe, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, hν1]
    simp
  have he1 : -‖e‖ ≤ ⟪e, ν⟫ := by
    have := abs_real_inner_le_norm e ν
    rw [hν1, mul_one] at this
    exact (abs_le.1 this).1
  have hle : ⟪x - x₀, ν⟫ ≤ ‖x - x₀‖ := by
    have := real_inner_le_norm (x - x₀) ν
    rwa [hν1, mul_one] at this
  intro hmem
  rw [mem_ball, dist_eq_norm] at hmem
  linarith

/-- **Boundary Poincaré inequality.** Let `z ∈ ∂B_r(x₀)`, `B̄_ρ(z) ⊆ U`, and let `g` have weak
gradient `G` in `U`, with `g ≥ 0` on `B̄_ρ(z)` and `g = 0` on `B_ρ(z) \ B_r(x₀)`. Then
`∫_{B_{ρ/8}(z)} g ≤ (ρ/4) ∫_{B_{ρ/2}(z)} |G|`. -/
theorem integral_le_boundary_poincare {U : Set (E d)} {g : E d → ℝ} {G : E d → E d}
    (hw : HasWeakGradient U g G) {x₀ z : E d} {r ρ : ℝ} (hr : 0 < r) (hz : dist z x₀ = r)
    (hρ : 0 < ρ) (hzU : closedBall z ρ ⊆ U) (hgnn : ∀ x ∈ closedBall z ρ, 0 ≤ g x)
    (hg0 : ∀ x ∈ ball z ρ, x ∉ ball x₀ r → g x = 0) :
    ∫ x in ball z (ρ / 8), g x ≤ ρ / 4 * ∫ x in ball z (ρ / 2), ‖G x‖ := by
  obtain ⟨ψ, hψ, hψ01, hψ1, hψ0, hψc, hψt, hψg⟩ :=
    exists_cutoff z (by positivity : 0 ≤ ρ / 8) (by linarith : ρ / 8 < ρ / 4)
  set ν : E d := r⁻¹ • (z - x₀) with hν
  have hzx : ‖z - x₀‖ = r := by rw [← dist_eq_norm]; exact hz
  have hν1 : ‖ν‖ = 1 := by
    rw [hν, norm_smul, hzx, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_cancel₀ hr.ne']
  set Cψ : ℝ := cutoffConst / (ρ / 4 - ρ / 8) with hCψ
  have hCψ0 : 0 ≤ Cψ := by have := cutoffConst_pos; rw [hCψ]; apply div_nonneg this.le; linarith
  have hfd : ∀ y, ‖fderiv ℝ ψ y‖ ≤ Cψ := fun y ↦ by rw [← norm_gradient_eq_norm_fderiv]; exact hψg y
  set K := closedBall z ρ with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hgK : IntegrableOn g K := hw.1.integrableOn_compact_subset hzU hKc
  have hGU : LocallyIntegrableOn G U := hw.2.1
  have hGb : IntegrableOn G (ball z (ρ / 2)) :=
    (hGU.integrableOn_compact_subset hzU hKc).mono_set
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)))
  have hψcont : Continuous ψ := hψ.continuous
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hfdc : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  -- the function `h`
  set F : ℝ → E d → ℝ := fun s x ↦ g x * ψ (x - s • ν) with hF
  set F' : ℝ → E d → ℝ := fun s x ↦ g x * fderiv ℝ ψ (x - s • ν) (-ν) with hF'
  set h : ℝ → ℝ := fun s ↦ ∫ x in K, F s x with hh
  set h' : ℝ → ℝ := fun s ↦ ∫ x in K, F' s x with hh'
  have hderivF : ∀ s x, HasDerivAt (fun s ↦ F s x) (F' s x) s := by
    intro s x
    have h1 : HasDerivAt (fun s : ℝ ↦ x - s • ν) (-ν) s := by
      simpa using ((hasDerivAt_id s).smul_const ν).const_sub x
    have h2 := (hψd (x - s • ν)).hasFDerivAt.comp_hasDerivAt s h1
    exact h2.const_mul (g x)
  have hmeasF : ∀ s, AEStronglyMeasurable (F s) (volume.restrict K) := fun s ↦
    hgK.1.mul (hψcont.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hmeasF' : ∀ s, AEStronglyMeasurable (F' s) (volume.restrict K) := fun s ↦ by
    refine hgK.1.mul (Continuous.aestronglyMeasurable ?_)
    exact (hfdc.comp (continuous_id.sub continuous_const)).clm_apply continuous_const
  have hintF : ∀ s, IntegrableOn (F s) K := fun s ↦ by
    refine hgK.mul_continuousOn_of_subset
      (hψcont.comp (continuous_id.sub continuous_const)).continuousOn
      measurableSet_closedBall hKc subset_rfl
  have hderiv : ∀ s, HasDerivAt h (h' s) s := by
    intro s
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
      (bound := fun x ↦ ‖g x‖ * Cψ)
      univ_mem (Eventually.of_forall hmeasF) (hintF s) (hmeasF' s)
      (ae_of_all _ fun x t _ ↦ ?_) (hgK.norm.mul_const Cψ)
      (ae_of_all _ fun x t _ ↦ hderivF t x)).2
    simp only [hF', norm_mul]
    refine mul_le_mul_of_nonneg_left (((fderiv ℝ ψ (x - t • ν)).le_opNorm _).trans ?_)
      (norm_nonneg _)
    rw [norm_neg, hν1, mul_one]
    exact hfd _
  -- the value of `h'` on `[0, T]`
  have hshift : ∀ s ∈ Icc 0 (ρ / 4), ∀ x, x - s • ν ∈ ball z (ρ / 4) → x ∈ ball z (ρ / 2) := by
    intro s hs x h1
    rw [mem_ball] at h1 ⊢
    have : dist x (x - s • ν) = s := by
      rw [dist_eq_norm, sub_sub_cancel, norm_smul, hν1, mul_one, Real.norm_eq_abs,
        abs_of_nonneg hs.1]
    have := dist_triangle x (x - s • ν) z
    linarith [hs.2]
  have hsupp : ∀ s ∈ Icc 0 (ρ / 4), ∀ x, ψ (x - s • ν) ≠ 0 → x ∈ ball z (ρ / 2) := by
    intro s hs x hx
    refine hshift s hs x ?_
    by_contra h'
    exact hx (hψ0 _ h').1
  have hbound : ∀ s ∈ Icc 0 (ρ / 4), ‖h' s‖ ≤ ∫ x in ball z (ρ / 2), ‖G x‖ := by
    intro s hs
    set φ : E d → ℝ := fun x ↦ ψ (x - s • ν) with hφ
    have hφs : ContDiff ℝ ∞ φ := hψ.comp (contDiff_id.sub contDiff_const)
    have hφsupp : Function.support φ ⊆ ball z (ρ / 2) := fun x hx ↦ hsupp s hs x hx
    have hφt : tsupport φ ⊆ closedBall z (ρ / 2) :=
      closure_minimal (hφsupp.trans ball_subset_closedBall) isClosed_closedBall
    have hφc : HasCompactSupport φ :=
      HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall z (ρ / 2))
        (hφsupp.trans ball_subset_closedBall)
    have hφU : tsupport φ ⊆ U := hφt.trans ((closedBall_subset_closedBall (by linarith)).trans hzU)
    have hweak := hw.integral_eq hφs hφc hφU ν
    have hfdφ : ∀ x, fderiv ℝ φ x = fderiv ℝ ψ (x - s • ν) := fun x ↦ by
      simp only [hφ, sub_eq_add_neg]
      exact fderiv_comp_add_right _
    have hKsub : closedBall z (ρ / 2) ⊆ K := closedBall_subset_closedBall (by linarith)
    have e1 : h' s = -∫ x, g x * fderiv ℝ φ x ν := by
      rw [hh', ← integral_neg]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ ?_) |>.trans ?_
      · have hnt : x - s • ν ∉ tsupport ψ := fun hmem ↦
          hx (hKsub (ball_subset_closedBall (hshift s hs x (hψt hmem))))
        simp [hF', fderiv_apply_eq_zero_of_notMem_tsupport hnt]
      · refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        simp only [hF', hfdφ, map_neg, mul_neg]
    rw [e1, hweak, neg_neg]
    calc ‖∫ x, ⟪G x, ν⟫ * φ x‖
        ≤ ∫ x, (ball z (ρ / 2)).indicator (fun x ↦ ‖G x‖) x := by
          refine norm_integral_le_of_norm_le
            (IntegrableOn.integrable_indicator (Integrable.norm hGb) measurableSet_ball)
            (ae_of_all _ fun x ↦ ?_)
          by_cases hx : x ∈ ball z (ρ / 2)
          · rw [indicator_of_mem hx, norm_mul]
            have h1 : ‖⟪G x, ν⟫‖ ≤ ‖G x‖ := by
              have := norm_inner_le_norm (𝕜 := ℝ) (G x) ν
              rwa [hν1, mul_one] at this
            have h2 : ‖φ x‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_of_nonneg (hψ01 _).1]; exact (hψ01 _).2
            calc ‖⟪G x, ν⟫‖ * ‖φ x‖ ≤ ‖G x‖ * 1 := mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
              _ = ‖G x‖ := mul_one _
          · have : φ x = 0 := by
              by_contra hne; exact hx (hφsupp hne)
            rw [indicator_of_notMem hx, this, mul_zero, norm_zero]
      _ = ∫ x in ball z (ρ / 2), ‖G x‖ := integral_indicator measurableSet_ball
  -- `h (ρ / 4) = 0`
  have hT0 : h (ρ / 4) = 0 := by
    have : ∀ x, F (ρ / 4) x = 0 := by
      intro x
      by_cases hx : ψ (x - (ρ / 4) • ν) = 0
      · simp [hF, hx]
      · have hxb := hsupp (ρ / 4) ⟨by positivity, le_rfl⟩ x hx
        have h1 : x - (ρ / 4) • ν ∈ ball z (ρ / 4) := by
          by_contra h'
          exact hx (hψ0 _ h').1
        have hnot := notMem_ball_of_shift (T := ρ / 4) hr hz (by rw [← mem_ball]; exact h1)
        simp [hF, hg0 x (ball_subset_ball (by linarith) hxb) hnot]
    simp [hh, this]
  -- `h 0 ≥ ∫_{B_{ρ/8}} g`
  have h0 : ∫ x in ball z (ρ / 8), g x ≤ h 0 := by
    have hsub : ball z (ρ / 8) ⊆ K := ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith))
    calc ∫ x in ball z (ρ / 8), g x = ∫ x in ball z (ρ / 8), F 0 x :=
          setIntegral_congr_fun measurableSet_ball fun x hx ↦ by
            simp [hF, hψ1 x (ball_subset_closedBall hx)]
      _ ≤ ∫ x in K, F 0 x := by
          refine setIntegral_mono_set (hintF 0) ?_ hsub.eventuallyLE
          refine (ae_restrict_iff' measurableSet_closedBall).2 (Eventually.of_forall fun x hx ↦ ?_)
          exact mul_nonneg (hgnn x hx) (hψ01 _).1
  -- mean value inequality
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := h) (a := 0) (b := ρ / 4)
    (fun s _ ↦ (hderiv s).hasDerivWithinAt) (fun s hs ↦ hbound s (Ico_subset_Icc_self hs))
    (ρ / 4) ⟨by positivity, le_rfl⟩
  rw [hT0, zero_sub, norm_neg, sub_zero] at hmv
  calc ∫ x in ball z (ρ / 8), g x ≤ h 0 := h0
    _ ≤ ‖h 0‖ := le_abs_self _
    _ ≤ (∫ x in ball z (ρ / 2), ‖G x‖) * (ρ / 4) := hmv
    _ = ρ / 4 * ∫ x in ball z (ρ / 2), ‖G x‖ := by ring

end EllipticBernoulli
