/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Equation
public import EllipticBernoulli.Hodograph.Flat
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The hodograph transform on a half ball of fixed size

`IsFlatChartData.exists_hodograph_of_le` is `IsFlatChartData.exists_hodograph` with a quantitative
input. If `‖gradVec e (G y) - e‖ ≤ η` on `closure {u > 0} ∩ B_ρ(x₀)`, then the conclusions hold on
the half ball of the fixed radius `ρ / 32`, with `‖∇w - e‖ ≤ η`. In `exists_hodograph` the radius
comes from the continuity of `G` at `x₀`, so it is not uniform.

`norm_gradVec_sub_le`: `‖gradVec e p - e‖ ≤ 4 ‖p - e‖` for `‖p - e‖ ≤ 1/4`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

public section

namespace EllipticBernoulli

open Hodograph

variable {d : ℕ} {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d} {ρ : ℝ} {G : E d → E d}

/-- `gradVec` is Lipschitz near `e`: `‖gradVec e p - e‖ ≤ 4 ‖p - e‖` for `‖p - e‖ ≤ 1/4`. -/
theorem Hodograph.norm_gradVec_sub_le (he : ‖e‖ = 1) {p : E d} (hp : ‖p - e‖ ≤ 1 / 4) :
    ‖gradVec e p - e‖ ≤ 4 * ‖p - e‖ := by
  set t := ⟪p, e⟫ with ht
  set δ := ‖p - e‖ with hδ
  have hpe : |t - 1| ≤ δ := by
    have h1 : t - 1 = ⟪p - e, e⟫ := by rw [inner_sub_left, inner_self_of_norm he]
    rw [h1]
    have := abs_real_inner_le_norm (p - e) e
    rwa [he, mul_one] at this
  have ht34 : 3 / 4 ≤ t := by linarith [(abs_le.1 hpe).1]
  have ht0 : t ≠ 0 := by linarith
  have hP : perpProj e p = perpProj e (p - e) := by
    rw [perpProj, perpProj, inner_sub_left, inner_self_of_norm he, sub_smul, one_smul]; abel
  have hPn : ‖perpProj e p‖ ≤ δ := by rw [hP]; exact norm_perpProj_le he _
  have heq : gradVec e p - e = t⁻¹ • ((1 - t) • e - perpProj e p) := by
    rw [gradVec, ← ht, smul_sub, smul_sub, smul_smul, mul_sub, mul_one, inv_mul_cancel₀ ht0,
      sub_smul, one_smul]
    abel
  rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith : (0 : ℝ) < t)]
  have hn : ‖(1 - t) • e - perpProj e p‖ ≤ 2 * δ := by
    calc ‖(1 - t) • e - perpProj e p‖ ≤ ‖(1 - t) • e‖ + ‖perpProj e p‖ := norm_sub_le _ _
      _ = |t - 1| + ‖perpProj e p‖ := by
          rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_sub_comm]
      _ ≤ 2 * δ := by linarith
  rw [inv_mul_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (p - e)]

namespace IsFlatChartData

variable (H : IsFlatChartData U u x₀ e ρ G)
include H

/-- **The partial hodograph transform on a half ball of fixed size.** -/
theorem exists_hodograph_of_le {η : ℝ}
    (hqη : ∀ y ∈ closure (posSet u U) ∩ ball x₀ ρ, ‖gradVec e (G y) - e‖ ≤ η) :
    ∃ r, r = ρ / 32 ∧ BasicElliptic.halfBall e 0 r ⊆ Adm e ρ ∧
      ContDiffOn ℝ 1 (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) ∧
      ContDiffOn ℝ 2 (hodograph u x₀ e ρ) (ball 0 r ∩ BasicElliptic.openHalfSpace e) ∧
      (∀ z ∈ BasicElliptic.halfBall e 0 r,
        ‖gradientWithin (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) z - e‖ ≤ η) ∧
      (∀ z ∈ ball 0 r ∩ BasicElliptic.openHalfSpace e,
        divergence (fun p ↦ field e (∇ (hodograph u x₀ e ρ) p)) z = 0) ∧
      (∀ z ∈ ball 0 r ∩ BasicElliptic.flatPart e,
        ⟪field e (gradientWithin (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) z), e⟫ = 0) ∧
      hodograph u x₀ e ρ 0 = 0 ∧
      gradientWithin (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) 0 = e := by
  have he := H.norm_e
  have hρ := H.pos
  set w := hodograph u x₀ e ρ with hw
  set q : E d → E d := fun z ↦ gradVec e (G (hodographPt u x₀ e ρ z)) with hq
  have hqc : ContinuousOn q (Adm e ρ) := H.continuousOn_gradVec_G
  have hq0 : q 0 = e := by simp only [hq, H.hodographPt_zero, H.G_x₀, gradVec_self he]
  set r := ρ / 32 with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r ≤ ρ / 32 := le_rfl
  have hHA : BasicElliptic.halfBall e 0 r ⊆ Adm e ρ := halfBall_subset_adm hρ he hrρ
  set S := ball (0 : E d) r ∩ BasicElliptic.openHalfSpace e with hS
  have hSH : S ⊆ BasicElliptic.halfBall e 0 r := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, show 0 ≤ ⟪z, e⟫ from le_of_lt hz.2⟩
  have hSA : S ⊆ Adm e ρ := hSH.trans hHA
  have hinner : Continuous fun z : E d ↦ ⟪z, e⟫ := by fun_prop
  have hSo : IsOpen S := isOpen_ball.inter (isOpen_lt continuous_const hinner)
  have hSc : Convex ℝ S := (convex_ball 0 r).inter (convex_openHalfSpace e)
  have hHcl : BasicElliptic.halfBall e 0 r ⊆ closure S := halfBall_subset_closure he hr0
  have hclH : closure S ⊆ BasicElliptic.halfBall e 0 r :=
    closure_minimal hSH (isClosed_halfBall e r)
  have hG : ∀ z ∈ S, ∇ u (hodographPt u x₀ e ρ z) = G (hodographPt u x₀ e ρ z) := fun z hz ↦
    (H.G_eq _ ⟨H.hodographPt_mem_posSet (hSA hz) hz.2, H.hodographPt_mem_ball (hSA hz)⟩).symm
  have hderS : ∀ z ∈ S, HasFDerivAt w (toDual ℝ (E d) (q z)) z := fun z hz ↦ by
    have := (H.hasFDerivAt_hodograph (hSA hz) hz.2).1
    rwa [hG z hz] at this
  have hwithin : ∀ z ∈ BasicElliptic.halfBall e 0 r,
      HasFDerivWithinAt w (toDual ℝ (E d) (q z)) (BasicElliptic.halfBall e 0 r) z := by
    intro z hz
    have hL : ContinuousWithinAt (fun z ↦ toDual ℝ (E d) (q z)) S z :=
      ((toDual ℝ (E d)).continuous.continuousAt.comp_continuousWithinAt (hqc z (hHA hz))).mono
        hSA
    have hT : Tendsto (fderiv ℝ w) (𝓝[S] z) (𝓝 (toDual ℝ (E d) (q z))) := by
      refine hL.tendsto.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hderS y hy).fderiv.symm
    exact (hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy ↦ (hderS y hy).differentiableAt.differentiableWithinAt) hSc hSo
      (fun y hy ↦ (H.continuousWithinAt_hodograph (hHA (hclH hy))).mono hSA) hT).mono hHcl
  have hcS : (r / 2) • e ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)]
      linarith
    · change 0 < ⟪(r / 2) • e, e⟫
      rw [real_inner_smul_left, inner_self_of_norm he]; linarith
  have huniq : UniqueDiffOn ℝ (BasicElliptic.halfBall e 0 r) :=
    uniqueDiffOn_convex (convex_halfBall e r) ⟨(r / 2) • e, interior_maximal hSH hSo hcS⟩
  have hgw : ∀ z ∈ BasicElliptic.halfBall e 0 r,
      gradientWithin w (BasicElliptic.halfBall e 0 r) z = q z := fun z hz ↦ by
    rw [gradientWithin, (hwithin z hz).fderivWithin (huniq z hz),
      LinearIsometryEquiv.symm_apply_apply]
  refine ⟨r, rfl, hHA, ?_, ?_, ?_, ?_, ?_, H.hodograph_zero, ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn huniq]
    refine ⟨by simp, fun z ↦ toDual ℝ (E d) (q z), ?_, hwithin⟩
    exact contDiffOn_zero.2 ((toDual ℝ (E d)).continuous.comp_continuousOn (hqc.mono hHA))
  · exact fun z hz ↦ (H.hasFDerivAt_hodograph (hSA hz) hz.2).2.contDiffWithinAt
  · intro z hz
    rw [hgw z hz]
    exact hqη _ ⟨H.hodographPt_mem_closure (hHA hz), H.hodographPt_mem_ball (hHA hz)⟩
  · exact fun z hz ↦ H.divergence_field_eq_zero (hSA hz) hz.2
  · intro z hz
    have hzt : ⟪z, e⟫ = 0 := hz.2
    have hzH : z ∈ BasicElliptic.halfBall e 0 r := ⟨ball_subset_closedBall hz.1, hzt.symm.le⟩
    rw [hgw z hzH]
    have hzA := hHA hzH
    have hfb := H.hodographPt_mem_freeBoundary hzA hzt
    have hB := H.hodographPt_mem_ball hzA
    have hne : ⟪G (hodographPt u x₀ e ρ z), e⟫ ≠ 0 := by
      have := H.inner_G _ ⟨H.hodographPt_mem_closure hzA, hB⟩
      exact (by linarith : (0 : ℝ) < _).ne'
    simp only [hq]
    rw [field_gradVec he hne, inner_fieldOf he, H.norm_G _ ⟨hfb, hB⟩]
    norm_num
  · rw [hgw 0 ⟨mem_closedBall_self hr0.le, by simp⟩, hq0]

end IsFlatChartData

end EllipticBernoulli
