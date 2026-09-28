/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Classical
import EllipticBernoulli.Classical.Viscosity
import EllipticBernoulli.Viscosity.Calculus
import EllipticBernoulli.Classical.BlowupExtraction
import EllipticBernoulli.Classical.HalfSpace
import EllipticBernoulli.Harmonic.Basic
import EllipticBernoulli.Harmonic.Limit
import EllipticBernoulli.Classical.OneDim
import EllipticBernoulli.Common.Calculus
import EllipticBernoulli.Flatness.Classical
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Order.IntermediateValue

/-!
# The gradient of a classical solution up to the free boundary

## Main results

* `gradient_eq_smul_of_zero_set`: two regular defining functions of the same hypersurface have
  parallel gradients (Lagrange multipliers).
* `IsClassicalSolution.side`: the restriction `u · 1_{σF > 0}` of a classical solution to one
  side of its smooth free boundary is again a classical solution in a small ball, with
  positivity set `B ∩ {σF > 0}` and free boundary `B ∩ {F = 0}`.

## Proof notes

At a two-sided point (`{u > 0}` on both sides of the free boundary) the gradient of `u` has two
different one-sided limits, so the gradient limit is stated side by side: each side
`u · 1_{σF > 0}` is a one-sided classical solution, to which the flatness route applies.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace NNReal

namespace EllipticBernoulli

variable {d : ℕ}

public section

/-! ### Parallel normals -/

/-- **Parallel normals.** If `F` and `G` are `C¹` near `y` with nonzero gradients, and locally
`{F = F y} ⊆ {G = G y}`, then `∇G(y) = c ∇F(y)` with `c ≠ 0` (Lagrange multipliers: `y` is a
local extremum of `G` on the level set of `F`). -/
theorem gradient_eq_smul_of_zero_set {F G : E d → ℝ} {y : E d} (hF : ContDiffAt ℝ 1 F y)
    (hG : ContDiffAt ℝ 1 G y) (hFn : ∇ F y ≠ 0) (hGn : ∇ G y ≠ 0)
    (hsub : ∀ᶠ z in 𝓝 y, F z = F y → G z = G y) :
    ∃ c : ℝ, c ≠ 0 ∧ ∇ G y = c • ∇ F y := by
  have hmin : IsLocalMinOn G {z | F z = F y} y := by
    filter_upwards [nhdsWithin_le_nhds hsub, self_mem_nhdsWithin] with z hz hzF
    exact (hz hzF).ge
  have hextr : IsLocalExtrOn G {z | F z = F y} y := Or.inl hmin
  obtain ⟨a, b, hab, hlag⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt_1d
    (hF.hasStrictFDerivAt one_ne_zero) (hG.hasStrictFDerivAt one_ne_zero)
  have hlagv : ∀ v, a * ⟪∇ F y, v⟫ + b * ⟪∇ G y, v⟫ = 0 := fun v ↦ by
    have := congrArg (fun L : StrongDual ℝ (E d) ↦ L v) hlag
    simpa [fderiv_apply_eq_inner_gradient] using this
  have hFnorm : 0 < ‖∇ F y‖ := norm_pos_iff.2 hFn
  have hGnorm : 0 < ‖∇ G y‖ := norm_pos_iff.2 hGn
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := fun ha ↦ hab (by simp [ha])
    have := hlagv (∇ F y)
    rw [real_inner_self_eq_norm_sq, zero_mul, add_zero] at this
    rcases mul_eq_zero.1 this with h | h
    · exact ha h
    · exact pow_ne_zero 2 hFnorm.ne' h
  have ha : a ≠ 0 := by
    rintro rfl
    have := hlagv (∇ G y)
    rw [real_inner_self_eq_norm_sq, zero_mul, zero_add] at this
    rcases mul_eq_zero.1 this with h | h
    · exact hb h
    · exact pow_ne_zero 2 hGnorm.ne' h
  refine ⟨-a / b, div_ne_zero (neg_ne_zero.2 ha) hb, ext_inner_right ℝ fun v ↦ ?_⟩
  rw [real_inner_smul_left]
  have := hlagv v
  field_simp
  linarith

/-- With `∇G(y) = c ∇F(y)`, `c ≠ 0`, the unit normal `σ ∇F/‖∇F‖` is `s ∇G/‖∇G‖` for
`s = σ sign(c)`. -/
theorem exists_sign_normal_eq {F G : E d → ℝ} {y : E d} {c σ : ℝ} (hc : c ≠ 0)
    (hG : ∇ G y = c • ∇ F y) (hσ : σ = 1 ∨ σ = -1) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      (s * ‖∇ G y‖⁻¹) • ∇ G y = (σ * ‖∇ F y‖⁻¹) • ∇ F y := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · refine ⟨-σ, by rcases hσ with rfl | rfl <;> simp, ?_⟩
    rw [hG, norm_smul, Real.norm_eq_abs, abs_of_neg hneg, smul_smul]
    congr 1
    by_cases h0 : ‖∇ F y‖ = 0
    · simp [h0]
    · field_simp
  · refine ⟨σ, hσ, ?_⟩
    rw [hG, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, smul_smul]
    congr 1
    by_cases h0 : ‖∇ F y‖ = 0
    · simp [h0]
    · field_simp

/-! ### One side of the free boundary -/

section Side

variable {U : Set (E d)} {Q u : E d → ℝ}

/-- The positivity set of the one-sided restriction. -/
private theorem posSet_side {x₀ : E d} {ρ σ : ℝ}
    {F : E d → ℝ} (hpos : ball x₀ ρ ∩ {y | 0 < σ * F y} ⊆ posSet u U) :
    posSet ({y | 0 < σ * F y}.indicator u) (ball x₀ ρ) = ball x₀ ρ ∩ {y | 0 < σ * F y} := by
  ext y
  simp only [posSet, mem_setOf_eq, mem_inter_iff]
  constructor
  · rintro ⟨hyB, hy⟩
    refine ⟨hyB, ?_⟩
    by_contra h
    rw [indicator_of_notMem (show y ∉ {y | 0 < σ * F y} from h)] at hy
    exact lt_irrefl _ hy
  · rintro ⟨hyB, hy⟩
    refine ⟨hyB, ?_⟩
    rw [indicator_of_mem (show y ∈ {y | 0 < σ * F y} from hy)]
    exact (hpos ⟨hyB, hy⟩).2

/-- The free boundary of the one-sided restriction. -/
private theorem freeBoundary_side {x₀ : E d} {ρ σ : ℝ} {F : E d → ℝ} {v : E d → ℝ}
    (hF : ContDiff ℝ ∞ F) (hσ : σ = 1 ∨ σ = -1) (hn : ∀ y ∈ ball x₀ ρ, ∇ F y ≠ 0)
    (hP : posSet v (ball x₀ ρ) = ball x₀ ρ ∩ {y | 0 < σ * F y}) :
    freeBoundary v (ball x₀ ρ) = ball x₀ ρ ∩ {y | F y = 0} := by
  have hFc : Continuous F := hF.continuous
  have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hSo : IsOpen (ball x₀ ρ ∩ {y | 0 < σ * F y}) :=
    isOpen_ball.inter (isOpen_lt continuous_const (continuous_const.mul hFc))
  rw [freeBoundary, hP]
  ext y
  simp only [mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hfr, hyB⟩
    refine ⟨hyB, ?_⟩
    have hcl : y ∈ closure {y | 0 < σ * F y} :=
      closure_mono inter_subset_right (frontier_subset_closure hfr)
    have hge : 0 ≤ σ * F y :=
      (closure_lt_subset_le continuous_const (continuous_const.mul hFc)) hcl
    have hnot : ¬ 0 < σ * F y := fun h ↦ by
      have := hfr.2
      rw [hSo.interior_eq] at this
      exact this ⟨hyB, h⟩
    have : σ * F y = 0 := le_antisymm (not_lt.1 hnot) hge
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hσ0
    · exact h
  · rintro ⟨hyB, hFy⟩
    refine ⟨⟨?_, ?_⟩, hyB⟩
    · have hray := eventually_pos_mul_ray (hF.differentiable (by simp) y) hFy (hn y hyB) hσ
      have hB := (tendsto_ray y ((σ * ‖∇ F y‖⁻¹) • ∇ F y)).eventually
        (isOpen_ball.mem_nhds hyB)
      exact mem_closure_of_tendsto (tendsto_ray y _) (hB.and hray)
    · rw [hSo.interior_eq]
      rintro ⟨-, h⟩
      rw [mem_setOf_eq, hFy, mul_zero] at h
      exact lt_irrefl _ h

/-- The one-sided restriction is Lipschitz on the ball. -/
private theorem lipschitzOnWith_side (hu : IsClassicalSolution U Q u) {x₀ : E d} {ρ σ : ℝ}
    {F : E d → ℝ} (hFc : Continuous F) {L : ℝ≥0} (hL : LipschitzOnWith L u U)
    (hBU : ball x₀ ρ ⊆ U)
    (hFB : ball x₀ ρ ∩ freeBoundary u U = ball x₀ ρ ∩ {y | F y = 0}) :
    LipschitzOnWith L ({y | 0 < σ * F y}.indicator u) (ball x₀ ρ) := by
  -- a positive point and a nonpositive point: cross the hypersurface
  have key : ∀ p ∈ ball x₀ ρ, ∀ q ∈ ball x₀ ρ, 0 < σ * F p → σ * F q ≤ 0 →
      |u p| ≤ L * dist p q := by
    intro p hp q hq hFp hFq
    set g : ℝ → ℝ := fun t ↦ σ * F (p + t • (q - p)) with hg
    have hgc : ContinuousOn g (Icc 0 1) :=
      (continuous_const.mul (hFc.comp (continuous_const.add
        (continuous_id.smul continuous_const)))).continuousOn
    obtain ⟨t, ht, hgt⟩ : ∃ t ∈ Icc (0 : ℝ) 1, g t = 0 := by
      have h0 : g 0 = σ * F p := by simp [hg]
      have h1 : g 1 = σ * F q := by simp [hg]
      have := intermediate_value_Icc' (zero_le_one' ℝ) hgc
      exact this ⟨by rw [h1]; exact hFq, by rw [h0]; exact hFp.le⟩
    set m := p + t • (q - p) with hm
    have hmB : m ∈ ball x₀ ρ := by
      have := (convex_ball x₀ ρ).add_smul_sub_mem hp hq ht
      simpa [hm] using this
    have hFm : F m = 0 := by
      rcases mul_eq_zero.1 hgt with h | h
      · rw [h, zero_mul] at hFp; exact absurd hFp (lt_irrefl 0)
      · exact h
    have hmFB : m ∈ freeBoundary u U := by
      have : m ∈ ball x₀ ρ ∩ {y | F y = 0} := ⟨hmB, hFm⟩
      rw [← hFB] at this
      exact this.2
    have hum : u m = 0 := hu.eq_zero_of_notMem (hBU hmB) (hu.notMem_posSet_of_mem_freeBoundary hmFB)
    have hdist : dist p m ≤ dist p q := by
      rw [hm, dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg ht.1, norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have := hL.dist_le_mul p (hBU hp) m (hBU hmB)
    rw [Real.dist_eq, hum, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hdist L.2)
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq ↦ ?_
  by_cases hFp : 0 < σ * F p <;> by_cases hFq : 0 < σ * F q
  · rw [indicator_of_mem (show p ∈ {y | 0 < σ * F y} from hFp),
      indicator_of_mem (show q ∈ {y | 0 < σ * F y} from hFq)]
    exact hL.dist_le_mul p (hBU hp) q (hBU hq)
  · rw [indicator_of_mem (show p ∈ {y | 0 < σ * F y} from hFp),
      indicator_of_notMem (show q ∉ {y | 0 < σ * F y} from hFq), Real.dist_eq, sub_zero]
    exact key p hp q hq hFp (not_lt.1 hFq)
  · rw [indicator_of_notMem (show p ∉ {y | 0 < σ * F y} from hFp),
      indicator_of_mem (show q ∈ {y | 0 < σ * F y} from hFq), Real.dist_eq, zero_sub, abs_neg,
      dist_comm]
    exact key q hq p hp hFq (not_lt.1 hFp)
  · rw [indicator_of_notMem (show p ∉ {y | 0 < σ * F y} from hFp),
      indicator_of_notMem (show q ∉ {y | 0 < σ * F y} from hFq), dist_self]
    positivity

/-- **One side of the free boundary is a classical solution.** Let `F` be smooth with
`∇F ≠ 0` on `B = B_ρ(x₀) ⊆ U`, and `B ∩ F(u) = B ∩ {F = 0}`. If the side `B ∩ {σF > 0}` lies in
`{u > 0}`, then `ũ = u · 1_{σF > 0}` is a classical solution in `B`, with
`{ũ > 0} ∩ B = B ∩ {σF > 0}` and `F(ũ) = B ∩ {F = 0}`. -/
theorem IsClassicalSolution.side (hu : IsClassicalSolution U Q u) {x₀ : E d} {ρ σ : ℝ}
    {F : E d → ℝ} (hF : ContDiff ℝ ∞ F) (hσ : σ = 1 ∨ σ = -1) (hBU : ball x₀ ρ ⊆ U)
    (hn : ∀ y ∈ ball x₀ ρ, ∇ F y ≠ 0)
    (hFB : ball x₀ ρ ∩ freeBoundary u U = ball x₀ ρ ∩ {y | F y = 0})
    (hpos : ball x₀ ρ ∩ {y | 0 < σ * F y} ⊆ posSet u U) :
    IsClassicalSolution (ball x₀ ρ) Q ({y | 0 < σ * F y}.indicator u) ∧
      posSet ({y | 0 < σ * F y}.indicator u) (ball x₀ ρ) = ball x₀ ρ ∩ {y | 0 < σ * F y} ∧
      freeBoundary ({y | 0 < σ * F y}.indicator u) (ball x₀ ρ) = ball x₀ ρ ∩ {y | F y = 0} := by
  set S := {y | 0 < σ * F y} with hS
  set v := S.indicator u with hv
  have hFc : Continuous F := hF.continuous
  have hSo : IsOpen S := isOpen_lt continuous_const (continuous_const.mul hFc)
  have hP := posSet_side (u := u) hpos
  have hFBv := freeBoundary_side hF hσ hn hP
  refine ⟨⟨isOpen_ball, ?_, ?_, ?_, ?_⟩, hP, hFBv⟩
  · obtain ⟨L, hL⟩ := hu.lipschitzOnWith
    exact ⟨L, lipschitzOnWith_side hu hFc hL hBU hFB⟩
  · intro y hy
    by_cases hyS : y ∈ S
    · rw [hv, indicator_of_mem hyS]; exact hu.nonneg y (hBU hy)
    · rw [hv, indicator_of_notMem hyS]
  · intro y hyB hy
    have hyS : y ∈ S := by
      by_contra h
      rw [hv, indicator_of_notMem h] at hy
      exact lt_irrefl _ hy
    have heq : v =ᶠ[𝓝 y] u := by
      filter_upwards [hSo.mem_nhds hyS] with z hz
      rw [hv, indicator_of_mem hz]
    have hyP := hpos ⟨hyB, hyS⟩
    exact (harmonicAt_congr_nhds heq).2 (hu.harmonicAt y hyP.1 hyP.2)
  · intro y hy
    rw [hFBv] at hy
    obtain ⟨hyB, hFy⟩ := hy
    have hFy' : F y = 0 := hFy
    set r := ρ - dist y x₀ with hr
    have hr0 : 0 < r := by rw [hr]; linarith [mem_ball.1 hyB]
    have hball : ball y r ⊆ ball x₀ ρ := ball_subset_ball' (by rw [hr]; linarith)
    refine ⟨r, hr0, F, hF, hn y hyB, ?_, fun s hs hev ↦ ?_⟩
    · rw [hFBv, ← inter_assoc, inter_eq_left.2 hball]
    -- the side `s` must be `σ`
    have hσ0 : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hsσ : s = σ := by
      have h1 := eventually_pos_mul_ray (hF.differentiable (by simp) y) hFy' (hn y hyB) hs
      have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          0 < σ * F (y + t • (s * ‖∇ F y‖⁻¹) • ∇ F y) := hev.mono fun t ht ↦ by
        by_contra h
        rw [hv, indicator_of_notMem (show _ ∉ S from h)] at ht
        exact lt_irrefl _ ht
      obtain ⟨t, h1t, h2t⟩ := (h1.and h2).exists
      rcases hs with rfl | rfl <;> rcases hσ with rfl | rfl
      · rfl
      · linarith
      · linarith
      · rfl
    subst hsσ
    -- `y` is a free boundary point of `u`
    have hyFB : y ∈ freeBoundary u U := by
      have : y ∈ ball x₀ ρ ∩ {y | F y = 0} := ⟨hyB, hFy'⟩
      rw [← hFB] at this
      exact this.2
    have huy : u y = 0 :=
      hu.eq_zero_of_notMem (hBU hyB) (hu.notMem_posSet_of_mem_freeBoundary hyFB)
    have hvy : v y = 0 := by
      rw [hv, indicator_of_notMem]
      simp [hS, hFy']
    obtain ⟨r', hr', G, hG, hGn, hGFB, hGq⟩ := hu.free_boundary y hyFB
    -- parallel normals
    have hGy : G y = 0 := by
      have : y ∈ ball y r' ∩ freeBoundary u U := ⟨mem_ball_self hr', hyFB⟩
      rw [hGFB] at this
      exact this.2
    have hsub : ∀ᶠ z in 𝓝 y, F z = F y → G z = G y := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr'),
        isOpen_ball.mem_nhds hyB] with z hz1 hz2 hFz
      rw [hFy'] at hFz
      have : z ∈ ball x₀ ρ ∩ {y | F y = 0} := ⟨hz2, hFz⟩
      rw [← hFB] at this
      have h2 : z ∈ ball y r' ∩ freeBoundary u U := ⟨hz1, this.2⟩
      rw [hGFB] at h2
      rw [hGy]; exact h2.2
    obtain ⟨c, hc, hGc⟩ := gradient_eq_smul_of_zero_set (hF.contDiffAt.of_le (by simp))
      (hG.contDiffAt.of_le (by simp)) (hn y hyB) hGn hsub
    obtain ⟨s', hs', hnormal⟩ := exists_sign_normal_eq (F := F) (G := G) hc hGc hs
    have hevu : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (y + t • (s' * ‖∇ G y‖⁻¹) • ∇ G y) := by
      rw [hnormal]
      refine hev.mono fun t ht ↦ ?_
      by_cases h : y + t • (s * ‖∇ F y‖⁻¹) • ∇ F y ∈ S
      · rwa [hv, indicator_of_mem h] at ht
      · rw [hv, indicator_of_notMem h] at ht; exact absurd ht (lt_irrefl 0)
    have hq := hGq s' hs' hevu
    rw [hnormal, huy] at hq
    rw [hvy]
    refine hq.congr' ?_
    filter_upwards [hev] with t ht
    by_cases h : y + t • (s * ‖∇ F y‖⁻¹) • ∇ F y ∈ S
    · rw [hv, indicator_of_mem h]
    · rw [hv, indicator_of_notMem h] at ht; exact absurd ht (lt_irrefl 0)

end Side

/-! ### Flatness at small scales -/

/-- First-order Taylor bound for `σ F` at a regular zero `x₀`, in terms of the unit normal
`e = σ ∇F(x₀)/‖∇F(x₀)‖`. -/
private theorem taylor_side {F : E d → ℝ} {x₀ : E d} (hF : DifferentiableAt ℝ F x₀)
    (hFx : F x₀ = 0) (hn : ∇ F x₀ ≠ 0) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ h : E d, ‖h‖ < δ →
      |σ * F (x₀ + h) - ‖∇ F x₀‖ * ⟪h, (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀⟫| ≤ η * ‖h‖ := by
  have ho := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hF.hasFDerivAt).def hη
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 ho
  refine ⟨δ, hδ, fun h hh ↦ ?_⟩
  have h1 := hball (show dist h 0 < δ by rwa [dist_zero_right])
  have hnorm : ‖∇ F x₀‖ ≠ 0 := norm_ne_zero_iff.2 hn
  have heq : σ * F (x₀ + h) - ‖∇ F x₀‖ * ⟪h, (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀⟫ =
      σ * (F (x₀ + h) - F x₀ - fderiv ℝ F x₀ h) := by
    rw [hFx, fderiv_apply_eq_inner_gradient, real_inner_smul_right, real_inner_comm]
    field_simp
    ring
  rw [heq, abs_mul]
  have : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  rw [this, one_mul]
  simpa [Real.norm_eq_abs] using h1

/-- Harmonic limits along a sequence that is harmonic on `U` only eventually. -/
private theorem harmonic_limit_eventually' {F : ℕ → E d → ℝ} {f : E d → ℝ} {U : Set (E d)}
    (hU : IsOpen U) (hF : ∀ᶠ k in atTop, HarmonicOnNhd (F k) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) : HarmonicOnNhd f U := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hF
  have hG : TendstoLocallyUniformlyOn (fun k ↦ F (k + K)) f atTop U := fun s hs x hx ↦ by
    obtain ⟨t, ht, h⟩ := hconv s hs x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat K).eventually h⟩
  exact (harmonicOnNhd_of_tendstoLocallyUniformlyOn' hU
    (fun k ↦ hK (k + K) (Nat.le_add_left K k)) hG).1

/-- **Flatness at small scales.** Let `v ≥ 0` be `L`-Lipschitz on `B_ρ(x₀)`, zero on
`{σF ≤ 0}` and harmonic on `{σF > 0}`, where `F(x₀) = 0`, `∇F(x₀) ≠ 0`, and let the normal
difference quotient `v(x₀ + t e)/t` tend to `q > 0`, `e = σ∇F(x₀)/‖∇F(x₀)‖`. Then for every
`ε > 0` and every small `r`, `q (⟪y - x₀, e⟫ - εr)₊ ≤ v ≤ q (⟪y - x₀, e⟫ + εr)₊` on `B_r(x₀)`.

Proof: blow up along `r_k → 0`; the limit vanishes on `{⟪z, e⟫ ≤ 0}` and is harmonic on
`{⟪z, e⟫ > 0}` (the rescaled hypersurfaces flatten), so it is `q ⟪z, e⟫₊` by the half-space
Liouville theorem `eq_linear_of_halfSpace` and the difference quotient. -/
theorem flat_of_side {x₀ : E d} {ρ σ q ε : ℝ} {F v : E d → ℝ} {L : ℝ≥0} (hρ : 0 < ρ)
    (hF : DifferentiableAt ℝ F x₀) (hFx : F x₀ = 0) (hn : ∇ F x₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (hL : LipschitzOnWith L v (ball x₀ ρ)) (hv0 : ∀ y ∈ ball x₀ ρ, 0 ≤ v y)
    (hzero : ∀ y ∈ ball x₀ ρ, σ * F y ≤ 0 → v y = 0)
    (hharm : ∀ y ∈ ball x₀ ρ, 0 < σ * F y → HarmonicAt v y)
    (hq : Tendsto (fun t : ℝ ↦ v (x₀ + t • (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀) / t) (𝓝[>] 0) (𝓝 q))
    (hq0 : 0 < q) (hε : 0 < ε) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ y ∈ ball x₀ r,
      q * max (⟪y - x₀, (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀⟫ - ε * r) 0 ≤ v y ∧
        v y ≤ q * max (⟪y - x₀, (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀⟫ + ε * r) 0 := by
  set a := ‖∇ F x₀‖ with ha_def
  set e : E d := (σ * a⁻¹) • ∇ F x₀ with he_def
  have ha : 0 < a := norm_pos_iff.2 hn
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have he1 : ‖e‖ = 1 := by
    rw [he_def, norm_smul, Real.norm_eq_abs, abs_mul, hσabs, abs_inv, abs_of_pos ha, one_mul,
      ← ha_def, inv_mul_cancel₀ ha.ne']
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he1, one_pow]
  have hinner_le : ∀ w : E d, |⟪w, e⟫| ≤ ‖w‖ := fun w ↦ by
    have := abs_real_inner_le_norm w e
    rwa [he1, mul_one] at this
  have hvx₀ : v x₀ = 0 := hzero x₀ (mem_ball_self hρ) (by rw [hFx, mul_zero])
  have htay := fun η (hη : 0 < η) ↦ taylor_side hF hFx hn hσ hη
  by_contra H
  push Not at H
  choose r hr0 hrle y hy hbad using fun k : ℕ ↦ H (ρ / ((k : ℝ) + 2)) (by positivity)
  -- the blow-ups
  set f : ℕ → E d → ℝ := fun k z ↦ v (x₀ + r k • z) / r k with hf
  have hmap : ∀ k z, z ∈ ball (0 : E d) (ρ / r k) → x₀ + r k • z ∈ ball x₀ ρ := by
    intro k z hz
    rw [mem_ball_zero_iff, lt_div_iff₀ (hr0 k)] at hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hr0 k)]
    linarith
  have hLipf : ∀ k, LipschitzOnWith L (f k) (ball 0 (ρ / r k)) := by
    intro k
    refine LipschitzOnWith.of_dist_le_mul fun p hp w hw ↦ ?_
    have h := hL.dist_le_mul _ (hmap k p hp) _ (hmap k w hw)
    have hAd : dist (x₀ + r k • p) (x₀ + r k • w) = r k * dist p w := by
      rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos (hr0 k)]
    rw [hAd] at h
    rw [hf, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (hr0 k), div_le_iff₀ (hr0 k)]
    rw [Real.dist_eq] at h
    linarith
  have hρt : Tendsto (fun k ↦ ρ / r k) atTop atTop := by
    refine tendsto_atTop_mono (fun k ↦ ?_) (tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds (x := (2 : ℝ))))
    rw [le_div_iff₀ (hr0 k)]
    have := hrle k
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hf0 : ∀ k, |f k 0| ≤ 0 := fun k ↦ by simp [hf, hvx₀]
  obtain ⟨φ, hφ, f₀, hf₀L, hconv⟩ :=
    exists_blowup_subseq hρt (fun k ↦ div_pos hρ (hr0 k)) hLipf hf0
  have hf₀c : Continuous f₀ := hf₀L.continuous
  have hpt : ∀ z, Tendsto (fun k ↦ f (φ k) z) atTop (𝓝 (f₀ z)) := fun z ↦
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ z)
  -- the scales tend to zero
  have hr_small : ∀ c > 0, ∀ᶠ k in atTop, r (φ k) < c := by
    intro c hc
    have ht : Tendsto (fun k : ℕ ↦ ρ / ((k : ℝ) + 2)) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add
        (tendsto_const_nhds (x := (2 : ℝ)))
      exact this.const_div_atTop ρ
    filter_upwards [(ht.comp hφ.tendsto_atTop).eventually (gt_mem_nhds hc)] with k hk
    exact (hrle (φ k)).trans_lt hk
  have hrt : Tendsto (fun k ↦ r (φ k)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ hr0 (φ k)⟩
    refine Metric.tendsto_atTop.2 fun c hc ↦ ?_
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hr_small c hc)
    refine ⟨K, fun k hk ↦ ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (hr0 _)]
    exact hK k hk
  -- the sign of `σF` along rescaled points
  have hsign_neg : ∀ z : E d, ∀ η, 0 < η → ∀ δ, (∀ h : E d, ‖h‖ < δ →
      |σ * F (x₀ + h) - a * ⟪h, e⟫| ≤ η * ‖h‖) → ∀ k, r k * ‖z‖ < δ →
      σ * F (x₀ + r k • z) ≤ r k * (a * ⟪z, e⟫ + η * ‖z‖) := by
    intro z η _ δ hδ k hk
    have hh : ‖r k • z‖ < δ := by
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (hr0 k)]
    have := hδ _ hh
    rw [real_inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hr0 k)] at this
    have := (abs_le.1 this).2
    linarith
  have hsign_pos : ∀ z : E d, ∀ η, 0 < η → ∀ δ, (∀ h : E d, ‖h‖ < δ →
      |σ * F (x₀ + h) - a * ⟪h, e⟫| ≤ η * ‖h‖) → ∀ k, r k * ‖z‖ < δ →
      r k * (a * ⟪z, e⟫ - η * ‖z‖) ≤ σ * F (x₀ + r k • z) := by
    intro z η _ δ hδ k hk
    have hh : ‖r k • z‖ < δ := by
      rwa [norm_smul, Real.norm_eq_abs, abs_of_pos (hr0 k)]
    have := hδ _ hh
    rw [real_inner_smul_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hr0 k)] at this
    have := (abs_le.1 this).1
    linarith
  have hmapB : ∀ k (z : E d), r k * ‖z‖ < ρ → x₀ + r k • z ∈ ball x₀ ρ := fun k z hz ↦ by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hr0 k)]
    exact hz
  -- (i) the limit vanishes on the closed lower half-space
  have hneg : ∀ z, ⟪z, e⟫ < 0 → f₀ z = 0 := by
    intro z hz
    set b := -⟪z, e⟫ with hb
    have hb0 : 0 < b := by linarith
    set η := a * b / (2 * (‖z‖ + 1)) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨δ, hδ, hδF⟩ := htay η hη0
    have hev : ∀ᶠ k in atTop, f (φ k) z = 0 := by
      filter_upwards [hr_small (min δ ρ / (‖z‖ + 1)) (by positivity)] with k hk
      rw [lt_div_iff₀ (by positivity)] at hk
      have hrz : r (φ k) * ‖z‖ < r (φ k) * (‖z‖ + 1) :=
        mul_lt_mul_of_pos_left (lt_add_one _) (hr0 _)
      have hk1 : r (φ k) * ‖z‖ < δ := hrz.trans (hk.trans_le (min_le_left _ _))
      have hk2 : r (φ k) * ‖z‖ < ρ := hrz.trans (hk.trans_le (min_le_right _ _))
      have hle := hsign_neg z η hη0 δ hδF (φ k) hk1
      have hkey : a * ⟪z, e⟫ + η * ‖z‖ < 0 := by
        have : η * ‖z‖ < a * b := by
          rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          have hab := mul_pos ha hb0
          linarith [mul_nonneg hab.le (norm_nonneg z)]
        linarith
      have : σ * F (x₀ + r (φ k) • z) ≤ 0 :=
        hle.trans (mul_nonpos_of_nonneg_of_nonpos (hr0 _).le hkey.le)
      change v (x₀ + r (φ k) • z) / r (φ k) = 0
      rw [hzero _ (hmapB _ z hk2) this, zero_div]
    exact tendsto_nhds_unique (hpt z) (tendsto_const_nhds.congr' (hev.mono fun k hk ↦ hk.symm))
  have hzero₀ : ∀ z, ⟪z, e⟫ ≤ 0 → f₀ z = 0 := by
    intro z hz
    rcases hz.lt_or_eq with hz | hz
    · exact hneg z hz
    · have hc : Tendsto (fun t : ℝ ↦ f₀ (z - t • e)) (𝓝[>] 0) (𝓝 (f₀ z)) := by
        have : Tendsto (fun t : ℝ ↦ z - t • e) (𝓝[>] 0) (𝓝 z) := by
          have hc' : Continuous fun t : ℝ ↦ z - t • e := by fun_prop
          simpa using (hc'.tendsto 0).mono_left nhdsWithin_le_nhds
        exact (hf₀c.tendsto z).comp this
      refine tendsto_nhds_unique hc (tendsto_const_nhds.congr' ?_)
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0 : ℝ) < t := ht
      refine (hneg _ ?_).symm
      rw [inner_sub_left, real_inner_smul_left, hee, hz]
      linarith
  -- (ii) the limit is harmonic on the upper half-space
  have hharm₀ : HarmonicOnNhd f₀ {z | 0 < ⟪z, e⟫} := by
    intro z₀ hz₀
    simp only [mem_setOf_eq] at hz₀
    set b := ⟪z₀, e⟫ with hb
    set s := b / 2 with hs
    have hs0 : 0 < s := by positivity
    set M := ‖z₀‖ + s + 1 with hM
    have hM0 : 0 < M := by positivity
    set η := a * b / (4 * M) with hη
    have hη0 : 0 < η := by positivity
    obtain ⟨δ, hδ, hδF⟩ := htay η hη0
    have hev : ∀ᶠ k in atTop, HarmonicOnNhd (f (φ k)) (ball z₀ s) := by
      filter_upwards [hr_small (min δ ρ / M) (by positivity)] with k hk z hz
      rw [lt_div_iff₀ hM0] at hk
      have hzn : ‖z‖ ≤ ‖z₀‖ + s := by
        have := norm_le_norm_add_norm_sub' z z₀
        rw [← dist_eq_norm] at this
        linarith [mem_ball.1 hz]
      have hze : b / 2 < ⟪z, e⟫ := by
        have h1 : ⟪z, e⟫ = b + ⟪z - z₀, e⟫ := by rw [inner_sub_left, hb]; ring
        have h2 := (abs_le.1 (hinner_le (z - z₀))).1
        rw [← dist_eq_norm] at h2
        have h3 := mem_ball.1 hz
        linarith
      have hMz : ‖z‖ < M := by rw [hM]; linarith
      have hrz : r (φ k) * ‖z‖ < r (φ k) * M := mul_lt_mul_of_pos_left hMz (hr0 _)
      have hk1 : r (φ k) * ‖z‖ < δ := hrz.trans (hk.trans_le (min_le_left _ _))
      have hk2 : r (φ k) * ‖z‖ < ρ := hrz.trans (hk.trans_le (min_le_right _ _))
      have hge := hsign_pos z η hη0 δ hδF (φ k) hk1
      have hkey : 0 < a * ⟪z, e⟫ - η * ‖z‖ := by
        have : η * ‖z‖ ≤ a * b / 4 := by
          rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          linarith [mul_le_mul_of_nonneg_left hMz.le (mul_pos ha hz₀).le]
        linarith [mul_lt_mul_of_pos_left hze ha, mul_pos ha hz₀]
      have hpos : 0 < σ * F (x₀ + r (φ k) • z) := lt_of_lt_of_le (mul_pos (hr0 _) hkey) hge
      have h1 := HarmonicAt.comp_add_smul (hharm _ (hmapB _ z hk2) hpos)
      have h2 := InnerProductSpace.HarmonicAt.const_smul (c := (r (φ k))⁻¹) h1
      refine (harmonicAt_congr_nhds (Eventually.of_forall fun w ↦ ?_)).1 h2
      simp [hf, div_eq_inv_mul]
    have hconvB : TendstoLocallyUniformlyOn (fun k ↦ f (φ k)) f₀ atTop (ball z₀ s) :=
      (tendstoLocallyUniformlyOn_univ.2 hconv).mono (subset_univ _)
    exact harmonic_limit_eventually' isOpen_ball hev hconvB z₀ (mem_ball_self hs0)
  -- (iii) half-space Liouville and the slope
  obtain ⟨α, hα⟩ := eq_linear_of_halfSpace he1 hf₀L hzero₀ hharm₀
  have hαq : α = q := by
    have h1 : f₀ e = α := by rw [hα e (by rw [hee]; exact one_pos), hee, mul_one]
    have h2 : Tendsto (fun k ↦ f (φ k) e) atTop (𝓝 q) := hq.comp hrt
    rw [← h1]
    exact tendsto_nhds_unique (hpt e) h2
  have hform : ∀ z, f₀ z = q * max ⟪z, e⟫ 0 := by
    intro z
    rcases le_or_gt ⟪z, e⟫ 0 with hz | hz
    · rw [hzero₀ z hz, max_eq_right hz, mul_zero]
    · rw [hα z hz, hαq, max_eq_left hz.le]
  -- (iv) uniform closeness on the unit ball and vanishing below `-ε/2`
  have hunif := Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) _ (isCompact_closedBall 0 1))
    (q * ε / 2) (by positivity)
  obtain ⟨δ, hδ, hδF⟩ := htay (a * ε / 4) (by positivity)
  obtain ⟨k, hk1, hk2⟩ := (hunif.and (hr_small (min δ ρ) (lt_min hδ hρ))).exists
  set R := r (φ k) with hR
  have hR0 : 0 < R := hr0 _
  have hlowzero : ∀ z ∈ closedBall (0 : E d) 1, ⟪z, e⟫ ≤ -(ε / 2) → f (φ k) z = 0 := by
    intro z hz hze
    have hz1 : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.1 hz
    have hRz : R * ‖z‖ ≤ R := mul_le_of_le_one_right hR0.le hz1
    have hk1' : R * ‖z‖ < δ := hRz.trans_lt (hk2.trans_le (min_le_left _ _))
    have hk2' : R * ‖z‖ < ρ := hRz.trans_lt (hk2.trans_le (min_le_right _ _))
    have hle := hsign_neg z (a * ε / 4) (by positivity) δ hδF (φ k) hk1'
    have hkey : a * ⟪z, e⟫ + a * ε / 4 * ‖z‖ < 0 := by
      have h1 : a * ε / 4 * ‖z‖ ≤ a * ε / 4 := by
        have := mul_le_mul_of_nonneg_left hz1 (show 0 ≤ a * ε / 4 by positivity)
        linarith
      have h2 : a * ⟪z, e⟫ ≤ a * (-(ε / 2)) := mul_le_mul_of_nonneg_left hze ha.le
      have h3 := mul_pos ha hε
      linarith
    have : σ * F (x₀ + R • z) ≤ 0 :=
      hle.trans (mul_nonpos_of_nonneg_of_nonpos hR0.le hkey.le)
    change v (x₀ + R • z) / R = 0
    rw [hzero _ (hmapB _ z hk2') this, zero_div]
  -- (v) the contradiction at scale `R`
  set Y := y (φ k) with hY
  have hYb : Y ∈ ball x₀ R := hy (φ k)
  set z : E d := R⁻¹ • (Y - x₀) with hz
  have hYz : x₀ + R • z = Y := by
    rw [hz, smul_smul, mul_inv_cancel₀ hR0.ne', one_smul, add_sub_cancel]
  have hz1 : z ∈ closedBall (0 : E d) 1 := by
    rw [mem_closedBall_zero_iff, hz, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0,
      inv_mul_le_iff₀ hR0, mul_one, ← dist_eq_norm]
    exact (mem_ball.1 hYb).le
  have hfz : f (φ k) z = v Y / R := by
    change v (x₀ + R • z) / R = v Y / R
    rw [hYz]
  have hinnerY : ⟪Y - x₀, e⟫ = R * ⟪z, e⟫ := by
    rw [hz, real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hR0.ne', one_mul]
  have hvY : v Y = R * f (φ k) z := by rw [hfz]; field_simp
  have hYB : Y ∈ ball x₀ ρ :=
    ball_subset_ball ((hk2.trans_le (min_le_right _ _)).le) hYb
  have hclose := hk1 z hz1
  rw [hform z, Real.dist_eq] at hclose
  have hcl := abs_lt.1 hclose
  set w := ⟪z, e⟫ with hw
  have hfk0 : 0 ≤ f (φ k) z := by
    rw [hfz]; exact div_nonneg (hv0 Y hYB) hR0.le
  set fk := f (φ k) z with hfk
  have hqRε : 0 < R * (q * ε) := mul_pos hR0 (mul_pos hq0 hε)
  have hlow : q * max (⟪Y - x₀, e⟫ - ε * R) 0 ≤ v Y := by
    rw [hinnerY, hvY]
    rcases le_or_gt w ε with hwε | hwε
    · have h1 : R * w - ε * R ≤ 0 := by
        have := mul_le_mul_of_nonneg_left hwε hR0.le
        linarith
      rw [max_eq_right h1, mul_zero]
      exact mul_nonneg hR0.le hfk0
    · have hmw : max w 0 = w := max_eq_left (by linarith)
      rw [hmw] at hcl
      have h1 : 0 ≤ R * w - ε * R := by
        have := mul_le_mul_of_nonneg_left hwε.le hR0.le
        linarith
      rw [max_eq_left h1]
      have h2 : q * w - q * ε / 2 < fk := by linarith [hcl.2]
      have h3 := mul_lt_mul_of_pos_left h2 hR0
      linarith
  have hup : v Y ≤ q * max (⟪Y - x₀, e⟫ + ε * R) 0 := by
    rw [hinnerY, hvY]
    rcases le_or_gt w (-(ε / 2)) with hwε | hwε
    · rw [hfk, hlowzero z hz1 hwε, mul_zero]
      exact mul_nonneg hq0.le (le_max_right _ _)
    · have h1 : 0 ≤ R * w + ε * R := by
        have := mul_le_mul_of_nonneg_left hwε.le hR0.le
        linarith [mul_pos hR0 hε]
      rw [max_eq_left h1]
      have h2 : fk < q * max w 0 + q * ε / 2 := by linarith [hcl.1]
      have h4 : q * max w 0 + q * ε / 2 ≤ q * (w + ε) := by
        rcases le_or_gt w 0 with hw0 | hw0
        · rw [max_eq_right hw0]
          have := mul_le_mul_of_nonneg_left (show ε / 2 ≤ w + ε by linarith) hq0.le
          linarith
        · rw [max_eq_left hw0.le]
          have := mul_pos hq0 hε
          linarith
      have h3 := mul_lt_mul_of_pos_left (h2.trans_le h4) hR0
      linarith
  exact absurd (hbad (φ k) hlow) (not_lt.2 hup)


/-! ### The gradient up to the free boundary -/

section Main

variable {U : Set (E d)} {Q u : E d → ℝ}

/-- Along the normal ray into a positive side, the one-sided restriction has the difference
quotient of `u`. -/
private theorem tendsto_quotient_side {x₀ : E d} {ρ σ : ℝ}
    {F : E d → ℝ} (hF : ContDiff ℝ ∞ F) (hn : ∇ F x₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1)
    (hFx : F x₀ = 0) (hux : u x₀ = 0) (hρ : 0 < ρ)
    (hq : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (x₀ + t • (s * ‖∇ F x₀‖⁻¹) • ∇ F x₀)) →
      Tendsto (fun t ↦ (u (x₀ + t • (s * ‖∇ F x₀‖⁻¹) • ∇ F x₀) - u x₀) / t) (𝓝[>] 0)
        (𝓝 (Q x₀)))
    (hpos : ball x₀ ρ ∩ {y | 0 < σ * F y} ⊆ posSet u U) :
    Tendsto (fun t : ℝ ↦ {y | 0 < σ * F y}.indicator u (x₀ + t • (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀) / t)
      (𝓝[>] 0) (𝓝 (Q x₀)) := by
  set e : E d := (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀
  have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • e ∈ ball x₀ ρ ∩ {y | 0 < σ * F y} :=
    ((tendsto_ray x₀ e).eventually (isOpen_ball.mem_nhds (mem_ball_self hρ))).and
      (eventually_pos_mul_ray (hF.differentiable (by simp) x₀) hFx hn hσ)
  have h := hq σ hσ (hray.mono fun t ht ↦ (hpos ht).2)
  rw [hux] at h
  refine h.congr' (hray.mono fun t ht ↦ ?_)
  simp only [sub_zero]
  rw [indicator_of_mem ht.2]

/-- **The gradient of a classical solution up to its free boundary**, norm form:
`‖∇u(x)‖ → Q(x₀)` as `x → x₀` inside `{u > 0}`, for every free boundary point `x₀`. This holds at
one-sided and two-sided points alike: each side is handled separately
(`IsClassicalSolution.side`), and the limit of the norm is the same on both sides.

Proof: for `d ≥ 2`, each positive side `u · 1_{σF > 0}` is a classical, hence viscosity
(`IsClassicalSolution.isViscSolution`), solution in a small ball which is flat at small scales
(`flat_of_side`), so `isClassicalNear_of_flat` extends its gradient continuously to the free
boundary with `‖G‖ = Q` there. For `d = 1` the gradient is constant on each side
(`norm_gradient_eq_of_ray_one`). No boundary Schauder theory is used: the classical definition gives
only a one-sided normal difference quotient at each point, and the gradient limit is derived from
it. -/
theorem IsClassicalSolution.tendsto_norm_gradient (hu : IsClassicalSolution U Q u)
    (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ y ∈ U, c ≤ Q y) {x₀ : E d}
    (hx₀ : x₀ ∈ freeBoundary u U) :
    Tendsto (fun x ↦ ‖∇ u x‖) (𝓝[posSet u U] x₀) (𝓝 (Q x₀)) := by
  obtain ⟨K, hK⟩ := hQ
  obtain ⟨c, hc, hcQ⟩ := hQpos
  have hx₀U : x₀ ∈ U := hx₀.2
  have hQx₀ : 0 < Q x₀ := hc.trans_le (hcQ x₀ hx₀U)
  have hux : u x₀ = 0 :=
    hu.eq_zero_of_notMem hx₀U (hu.notMem_posSet_of_mem_freeBoundary hx₀)
  obtain ⟨r, hr, F, hF, hn, hFB, hq⟩ := hu.free_boundary x₀ hx₀
  have hFx : F x₀ = 0 := by
    have h : x₀ ∈ ball x₀ r ∩ freeBoundary u U := ⟨mem_ball_self hr, hx₀⟩
    rw [hFB] at h
    exact h.2
  obtain ⟨N, hNo, hxN, hNV, hsides⟩ := hu.exists_sides hx₀ hr hF hn hFB
  -- a ball inside `N` on which `∇F ≠ 0`
  have hgc : Continuous (∇ F) := continuous_gradient (hF.of_le (by simp))
  have hW : IsOpen (N ∩ {y | ∇ F y ≠ 0}) := hNo.inter (isOpen_ne_fun hgc continuous_const)
  obtain ⟨ρ, hρ, hρW⟩ := Metric.isOpen_iff.1 hW x₀ ⟨hxN, hn⟩
  have hBN : ball x₀ ρ ⊆ N := fun y hy ↦ (hρW hy).1
  have hnB : ∀ y ∈ ball x₀ ρ, ∇ F y ≠ 0 := fun y hy ↦ (hρW hy).2
  have hBU : ball x₀ ρ ⊆ U := fun y hy ↦ (hNV (hBN hy)).2
  have hBr : ball x₀ ρ ⊆ ball x₀ r := fun y hy ↦ (hNV (hBN hy)).1
  have hFBB : ball x₀ ρ ∩ freeBoundary u U = ball x₀ ρ ∩ {y | F y = 0} := by
    rw [← inter_eq_left.2 hBr, inter_assoc, hFB, ← inter_assoc]
  -- each side separately
  have hside : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      Tendsto (fun x ↦ ‖∇ u x‖) (𝓝[posSet u U ∩ {y | 0 < σ * F y}] x₀) (𝓝 (Q x₀)) := by
    intro σ hσ
    rcases (hsides σ).2 with hNpos | hNzero
    swap
    · -- a zero side: no positive points near `x₀`
      have hempty : posSet u U ∩ {y | 0 < σ * F y} ∩ N = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
        rintro ⟨⟨hyP, hyσ⟩, hyN⟩
        exact hNzero ⟨hyN, hyσ⟩ (subset_closure hyP)
      have : 𝓝[posSet u U ∩ {y | 0 < σ * F y}] x₀ = ⊥ := by
        rw [nhdsWithin_restrict _ hxN hNo, hempty, nhdsWithin_empty]
      rw [this]
      exact tendsto_bot
    have hpos : ball x₀ ρ ∩ {y | 0 < σ * F y} ⊆ posSet u U := fun y hy ↦
      hNpos ⟨hBN hy.1, hy.2⟩
    obtain rfl | rfl | hd : d = 0 ∨ d = 1 ∨ 2 ≤ d := by omega
    · exact absurd (Subsingleton.elim _ _) hn
    · -- dimension one: the gradient is constant on the side
      set e : E 1 := (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀
      have hS := hsides σ
      have hSo : IsOpen (N ∩ {y | 0 < σ * F y}) :=
        hNo.inter (isOpen_lt continuous_const (continuous_const.mul hF.continuous))
      have hray : ∀ᶠ t in 𝓝[>] (0 : ℝ), x₀ + t • e ∈ N ∩ {y | 0 < σ * F y} :=
        ((tendsto_ray x₀ e).eventually (hNo.mem_nhds hxN)).and
          (eventually_pos_mul_ray (hF.differentiable (by simp) x₀) hFx hn hσ)
      have hqσ := hq σ hσ (hray.mono fun t ht ↦ (hNpos ht).2)
      have hconst := norm_gradient_eq_of_ray_one hSo hS.1
        (fun y hy ↦ hu.harmonicAt y (hNpos hy).1 (hNpos hy).2) (e := e) (by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_norm,
            show |σ| = 1 by rcases hσ with rfl | rfl <;> simp, one_mul,
            inv_mul_cancel₀ (norm_ne_zero_iff.2 hn)]) hray hqσ
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (hNo.mem_nhds hxN), self_mem_nhdsWithin]
        with y hyN hy
      rw [hconst y ⟨hyN, hy.2⟩, abs_of_pos hQx₀]
    · -- dimension `≥ 2`: flatness and `isClassicalNear_of_flat`
      set v := {y | 0 < σ * F y}.indicator u with hv
      obtain ⟨hvC, hPv, hFBv⟩ := hu.side hF hσ hBU hnB hFBB hpos
      have hx₀v : x₀ ∈ freeBoundary v (ball x₀ ρ) := by
        rw [hFBv]; exact ⟨mem_ball_self hρ, hFx⟩
      obtain ⟨L, hL⟩ := hvC.lipschitzOnWith
      set qmax := Q x₀ + K * ρ with hqmax
      have hQB : ∀ y ∈ ball x₀ ρ, c ≤ Q y ∧ Q y ≤ qmax := by
        intro y hy
        refine ⟨hcQ y (hBU hy), ?_⟩
        have h1 := hK.dist_le_mul y (hBU hy) x₀ hx₀U
        rw [Real.dist_eq] at h1
        have h2 : dist y x₀ < ρ := hy
        have h3 : (K : ℝ) * dist y x₀ ≤ K * ρ := mul_le_mul_of_nonneg_left h2.le K.2
        have h4 := (abs_le.1 h1).2
        linarith
      obtain ⟨εbar, hεbar, Hflat⟩ := isClassicalNear_of_flat hd K c qmax hc
      set e : E d := (σ * ‖∇ F x₀‖⁻¹) • ∇ F x₀ with he
      have he1 : ‖e‖ = 1 := by
        rw [he, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_norm,
          show |σ| = 1 by rcases hσ with rfl | rfl <;> simp, one_mul,
          inv_mul_cancel₀ (norm_ne_zero_iff.2 hn)]
      have hvq := tendsto_quotient_side hF hn hσ hFx hux hρ hq hpos
      obtain ⟨r₀, hr₀, hflat⟩ := flat_of_side (v := v) hρ (hF.differentiable (by simp) x₀)
        hFx hn hσ hL (fun y hy ↦ hvC.nonneg y hy)
        (fun y _ hy ↦ indicator_of_notMem (show y ∉ {y | 0 < σ * F y} from not_lt.2 hy) _)
        (fun y hy hσy ↦ hvC.harmonicAt y hy (by
          rw [indicator_of_mem (show y ∈ {y | 0 < σ * F y} from hσy)]
          exact (hpos ⟨hy, hσy⟩).2)) hvq hQx₀ hεbar
      set r₁ := min r₀ (min εbar ρ) with hr₁
      have hr₁0 : 0 < r₁ := lt_min hr₀ (lt_min hεbar hρ)
      have hvisc : IsViscSolution (ball x₀ ρ) Q v :=
        IsClassicalSolution.isViscSolution hvC (hK.mono hBU).continuousOn
      have hnear := Hflat (ball x₀ ρ) Q v x₀ e r₁ isOpen_ball (hK.mono hBU) hQB hvisc hx₀v
        he1 hr₁0 ((min_le_right _ _).trans (min_le_left _ _))
        (ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)))
        (hflat r₁ hr₁0 (min_le_left _ _))
      obtain ⟨r', hr', -, -, -, -, G, hGc, hGpos, hGfb⟩ := hnear
      -- the limit of `‖∇v‖` inside the positivity set of `v`
      have hx₀cl : x₀ ∈ closure (posSet v (ball x₀ ρ)) ∩ ball x₀ r' :=
        ⟨frontier_subset_closure hx₀v.1, mem_ball_self hr'⟩
      have hGt : Tendsto (fun y ↦ ‖G y‖) (𝓝[posSet v (ball x₀ ρ) ∩ ball x₀ r'] x₀)
          (𝓝 (Q x₀)) := by
        have h1 := (hGc x₀ hx₀cl).tendsto.norm
        rw [hGfb x₀ ⟨hx₀v, mem_ball_self hr'⟩] at h1
        exact h1.mono_left (nhdsWithin_mono _ (inter_subset_inter_left _ subset_closure))
      have hvt : Tendsto (fun y ↦ ‖∇ v y‖) (𝓝[posSet v (ball x₀ ρ)] x₀) (𝓝 (Q x₀)) := by
        rw [nhdsWithin_restrict _ (mem_ball_self hr') isOpen_ball]
        refine hGt.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with y hy
        rw [hGpos y hy]
      -- back to `u`
      rw [hPv] at hvt
      rw [nhdsWithin_restrict _ (mem_ball_self hρ) isOpen_ball]
      have hmono : posSet u U ∩ {y | 0 < σ * F y} ∩ ball x₀ ρ ⊆
          ball x₀ ρ ∩ {y | 0 < σ * F y} := fun y hy ↦ ⟨hy.2, hy.1.2⟩
      refine (hvt.mono_left (nhdsWithin_mono _ hmono)).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hSo : IsOpen (ball x₀ ρ ∩ {y | 0 < σ * F y}) :=
        isOpen_ball.inter (isOpen_lt continuous_const (continuous_const.mul hF.continuous))
      have heq : v =ᶠ[𝓝 y] u := by
        filter_upwards [hSo.mem_nhds (hmono hy)] with z hz
        rw [hv, indicator_of_mem hz.2]
      rw [heq.gradient_eq]
  -- combine the two sides
  have hsplit : posSet u U ∩ N ⊆
      (posSet u U ∩ {y | 0 < 1 * F y}) ∪ (posSet u U ∩ {y | 0 < -1 * F y}) := by
    rintro y ⟨hyP, hyN⟩
    have hFy : F y ≠ 0 := by
      intro h
      have : y ∈ ball x₀ r ∩ {y | F y = 0} := ⟨(hNV hyN).1, h⟩
      rw [← hFB] at this
      exact hu.notMem_posSet_of_mem_freeBoundary this.2 hyP
    rcases hFy.lt_or_gt with h | h
    · exact Or.inr ⟨hyP, by simp only [mem_setOf_eq]; linarith⟩
    · exact Or.inl ⟨hyP, by simp only [mem_setOf_eq]; linarith⟩
  rw [nhdsWithin_restrict _ hxN hNo]
  refine Tendsto.mono_left ?_ (nhdsWithin_mono _ hsplit)
  rw [nhdsWithin_union]
  exact (hside 1 (Or.inl rfl)).sup (hside (-1) (Or.inr rfl))

end Main

end

end EllipticBernoulli
