/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import Mathlib.Analysis.Calculus.Gradient.Basic
import EllipticBernoulli.Flatness.Classical
import EllipticBernoulli.Flatness.Graph
import EllipticBernoulli.Flatness.OneStep
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Harmonic.GradientEstimate
import EllipticBernoulli.Lipschitz.LinearGrowth

/-!
# A uniform gradient bound for flat solutions

`norm_gradient_sub_le_of_flat_uniform`: there are `ε₁, C₁ > 0` (depending on `d` only) such that,
if `v` is a viscosity solution with coefficient `1` in `U ⊇ B_1` and
`(x · e - ε)₊ ≤ v ≤ (x · e + ε)₊` on `B_1` with `0 < ε ≤ ε₁`, then `|∇v - e| ≤ C₁ ε` on
`{v > 0} ∩ B_{1/2}`.

## Proof

Let `y ∈ {v > 0} ∩ B_{1/2}`. If `v` has a zero within distance `1/64` of `y`, let `x₁` be a nearest
one, at distance `s`. Then `x₁` is a free-boundary point, and De Silva's pointwise expansion at
`x₁` with the interior gradient estimate (`norm_gradient_sub_le_of_flat`) gives
`|∇v(y) - ν(x₁)| ≤ 16 C_d C ε s^α`, while `|ν(x₁) - e| ≤ C ε`. Otherwise `B̄_{1/64}(y) ⊆ {v > 0}`,
where `|v - x · e| ≤ ε`, and the interior gradient estimate for the harmonic function
`v - x · e` gives `|∇v(y) - e| ≤ 64 C_d ε`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **A uniform gradient bound for flat solutions.** -/
theorem norm_gradient_sub_le_of_flat_uniform (hd : 2 ≤ d) : ∃ ε₁ > 0, ∃ C₁ > 0,
    ∀ (U : Set (E d)) (v : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
    IsViscSolution U (fun _ ↦ 1) v → ‖e‖ = 1 → 0 < ε → ε ≤ ε₁ →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ v y ∧ v y ≤ max (⟪y, e⟫ + ε) 0) →
    ∀ y ∈ posSet v U ∩ ball 0 (1 / 2), ‖∇ v y - e‖ ≤ C₁ * ε := by
  obtain ⟨ε₁, hε₁, α, hα, C, hC, H⟩ := exists_flatGraphData hd
  obtain ⟨Cd, hCd0, hCd⟩ := exists_norm_fderiv_le_div_of_harmonic (d := d) (by omega)
  refine ⟨ε₁, hε₁, 16 * Cd * C + C + 64 * Cd + 1, by positivity,
    fun U v e ε hU hB hv he hε hεle hflat y hy ↦ ?_⟩
  obtain ⟨ν, hG, hF⟩ := H U (fun _ ↦ 1) v e ε hU hB hv he hε hεle
    (fun _ _ ↦ by rw [sub_self, abs_zero]; positivity)
    ((LipschitzWith.const (1 : ℝ)).weaken bot_le).lipschitzOnWith hflat
  have hvH : HarmonicOnNhd v (posSet v U) := IsViscSolution.harmonicOnNhd_posSet hU hv
  have hnn : ∀ z ∈ ball (0 : E d) 1, 0 ≤ v z := fun z hz ↦ (le_max_right _ _).trans (hflat z hz).1
  have hcont : ContinuousOn v (ball (0 : E d) 1) := hv.1.1.mono hB
  obtain ⟨hyP, hy2⟩ := hy
  have hy2' : ‖y‖ < 1 / 2 := by simpa using hy2
  have hcb : closedBall y (1 / 64) ⊆ ball (0 : E d) 1 := fun z hz ↦ by
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z y
    linarith
  have hCε : 0 ≤ C * ε := by positivity
  by_cases hzero : ∃ z ∈ closedBall y (1 / 64), v z = 0
  · -- near the free boundary
    obtain ⟨x₁, hx₁B, hx₁0, hdist, hpos⟩ :=
      exists_nearest_zero hcont hnn hcb hyP.2 hzero
    set s := ‖y - x₁‖ with hs
    have hsd : dist x₁ y = s := by rw [dist_comm, dist_eq_norm]
    rw [hsd] at hdist hpos
    have hs64 : s ≤ 1 / 64 := by rw [← hsd]; exact hx₁B
    have hball : ball y s ⊆ posSet v U := fun z hz ↦
      ⟨hB (hcb (ball_subset_closedBall.trans (closedBall_subset_closedBall hs64) hz)), hpos z hz⟩
    have hx₁F : x₁ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) := by
      refine ⟨⟨⟨?_, fun hint ↦ ?_⟩, hB (hcb hx₁B)⟩, ?_⟩
      · have : x₁ ∈ closure (ball y s) := by
          rw [closure_ball y hdist.ne']; rw [mem_closedBall, hsd]
        exact closure_mono hball this
      · have := (interior_subset hint : x₁ ∈ posSet v U).2
        rw [hx₁0] at this; exact lt_irrefl _ this
      · rw [mem_closedBall, dist_eq_norm] at hx₁B
        rw [mem_ball, dist_zero_right]
        have := norm_le_norm_add_norm_sub' x₁ y
        linarith
    have hgrad := norm_gradient_sub_le_of_flat hCd0 hCd hvH (hF x₁ hx₁F) hCε hα.2.le one_pos
      (by norm_num) hdist (by linarith) hball le_rfl
    have hsα : s ^ α ≤ 1 := Real.rpow_le_one hdist.le (by linarith) hα.1.le
    have hν := (hG.normal x₁ hx₁F).1
    simp only [one_smul] at hgrad
    calc ‖∇ v y - e‖ ≤ ‖∇ v y - ν x₁‖ + ‖ν x₁ - e‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 16 * Cd * (C * ε) * 1 + C * ε := by
          gcongr
          exact hgrad.trans (mul_le_mul_of_nonneg_left hsα (by positivity))
      _ ≤ (16 * Cd * C + C + 64 * Cd + 1) * ε := by nlinarith [hCd0, hε]
  · -- away from the free boundary
    push Not at hzero
    have hsub : closedBall y (1 / 64) ⊆ posSet v U := fun z hz ↦
      ⟨hB (hcb hz), lt_of_le_of_ne (hnn z (hcb hz)) (Ne.symm (hzero z hz))⟩
    set h : E d → ℝ := fun x ↦ v x - (⟪x, e⟫ + 0) with hh
    have hhH : HarmonicOnNhd h (closedBall y (1 / 64)) := fun x hx ↦
      (hvH x (hsub hx)).sub (harmonicAt_inner_add e 0 x)
    have hbd : ∀ z ∈ closedBall y (1 / 64), |h z| ≤ ε := by
      intro z hz
      have hzpos := (hsub hz).2
      obtain ⟨h1, h2⟩ := hflat z (hcb hz)
      have h3 : v z ≤ ⟪z, e⟫ + ε := by
        rcases le_total 0 (⟪z, e⟫ + ε) with h0 | h0
        · rw [max_eq_left h0] at h2; exact h2
        · rw [max_eq_right h0] at h2; linarith
      simp only [hh, add_zero]
      rw [abs_le]
      constructor <;> linarith [le_max_left (⟪z, e⟫ - ε) 0]
    have hest := hCd h y (1 / 64) ε (by norm_num) hhH hbd
    have hvd : DifferentiableAt ℝ v y := (hvH y hyP).1.differentiableAt (by norm_num)
    have hlin : HasFDerivAt (fun x : E d ↦ ⟪x, e⟫ + 0) (toDual ℝ (E d) e) y := by
      have : (fun x : E d ↦ ⟪x, e⟫ + 0) = fun x ↦ toDual ℝ (E d) e x := by
        funext x; rw [toDual_apply_apply, real_inner_comm, add_zero]
      rw [this]; exact (toDual ℝ (E d) e).hasFDerivAt
    have hfd : fderiv ℝ h y = fderiv ℝ v y - toDual ℝ (E d) e :=
      (hvd.hasFDerivAt.sub hlin).fderiv
    rw [norm_gradient_sub_eq, ← hfd]
    calc ‖fderiv ℝ h y‖ ≤ Cd * ε / (1 / 64) := hest
      _ = 64 * Cd * ε := by ring
      _ ≤ (16 * Cd * C + C + 64 * Cd + 1) * ε := by nlinarith [hCd0, hε, hC]

end EllipticBernoulli
