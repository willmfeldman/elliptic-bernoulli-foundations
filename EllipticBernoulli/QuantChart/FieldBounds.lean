/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Field
import EllipticBernoulli.QuantChart.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Uniform derivative bounds for the hodograph maps

* `exists_bound_iteratedFDeriv_gradVec`: `‖D^i gradVec e‖ ≤ M` on `B̄_{1/4}(e)` for `i ≤ 2`,
  uniformly in the unit vector `e`.
* `exists_bound_iteratedFDeriv_field`: `‖D^i (p ↦ field e (p + e))‖ ≤ M` on `B̄_{1/16}(0)` for
  `i ≤ 3`, uniformly in the unit vector `e`.

Both come from `exists_bound_iteratedFDeriv_slice`: the maps are jointly smooth in `(e, p)` where
`p · e` (resp. `(p + e) · e`) stays away from `0`, and the parameter sets are compact.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff RealInnerProductSpace

public section

namespace EllipticBernoulli.Hodograph

variable {d : ℕ}

private theorem inner_ge_of_norm_sub_le {e p : E d} (he : ‖e‖ = 1) {δ : ℝ} (hp : ‖p - e‖ ≤ δ) :
    1 - δ ≤ ⟪p, e⟫ := by
  have h1 : ⟪p, e⟫ = 1 + ⟪p - e, e⟫ := by rw [inner_sub_left, inner_self_of_norm he]; ring
  have h2 := abs_real_inner_le_norm (p - e) e
  rw [he, mul_one] at h2
  linarith [neg_abs_le ⟪p - e, e⟫]

/-- Uniform bounds for `gradVec e` near `e`. -/
theorem exists_bound_iteratedFDeriv_gradVec : ∃ M, ∀ e : E d, ‖e‖ = 1 →
    ∀ p ∈ closedBall e (1 / 4), ∀ i ≤ 2, ‖iteratedFDeriv ℝ i (gradVec e) p‖ ≤ M := by
  set O : Set (E d × E d) := {x | 1 / 2 < ⟪x.2, x.1⟫} with hO
  set K : Set (E d × E d) := {x | ‖x.1‖ = 1 ∧ ‖x.2 - x.1‖ ≤ 1 / 4} with hK
  have hOo : IsOpen O := isOpen_lt continuous_const (by fun_prop)
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_eq continuous_fst.norm continuous_const).inter
        (isClosed_le (continuous_snd.sub continuous_fst).norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : E d × E d)) (r := 2)).subset fun x hx ↦ ?_
      rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
      have := norm_le_norm_add_norm_sub' x.2 x.1
      exact ⟨by rw [hx.1]; norm_num, by linarith [hx.1, hx.2]⟩
  have hKO : K ⊆ O := fun x hx ↦ by
    have := inner_ge_of_norm_sub_le hx.1 hx.2
    change 1 / 2 < ⟪x.2, x.1⟫
    linarith
  set H : E d × E d → E d := fun x ↦ gradVec x.1 x.2 with hH
  have hHs : ContDiffOn ℝ ∞ H O := by
    have hfun : H = fun x ↦ (⟪x.2, x.1⟫)⁻¹ • (x.1 - (x.2 - ⟪x.2, x.1⟫ • x.1)) := by
      funext x; simp [hH, gradVec, perpProj]
    rw [hfun]
    have hi : ContDiff ℝ ∞ fun x : E d × E d ↦ ⟪x.2, x.1⟫ := contDiff_snd.inner ℝ contDiff_fst
    refine (hi.contDiffOn.inv fun x hx ↦ ?_).smul (contDiff_fst.sub (contDiff_snd.sub
      (hi.smul contDiff_fst))).contDiffOn
    have : (1 : ℝ) / 2 < ⟪x.2, x.1⟫ := hx
    linarith
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv_slice hOo hHs hKc hKO 2
  refine ⟨M, fun e he p hp i hi ↦ ?_⟩
  have hp' : ‖p - e‖ ≤ 1 / 4 := by rwa [mem_closedBall, dist_eq_norm] at hp
  exact hM (e, p) ⟨he, hp'⟩ i hi

/-- Uniform bounds for the shifted hodograph flux `p ↦ field e (p + e)` near `0`. -/
theorem exists_bound_iteratedFDeriv_field : ∃ M, ∀ e : E d, ‖e‖ = 1 →
    ∀ p ∈ closedBall (0 : E d) (1 / 16), ∀ i ≤ 3,
      ‖iteratedFDeriv ℝ i (fun p ↦ field e (p + e)) p‖ ≤ M := by
  set O : Set (E d × E d) := {x | 1 / 2 < ⟪x.2 + x.1, x.1⟫} with hO
  set K : Set (E d × E d) := {x | ‖x.1‖ = 1 ∧ ‖x.2‖ ≤ 1 / 16} with hK
  have hOo : IsOpen O := isOpen_lt continuous_const (by fun_prop)
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_eq continuous_fst.norm continuous_const).inter
        (isClosed_le continuous_snd.norm continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : E d × E d)) (r := 1)).subset fun x hx ↦ ?_
      rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
      exact ⟨by rw [hx.1], by linarith [hx.2]⟩
  have hKO : K ⊆ O := fun x hx ↦ by
    have := inner_ge_of_norm_sub_le hx.1 (p := x.2 + x.1) (δ := 1 / 16)
      (by rw [add_sub_cancel_right]; exact hx.2)
    change 1 / 2 < ⟪x.2 + x.1, x.1⟫
    linarith
  set H : E d × E d → E d := fun x ↦ field x.1 (x.2 + x.1) with hH
  have hHs : ContDiffOn ℝ ∞ H O := by
    set n : E d × E d → ℝ := fun x ↦ ⟪x.2 + x.1, x.1⟫ with hn
    set P : E d × E d → E d := fun x ↦ (x.2 + x.1) - ⟪x.2 + x.1, x.1⟫ • x.1 with hP
    have hfun : H = fun x ↦ (2 / n x) • P x + (1 - (1 + ‖P x‖ ^ 2) / n x ^ 2) • x.1 := by
      funext x; simp [hH, field, perpProj, hn, hP]
    have hnc : ContDiff ℝ ∞ n := (contDiff_snd.add contDiff_fst).inner ℝ contDiff_fst
    have hPc : ContDiff ℝ ∞ P :=
      (contDiff_snd.add contDiff_fst).sub (hnc.smul contDiff_fst)
    have hne : ∀ x ∈ O, n x ≠ 0 := fun x hx ↦ by
      have : (1 : ℝ) / 2 < n x := hx
      linarith
    rw [hfun]
    exact ((contDiffOn_const.div hnc.contDiffOn hne).smul hPc.contDiffOn).add
      ((contDiffOn_const.sub ((contDiffOn_const.add (hPc.norm_sq ℝ).contDiffOn).div
        (hnc.pow 2).contDiffOn fun x hx ↦ pow_ne_zero 2 (hne x hx))).smul contDiff_fst.contDiffOn)
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv_slice hOo hHs hKc hKO 3
  refine ⟨M, fun e he p hp i hi ↦ ?_⟩
  have hp' : ‖p‖ ≤ 1 / 16 := by rwa [mem_closedBall, dist_zero_right] at hp
  exact hM (e, p) ⟨he, hp'⟩ i hi

end EllipticBernoulli.Hodograph
