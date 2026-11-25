/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Weiss
import EllipticBernoulli.TwoPhase.ACFCore
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sobolev.Energy
import EllipticBernoulli.Sobolev.Lattice
import EllipticBernoulli.Sobolev.Uniqueness
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Weiss monotonicity in a ball

Let `d ≥ 2`, let `U ⊆ ℝᵈ` be open with `B_R(x₀) ⊆ U`, and let `u` be a local minimizer of
`J(v, B) = ∫_B |∇v|² + 1_{v > 0}` in `U` (no sign condition) that is `L`-Lipschitz on
`B_R(x₀)`, with `u(x₀) = 0`. Then, for `0 < r < s < R`:

* `W(u, x₀, s) - W(u, x₀, r) ≥ D(u, x₀; r, s) ≥ 0`;
* `|W(u, x₀, r)| ≤ (L² + 1) |B₁| + L² σ(𝕊)`;
* **rigidity**: if `W(u, x₀, r) = W(u, x₀, s)`, then `u` is `1`-homogeneous about `x₀` on the
  annulus `r < |x - x₀| < s`.

This is `weissMonotoneLocal : WeissMonotoneLocalStatement`.

## Proof

Extend `u|_{B_R(x₀)}` to an `L`-Lipschitz `w` on `ℝᵈ` (McShane). The functionals `W` and `D` on
radii `< R` see `w` only on `B_R(x₀)`, where `w = u`
(`weissW_congr_of_eqOn_ball`,
`weissDefect_congr_of_eqOn_ball`). The only use of minimality in the global proof is the
homogeneous-competitor bound on `B_t(x₀)`. For `t < R` it follows from minimality of `u` in `U`
tested with `u + (v - w)` (`IsLocalEnergyMinimizer.energyJ_le_of_eqOn_ball`). Here `v` is a
Lipschitz competitor for `w` that agrees with `w` off `B_t(x₀)`, so `v - w` vanishes off `B_t(x₀)`
and no gluing of weak gradients is needed. The rest of the global argument applies verbatim on
`(0, R)`.

For rigidity, `D(u, x₀; r, s) = 0` forces `(x - x₀) · ∇u(x) = u(x)` a.e. on the annulus. As in
`homogeneous_of_ae_inner_gradient_eq`, for a.e. direction `z` the function `τ ↦ u(x₀ + τz)/τ` has
derivative `0` a.e. while `x₀ + τz` stays in the annulus. So it is constant there, and continuity
extends the identity to every point.

## References

* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped Gradient NNReal

namespace EllipticBernoulli

variable {d : ℕ}

public section

/-! ### Minimality tested in a ball -/

/-- The gradient of a difference of functions differentiable at `y`. -/
private theorem gradient_sub_apply {f g : E d → ℝ} {y : E d} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) : ∇ (fun x ↦ f x - g x) y = ∇ f y - ∇ g y := by
  have h : HasFDerivAt (fun x ↦ f x - g x) (fderiv ℝ f y - fderiv ℝ g y) y :=
    hf.hasFDerivAt.sub hg.hasFDerivAt
  rw [gradient, gradient, gradient, h.fderiv, map_sub]

/-- **Minimality in a ball against Lipschitz competitors.** Let `u` be a local minimizer of `J_Q`
in the open set `U`, with `B_R(x₀) ⊆ U`, and let `w` be Lipschitz on `ℝᵈ` with `w = u` on
`B_R(x₀)`. If `0 < t < R` and `v` is Lipschitz with `v = w` off `B_t(x₀)`, then
`J_Q(w, B_t(x₀)) ≤ J_Q(v, B_t(x₀))`, with pointwise gradients. -/
theorem IsLocalEnergyMinimizer.energyJ_le_of_eqOn_ball {U : Set (E d)} (hU : IsOpen U)
    {Q u : E d → ℝ} (hmin : IsLocalEnergyMinimizer U Q u) {x₀ : E d} {R : ℝ}
    (hRU : ball x₀ R ⊆ U) {w : E d → ℝ} {L : ℝ≥0} (hw : LipschitzWith L w)
    (hwu : EqOn u w (ball x₀ R)) {t : ℝ} (ht : 0 < t) (htR : t < R) {v : E d → ℝ} {K : ℝ≥0}
    (hv : LipschitzWith K v) (hvw : ∀ y ∉ ball x₀ t, v y = w y) :
    energyJ (ball x₀ t) Q w (∇ w) ≤ energyJ (ball x₀ t) Q v (∇ v) := by
  obtain ⟨G, hG, hm⟩ := hmin
  have hBU : closedBall x₀ t ⊆ U := (closedBall_subset_ball htR).trans hRU
  have htR' : ball x₀ t ⊆ ball x₀ R := ball_subset_ball htR.le
  -- the weak gradient of `u` is `∇w` a.e. on `B_R(x₀)`
  have hGw : ∀ᵐ y ∂(volume.restrict (ball x₀ R)), G y = ∇ w y :=
    hG.1.ae_eq_of_eqOn hU isOpen_ball hRU
      (memH1Loc_gradient_of_locallyLipschitzOn hU hw.locallyLipschitz.locallyLipschitzOn).1 hwu
  -- the competitor `u + (v - w)`
  set f : E d → ℝ := fun y ↦ v y - w y with hf
  have hfL : LipschitzWith (K + L) f := hv.sub hw
  have hf1 := memH1Loc_gradient_of_locallyLipschitzOn hU hfL.locallyLipschitz.locallyLipschitzOn
  have hH1 : MemH1Loc U (fun y ↦ u y + f y) (fun y ↦ G y + ∇ f y) :=
    ⟨hG.1.add hf1.1, fun C hCU hC ↦ ⟨(hG.2 C hCU hC).1.add (hf1.2 C hCU hC).1,
      (hG.2 C hCU hC).2.add (hf1.2 C hCU hC).2⟩⟩
  have hf0 : ∀ y ∉ ball x₀ t, f y = 0 := fun y hy ↦ by simp [hf, hvw y hy]
  have hle := (hm x₀ t ht hBU).2.2.2 (fun y ↦ u y + f y) (fun y ↦ G y + ∇ f y) hH1
    (ae_restrict_of_forall_mem (hU.measurableSet.diff measurableSet_ball) fun y hy ↦ by
      simp [hf0 y hy.2])
    (ae_of_all _ fun _ ↦ mem_univ _)
  have hGt : ∀ᵐ y ∂(volume.restrict (ball x₀ t)), G y = ∇ w y :=
    ae_restrict_of_ae_restrict_of_subset htR' hGw
  calc energyJ (ball x₀ t) Q w (∇ w) = energyJ (ball x₀ t) Q u G :=
        energyJ_congr (fun y hy ↦ (hwu (htR' hy)).symm) (hGt.mono fun y hy ↦ hy.symm)
    _ ≤ _ := hle
    _ = energyJ (ball x₀ t) Q v (∇ v) := by
        refine energyJ_congr (fun y hy ↦ ?_) ?_
        · simp only [hf, hwu (htR' hy)]; ring
        · filter_upwards [hGt, ae_restrict_of_ae hv.ae_differentiableAt,
            ae_restrict_of_ae hw.ae_differentiableAt] with y hy hvy hwy
          rw [hy, gradient_sub_apply hvy hwy]
          abel

/-! ### Congruence of the Weiss quantities -/

private theorem gradient_eq_of_eqOn_ball {u w : E d → ℝ} {x₀ : E d} {R : ℝ}
    (hwu : EqOn u w (ball x₀ R)) {x : E d} (hx : x ∈ ball x₀ R) : ∇ u x = ∇ w x := by
  have h : u =ᶠ[𝓝 x] w := Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx) hwu
  simp only [gradient, h.fderiv_eq]

/-- `W(u, x₀, t)` depends only on `u` on `B_R(x₀)` when `0 ≤ t < R`. -/
theorem weissW_congr_of_eqOn_ball {u w : E d → ℝ} {x₀ : E d} {R : ℝ}
    (hwu : EqOn u w (ball x₀ R)) {t : ℝ} (ht : 0 ≤ t) (htR : t < R) :
    weissW u x₀ t = weissW w x₀ t := by
  have htR' : ball x₀ t ⊆ ball x₀ R := ball_subset_ball htR.le
  have hJ : energyJ (ball x₀ t) (fun _ ↦ 1) u (∇ u) = energyJ (ball x₀ t) (fun _ ↦ 1) w (∇ w) :=
    energyJ_congr (fun y hy ↦ hwu (htR' hy))
      (ae_restrict_of_forall_mem measurableSet_ball fun y hy ↦
        gradient_eq_of_eqOn_ball hwu (htR' hy))
  have hM : ∀ ω : sphere (0 : E d) 1, u (x₀ + t • (ω : E d)) = w (x₀ + t • (ω : E d)) := by
    intro ω
    refine hwu ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere ω, mul_one,
      Real.norm_of_nonneg ht]
    exact htR
  simp only [weissW, hJ, hM]

/-- `D(u, x₀; r, s)` depends only on `u` on `B_R(x₀)` when `s ≤ R`. -/
theorem weissDefect_congr_of_eqOn_ball {u w : E d → ℝ} {x₀ : E d} {R : ℝ}
    (hwu : EqOn u w (ball x₀ R)) (r : ℝ) {s : ℝ} (hsR : s ≤ R) :
    weissDefect u x₀ r s = weissDefect w x₀ r s := by
  refine setIntegral_congr_fun (measurableSet_ball.diff measurableSet_ball) fun x hx ↦ ?_
  have hxR : x ∈ ball x₀ R := ball_subset_ball hsR hx.1
  simp only [hwu hxR, gradient_eq_of_eqOn_ball hwu hxR]

/-! ### Monotonicity for a Lipschitz function minimizing in a ball -/

section Global

variable {w : E d → ℝ} {L : ℝ≥0} {x₀ : E d} {R : ℝ}

/-- The hypothesis used below: `w` is `L`-Lipschitz and minimizes `J` on every `B_t(x₀)` with
`0 < t < R` against Lipschitz competitors that agree with `w` off `B_t(x₀)`. -/
private def MinimizesInBall (w : E d → ℝ) (x₀ : E d) (R : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → t < R → ∀ (v : E d → ℝ) (K : ℝ≥0), LipschitzWith K v →
    (∀ y ∉ ball x₀ t, v y = w y) →
    energyJ (ball x₀ t) (fun _ ↦ 1) w (∇ w) ≤ energyJ (ball x₀ t) (fun _ ↦ 1) v (∇ v)

/-- The homogeneous-competitor bound for `0 < t < R`. -/
private theorem ae_setIntegral_weissDensity_le_of_minimizesInBall (hd : 1 ≤ d)
    (hw : LipschitzWith L w) (hmin : MinimizesInBall w x₀ R) (hx₀ : w x₀ = 0) :
    ∀ᵐ t, 0 < t → t < R → ∫ x in ball x₀ t, weissDensity w x ≤
      t ^ d / d * (radialJ w x₀ t - radialA w x₀ t + radialM w x₀ t / t ^ 2) := by
  filter_upwards [ae_ae_differentiableAt_add_smul hd hw x₀] with t hdiff ht htR
  have hv := lipschitzWith_homogCompetitor hw hx₀ ht
  have hle := hmin t ht htR _ _ hv fun x hx ↦ homogCompetitor_eq_of_not_mem_ball hx₀ ht hx
  rw [energyJ_ball_gradient_eq hw, energyJ_ball_gradient_eq hv, ENNReal.ofReal_le_ofReal_iff
    (setIntegral_nonneg measurableSet_ball fun x _ ↦ weissDensity_nonneg _ x)] at hle
  rw [← setIntegral_weissDensity_homogCompetitor hd hw hx₀ ht (hdiff ht)]
  exact hle

/-- For a.e. `t ∈ (0, R)`, `W'(t) ≥ a(t)/t - 2k(t)/t² + m(t)/t³`. -/
private theorem ae_weissRate_le_deriv_weissW_of_minimizesInBall (hd : 1 ≤ d)
    (hw : LipschitzWith L w) (hmin : MinimizesInBall w x₀ R) (hx₀ : w x₀ = 0) :
    ∀ᵐ t, 0 < t → t < R → weissRate w x₀ t ≤ deriv (weissW w x₀) t := by
  filter_upwards [ae_hasDerivAt_setIntegral_weissDensity hd hw x₀,
    ae_hasDerivAt_radialM hd hw hx₀,
    ae_setIntegral_weissDensity_le_of_minimizesInBall hd hw hmin hx₀]
    with t hJ hm hle ht htR
  set Jb := fun s ↦ ∫ x in ball x₀ s, weissDensity w x with hJb
  have hWfun : weissW w x₀ = fun s ↦ Jb s / s ^ d - radialM w x₀ s / s ^ 2 :=
    funext (weissW_eq hw x₀)
  have hW : HasDerivAt (fun s ↦ Jb s / s ^ d - radialM w x₀ s / s ^ 2) _ t :=
    ((hJ ht).div (hasDerivAt_pow d t) (pow_ne_zero d ht.ne')).sub
      ((hm ht).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht.ne'))
  rw [hWfun, hW.deriv]
  set P := t ^ (d - 1)
  have hP : 0 < P := pow_pos ht _
  have htd : t ^ d = P * t := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hle' : d * Jb t ≤ P * t * (radialJ w x₀ t - radialA w x₀ t + radialM w x₀ t / t ^ 2) := by
    have := hle ht htR
    rw [htd] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hdpos] at this
    linarith
  rw [htd, weissRate]
  simp only [Nat.cast_ofNat, Nat.succ_sub_one, pow_one]
  have key : (P * radialJ w x₀ t * (P * t) - Jb t * (d * P)) / (P * t) ^ 2 -
      (2 * radialK w x₀ t * t ^ 2 - radialM w x₀ t * (2 * t)) / (t ^ 2) ^ 2 -
      (radialA w x₀ t / t - 2 * radialK w x₀ t / t ^ 2 + radialM w x₀ t / t ^ 3) =
      (P * t * (radialJ w x₀ t - radialA w x₀ t + radialM w x₀ t / t ^ 2) - d * Jb t) /
        (P * t ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (P * t * (radialJ w x₀ t - radialA w x₀ t + radialM w x₀ t / t ^ 2) - d * Jb t) /
      (P * t ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith

/-- `D(w, x₀; r, s) ≤ W(w, x₀, s) - W(w, x₀, r)` for `0 < r ≤ s < R`. -/
private theorem weissDefect_le_weissW_sub_of_minimizesInBall (hd : 1 ≤ d)
    (hw : LipschitzWith L w) (hmin : MinimizesInBall w x₀ R) (hx₀ : w x₀ = 0) {r s : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) (hsR : s < R) :
    weissDefect w x₀ r s ≤ weissW w x₀ s - weissW w x₀ r := by
  have hAC := absolutelyContinuousOnInterval_weissW hd hw hx₀ hr hrs
  rw [weissDefect_eq_integral_weissRate hd hw hx₀ hr hrs, ← hAC.integral_deriv_eq_sub]
  refine intervalIntegral.integral_mono_ae_restrict hrs
    (intervalIntegrable_weissRate hw hx₀ hr hrs) hAC.intervalIntegrable_deriv ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_weissRate_le_deriv_weissW_of_minimizesInBall hd hw hmin hx₀] with t ht htI
  exact ht (hr.trans_le htI.1) (htI.2.trans_lt hsR)

end Global

/-! ### Rigidity -/

/-- **Euler's relation on an annulus, integrated.** If `w` is Lipschitz and
`(x - x₀) · ∇w(x) = w(x)` for a.e. `x` with `r < |x - x₀| < s`, then
`w(x₀ + τ z) = τ w(x₀ + z)` whenever `τ > 0` and `|z|`, `τ |z|` both lie in `(r, s)`. -/
theorem homogeneous_of_ae_inner_gradient_eq_annulus {w : E d → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) {x₀ : E d} {r s : ℝ}
    (h : ∀ᵐ x, r < ‖x - x₀‖ → ‖x - x₀‖ < s → inner ℝ (x - x₀) (∇ w x) = w x) :
    ∀ τ : ℝ, 0 < τ → ∀ z : E d, r < ‖z‖ → ‖z‖ < s → r < τ * ‖z‖ → τ * ‖z‖ < s →
      w (x₀ + τ • z) = τ * w (x₀ + z) := by
  set G : Set (E d) := {y | DifferentiableAt ℝ w y ∧
    (r < ‖y - x₀‖ → ‖y - x₀‖ < s → inner ℝ (y - x₀) (∇ w y) = w y)} with hGdef
  have hGm : MeasurableSet G := by
    have h1 : Measurable fun y : E d ↦ ‖y - x₀‖ := (measurable_id.sub_const x₀).norm
    have e : {y : E d | r < ‖y - x₀‖ → ‖y - x₀‖ < s → inner ℝ (y - x₀) (∇ w y) = w y} =
        {y | r < ‖y - x₀‖}ᶜ ∪ ({y | ‖y - x₀‖ < s}ᶜ ∪ {y | inner ℝ (y - x₀) (∇ w y) = w y}) := by
      ext y; simp only [mem_ofPred_eq, mem_union, mem_compl_iff]; tauto
    have hP : MeasurableSet
        {y : E d | r < ‖y - x₀‖ → ‖y - x₀‖ < s → inner ℝ (y - x₀) (∇ w y) = w y} := by
      rw [e]
      exact (measurableSet_lt measurable_const h1).compl.union
        ((measurableSet_lt h1 measurable_const).compl.union
          (measurableSet_eq_fun ((measurable_id.sub_const x₀).inner (measurable_gradient w))
            hw.continuous.measurable))
    exact (measurableSet_of_differentiableAt ℝ w).inter hP
  have hGae : ∀ᵐ y, y ∈ G := hw.ae_differentiableAt.and h
  -- for a.e. `t`, a.e. `z` has `x₀ + t z ∈ G`
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ z : E d, x₀ + t • z ∈ G := by
    have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with t ht
    rw [ae_iff]
    have hnull : volume ((fun y : E d ↦ x₀ + y) ⁻¹' Gᶜ) = 0 := by
      rw [measure_preimage_add, show volume Gᶜ = 0 from ae_iff.1 hGae]
    change volume ((t • ·) ⁻¹' ((fun y : E d ↦ x₀ + y) ⁻¹' Gᶜ)) = 0
    rw [Measure.addHaar_preimage_smul volume ht, hnull, mul_zero]
  have hS : MeasurableSet {p : ℝ × E d | x₀ + p.1 • p.2 ∈ G} :=
    hGm.preimage (measurable_const.add measurable_smul)
  have h2 : ∀ᵐ z : E d, ∀ᵐ t : ℝ, x₀ + t • z ∈ G := (Measure.ae_ae_comm hS).1 h1
  -- for such `z`, `t ↦ w (x₀ + t z) / t` is constant while `x₀ + t z` stays in the annulus
  have key : ∀ᵐ z : E d, ∀ τ : ℝ, 0 < τ → r < ‖z‖ → ‖z‖ < s → r < τ * ‖z‖ → τ * ‖z‖ < s →
      w (x₀ + τ • z) = τ * w (x₀ + z) := by
    filter_upwards [h2] with z hz τ hτ hz1 hz2 hτ1 hτ2
    set ψ : ℝ → ℝ := fun t ↦ w (x₀ + t • z) * t⁻¹ with hψ
    have hmem : ∀ t ∈ uIcc 1 τ, 0 < t ∧ r < t * ‖z‖ ∧ t * ‖z‖ < s := by
      intro t ht
      have hlo : min 1 τ ≤ t := by simpa [uIcc] using ht.1
      have hhi : t ≤ max 1 τ := by simpa [uIcc] using ht.2
      have ht0 : 0 < t := (lt_min one_pos hτ).trans_le hlo
      have hzn : 0 ≤ ‖z‖ := norm_nonneg z
      refine ⟨ht0, ?_, ?_⟩
      · rcases le_total 1 τ with h1τ | h1τ
        · rw [min_eq_left h1τ] at hlo
          nlinarith
        · rw [min_eq_right h1τ] at hlo
          nlinarith
      · rcases le_total 1 τ with h1τ | h1τ
        · rw [max_eq_right h1τ] at hhi
          nlinarith
        · rw [max_eq_left h1τ] at hhi
          nlinarith
    have hAC : AbsolutelyContinuousOnInterval ψ 1 τ := by
      have hlin : LipschitzWith ‖z‖₊ fun t : ℝ ↦ x₀ + t • z := LipschitzWith.of_dist_le_mul
        fun t t' ↦ by
          rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
            coe_nnNorm, mul_comm]
      have hA : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ w (x₀ + t • z)) 1 τ :=
        (hw.comp hlin).lipschitzOnWith.absolutelyContinuousOnInterval
      have hB : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ t⁻¹) 1 τ :=
        ContDiffOn.absolutelyContinuousOnInterval
          ((contDiffOn_inv ℝ).mono fun t ht ↦ (hmem t ht).1.ne')
      exact hA.mul hB
    have hd : ∀ᵐ t, t ∈ uIcc 1 τ → HasDerivAt ψ 0 t := by
      filter_upwards [hz] with t ht htI
      obtain ⟨ht0, ht1, ht2⟩ := hmem t htI
      obtain ⟨hdiff, heul⟩ := ht
      have hn : ‖x₀ + t • z - x₀‖ = t * ‖z‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
      have heul' := heul (by rw [hn]; exact ht1) (by rw [hn]; exact ht2)
      have hv' : HasDerivAt (fun t : ℝ ↦ w (x₀ + t • z)) (fderiv ℝ w (x₀ + t • z) z) t := by
        have hl : HasDerivAt (fun t : ℝ ↦ x₀ + t • z) z t := by
          simpa using ((hasDerivAt_id t).smul_const z).const_add x₀
        exact hdiff.hasFDerivAt.comp_hasDerivAt t hl
      have hprod := hv'.mul (hasDerivAt_inv ht0.ne')
      convert hprod using 1
      rw [← inner_gradient_left_eq_fderiv, real_inner_comm]
      rw [add_sub_cancel_left, inner_smul_left, RCLike.conj_to_real] at heul'
      field_simp
      linear_combination (-1 : ℝ) * heul'
    obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hd
    have e1 := hC 1 left_mem_uIcc
    have e2 := hC τ right_mem_uIcc
    simp only [hψ, one_smul, inv_one, mul_one] at e1 e2
    rw [← e1] at e2
    field_simp at e2
    linarith
  -- all `z`, by continuity on the open set of admissible `z`
  intro τ hτ
  set O : Set (E d) := {z | r < ‖z‖ ∧ ‖z‖ < s ∧ r < τ * ‖z‖ ∧ τ * ‖z‖ < s} with hO
  have hOo : IsOpen O := by
    have hc : Continuous fun z : E d ↦ ‖z‖ := continuous_norm
    exact (isOpen_lt continuous_const hc).inter ((isOpen_lt hc continuous_const).inter
      ((isOpen_lt continuous_const (continuous_const.mul hc)).inter
        (isOpen_lt (continuous_const.mul hc) continuous_const)))
  have hae : ∀ᵐ z ∂(volume.restrict O), w (x₀ + τ • z) = τ * w (x₀ + z) := by
    rw [ae_restrict_iff' hOo.measurableSet]
    filter_upwards [key] with z hz hzO
    exact hz τ hτ hzO.1 hzO.2.1 hzO.2.2.1 hzO.2.2.2
  have heq := Measure.eqOn_open_of_ae_eq hae hOo
    (hw.continuous.comp (continuous_const.add (continuous_const_smul τ))).continuousOn
    (continuous_const.mul (hw.continuous.comp (continuous_const.add continuous_id))).continuousOn
  intro z hz1 hz2 hτ1 hτ2
  exact heq ⟨hz1, hz2, hτ1, hτ2⟩

/-- A vanishing defect `D(w, x₀; r, s) = 0` forces Euler's relation a.e. on the annulus. -/
private theorem ae_inner_gradient_eq_of_weissDefect_eq_zero_annulus {w : E d → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) {x₀ : E d} (hx₀ : w x₀ = 0) {r s : ℝ} (hr : 0 < r)
    (hD : weissDefect w x₀ r s = 0) :
    ∀ᵐ x, r < ‖x - x₀‖ → ‖x - x₀‖ < s → inner ℝ (x - x₀) (∇ w x) = w x := by
  set A : Set (E d) := ball x₀ s \ ball x₀ r with hA
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  set F : E d → ℝ := fun x ↦ ‖x - x₀‖ ^ (-(d : ℝ) - 2) * (inner ℝ (x - x₀) (∇ w x) - w x) ^ 2
  have hFm : Measurable F :=
    ((measurable_id.sub_const x₀).norm.pow_const _).mul
      ((((measurable_id.sub_const x₀).inner (measurable_gradient w)).sub
        hw.continuous.measurable).pow_const 2)
  have hFb : ∀ x ∈ A, ‖F x‖ ≤ r ^ (-(d : ℝ) - 2) * (2 * L * s) ^ 2 := by
    intro x hx
    have hxr : r ≤ ‖x - x₀‖ := by
      have := hx.2; rw [mem_ball, dist_eq_norm, not_lt] at this; exact this
    have hxs : ‖x - x₀‖ < s := by have := hx.1; rwa [mem_ball, dist_eq_norm] at this
    have hwx : |w x| ≤ L * ‖x - x₀‖ := by
      have := hw.dist_le_mul x x₀
      rwa [Real.dist_eq, hx₀, sub_zero, dist_eq_norm] at this
    have hin : |inner ℝ (x - x₀) (∇ w x)| ≤ ‖x - x₀‖ * L :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        (norm_gradient_le_of_lipschitzWith hw x) (norm_nonneg _))
    have h1 : |inner ℝ (x - x₀) (∇ w x) - w x| ≤ 2 * L * s := by
      have := abs_sub (inner ℝ (x - x₀) (∇ w x)) (w x)
      nlinarith [NNReal.coe_nonneg L]
    have hpw : ‖x - x₀‖ ^ (-(d : ℝ) - 2) ≤ r ^ (-(d : ℝ) - 2) :=
      Real.rpow_le_rpow_of_nonpos hr hxr (by linarith [(d.cast_nonneg : (0 : ℝ) ≤ d)])
    simp only [F]
    rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), norm_pow,
      Real.norm_eq_abs]
    exact mul_le_mul hpw (pow_le_pow_left₀ (abs_nonneg _) h1 2) (by positivity)
      (Real.rpow_nonneg hr.le _)
  have hFi : IntegrableOn F A :=
    Measure.integrableOn_of_bounded (M := r ^ (-(d : ℝ) - 2) * (2 * L * s) ^ 2)
      ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne hFm.aestronglyMeasurable
      ((ae_restrict_mem hAm).mono hFb)
  have hz := (setIntegral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x ↦ mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (sq_nonneg _)) hFi).1 hD
  rw [EventuallyEq, ae_restrict_iff' hAm] at hz
  filter_upwards [hz] with x hx hx1 hx2
  have hxA : x ∈ A := ⟨by rw [mem_ball, dist_eq_norm]; exact hx2,
    by rw [mem_ball, dist_eq_norm, not_lt]; exact hx1.le⟩
  have h0 := hx hxA
  simp only [Pi.zero_apply, mul_eq_zero] at h0
  rcases h0 with h | h
  · exact absurd h (Real.rpow_pos_of_pos (hr.trans hx1) _).ne'
  · have := pow_eq_zero_iff two_ne_zero |>.1 h
    linarith

/-! ### The statement -/

/-- **Weiss monotonicity in a ball, with rigidity** (after Weiss 1999). -/
theorem weissMonotoneLocal : WeissMonotoneLocalStatement := by
  intro d hd U u L x₀ R hU hRU hmin hu hx₀
  have hd1 : 1 ≤ d := by omega
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨fun r s hr hrs hsR ↦ ?_, fun r hr hrR ↦ ?_, fun r s hr hrs hsR ↦ ?_⟩ <;> linarith
  obtain ⟨w, hw, hwu⟩ := hu.extend_real
  have hwx₀ : w x₀ = 0 := by rw [← hwu (mem_ball_self hR)]; exact hx₀
  have hmin' : MinimizesInBall w x₀ R := fun t ht htR v K hv hvw ↦
    hmin.energyJ_le_of_eqOn_ball hU hRU hw hwu ht htR hv hvw
  have hmono : ∀ r s : ℝ, 0 < r → r < s → s < R →
      weissDefect u x₀ r s ≤ weissW u x₀ s - weissW u x₀ r := by
    intro r s hr hrs hsR
    rw [weissDefect_congr_of_eqOn_ball hwu r hsR.le,
      weissW_congr_of_eqOn_ball hwu (hr.trans hrs).le hsR,
      weissW_congr_of_eqOn_ball hwu hr.le (hrs.trans hsR)]
    exact weissDefect_le_weissW_sub_of_minimizesInBall hd1 hw hmin' hwx₀ hr hrs.le hsR
  refine ⟨fun r s hr hrs hsR ↦ ⟨hmono r s hr hrs hsR, weissDefect_nonneg _ _ _ _⟩,
    fun r hr hrR ↦ ?_, fun r s hr hrs hsR hW ↦ ?_⟩
  · rw [weissW_congr_of_eqOn_ball hwu hr.le hrR]
    exact abs_weissW_le hd1 hw hwx₀ hr
  · have hD : weissDefect w x₀ r s = 0 := by
      have h1 := hmono r s hr hrs hsR
      rw [hW, sub_self, weissDefect_congr_of_eqOn_ball hwu r hsR.le] at h1
      exact le_antisymm h1 (weissDefect_nonneg _ _ _ _)
    have hhom := homogeneous_of_ae_inner_gradient_eq_annulus hw
      (ae_inner_gradient_eq_of_weissDefect_eq_zero_annulus hw hwx₀ hr hD)
    intro x hx1 hx2 τ hτ hτ1 hτ2
    have h := hhom τ hτ (x - x₀) hx1 hx2 hτ1 hτ2
    rw [add_sub_cancel] at h
    have hxR : x ∈ ball x₀ R := by
      rw [mem_ball, dist_eq_norm]; linarith
    have hyR : x₀ + τ • (x - x₀) ∈ ball x₀ R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ.le]
      linarith
    rw [hwu hxR, hwu hyR]
    exact h

end

end EllipticBernoulli
