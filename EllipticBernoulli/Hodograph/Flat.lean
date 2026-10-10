/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Regularity
import EllipticBernoulli.Flatness.Classical
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Lipschitz.Estimate
import EllipticBernoulli.Nondegeneracy.Minimizer
import EllipticBernoulli.Sobolev.Uniqueness
import EllipticBernoulli.Sobolev.Energy
import EllipticBernoulli.Harmonic.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Flat blow-up implies classical regularity, with the free-boundary geometry

Let `u` be a continuous, non-negative local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` in an open
set `U`, and let `(y · e)₊` be a blow-up limit of `u` at the free-boundary point `x₀`. This file
produces the data needed by the partial hodograph transform (`IsFlatChartData`): a radius `ρ` such
that, in `B_ρ(x₀)`,
* `u = 0` on `{(y - x₀) · e ≤ -ρ/4}` and `u > 0` on `{(y - x₀) · e ≥ ρ/4}`;
* `∇u` extends continuously (as `G`) to `\overline{{u > 0}}`, with `|G| = 1` on the free boundary,
  `G(x₀) = e` and `G · e ≥ 1/2`.

## Main results

* `IsLocalEnergyMinimizer.isDownwardMinimizer`: a continuous local minimizer which is harmonic in
  `{u > 0}` is a downward minimizer (the downward competitors are a subclass).
* `exists_scale_approx`: the blow-up hypothesis at a single small scale.
* `eq_zero_of_approx`: non-degeneracy upgrades closeness to `(y · e)₊` to vanishing on
  `{(y - x₀) · e ≤ -2σ}`.
* `exists_isFlatChartData`: the main result.

## Proof

Continuous local minimizers are viscosity solutions (`IsLocalEnergyMinimizer.isViscSolution`),
hence harmonic in `{u > 0}` (`IsViscSolution.harmonicOnNhd_posSet`) and locally Lipschitz
(`locallyLipschitzOn_of_isViscSuper`); they are downward minimizers, hence non-degenerate with the
constant `c = 1/(8 d e^{d/2})` (`IsDownwardMinimizer.exists_le_of_closedBall_subset`). At a small
scale `R`, `|u - (· - x₀) · e)₊| ≤ δ R` on `B_R(x₀)`. Non-degeneracy turns this into two-sided
flatness, and De Silva's theorem (`isClassicalNear_of_flat`) gives the continuous extension `G` of
`∇u`. The mean value theorem along the segment `x₀ + [R/4, R/2] e`, at arbitrarily small scales,
gives `G(x₀) · e = 1`, hence `G(x₀) = e` since `|G(x₀)| = 1`.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

open Set Filter Topology Metric InnerProductSpace MeasureTheory
open scoped ContDiff Gradient RealInnerProductSpace NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Data for the partial hodograph transform at a flat free-boundary point.** In `B_ρ(x₀) ⊆ U`,
`u` vanishes on `{(y - x₀) · e ≤ -ρ/4}` and is positive on `{(y - x₀) · e ≥ ρ/4}`, `u` is harmonic
in `{u > 0}`, and `∇u` extends continuously (as `G`) to `\overline{{u > 0}} ∩ B_ρ(x₀)` with
`|G| = 1` on the free boundary, `G(x₀) = e` and `G · e ≥ 1/2`. -/
structure IsFlatChartData (U : Set (E d)) (u : E d → ℝ) (x₀ e : E d) (ρ : ℝ) (G : E d → E d) :
    Prop where
  pos : 0 < ρ
  norm_e : ‖e‖ = 1
  isOpen : IsOpen U
  ball_subset : ball x₀ ρ ⊆ U
  continuousOn : ContinuousOn u U
  nonneg : ∀ y ∈ U, 0 ≤ u y
  harmonic : HarmonicOnNhd u (posSet u U)
  mem_freeBoundary : x₀ ∈ freeBoundary u U
  eq_zero : ∀ y ∈ ball x₀ ρ, ⟪y - x₀, e⟫ ≤ -(ρ / 4) → u y = 0
  pos_of_le : ∀ y ∈ ball x₀ ρ, ρ / 4 ≤ ⟪y - x₀, e⟫ → 0 < u y
  continuousOn_G : ContinuousOn G (closure (posSet u U) ∩ ball x₀ ρ)
  G_eq : ∀ y ∈ posSet u U ∩ ball x₀ ρ, G y = ∇ u y
  norm_G : ∀ y ∈ freeBoundary u U ∩ ball x₀ ρ, ‖G y‖ = 1
  inner_G : ∀ y ∈ closure (posSet u U) ∩ ball x₀ ρ, 1 / 2 ≤ ⟪G y, e⟫
  G_x₀ : G x₀ = e

/-- **Continuous local minimizers harmonic in `{u > 0}` are downward minimizers** (the downward
competitors `v ≤ u` are a subclass of the unconstrained ones; the energy of `u` does not depend on
the choice of weak gradient, by uniqueness of weak gradients). -/
theorem IsLocalEnergyMinimizer.isDownwardMinimizer {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hc : ContinuousOn u U) (hmin : IsLocalEnergyMinimizer U Q u)
    (hH : HarmonicOnNhd u (posSet u U)) : IsDownwardMinimizer U Q u := by
  obtain ⟨Gu, hGu, hmin⟩ := hmin
  have hP : IsOpen (posSet u U) := isOpen_posSet hU hc
  refine ⟨⟨Gu, hGu⟩, hP, ((HarmonicOnNhd.contDiffOn_top hP hH).of_le (by norm_cast)),
    fun x hx ↦ (hH x hx).2.self_of_nhds, ?_⟩
  intro x r hr hxr Gu' v Gv hu' hv _ hvu
  have hball : ball x r ⊆ U := ball_subset_closedBall.trans hxr
  have hae : ∀ᵐ y ∂(volume.restrict (ball x r)), Gu' y = Gu y :=
    HasWeakGradient.ae_eq_of_eqOn hU isOpen_ball hball hu'.1 hGu.1 (fun _ _ ↦ rfl)
  rw [energyJ_congr (fun _ _ ↦ rfl) hae]
  exact (hmin x r hr hxr).2.2.2 v Gv hv hvu (Eventually.of_forall fun _ ↦ trivial)

/-- **The blow-up hypothesis at one small scale.** If `(y · e)₊` is a blow-up limit of `u` at
`x₀ ∈ U`, then for every `δ > 0` and `R₀ > 0` there is `R ∈ (0, R₀]` with `B_R(x₀) ⊆ U` and
`|u(y) - ((y - x₀) · e)₊| ≤ δ R` on `B_R(x₀)`. -/
theorem exists_scale_approx {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d} (hU : IsOpen U)
    (hx₀ : x₀ ∈ U) (hblow : IsBlowupLimit u x₀ (fun y ↦ max ⟪y, e⟫ 0)) {δ R₀ : ℝ} (hδ : 0 < δ)
    (hR₀ : 0 < R₀) :
    ∃ R, 0 < R ∧ R ≤ R₀ ∧ ball x₀ R ⊆ U ∧
      ∀ y ∈ ball x₀ R, |u y - max ⟪y - x₀, e⟫ 0| ≤ δ * R := by
  obtain ⟨r, hr, hr0, hT⟩ := hblow
  obtain ⟨ε₀, hε₀, hε₀U⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 hT) (closedBall 0 1)
    (isCompact_closedBall 0 1)
  have hev := (Metric.tendstoUniformlyOn_iff.1 hunif) δ hδ
  have hsmall : ∀ᶠ n in atTop, r n < min R₀ ε₀ := hr0.eventually (gt_mem_nhds (lt_min hR₀ hε₀))
  obtain ⟨n, hn1, hn2⟩ := (hev.and hsmall).exists
  set R := r n with hRdef
  have hR : 0 < R := hr n
  refine ⟨R, hR, (hn2.trans_le (min_le_left _ _)).le,
    (ball_subset_ball (hn2.trans_le (min_le_right _ _)).le).trans hε₀U, fun y hy ↦ ?_⟩
  set z : E d := R⁻¹ • (y - x₀) with hz
  have hzB : z ∈ closedBall (0 : E d) 1 := by
    rw [mem_closedBall, dist_zero_right, hz, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR),
      inv_mul_le_iff₀ hR, mul_one, ← dist_eq_norm]
    exact (mem_ball.1 hy).le
  have h := hn1 z hzB
  have hxz : x₀ + R • z = y := by
    rw [hz, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]; abel
  have hmax : max ⟪z, e⟫ 0 = R⁻¹ * max ⟪y - x₀, e⟫ 0 := by
    rw [hz, real_inner_smul_left, mul_max_of_nonneg _ _ (inv_pos.2 hR).le, mul_zero]
  rw [Real.dist_eq, blowup, hxz, hmax] at h
  have h2 : u y - max ⟪y - x₀, e⟫ 0 = -(R * (R⁻¹ * max ⟪y - x₀, e⟫ 0 - u y / R)) := by
    field_simp; ring
  rw [h2, abs_neg, abs_mul, abs_of_pos hR, mul_comm]
  exact mul_le_mul_of_nonneg_right h.le hR.le

/-- **Non-degeneracy kills the flat side.** Suppose `|u - ((· - x₀) · e)₊| ≤ δ R` on
`B_R(x₀) ⊆ U`, `u ≥ 0` on `U`, and `sup_{B̄_r(z)} u ≥ c r` for every `z ∈ \overline{{u > 0}}` and
every `B̄_r(z) ⊆ U`. If `y ∈ B_{R/2}(x₀)` with `(y - x₀) · e ≤ -2σ`, `0 < σ ≤ R/4` and `δ R < c σ`,
then `u(y) = 0`. -/
theorem eq_zero_of_approx {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d} {c δ R σ : ℝ}
    (he : ‖e‖ = 1) (hnn : ∀ y ∈ U, 0 ≤ u y)
    (hnd : ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, c * r ≤ u y)
    (hRU : ball x₀ R ⊆ U) (happrox : ∀ y ∈ ball x₀ R, |u y - max ⟪y - x₀, e⟫ 0| ≤ δ * R)
    {y : E d} (hy : y ∈ ball x₀ (R / 2)) (hσ : 0 < σ) (hσR : σ ≤ R / 4)
    (hys : ⟪y - x₀, e⟫ ≤ -(2 * σ)) (hδ : δ * R < c * σ) : u y = 0 := by
  have hyU : y ∈ U := hRU (ball_subset_ball (by linarith) hy)
  by_contra hne
  have hpos : 0 < u y := lt_of_le_of_ne (hnn y hyU) (Ne.symm hne)
  have hsub : closedBall y σ ⊆ ball x₀ R := fun y' hy' ↦ by
    rw [mem_ball] at hy ⊢
    rw [mem_closedBall] at hy'
    linarith [dist_triangle y' y x₀]
  obtain ⟨y', hy', hcy'⟩ := hnd y (subset_closure ⟨hyU, hpos⟩) σ hσ (hsub.trans hRU)
  have hinner : ⟪y' - x₀, e⟫ < 0 := by
    have h1 : ⟪y' - x₀, e⟫ = ⟪y - x₀, e⟫ + ⟪y' - y, e⟫ := by
      rw [← inner_add_left]; congr 1; abel
    have h2 : ⟪y' - y, e⟫ ≤ σ := by
      calc ⟪y' - y, e⟫ ≤ ‖y' - y‖ * ‖e‖ := real_inner_le_norm _ _
        _ ≤ σ := by rw [he, mul_one, ← dist_eq_norm]; exact mem_closedBall.1 hy'
    linarith
  have := happrox y' (hsub hy')
  rw [max_eq_right hinner.le, sub_zero] at this
  linarith [le_abs_self (u y')]

theorem inner_self_of_norm' {e : E d} (he : ‖e‖ = 1) : ⟪e, e⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, he, one_pow]

/-- The derivative of `u` along the line `σ ↦ x₀ + σ e` at a point where `u` is differentiable. -/
theorem hasDerivAt_line {u : E d → ℝ} {x₀ e : E d} {σ : ℝ}
    (hu : DifferentiableAt ℝ u (x₀ + σ • e)) :
    HasDerivAt (fun s ↦ u (x₀ + s • e)) ⟪∇ u (x₀ + σ • e), e⟫ σ := by
  have hA : HasDerivAt (fun s : ℝ ↦ x₀ + s • e) e σ := by
    simpa using ((hasDerivAt_id σ).smul_const e).const_add x₀
  have := hu.hasFDerivAt.comp_hasDerivAt σ hA
  rwa [gradient, toDual_symm_apply]

/-- **`G(x₀) = e`.** Let `G` be a continuous extension of `∇u` to `\overline{{u > 0}} ∩ B_r(x₀)`
with `|G(x₀)| = 1`. If `(y · e)₊` is a blow-up limit of `u` at `x₀`, then `G(x₀) = e`: by the mean
value theorem on the segment `x₀ + [R/4, R/2] e` at arbitrarily small scales `R`,
`G(x₀) · e = 1`. -/
theorem eq_of_blowup {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d} {G : E d → E d} {r : ℝ}
    (hU : IsOpen U) (hx₀U : x₀ ∈ U) (he : ‖e‖ = 1) (hc : ContinuousOn u U)
    (hH : HarmonicOnNhd u (posSet u U)) (hr : 0 < r)
    (hx₀ : x₀ ∈ closure (posSet u U))
    (hGc : ContinuousOn G (closure (posSet u U) ∩ ball x₀ r))
    (hGeq : ∀ y ∈ posSet u U ∩ ball x₀ r, G y = ∇ u y) (hGn : ‖G x₀‖ = 1)
    (hblow : IsBlowupLimit u x₀ (fun y ↦ max ⟪y, e⟫ 0)) : G x₀ = e := by
  have hinner : ⟪G x₀, e⟫ = 1 := by
    by_contra hne
    set ε := |⟪G x₀, e⟫ - 1| / 20 with hε
    have hε0 : 0 < ε := by have := abs_pos.2 (sub_ne_zero.2 hne); positivity
    obtain ⟨κ, hκ, hκG⟩ := Metric.continuousWithinAt_iff.1
      (hGc x₀ ⟨hx₀, mem_ball_self hr⟩) ε hε0
    set δ := min ε (1 / 8) with hδ
    have hδ0 : 0 < δ := lt_min hε0 (by norm_num)
    obtain ⟨R, hR, hRle, hRU, happ⟩ := exists_scale_approx hU hx₀U hblow hδ0
      (show 0 < min κ r / 2 by positivity)
    have hmin0 : 0 < min κ r := lt_min hκ hr
    have hRκ : R < κ := by have := min_le_left κ r; linarith
    have hRr : R < r := by have := min_le_right κ r; linarith
    -- points of the segment
    have hpt : ∀ s, 0 ≤ s → s < R → x₀ + s • e ∈ ball x₀ R := fun s h0 h1 ↦ by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
        Real.norm_of_nonneg h0]; exact h1
    have happs : ∀ s, 0 ≤ s → s < R → |u (x₀ + s • e) - s| ≤ δ * R := fun s h0 h1 ↦ by
      have := happ _ (hpt s h0 h1)
      rwa [add_sub_cancel_left, real_inner_smul_left, inner_self_of_norm' he, mul_one,
        max_eq_left h0] at this
    have hpos : ∀ s, R / 4 ≤ s → s < R → x₀ + s • e ∈ posSet u U := fun s h0 h1 ↦ by
      refine ⟨hRU (hpt s (by linarith) h1), ?_⟩
      have := (abs_le.1 (happs s (by linarith) h1)).1
      have : δ * R ≤ R / 8 := by
        have := min_le_right ε (1 / 8 : ℝ); nlinarith
      linarith
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s ↦ u (x₀ + s • e))
      (fun s ↦ ⟪∇ u (x₀ + s • e), e⟫) (show R / 4 < R / 2 by linarith)
      (fun s hs ↦ (ContinuousAt.comp (f := fun s : ℝ ↦ x₀ + s • e)
        (hc.continuousAt (hU.mem_nhds (hpos s hs.1 (by linarith [hs.2])).1))
        (by fun_prop : Continuous fun s : ℝ ↦ x₀ + s • e).continuousAt).continuousWithinAt)
      (fun s hs ↦ hasDerivAt_line
        ((hH _ (hpos s hs.1.le (by linarith [hs.2]))).1.differentiableAt (by norm_num)))
    have hξP := hpos ξ hξ.1.le (by linarith [hξ.2])
    have hξB : x₀ + ξ • e ∈ ball x₀ r :=
      ball_subset_ball hRr.le (hpt ξ (by linarith [hξ.1]) (by linarith [hξ.2]))
    rw [← hGeq _ ⟨hξP, hξB⟩] at hslope
    have hd : dist (G (x₀ + ξ • e)) (G x₀) < ε := hκG ⟨subset_closure hξP, hξB⟩ (by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
        Real.norm_of_nonneg (by linarith [hξ.1])]; linarith [hξ.2])
    have h1 := happs (R / 2) (by linarith) (by linarith)
    have h2 := happs (R / 4) (by linarith) (by linarith)
    have hδε : δ ≤ ε := min_le_left _ _
    have hslope' : |⟪G (x₀ + ξ • e), e⟫ - 1| ≤ 8 * δ := by
      rw [hslope, abs_le]
      have hR4 : (R / 2 - R / 4) = R / 4 := by ring
      rw [hR4]
      constructor
      · rw [le_sub_iff_add_le, le_div_iff₀ (by linarith)]
        linarith [(abs_le.1 h1).1, (abs_le.1 h2).2]
      · rw [sub_le_iff_le_add, div_le_iff₀ (by linarith)]
        linarith [(abs_le.1 h1).2, (abs_le.1 h2).1]
    have hGG : |⟪G (x₀ + ξ • e), e⟫ - ⟪G x₀, e⟫| ≤ ‖G (x₀ + ξ • e) - G x₀‖ := by
      rw [← inner_sub_left]
      have := abs_real_inner_le_norm (G (x₀ + ξ • e) - G x₀) e
      rwa [he, mul_one] at this
    rw [dist_eq_norm] at hd
    have : |⟪G x₀, e⟫ - 1| ≤ 9 * ε := by
      have := abs_sub_le (⟪G x₀, e⟫) (⟪G (x₀ + ξ • e), e⟫) 1
      rw [abs_sub_comm] at hGG
      linarith
    rw [hε] at this
    have h0 := abs_pos.2 (sub_ne_zero.2 hne)
    linarith
  have hsq : ‖G x₀ - e‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hGn, he, hinner]; norm_num
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq))

/-- **Flat blow-up gives the hodograph data** (De Silva (2011), with non-degeneracy from
Velichkov (2023)). For `d ≥ 2`, a continuous non-negative local minimizer of
`∫ |∇v|² + 1_{v>0}` in an open `U`, at a free-boundary point `x₀` where `(y · e)₊` is a blow-up
limit, satisfies `IsFlatChartData U u x₀ e ρ G` for some `ρ > 0` and `G`. -/
theorem exists_isFlatChartData (hd : 2 ≤ d) {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d}
    (hU : IsOpen U) (hc : ContinuousOn u U) (hnn : ∀ x ∈ U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) (hx₀ : x₀ ∈ freeBoundary u U)
    (he : ‖e‖ = 1) (hblow : IsBlowupLimit u x₀ (fun y ↦ max ⟪y, e⟫ 0)) :
    ∃ ρ G, IsFlatChartData U u x₀ e ρ G := by
  have hx₀U : x₀ ∈ U := hx₀.2
  have hvisc : IsViscSolution U (fun _ ↦ 1) u :=
    IsLocalEnergyMinimizer.isViscSolution hU continuousOn_const (fun _ _ ↦ zero_le_one) hc hnn
      hmin
  have hH : HarmonicOnNhd u (posSet u U) := IsViscSolution.harmonicOnNhd_posSet hU hvisc
  have hlip : LocallyLipschitzOn U u :=
    locallyLipschitzOn_of_isViscSuper hU hvisc.1 hH continuousOn_const
  have hdm := hmin.isDownwardMinimizer hU hc hH
  set c : ℝ := 1 / (8 * d * Real.exp ((d : ℝ) / 2)) with hcdef
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc0 : 0 < c := by positivity
  have hnd : ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, c * r ≤ u y := fun z hz r hr hsub ↦
    IsDownwardMinimizer.exists_le_of_closedBall_subset (by omega) hU hdm hlip hnn one_pos
      (fun _ _ ↦ le_rfl) ⟨1, fun _ _ ↦ le_rfl⟩ measurable_const z hz r hr hsub
  -- Step 1: two-sided flatness at a small scale, and De Silva's theorem
  obtain ⟨εbar, hεbar, Hc⟩ := isClassicalNear_of_flat hd 0 1 1 one_pos
  set m := min (εbar / 8) (1 / 4) with hm
  have hm0 : 0 < m := lt_min (by positivity) (by norm_num)
  set δ₁ := min (εbar / 4) (c * m / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by positivity) (by positivity)
  obtain ⟨R₁, hR₁, hR₁le, hR₁U, happ₁⟩ :=
    exists_scale_approx hU hx₀U hblow hδ₁0 (show 0 < 2 * εbar by positivity)
  set r₁ := R₁ / 2 with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hδ₁ε : δ₁ * R₁ ≤ εbar * r₁ / 2 := by
    have := min_le_left (εbar / 4) (c * m / 2)
    rw [hr₁]; nlinarith
  have hflat : ∀ y ∈ ball x₀ r₁, (fun _ ↦ (1 : ℝ)) x₀ * max (⟪y - x₀, e⟫ - εbar * r₁) 0 ≤ u y ∧
      u y ≤ (fun _ ↦ (1 : ℝ)) x₀ * max (⟪y - x₀, e⟫ + εbar * r₁) 0 := by
    intro y hy
    have hyR : y ∈ ball x₀ R₁ := ball_subset_ball (by linarith) hy
    have hyU : y ∈ U := hR₁U hyR
    have hA := abs_le.1 (happ₁ y hyR)
    simp only [one_mul]
    constructor
    · refine max_le ?_ (hnn y hyU)
      linarith [le_max_left ⟪y - x₀, e⟫ 0]
    · by_cases hs : ⟪y - x₀, e⟫ ≤ -(εbar * r₁ / 2)
      · have hσ : 0 < min (εbar * R₁ / 8) (R₁ / 4) := lt_min (by positivity) (by positivity)
        have hσm : min (εbar * R₁ / 8) (R₁ / 4) = m * R₁ := by
          rw [hm, min_mul_of_nonneg _ _ hR₁.le]; congr 1 <;> ring
        have hzero : u y = 0 := by
          refine eq_zero_of_approx he hnn hnd hR₁U happ₁ hy hσ (min_le_right _ _) ?_ ?_
          · have := min_le_left (εbar * R₁ / 8) (R₁ / 4)
            rw [hr₁] at hs; linarith
          · rw [hσm]
            have := min_le_right (εbar / 4) (c * m / 2)
            nlinarith [mul_pos hc0 hm0]
        rw [hzero]; exact le_max_right _ _
      · push Not at hs
        refine le_trans ?_ (le_max_left _ _)
        rcases le_total 0 ⟪y - x₀, e⟫ with h0 | h0
        · rw [max_eq_left h0] at hA; linarith
        · rw [max_eq_right h0] at hA; linarith
  have hcl := Hc U (fun _ ↦ 1) u x₀ e r₁ hU (LipschitzWith.const 1).lipschitzOnWith
    (fun _ _ ↦ ⟨le_rfl, le_rfl⟩) hvisc hx₀ he hr₁0 (by linarith)
    ((ball_subset_ball (by linarith)).trans hR₁U) hflat
  obtain ⟨r₂, hr₂, hr₂U, -, -, -, G, hGc, hGeq, hGn⟩ := hcl
  -- Step 2: `G(x₀) = e`
  have hx₀cl : x₀ ∈ closure (posSet u U) := hx₀.1.1
  have hGx₀ : G x₀ = e := eq_of_blowup hU hx₀U he hc hH hr₂ hx₀cl hGc hGeq
    (hGn x₀ ⟨hx₀, mem_ball_self hr₂⟩) hblow
  -- Step 3: `G · e ≥ 1/2` near `x₀`
  obtain ⟨κ, hκ, hκG⟩ := Metric.continuousWithinAt_iff.1
    (hGc x₀ ⟨hx₀cl, mem_ball_self hr₂⟩) (1 / 2) (by norm_num)
  set ρ₁ := min r₂ κ with hρ₁
  have hρ₁0 : 0 < ρ₁ := lt_min hr₂ hκ
  -- Step 4: flatness at a scale below `ρ₁`
  set δ₄ := min (1 / 16) (c / 32) with hδ₄
  have hδ₄0 : 0 < δ₄ := lt_min (by norm_num) (by positivity)
  obtain ⟨R, hR, hRle, hRU, happ⟩ := exists_scale_approx hU hx₀U hblow hδ₄0 hρ₁0
  have hsub : ball x₀ (R / 2) ⊆ ball x₀ r₂ :=
    ball_subset_ball (by have := min_le_left r₂ κ; linarith)
  refine ⟨R / 2, G, ⟨by positivity, he, hU, (ball_subset_ball (by linarith)).trans hRU, hc, hnn,
    hH, hx₀, ?_, ?_, ?_, ?_, ?_, ?_, hGx₀⟩⟩
  · intro y hy hs
    refine eq_zero_of_approx he hnn hnd hRU happ hy (σ := R / 16) (by positivity) (by linarith)
      (by linarith) ?_
    have := min_le_right (1 / 16 : ℝ) (c / 32)
    nlinarith
  · intro y hy hs
    have hA := abs_le.1 (happ y (ball_subset_ball (by linarith) hy))
    have := min_le_left (1 / 16 : ℝ) (c / 32)
    have h2 : δ₄ * R ≤ R / 16 := by nlinarith
    linarith [le_max_left ⟪y - x₀, e⟫ 0]
  · exact hGc.mono (inter_subset_inter_right _ hsub)
  · exact fun y hy ↦ hGeq y ⟨hy.1, hsub hy.2⟩
  · exact fun y hy ↦ hGn y ⟨hy.1, hsub hy.2⟩
  · intro y hy
    have hyκ : dist y x₀ < κ := by
      have := mem_ball.1 hy.2; have := min_le_right r₂ κ; linarith
    have hd := hκG ⟨hy.1, hsub hy.2⟩ hyκ
    rw [dist_eq_norm, hGx₀] at hd
    have h1 : ⟪G y, e⟫ = 1 + ⟪G y - e, e⟫ := by
      rw [inner_sub_left, inner_self_of_norm' he]; ring
    have h2 : ⟪G y - e, e⟫ ≥ -‖G y - e‖ := by
      have := abs_real_inner_le_norm (G y - e) e
      rw [he, mul_one] at this
      linarith [neg_abs_le ⟪G y - e, e⟫]
    linarith

end EllipticBernoulli
