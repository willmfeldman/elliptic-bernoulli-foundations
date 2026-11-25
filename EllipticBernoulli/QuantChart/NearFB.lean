/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.QuantChart.ChartData
public import EllipticBernoulli.Hodograph.Field
import EllipticBernoulli.QuantChart.Hodograph
import EllipticBernoulli.QuantChart.HodographBounds
import EllipticBernoulli.QuantChart.FieldBounds
import EllipticBernoulli.QuantChart.Implicit
import EllipticBernoulli.Hodograph.Equation
import EllipticBernoulli.Harmonic.Basic
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Variational.OneSided
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Second and third derivatives near the free boundary of a flat minimizer

`exists_norm_iteratedFDeriv_le_near_freeBoundary`: for `d ≥ 2` there are `ε₄ > 0` and `C₀`
(depending on `d` only) such that, if `u` is an `ε`-flat minimizer in `B_1` with `0 < ε ≤ ε₄` and
`y` is a free-boundary point with `‖y‖ ≤ 3/8`, then `‖D²u‖ ≤ C₀` and `‖D³u‖ ≤ C₀` on
`{u > 0} ∩ B_{1/2048}(y)`.

## Proof

Take the fixed-size hodograph data at `y` (`exists_isFlatChartData_of_flat`): direction `e'`,
radius `1/8`, and transform `w` on the half ball of radius `r = 1/256` with
`|∇w - e'| ≤ η = 8 C ε`. The scaled estimates (`exists_hodograph_derivative_bounds`) bound `D²w`
and `D³w` on `T = B_{r/2} ∩ {z · e' > 0}`. On `{u > 0}` near `y`, `∇u = gradVec e' (∇w ∘ hodoMap)`
(`gradVec` is an involution), and `hodoMap` maps `B_{1/2048}(y) ∩ {u > 0}` into `T`. Faà di Bruno
bounds `K = gradVec e' ∘ ∇w` and its first two derivatives on `T`, and
`norm_iteratedFDeriv_le_of_gradient_eq_comp` concludes.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Nat

public section

namespace EllipticBernoulli

open Hodograph BasicElliptic

variable {d : ℕ}

/-- `gradVec e` is an involution where `p · e ≠ 0`. -/
theorem Hodograph.gradVec_gradVec {e p : E d} (he : ‖e‖ = 1) (hp : ⟪p, e⟫ ≠ 0) :
    gradVec e (gradVec e p) = p := by
  change ⟪gradVec e p, e⟫⁻¹ • (e - perpProj e (gradVec e p)) = p
  rw [inner_gradVec he, perpProj_gradVec he, inv_inv, neg_smul, sub_neg_eq_add,
    smul_add, smul_smul, mul_inv_cancel₀ hp, one_smul, perpProj]
  abel

/-- `gradVec e` is smooth on `B_{1/4}(e)`. -/
theorem Hodograph.contDiffOn_gradVec {e : E d} (he : ‖e‖ = 1) :
    ContDiffOn ℝ ∞ (gradVec e) (ball e (1 / 4)) := by
  have hne : ∀ p ∈ ball e (1 / 4), ⟪p, e⟫ ≠ 0 := fun p hp ↦ by
    have hpe : ‖p - e‖ < 1 / 4 := by rwa [mem_ball, dist_eq_norm] at hp
    have h1 : ⟪p, e⟫ = 1 + ⟪p - e, e⟫ := by rw [inner_sub_left, inner_self_of_norm he]; ring
    have h2 := abs_real_inner_le_norm (p - e) e
    rw [he, mul_one] at h2
    linarith [neg_abs_le ⟪p - e, e⟫]
  have hfun : gradVec e = fun p ↦ (⟪p, e⟫)⁻¹ • (e - (p - ⟪p, e⟫ • e)) := by
    funext p; simp [gradVec, perpProj]
  rw [hfun]
  have hi : ContDiff ℝ ∞ fun p : E d ↦ ⟪p, e⟫ := contDiff_id.inner ℝ contDiff_const
  exact (hi.contDiffOn.inv hne).smul (contDiff_const.sub (contDiff_id.sub
    (hi.smul contDiff_const))).contDiffOn

/-- The Riesz map `L ↦ ∇` as a real-linear map of norm `≤ 1`. -/
private noncomputable def gradL : (E d →L[ℝ] ℝ) →L[ℝ] E d :=
  LinearMap.mkContinuous
    { toFun := fun L ↦ (toDual ℝ (E d)).symm L
      map_add' := fun L M ↦ map_add _ L M
      map_smul' := fun c L ↦ by simp }
    1 fun L ↦ by simp

private theorem gradient_eq_gradL (w : E d → ℝ) : ∇ w = gradL ∘ fderiv ℝ w := by
  funext z; rfl

private theorem norm_gradL_le : ‖(gradL : (E d →L[ℝ] ℝ) →L[ℝ] E d)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- **Second and third derivatives near the free boundary of a flat minimizer.** -/
theorem exists_norm_iteratedFDeriv_le_near_freeBoundary (hd : 2 ≤ d) : ∃ ε₄ > 0, ∃ C₀ ≥ 0,
    ∀ {u : E d → ℝ} {e : E d} {ε : ℝ}, 0 < ε → ε ≤ ε₄ →
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ y ∈ freeBoundary u (ball 0 1), ‖y‖ ≤ 3 / 8 →
    ∀ z ∈ posSet u (ball 0 1) ∩ ball y (1 / 2048),
      ‖iteratedFDeriv ℝ 2 u z‖ ≤ C₀ ∧ ‖iteratedFDeriv ℝ 3 u z‖ ≤ C₀ := by
  obtain ⟨ε₃, hε₃, C, hC, HD⟩ := exists_isFlatChartData_of_flat (d := d) hd
  obtain ⟨η₀, hη₀, Ch, hCh, HB⟩ := exists_hodograph_derivative_bounds (d := d)
  obtain ⟨Mg, hMg⟩ := exists_bound_iteratedFDeriv_gradVec (d := d)
  set c := ndConst d with hcdef
  have hc0 : 0 < c := ndConst_pos hd
  have hc1 : c ≤ 1 := ndConst_le_one hd
  set D : ℝ := 1 + Ch * η₀ / (1 / 8 / 32) + Ch * η₀ / (1 / 8 / 32) ^ 2 with hD
  have hD1 : 1 ≤ D := by
    have : 0 ≤ Ch * η₀ / (1 / 8 / 32) := by positivity
    have : 0 ≤ Ch * η₀ / (1 / 8 / 32) ^ 2 := by positivity
    linarith
  set Mg' := max Mg 0 with hMg'
  have hMg0 : 0 ≤ Mg' := le_max_right _ _
  set A : ℝ := 2 * Mg' * D ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨min ε₃ (min (η₀ / (8 * C)) (min (1 / (128 * C)) (c / 4096))),
    lt_min hε₃ (lt_min (by positivity) (lt_min (by positivity) (by positivity))),
    max (A * (2 + A)) (2 * A * (2 + A) ^ 4), le_max_of_le_left (by positivity),
    fun {u e ε} hε hεle hc hnn hmin he hflat y hy hy3 z hz ↦ ?_⟩
  have hε3 : ε ≤ ε₃ := hεle.trans (min_le_left _ _)
  have hεη : 8 * C * ε ≤ η₀ := by
    have := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hεC : 8 * C * ε ≤ 1 / 16 := by
    have := hεle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hεc : ε ≤ c / 4096 :=
    hεle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨e', G, -, H, hGb⟩ := HD hε hε3 hc hnn hmin he hflat y hy hy3
  have he' := H.norm_e
  set η := 8 * C * ε with hη
  have hqη : ∀ z ∈ closure (posSet u (ball 0 1)) ∩ ball y (1 / 8),
      ‖gradVec e' (G z) - e'‖ ≤ η := fun z hz ↦ by
    have h := hGb z hz
    have h4 : ‖G z - e'‖ ≤ 1 / 4 := by linarith
    calc ‖gradVec e' (G z) - e'‖ ≤ 4 * ‖G z - e'‖ := norm_gradVec_sub_le he' h4
      _ ≤ η := by linarith
  obtain ⟨r', hr', hHA, h1, h2, hgw, hdiv, hbc, -, -⟩ := H.exists_hodograph_of_le hqη
  subst hr'
  set w := hodograph u y e' (1 / 8) with hw
  have HBw := HB he' (by norm_num) (by positivity) hεη h1 h2 hgw hdiv hbc
  set T : Set (E d) := ball 0 (1 / 8 / 32 / 2) ∩ openHalfSpace e' with hT
  have hTo : IsOpen T := isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
  have hTH : T ⊆ halfBall e' 0 (1 / 8 / 32) := fun z hz ↦
    ⟨ball_subset_closedBall (ball_subset_ball (by norm_num) hz.1),
      (show 0 ≤ ⟪z, e'⟫ from le_of_lt hz.2)⟩
  have hgradT : ∀ z' ∈ T, ‖∇ w z' - e'‖ ≤ η := fun z' hz' ↦ by
    have hn : halfBall e' 0 (1 / 8 / 32) ∈ 𝓝 z' :=
      Filter.mem_of_superset (hTo.mem_nhds hz') hTH
    have : ∇ w z' = gradientWithin w (halfBall e' 0 (1 / 8 / 32)) z' := by
      rw [gradientWithin, fderivWithin_of_mem_nhds hn, gradient]
    rw [this]; exact hgw z' (hTH hz')
  have hwsm : ∀ z' ∈ T, ContDiffAt ℝ ∞ w z' := fun z' hz' ↦ (HBw z' hz').1
  have hfd : ∀ z' ∈ T, ContDiffAt ℝ ∞ (fderiv ℝ w) z' := fun z' hz' ↦
    (hwsm z' hz').fderiv_right (by simp)
  have hgs : ContDiffOn ℝ ∞ (∇ w) T := fun z' hz' ↦ by
    rw [gradient_eq_gradL]
    exact (gradL.contDiff.contDiffAt.comp z' (hfd z' hz')).contDiffWithinAt
  have hmT : MapsTo (∇ w) T (ball e' (1 / 4)) := fun z' hz' ↦ by
    rw [mem_ball, dist_eq_norm]; linarith [hgradT z' hz']
  set K : E d → E d := gradVec e' ∘ ∇ w with hK
  have hKs : ContDiffOn ℝ ∞ K T := (contDiffOn_gradVec he').comp hgs hmT
  have hKb : ∀ i ≤ 2, ∀ z' ∈ T, ‖iteratedFDeriv ℝ i K z'‖ ≤ A := by
    intro i hi z' hz'
    have hbd := norm_iteratedFDerivWithin_comp_le (n := i) (contDiffOn_gradVec he') hgs
      (by exact_mod_cast le_top) isOpen_ball.uniqueDiffOn hTo.uniqueDiffOn hmT hz' (C := Mg')
      (D := D)
      (fun j hj ↦ by
        rw [iteratedFDerivWithin_of_isOpen j isOpen_ball (hmT hz')]
        exact (hMg e' he' _ (ball_subset_closedBall (hmT hz')) j (hj.trans hi)).trans
          (le_max_left _ _))
      (fun j hj1 hj2 ↦ by
        rw [iteratedFDerivWithin_of_isOpen j hTo hz', gradient_eq_gradL]
        refine (gradL.norm_iteratedFDeriv_comp_left (hfd z' hz') (by exact_mod_cast le_top)).trans
          ?_
        refine (mul_le_of_le_one_left (norm_nonneg _) norm_gradL_le).trans ?_
        rw [norm_iteratedFDeriv_fderiv]
        obtain ⟨-, hb2, hb3⟩ := HBw z' hz'
        have e1 : Ch * η / (1 / 8 / 32) ≤ Ch * η₀ / (1 / 8 / 32) := by gcongr
        have e2 : Ch * η / (1 / 8 / 32) ^ 2 ≤ Ch * η₀ / (1 / 8 / 32) ^ 2 := by gcongr
        have hj : j = 1 ∨ j = 2 := by omega
        rcases hj with rfl | rfl
        · rw [pow_one]
          have : 0 ≤ Ch * η₀ / (1 / 8 / 32) ^ 2 := by positivity
          linarith
        · have : 0 ≤ Ch * η₀ / (1 / 8 / 32) := by positivity
          nlinarith)
    rw [iteratedFDerivWithin_of_isOpen i hTo hz'] at hbd
    refine hbd.trans ?_
    have hfac : (i ! : ℝ) ≤ 2 := by
      have := Nat.factorial_le hi
      exact_mod_cast this
    have hDi : D ^ i ≤ D ^ 2 := pow_le_pow_right₀ hD1 hi
    have : 0 ≤ D ^ i := by positivity
    calc (i ! : ℝ) * Mg' * D ^ i ≤ 2 * Mg' * D ^ 2 := by gcongr
      _ = A := rfl
  -- the positive phase near `y` maps into `T`
  set O : Set (E d) := posSet u (ball 0 1) ∩ ball y (1 / 2048) with hO
  have hPo : IsOpen (posSet u (ball (0 : E d) 1)) := isOpen_posSet isOpen_ball hc
  have hOo : IsOpen O := hPo.inter isOpen_ball
  have hH : HarmonicOnNhd u (posSet u (ball 0 1)) :=
    IsViscSolution.harmonicOnNhd_posSet isOpen_ball (IsLocalEnergyMinimizer.isViscSolution
      isOpen_ball continuousOn_const (fun _ _ ↦ zero_le_one) hc hnn hmin)
  have hus : ContDiffOn ℝ ∞ u O := (HarmonicOnNhd.contDiffOn_top hPo hH).mono inter_subset_left
  have hrc : 2 * ε / c < 1 / 2 := by rw [div_lt_iff₀ hc0]; nlinarith
  obtain ⟨-, hye⟩ := abs_inner_le_of_mem_freeBoundary_of_flat hd hε hrc hc hnn hmin he hflat hy
    (by linarith)
  have ha : 2 * ε / c ≤ 2 / 4096 := by rw [div_le_iff₀ hc0]; nlinarith
  have hε4096 : ε ≤ 1 / 4096 := by
    have := hεc; have : c / 4096 ≤ 1 / 4096 := by linarith
    linarith
  have hsmall : ∀ y' ∈ O, ‖hodoMap u y e' y'‖ < 1 / 8 / 32 / 2 ∧ u y' < 1 / 8 / 32 / 2 := by
    intro y' hy'
    have hyy : ‖y' - y‖ < 1 / 2048 := by simpa [dist_eq_norm] using hy'.2
    have hupper : u y' ≤ ‖y' - y‖ + 2 * ε / c + ε := by
      have h1 := (abs_le.1 (hflat y' hy'.1.1)).2
      have h2 : max ⟪y', e⟫ 0 ≤ |⟪y', e⟫| := max_le (le_abs_self _) (abs_nonneg _)
      have h3 : |⟪y', e⟫| ≤ ‖y' - y‖ + |⟪y, e⟫| := by
        have : ⟪y', e⟫ = ⟪y' - y, e⟫ + ⟪y, e⟫ := by rw [inner_sub_left]; ring
        rw [this]
        refine (abs_add_le _ _).trans ?_
        have := abs_real_inner_le_norm (y' - y) e
        rw [he, mul_one] at this
        linarith
      linarith
    have hn : ‖hodoMap u y e' y'‖ ≤ ‖y' - y‖ + u y' := by
      rw [hodoMap]
      refine (norm_add_le _ _).trans (add_le_add (norm_perpProj_le he' _) ?_)
      rw [norm_smul, he', mul_one, Real.norm_of_nonneg (hnn y' hy'.1.1)]
    constructor <;> linarith
  have hmaps : MapsTo (hodoMap u y e') O T := fun y' hy' ↦ by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]; exact (hsmall y' hy').1
    · change 0 < ⟪hodoMap u y e' y', e'⟫
      rw [Hodograph.inner_hodoMap he']; exact hy'.1.2
  have hgrad : ∀ y' ∈ O, ∇ u y' = K (hodoMap u y e' y') := by
    intro y' hy'
    have hz'T := hmaps hy'
    have hzA := hHA (hTH hz'T)
    have hyy : ‖y' - y‖ < 1 / 2048 := by simpa [dist_eq_norm] using hy'.2
    have hpt : hodographPt u y e' (1 / 8) (hodoMap u y e' y') = y' := by
      refine H.hodographPt_hodoMap ((norm_perpProj_le he' _).trans_lt (by linarith)) ?_ hy'.1.2
        (by linarith [(hsmall y' hy').2])
      have := abs_real_inner_le_norm (y' - y) e'
      rw [he', mul_one] at this
      linarith
    have hd := (H.hasFDerivAt_hodograph hzA hz'T.2).1
    rw [hpt] at hd
    have hgw' : ∇ w (hodoMap u y e' y') = gradVec e' (∇ u y') := by
      rw [gradient, hd.fderiv, LinearIsometryEquiv.symm_apply_apply]
    have hyB : y' ∈ ball y (1 / 8) := ball_subset_ball (by norm_num) hy'.2
    have hne : ⟪∇ u y', e'⟫ ≠ 0 := by
      have h := H.inner_G y' ⟨subset_closure hy'.1, hyB⟩
      rw [H.G_eq y' ⟨hy'.1, hyB⟩] at h
      linarith
    change ∇ u y' = gradVec e' (∇ w (hodoMap u y e' y'))
    rw [hgw', gradVec_gradVec he' hne]
  obtain ⟨hb2, hb3⟩ := norm_iteratedFDeriv_le_of_gradient_eq_comp hOo hTo hus he' hKs hmaps
    hgrad hKb hz
  exact ⟨hb2.trans (le_max_left _ _), hb3.trans (le_max_right _ _)⟩

end EllipticBernoulli
