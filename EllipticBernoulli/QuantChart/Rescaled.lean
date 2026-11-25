/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.QuantChart.Core
import EllipticBernoulli.QuantChart.Restrict
import EllipticBernoulli.QuantChart.Scaling
import EllipticBernoulli.Flatness.Classical
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Harmonic.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform bounds near free-boundary points away from the centre

`exists_bounds_at_freeBoundary`: for an `ε`-flat minimizer `u` in `B_1` (`0 < ε ≤ ε₅(d)`) and a
free-boundary point `y` with `‖y‖ ≤ 5/8`, on `{u > 0} ∩ B_{1/32}(y)` we have `‖∇u - e‖ ≤ C ε`,
`‖D²u‖ ≤ C` and `‖D³u‖ ≤ C`.

The rescaling `v(x) = 8 u(y + x/8)` is a minimizer in `B_1` (`IsLocalEnergyMinimizer.rescale`,
`IsLocalEnergyMinimizer.mono`). It is `(8 + 16/c) ε`-flat, because `|y · e| ≤ (2/c) ε`. The bounds
on `{v > 0} ∩ B_{1/4}` (`exists_norm_iteratedFDeriv_le_of_flat`,
`exists_norm_gradient_sub_le_of_flat_quarter`) transfer back through `u(w) = v(8(w - y))/8`
(Faà di Bruno with an affine inner map).
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Nat

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The affine map `w ↦ a + s w` has `‖D^i‖ ≤ s^i` for `i ≥ 1` (`s ≥ 0`). -/
private theorem norm_iteratedFDeriv_affine_le (a : E d) {s : ℝ} (hs : 0 ≤ s) {i : ℕ}
    (hi : 1 ≤ i) (w : E d) :
    ‖iteratedFDeriv ℝ i (fun w : E d ↦ a + s • w) w‖ ≤ s ^ i := by
  have hfd : fderiv ℝ (fun w : E d ↦ a + s • w) = fun _ ↦ s • ContinuousLinearMap.id ℝ (E d) := by
    funext w'; exact (((hasFDerivAt_id w').const_smul s).const_add a).fderiv
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero, norm_smul, Real.norm_of_nonneg hs, zero_add, pow_one]
    exact mul_le_of_le_one_right hs ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne hj.ne', Pi.zero_apply, norm_zero]; positivity

private theorem abs_max_add_sub_max_le' (a b : ℝ) : |max (a + b) 0 - max b 0| ≤ |a| := by
  rcases le_total 0 (a + b) with h1 | h1 <;> rcases le_total 0 b with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;> rw [abs_le] <;>
    constructor <;> linarith [le_abs_self a, neg_abs_le a]

/-- **Uniform bounds at free-boundary points with `‖y‖ ≤ 5/8`.** -/
theorem exists_bounds_at_freeBoundary (hd : 2 ≤ d) : ∃ ε₅ > 0, ∃ C₅ ≥ 0,
    ∀ {u : E d → ℝ} {e : E d} {ε : ℝ}, 0 < ε → ε ≤ ε₅ →
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ y ∈ freeBoundary u (ball 0 1), ‖y‖ ≤ 5 / 8 →
    ∀ z ∈ posSet u (ball 0 1) ∩ ball y (1 / 32),
      ‖∇ u z - e‖ ≤ C₅ * ε ∧ ‖iteratedFDeriv ℝ 2 u z‖ ≤ C₅ ∧
        ‖iteratedFDeriv ℝ 3 u z‖ ≤ C₅ := by
  obtain ⟨ε₀, hε₀, C₀, hC₀, H3⟩ := exists_norm_iteratedFDeriv_le_of_flat (d := d) hd
  obtain ⟨εg, hεg, Cg, hCg, HG⟩ := exists_norm_gradient_sub_le_of_flat_quarter (d := d) hd
  set c := ndConst d with hcdef
  have hc0 : 0 < c := ndConst_pos hd
  have hc1 : c ≤ 1 := ndConst_le_one hd
  set K : ℝ := 8 + 16 / c with hK
  have hK0 : 0 < K := by positivity
  set B : ℝ := max (max 16 (1 + ε₀)) C₀ with hB
  refine ⟨min (min (ε₀ / K) (εg / K)) (min (c / 64) (1 / (Cg * K))),
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity)),
    max (Cg * K) (6 * B * 8 ^ 3), le_max_of_le_left (by positivity),
    fun {u e ε} hε hεle hc hnn hmin he hflat y hy hy5 z hz ↦ ?_⟩
  have hε0 : K * ε ≤ ε₀ := by
    have := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ hK0] at this; linarith
  have hεg' : K * ε ≤ εg := by
    have := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ hK0] at this; linarith
  have hεc : ε ≤ c / 64 := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεCK : Cg * K * ε ≤ 1 := by
    have := hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hyr : ‖y‖ + 2 * ε / c < 1 := by
    have : 2 * ε / c ≤ 1 / 32 := by rw [div_le_iff₀ hc0]; nlinarith
    linarith
  obtain ⟨-, hye⟩ := abs_inner_le_of_mem_freeBoundary_of_flat_of_lt hd hε hc hnn hmin he hflat hy
    hyr
  -- the rescaled function
  set v : E d → ℝ := fun x ↦ u (y + (1 / 8 : ℝ) • x) / (1 / 8) with hv
  have hAB : ∀ x ∈ ball (0 : E d) 1, y + (1 / 8 : ℝ) • x ∈ ball (0 : E d) 1 := fun x hx ↦ by
    rw [mem_ball, dist_zero_right] at hx ⊢
    calc ‖y + (1 / 8 : ℝ) • x‖ ≤ ‖y‖ + ‖(1 / 8 : ℝ) • x‖ := norm_add_le _ _
      _ = ‖y‖ + 1 / 8 * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      _ < 1 := by linarith
  have hvmin : IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) v :=
    (hmin.rescale isOpen_ball y (by norm_num : (0 : ℝ) < 1 / 8)).mono
      (isOpen_ball.preimage (by fun_prop)) isOpen_ball fun x hx ↦ hAB x hx
  have hvc : ContinuousOn v (ball 0 1) :=
    (hc.comp (by fun_prop : Continuous fun x : E d ↦ y + (1 / 8 : ℝ) • x).continuousOn
      fun x hx ↦ hAB x hx).div_const _
  have hvnn : ∀ x ∈ ball (0 : E d) 1, 0 ≤ v x := fun x hx ↦
    div_nonneg (hnn _ (hAB x hx)) (by norm_num)
  have hvflat : ∀ x ∈ ball (0 : E d) 1, |v x - max ⟪x, e⟫ 0| ≤ K * ε := by
    intro x hx
    have h1 := hflat _ (hAB x hx)
    have h2 := abs_max_add_sub_max_le' (8 * ⟪y, e⟫) ⟪x, e⟫
    have h3 : 8 * max ⟪y + (1 / 8 : ℝ) • x, e⟫ 0 = max (8 * ⟪y, e⟫ + ⟪x, e⟫) 0 := by
      rw [inner_add_left, real_inner_smul_left, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 8),
        mul_zero]
      ring_nf
    have hv' : v x = 8 * u (y + (1 / 8 : ℝ) • x) := by rw [hv]; ring
    rw [hv']
    calc |8 * u (y + (1 / 8 : ℝ) • x) - max ⟪x, e⟫ 0|
        ≤ |8 * u (y + (1 / 8 : ℝ) • x) - 8 * max ⟪y + (1 / 8 : ℝ) • x, e⟫ 0| +
          |8 * max ⟪y + (1 / 8 : ℝ) • x, e⟫ 0 - max ⟪x, e⟫ 0| := abs_sub_le _ _ _
      _ ≤ 8 * ε + 8 * (2 * ε / c) := by
          gcongr
          · rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]; linarith
          · rw [h3]
            refine h2.trans ?_
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]; linarith
      _ = K * ε := by rw [hK]; ring
  have hKε : 0 < K * ε := by positivity
  -- the point `x = 8 (z - y)`
  set x : E d := (8 : ℝ) • (z - y) with hx
  have hxz : y + (1 / 8 : ℝ) • x = z := by rw [hx, smul_smul]; norm_num
  have hzy : ‖z - y‖ < 1 / 32 := by simpa [dist_eq_norm] using hz.2
  have hx4 : x ∈ ball (0 : E d) (1 / 4) := by
    rw [mem_ball, dist_zero_right, hx, norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith
  have hx1 : x ∈ ball (0 : E d) 1 := ball_subset_ball (by norm_num) hx4
  have hxP : x ∈ posSet v (ball 0 1) := ⟨hx1, by
    change 0 < u (y + (1 / 8 : ℝ) • x) / (1 / 8); rw [hxz]; have := hz.1.2; positivity⟩
  -- gradient
  have hH : HarmonicOnNhd u (posSet u (ball 0 1)) :=
    IsViscSolution.harmonicOnNhd_posSet isOpen_ball (IsLocalEnergyMinimizer.isViscSolution
      isOpen_ball continuousOn_const (fun _ _ ↦ zero_le_one) hc hnn hmin)
  have hud : DifferentiableAt ℝ u (y + (1 / 8 : ℝ) • x) := by
    rw [hxz]; exact (hH z hz.1).1.differentiableAt (by norm_num)
  have hgv : ∇ v x = ∇ u z := by
    have := gradient_rescale (c := 1) (by norm_num : (1 / 8 : ℝ) ≠ 0) hud
    rw [hxz] at this
    rw [show v = fun x ↦ u (y + (1 / 8 : ℝ) • x) / (1 / 8 * 1) by funext; simp [hv], this]
    simp
  have hgb := HG hKε hεg' hvc hvnn hvmin he hvflat x ⟨hxP, hx4⟩
  rw [hgv] at hgb
  have hgb2 : Cg * (K * ε) ≤ max (Cg * K) (6 * B * 8 ^ 3) * ε := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le
  refine ⟨hgb.trans hgb2, ?_⟩
  -- second and third derivatives, by Faà di Bruno
  set T : Set (E d) := posSet v (ball 0 1) ∩ ball 0 (1 / 4) with hT
  have hTo : IsOpen T := (isOpen_posSet isOpen_ball hvc).inter isOpen_ball
  have hvH : HarmonicOnNhd v (posSet v (ball 0 1)) :=
    IsViscSolution.harmonicOnNhd_posSet isOpen_ball (IsLocalEnergyMinimizer.isViscSolution
      isOpen_ball continuousOn_const (fun _ _ ↦ zero_le_one) hvc hvnn hvmin)
  have hvs : ContDiffOn ℝ ∞ v T :=
    (HarmonicOnNhd.contDiffOn_top (isOpen_posSet isOpen_ball hvc) hvH).mono inter_subset_left
  set S : Set (E d) := posSet u (ball 0 1) ∩ ball y (1 / 32) with hS
  have hSo : IsOpen S := (isOpen_posSet isOpen_ball hc).inter isOpen_ball
  set A : E d → E d := fun w ↦ (-(8 : ℝ) • y) + (8 : ℝ) • w with hA
  have hAw : ∀ w, y + (1 / 8 : ℝ) • A w = w := fun w ↦ by
    simp only [hA, smul_add, smul_smul]; norm_num
  have hmaps : MapsTo A S T := fun w hw ↦ by
    refine ⟨⟨by
      rw [mem_ball, dist_zero_right] at *
      have := hAB (A w)
      have hw' : ‖w - y‖ < 1 / 32 := by simpa [dist_eq_norm] using hw.2
      have : A w = (8 : ℝ) • (w - y) := by simp only [hA, smul_sub, neg_smul]; abel
      rw [this, norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith, by
      change 0 < u (y + (1 / 8 : ℝ) • A w) / (1 / 8); rw [hAw]; have := hw.1.2; positivity⟩, ?_⟩
    have hw' : ‖w - y‖ < 1 / 32 := by simpa [dist_eq_norm] using hw.2
    have : A w = (8 : ℝ) • (w - y) := by simp only [hA, smul_sub, neg_smul]; abel
    rw [mem_ball, dist_zero_right, this, norm_smul, Real.norm_of_nonneg (by norm_num)]; linarith
  have hAs : ContDiffOn ℝ ∞ A S := by fun_prop
  have hueq : u = fun w ↦ (1 / 8 : ℝ) * v (A w) := by
    funext w; simp only [hv, hAw]; ring
  have hvb : ∀ x' ∈ T, ∀ i ≤ 3, ‖iteratedFDeriv ℝ i v x'‖ ≤ B := by
    intro x' hx' i hi
    obtain ⟨b2, b3⟩ := H3 hKε hε0 hvc hvnn hvmin he hvflat x' hx'
    interval_cases i
    · rw [norm_iteratedFDeriv_zero]
      refine le_trans ?_ ((le_max_right 16 (1 + ε₀)).trans (le_max_left _ _))
      have h1 := (abs_le.1 (hvflat x' hx'.1.1)).2
      have h2 : max ⟪x', e⟫ 0 ≤ 1 := by
        refine max_le ?_ zero_le_one
        have := real_inner_le_norm x' e
        rw [he, mul_one] at this
        have : ‖x'‖ < 1 := by simpa using hx'.1.1
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (hvnn x' hx'.1.1)]
      nlinarith
    · rw [norm_iteratedFDeriv_one]
      refine le_trans ?_ ((le_max_left 16 (1 + ε₀)).trans (le_max_left _ _))
      have hgb' := HG hKε hεg' hvc hvnn hvmin he hvflat x' hx'
      have : ‖fderiv ℝ v x'‖ = ‖∇ v x'‖ := by
        rw [gradient, LinearIsometryEquiv.norm_map]
      rw [this]
      have := norm_le_norm_add_norm_sub' (∇ v x') e
      rw [he] at this
      nlinarith
    · exact b2.trans (le_max_right _ _)
    · exact b3.trans (le_max_right _ _)
  have hfdb : ∀ n ≤ 3, ‖iteratedFDeriv ℝ n (v ∘ A) z‖ ≤ n ! * B * 8 ^ n := by
    intro n hn
    have := norm_iteratedFDerivWithin_comp_le (n := n) hvs hAs (by exact_mod_cast le_top)
      hTo.uniqueDiffOn hSo.uniqueDiffOn hmaps hz (C := B) (D := 8)
      (fun i hi ↦ by
        rw [iteratedFDerivWithin_of_isOpen i hTo (hmaps hz)]
        exact hvb _ (hmaps hz) i (hi.trans hn))
      (fun i hi1 _ ↦ by
        rw [iteratedFDerivWithin_of_isOpen i hSo hz]
        exact norm_iteratedFDeriv_affine_le _ (by norm_num) hi1 z)
    rwa [iteratedFDerivWithin_of_isOpen n hSo hz] at this
  have hcomp : ∀ n ≤ 3, ‖iteratedFDeriv ℝ n u z‖ ≤ 6 * B * 8 ^ 3 := by
    intro n hn
    have hca : ContDiffAt ℝ ∞ (v ∘ A) z :=
      (hvs.comp hAs hmaps).contDiffAt (hSo.mem_nhds hz)
    have hL := (((1 / 8 : ℝ) • ContinuousLinearMap.id ℝ ℝ)).norm_iteratedFDeriv_comp_left
      (n := n) hca (by exact_mod_cast le_top)
    have hLn : ‖(1 / 8 : ℝ) • ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 := by
      rw [norm_smul]
      refine (mul_le_of_le_one_right (by norm_num) ContinuousLinearMap.norm_id_le).trans ?_
      norm_num
    have heq : u = ((1 / 8 : ℝ) • ContinuousLinearMap.id ℝ ℝ) ∘ (v ∘ A) := by
      rw [hueq]; funext w; simp
    rw [heq]
    refine hL.trans ((mul_le_of_le_one_left (norm_nonneg _) hLn).trans ((hfdb n hn).trans ?_))
    have hB0 : 0 ≤ B := le_max_of_le_left (le_max_of_le_left (by norm_num))
    have hf : (n ! : ℝ) ≤ 6 := by
      have := Nat.factorial_le hn
      have h6 : Nat.factorial 3 = 6 := rfl
      exact_mod_cast (h6 ▸ this)
    have hp : (8 : ℝ) ^ n ≤ 8 ^ 3 := pow_le_pow_right₀ (by norm_num) hn
    have hfin : (n ! : ℝ) * B * 8 ^ n ≤ 6 * B * 8 ^ 3 := by gcongr
    exact hfin
  exact ⟨(hcomp 2 (by norm_num)).trans (le_max_right _ _),
    (hcomp 3 le_rfl).trans (le_max_right _ _)⟩

end EllipticBernoulli
