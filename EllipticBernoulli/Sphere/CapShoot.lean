/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The shooting solution of the colatitude eigenvalue equation

For `m : ℕ` and `λ : ℝ`, the shooting solution `y = capShoot m λ` solves
`(sin^m y')' = -λ sin^m y` on `(0, π)` with `y(0) = 1`. It is the Volterra
series `y = ∑_j (-λ)^j T^j 1`, where
`T h (x) = ∫_0^x (∫_0^τ sin^m h) / sin^m τ dτ` (`capVolterra`).

For `0 ≤ σ ≤ τ ≤ b < π`, `sin^m σ ≤ c_b sin^m τ` with `c_b = max 1 (sin b)^{-m}`, so
`|T^j 1 (x)| ≤ (c_b b x)^j / j!` on `[0, b]`, and the series converges locally uniformly on
`[0, π) × ℝ`.

## Main definitions

* `capShoot m λ x`: the shooting solution `y(x, λ)`.
* `capShootFlux m λ x = -λ ∫_0^x sin^m y`: the flux `sin^m y'`.
* `capShootDeriv m λ x = capShootFlux m λ x / sin^m x`: the derivative `y'`.

## Main results

* `capShoot_zero_right`, `capShoot_zero_left`: `y(0, λ) = 1` and `y(x, 0) = 1`.
* `continuousOn_capShoot`: `(x, λ) ↦ y(x, λ)` is continuous on `[0, π) × ℝ`.
* `hasDerivAt_capShoot`: `y' = capShootDeriv` on `(0, π)`.
* `hasDerivAt_capShootFlux`: `(sin^m y')' = -λ sin^m y` on `(0, π)`.
* `continuousOn_capShootDeriv_left`: for fixed `λ`, `y'` is continuous on `[0, π)`.
* `continuousOn_capShootFlux`, `continuousOn_capShootDeriv`: joint continuity of the flux on
  `[0, π) × ℝ` and of `y'` on `(0, π) × ℝ`.
* `continuousAt_integral_capShoot_mul`: joint continuity of `∫_0^a sin^m y(·, λ) y(·, μ)`.

The solution is not differentiated in `λ`; the proof of Koch convexity (`CapKoch.lean`) uses only
the joint continuity (see `CapHadamard.lean`).
-/

open Set Filter Topology MeasureTheory Real
open scoped Nat

@[expose] public noncomputable section

namespace EllipticBernoulli

/-! ### Definitions -/

/-- The inner function of the Volterra operator: `τ ↦ (∫_0^τ sin^m h) / sin^m τ`. -/
def capVolterraInner (m : ℕ) (h : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (∫ σ in 0..τ, sin σ ^ m * h σ) / sin τ ^ m

/-- The Volterra operator `T h (x) = ∫_0^x (∫_0^τ sin^m h) / sin^m τ dτ`. -/
def capVolterra (m : ℕ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ τ in 0..x, capVolterraInner m h τ

/-- The terms `T^j 1` of the Volterra series. -/
def capShootTerm (m : ℕ) : ℕ → ℝ → ℝ
  | 0 => fun _ ↦ 1
  | j + 1 => capVolterra m (capShootTerm m j)

/-- **The shooting solution** `y(x, λ) = ∑_j (-λ)^j (T^j 1)(x)` of `(sin^m y')' = -λ sin^m y`,
`y(0) = 1`. It is meaningful for `x ∈ [0, π)`. -/
def capShoot (m : ℕ) (lam x : ℝ) : ℝ :=
  ∑' j : ℕ, (-lam) ^ j * capShootTerm m j x

/-- The flux `sin^m y' = -λ ∫_0^x sin^m y` of the shooting solution. -/
def capShootFlux (m : ℕ) (lam x : ℝ) : ℝ :=
  -lam * ∫ t in 0..x, sin t ^ m * capShoot m lam t

/-- The derivative `y'(x, λ) = capShootFlux m λ x / sin^m x` of the shooting solution (for
`x ∈ (0, π)`; its value at `x = 0` is `0`). -/
def capShootDeriv (m : ℕ) (lam x : ℝ) : ℝ :=
  capShootFlux m lam x / sin x ^ m

/-- The constant `c_b = max 1 (sin b)^{-m}` with `sin^m σ ≤ c_b sin^m τ` for
`0 ≤ σ ≤ τ ≤ b < π`. -/
def capVolterraConst (m : ℕ) (b : ℝ) : ℝ :=
  max 1 ((sin b)⁻¹ ^ m)

end EllipticBernoulli

end

open Set Filter Topology MeasureTheory Real
open scoped Nat Interval

public section

namespace EllipticBernoulli

variable {m : ℕ} {b : ℝ}

/-! ### The Volterra operator -/

theorem one_le_capVolterraConst (m : ℕ) (b : ℝ) : 1 ≤ capVolterraConst m b :=
  le_max_left _ _

/-- For `0 ≤ σ ≤ τ ≤ b < π`, `sin^m σ ≤ c_b sin^m τ`. -/
theorem sin_pow_le_capVolterraConst_mul {σ τ : ℝ} (hσ : 0 ≤ σ) (hστ : σ ≤ τ) (hτb : τ ≤ b)
    (hb : b < π) : sin σ ^ m ≤ capVolterraConst m b * sin τ ^ m := by
  have hsσ : 0 ≤ sin σ := sin_nonneg_of_nonneg_of_le_pi hσ (by linarith)
  have hsτ : 0 ≤ sin τ := sin_nonneg_of_nonneg_of_le_pi (hσ.trans hστ) (by linarith)
  rcases le_or_gt τ (π / 2) with h | h
  · have hle : sin σ ≤ sin τ := sin_le_sin_of_le_of_le_pi_div_two (by linarith) h hστ
    calc sin σ ^ m ≤ sin τ ^ m := pow_le_pow_left₀ hsσ hle m
      _ = 1 * sin τ ^ m := (one_mul _).symm
      _ ≤ capVolterraConst m b * sin τ ^ m :=
        mul_le_mul_of_nonneg_right (one_le_capVolterraConst m b) (pow_nonneg hsτ m)
  · have hb0 : 0 < sin b := sin_pos_of_pos_of_lt_pi (by linarith) hb
    have hbτ : sin b ≤ sin τ := by
      rw [← sin_pi_sub b, ← sin_pi_sub τ]
      exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    calc sin σ ^ m ≤ 1 := pow_le_one₀ hsσ (sin_le_one σ)
      _ = (sin b)⁻¹ ^ m * sin b ^ m := by rw [← mul_pow, inv_mul_cancel₀ hb0.ne', one_pow]
      _ ≤ (sin b)⁻¹ ^ m * sin τ ^ m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0.le hbτ m) (by positivity)
      _ ≤ capVolterraConst m b * sin τ ^ m :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hsτ m)

/-- `|T-inner h (τ)| ≤ c_b τ B` if `|h| ≤ B` on `[0, τ]` and `τ ∈ [0, b]`, `b < π`. -/
theorem abs_capVolterraInner_le {h : ℝ → ℝ} {τ B : ℝ} (hb : b < π) (hτ : τ ∈ Icc 0 b)
    (hB : ∀ σ ∈ Icc 0 τ, |h σ| ≤ B) :
    |capVolterraInner m h τ| ≤ capVolterraConst m b * τ * B := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 ⟨le_rfl, hτ.1⟩)
  have hC := one_le_capVolterraConst m b
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0; simp [capVolterraInner]
  have hsτ : 0 < sin τ := sin_pos_of_pos_of_lt_pi hpos (hτ.2.trans_lt hb)
  have hint : ‖∫ σ in 0..τ, sin σ ^ m * h σ‖ ≤ capVolterraConst m b * sin τ ^ m * B * |τ - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (f := fun σ ↦ sin σ ^ m * h σ)
      fun σ hσ ↦ ?_
    rw [uIoc_of_le hpos.le] at hσ
    have hs := sin_pow_le_capVolterraConst_mul (m := m) hσ.1.le hσ.2 hτ.2 hb
    have hsσ : 0 ≤ sin σ := sin_nonneg_of_nonneg_of_le_pi hσ.1.le (by linarith [hτ.2, hσ.2])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hsσ m)]
    exact mul_le_mul hs (hB σ ⟨hσ.1.le, hσ.2⟩) (abs_nonneg _) (by positivity)
  rw [sub_zero, abs_of_pos hpos, Real.norm_eq_abs] at hint
  rw [capVolterraInner, abs_div, abs_of_pos (pow_pos hsτ m), div_le_iff₀ (pow_pos hsτ m)]
  nlinarith

/-- The Volterra inner function of a function continuous on `[0, b]`, `b < π`, is continuous on
`[0, b]`. -/
theorem continuousOn_capVolterraInner {h : ℝ → ℝ} (hb : b < π) (hh : ContinuousOn h (Icc 0 b)) :
    ContinuousOn (capVolterraInner m h) (Icc 0 b) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hprim : ContinuousOn (fun τ ↦ ∫ σ in 0..τ, sin σ ^ m * h σ) (Icc 0 b) := by
    rcases le_or_gt 0 b with hb0 | hb0
    · have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := b)
        (f := fun σ ↦ sin σ ^ m * h σ) ?_
      · rwa [uIcc_of_le hb0] at this
      rw [uIcc_of_le hb0]
      exact ((continuous_sin.pow m).continuousOn.mul hh).integrableOn_Icc
    · rw [Icc_eq_empty (not_le.2 hb0)]; exact continuousOn_empty _
  intro τ hτ
  rcases hτ.1.eq_or_lt with h0 | hpos
  · subst h0
    have hval : capVolterraInner m h 0 = 0 := by simp [capVolterraInner]
    rw [ContinuousWithinAt, hval]
    refine squeeze_zero_norm' (a := fun τ ↦ capVolterraConst m b * τ * B) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with τ' hτ'
      rw [Real.norm_eq_abs]
      exact abs_capVolterraInner_le hb hτ' fun σ hσ ↦ by
        simpa using hB σ ⟨hσ.1, hσ.2.trans hτ'.2⟩
    · have : Tendsto (fun τ ↦ capVolterraConst m b * τ * B) (𝓝 0)
          (𝓝 (capVolterraConst m b * 0 * B)) :=
        ((continuous_const.mul continuous_id).mul continuous_const).tendsto 0
      rw [mul_zero, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
  · have hs : sin τ ^ m ≠ 0 :=
      (pow_pos (sin_pos_of_pos_of_lt_pi hpos (hτ.2.trans_lt hb)) m).ne'
    exact (hprim τ hτ).div (continuous_sin.pow m).continuousWithinAt hs

/-- The Volterra operator maps functions continuous on `[0, b]` to functions continuous on
`[0, b]`. -/
theorem continuousOn_capVolterra {h : ℝ → ℝ} (hb0 : 0 ≤ b) (hb : b < π)
    (hh : ContinuousOn h (Icc 0 b)) : ContinuousOn (capVolterra m h) (Icc 0 b) := by
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := b)
    (f := capVolterraInner m h) ?_
  · rwa [uIcc_of_le hb0] at this
  rw [uIcc_of_le hb0]
  exact (continuousOn_capVolterraInner hb hh).integrableOn_Icc

/-- FTC for the primitive of a function continuous on `[0, b]`, at interior points. -/
theorem hasDerivAt_integral_of_continuousOn {f : ℝ → ℝ} {x : ℝ}
    (hf : ContinuousOn f (Icc 0 b)) (hx : x ∈ Ioo 0 b) :
    HasDerivAt (fun u ↦ ∫ t in 0..u, f t) (f x) x := by
  refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
  · refine (hf.mono ?_).intervalIntegrable
    rw [uIcc_of_le hx.1.le]; exact Icc_subset_Icc le_rfl hx.2.le
  · exact (hf.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  · exact hf.continuousAt (Icc_mem_nhds hx.1 hx.2)

theorem hasDerivAt_capVolterra {h : ℝ → ℝ} {x : ℝ} (hb : b < π)
    (hh : ContinuousOn h (Icc 0 b)) (hx : x ∈ Ioo 0 b) :
    HasDerivAt (capVolterra m h) (capVolterraInner m h x) x :=
  hasDerivAt_integral_of_continuousOn (continuousOn_capVolterraInner hb hh) hx

/-! ### The terms of the Volterra series -/

/-- The constant `A = c_b b` in the bound `|T^j 1 (x)| ≤ (A x)^j / j!`. -/
private theorem capVolterraConst_mul_nonneg (hb0 : 0 ≤ b) : 0 ≤ capVolterraConst m b * b :=
  mul_nonneg (zero_le_one.trans (one_le_capVolterraConst m b)) hb0

/-- The antiderivative of `A (A τ)^j / j!` is `(A τ)^{j+1} / (j+1)!`. -/
private theorem hasDerivAt_pow_div_factorial (A τ : ℝ) (j : ℕ) :
    HasDerivAt (fun t ↦ (A * t) ^ (j + 1) / ((j + 1)! : ℝ)) (A * ((A * τ) ^ j / (j ! : ℝ))) τ := by
  have h := (((hasDerivAt_id τ).const_mul A).pow (j + 1)).div_const ((j + 1)! : ℝ)
  convert h using 1
  · funext t; simp
  have hj : ((j ! : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [id, Nat.add_sub_cancel, mul_one]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- **Bounds for the Volterra terms.** For `0 ≤ b < π`, each `T^j 1`
is continuous on `[0, b]` and `|T^j 1 (x)| ≤ (c_b b x)^j / j!` there. -/
theorem continuousOn_capShootTerm_and_abs_le (hb0 : 0 ≤ b) (hb : b < π) (j : ℕ) :
    ContinuousOn (capShootTerm m j) (Icc 0 b) ∧
      ∀ x ∈ Icc 0 b, |capShootTerm m j x| ≤ (capVolterraConst m b * b * x) ^ j / j ! := by
  set A := capVolterraConst m b * b
  have hA : 0 ≤ A := capVolterraConst_mul_nonneg hb0
  induction j with
  | zero => exact ⟨continuousOn_const, fun x _ ↦ by simp [capShootTerm]⟩
  | succ j ih =>
    obtain ⟨hc, hbd⟩ := ih
    refine ⟨continuousOn_capVolterra hb0 hb hc, fun x hx ↦ ?_⟩
    have hinner : ∀ τ ∈ Icc 0 x,
        |capVolterraInner m (capShootTerm m j) τ| ≤ A * ((A * τ) ^ j / j !) := by
      intro τ hτ
      have hτb : τ ∈ Icc 0 b := ⟨hτ.1, hτ.2.trans hx.2⟩
      have h1 := abs_capVolterraInner_le (m := m) hb hτb (B := (A * τ) ^ j / j !)
        fun σ hσ ↦ (hbd σ ⟨hσ.1, hσ.2.trans hτb.2⟩).trans (by
          gcongr
          · exact mul_nonneg hA hσ.1
          · exact hσ.2)
      calc _ ≤ capVolterraConst m b * τ * ((A * τ) ^ j / j !) := h1
        _ ≤ A * ((A * τ) ^ j / j !) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτb.2
            (zero_le_one.trans (one_le_capVolterraConst m b)))
            (div_nonneg (pow_nonneg (mul_nonneg hA hτ.1) j) (by positivity))
    have hcx : ContinuousOn (capVolterraInner m (capShootTerm m j)) (Icc 0 x) :=
      (continuousOn_capVolterraInner hb hc).mono (Icc_subset_Icc le_rfl hx.2)
    have hint : ∫ τ in 0..x, A * ((A * τ) ^ j / j !) = (A * x) ^ (j + 1) / (j + 1)! := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun τ _ ↦ hasDerivAt_pow_div_factorial A τ j)
        ((by fun_prop : Continuous fun τ : ℝ ↦ A * ((A * τ) ^ j / j !)).intervalIntegrable 0 x)]
      simp
    change |∫ τ in 0..x, capVolterraInner m (capShootTerm m j) τ| ≤ _
    rw [← hint]
    refine (intervalIntegral.abs_integral_le_integral_abs hx.1).trans ?_
    refine intervalIntegral.integral_mono_on hx.1 ?_
      ((by fun_prop : Continuous fun τ : ℝ ↦ A * ((A * τ) ^ j / j !)).intervalIntegrable 0 x)
      hinner
    exact (hcx.abs).intervalIntegrable_of_Icc hx.1

/-! ### Summation -/

/-- Termwise interchange of a uniformly dominated series and an integral over `[0, x]`. -/
theorem hasSum_intervalIntegral_of_abs_le {f : ℕ → ℝ → ℝ} {M : ℕ → ℝ} {x : ℝ}
    (hx : x ∈ Icc 0 b) (hf : ∀ j, ContinuousOn (f j) (Icc 0 b))
    (hM : ∀ j, ∀ t ∈ Icc 0 b, |f j t| ≤ M j) (hs : Summable M) :
    HasSum (fun j ↦ ∫ t in 0..x, f j t) (∫ t in 0..x, ∑' j, f j t) := by
  have hsub : Ι 0 x ⊆ Icc 0 b := by
    rw [uIoc_of_le hx.1]; exact Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl hx.2)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun j _ ↦ M j)
    (fun j ↦ ((hf j).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (fun j ↦ Eventually.of_forall fun t ht ↦ hM j t (hsub ht))
    (Eventually.of_forall fun _ _ ↦ hs) intervalIntegrable_const
    (Eventually.of_forall fun t ht ↦ ?_)
  exact (hs.of_norm_bounded fun j ↦ hM j t (hsub ht)).hasSum

/-- Uniform summability of the Volterra series on `[0, b] × [-L, L]`. -/
private theorem abs_pow_mul_capShootTerm_le (hb0 : 0 ≤ b) (hb : b < π) {L lam x : ℝ}
    (hlam : |lam| ≤ L) (hx : x ∈ Icc 0 b) (j : ℕ) :
    |(-lam) ^ j * capShootTerm m j x| ≤ (L * (capVolterraConst m b * b * b)) ^ j / j ! := by
  have hA := capVolterraConst_mul_nonneg (m := m) hb0
  have h1 := (continuousOn_capShootTerm_and_abs_le (m := m) hb0 hb j).2 x hx
  have h2 : (capVolterraConst m b * b * x) ^ j / j ! ≤
      (capVolterraConst m b * b * b) ^ j / j ! := by
    gcongr
    · exact mul_nonneg hA hx.1
    · exact hx.2
  rw [abs_mul, abs_pow, abs_neg, mul_pow, mul_div_assoc]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hlam j) (h1.trans h2) (abs_nonneg _)
    (pow_nonneg ((abs_nonneg _).trans hlam) j)

theorem summable_capShoot (hb0 : 0 ≤ b) (hb : b < π) (lam : ℝ) {x : ℝ} (hx : x ∈ Icc 0 b) :
    Summable fun j ↦ (-lam) ^ j * capShootTerm m j x :=
  (Real.summable_pow_div_factorial _).of_norm_bounded fun j ↦
    abs_pow_mul_capShootTerm_le (m := m) hb0 hb le_rfl hx j

/-- `(x, λ) ↦ y(x, λ)` is continuous on `[0, b] × [-L, L]`. -/
theorem continuousOn_capShoot_Icc (hb0 : 0 ≤ b) (hb : b < π) (L : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ capShoot m p.2 p.1) (Icc 0 b ×ˢ Icc (-L) L) := by
  refine continuousOn_tsum (u := fun j ↦ (L * (capVolterraConst m b * b * b)) ^ j / j !)
    (fun j ↦ ?_) (Real.summable_pow_div_factorial _) fun j p hp ↦ ?_
  · exact ((continuous_snd.neg.pow j).continuousOn).mul
      ((continuousOn_capShootTerm_and_abs_le hb0 hb j).1.comp continuous_fst.continuousOn
        fun p hp ↦ hp.1)
  · exact abs_pow_mul_capShootTerm_le hb0 hb (abs_le.2 hp.2) hp.1 j

/-- **Joint continuity of the shooting solution** on `[0, π) × ℝ`. -/
theorem continuousOn_capShoot (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ capShoot m p.2 p.1) (Ico 0 π ×ˢ univ) := by
  rintro ⟨x, lam⟩ ⟨hx, -⟩
  set b := (x + π) / 2
  have hxb : x < b := by simp only [b]; linarith [hx.2]
  have hb : b < π := by simp only [b]; linarith [hx.2]
  refine (continuousOn_capShoot_Icc (hx.1.trans hxb.le) hb (|lam| + 1) _
    ⟨⟨hx.1, hxb.le⟩, abs_le.1 (by linarith)⟩).mono_of_mem_nhdsWithin ?_
  have hopen : Iio b ×ˢ Ioo (-(|lam| + 1)) (|lam| + 1) ∈ 𝓝 (x, lam) :=
    prod_mem_nhds (Iio_mem_nhds hxb) (Ioo_mem_nhds (by linarith [abs_nonneg lam, neg_abs_le lam])
      (by linarith [le_abs_self lam]))
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hopen] with p hp hp'
  exact ⟨⟨hp.1.1, hp'.1.le⟩, Ioo_subset_Icc_self hp'.2⟩

/-- For fixed `λ`, `y(·, λ)` is continuous on `[0, π)`. -/
theorem continuousOn_capShoot_left (m : ℕ) (lam : ℝ) : ContinuousOn (capShoot m lam) (Ico 0 π) :=
  (continuousOn_capShoot m).comp (continuous_id.prodMk continuous_const).continuousOn
    fun _ hx ↦ ⟨hx, mem_univ _⟩

/-- A clamped version of `y` is continuous on `ℝ × ℝ`. -/
theorem continuous_capShoot_clamp (m : ℕ) (hb : b < π) :
    Continuous fun p : ℝ × ℝ ↦ capShoot m p.2 (max 0 (min p.1 b)) := by
  refine (continuousOn_capShoot m).comp_continuous
    ((continuous_const.max (continuous_fst.min continuous_const)).prodMk continuous_snd) ?_
  intro p
  exact ⟨⟨le_max_left _ _, max_lt pi_pos ((min_le_right _ _).trans_lt hb)⟩, mem_univ _⟩

theorem max_zero_min_eq {t : ℝ} (ht : t ∈ Icc 0 b) : max 0 (min t b) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

/-! ### Values -/

theorem capShootTerm_succ_zero (m j : ℕ) : capShootTerm m (j + 1) 0 = 0 := by
  simp [capShootTerm, capVolterra]

/-- `y(0, λ) = 1`. -/
@[simp]
theorem capShoot_zero_right (m : ℕ) (lam : ℝ) : capShoot m lam 0 = 1 := by
  rw [capShoot, tsum_eq_single 0]
  · simp [capShootTerm]
  · intro j hj
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [capShootTerm_succ_zero, mul_zero]

/-- `y(x, 0) = 1`. -/
@[simp]
theorem capShoot_zero_left (m : ℕ) (x : ℝ) : capShoot m 0 x = 1 := by
  rw [capShoot, tsum_eq_single 0]
  · simp [capShootTerm]
  · intro j hj
    simp [hj]

@[simp]
theorem capShootFlux_zero_right (m : ℕ) (lam : ℝ) : capShootFlux m lam 0 = 0 := by
  simp [capShootFlux]

@[simp]
theorem capShootDeriv_zero_right (m : ℕ) (lam : ℝ) : capShootDeriv m lam 0 = 0 := by
  simp [capShootDeriv]

/-! ### The integral equation -/

theorem capShootDeriv_eq_mul_capVolterraInner (m : ℕ) (lam x : ℝ) :
    capShootDeriv m lam x = -lam * capVolterraInner m (capShoot m lam) x := by
  rw [capShootDeriv, capShootFlux, capVolterraInner, mul_div_assoc]

/-- `y'` is continuous on `[0, b]` for `b < π`. -/
theorem continuousOn_capShootDeriv_Icc (lam : ℝ) (hb : b < π) :
    ContinuousOn (capShootDeriv m lam) (Icc 0 b) := by
  have h : ContinuousOn (capShoot m lam) (Icc 0 b) :=
    (continuousOn_capShoot_left m lam).mono fun x hx ↦ ⟨hx.1, hx.2.trans_lt hb⟩
  have := (continuousOn_capVolterraInner (m := m) hb h).const_smul (-lam)
  refine this.congr fun x _ ↦ ?_
  rw [capShootDeriv_eq_mul_capVolterraInner, Pi.smul_apply, smul_eq_mul]

/-- **The integral equation** `y(x) = 1 + ∫_0^x y'` on `[0, π)`. -/
theorem capShoot_eq_one_add_integral (hb0 : 0 ≤ b) (hb : b < π) (lam : ℝ) {x : ℝ}
    (hx : x ∈ Icc 0 b) : capShoot m lam x = 1 + ∫ τ in 0..x, capShootDeriv m lam τ := by
  set A := capVolterraConst m b * b
  have hA : 0 ≤ A := capVolterraConst_mul_nonneg hb0
  have hterm := continuousOn_capShootTerm_and_abs_le (m := m) hb0 hb
  -- inner interchange: `∑_j (-λ)^j ∫_0^τ sin^m T^j 1 = ∫_0^τ sin^m y`
  have hinner : ∀ τ ∈ Icc 0 b, HasSum
      (fun j ↦ (-lam) ^ (j + 1) * capVolterraInner m (capShootTerm m j) τ)
      (capShootDeriv m lam τ) := by
    intro τ hτ
    have h := hasSum_intervalIntegral_of_abs_le (b := b) hτ
      (f := fun j t ↦ sin t ^ m * ((-lam) ^ j * capShootTerm m j t))
      (M := fun j ↦ (|lam| * (A * b)) ^ j / j !)
      (fun j ↦ (continuous_sin.pow m).continuousOn.mul (continuousOn_const.mul (hterm j).1))
      (fun j t ht ↦ by
        rw [abs_mul, abs_of_nonneg (pow_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1
          (by linarith [ht.2])) m)]
        exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀
          (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2])) (sin_le_one t))).trans
          (abs_pow_mul_capShootTerm_le hb0 hb le_rfl ht j))
      (Real.summable_pow_div_factorial _)
    have hsum : ∀ t ∈ Icc 0 b, ∑' j, sin t ^ m * ((-lam) ^ j * capShootTerm m j t) =
        sin t ^ m * capShoot m lam t := fun t _ ↦ by rw [tsum_mul_left, capShoot]
    rw [intervalIntegral.integral_congr (g := fun t ↦ sin t ^ m * capShoot m lam t)
      fun t ht ↦ hsum t (by
        rw [uIcc_of_le hτ.1] at ht; exact ⟨ht.1, ht.2.trans hτ.2⟩)] at h
    have h' := (h.mul_left (-lam)).div_const (sin τ ^ m)
    convert h' using 1
    · funext j
      have e : ∫ t in 0..τ, sin t ^ m * ((-lam) ^ j * capShootTerm m j t) =
          (-lam) ^ j * ∫ t in 0..τ, sin t ^ m * capShootTerm m j t := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1; funext t; ring
      rw [capVolterraInner, pow_succ, e]
      ring
    · rw [capShootDeriv, capShootFlux]
  -- outer interchange
  have houter := hasSum_intervalIntegral_of_abs_le (b := b) hx
    (f := fun j τ ↦ (-lam) ^ (j + 1) * capVolterraInner m (capShootTerm m j) τ)
    (M := fun j ↦ |lam| * A * ((|lam| * (A * b)) ^ j / j !))
    (fun j ↦ continuousOn_const.mul (continuousOn_capVolterraInner hb (hterm j).1))
    (fun j τ hτ ↦ by
      have h1 := abs_capVolterraInner_le (m := m) hb hτ (B := (A * b) ^ j / j !)
        fun σ hσ ↦ ((hterm j).2 σ ⟨hσ.1, hσ.2.trans hτ.2⟩).trans (by
          gcongr
          · exact mul_nonneg hA hσ.1
          · exact hσ.2.trans hτ.2)
      have h2 : capVolterraConst m b * τ * ((A * b) ^ j / j !) ≤ A * ((A * b) ^ j / j !) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ.2
          (zero_le_one.trans (one_le_capVolterraConst m b)))
          (div_nonneg (pow_nonneg (mul_nonneg hA hb0) j) (by positivity))
      rw [abs_mul, abs_pow, abs_neg, pow_succ, mul_pow]
      calc |lam| ^ j * |lam| * |capVolterraInner m (capShootTerm m j) τ|
          ≤ |lam| ^ j * |lam| * (A * ((A * b) ^ j / j !)) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
        _ = |lam| * A * (|lam| ^ j * (A * b) ^ j / j !) := by ring)
    ((Real.summable_pow_div_factorial _).mul_left _)
  have hsplit := (summable_capShoot (m := m) hb0 hb lam hx).tsum_eq_zero_add
  rw [capShoot, hsplit]
  simp only [pow_zero, one_mul, capShootTerm]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun τ ↦ ∑' j, (-lam) ^ (j + 1) *
    capVolterraInner m (capShootTerm m j) τ) fun τ hτ ↦ by
      rw [uIcc_of_le hx.1] at hτ
      exact ((hinner τ ⟨hτ.1, hτ.2.trans hx.2⟩).tsum_eq).symm]
  rw [← houter.tsum_eq]
  congr 1
  funext j
  rw [capVolterra, intervalIntegral.integral_const_mul]

/-! ### Derivatives -/

/-- **`y' = capShootDeriv`** on `(0, π)`. -/
theorem hasDerivAt_capShoot (m : ℕ) (lam : ℝ) {x : ℝ} (hx : x ∈ Ioo 0 π) :
    HasDerivAt (capShoot m lam) (capShootDeriv m lam x) x := by
  set b := (x + π) / 2
  have hxb : x < b := by simp only [b]; linarith [hx.2]
  have hb : b < π := by simp only [b]; linarith [hx.2]
  have hb0 : 0 ≤ b := hx.1.le.trans hxb.le
  have hD := hasDerivAt_integral_of_continuousOn (continuousOn_capShootDeriv_Icc (m := m) lam hb)
    ⟨hx.1, hxb⟩
  refine (hD.const_add 1).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hxb] with t ht
  exact capShoot_eq_one_add_integral hb0 hb lam ⟨ht.1.le, ht.2.le⟩

/-- **The flux equation** `(sin^m y')' = -λ sin^m y` on `(0, π)`. -/
theorem hasDerivAt_capShootFlux (m : ℕ) (lam : ℝ) {x : ℝ} (hx : x ∈ Ioo 0 π) :
    HasDerivAt (capShootFlux m lam) (-(lam * sin x ^ m * capShoot m lam x)) x := by
  set b := (x + π) / 2
  have hxb : x < b := by simp only [b]; linarith [hx.2]
  have hb : b < π := by simp only [b]; linarith [hx.2]
  have hc : ContinuousOn (fun t ↦ sin t ^ m * capShoot m lam t) (Icc 0 b) :=
    (continuous_sin.pow m).continuousOn.mul
      ((continuousOn_capShoot_left m lam).mono fun t ht ↦ ⟨ht.1, ht.2.trans_lt hb⟩)
  have h := (hasDerivAt_integral_of_continuousOn hc ⟨hx.1, hxb⟩).const_mul (-lam)
  convert h using 1
  · funext y; rw [capShootFlux]
  · ring

/-- For fixed `λ`, `y'` is continuous on `[0, π)`. -/
theorem continuousOn_capShootDeriv_left (m : ℕ) (lam : ℝ) :
    ContinuousOn (capShootDeriv m lam) (Ico 0 π) := by
  intro x hx
  set b := (x + π) / 2
  have hxb : x < b := by simp only [b]; linarith [hx.2]
  have hb : b < π := by simp only [b]; linarith [hx.2]
  refine ((continuousOn_capShootDeriv_Icc (m := m) lam hb) x ⟨hx.1, hxb.le⟩).mono_of_mem_nhdsWithin
    ?_
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hxb)] with t ht ht'
  exact ⟨ht.1, ht'.le⟩

/-! ### Joint continuity of the flux and of parametric integrals -/

/-- **Joint continuity of the flux** on `[0, π) × ℝ`. -/
theorem continuousOn_capShootFlux (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ capShootFlux m p.2 p.1) (Ico 0 π ×ˢ univ) := by
  rintro ⟨x, lam⟩ ⟨hx, -⟩
  set b := (x + π) / 2
  have hxb : x < b := by simp only [b]; linarith [hx.2]
  have hb : b < π := by simp only [b]; linarith [hx.2]
  have hb0 : 0 ≤ b := hx.1.trans hxb.le
  have hY := continuous_capShoot_clamp m hb
  have hP := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume)
    (a₀ := 0) (f := fun (l : ℝ) (t : ℝ) ↦ sin t ^ m * capShoot m l (max 0 (min t b)))
    ((continuous_sin.comp continuous_snd).pow m |>.mul (hY.comp continuous_swap))
  have hG : Continuous fun p : ℝ × ℝ ↦
      -p.2 * ∫ t in 0..p.1, sin t ^ m * capShoot m p.2 (max 0 (min t b)) :=
    continuous_snd.neg.mul (hP.comp continuous_swap)
  refine (hG.continuousWithinAt (s := Icc 0 b ×ˢ univ)).congr_of_mem (fun p hp ↦ ?_)
    ⟨⟨hx.1, hxb.le⟩, mem_univ _⟩ |>.mono_of_mem_nhdsWithin ?_
  · simp only [capShootFlux]
    congr 1
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hp.1.1] at ht
    simp only [max_zero_min_eq ⟨ht.1, ht.2.trans hp.1.2⟩]
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (prod_mem_nhds (Iio_mem_nhds hxb) univ_mem)] with p hp hp'
    exact ⟨⟨hp.1.1, hp'.1.le⟩, mem_univ _⟩

/-- **Joint continuity of `y'`** on `(0, π) × ℝ`. -/
theorem continuousOn_capShootDeriv (m : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ ↦ capShootDeriv m p.2 p.1) (Ioo 0 π ×ˢ univ) := by
  refine ((continuousOn_capShootFlux m).mono
    (prod_mono Ioo_subset_Ico_self subset_rfl)).div
    ((continuous_sin.comp continuous_fst).pow m).continuousOn fun p hp ↦ ?_
  exact (pow_pos (sin_pos_of_pos_of_lt_pi hp.1.1 hp.1.2) m).ne'

/-- **Joint continuity of `∫_0^a sin^m y(·, λ) y(·, μ)`** at `a ∈ (0, π)`. -/
theorem continuousAt_integral_capShoot_mul (m : ℕ) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) (lam mu : ℝ) :
    ContinuousAt (fun q : ℝ × ℝ × ℝ ↦
      ∫ t in 0..q.1, sin t ^ m * (capShoot m q.2.1 t * capShoot m q.2.2 t)) (θ, lam, mu) := by
  set b := (θ + π) / 2
  have hθb : θ < b := by simp only [b]; linarith [hθ.2]
  have hb : b < π := by simp only [b]; linarith [hθ.2]
  have hb0 : 0 ≤ b := hθ.1.le.trans hθb.le
  have hY := continuous_capShoot_clamp m hb
  have hP := intervalIntegral.continuous_parametric_primitive_of_continuous (μ := volume)
    (a₀ := 0) (f := fun (p : ℝ × ℝ) (t : ℝ) ↦
      sin t ^ m * (capShoot m p.1 (max 0 (min t b)) * capShoot m p.2 (max 0 (min t b))))
    ((continuous_sin.comp continuous_snd).pow m |>.mul
      ((hY.comp (continuous_snd.prodMk (continuous_fst.comp continuous_fst))).mul
        (hY.comp (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))))
  have hG := (hP.comp ((continuous_snd.prodMk continuous_fst) :
    Continuous fun q : ℝ × ℝ × ℝ ↦ (q.2, q.1))).continuousAt (x := (θ, lam, mu))
  refine hG.congr_of_eventuallyEq ?_
  filter_upwards [(continuous_fst.tendsto (θ, lam, mu)).eventually (Ioo_mem_nhds hθ.1 hθb)]
    with q hq
  simp only [Function.comp_apply]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  rw [uIcc_of_le hq.1.le] at ht
  simp only [max_zero_min_eq ⟨ht.1, ht.2.trans hq.2.le⟩]

end EllipticBernoulli

end
