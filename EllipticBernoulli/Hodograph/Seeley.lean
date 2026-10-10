/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import EllipticBernoulli.Basic.Setting
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.LinearCombination

/-!
# Seeley extension across a hyperplane

A function that is `C^∞` on a closed half ball (derivatives taken within the half ball) is the
restriction of a function that is `C^∞` on a full ball of half the radius. We follow
R. T. Seeley, *Extension of `C^∞` functions defined in a half space*, Proc. Amer. Math. Soc. 15
(1964), 625–626.

Write `y = y' + t ν` with `y' ⊥ ν`. For `t ≥ 0` the extension is `f` itself, and for `t < 0` it is
`∑_k a_k φ(2^k t) f(y' - 2^k t ν)`, where `φ` is a cutoff equal to `1` near `0` and
`a_k = ∏_{j ≠ k} (1 + 2^j) / (2^j - 2^k)` are Seeley's coefficients.

## Main results

* `EllipticBernoulli.exists_contDiffOn_extension_halfSpace`: the extension theorem in `E d`.
* `Seeley.exists_contDiffOn_extension`: the same in any finite-dimensional real inner product space.
* `Seeley.hasSum_coeff_mul_pow`: the moment identities `∑_k a_k (-2^k)^j = 1` for all `j ≥ 0`, and
  `Seeley.summable_abs_coeff_mul_pow`: `∑_k |a_k| 2^{kj} < ∞` for all `j`.
* `Seeley.hasFTaylorSeriesUpToOn_of_hyperplane`: a gluing lemma. A candidate Taylor series that is
  continuous on an open set, and is a Taylor series off a hyperplane, is a Taylor series on the
  whole set.

## Proof notes

* The coefficients are limits of the Lagrange weights of the nodes `-2^0, …, -2^(N-1)` evaluated
  at `1`. The finite moment identities come from Lagrange interpolation of `X^j`, and pass to the
  limit by dominated convergence, using `|a_k| ≤ e^4 ∏_{j<k} (1 + 2^j)/(2^k - 2^j)` and the ratio
  test.
* Below the hyperplane each term is smooth (it is either a composition of `f` with a reflection
  into the open upper half ball, or locally zero), and its `m`-th derivative is bounded by
  `C_m 2^{km}` (Leibniz rule). Hence the derivatives of the series converge, and the series is
  differentiable termwise.
* At a point of the hyperplane, each derivative of the series tends to that of `f`: termwise the
  `m`-th derivative tends to `a_k D^m f(y) ∘ (R_k, …, R_k)`, and the multilinear form of the
  moment identities sums these to `D^m f(y)`. The gluing lemma, which rests on
  `hasFDerivWithinAt_closure_of_tendsto_fderiv`, then gives smoothness across the hyperplane.
-/

open Finset Filter Topology
open scoped ContDiff RealInnerProductSpace

public noncomputable section

namespace EllipticBernoulli

namespace Seeley

/-- The lower part `∏_{j < k} (1 + 2^j) / (2^j - 2^k)` of Seeley's coefficient. -/
def lowerProd (k : ℕ) : ℝ := ∏ j ∈ range k, (1 + (2 : ℝ) ^ j) / ((2 : ℝ) ^ j - 2 ^ k)

/-- The partial upper products `∏_{i < n} (1 + 2^(k+1+i)) / (2^(k+1+i) - 2^k)`. -/
def upperProd (k n : ℕ) : ℝ :=
  ∏ i ∈ range n, (1 + (2 : ℝ) ^ (k + 1 + i)) / ((2 : ℝ) ^ (k + 1 + i) - 2 ^ k)

/-- The Lagrange weights at the nodes `-2^0, …, -2^(N-1)`, evaluated at `1`. -/
def weight (N k : ℕ) : ℝ := ∏ j ∈ (range N).erase k, (1 + (2 : ℝ) ^ j) / ((2 : ℝ) ^ j - 2 ^ k)

/-- Seeley's coefficients `a_k = ∏_{j ≠ k} (1 + 2^j) / (2^j - 2^k)`. -/
def coeff (k : ℕ) : ℝ := lowerProd k * ⨆ n, upperProd k n

/-- The finite Lagrange identity: for `j < N`, `∑_{k < N} w_{N,k} (-2^k)^j = 1`. -/
theorem sum_weight_mul_pow {N j : ℕ} (hj : j < N) :
    ∑ k ∈ range N, weight N k * (-(2 : ℝ) ^ k) ^ j = 1 := by
  classical
  set v : ℕ → ℝ := fun k ↦ -(2 : ℝ) ^ k
  have hinj : Set.InjOn v (range N : Set ℕ) := by
    intro a _ b _ hab
    simp only [v, neg_inj] at hab
    exact Nat.pow_right_injective le_rfl (by exact_mod_cast hab)
  have hdeg : (Polynomial.X ^ j : Polynomial ℝ).degree < (range N).card := by
    rw [Polynomial.degree_X_pow, card_range]; exact_mod_cast hj
  have h := congrArg (Polynomial.eval 1) (Lagrange.eq_interpolate hinj hdeg)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at h
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, Polynomial.eval_mul,
    Polynomial.eval_C] at h
  rw [h]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [mul_comm]
  congr 1
  rw [Lagrange.basis, Polynomial.eval_prod, weight]
  refine prod_congr rfl fun i _ ↦ ?_
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, v]
  rw [div_eq_inv_mul]
  congr 1
  · congr 1; ring
  · ring

theorem weight_eq (k n : ℕ) : weight (k + 1 + n) k = lowerProd k * upperProd k n := by
  induction n with
  | zero =>
    simp only [add_zero, upperProd, range_zero, prod_empty, mul_one, weight, lowerProd]
    rw [range_add_one, erase_insert (by simp)]
  | succ n ih =>
    rw [upperProd, prod_range_succ, ← upperProd, ← mul_assoc, ← ih, weight, weight,
      show k + 1 + (n + 1) = (k + 1 + n) + 1 by ring, range_add_one,
      erase_insert_of_ne (by omega), prod_insert (by simp)]
    ring

/-- Each upper factor lies in `[1, 1 + 2 (1/2)^i]`. -/
private theorem upper_factor_bounds (k i : ℕ) :
    1 ≤ (1 + (2 : ℝ) ^ (k + 1 + i)) / ((2 : ℝ) ^ (k + 1 + i) - 2 ^ k) ∧
      (1 + (2 : ℝ) ^ (k + 1 + i)) / ((2 : ℝ) ^ (k + 1 + i) - 2 ^ k) ≤ 1 + 2 * (1 / 2) ^ i := by
  have ha : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hc : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  have hsplit : (2 : ℝ) ^ (k + 1 + i) = 2 * 2 ^ k * 2 ^ i := by ring
  have hd : 0 < (2 : ℝ) ^ (k + 1 + i) - 2 ^ k := by rw [hsplit]; nlinarith
  have hhalf : ((1 : ℝ) / 2) ^ i = 1 / 2 ^ i := by rw [div_pow, one_pow]
  constructor
  · rw [le_div_iff₀ hd]; linarith
  · rw [div_le_iff₀ hd, hhalf, hsplit]
    set u : ℝ := 1 / 2 ^ i
    have huc : u * 2 ^ i = 1 := by simp [u]
    have hu : u ≤ 1 := by simpa [u] using inv_le_one_of_one_le₀ hc
    have key : (1 + 2 * u) * (2 * 2 ^ k * 2 ^ i - 2 ^ k)
        = 2 * 2 ^ k * 2 ^ i + 3 * 2 ^ k - 2 * 2 ^ k * u := by
      linear_combination (4 * (2 : ℝ) ^ k) * huc
    rw [key]
    nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 2 ^ k)]

theorem one_le_upperProd (k n : ℕ) : 1 ≤ upperProd k n :=
  one_le_prod₀ fun i _ ↦ (upper_factor_bounds k i).1

theorem monotone_upperProd (k : ℕ) : Monotone (upperProd k) := by
  refine monotone_nat_of_le_succ fun n ↦ ?_
  have h := one_le_upperProd k n
  simp only [upperProd] at h ⊢
  rw [prod_range_succ]
  exact le_mul_of_one_le_right (zero_le_one.trans (one_le_upperProd k n))
    (upper_factor_bounds k n).1

theorem upperProd_le (k n : ℕ) : upperProd k n ≤ Real.exp 4 := by
  calc upperProd k n ≤ ∏ i ∈ range n, Real.exp (2 * (1 / 2) ^ i) := by
        refine prod_le_prod₀ (fun i _ ↦ zero_le_one.trans (upper_factor_bounds k i).1)
          fun i _ ↦ ?_
        refine (upper_factor_bounds k i).2.trans ?_
        linarith [Real.add_one_le_exp (2 * (1 / 2 : ℝ) ^ i)]
    _ = Real.exp (2 * ∑ i ∈ range n, (1 / 2 : ℝ) ^ i) := by
        rw [← Real.exp_sum, mul_sum]
    _ ≤ Real.exp 4 := by
        gcongr
        linarith [sum_geometric_two_le n]

theorem tendsto_upperProd (k : ℕ) :
    Tendsto (upperProd k) atTop (𝓝 (⨆ n, upperProd k n)) :=
  tendsto_atTop_ciSup (monotone_upperProd k) ⟨_, fun _ ⟨n, hn⟩ ↦ hn ▸ upperProd_le k n⟩

theorem iSup_upperProd_le (k : ℕ) : ⨆ n, upperProd k n ≤ Real.exp 4 :=
  ciSup_le fun n ↦ upperProd_le k n

theorem iSup_upperProd_nonneg (k : ℕ) : 0 ≤ ⨆ n, upperProd k n :=
  zero_le_one.trans ((one_le_upperProd k 0).trans
    (le_ciSup ⟨_, fun _ ⟨n, hn⟩ ↦ hn ▸ upperProd_le k n⟩ 0))

/-- The absolute value of the lower product. -/
def lowerAbs (k : ℕ) : ℝ := ∏ j ∈ range k, (1 + (2 : ℝ) ^ j) / ((2 : ℝ) ^ k - 2 ^ j)

theorem abs_lowerProd (k : ℕ) : |lowerProd k| = lowerAbs k := by
  rw [lowerProd, abs_prod, lowerAbs]
  refine prod_congr rfl fun j hj ↦ ?_
  have hjk : (2 : ℝ) ^ j < 2 ^ k := pow_lt_pow_right₀ (by norm_num) (mem_range.1 hj)
  rw [abs_div, abs_of_pos (by positivity), abs_of_neg (by linarith), neg_sub]

theorem lowerAbs_nonneg (k : ℕ) : 0 ≤ lowerAbs k := by
  rw [← abs_lowerProd]; exact abs_nonneg _

theorem lowerAbs_succ_le (k : ℕ) : lowerAbs (k + 1) ≤ 2 * (1 / 2) ^ k * lowerAbs k := by
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  rw [lowerAbs, prod_range_succ]
  have hlast : (1 + (2 : ℝ) ^ k) / (2 ^ (k + 1) - 2 ^ k) ≤ 2 := by
    rw [div_le_iff₀ (by rw [pow_succ]; linarith), pow_succ]
    nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := k) (by norm_num)]
  have hfirst : ∏ j ∈ range k, (1 + (2 : ℝ) ^ j) / (2 ^ (k + 1) - 2 ^ j)
      ≤ ∏ j ∈ range k, ((1 / 2) * ((1 + (2 : ℝ) ^ j) / (2 ^ k - 2 ^ j))) := by
    refine prod_le_prod₀ (fun j hj ↦ ?_) fun j hj ↦ ?_
    · have hjk : (2 : ℝ) ^ j < 2 ^ k := pow_lt_pow_right₀ (by norm_num) (mem_range.1 hj)
      have : (0 : ℝ) < 2 ^ (k + 1) - 2 ^ j := by rw [pow_succ]; linarith
      positivity
    · have hjk : (2 : ℝ) ^ j < 2 ^ k := pow_lt_pow_right₀ (by norm_num) (mem_range.1 hj)
      have h1 : (0 : ℝ) < 2 ^ k - 2 ^ j := by linarith
      have h2 : 2 * (2 ^ k - 2 ^ j) ≤ (2 : ℝ) ^ (k + 1) - 2 ^ j := by
        rw [pow_succ]; linarith [pow_pos (two_pos (α := ℝ)) j]
      calc (1 + (2 : ℝ) ^ j) / (2 ^ (k + 1) - 2 ^ j)
          ≤ (1 + (2 : ℝ) ^ j) / (2 * (2 ^ k - 2 ^ j)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) h2
        _ = 1 / 2 * ((1 + (2 : ℝ) ^ j) / (2 ^ k - 2 ^ j)) := by
            rw [mul_comm (2 : ℝ) (2 ^ k - 2 ^ j), ← div_div]; ring
  rw [prod_mul_distrib, prod_const, card_range, ← lowerAbs] at hfirst
  have hpos : 0 ≤ ∏ j ∈ range k, (1 + (2 : ℝ) ^ j) / (2 ^ (k + 1) - 2 ^ j) := by
    refine prod_nonneg fun j hj ↦ ?_
    have hjk : (2 : ℝ) ^ j < 2 ^ k := pow_lt_pow_right₀ (by norm_num) (mem_range.1 hj)
    have : (0 : ℝ) < 2 ^ (k + 1) - 2 ^ j := by rw [pow_succ]; linarith
    positivity
  calc (∏ j ∈ range k, (1 + (2 : ℝ) ^ j) / (2 ^ (k + 1) - 2 ^ j)) *
        ((1 + 2 ^ k) / (2 ^ (k + 1) - 2 ^ k))
      ≤ ((1 / 2) ^ k * lowerAbs k) * 2 :=
        mul_le_mul hfirst hlast (by
          have : (0 : ℝ) < 2 ^ (k + 1) - 2 ^ k := by rw [pow_succ]; linarith
          positivity) (mul_nonneg (by positivity) (lowerAbs_nonneg k))
    _ = 2 * (1 / 2) ^ k * lowerAbs k := by ring

/-- Super-exponential decay: `∑_k |L_k| 2^{km} < ∞` for every `m`. -/
theorem summable_lowerAbs_mul_pow (m : ℕ) :
    Summable fun k ↦ lowerAbs k * ((2 : ℝ) ^ k) ^ m := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [eventually_ge_atTop (m + 2)] with k hk
  have h0 := lowerAbs_nonneg k
  have h1 := lowerAbs_nonneg (k + 1)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  have hpow : (2 : ℝ) ^ (m + 1) * (1 / 2) ^ k ≤ 1 / 2 := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [show m + 2 + l = (m + 1) + (l + 1) by ring, pow_add (1 / 2 : ℝ) (m + 1) (l + 1),
      ← mul_assoc, ← mul_pow]
    norm_num
    calc ((1 : ℝ) / 2) ^ (l + 1) = (1 / 2) ^ l * (1 / 2) := pow_succ _ _
      _ ≤ 1 * (1 / 2) := by gcongr; exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = 1 / 2 := by norm_num
  calc lowerAbs (k + 1) * ((2 : ℝ) ^ (k + 1)) ^ m
      ≤ (2 * (1 / 2) ^ k * lowerAbs k) * ((2 : ℝ) ^ (k + 1)) ^ m := by
        gcongr; exact lowerAbs_succ_le k
    _ = ((2 : ℝ) ^ (m + 1) * (1 / 2) ^ k) * (lowerAbs k * ((2 : ℝ) ^ k) ^ m) := by
        ring
    _ ≤ 1 / 2 * (lowerAbs k * ((2 : ℝ) ^ k) ^ m) := by gcongr

theorem abs_coeff_le (k : ℕ) : |coeff k| ≤ Real.exp 4 * lowerAbs k := by
  rw [coeff, abs_mul, abs_lowerProd, abs_of_nonneg (iSup_upperProd_nonneg k), mul_comm]
  exact mul_le_mul_of_nonneg_right (iSup_upperProd_le k) (lowerAbs_nonneg k)

/-- `∑_k |a_k| (2^k)^m < ∞` for every `m`. -/
theorem summable_abs_coeff_mul_pow (m : ℕ) :
    Summable fun k ↦ |coeff k| * ((2 : ℝ) ^ k) ^ m :=
  ((summable_lowerAbs_mul_pow m).mul_left (Real.exp 4)).of_nonneg_of_le
    (fun k ↦ by positivity) fun k ↦ by
      rw [← mul_assoc]; gcongr; exact abs_coeff_le k

/-- The moment identities `∑_k a_k (-2^k)^j = 1` for every `j`. -/
theorem hasSum_coeff_mul_pow (j : ℕ) :
    HasSum (fun k ↦ coeff k * (-(2 : ℝ) ^ k) ^ j) 1 := by
  have hsum : Summable fun k ↦ coeff k * (-(2 : ℝ) ^ k) ^ j :=
    (summable_abs_coeff_mul_pow j).of_norm_bounded fun k ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
  refine hsum.hasSum_iff.2 ?_
  set F : ℕ → ℕ → ℝ := fun N k ↦ if k < N then weight N k * (-(2 : ℝ) ^ k) ^ j else 0
  have hlim : Tendsto (fun N ↦ ∑' k, F N k) atTop (𝓝 (∑' k, coeff k * (-(2 : ℝ) ^ k) ^ j)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun k ↦
      Real.exp 4 * lowerAbs k * ((2 : ℝ) ^ k) ^ j) ?_ (fun k ↦ ?_) ?_
    · simpa [mul_assoc] using (summable_lowerAbs_mul_pow j).mul_left (Real.exp 4)
    · have : ∀ᶠ N in atTop,
          F N k = lowerProd k * upperProd k (N - (k + 1)) * (-(2 : ℝ) ^ k) ^ j := by
        filter_upwards [eventually_ge_atTop (k + 1)] with N hN
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
        simp only [F, show k < k + 1 + n by omega, ite_true, weight_eq, Nat.add_sub_cancel_left]
      have h := (((tendsto_upperProd k).comp (tendsto_sub_atTop_nat (k + 1))).const_mul
        (lowerProd k)).mul_const ((-(2 : ℝ) ^ k) ^ j)
      rw [coeff]
      exact h.congr' (this.mono fun N hN ↦ hN.symm)
    · refine Eventually.of_forall fun N k ↦ ?_
      simp only [F]
      split_ifs with hk
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hk
        rw [show k + n + 1 = k + 1 + n by ring, weight_eq, norm_mul, norm_mul, norm_pow,
          Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
          abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k), abs_lowerProd,
          abs_of_nonneg (zero_le_one.trans (one_le_upperProd k n))]
        rw [mul_comm (lowerAbs k)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (upperProd_le k n)
          (lowerAbs_nonneg k)) (by positivity)
      · simp only [norm_zero]; have := lowerAbs_nonneg k; positivity
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_gt_atTop j] with N hN
  rw [tsum_eq_sum (s := range N) fun k hk ↦ by simp [F, mem_range.not.1 hk]]
  rw [← sum_weight_mul_pow hN]
  exact sum_congr rfl fun k hk ↦ by simp [F, mem_range.1 hk]

open Set Metric

section Multilinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The operator `P - 2^k Q`; with `P + Q = id` this is Seeley's `k`-th reflection. -/
def reflectOp (P Q : E →L[ℝ] E) (k : ℕ) : E →L[ℝ] E := P - (2 : ℝ) ^ k • Q

theorem norm_reflectOp_le (P Q : E →L[ℝ] E) (k : ℕ) :
    ‖reflectOp P Q k‖ ≤ (‖P‖ + ‖Q‖) * 2 ^ k := by
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  calc ‖reflectOp P Q k‖ ≤ ‖P‖ + ‖(2 : ℝ) ^ k • Q‖ := norm_sub_le _ _
    _ = ‖P‖ + 2 ^ k * ‖Q‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ (‖P‖ + ‖Q‖) * 2 ^ k := by nlinarith [norm_nonneg P, norm_nonneg Q]

theorem apply_reflectOp_eq_sum {m : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F)
    (P Q : E →L[ℝ] E) (k : ℕ) (v : Fin m → E) :
    M (fun i ↦ reflectOp P Q k (v i)) = ∑ S : Finset (Fin m),
      (-(2 : ℝ) ^ k) ^ S.card • M (S.piecewise (fun i ↦ Q (v i)) (fun i ↦ P (v i))) := by
  classical
  have : (fun i ↦ reflectOp P Q k (v i)) =
      (fun i ↦ (-(2 : ℝ) ^ k) • Q (v i)) + fun i ↦ P (v i) := by
    ext1 i
    simp only [reflectOp, Pi.add_apply]
    simp [sub_eq_add_neg, add_comm]
  rw [this, M.map_add_univ]
  refine sum_congr rfl fun S _ ↦ ?_
  have : S.piecewise (fun i ↦ (-(2 : ℝ) ^ k) • Q (v i)) (fun i ↦ P (v i)) = fun i ↦
      S.piecewise (fun _ ↦ -(2 : ℝ) ^ k) (fun _ ↦ 1) i •
        S.piecewise (fun i ↦ Q (v i)) (fun i ↦ P (v i)) i := by
    ext1 i
    by_cases hi : i ∈ S <;> simp [hi]
  rw [this, M.map_smul_univ, prod_piecewise, Finset.univ_inter, prod_const, prod_const_one, mul_one]

/-- The multilinear form of the moment identities: `∑_k a_k M ∘ (R_k, …, R_k) = M`. -/
theorem hasSum_coeff_smul_compContinuousLinearMap [CompleteSpace F] {m : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F) (P Q : E →L[ℝ] E)
    (hPQ : ∀ v, P v + Q v = v) :
    HasSum (fun k ↦ coeff k • M.compContinuousLinearMap fun _ ↦ reflectOp P Q k) M := by
  classical
  have hs : Summable fun k ↦ coeff k • M.compContinuousLinearMap fun _ ↦ reflectOp P Q k := by
    refine (((summable_abs_coeff_mul_pow m).mul_left (‖M‖ * (‖P‖ + ‖Q‖) ^ m))).of_norm_bounded
      fun k ↦ ?_
    rw [norm_smul, Real.norm_eq_abs]
    calc |coeff k| * ‖M.compContinuousLinearMap fun _ ↦ reflectOp P Q k‖
        ≤ |coeff k| * (‖M‖ * ∏ _i : Fin m, ‖reflectOp P Q k‖) :=
          mul_le_mul_of_nonneg_left (M.norm_compContinuousLinearMap_le _) (abs_nonneg _)
      _ ≤ |coeff k| * (‖M‖ * ∏ _i : Fin m, ((‖P‖ + ‖Q‖) * 2 ^ k)) := by
          gcongr with i; exact norm_reflectOp_le P Q k
      _ = ‖M‖ * (‖P‖ + ‖Q‖) ^ m * (|coeff k| * ((2 : ℝ) ^ k) ^ m) := by
          rw [prod_const, card_univ, Fintype.card_fin, mul_pow]; ring
  refine hs.hasSum_iff.2 (ContinuousMultilinearMap.ext fun v ↦ ?_)
  rw [ContinuousMultilinearMap.tsum_eval hs]
  set X : Finset (Fin m) → F := fun S ↦ M (S.piecewise (fun i ↦ Q (v i)) (fun i ↦ P (v i)))
  have hk : ∀ k, (coeff k • M.compContinuousLinearMap fun _ ↦ reflectOp P Q k) v =
      ∑ S : Finset (Fin m), (coeff k * (-(2 : ℝ) ^ k) ^ S.card) • X S := fun k ↦ by
    rw [_root_.smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
      apply_reflectOp_eq_sum, smul_sum]
    simp only [smul_smul, X]
  have hsum : ∀ S : Finset (Fin m),
      Summable fun k ↦ (coeff k * (-(2 : ℝ) ^ k) ^ S.card) • X S :=
    fun S ↦ (hasSum_coeff_mul_pow S.card).summable.smul_const (X S)
  rw [tsum_congr hk]
  rw [Summable.tsum_finsetSum fun S _ ↦ hsum S]
  have hS : ∀ S : Finset (Fin m), ∑' k, (coeff k * (-(2 : ℝ) ^ k) ^ S.card) • X S = X S :=
    fun S ↦ by rw [(hasSum_coeff_mul_pow S.card).summable.tsum_smul_const,
      (hasSum_coeff_mul_pow S.card).tsum_eq, one_smul]
  rw [sum_congr rfl fun S _ ↦ hS S]
  simp only [X]
  rw [← M.map_add_univ]
  congr 1
  ext1 i
  rw [Pi.add_apply, add_comm, hPQ]

end Multilinear

section Glue

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

private theorem mem_closure_inter_inner_lt {ν y : E} (hν : ν ≠ 0) {U : Set E} (hU : IsOpen U)
    (hy : y ∈ U) (hyν : ⟪y, ν⟫ = 0) : y ∈ closure (U ∩ {z | ⟪z, ν⟫ < 0}) := by
  have hc : Continuous fun c : ℝ ↦ y - c • ν := by fun_prop
  have ht : Tendsto (fun c : ℝ ↦ y - c • ν) (𝓝[>] 0) (𝓝 y) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  have h1 : ∀ᶠ c in 𝓝[>] (0 : ℝ), y - c • ν ∈ U :=
    ht.eventually (hU.mem_nhds hy)
  filter_upwards [h1, self_mem_nhdsWithin] with c hcU hc0
  refine ⟨hcU, ?_⟩
  have : 0 < ⟪ν, ν⟫ := real_inner_self_pos.2 hν
  simp only [mem_ofPred_eq, inner_sub_left, hyν, inner_smul_left, RCLike.conj_to_real, zero_sub,
    neg_neg_iff_pos]
  exact mul_pos hc0 this

private theorem mem_closure_inter_inner_gt {ν y : E} (hν : ν ≠ 0) {U : Set E} (hU : IsOpen U)
    (hy : y ∈ U) (hyν : ⟪y, ν⟫ = 0) : y ∈ closure (U ∩ {z | 0 < ⟪z, ν⟫}) := by
  have h := mem_closure_inter_inner_lt (neg_ne_zero.2 hν) hU hy (by simp [hyν])
  simpa only [inner_neg_right, neg_lt_zero] using h

/-- **Gluing across a hyperplane.** If a candidate Taylor series `p` of `g` is continuous on an
open set `V`, and off the hyperplane `{⟪y, ν⟫ = 0}` each `p · m` is differentiable with derivative
`p · (m + 1)`, then `p` is a Taylor series of `g` of every order on `V`. -/
theorem hasFTaylorSeriesUpToOn_of_hyperplane {ν : E} (hν : ν ≠ 0) {V : Set E} (hV : IsOpen V)
    {g : E → F} {p : E → FormalMultilinearSeries ℝ E F}
    (h0 : ∀ y ∈ V, (p y 0).curry0 = g y)
    (hderiv : ∀ m, ∀ y ∈ V, ⟪y, ν⟫ ≠ 0 →
      HasFDerivAt (fun z ↦ p z m) (p y (m + 1)).curryLeft y)
    (hcont : ∀ m, ∀ y ∈ V, ⟪y, ν⟫ = 0 → ContinuousWithinAt (fun z ↦ p z m) V y) :
    HasFTaylorSeriesUpToOn ∞ g p V := by
  have hc : ∀ m, ContinuousOn (fun z ↦ p z m) V := fun m y hy ↦ by
    by_cases h : ⟪y, ν⟫ = 0
    · exact hcont m y hy h
    · exact (hderiv m y hy h).continuousAt.continuousWithinAt
  refine ⟨h0, fun m _ y hy ↦ ?_, fun m _ ↦ hc m⟩
  by_cases h : ⟪y, ν⟫ = 0
  swap
  · exact (hderiv m y hy h).hasFDerivWithinAt
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ > 0, closedBall y δ ⊆ V :=
    nhds_basis_closedBall.mem_iff.1 (hV.mem_nhds hy)
  have side : ∀ s ⊆ ball y δ, IsOpen s → Convex ℝ s → (∀ z ∈ s, ⟪z, ν⟫ ≠ 0) →
      HasFDerivWithinAt (fun z ↦ p z m) (p y (m + 1)).curryLeft (closure s) y := by
    intro s hsB hso hsc hsν
    have hsV : s ⊆ V := hsB.trans (ball_subset_closedBall.trans hδ)
    refine hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun z hz ↦ (hderiv m z (hsV hz) (hsν z hz)).differentiableAt.differentiableWithinAt)
      hsc hso (fun z hz ↦ ?_) ?_
    · have hzV : z ∈ V := hδ ((closure_mono hsB).trans closure_ball_subset_closedBall hz)
      exact (hc m z hzV).mono hsV
    · have heq : (fun z ↦ (p z (m + 1)).curryLeft) =ᶠ[𝓝[s] y]
          fun z ↦ fderiv ℝ (fun z ↦ p z m) z :=
        eventually_mem_nhdsWithin.mono fun z hz ↦
          (hderiv m z (hsV hz) (hsν z hz)).fderiv.symm
      refine Tendsto.congr' heq ?_
      have ht : Tendsto (fun z ↦ p z (m + 1)) (𝓝[s] y) (𝓝 (p y (m + 1))) :=
        ((hc (m + 1)) y hy).mono hsV |>.tendsto
      exact ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ E) F).continuous.tendsto
        _).comp ht
  have hA := side (ball y δ ∩ {z | ⟪z, ν⟫ < 0}) inter_subset_left
    (isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const))
    ((convex_ball _ _).inter (convex_halfSpace_lt
      ⟨fun a b ↦ inner_add_left a b ν, fun c a ↦ real_inner_smul_left a ν c⟩ _))
    fun z hz ↦ hz.2.ne
  have hB := side (ball y δ ∩ {z | 0 < ⟪z, ν⟫}) inter_subset_left
    (isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop)))
    ((convex_ball _ _).inter (convex_halfSpace_gt
      ⟨fun a b ↦ inner_add_left a b ν, fun c a ↦ real_inner_smul_left a ν c⟩ _))
    fun z hz ↦ hz.2.ne'
  have hsub : ball y δ ⊆ closure (ball y δ ∩ {z | ⟪z, ν⟫ < 0}) ∪
      closure (ball y δ ∩ {z | 0 < ⟪z, ν⟫}) := by
    intro z hz
    rcases lt_trichotomy ⟪z, ν⟫ 0 with h | h | h
    · exact Or.inl (subset_closure ⟨hz, h⟩)
    · exact Or.inl (mem_closure_inter_inner_lt hν isOpen_ball hz h)
    · exact Or.inr (subset_closure ⟨hz, h⟩)
  exact (((hA.union hB).mono hsub).hasFDerivAt (ball_mem_nhds y δpos)).hasFDerivWithinAt

end Glue

section Construction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The orthogonal projection `v ↦ ⟪ν, v⟫ ν` onto the line through a unit vector `ν`. -/
def projLine (ν : E) : E →L[ℝ] E := (innerSL ℝ ν).smulRight ν

/-- Seeley's `k`-th reflection `y' + t ν ↦ y' - 2^k t ν`. -/
def reflection (ν : E) (k : ℕ) : E →L[ℝ] E :=
  reflectOp (ContinuousLinearMap.id ℝ E - projLine ν) (projLine ν) k

/-- The `k`-th term `φ(2^k t) f(y' - 2^k t ν)` of Seeley's series, at `y = y' + t ν`. -/
def term (ν : E) (φ : ℝ → ℝ) (f : E → ℝ) (k : ℕ) (y : E) : ℝ :=
  φ (2 ^ k * ⟪y, ν⟫) * f (reflection ν k y)

/-- **Seeley's extension**: `f` on `{0 ≤ ⟪y, ν⟫}` and `∑_k a_k φ(2^k t) f(y' - 2^k t ν)` below. -/
def extension (ν : E) (φ : ℝ → ℝ) (f : E → ℝ) (y : E) : ℝ :=
  if 0 ≤ ⟪y, ν⟫ then f y else ∑' k, coeff k * term ν φ f k y

theorem projLine_add (ν v : E) :
    (ContinuousLinearMap.id ℝ E - projLine ν) v + projLine ν v = v := by
  simp

theorem reflection_apply (ν y : E) (k : ℕ) :
    reflection ν k y = y - ((1 + 2 ^ k) * ⟪y, ν⟫) • ν := by
  simp only [reflection, reflectOp, projLine]
  simp [real_inner_comm, add_smul, mul_smul]
  abel

theorem inner_reflection {ν : E} (hν : ‖ν‖ = 1) (y : E) (k : ℕ) :
    ⟪reflection ν k y, ν⟫ = -(2 ^ k * ⟪y, ν⟫) := by
  rw [reflection_apply, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hν]
  ring

theorem reflection_of_inner_eq_zero {ν y : E} (hy : ⟪y, ν⟫ = 0) (k : ℕ) :
    reflection ν k y = y := by
  rw [reflection_apply, hy, mul_zero, zero_smul, sub_zero]

theorem norm_reflection_sq_le {ν : E} (hν : ‖ν‖ = 1) (w : E) (k : ℕ) :
    ‖reflection ν k w‖ ^ 2 ≤ ‖w‖ ^ 2 + (2 ^ k * ⟪w, ν⟫) ^ 2 := by
  rw [reflection_apply, norm_sub_sq_real, real_inner_smul_right, norm_smul, hν, mul_one,
    Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg ⟪w, ν⟫, pow_pos (two_pos (α := ℝ)) k]

/-- For `y` in the lower half of `B(x, r/2)` with `2^k |t| ≤ r/2`, the reflected point lies in the
open upper half ball `B(x, r) ∩ {0 < t}`. -/
theorem reflection_mem_upper {ν x : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) {r : ℝ} {y : E}
    {k : ℕ} (hy : y ∈ ball x (r / 2)) (hyν : ⟪y, ν⟫ < 0) (hk : |2 ^ k * ⟪y, ν⟫| ≤ r / 2) :
    reflection ν k y ∈ ball x r ∩ {z | 0 < ⟪z, ν⟫} := by
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, ← reflection_of_inner_eq_zero hx k, ← map_sub]
    have h1 := norm_reflection_sq_le hν (y - x) k
    have h2 : ⟪y - x, ν⟫ = ⟪y, ν⟫ := by rw [inner_sub_left, hx, sub_zero]
    rw [h2] at h1
    have h3 : ‖y - x‖ < r / 2 := by rwa [mem_ball, dist_eq_norm] at hy
    have h4 : (2 ^ k * ⟪y, ν⟫) ^ 2 ≤ (r / 2) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hk 2
    have hr : 0 < r := by linarith [norm_nonneg (y - x)]
    have h5 : ‖y - x‖ ^ 2 < (r / 2) ^ 2 := pow_lt_pow_left₀ h3 (norm_nonneg _) two_ne_zero
    refine lt_of_pow_lt_pow_left₀ 2 hr.le ?_
    nlinarith
  · rw [mem_ofPred_eq, inner_reflection hν]
    have : (0 : ℝ) < 2 ^ k := by positivity
    nlinarith

/-- The `k`-th term is either composed with a reflection into the open upper half ball, or it
vanishes near the point. -/
theorem reflection_mem_or_term_eventuallyEq_zero {ν x : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    {r : ℝ} {φ : ℝ → ℝ} (hφ0 : ∀ s, r / 4 ≤ |s| → φ s = 0) (f : E → ℝ) {y : E} (k : ℕ)
    (hy : y ∈ ball x (r / 2)) (hyν : ⟪y, ν⟫ < 0) :
    reflection ν k y ∈ ball x r ∩ {z | 0 < ⟪z, ν⟫} ∨ term ν φ f k =ᶠ[𝓝 y] 0 := by
  by_cases hk : |2 ^ k * ⟪y, ν⟫| ≤ r / 2
  · exact Or.inl (reflection_mem_upper hν hx hy hyν hk)
  · right
    have hr : 0 < r := by
      have := mem_ball.1 hy; linarith [dist_nonneg (x := y) (y := x)]
    have hopen : IsOpen {z : E | r / 4 < |2 ^ k * ⟪z, ν⟫|} :=
      isOpen_lt continuous_const (by fun_prop)
    filter_upwards [hopen.mem_nhds (show r / 4 < |2 ^ k * ⟪y, ν⟫| by linarith)] with z hz
    simp [term, hφ0 _ hz.le]

theorem hasFDerivAt_iteratedFDeriv_of_contDiffOn {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : E → F} {s : Set E} (hs : IsOpen s) (hg : ContDiffOn ℝ ∞ g s)
    {z : E} (hz : z ∈ s) (m : ℕ) :
    HasFDerivAt (iteratedFDeriv ℝ m g) (iteratedFDeriv ℝ (m + 1) g z).curryLeft z := by
  have h := (hg.ftaylorSeriesWithin hs.uniqueDiffOn).fderivWithin m
    (by exact_mod_cast ENat.natCast_lt_top m) z hz
  simp only [ftaylorSeriesWithin] at h
  rw [iteratedFDerivWithin_of_isOpen (m + 1) hs hz] at h
  exact (h.hasFDerivAt (hs.mem_nhds hz)).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (hs.mem_nhds hz) fun w hw ↦
      (iteratedFDerivWithin_of_isOpen m hs hw).symm)

end Construction

section Terms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν x : E} {r : ℝ} {f : E → ℝ} {φ : ℝ → ℝ}

theorem isOpen_upper (ν x : E) (r : ℝ) : IsOpen (ball x r ∩ {z | 0 < ⟪z, ν⟫}) :=
  isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))

theorem upper_subset_halfBall (ν x : E) (r : ℝ) :
    ball x r ∩ {z | 0 < ⟪z, ν⟫} ⊆ closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫} :=
  fun w hw ↦ ⟨ball_subset_closedBall hw.1, (show 0 < ⟪w, ν⟫ from hw.2).le⟩

theorem uniqueDiffOn_halfBall (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) (hr : 0 < r) :
    UniqueDiffOn ℝ (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}) := by
  refine uniqueDiffOn_convex ((convex_closedBall x r).inter (convex_halfSpace_ge
    ⟨fun a b ↦ inner_add_left a b ν, fun c a ↦ real_inner_smul_left a ν c⟩ 0)) ⟨x + (r / 2) • ν, ?_⟩
  refine interior_maximal (upper_subset_halfBall ν x r) (isOpen_upper ν x r) ⟨?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hν,
      Real.norm_of_nonneg (by positivity)]
    linarith
  · rw [mem_ofPred_eq, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hν, hx]
    positivity

theorem iteratedFDeriv_comp_reflection
    (hf : ContDiffOn ℝ ∞ f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫})) {k : ℕ} {z : E}
    (hz : reflection ν k z ∈ ball x r ∩ {z | 0 < ⟪z, ν⟫}) (j : ℕ) :
    iteratedFDeriv ℝ j (f ∘ reflection ν k) z =
      (iteratedFDerivWithin ℝ j f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫})
        (reflection ν k z)).compContinuousLinearMap fun _ ↦ reflection ν k := by
  have hO := isOpen_upper ν x r
  have hOK := upper_subset_halfBall ν x r
  have hpre : IsOpen (reflection ν k ⁻¹' (ball x r ∩ {z | 0 < ⟪z, ν⟫})) :=
    hO.preimage (reflection ν k).continuous
  have h1 := ContinuousLinearMap.iteratedFDerivWithin_comp_right (reflection ν k) (hf.mono hOK)
    hO.uniqueDiffOn hpre.uniqueDiffOn hz (i := j) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
  rw [iteratedFDerivWithin_of_isOpen j hpre hz] at h1
  rw [h1, ← iteratedFDerivWithin_inter_open (s := closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}) hO hz,
    inter_eq_right.2 hOK]

theorem norm_iteratedFDeriv_cutoff_le (hν : ‖ν‖ = 1) (hφ : ContDiff ℝ ∞ φ) {Φ : ℕ → ℝ}
    (hΦ : ∀ i s, ‖iteratedFDeriv ℝ i φ s‖ ≤ Φ i) (k i : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ i (fun y ↦ φ (2 ^ k * ⟪y, ν⟫)) z‖ ≤ Φ i * ((2 : ℝ) ^ k) ^ i := by
  set L : E →L[ℝ] ℝ := (2 : ℝ) ^ k • innerSL ℝ ν
  have hfun : (fun y ↦ φ (2 ^ k * ⟪y, ν⟫)) = φ ∘ L := by
    funext y; simp [L, real_inner_comm]
  have hL : ‖L‖ ≤ 2 ^ k := by
    simp only [L, norm_smul, innerSL_apply_norm, hν, mul_one, Real.norm_of_nonneg (by positivity :
      (0 : ℝ) ≤ 2 ^ k), le_refl]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right L hφ z
    (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [prod_const, card_univ, Fintype.card_fin]
  exact mul_le_mul (hΦ i _) (pow_le_pow_left₀ (norm_nonneg _) hL i) (by positivity)
    ((norm_nonneg _).trans (hΦ i 0))

/-- The constant `‖id - Q‖ + ‖Q‖` bounding `‖R_k‖ / 2^k`. -/
def reflConst (ν : E) : ℝ := ‖ContinuousLinearMap.id ℝ E - projLine ν‖ + ‖projLine ν‖

theorem norm_reflection_le (ν : E) (k : ℕ) : ‖reflection ν k‖ ≤ reflConst ν * 2 ^ k :=
  norm_reflectOp_le _ _ k

theorem norm_iteratedFDeriv_comp_reflection_le
    (hf : ContDiffOn ℝ ∞ f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫})) {Mf : ℕ → ℝ}
    (hMf : ∀ j, ∀ w ∈ closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫},
      ‖iteratedFDerivWithin ℝ j f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}) w‖ ≤ Mf j)
    {k : ℕ} {z : E} (hz : reflection ν k z ∈ ball x r ∩ {z | 0 < ⟪z, ν⟫}) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ reflection ν k) z‖ ≤ Mf j * (reflConst ν * 2 ^ k) ^ j := by
  have hzK := upper_subset_halfBall ν x r hz
  rw [iteratedFDeriv_comp_reflection hf hz]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [prod_const, card_univ, Fintype.card_fin]
  exact mul_le_mul (hMf j _ hzK) (pow_le_pow_left₀ (norm_nonneg _) (norm_reflection_le ν k) j)
    (by positivity) ((norm_nonneg _).trans (hMf j _ hzK))

theorem contDiffOn_term (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0)
    (hf : ContDiffOn ℝ ∞ f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫})) (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : ∀ s, r / 4 ≤ |s| → φ s = 0) (k : ℕ) :
    ContDiffOn ℝ ∞ (term ν φ f k) (ball x (r / 2) ∩ {z | ⟪z, ν⟫ < 0}) := by
  intro z hz
  apply ContDiffAt.contDiffWithinAt
  rcases reflection_mem_or_term_eventuallyEq_zero hν hx hφ0 f k hz.1 hz.2 with h | h
  · have hfR : ContDiffAt ℝ ∞ f (reflection ν k z) :=
      hf.contDiffAt (mem_of_superset ((isOpen_upper ν x r).mem_nhds h)
        (upper_subset_halfBall ν x r))
    have hc : ContDiff ℝ ∞ fun y : E ↦ φ (2 ^ k * ⟪y, ν⟫) :=
      hφ.comp (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))
    exact hc.contDiffAt.mul (hfR.comp z (reflection ν k).contDiff.contDiffAt)
  · exact contDiffAt_const.congr_of_eventuallyEq h

/-- The constant in the derivative bound of the terms. -/
def boundConst (Φ Mf : ℕ → ℝ) (c : ℝ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1), (m.choose i : ℝ) * Φ i * (Mf (m - i) * c ^ (m - i))

theorem norm_iteratedFDeriv_term_le (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫})) (hφ : ContDiff ℝ ∞ φ)
    (hφ0 : ∀ s, r / 4 ≤ |s| → φ s = 0) {Φ : ℕ → ℝ} (hΦ : ∀ i s, ‖iteratedFDeriv ℝ i φ s‖ ≤ Φ i)
    {Mf : ℕ → ℝ} (hMf : ∀ j, ∀ w ∈ closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫},
      ‖iteratedFDerivWithin ℝ j f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}) w‖ ≤ Mf j)
    (k m : ℕ) {z : E} (hz : z ∈ ball x (r / 2) ∩ {z | ⟪z, ν⟫ < 0}) :
    ‖iteratedFDeriv ℝ m (term ν φ f k) z‖ ≤
      boundConst Φ Mf (reflConst ν) m * ((2 : ℝ) ^ k) ^ m := by
  have hxK : x ∈ closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫} := ⟨mem_closedBall_self hr.le, hx.ge⟩
  have hΦ0 : ∀ i, 0 ≤ Φ i := fun i ↦ (norm_nonneg _).trans (hΦ i 0)
  have hM0 : ∀ j, 0 ≤ Mf j := fun j ↦ (norm_nonneg _).trans (hMf j x hxK)
  have hc0 : 0 ≤ reflConst ν := by unfold reflConst; positivity
  rcases reflection_mem_or_term_eventuallyEq_zero hν hx hφ0 f k hz.1 hz.2 with h | h
  swap
  · rw [(h.iteratedFDeriv ℝ m).eq_of_nhds]
    change ‖iteratedFDeriv ℝ m (fun _ : E ↦ (0 : ℝ)) z‖ ≤ _
    rw [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    refine mul_nonneg (sum_nonneg fun i _ ↦ ?_) (by positivity)
    have := hΦ0 i; have := hM0 (m - i); positivity
  set R := reflection ν k
  have hU : IsOpen (R ⁻¹' (ball x r ∩ {z | 0 < ⟪z, ν⟫})) :=
    (isOpen_upper ν x r).preimage R.continuous
  have hc : ContDiff ℝ ∞ fun y : E ↦ φ (2 ^ k * ⟪y, ν⟫) :=
    hφ.comp (contDiff_const.mul (contDiff_id.inner ℝ contDiff_const))
  have hfR : ContDiffOn ℝ ∞ (f ∘ R) (R ⁻¹' (ball x r ∩ {z | 0 < ⟪z, ν⟫})) :=
    (hf.mono (upper_subset_halfBall ν x r)).comp R.contDiff.contDiffOn fun _ hw ↦ hw
  have e1 : iteratedFDeriv ℝ m (term ν φ f k) z = iteratedFDerivWithin ℝ m
      (fun y ↦ φ (2 ^ k * ⟪y, ν⟫) * (f ∘ R) y) (R ⁻¹' (ball x r ∩ {z | 0 < ⟪z, ν⟫})) z :=
    (iteratedFDerivWithin_of_isOpen m hU h).symm
  rw [e1]
  refine (norm_iteratedFDerivWithin_mul_le hc.contDiffOn hfR hU.uniqueDiffOn h
    (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))).trans ?_
  rw [boundConst, sum_mul]
  refine sum_le_sum fun i hi ↦ ?_
  rw [iteratedFDerivWithin_of_isOpen i hU h, iteratedFDerivWithin_of_isOpen (m - i) hU h]
  have b1 := norm_iteratedFDeriv_cutoff_le hν hφ hΦ k i z
  have b2 := norm_iteratedFDeriv_comp_reflection_le hf hMf h (m - i)
  have hpow : ((2 : ℝ) ^ k) ^ i * ((2 : ℝ) ^ k) ^ (m - i) = ((2 : ℝ) ^ k) ^ m := by
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.1 (mem_range.1 hi))]
  calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y ↦ φ (2 ^ k * ⟪y, ν⟫)) z‖ *
        ‖iteratedFDeriv ℝ (m - i) (f ∘ R) z‖
      ≤ (m.choose i : ℝ) * (Φ i * ((2 : ℝ) ^ k) ^ i) *
        (Mf (m - i) * (reflConst ν * 2 ^ k) ^ (m - i)) := by
        have := hΦ0 i
        gcongr
    _ = (m.choose i : ℝ) * Φ i * (Mf (m - i) * reflConst ν ^ (m - i)) * ((2 : ℝ) ^ k) ^ m := by
        rw [← hpow, mul_pow]; ring

theorem tendsto_iteratedFDeriv_term (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}))
    (hφ1 : ∀ s, |s| ≤ r / 8 → φ s = 1) (k m : ℕ) {y : E} (hy : y ∈ ball x (r / 2))
    (hyν : ⟪y, ν⟫ = 0) :
    Tendsto (fun z ↦ iteratedFDeriv ℝ m (term ν φ f k) z)
      (𝓝[ball x (r / 2) ∩ {z | ⟪z, ν⟫ < 0}] y)
      (𝓝 ((iteratedFDerivWithin ℝ m f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}) y).compContinuousLinearMap
        fun _ ↦ reflection ν k)) := by
  set K := closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}
  set A := ball x (r / 2) ∩ {z | ⟪z, ν⟫ < 0}
  set R := reflection ν k
  set W := {z : E | |2 ^ k * ⟪z, ν⟫| < r / 8}
  have hW : IsOpen W := isOpen_lt (by fun_prop) continuous_const
  have hyW : y ∈ W := by simp only [W, mem_ofPred_eq, hyν, mul_zero, abs_zero]; positivity
  have hRz : ∀ z ∈ A ∩ W, R z ∈ ball x r ∩ {z | 0 < ⟪z, ν⟫} := fun z hz ↦
    reflection_mem_upper hν hx hz.1.1 hz.1.2
      (by have := hz.2; simp only [W, mem_ofPred_eq] at this; linarith)
  have key : ∀ z ∈ A ∩ W, iteratedFDeriv ℝ m (term ν φ f k) z =
      (iteratedFDerivWithin ℝ m f K (R z)).compContinuousLinearMap fun _ ↦ R := by
    intro z hz
    have heq : term ν φ f k =ᶠ[𝓝 z] f ∘ R := by
      filter_upwards [hW.mem_nhds hz.2] with w hw
      simp [term, hφ1 _ hw.le, R]
    rw [(heq.iteratedFDeriv ℝ m).eq_of_nhds, iteratedFDeriv_comp_reflection hf (hRz z hz)]
  have hev : ∀ᶠ z in 𝓝[A] y, z ∈ A ∩ W :=
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hyW))
  have hyK : y ∈ K := ⟨ball_subset_closedBall (ball_subset_ball (by linarith) hy), hyν.ge⟩
  have hcont : ContinuousWithinAt (iteratedFDerivWithin ℝ m f K) K y :=
    hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
      (uniqueDiffOn_halfBall hν hx hr) y hyK
  have hR : Tendsto R (𝓝[A] y) (𝓝[K] y) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hev.mono fun z hz ↦ upper_subset_halfBall ν x r (hRz z hz)⟩
    have := R.continuous.tendsto y
    rw [show R y = y from reflection_of_inner_eq_zero hyν k] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hlim := ((ContinuousMultilinearMap.continuous_precomp fun _ : Fin m ↦ R).tendsto _).comp
    (hcont.tendsto.comp hR)
  exact hlim.congr' (hev.mono fun z hz ↦ (key z hz).symm)

end Terms

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν x : E} {r : ℝ} {f : E → ℝ} {φ : ℝ → ℝ}

private theorem curryLeft_tsum {n : ℕ}
    (g : ℕ → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) ℝ) :
    (∑' k, g k).curryLeft = ∑' k, (g k).curryLeft :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℝ).toContinuousLinearEquiv
    |>.map_tsum

private theorem curryLeft_smul {n : ℕ} (c : ℝ)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) ℝ) :
    (c • g).curryLeft = c • g.curryLeft :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ E) ℝ).map_smul c g

/-- The candidate Taylor series of Seeley's extension. -/
def series (ν : E) (φ : ℝ → ℝ) (f : E → ℝ) (K : Set E) (z : E) : FormalMultilinearSeries ℝ E ℝ :=
  fun m ↦ if 0 ≤ ⟪z, ν⟫ then iteratedFDerivWithin ℝ m f K z
    else ∑' k, coeff k • iteratedFDeriv ℝ m (term ν φ f k) z

/-- Seeley's extension has the expected Taylor series of every order on `B(x, r/2)`. -/
theorem hasFTaylorSeriesUpToOn_extension (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫})) (hφ : ContDiff ℝ ∞ φ)
    (hφ1 : ∀ s, |s| ≤ r / 8 → φ s = 1) (hφ0 : ∀ s, r / 4 ≤ |s| → φ s = 0) {Φ : ℕ → ℝ}
    (hΦ : ∀ i s, ‖iteratedFDeriv ℝ i φ s‖ ≤ Φ i) {Mf : ℕ → ℝ}
    (hMf : ∀ j, ∀ w ∈ closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫},
      ‖iteratedFDerivWithin ℝ j f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}) w‖ ≤ Mf j) :
    HasFTaylorSeriesUpToOn ∞ (extension ν φ f)
      (series ν φ f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫})) (ball x (r / 2)) := by
  set K := closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}
  set A := ball x (r / 2) ∩ {z | ⟪z, ν⟫ < 0}
  set p := series ν φ f K
  have hνne : ν ≠ 0 := by rintro rfl; simp at hν
  have hA : IsOpen A := isOpen_ball.inter (isOpen_lt (by fun_prop) continuous_const)
  have hAc : Convex ℝ A := (convex_ball _ _).inter
    (convex_halfSpace_lt ⟨fun a b ↦ inner_add_left a b ν, fun c a ↦ real_inner_smul_left a ν c⟩ _)
  have hKu := uniqueDiffOn_halfBall hν hx hr
  set B : ℕ → ℕ → ℝ := fun m k ↦ boundConst Φ Mf (reflConst ν) m * (|coeff k| * ((2 : ℝ) ^ k) ^ m)
  have hbound : ∀ m k, ∀ z ∈ A, ‖coeff k • iteratedFDeriv ℝ m (term ν φ f k) z‖ ≤ B m k := by
    intro m k z hz
    rw [norm_smul, Real.norm_eq_abs]
    calc |coeff k| * ‖iteratedFDeriv ℝ m (term ν φ f k) z‖
        ≤ |coeff k| * (boundConst Φ Mf (reflConst ν) m * ((2 : ℝ) ^ k) ^ m) :=
          mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_term_le hν hx hr hf hφ hφ0 hΦ hMf k m hz) (abs_nonneg _)
      _ = B m k := by simp only [B]; ring
  have hsumm : ∀ m, Summable (B m) := fun m ↦
    (summable_abs_coeff_mul_pow m).mul_left (boundConst Φ Mf (reflConst ν) m)
  have hsummAt : ∀ m, ∀ z ∈ A, Summable fun k ↦ coeff k • iteratedFDeriv ℝ m (term ν φ f k) z :=
    fun m z hz ↦ (hsumm m).of_norm_bounded fun k ↦ hbound m k z hz
  refine hasFTaylorSeriesUpToOn_of_hyperplane hνne isOpen_ball ?_ ?_ ?_
  · -- the zeroth term
    intro y hy
    by_cases h : 0 ≤ ⟪y, ν⟫
    · simp only [p, series, extension, ite_eq_left h, ContinuousMultilinearMap.curry0_apply,
        iteratedFDerivWithin_zero_apply]
    · have hyA : y ∈ A := ⟨hy, not_le.1 h⟩
      simp only [p, series, extension, ite_eq_right h, ContinuousMultilinearMap.curry0_apply]
      rw [ContinuousMultilinearMap.tsum_eval (hsummAt 0 y hyA)]
      refine tsum_congr fun k ↦ ?_
      rw [_root_.smul_apply, iteratedFDeriv_zero_apply, smul_eq_mul]
  · -- derivatives off the hyperplane
    intro m y hy hne
    rcases hne.lt_or_gt with hlt | hgt
    · have hyA : y ∈ A := ⟨hy, hlt⟩
      have heq : (fun z ↦ p z m) =ᶠ[𝓝 y]
          fun z ↦ ∑' k, coeff k • iteratedFDeriv ℝ m (term ν φ f k) z := by
        filter_upwards [hA.mem_nhds hyA] with z hz
        simp only [p, series, ite_eq_right (not_le.2 (show ⟪z, ν⟫ < 0 from hz.2))]
      have hp1 : p y (m + 1) = ∑' k, coeff k • iteratedFDeriv ℝ (m + 1) (term ν φ f k) y := by
        simp only [p, series, ite_eq_right (not_le.2 hlt)]
      have hd := hasFDerivAt_tsum_of_isPreconnected (hsumm (m + 1)) hA hAc.isPreconnected
        (f := fun k z ↦ coeff k • iteratedFDeriv ℝ m (term ν φ f k) z)
        (f' := fun k z ↦ (coeff k • iteratedFDeriv ℝ (m + 1) (term ν φ f k) z).curryLeft)
        (fun k z hz ↦ by
          rw [curryLeft_smul]
          exact (hasFDerivAt_iteratedFDeriv_of_contDiffOn hA
            (contDiffOn_term hν hx hf hφ hφ0 k) hz m).const_smul (coeff k))
        (fun k z hz ↦ by
          rw [ContinuousMultilinearMap.curryLeft_norm]; exact hbound (m + 1) k z hz)
        hyA (hsummAt m y hyA) hyA
      rw [hp1, curryLeft_tsum]
      exact hd.congr_of_eventuallyEq heq
    · have hyO : y ∈ ball x r ∩ {z | 0 < ⟪z, ν⟫} :=
        ⟨ball_subset_ball (by linarith) hy, hgt⟩
      have hKn : K ∈ 𝓝 y := mem_of_superset ((isOpen_upper ν x r).mem_nhds hyO)
        (upper_subset_halfBall ν x r)
      have hT := (hf.ftaylorSeriesWithin hKu).fderivWithin m
        (by exact_mod_cast ENat.natCast_lt_top m) y (upper_subset_halfBall ν x r hyO)
      simp only [ftaylorSeriesWithin] at hT
      have heq : (fun z ↦ p z m) =ᶠ[𝓝 y] fun z ↦ iteratedFDerivWithin ℝ m f K z := by
        filter_upwards [(isOpen_lt continuous_const (by fun_prop) :
          IsOpen {z : E | 0 < ⟪z, ν⟫}).mem_nhds hgt] with z hz
        simp only [p, series, ite_eq_left (le_of_lt (show 0 < ⟪z, ν⟫ from hz))]
      have hp1 : p y (m + 1) = iteratedFDerivWithin ℝ (m + 1) f K y := by
        simp only [p, series, ite_eq_left hgt.le]
      rw [hp1]
      exact (hT.hasFDerivAt hKn).congr_of_eventuallyEq heq
  · -- continuity at the hyperplane
    intro m y hy hyν
    have hyK : y ∈ K := ⟨ball_subset_closedBall (ball_subset_ball (by linarith) hy), hyν.ge⟩
    have hpy : p y m = iteratedFDerivWithin ℝ m f K y := by
      simp only [p, series, ite_eq_left hyν.ge]
    have hVK : ball x (r / 2) ∩ {z | 0 ≤ ⟪z, ν⟫} ⊆ K := fun z hz ↦
      ⟨ball_subset_closedBall (ball_subset_ball (by linarith) hz.1), hz.2⟩
    have h1 : ContinuousWithinAt (fun z ↦ p z m) (ball x (r / 2) ∩ {z | 0 ≤ ⟪z, ν⟫}) y := by
      refine (((hf.continuousOn_iteratedFDerivWithin
        (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)) hKu) y hyK).mono hVK).congr
        (fun z hz ↦ ?_) hpy
      simp only [p, series, ite_eq_left (show 0 ≤ ⟪z, ν⟫ from hz.2)]
    have h2 : ContinuousWithinAt (fun z ↦ p z m) A y := by
      have hT := tendsto_tsum_of_dominated_convergence (hsumm m)
        (fun k ↦ (tendsto_iteratedFDeriv_term hν hx hr hf hφ1 k m hy hyν).const_smul (coeff k))
        (eventually_mem_nhdsWithin.mono fun z hz k ↦ hbound m k z hz)
      have hS : HasSum (fun k ↦ coeff k • (iteratedFDerivWithin ℝ m f
          (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}) y).compContinuousLinearMap fun _ ↦ reflection ν k)
          (iteratedFDerivWithin ℝ m f (closedBall x r ∩ {z | 0 ≤ ⟪z, ν⟫}) y) :=
        hasSum_coeff_smul_compContinuousLinearMap _ _ _ (projLine_add ν)
      rw [hS.tsum_eq] at hT
      rw [ContinuousWithinAt, hpy]
      refine hT.congr' (eventually_mem_nhdsWithin.mono fun z hz ↦ ?_)
      simp only [p, series, ite_eq_right (not_le.2 (show ⟪z, ν⟫ < 0 from hz.2))]
    refine (h1.union h2).mono fun z hz ↦ ?_
    by_cases h : 0 ≤ ⟪z, ν⟫
    · exact Or.inl ⟨hz, h⟩
    · exact Or.inr ⟨hz, not_le.1 h⟩

end Assembly

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Seeley extension** in a finite-dimensional real inner product space: a function smooth on
the closed half ball `closedBall x r ∩ {0 ≤ ⟪y, ν⟫}` (with `x` on the hyperplane) agrees, on the
half of `ball x (r / 2)`, with a function smooth on all of `ball x (r / 2)`. -/
theorem exists_contDiffOn_extension {ν x : E} (hν : ‖ν‖ = 1) (hx : ⟪x, ν⟫ = 0) {r : ℝ}
    (hr : 0 < r) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (closedBall x r ∩ {y | 0 ≤ ⟪y, ν⟫})) :
    ∃ g : E → ℝ, ContDiffOn ℝ ∞ g (ball x (r / 2)) ∧
      EqOn g f (ball x (r / 2) ∩ {y | 0 ≤ ⟪y, ν⟫}) := by
  set K := closedBall x r ∩ {y | 0 ≤ ⟪y, ν⟫}
  let b : ContDiffBump (0 : ℝ) := ⟨r / 8, r / 4, by positivity, by linarith⟩
  have hφ : ContDiff ℝ ∞ (b : ℝ → ℝ) := b.contDiff
  have hφ1 : ∀ s, |s| ≤ r / 8 → b s = 1 := fun s hs ↦
    b.one_of_mem_closedBall (by rwa [mem_closedBall, Real.dist_eq, sub_zero])
  have hφ0 : ∀ s, r / 4 ≤ |s| → b s = 0 := fun s hs ↦
    b.zero_of_le_dist (by rwa [Real.dist_eq, sub_zero])
  have hΦ : ∀ i, ∃ C, ∀ s, ‖iteratedFDeriv ℝ i (b : ℝ → ℝ) s‖ ≤ C := fun i ↦
    (hφ.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤)))
      |>.bounded_above_of_compact_support
      (b.hasCompactSupport.iteratedFDeriv i)
  choose Φ hΦ using hΦ
  have hK : IsCompact K :=
    (isCompact_closedBall x r).inter_right (isClosed_le continuous_const (by fun_prop))
  have hMf : ∀ j, ∃ C, ∀ w ∈ K, ‖iteratedFDerivWithin ℝ j f K w‖ ≤ C := fun j ↦
    hK.exists_bound_of_continuousOn (hf.continuousOn_iteratedFDerivWithin
      (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)) (uniqueDiffOn_halfBall hν hx hr))
  choose Mf hMf using hMf
  refine ⟨extension ν b f, ?_, fun y hy ↦ by simp [extension, show 0 ≤ ⟪y, ν⟫ from hy.2]⟩
  exact (hasFTaylorSeriesUpToOn_extension hν hx hr hf hφ hφ1 hφ0 hΦ hMf).contDiffOn

end Main

end Seeley

open Set Metric

/-- **Seeley extension across a hyperplane** (R. T. Seeley, *Extension of `C^∞` functions defined
in a half space*, Proc. Amer. Math. Soc. 15 (1964), 625–626). Let `ν` be a unit vector and `x` a
point of the hyperplane `{⟪y, ν⟫ = 0}`. If `f` is `C^∞` on the closed half ball
`closedBall x r ∩ {0 ≤ ⟪y, ν⟫}` (derivatives taken within that set), then there is a function `g`,
`C^∞` on the full open ball `ball x (r / 2)`, that agrees with `f` on the half of that ball. -/
theorem exists_contDiffOn_extension_halfSpace {d : ℕ} {ν x : E d} (hν : ‖ν‖ = 1)
    (hx : ⟪x, ν⟫ = 0) {r : ℝ} (hr : 0 < r) {f : E d → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall x r ∩ {y | 0 ≤ ⟪y, ν⟫})) :
    ∃ g : E d → ℝ, ContDiffOn ℝ ∞ g (ball x (r / 2)) ∧
      EqOn g f (ball x (r / 2) ∩ {y | 0 ≤ ⟪y, ν⟫}) :=
  Seeley.exists_contDiffOn_extension hν hx hr hf

end EllipticBernoulli
