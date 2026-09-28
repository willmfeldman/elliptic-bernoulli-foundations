/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Lipschitz.Barrier
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# De Silva's barrier, globally smooth

The barrier of De Silva's one-step lemma (De Silva (2011), Lemma 3.3) is
`w = c (|x - x̄|^{-γ} - (3/4)^{-γ})` on the annulus `B_{3/4}(x̄) \ B̄_{1/20}(x̄)`, extended by `1`
inside. It is singular at `x̄` and only Lipschitz across the inner sphere, while our viscosity
notion (`IsViscSolution`, after Abedin–Feldman–Stinson, Definition 2.1) tests with globally `C^∞`
functions only.

We use instead the **Gaussian** profile of `radialSubBarrier` (`Lipschitz/Barrier.lean`;
Caffarelli–Salsa's device)
`deSilvaBarrier x̄ z = A (exp (-λ |z - x̄|²) - exp (-λ (3/4)²))` with `λ = 625 d` and `A`
normalized so that the barrier equals `1` on `|z - x̄| = 1/25`. It is globally `C^∞`, so every test
function built from it is admissible as it stands (no localization lemma is needed), and it has
every property De Silva uses on the annulus `1/25 < |z - x̄| < 3/4`:

* `deSilvaBarrier_eq_zero`: `= 0` on `|z - x̄| = 3/4`; `deSilvaBarrier_nonneg`: `≥ 0` inside;
* `deSilvaBarrier_lt_one`: `< 1` for `|z - x̄| > 1/25`;
* `le_deSilvaBarrier`: `≥ c₂ > 0` for `|z - x̄| ≤ 7/10` (which covers `B̄_{1/2}` when `|x̄| = 1/5`);
* `laplacian_deSilvaBarrier_pos`: strictly subharmonic for `|z - x̄| > 1/25`;
* `hasGradientAt_deSilvaBarrier`: `∇ = -k(z) (z - x̄)`, with `k(z) ∈ [k_min, k_max]` on
  `B̄_{3/4}(x̄)` (`deSilvaBarrierSlope_mem`).

The inner radius is `1/25` rather than De Silva's `1/20` so that the closed inner ball lies inside
the open ball `B_{1/20}(x̄)` on which the open-ball Harnack inequality (`harnack_ball_explicit`)
gives the lower bound.

Also: `hasGradientAt_mul_inner_add_mul` and `laplacian_mul_inner_add_mul`, the jet of the test
functions `y ↦ a ⟪y, e⟫ + b + κ W(y)` used in both barrier arguments.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The rate `λ = 625 d` of De Silva's Gaussian barrier. -/
def deSilvaRate (d : ℕ) : ℝ := 625 * d

/-- The normalizing constant `A = (exp (-λ/625) - exp (-λ (3/4)²))⁻¹` of De Silva's barrier. -/
def deSilvaBarrierConst (d : ℕ) : ℝ :=
  (Real.exp (-(deSilvaRate d * (1 / 25) ^ 2)) - Real.exp (-(deSilvaRate d * (3 / 4) ^ 2)))⁻¹

/-- **De Silva's barrier (Gaussian form).** `A (exp (-λ |z - x̄|²) - exp (-λ (3/4)²))`, globally
`C^∞`, equal to `0` on `∂B_{3/4}(x̄)` and to `1` on `∂B_{1/25}(x̄)`. -/
def deSilvaBarrier (xbar : E d) : E d → ℝ :=
  radialSubBarrier xbar (3 / 4) (deSilvaRate d) (deSilvaBarrierConst d)

/-- The radial slope `k(z) = 2 A λ exp (-λ |z - x̄|²)`: `∇W(z) = -k(z) (z - x̄)`. -/
def deSilvaBarrierSlope (xbar z : E d) : ℝ :=
  2 * deSilvaBarrierConst d * deSilvaRate d * Real.exp (-(deSilvaRate d * ‖z - xbar‖ ^ 2))

/-- The lower bound `c₂` of the barrier on `B̄_{7/10}(x̄)`. -/
def deSilvaBarrierInner (d : ℕ) : ℝ :=
  deSilvaBarrierConst d *
    (Real.exp (-(deSilvaRate d * (7 / 10) ^ 2)) - Real.exp (-(deSilvaRate d * (3 / 4) ^ 2)))

variable {xbar z : E d}

theorem deSilvaRate_pos (hd : 0 < d) : 0 < deSilvaRate d := by
  unfold deSilvaRate; positivity

private theorem exp_lt_exp_of_sq_lt {lam s t : ℝ} (hlam : 0 < lam) (h : s < t) :
    Real.exp (-(lam * t)) < Real.exp (-(lam * s)) :=
  Real.exp_lt_exp.2 (by nlinarith)

private theorem exp_le_exp_of_sq_le {lam s t : ℝ} (hlam : 0 ≤ lam) (h : s ≤ t) :
    Real.exp (-(lam * t)) ≤ Real.exp (-(lam * s)) :=
  Real.exp_le_exp.2 (by nlinarith)

theorem deSilvaBarrierConst_pos (hd : 0 < d) : 0 < deSilvaBarrierConst d := by
  unfold deSilvaBarrierConst
  exact inv_pos.2 (sub_pos.2 (exp_lt_exp_of_sq_lt (deSilvaRate_pos hd) (by norm_num)))

theorem deSilvaBarrier_apply (xbar z : E d) :
    deSilvaBarrier xbar z = deSilvaBarrierConst d *
      (Real.exp (-(deSilvaRate d * ‖z - xbar‖ ^ 2)) -
        Real.exp (-(deSilvaRate d * (3 / 4) ^ 2))) :=
  radialSubBarrier_apply z

theorem contDiff_deSilvaBarrier (xbar : E d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (deSilvaBarrier xbar) :=
  contDiff_radialSubBarrier

theorem continuous_deSilvaBarrier (xbar : E d) : Continuous (deSilvaBarrier xbar) :=
  (contDiff_deSilvaBarrier xbar (n := 0)).continuous

/-- The barrier vanishes on `∂B_{3/4}(x̄)`. -/
theorem deSilvaBarrier_eq_zero (hz : ‖z - xbar‖ = 3 / 4) : deSilvaBarrier xbar z = 0 :=
  radialSubBarrier_eq_zero hz

/-- The barrier is nonnegative on `B̄_{3/4}(x̄)`. -/
theorem deSilvaBarrier_nonneg (hd : 0 < d) (hz : ‖z - xbar‖ ≤ 3 / 4) :
    0 ≤ deSilvaBarrier xbar z := by
  rw [deSilvaBarrier_apply]
  refine mul_nonneg (deSilvaBarrierConst_pos hd).le (sub_nonneg.2 ?_)
  exact exp_le_exp_of_sq_le (deSilvaRate_pos hd).le
    (pow_le_pow_left₀ (norm_nonneg _) hz 2)

/-- The barrier is `< 1` outside `B̄_{1/25}(x̄)`. -/
theorem deSilvaBarrier_lt_one (hd : 0 < d) (hz : 1 / 25 < ‖z - xbar‖) :
    deSilvaBarrier xbar z < 1 := by
  have hlam := deSilvaRate_pos hd
  have hden : 0 < Real.exp (-(deSilvaRate d * (1 / 25) ^ 2)) -
      Real.exp (-(deSilvaRate d * (3 / 4) ^ 2)) :=
    sub_pos.2 (exp_lt_exp_of_sq_lt hlam (by norm_num))
  rw [deSilvaBarrier_apply, deSilvaBarrierConst, inv_mul_lt_iff₀ hden, mul_one]
  have : (1 / 25 : ℝ) ^ 2 < ‖z - xbar‖ ^ 2 := pow_lt_pow_left₀ hz (by norm_num) two_ne_zero
  linarith [exp_lt_exp_of_sq_lt hlam this]

theorem deSilvaBarrierInner_pos (hd : 0 < d) : 0 < deSilvaBarrierInner d :=
  mul_pos (deSilvaBarrierConst_pos hd)
    (sub_pos.2 (exp_lt_exp_of_sq_lt (deSilvaRate_pos hd) (by norm_num)))

theorem deSilvaBarrierInner_le_one (hd : 0 < d) : deSilvaBarrierInner d ≤ 1 := by
  have hlam := deSilvaRate_pos hd
  have hden : 0 < Real.exp (-(deSilvaRate d * (1 / 25) ^ 2)) -
      Real.exp (-(deSilvaRate d * (3 / 4) ^ 2)) :=
    sub_pos.2 (exp_lt_exp_of_sq_lt hlam (by norm_num))
  rw [deSilvaBarrierInner, deSilvaBarrierConst, inv_mul_le_iff₀ hden, mul_one]
  linarith [exp_lt_exp_of_sq_lt hlam (show (1 / 25 : ℝ) ^ 2 < (7 / 10) ^ 2 by norm_num)]

/-- The barrier is `≥ c₂ > 0` on `B̄_{7/10}(x̄)`. -/
theorem le_deSilvaBarrier (hd : 0 < d) (hz : ‖z - xbar‖ ≤ 7 / 10) :
    deSilvaBarrierInner d ≤ deSilvaBarrier xbar z := by
  rw [deSilvaBarrier_apply, deSilvaBarrierInner]
  refine mul_le_mul_of_nonneg_left (sub_le_sub_right ?_ _) (deSilvaBarrierConst_pos hd).le
  exact exp_le_exp_of_sq_le (deSilvaRate_pos hd).le (pow_le_pow_left₀ (norm_nonneg _) hz 2)

/-- **Strict subharmonicity** outside `B̄_{1/25}(x̄)`. -/
theorem laplacian_deSilvaBarrier_pos (hd : 0 < d) (hz : 1 / 25 < ‖z - xbar‖) :
    0 < Δ (deSilvaBarrier xbar) z := by
  refine laplacian_radialSubBarrier_pos (deSilvaBarrierConst_pos hd) (deSilvaRate_pos hd) ?_
  have : (1 / 25 : ℝ) ^ 2 < ‖z - xbar‖ ^ 2 := pow_lt_pow_left₀ hz (by norm_num) two_ne_zero
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold deSilvaRate
  nlinarith

/-- **Gradient of the barrier:** `∇W(z) = -k(z) (z - x̄)`. -/
theorem hasGradientAt_deSilvaBarrier (xbar z : E d) :
    HasGradientAt (deSilvaBarrier xbar) (-(deSilvaBarrierSlope xbar z) • (z - xbar)) z := by
  have hcomp := (hasDerivAt_radialSubProfile (ρ := 3 / 4) (lam := deSilvaRate d)
    (A := deSilvaBarrierConst d) (‖z - xbar‖ ^ 2)).comp_hasFDerivAt
      (f := fun y : E d ↦ ‖y - xbar‖ ^ 2) z (hasFDerivAt_normSq_sub_const xbar z)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hcomp using 1
  ext v
  simp only [toDual_apply_apply, inner_smul_left, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul, deSilvaBarrierSlope, RCLike.conj_to_real]
  ring

/-- Bounds `k_min ≤ k(z) ≤ k_max` for the radial slope on `B̄_{3/4}(x̄)`. -/
theorem deSilvaBarrierSlope_mem (hd : 0 < d) (hz : ‖z - xbar‖ ≤ 3 / 4) :
    2 * deSilvaBarrierConst d * deSilvaRate d * Real.exp (-(deSilvaRate d * (3 / 4) ^ 2)) ≤
        deSilvaBarrierSlope xbar z ∧
      deSilvaBarrierSlope xbar z ≤ 2 * deSilvaBarrierConst d * deSilvaRate d := by
  have hA := deSilvaBarrierConst_pos hd
  have hlam := deSilvaRate_pos hd
  have hpos : 0 < 2 * deSilvaBarrierConst d * deSilvaRate d := by positivity
  refine ⟨mul_le_mul_of_nonneg_left
    (exp_le_exp_of_sq_le hlam.le (pow_le_pow_left₀ (norm_nonneg _) hz 2)) hpos.le, ?_⟩
  refine (mul_le_iff_le_one_right hpos).2 (Real.exp_le_one_iff.2 ?_)
  have := sq_nonneg ‖z - xbar‖
  nlinarith

/-! ### Jets of the test functions `a ⟪y, e⟫ + b + κ W(y)` -/

section Jet

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Gradient of `y ↦ a ⟪y, e⟫ + b + κ W(y)`. -/
theorem hasGradientAt_mul_inner_add_mul {W : F → ℝ} {G e x : F} (hW : HasGradientAt W G x)
    (a b κ : ℝ) :
    HasGradientAt (fun y ↦ a * ⟪y, e⟫ + b + κ * W y) (a • e + κ • G) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at hW ⊢
  have hlin : HasFDerivAt (fun y : F ↦ ⟪y, e⟫) (toDual ℝ F e : F →L[ℝ] ℝ) x := by
    have : (fun y : F ↦ ⟪y, e⟫) = fun y ↦ (toDual ℝ F e : F →L[ℝ] ℝ) y := by
      funext y; simp [real_inner_comm]
    rw [this]
    exact (toDual ℝ F e : F →L[ℝ] ℝ).hasFDerivAt
  convert ((hlin.const_mul a).add_const b).add (hW.const_mul κ) using 1
  ext v
  simp

/-- Affine functions are harmonic: `Δ (y ↦ a ⟪y, e⟫ + b) = 0`. -/
theorem laplacian_mul_inner_add [FiniteDimensional ℝ F] (e : F) (a b : ℝ) (x : F) :
    Δ (fun y ↦ a * ⟪y, e⟫ + b) x = 0 := by
  have hf : fderiv ℝ (fun y : F ↦ a * ⟪y, e⟫ + b) = fun _ ↦ a • (toDual ℝ F e : F →L[ℝ] ℝ) := by
    funext y
    have hlin : HasFDerivAt (fun y : F ↦ ⟪y, e⟫) (toDual ℝ F e : F →L[ℝ] ℝ) y := by
      have : (fun y : F ↦ ⟪y, e⟫) = fun y ↦ (toDual ℝ F e : F →L[ℝ] ℝ) y := by
        funext y; simp [real_inner_comm]
      rw [this]
      exact (toDual ℝ F e : F →L[ℝ] ℝ).hasFDerivAt
    exact ((hlin.const_mul a).add_const b).fderiv
  rw [laplacian_eq_sum_fderiv_fderiv, hf]
  simp

/-- Laplacian of `y ↦ a ⟪y, e⟫ + b + κ W(y)`. -/
theorem laplacian_mul_inner_add_mul [FiniteDimensional ℝ F] {W : F → ℝ} (hW : ContDiff ℝ 2 W)
    (e : F) (a b κ : ℝ) (x : F) :
    Δ (fun y ↦ a * ⟪y, e⟫ + b + κ * W y) x = κ * Δ W x := by
  have h1 : ContDiffAt ℝ 2 (fun y : F ↦ a * ⟪y, e⟫ + b) x :=
    (contDiffAt_const.mul (contDiffAt_id.inner ℝ contDiffAt_const)).add contDiffAt_const
  have h2 : ContDiffAt ℝ 2 (κ • W) x := (hW.const_smul κ).contDiffAt
  have := h1.laplacian_add h2
  have h3 : Δ (κ • W) x = κ * Δ W x := by
    rw [laplacian_smul κ hW.contDiffAt]; rfl
  rw [laplacian_mul_inner_add, h3, zero_add] at this
  exact this

end Jet

end EllipticBernoulli
