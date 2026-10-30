/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Regularity
public import EllipticBernoulli.Statements.TwoPhase
public import EllipticBernoulli.TwoPhase.WeissCompetitor
import EllipticBernoulli.TwoPhase.ACF
import EllipticBernoulli.TwoPhase.ACFCore
import EllipticBernoulli.Sobolev.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Weiss monotonicity for sign-changing minimizers

Let `d ≥ 2` and let `u : ℝᵈ → ℝ` be `L`-Lipschitz and a local minimizer of
`J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ` (no sign condition), with `u(x₀) = 0`. With the radial
quantities `k, m, a` of `u` about `x₀` (`Sphere/Radial.lean`) and
`W(t) = W(u, x₀, t) = t^{-d} J(u, B_t(x₀)) - t^{-2} m(t)` (`weissW`):

* `weissW_eq`: `W(t) = t^{-d} ∫_{B_t(x₀)} e_u - t^{-2} m(t)` with the real integral of the energy
  density `e_u = |∇u|² + 1_{u > 0}` (`weissDensity`).
* `weissRate u x₀ t = a(t)/t - 2k(t)/t² + m(t)/t³ = t^{-1} ∫_𝕊 (∂ᵣu - u/t)²(x₀ + tω) dσ(ω)`, the
  integrand of the defect in polar form.
* `ae_weissRate_le_deriv_weissW`: for a.e. `t > 0`, `W'(t) ≥ weissRate u x₀ t`
  (using the homogeneous competitor bound `ae_setIntegral_weissDensity_le`).
* `weissDefect_eq_integral_weissRate`: `D(u, x₀; r, s) = ∫_r^s weissRate u x₀ t dt`.
* `weissDefect_le_weissW_sub`, `weissDefect_nonneg`, `abs_weissW_le`, and
  `weissMonotone : WeissMonotoneStatement`.
* `exists_tendsto_weissW`: `W(0⁺)` and `W(∞)` exist, are finite,
  `W(0⁺) ≤ W(∞)`, and `W(0⁺) = W(∞)` forces `D(u, x₀; r, s) = 0` for all `0 < r < s`.
* Scaling, for the rescaling `u_{x₀,R}(y) = u(x₀ + Ry)/R` (`blowup`)
  with `R > 0`: `lipschitzWith_blowup`, `weissW_blowup` (`W(u_{x₀,R}, 0, ρ) = W(u, x₀, Rρ)`) and
  `weissDefect_blowup` (`D(u_{x₀,R}, 0; r, s) = D(u, x₀; Rr, Rs)`).

The lemmas assume `1 ≤ d` where the proofs need it; `WeissMonotoneStatement` assumes `2 ≤ d`.
Monotonicity is stated in the integrated form `W(s) - W(r) ≥ D(u, x₀; r, s)`, with factor `1` in
front of the defect; the derivative computation gives the sharp factor `2`, which is not needed.

## Proof

`t ↦ J(u, B_t(x₀))` is Lipschitz on `[0, R]` with a.e. derivative `t^{d-1} j(t)`
(`ae_hasDerivAt_setIntegral_ball_mul_rpow` with `β = 0`) and `m` is Lipschitz on `[0, R]` with
`m' = 2k` a.e. (`radialM_sub_eq_integral`, `ae_hasDerivAt_radialM`). So `W` is absolutely
continuous on every `[r, s] ⊆ (0, ∞)`, and a.e.
`W' = j/t - d t^{-d-1} J + 2m/t³ - 2k/t² ≥ a/t + m/t³ - 2k/t²` by the competitor bound
`d J ≤ t^d (j - a + m/t²)`. The fundamental theorem of calculus for absolutely continuous
functions concludes.

## References

* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped Gradient NNReal

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public noncomputable section

/-- The polar integrand of the Weiss defect:
`a(t)/t - 2k(t)/t² + m(t)/t³ = t^{-1} ∫_𝕊 (∂ᵣu - u/t)²(x₀ + tω) dσ(ω)`. -/
def weissRate (u : E d → ℝ) (x₀ : E d) (t : ℝ) : ℝ :=
  radialA u x₀ t / t - 2 * radialK u x₀ t / t ^ 2 + radialM u x₀ t / t ^ 3

end

public section

variable {u : E d → ℝ} {L : ℝ≥0} {x₀ : E d}

/-! ### The Weiss functional in real form -/

/-- `W(u, x₀, r) = r^{-d} ∫_{B_r(x₀)} (|∇u|² + 1_{u > 0}) - r^{-2} m(r)` for Lipschitz `u`. -/
theorem weissW_eq (hu : LipschitzWith L u) (x₀ : E d) (r : ℝ) :
    weissW u x₀ r = (∫ x in ball x₀ r, weissDensity u x) / r ^ d - radialM u x₀ r / r ^ 2 := by
  rw [weissW, toReal_energyJ_ball_gradient_eq hu]
  rfl

private theorem weissDensity_mul_rpow_zero (u : E d → ℝ) (x₀ : E d) :
    (fun s ↦ ∫ x in ball x₀ s, weissDensity u x * ‖x - x₀‖ ^ (0 : ℝ)) =
      fun s ↦ ∫ x in ball x₀ s, weissDensity u x := by
  simp only [Real.rpow_zero, mul_one]

/-- `t ↦ J(u, B_t(x₀))` is Lipschitz on `[0, R]`. -/
theorem exists_lipschitzOnWith_setIntegral_weissDensity (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (x₀ : E d) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun s ↦ ∫ x in ball x₀ s, weissDensity u x) (Icc 0 R) := by
  rw [← weissDensity_mul_rpow_zero]
  exact exists_lipschitzOnWith_setIntegral_ball_mul_rpow hd
    (measurable_weissDensity hu.continuous) (abs_weissDensity_le hu) x₀ (by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith) R

/-- `d/dt J(u, B_t(x₀)) = t^{d-1} j(t)` for a.e. `t > 0`. -/
theorem ae_hasDerivAt_setIntegral_weissDensity (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (x₀ : E d) :
    ∀ᵐ t, 0 < t → HasDerivAt (fun s ↦ ∫ x in ball x₀ s, weissDensity u x)
      (t ^ (d - 1) * radialJ u x₀ t) t := by
  filter_upwards [ae_hasDerivAt_setIntegral_ball_mul_rpow hd
    (measurable_weissDensity hu.continuous) (abs_weissDensity_le hu) x₀ (β := 0) (by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith)] with t ht htpos
  have h := ht htpos
  rw [weissDensity_mul_rpow_zero, add_zero,
    show (d : ℝ) - 1 = ((d - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hd, Nat.cast_one],
    Real.rpow_natCast] at h
  exact h

/-- `m` is Lipschitz on `[0, R]` when `u(x₀) = 0`. -/
theorem exists_lipschitzOnWith_radialM (hd : 1 ≤ d) (hu : LipschitzWith L u) (hx₀ : u x₀ = 0)
    (R : ℝ) : ∃ K, LipschitzOnWith K (radialM u x₀) (Icc 0 R) := by
  set C := 2 * ((L : ℝ) ^ 2 * R * (volume : Measure (E d)).toSphere.real univ)
  refine ⟨Real.toNNReal C, LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_⟩
  have hbound : ∀ {p q : ℝ}, p ∈ Icc 0 R → q ∈ Icc 0 R → p ≤ q →
      |radialM u x₀ q - radialM u x₀ p| ≤ C * |q - p| := by
    intro p q hp hq hpq
    rw [radialM_sub_eq_integral hd hu x₀ hp.1 hpq]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := q)
      (f := fun τ ↦ 2 * radialK u x₀ τ) (C := C) fun τ hτ ↦ by
        rw [uIoc_of_le hpq] at hτ
        have hτ0 : 0 ≤ τ := hp.1.trans hτ.1.le
        rw [Real.norm_eq_abs, abs_mul, abs_two]
        have hk := abs_radialK_le hu hx₀ hτ0 (x₀ := x₀)
        have hσ : 0 ≤ (volume : Measure (E d)).toSphere.real univ := measureReal_nonneg
        have : (L : ℝ) ^ 2 * τ * (volume : Measure (E d)).toSphere.real univ ≤
            (L : ℝ) ^ 2 * R * (volume : Measure (E d)).toSphere.real univ := by
          gcongr; exact hτ.2.trans hq.2
        linarith
    rwa [Real.norm_eq_abs] at h
  have hC : 0 ≤ C := by
    have hR : 0 ≤ R := ha.1.trans ha.2
    have hσ : 0 ≤ (volume : Measure (E d)).toSphere.real univ := measureReal_nonneg
    positivity
  rw [Real.coe_toNNReal _ hC, Real.dist_eq, Real.dist_eq]
  rcases le_total a b with hab | hab
  · rw [abs_sub_comm, abs_sub_comm a]; exact hbound ha hb hab
  · exact hbound hb ha hab

/-! ### The derivative of `W` -/

/-- **The derivative of the Weiss functional.** For a.e. `t > 0`,
`W'(t) ≥ a(t)/t - 2k(t)/t² + m(t)/t³`. -/
theorem ae_weissRate_le_deriv_weissW (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hx₀ : u x₀ = 0) :
    ∀ᵐ t, 0 < t → weissRate u x₀ t ≤ deriv (weissW u x₀) t := by
  filter_upwards [ae_hasDerivAt_setIntegral_weissDensity hd hu x₀,
    ae_hasDerivAt_radialM hd hu hx₀, ae_setIntegral_weissDensity_le hd hu hmin hx₀]
    with t hJ hm hle ht
  set Jb := fun s ↦ ∫ x in ball x₀ s, weissDensity u x with hJb
  have hWfun : weissW u x₀ = fun s ↦ Jb s / s ^ d - radialM u x₀ s / s ^ 2 :=
    funext (weissW_eq hu x₀)
  have hW : HasDerivAt (fun s ↦ Jb s / s ^ d - radialM u x₀ s / s ^ 2) _ t :=
    ((hJ ht).div (hasDerivAt_pow d t) (pow_ne_zero d ht.ne')).sub
      ((hm ht).div (hasDerivAt_pow 2 t) (pow_ne_zero 2 ht.ne'))
  rw [hWfun, hW.deriv]
  set P := t ^ (d - 1)
  have hP : 0 < P := pow_pos ht _
  have htd : t ^ d = P * t := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hle' : d * Jb t ≤ P * t * (radialJ u x₀ t - radialA u x₀ t + radialM u x₀ t / t ^ 2) := by
    have := hle ht
    rw [htd] at this
    rw [div_mul_eq_mul_div, le_div_iff₀ hdpos] at this
    linarith
  rw [htd, weissRate]
  simp only [Nat.cast_ofNat, Nat.succ_sub_one, pow_one]
  have key : (P * radialJ u x₀ t * (P * t) - Jb t * (d * P)) / (P * t) ^ 2 -
      (2 * radialK u x₀ t * t ^ 2 - radialM u x₀ t * (2 * t)) / (t ^ 2) ^ 2 -
      (radialA u x₀ t / t - 2 * radialK u x₀ t / t ^ 2 + radialM u x₀ t / t ^ 3) =
      (P * t * (radialJ u x₀ t - radialA u x₀ t + radialM u x₀ t / t ^ 2) - d * Jb t) /
        (P * t ^ 2) := by
    field_simp
    ring
  have : 0 ≤ (P * t * (radialJ u x₀ t - radialA u x₀ t + radialM u x₀ t / t ^ 2) - d * Jb t) /
      (P * t ^ 2) := div_nonneg (by linarith) (by positivity)
  linarith

/-! ### The defect in polar form -/

/-- `∫_𝕊 (α ∂ᵣu - β u)²(x₀ + τω) dσ = α² a(τ) - 2αβ k(τ) + β² m(τ)` for Lipschitz `u` with
`u(x₀) = 0`. -/
private theorem integral_sq_sub_eq (hu : LipschitzWith L u) (hx₀ : u x₀ = 0) {τ : ℝ}
    (hτ : 0 ≤ τ) (α β : ℝ) :
    ∫ ω : sphere (0 : E d) 1, (α * radialDeriv u x₀ (x₀ + τ • (ω : E d)) -
        β * u (x₀ + τ • (ω : E d))) ^ 2 ∂(volume : Measure (E d)).toSphere =
      α ^ 2 * radialA u x₀ τ - 2 * α * β * radialK u x₀ τ + β ^ 2 * radialM u x₀ τ := by
  set σ := (volume : Measure (E d)).toSphere
  have hwm : Measurable u := hu.continuous.measurable
  have hrd := measurable_radialDeriv u x₀
  have hfL : ∀ ω : sphere (0 : E d) 1, |u (x₀ + τ • (ω : E d))| ≤ L * τ := fun ω ↦ by
    have h := abs_apply_add_smul_le hu x₀ hτ ω
    rwa [hx₀, abs_zero, zero_add] at h
  have hint_m : Integrable (fun ω : sphere (0 : E d) 1 ↦ u (x₀ + τ • (ω : E d)) ^ 2) σ :=
    integrable_toSphere_of_bound (hwm.pow_const 2) x₀ τ (B := (L * τ) ^ 2) fun ω ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfL ω) 2
  have hint_k : Integrable (fun ω : sphere (0 : E d) 1 ↦
      u (x₀ + τ • (ω : E d)) * radialDeriv u x₀ (x₀ + τ • (ω : E d))) σ :=
    integrable_toSphere_of_bound (hwm.mul hrd) x₀ τ (B := L * τ * L) fun ω ↦ by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hfL ω) (abs_radialDeriv_le hu _ _) (abs_nonneg _) (by positivity)
  have hint_a : Integrable (fun ω : sphere (0 : E d) 1 ↦
      radialDeriv u x₀ (x₀ + τ • (ω : E d)) ^ 2) σ :=
    integrable_toSphere_of_bound (hrd.pow_const 2) x₀ τ (B := (L : ℝ) ^ 2) fun ω ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_radialDeriv_le hu _ _) 2
  rw [integral_congr_ae (g := fun ω : sphere (0 : E d) 1 ↦
      (α ^ 2 * radialDeriv u x₀ (x₀ + τ • (ω : E d)) ^ 2 -
        2 * α * β * (u (x₀ + τ • (ω : E d)) * radialDeriv u x₀ (x₀ + τ • (ω : E d)))) +
        β ^ 2 * u (x₀ + τ • (ω : E d)) ^ 2) (ae_of_all _ fun ω ↦ by ring),
    integral_add (f := fun ω : sphere (0 : E d) 1 ↦
        α ^ 2 * radialDeriv u x₀ (x₀ + τ • (ω : E d)) ^ 2 -
        2 * α * β * (u (x₀ + τ • (ω : E d)) * radialDeriv u x₀ (x₀ + τ • (ω : E d))))
      ((hint_a.const_mul _).sub (hint_k.const_mul _)) (hint_m.const_mul _),
    integral_sub (hint_a.const_mul _) (hint_k.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul]
  rfl

/-- The defect integrand, `|x - x₀|^{-d-2} ((x - x₀) · ∇u(x) - u(x))²`. -/
private noncomputable def defectDensity (u : E d → ℝ) (x₀ x : E d) : ℝ :=
  ‖x - x₀‖ ^ (-(d : ℝ) - 2) * (inner ℝ (x - x₀) (∇ u x) - u x) ^ 2

private theorem measurable_defectDensity {u : E d → ℝ} (hu : Continuous u) (x₀ : E d) :
    Measurable (defectDensity u x₀) :=
  ((measurable_id.sub_const x₀).norm.pow_const _).mul
    ((((measurable_id.sub_const x₀).inner (measurable_gradient u)).sub hu.measurable).pow_const 2)

private theorem defectDensity_le (hu : LipschitzWith L u) (hx₀ : u x₀ = 0) {r : ℝ} (hr : 0 < r)
    {x : E d} (hx : r ≤ ‖x - x₀‖) :
    defectDensity u x₀ x ≤ 4 * (L : ℝ) ^ 2 * r ^ (-(d : ℝ)) := by
  have hpos : 0 < ‖x - x₀‖ := hr.trans_le hx
  have h1 : |inner ℝ (x - x₀) (∇ u x)| ≤ ‖x - x₀‖ * L :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_gradient_le_of_lipschitzWith hu x) (norm_nonneg _))
  have h2 : |u x| ≤ L * ‖x - x₀‖ := by
    have := hu.dist_le_mul x x₀
    rwa [Real.dist_eq, hx₀, sub_zero, dist_eq_norm] at this
  have hsq : (inner ℝ (x - x₀) (∇ u x) - u x) ^ 2 ≤ 4 * (L : ℝ) ^ 2 * ‖x - x₀‖ ^ (2 : ℝ) := by
    rw [Real.rpow_two, ← sq_abs]
    have : |inner ℝ (x - x₀) (∇ u x) - u x| ≤ 2 * L * ‖x - x₀‖ :=
      (abs_sub _ _).trans (by linarith)
    nlinarith [abs_nonneg (inner ℝ (x - x₀) (∇ u x) - u x)]
  have hpow : ‖x - x₀‖ ^ (-(d : ℝ) - 2) * ‖x - x₀‖ ^ (2 : ℝ) = ‖x - x₀‖ ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add hpos]; congr 1; ring
  calc defectDensity u x₀ x ≤ ‖x - x₀‖ ^ (-(d : ℝ) - 2) * (4 * (L : ℝ) ^ 2 * ‖x - x₀‖ ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg (norm_nonneg _) _)
    _ = 4 * (L : ℝ) ^ 2 * ‖x - x₀‖ ^ (-(d : ℝ)) := by rw [← hpow]; ring
    _ ≤ 4 * (L : ℝ) ^ 2 * r ^ (-(d : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hr hx (neg_nonpos.mpr (Nat.cast_nonneg d))) (by positivity)

/-- On the sphere of radius `τ > 0`, the defect integrand is
`τ^{-d-2} (τ ∂ᵣu - u)²(x₀ + τω)`. -/
private theorem defectDensity_add_smul (u : E d → ℝ) (x₀ : E d) {τ : ℝ} (hτ : 0 < τ)
    (ω : sphere (0 : E d) 1) :
    defectDensity u x₀ (x₀ + τ • (ω : E d)) = τ ^ (-(d : ℝ) - 2) *
      (τ * radialDeriv u x₀ (x₀ + τ • (ω : E d)) - 1 * u (x₀ + τ • (ω : E d))) ^ 2 := by
  have hω : ‖(ω : E d)‖ = 1 := norm_eq_of_mem_sphere ω
  rw [defectDensity, radialDeriv_add_smul u x₀ hτ ω, add_sub_cancel_left, norm_smul, hω, mul_one,
    Real.norm_of_nonneg hτ.le, inner_smul_left, real_inner_comm, one_mul]
  rfl

/-- **The defect in polar form**: `D(u, x₀; r, s) = ∫_r^s weissRate u x₀ t dt` for `0 < r ≤ s`,
when `u` is Lipschitz with `u(x₀) = 0`. -/
theorem weissDefect_eq_integral_weissRate (hd : 1 ≤ d) (hu : LipschitzWith L u) (hx₀ : u x₀ = 0)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    weissDefect u x₀ r s = ∫ t in r..s, weissRate u x₀ t := by
  have hs : 0 ≤ s := hr.le.trans hrs
  set h := (ball x₀ r)ᶜ.indicator (defectDensity u x₀) with hh
  have hhm : Measurable h :=
    (measurable_defectDensity hu.continuous x₀).indicator measurableSet_ball.compl
  have hC : ∀ x, |h x| ≤ 4 * (L : ℝ) ^ 2 * r ^ (-(d : ℝ)) := by
    intro x
    by_cases hx : x ∈ ball x₀ r
    · rw [hh, indicator_of_notMem (fun h' ↦ (mem_compl_iff _ _).mp h' hx), abs_zero]; positivity
    · rw [hh, indicator_of_mem (show x ∈ (ball x₀ r)ᶜ from hx)]
      rw [mem_ball, dist_eq_norm, not_lt] at hx
      have hnn : 0 ≤ defectDensity u x₀ x :=
        mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)
      rw [abs_of_nonneg hnn]
      exact defectDensity_le hu hx₀ hr hx
  have h1 : weissDefect u x₀ r s = ∫ x in ball x₀ s, h x * ‖x - x₀‖ ^ (0 : ℝ) := by
    simp only [Real.rpow_zero, mul_one]
    rw [hh, setIntegral_indicator measurableSet_ball.compl, ← sdiff_eq]
    rfl
  rw [h1, setIntegral_ball_mul_rpow_eq hd hhm hC x₀ (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith) hs, add_zero]
  -- the radial profile is `weissRate` on `[r, s]` and `0` on `(0, r)`
  have hprof : ∀ τ, 0 < τ → τ ^ ((d : ℝ) - 1) * ∫ ω : sphere (0 : E d) 1,
      h (x₀ + τ • (ω : E d)) ∂(volume : Measure (E d)).toSphere =
      (Ici r).indicator (weissRate u x₀) τ := by
    intro τ hτ
    have hnorm : ∀ ω : sphere (0 : E d) 1, ‖x₀ + τ • (ω : E d) - x₀‖ = τ := fun ω ↦ by
      rw [add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere ω, mul_one,
        Real.norm_of_nonneg hτ.le]
    by_cases hτr : τ < r
    · have h0 : ∀ ω : sphere (0 : E d) 1, h (x₀ + τ • (ω : E d)) = 0 := fun ω ↦ by
        rw [hh, indicator_of_notMem]
        rw [mem_compl_iff, not_not, mem_ball, dist_eq_norm, hnorm]; exact hτr
      simp only [h0, integral_zero, mul_zero]
      rw [indicator_of_notMem (show τ ∉ Ici r from fun h' ↦ (not_le.mpr hτr) h')]
    · rw [not_lt] at hτr
      have hF : ∀ ω : sphere (0 : E d) 1, h (x₀ + τ • (ω : E d)) =
          defectDensity u x₀ (x₀ + τ • (ω : E d)) := fun ω ↦ by
        rw [hh, indicator_of_mem]
        rw [mem_compl_iff, mem_ball, dist_eq_norm, hnorm, not_lt]; exact hτr
      simp only [hF, defectDensity_add_smul u x₀ hτ]
      rw [integral_const_mul, integral_sq_sub_eq hu hx₀ hτ.le,
        indicator_of_mem (show τ ∈ Ici r from hτr), weissRate, ← mul_assoc,
        ← Real.rpow_add hτ, show (d : ℝ) - 1 + (-(d : ℝ) - 2) = -(3 : ℕ) by push_cast; ring,
        Real.rpow_neg hτ.le, Real.rpow_natCast]
      field_simp
  rw [intervalIntegral.integral_congr_ae (g := (Ici r).indicator (weissRate u x₀))
      (ae_of_all _ fun τ hτ ↦ by
        rw [uIoc_of_le hs] at hτ
        exact hprof τ hτ.1),
    intervalIntegral.integral_of_le hs, intervalIntegral.integral_of_le hrs,
    setIntegral_indicator measurableSet_Ici,
    show Ioc 0 s ∩ Ici r = Icc r s by
      ext τ
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨hr.trans_le h1, h2⟩, h1⟩,
    integral_Icc_eq_integral_Ioc]

/-- The defect is nonnegative. -/
theorem weissDefect_nonneg (u : E d → ℝ) (x₀ : E d) (r s : ℝ) : 0 ≤ weissDefect u x₀ r s :=
  setIntegral_nonneg (measurableSet_ball.diff measurableSet_ball) fun _ _ ↦
    mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _)

/-! ### The integrated inequality -/

private theorem intervalIntegrable_weissRate (hu : LipschitzWith L u) (hx₀ : u x₀ = 0)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) : IntervalIntegrable (weissRate u x₀) volume r s := by
  set σ := (volume : Measure (E d)).toSphere.real univ
  have hσ : 0 ≤ σ := measureReal_nonneg
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hrs]
  have hm : Measurable (weissRate u x₀) := by
    have hA := (stronglyMeasurable_radialA u x₀).measurable
    have hK := (stronglyMeasurable_radialK hu.continuous.measurable x₀).measurable
    have hM := (stronglyMeasurable_radialM hu.continuous.measurable x₀).measurable
    unfold weissRate
    fun_prop
  refine IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable
    (4 * ((L : ℝ) ^ 2 * σ) / r) ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine ae_of_all _ fun t ht ↦ ?_
  have ht0 : 0 < t := hr.trans_le ht.1
  have hA := radialA_le hu x₀ t
  have hA0 := radialA_nonneg u x₀ t
  have hK := abs_radialK_le hu hx₀ ht0.le
  have hM := radialM_le hu hx₀ ht0.le
  have hM0 := radialM_nonneg u x₀ t
  rw [Real.norm_eq_abs, weissRate]
  have e1 : |radialA u x₀ t / t| ≤ (L : ℝ) ^ 2 * σ / t := by
    rw [abs_div, abs_of_pos ht0, abs_of_nonneg hA0]; gcongr
  have e2 : |2 * radialK u x₀ t / t ^ 2| ≤ 2 * ((L : ℝ) ^ 2 * σ) / t := by
    rw [abs_div, abs_mul, abs_two, abs_of_pos (pow_pos ht0 2), div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have e3 : |radialM u x₀ t / t ^ 3| ≤ (L : ℝ) ^ 2 * σ / t := by
    rw [abs_div, abs_of_pos (pow_pos ht0 3), abs_of_nonneg hM0,
      div_le_div_iff₀ (by positivity) ht0]
    nlinarith
  have e4 : 4 * ((L : ℝ) ^ 2 * σ) / t ≤ 4 * ((L : ℝ) ^ 2 * σ) / r := by
    gcongr; exact ht.1
  calc |radialA u x₀ t / t - 2 * radialK u x₀ t / t ^ 2 + radialM u x₀ t / t ^ 3|
      ≤ |radialA u x₀ t / t| + |2 * radialK u x₀ t / t ^ 2| + |radialM u x₀ t / t ^ 3| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ (L : ℝ) ^ 2 * σ / t + 2 * ((L : ℝ) ^ 2 * σ) / t + (L : ℝ) ^ 2 * σ / t := by
        linarith
    _ = 4 * ((L : ℝ) ^ 2 * σ) / t := by ring
    _ ≤ 4 * ((L : ℝ) ^ 2 * σ) / r := e4

/-- `W` is absolutely continuous on `[r, s]` for `0 < r ≤ s`. -/
theorem absolutelyContinuousOnInterval_weissW (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (hx₀ : u x₀ = 0) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    AbsolutelyContinuousOnInterval (weissW u x₀) r s := by
  obtain ⟨K₁, hK₁⟩ := exists_lipschitzOnWith_setIntegral_weissDensity hd hu x₀ s
  obtain ⟨K₂, hK₂⟩ := exists_lipschitzOnWith_radialM hd hu hx₀ s
  have hsub : uIcc r s ⊆ Icc 0 s := by
    rw [uIcc_of_le hrs]; exact Icc_subset_Icc hr.le le_rfl
  have hinv : ∀ n : ℕ, AbsolutelyContinuousOnInterval (fun t : ℝ ↦ (t ^ n)⁻¹) r s := fun n ↦
    ContDiffOn.absolutelyContinuousOnInterval fun t ht ↦ by
      rw [uIcc_of_le hrs] at ht
      exact ((contDiff_id.pow n).contDiffAt.inv
        (pow_ne_zero n (hr.trans_le ht.1).ne')).contDiffWithinAt
  refine ((((hK₁.mono hsub).absolutelyContinuousOnInterval.fun_mul (hinv d)).fun_sub
    ((hK₂.mono hsub).absolutelyContinuousOnInterval.fun_mul (hinv 2)))).congr fun t _ ↦ ?_
  simp only [weissW_eq hu, div_eq_mul_inv]

/-- **Weiss monotonicity, integrated form.** For `0 < r < s`,
`D(u, x₀; r, s) ≤ W(u, x₀, s) - W(u, x₀, r)`. -/
theorem weissDefect_le_weissW_sub (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hx₀ : u x₀ = 0) {r s : ℝ} (hr : 0 < r)
    (hrs : r ≤ s) : weissDefect u x₀ r s ≤ weissW u x₀ s - weissW u x₀ r := by
  have hAC := absolutelyContinuousOnInterval_weissW hd hu hx₀ hr hrs
  rw [weissDefect_eq_integral_weissRate hd hu hx₀ hr hrs, ← hAC.integral_deriv_eq_sub]
  refine intervalIntegral.integral_mono_ae_restrict hrs
    (intervalIntegrable_weissRate hu hx₀ hr hrs) hAC.intervalIntegrable_deriv ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_weissRate_le_deriv_weissW hd hu hmin hx₀] with t ht htI
  exact ht (hr.trans_le htI.1)

/-! ### The bound -/

/-- `|W(u, x₀, r)| ≤ (L² + 1) |B₁| + L² σ(𝕊)` for `r > 0`, when `u` is `L`-Lipschitz with
`u(x₀) = 0`. -/
theorem abs_weissW_le (hd : 1 ≤ d) (hu : LipschitzWith L u) (hx₀ : u x₀ = 0) {r : ℝ}
    (hr : 0 < r) :
    |weissW u x₀ r| ≤ ((L : ℝ) ^ 2 + 1) * volume.real (ball (0 : E d) 1) +
      (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ := by
  have := nontrivial_E hd
  set σ := (volume : Measure (E d)).toSphere.real univ
  set V := volume.real (ball (0 : E d) 1)
  set Jb := ∫ x in ball x₀ r, weissDensity u x
  have hJ0 : 0 ≤ Jb := setIntegral_nonneg measurableSet_ball fun x _ ↦ weissDensity_nonneg u x
  have hvol : volume.real (ball x₀ r) = r ^ d * V := by
    rw [measureReal_def, Measure.addHaar_ball _ _ hr.le, finrank_euclideanSpace_fin,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    rfl
  have hJ : Jb ≤ ((L : ℝ) ^ 2 + 1) * (r ^ d * V) := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := weissDensity u)
      (s := ball x₀ r) (C := (L : ℝ) ^ 2 + 1) measure_ball_lt_top fun x _ ↦ by
        rw [Real.norm_eq_abs]; exact abs_weissDensity_le hu x
    rw [Real.norm_eq_abs, abs_of_nonneg hJ0, hvol] at h
    exact h
  have hrd : 0 < r ^ d := pow_pos hr d
  have hA : Jb / r ^ d ≤ ((L : ℝ) ^ 2 + 1) * V := by
    rw [div_le_iff₀ hrd]; linarith
  have hA0 : 0 ≤ Jb / r ^ d := div_nonneg hJ0 hrd.le
  have hB : radialM u x₀ r / r ^ 2 ≤ (L : ℝ) ^ 2 * σ := by
    rw [div_le_iff₀ (pow_pos hr 2)]; linarith [radialM_le hu hx₀ hr.le]
  have hB0 : 0 ≤ radialM u x₀ r / r ^ 2 := div_nonneg (radialM_nonneg u x₀ r) (sq_nonneg r)
  rw [weissW_eq hu, abs_le]
  constructor <;> linarith

/-- **Weiss monotonicity for sign-changing minimizers** (after Weiss 1999). -/
theorem weissMonotone : WeissMonotoneStatement := by
  intro d hd u L x₀ hu hmin hx₀
  have hd1 : 1 ≤ d := by omega
  exact ⟨fun r s hr hrs ↦ ⟨weissDefect_le_weissW_sub hd1 hu hmin hx₀ hr hrs.le,
    weissDefect_nonneg u x₀ r s⟩, fun r hr ↦ abs_weissW_le hd1 hu hx₀ hr⟩

/-! ### Scaling -/

/-- The rescaling `u_{x₀,R}(y) = u(x₀ + Ry)/R` of an `L`-Lipschitz function is `L`-Lipschitz for
`R > 0`. -/
theorem lipschitzWith_blowup (hu : LipschitzWith L u) (x₀ : E d) {R : ℝ} (hR : 0 < R) :
    LipschitzWith L (blowup u x₀ R) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have h := hu.dist_le_mul (x₀ + R • x) (x₀ + R • y)
  rw [Real.dist_eq, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_of_nonneg hR.le] at h
  rw [Real.dist_eq, dist_eq_norm, blowup, blowup, ← sub_div,
    abs_div, abs_of_pos hR, div_le_iff₀ hR]
  linarith

/-- Change of variables `x = x₀ + R y` on sets `S, T` with `x₀ + R y ∈ T ↔ y ∈ S`. -/
private theorem setIntegral_comp_add_smul (f : E d → ℝ) (x₀ : E d) {R : ℝ} (hR : 0 < R)
    {S T : Set (E d)} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : ∀ y, x₀ + R • y ∈ T ↔ y ∈ S) :
    ∫ y in S, f (x₀ + R • y) = (R ^ d)⁻¹ * ∫ x in T, f x := by
  set F := T.indicator f with hF
  have hI : ∫ x in T, f x = ∫ x, F (x₀ + x) := by
    rw [integral_add_left_eq_self F x₀, hF, integral_indicator hT]
  have hpt : ∀ y, F (x₀ + R • y) = S.indicator (fun y ↦ f (x₀ + R • y)) y := fun y ↦ by
    by_cases hy : y ∈ S
    · rw [hF, indicator_of_mem ((hST y).mpr hy), indicator_of_mem hy]
    · rw [hF, indicator_of_notMem (fun h ↦ hy ((hST y).mp h)), indicator_of_notMem hy]
  rw [← integral_indicator hS]
  simp_rw [← hpt]
  rw [Measure.integral_comp_smul (μ := (volume : Measure (E d))) (fun x ↦ F (x₀ + x)) R,
    finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hR d)), smul_eq_mul, hI]

private theorem add_smul_mem_ball_iff (x₀ : E d) {R : ℝ} (hR : 0 < R) (ρ : ℝ) (y : E d) :
    x₀ + R • y ∈ ball x₀ (R * ρ) ↔ y ∈ ball (0 : E d) ρ := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_zero_right, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg hR.le, mul_lt_mul_iff_right₀ hR]

theorem weissDensity_blowup (u : E d → ℝ) (x₀ : E d) {R : ℝ} (hR : 0 < R) (y : E d) :
    weissDensity (blowup u x₀ R) y = weissDensity u (x₀ + R • y) := by
  have hpos : 0 < blowup u x₀ R y ↔ 0 < u (x₀ + R • y) := by
    rw [blowup]; exact div_pos_iff_of_pos_right hR
  rw [weissDensity, weissDensity, gradient_blowup u x₀ hR.ne']
  congr 1
  by_cases h : 0 < u (x₀ + R • y)
  · rw [indicator_of_mem (show y ∈ {y | 0 < blowup u x₀ R y} from hpos.mpr h),
      indicator_of_mem (show x₀ + R • y ∈ {y | 0 < u y} from h)]
    rfl
  · rw [indicator_of_notMem (show y ∉ {y | 0 < blowup u x₀ R y} from fun h' ↦ h (hpos.mp h')),
      indicator_of_notMem (show x₀ + R • y ∉ {y | 0 < u y} from h)]

/-- **Scaling of the Weiss functional**:
`W(u_{x₀,R}, 0, ρ) = W(u, x₀, Rρ)` for `R > 0`, where `u_{x₀,R}(y) = u(x₀ + Ry)/R`
(`blowup`). -/
theorem weissW_blowup (hu : LipschitzWith L u) (x₀ : E d) {R : ℝ} (hR : 0 < R) (ρ : ℝ) :
    weissW (blowup u x₀ R) 0 ρ = weissW u x₀ (R * ρ) := by
  rw [weissW_eq (lipschitzWith_blowup hu x₀ hR), weissW_eq hu]
  have hJ : ∫ y in ball (0 : E d) ρ, weissDensity (blowup u x₀ R) y =
      (R ^ d)⁻¹ * ∫ x in ball x₀ (R * ρ), weissDensity u x := by
    simp_rw [weissDensity_blowup u x₀ hR]
    exact setIntegral_comp_add_smul _ x₀ hR measurableSet_ball measurableSet_ball
      (add_smul_mem_ball_iff x₀ hR ρ)
  have hM : radialM (blowup u x₀ R) 0 ρ = radialM u x₀ (R * ρ) / R ^ 2 := by
    rw [radialM, radialM, ← integral_div]
    congr 1
    funext ω
    rw [blowup, zero_add, smul_smul, div_pow]
  rw [hJ, hM, mul_pow, mul_pow]
  have hRd : R ^ d ≠ 0 := pow_ne_zero d hR.ne'
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  rcases eq_or_ne ρ 0 with rfl | hρ
  · simp
  · field_simp

/-- **Scaling of the Weiss defect**:
`D(u_{x₀,R}, 0; r, s) = D(u, x₀; Rr, Rs)` for `R > 0`. -/
theorem weissDefect_blowup (u : E d → ℝ) (x₀ : E d) {R : ℝ} (hR : 0 < R) (r s : ℝ) :
    weissDefect (blowup u x₀ R) 0 r s = weissDefect u x₀ (R * r) (R * s) := by
  have hpt : ∀ y : E d, ‖y - 0‖ ^ (-(d : ℝ) - 2) *
      (inner ℝ (y - 0) (∇ (blowup u x₀ R) y) - blowup u x₀ R y) ^ 2 =
      R ^ d * (‖x₀ + R • y - x₀‖ ^ (-(d : ℝ) - 2) *
        (inner ℝ (x₀ + R • y - x₀) (∇ u (x₀ + R • y)) - u (x₀ + R • y)) ^ 2) := fun y ↦ by
    rw [gradient_blowup u x₀ hR.ne', sub_zero, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hR.le, Real.mul_rpow hR.le (norm_nonneg _), inner_smul_left,
      RCLike.conj_to_real, blowup]
    have hRpow : R ^ d * R ^ (-(d : ℝ) - 2) * R ^ 2 = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast R 2, ← Real.rpow_add hR, ← Real.rpow_add hR,
        show (d : ℝ) + (-(d : ℝ) - 2) + ((2 : ℕ) : ℝ) = 0 by push_cast; ring, Real.rpow_zero]
    have : R * inner ℝ y (∇ u (x₀ + R • y)) - u (x₀ + R • y) =
        R * (inner ℝ y (∇ u (x₀ + R • y)) - u (x₀ + R • y) / R) := by
      field_simp
    rw [this, mul_pow]
    linear_combination -(‖y‖ ^ (-(d : ℝ) - 2) *
      (inner ℝ y (∇ u (x₀ + R • y)) - u (x₀ + R • y) / R) ^ 2) * hRpow
  have hiff : ∀ y, x₀ + R • y ∈ ball x₀ (R * s) \ ball x₀ (R * r) ↔
      y ∈ ball (0 : E d) s \ ball 0 r := fun y ↦ by
    rw [Set.mem_sdiff, Set.mem_sdiff, add_smul_mem_ball_iff x₀ hR, add_smul_mem_ball_iff x₀ hR]
  rw [weissDefect, weissDefect]
  simp_rw [hpt]
  rw [integral_const_mul, setIntegral_comp_add_smul (fun x ↦ ‖x - x₀‖ ^ (-(d : ℝ) - 2) *
      (inner ℝ (x - x₀) (∇ u x) - u x) ^ 2) x₀ hR (measurableSet_ball.diff measurableSet_ball)
      (measurableSet_ball.diff measurableSet_ball) hiff, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero d hR.ne'), one_mul]

/-! ### Limits -/

/-- `W` is nondecreasing on `(0, ∞)`. -/
theorem monotoneOn_weissW (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hx₀ : u x₀ = 0) :
    MonotoneOn (weissW u x₀) (Ioi 0) := fun r hr s _ hrs ↦ by
  have h := weissDefect_le_weissW_sub hd hu hmin hx₀ (show (0 : ℝ) < r from hr) hrs
  linarith [weissDefect_nonneg u x₀ r s]

/-- **Limits of the Weiss functional.** The limits
`W(0⁺) = lim_{r → 0⁺} W(u, x₀, r)` and `W(∞) = lim_{r → ∞} W(u, x₀, r)` exist, are finite, and
satisfy `W(0⁺) ≤ W(∞)`; if `W(0⁺) = W(∞)`, then `D(u, x₀; r, s) = 0` for all `0 < r < s`. -/
theorem exists_tendsto_weissW (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hx₀ : u x₀ = 0) :
    ∃ W₀ W₁ : ℝ, Tendsto (weissW u x₀) (𝓝[>] 0) (𝓝 W₀) ∧
      Tendsto (weissW u x₀) atTop (𝓝 W₁) ∧ W₀ ≤ W₁ ∧
      (W₀ = W₁ → ∀ r s : ℝ, 0 < r → r < s → weissDefect u x₀ r s = 0) := by
  set W := weissW u x₀
  set C := ((L : ℝ) ^ 2 + 1) * volume.real (ball (0 : E d) 1) +
    (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ
  have hmono := monotoneOn_weissW hd hu hmin hx₀
  have hbd : ∀ r, 0 < r → |W r| ≤ C := fun r hr ↦ abs_weissW_le hd hu hx₀ hr
  have hbdd : BddBelow (W '' Ioi 0) := ⟨-C, by
    rintro _ ⟨r, hr, rfl⟩; exact (abs_le.mp (hbd r hr)).1⟩
  -- the monotone extension `g(t) = W(max t 1)`
  set g : ℝ → ℝ := fun t ↦ W (max t 1)
  have hg : Monotone g := fun a b hab ↦
    hmono (show (0 : ℝ) < max a 1 from lt_max_of_lt_right one_pos)
      (show (0 : ℝ) < max b 1 from lt_max_of_lt_right one_pos) (max_le_max hab le_rfl)
  have hgbdd : BddAbove (range g) := ⟨C, by
    rintro _ ⟨t, rfl⟩; exact (abs_le.mp (hbd _ (lt_max_of_lt_right one_pos))).2⟩
  have hlim₀ := hmono.tendsto_nhdsGT hbdd
  have hlim₁ : Tendsto W atTop (𝓝 (⨆ t, g t)) := by
    refine (tendsto_atTop_ciSup hg hgbdd).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    simp only [g, max_eq_left ht]
  have hW₀ : ∀ r, 0 < r → sInf (W '' Ioi 0) ≤ W r := fun r hr ↦ csInf_le hbdd ⟨r, hr, rfl⟩
  have hW₁ : ∀ s, 0 < s → W s ≤ ⨆ t, g t := fun s hs ↦
    (hmono hs (lt_max_of_lt_right one_pos) (le_max_left s 1)).trans (le_ciSup hgbdd s)
  refine ⟨_, _, hlim₀, hlim₁, (hW₀ 1 one_pos).trans (hW₁ 1 one_pos), fun heq r s hr hrs ↦ ?_⟩
  have h := weissDefect_le_weissW_sub hd hu hmin hx₀ hr hrs.le
  have h1 := hW₀ r hr
  have h2 := hW₁ s (hr.trans hrs)
  exact le_antisymm (by linarith) (weissDefect_nonneg u x₀ r s)

end

end EllipticBernoulli
