/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.GaussianPoincare.Weight
public import EllipticBernoulli.Statements.TwoPhase
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
import EllipticBernoulli.TwoPhase.EnergyIdentity
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sobolev.GaussianPoincare
import EllipticBernoulli.Sobolev.Uniqueness
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Homogeneous two-phase functions in every dimension

* `fderiv_apply_self_eq_of_homogeneous`: **Euler's relation** `Dw(x) x = w(x)` for a positively
  `1`-homogeneous `w` at every point of differentiability.
* `integral_norm_sq_gradient_mul_gaussWeight`: **Gaussian energy
  identity.** If `w ≥ 0` is Lipschitz, positively `1`-homogeneous and harmonic on `{w > 0}`, then
  `∫ |∇w|² e^{-|x|²/2} = ∫ w² e^{-|x|²/2}`.
* `homogeneousTwoPhaseIn` (general `d`): a Lipschitz, positively
  `1`-homogeneous `v`, harmonic on `{v > 0}` and on `{v < 0}`, with both phases nonempty, is a
  two-plane function `a (x·e)⁺ - b (x·e)⁻`. The argument works in every dimension;
  `homogeneousTwoPhaseIn_of_two_le` is the form with the hypothesis `2 ≤ d`.

## Proof of the Gaussian energy identity

Test the energy identity `∫ |∇w|² η = -∫ w ∇w · ∇η` (`integral_norm_sq_gradient_mul_eq_neg`)
with `η_R(x) = e^{-|x|²/2} χ(x/R)`, where `χ` is a smooth bump equal to `1` on the unit ball and
supported in the ball of radius `2`. Since `∇e^{-|x|²/2} = -x e^{-|x|²/2}` and `x · ∇w = w` a.e.
(Euler), `∫ |∇w|² e^{-|x|²/2} χ_R = ∫ w² e^{-|x|²/2} χ_R - R⁻¹ ∫ w e^{-|x|²/2} Dχ(x/R) ∇w`.
The last term is `O(1/R)`; let `R → ∞` by dominated convergence. A smooth bump, rather than a
piecewise-linear radial cutoff, avoids a null set where the cutoff is not differentiable.

## Proof of the classification

Let `A^± = ∫ v^± e^{-|x|²/2} > 0`, `c = A⁺/A⁻` and `G = v⁺ - c v⁻`, so that `∫ G e^{-|x|²/2} = 0`.
A.e., `|∇G|² = |∇v⁺|² + c² |∇v⁻|²` (locally `G = v⁺` on `{v > 0}`, `G = -c v⁻` on `{v < 0}`, and
all three gradients vanish a.e. on `{v = 0}` by Stampacchia). The Gaussian energy identity for
`v^±` and `v⁺ v⁻ = 0` give `∫ |∇G|² e^{-|x|²/2} = ∫ G² e^{-|x|²/2}`, which is equality in the
Gaussian Poincaré inequality, so `G(x) = ⟨p, x⟩ + q` (`exists_eq_inner_add_of_le_gaussVariance`),
with `q = G(0) = 0`. Then `v = G⁺ - G⁻/c`, `p ≠ 0`, and `e = p/|p|`, `a = |p|`, `b = |p|/c`.

The spectral idea is that of De Philippis–Spolaor–Velichkov (arXiv:1911.02165), Lemma 2.2, which
classifies the blow-up limits at two-phase points of minimizers of the two-phase functional with
both phases penalized; there the nondegeneracy of both phases and the Weiss formula give a
homogeneous limit whose restriction to the sphere is an eigenfunction. Here the classification is
stated directly for `1`-homogeneous functions harmonic in both phases, and the identification of
the first eigenfunctions is replaced by the equality case of the Gaussian Poincaré inequality.

## References

* G. De Philippis, L. Spolaor, B. Velichkov, *Regularity of the free boundary for the two-phase
  Bernoulli problem*, Invent. Math. 225 (2021), 347–394; arXiv:1911.02165.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient NNReal

namespace EllipticBernoulli

variable {d : ℕ}

public section

/-- **Euler's relation.** If `w(t x) = t w(x)` for every `t > 0`, then `Dw(x) x = w(x)` at every
point `x` where `w` is differentiable. -/
theorem fderiv_apply_self_eq_of_homogeneous {w : E d → ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, w (t • x) = t * w x) {x : E d}
    (hx : DifferentiableAt ℝ w x) : fderiv ℝ w x x = w x := by
  have h := hx.hasFDerivAt.apply_self_eq_smul_of_eventuallyEq (w := id) (hasDerivAt_id 1) <| by
    filter_upwards [lt_mem_nhds one_pos] with t ht
    simp [hhom t ht x]
  simpa using h

/-- A positively `1`-homogeneous function vanishes at the origin. -/
theorem eq_zero_at_zero_of_homogeneous {w : E d → ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, w (t • x) = t * w x) : w 0 = 0 := by
  have := hhom 2 two_pos 0
  rw [smul_zero] at this
  linarith

end

/-- The bump `χ` with `χ = 1` on the unit ball and support in the ball of radius `2`. -/
private noncomputable def unitBump : ContDiffBump (0 : E d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The cutoff `η_R(x) = e^{-|x|²/2} χ(x / R)`. -/
private noncomputable def gaussCutoff (R : ℝ) (x : E d) : ℝ :=
  gaussWeight x * unitBump (R⁻¹ • x)

private theorem hasFDerivAt_gaussCutoff (R : ℝ) (x : E d) :
    HasFDerivAt (gaussCutoff R)
      (gaussWeight x • ((fderiv ℝ unitBump (R⁻¹ • x)).comp
          (R⁻¹ • ContinuousLinearMap.id ℝ (E d))) +
        unitBump (R⁻¹ • x) • (-gaussWeight x • innerSL ℝ x)) x := by
  have hχ : HasFDerivAt (fun y : E d ↦ unitBump (R⁻¹ • y))
      ((fderiv ℝ unitBump (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ (E d))) x :=
    ((unitBump.contDiff (n := 1)).differentiable one_ne_zero _).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul R⁻¹)
  exact (hasFDerivAt_gaussWeight x).mul hχ

private theorem contDiff_gaussCutoff (R : ℝ) : ContDiff ℝ 1 (gaussCutoff (d := d) R) :=
  contDiff_gaussWeight.mul (unitBump.contDiff.comp (contDiff_const_smul R⁻¹))

private theorem hasCompactSupport_gaussCutoff {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (gaussCutoff (d := d) R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E d) (2 * R)) fun x hx ↦ ?_
  have h2 : unitBump (R⁻¹ • x) = 0 := by
    refine Function.notMem_support.1 fun hs ↦ hx ?_
    rw [unitBump.support_eq, mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hR] at hs
    rw [mem_closedBall, dist_zero_right]
    have hr : (unitBump (d := d)).rOut = 2 := rfl
    rw [hr, inv_mul_lt_iff₀ hR, mul_comm] at hs
    exact hs.le
  simp [gaussCutoff, h2]

/-- **Gaussian energy identity.** Let `w ≥ 0` be Lipschitz,
positively `1`-homogeneous, and harmonic on `{w > 0}`. Then
`∫ |∇w|² e^{-|x|²/2} = ∫ w² e^{-|x|²/2}`. Gradients are pointwise (`0` where `w` is not
differentiable). -/
public theorem integral_norm_sq_gradient_mul_gaussWeight {w : E d → ℝ} {K : ℝ≥0}
    (hw : LipschitzWith K w) (hw0 : ∀ x, 0 ≤ w x) (hharm : HarmonicOnNhd w {x | 0 < w x})
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, w (t • x) = t * w x) :
    ∫ x, ‖∇ w x‖ ^ 2 * gaussWeight x = ∫ x, w x ^ 2 * gaussWeight x := by
  have hw00 : w 0 = 0 := eq_zero_at_zero_of_homogeneous hhom
  have hwle : ∀ x, |w x| ≤ K * ‖x‖ := fun x ↦ by
    have := hw.dist_le_mul x 0
    rwa [dist_zero_right, Real.dist_eq, hw00, sub_zero] at this
  have hgw : ∀ x, ‖∇ w x‖ ≤ K := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hw
  -- the bound on `Dχ`
  obtain ⟨C₁, hC₁⟩ := ((unitBump (d := d)).contDiff.continuous_fderiv
    (by simp : (1 : WithTop ℕ∞) ≠ 0)).bounded_above_of_compact_support
    (HasCompactSupport.fderiv (𝕜 := ℝ) (unitBump (d := d)).hasCompactSupport)
  -- Euler's relation a.e.
  have heuler : ∀ᵐ x, inner ℝ x (∇ w x) = w x := by
    filter_upwards [hw.ae_differentiableAt] with x hx
    rw [real_inner_comm, inner_gradient_left_eq_fderiv,
      fderiv_apply_self_eq_of_homogeneous hhom hx]
  set χ : E d → ℝ := fun x ↦ unitBump (d := d) x with hχ_def
  have hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := fun x ↦ ⟨unitBump.nonneg, unitBump.le_one⟩
  have hDχ : Continuous (fderiv ℝ χ) :=
    (unitBump (d := d)).contDiff.continuous_fderiv (by simp : (1 : WithTop ℕ∞) ≠ 0)
  -- the three integrands
  set A : ℝ → E d → ℝ := fun R x ↦ ‖∇ w x‖ ^ 2 * χ (R⁻¹ • x) * gaussWeight x with hA
  set B : ℝ → E d → ℝ := fun R x ↦ w x ^ 2 * χ (R⁻¹ • x) * gaussWeight x with hB
  set Ce : ℝ → E d → ℝ := fun R x ↦
    w x * (R⁻¹ * fderiv ℝ χ (R⁻¹ • x) (∇ w x)) * gaussWeight x with hCe
  have hmD : ∀ R : ℝ, Measurable fun x ↦ fderiv ℝ χ (R⁻¹ • x) (∇ w x) := fun R ↦
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hDχ.comp (continuous_const_smul R⁻¹)).measurable.prodMk (measurable_gradient w))
  have hχc : Continuous χ := (unitBump (d := d)).contDiff.continuous (n := 0)
  have hwsq : ∀ x, |w x ^ 2| ≤ (K : ℝ) ^ 2 * (1 + ‖x‖ ^ 2) := fun x ↦ by
    rw [abs_pow, mul_add, mul_one]
    have h1 := hwle x
    have h2 : |w x| ^ 2 ≤ (K * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (K : ℝ)]
  have hintB : ∀ R, Integrable (B R) := fun R ↦ by
    refine integrable_mul_gaussWeight
      ((hw.continuous.pow 2).mul (hχc.comp (continuous_const_smul R⁻¹))).aestronglyMeasurable
      (C := (K : ℝ) ^ 2) fun x ↦ ?_
    rw [abs_mul, abs_of_nonneg (hχ01 _).1]
    exact (mul_le_of_le_one_right (abs_nonneg _) (hχ01 _).2).trans (hwsq x)
  have hintCe : ∀ R, Integrable (Ce R) := fun R ↦ by
    refine integrable_mul_gaussWeight
      (hw.continuous.measurable.mul (measurable_const.mul (hmD R))).aestronglyMeasurable
      (C := |R⁻¹| * C₁ * K * K) fun x ↦ ?_
    have h1 : |fderiv ℝ χ (R⁻¹ • x) (∇ w x)| ≤ C₁ * K := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      exact mul_le_mul (hC₁ _) (hgw x) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ 0))
    rw [abs_mul, abs_mul]
    have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
    have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0)
    calc |w x| * (|R⁻¹| * |fderiv ℝ χ (R⁻¹ • x) (∇ w x)|)
        ≤ (K * ‖x‖) * (|R⁻¹| * (C₁ * K)) := by gcongr; exact hwle x
      _ = |R⁻¹| * C₁ * K * K * ‖x‖ := by ring
      _ ≤ |R⁻¹| * C₁ * K * K * (1 + ‖x‖ ^ 2) := by gcongr
  -- the identity for each `R > 0`
  have hid : ∀ R : ℝ, 0 < R → ∫ x, A R x = ∫ x, (B R x - Ce R x) := by
    intro R hR
    obtain ⟨Kη, hKη⟩ := (contDiff_gaussCutoff (d := d) R).lipschitzWith_of_hasCompactSupport
      (hasCompactSupport_gaussCutoff hR) one_ne_zero
    have h := integral_norm_sq_gradient_mul_eq_neg hw hw0 hharm hKη
      (hasCompactSupport_gaussCutoff hR)
    have hl : (fun x ↦ ‖∇ w x‖ ^ 2 * gaussCutoff R x) = A R := by
      funext x; simp only [gaussCutoff, hA]; ring
    rw [hl] at h
    rw [h, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [heuler] with x hx
    rw [real_inner_comm, inner_gradient_left_eq_fderiv, (hasFDerivAt_gaussCutoff R x).fderiv]
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      map_smul, innerSL_apply_apply, smul_eq_mul, hx, hB, hCe]
    ring
  -- limits as `R → ∞`
  have hev : ∀ x : E d, ∀ᶠ R in atTop, χ (R⁻¹ • x) = 1 := fun x ↦ by
    filter_upwards [eventually_gt_atTop ‖x‖] with R hR
    have hR0 : 0 < R := (norm_nonneg x).trans_lt hR
    refine unitBump.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hR0,
      inv_mul_le_iff₀ hR0]
    exact hR.le.trans_eq (mul_one R).symm
  have hlimA : Tendsto (fun R ↦ ∫ x, A R x) atTop (𝓝 (∫ x, ‖∇ w x‖ ^ 2 * gaussWeight x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ (K : ℝ) ^ 2 * gaussWeight x)
      (Eventually.of_forall fun R ↦ (((measurable_gradient w).norm.pow_const 2).mul
        ((hχc.comp (continuous_const_smul R⁻¹)).measurable)).mul
        continuous_gaussWeight.measurable |>.aestronglyMeasurable)
      (Eventually.of_forall fun R ↦ Eventually.of_forall fun x ↦ ?_)
      (integrable_gaussWeight.const_mul _) (Eventually.of_forall fun x ↦ ?_)
    · rw [Real.norm_eq_abs, hA, abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (hχ01 _).1) (gaussWeight_nonneg x))]
      have h1 : ‖∇ w x‖ ^ 2 ≤ (K : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hgw x) 2
      have h2 := mul_le_of_le_one_right (by positivity : 0 ≤ ‖∇ w x‖ ^ 2) (hχ01 (R⁻¹ • x)).2
      exact mul_le_mul_of_nonneg_right (h2.trans h1) (gaussWeight_nonneg x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with R hR
      simp only [hA, hR, mul_one]
  have hlimB : Tendsto (fun R ↦ ∫ x, B R x) atTop (𝓝 (∫ x, w x ^ 2 * gaussWeight x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ w x ^ 2 * gaussWeight x)
      (Eventually.of_forall fun R ↦ (hintB R).aestronglyMeasurable)
      (Eventually.of_forall fun R ↦ Eventually.of_forall fun x ↦ ?_)
      (integrable_mul_gaussWeight (hw.continuous.pow 2).aestronglyMeasurable hwsq)
      (Eventually.of_forall fun x ↦ ?_)
    · rw [Real.norm_eq_abs, hB, abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity)
        (hχ01 _).1) (gaussWeight_nonneg x))]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) (hχ01 _).2)
        (gaussWeight_nonneg x)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev x] with R hR
      simp only [hB, hR, mul_one]
  have hlimCe : Tendsto (fun R ↦ ∫ x, Ce R x) atTop (𝓝 0) := by
    set M : ℝ := ∫ x, C₁ * K * |w x| * gaussWeight x
    have hM : Integrable fun x ↦ C₁ * K * |w x| * gaussWeight x :=
      integrable_mul_gaussWeight (hw.continuous.abs.const_mul _).aestronglyMeasurable
        (C := C₁ * K * K) fun x ↦ by
          have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0)
          have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
          rw [abs_mul, abs_abs, abs_of_nonneg (by positivity : 0 ≤ C₁ * K)]
          calc C₁ * K * |w x| ≤ C₁ * K * (K * ‖x‖) := by gcongr; exact hwle x
            _ = C₁ * K * K * ‖x‖ := by ring
            _ ≤ C₁ * K * K * (1 + ‖x‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hx (mul_nonneg (mul_nonneg hC₁0 K.2) K.2)
    have hbound : ∀ R : ℝ, 0 < R → ‖∫ x, Ce R x‖ ≤ R⁻¹ * M := by
      intro R hR
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hM.const_mul _) (Eventually.of_forall fun x ↦ ?_)
      have h1 : |fderiv ℝ χ (R⁻¹ • x) (∇ w x)| ≤ C₁ * K := by
        rw [← Real.norm_eq_abs]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        exact mul_le_mul (hC₁ _) (hgw x) (norm_nonneg _) ((norm_nonneg _).trans (hC₁ 0))
      rw [Real.norm_eq_abs, hCe, abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.2 hR),
        abs_of_nonneg (gaussWeight_nonneg x)]
      calc |w x| * (R⁻¹ * |fderiv ℝ χ (R⁻¹ • x) (∇ w x)|) * gaussWeight x
          ≤ |w x| * (R⁻¹ * (C₁ * K)) * gaussWeight x := by
            have := gaussWeight_nonneg x
            gcongr
        _ = R⁻¹ * (C₁ * K * |w x| * gaussWeight x) := by ring
    refine squeeze_zero_norm' ?_ (by simpa using tendsto_inv_atTop_zero.mul_const M)
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact hbound R hR
  refine tendsto_nhds_unique hlimA ?_
  have := hlimB.sub hlimCe
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact ((hid R hR).trans (integral_sub (hintB R) (hintCe R))).symm



/-! ### The classification -/

/-- The positive part of a function harmonic on its positivity set is harmonic on its own
positivity set. -/
private theorem harmonicOnNhd_max_zero {w : E d → ℝ} (hw : Continuous w)
    (hH : HarmonicOnNhd w {x | 0 < w x}) :
    HarmonicOnNhd (fun x ↦ max (w x) 0) {x | 0 < max (w x) 0} := by
  intro x hx
  have hx' : 0 < w x := by
    rw [mem_ofPred_eq] at hx
    rcases lt_max_iff.1 hx with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  have hloc : (fun y ↦ max (w y) 0) =ᶠ[𝓝 x] w := by
    filter_upwards [(isOpen_lt continuous_const hw).mem_nhds hx'] with y hy
    exact max_eq_left (le_of_lt hy)
  exact (harmonicAt_congr_nhds hloc).2 (hH x hx')

/-- `∇(k f) = k ∇f`, with no differentiability assumption. -/
private theorem gradient_const_mul (k : ℝ) (f : E d → ℝ) (x : E d) :
    ∇ (fun y ↦ k * f y) x = k • ∇ f x := by
  have : (fun y ↦ k * f y) = k • f := rfl
  rw [this, gradient, gradient, fderiv_const_smul_field, Pi.smul_apply, map_smul]

private theorem gradient_congr_of_eventuallyEq {f g : E d → ℝ} {x : E d} (h : f =ᶠ[𝓝 x] g) :
    ∇ f x = ∇ g x := by
  rw [gradient, gradient, h.fderiv_eq]

/-- A function eventually equal to `0` near `x` has zero gradient at `x`. -/
private theorem gradient_eq_zero_of_eventuallyEq {f : E d → ℝ} {x : E d}
    (h : f =ᶠ[𝓝 x] fun _ ↦ 0) : ∇ f x = 0 := by
  rw [gradient, h.fderiv_eq, fderiv_const_apply, map_zero]

/-- **Homogeneous two-phase functions** in every dimension (after De Philippis–Spolaor–Velichkov,
arXiv:1911.02165, Lemma 2.2, via the equality case of the Gaussian Poincaré inequality). The
argument does not use `2 ≤ d`. -/
public theorem homogeneousTwoPhaseIn (d : ℕ) : HomogeneousTwoPhaseIn d := by
  intro v L hv hhom hHpos hHneg hpos hneg
  have hv00 : v 0 = 0 := eq_zero_at_zero_of_homogeneous hhom
  have hvle : ∀ x, |v x| ≤ L * ‖x‖ := fun x ↦ by
    have := hv.dist_le_mul x 0
    rwa [dist_zero_right, Real.dist_eq, hv00, sub_zero] at this
  -- the two phases
  set wp : E d → ℝ := fun x ↦ max (v x) 0 with hwp
  set wm : E d → ℝ := fun x ↦ max (-v x) 0 with hwm
  have hwpL : LipschitzWith L wp := hv.max_const 0
  have hwmL : LipschitzWith L wm := hv.neg.max_const 0
  have hwp0 : ∀ x, 0 ≤ wp x := fun x ↦ le_max_right _ _
  have hwm0 : ∀ x, 0 ≤ wm x := fun x ↦ le_max_right _ _
  have hhomp : ∀ t : ℝ, 0 < t → ∀ x, wp (t • x) = t * wp x := fun t ht x ↦ by
    simp only [hwp, hhom t ht x, mul_max_of_nonneg _ _ ht.le, mul_zero]
  have hhomm : ∀ t : ℝ, 0 < t → ∀ x, wm (t • x) = t * wm x := fun t ht x ↦ by
    simp only [hwm, hhom t ht x, ← mul_neg, mul_max_of_nonneg _ _ ht.le, mul_zero]
  have hHp : HarmonicOnNhd wp {x | 0 < wp x} := harmonicOnNhd_max_zero hv.continuous hHpos
  have hHm : HarmonicOnNhd wm {x | 0 < wm x} :=
    harmonicOnNhd_max_zero (w := -v) hv.continuous.neg fun x hx ↦
      hHneg.neg x (show v x < 0 by simpa using hx)
  -- Gaussian energy identities (M1)
  have Ep := integral_norm_sq_gradient_mul_gaussWeight hwpL hwp0 hHp hhomp
  have Em := integral_norm_sq_gradient_mul_gaussWeight hwmL hwm0 hHm hhomm
  -- integrability
  have hgrowth : ∀ (w : E d → ℝ), (∀ x, |w x| ≤ |v x|) →
      (∀ x, |w x| ≤ L * (1 + ‖x‖ ^ 2)) ∧ (∀ x, |w x ^ 2| ≤ L ^ 2 * (1 + ‖x‖ ^ 2)) := by
    intro w hw
    refine ⟨fun x ↦ ?_, fun x ↦ ?_⟩
    · have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
      exact (hw x).trans ((hvle x).trans (mul_le_mul_of_nonneg_left hx (NNReal.coe_nonneg L)))
    · rw [abs_pow]
      have h1 : |w x| ^ 2 ≤ (L * ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) ((hw x).trans (hvle x)) 2
      nlinarith [sq_nonneg (L : ℝ)]
  have hwpv : ∀ x, |wp x| ≤ |v x| := fun x ↦ by
    rw [abs_of_nonneg (hwp0 x)]; exact max_le (le_abs_self _) (abs_nonneg _)
  have hwmv : ∀ x, |wm x| ≤ |v x| := fun x ↦ by
    rw [abs_of_nonneg (hwm0 x)]; exact max_le (neg_le_abs _) (abs_nonneg _)
  have Ip1 := integrable_mul_gaussWeight hwpL.continuous.aestronglyMeasurable
    (hgrowth wp hwpv).1
  have Im1 := integrable_mul_gaussWeight hwmL.continuous.aestronglyMeasurable
    (hgrowth wm hwmv).1
  have Ip2 := integrable_mul_gaussWeight (hwpL.continuous.pow 2).aestronglyMeasurable
    (hgrowth wp hwpv).2
  have Im2 := integrable_mul_gaussWeight (hwmL.continuous.pow 2).aestronglyMeasurable
    (hgrowth wm hwmv).2
  have hgradint : ∀ w : E d → ℝ, LipschitzWith L w →
      Integrable fun x ↦ ‖∇ w x‖ ^ 2 * gaussWeight x := fun w hw ↦
    integrable_mul_gaussWeight ((measurable_gradient w).norm.pow_const 2).aestronglyMeasurable
      (C := (L : ℝ) ^ 2) fun x ↦ by
        rw [abs_of_nonneg (sq_nonneg _)]
        have h1 : ‖∇ w x‖ ^ 2 ≤ (L : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
          ((norm_gradient_eq_norm_fderiv w x).trans_le (norm_fderiv_le_of_lipschitz ℝ hw)) 2
        nlinarith [sq_nonneg ‖x‖, sq_nonneg (L : ℝ)]
  -- the Gaussian masses of the two phases
  have hApos : ∀ w : E d → ℝ, Continuous w → (∀ x, 0 ≤ w x) → (∃ x, 0 < w x) →
      Integrable (fun x ↦ w x * gaussWeight x) → 0 < ∫ x, w x * gaussWeight x := by
    intro w hw hw0 ⟨x₀, hx₀⟩ hint
    rw [integral_pos_iff_support_of_nonneg (fun x ↦ mul_nonneg (hw0 x) (gaussWeight_nonneg x))
      hint]
    refine lt_of_lt_of_le ((isOpen_lt continuous_const hw).measure_pos volume ⟨x₀, hx₀⟩)
      (measure_mono fun x hx ↦ ?_)
    exact mul_ne_zero (ne_of_gt hx) (gaussWeight_pos x).ne'
  obtain ⟨xp, hxp⟩ := hpos
  obtain ⟨xm, hxm⟩ := hneg
  set Ap := ∫ x, wp x * gaussWeight x with hAp
  set Am := ∫ x, wm x * gaussWeight x with hAm
  have hAp0 : 0 < Ap := hApos wp hwpL.continuous hwp0 ⟨xp, lt_max_of_lt_left hxp⟩ Ip1
  have hAm0 : 0 < Am :=
    hApos wm hwmL.continuous hwm0 ⟨xm, lt_max_of_lt_left (by linarith)⟩ Im1
  set c := Ap / Am with hc
  have hc0 : 0 < c := div_pos hAp0 hAm0
  -- `G = v⁺ - c v⁻` has Gaussian mean zero
  set G : E d → ℝ := fun x ↦ wp x - c * wm x with hG
  have hGL : LipschitzWith (L + ‖c‖₊ * L) G := hwpL.sub ((lipschitzWith_smul c).comp hwmL)
  have hprod : ∀ x, wp x * wm x = 0 := fun x ↦ by
    rcases le_total (v x) 0 with h | h
    · simp [hwp, max_eq_right h]
    · simp [hwm, max_eq_right (neg_nonpos.2 h)]
  have hmean : ∫ x, G x * gaussWeight x = 0 := by
    have : (fun x ↦ G x * gaussWeight x) =
        fun x ↦ wp x * gaussWeight x - c * (wm x * gaussWeight x) := by
      funext x; simp only [hG]; ring
    rw [this, integral_sub Ip1 (Im1.const_mul c), integral_const_mul, ← hAp, ← hAm, hc,
      div_mul_cancel₀ _ hAm0.ne', sub_self]
  have hsq : ∫ x, G x ^ 2 * gaussWeight x =
      (∫ x, wp x ^ 2 * gaussWeight x) + c ^ 2 * ∫ x, wm x ^ 2 * gaussWeight x := by
    calc ∫ x, G x ^ 2 * gaussWeight x
        = ∫ x, (wp x ^ 2 * gaussWeight x + c ^ 2 * (wm x ^ 2 * gaussWeight x)) := by
          refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
          have := hprod x
          simp only [hG]
          linear_combination (-2 * c * gaussWeight x) * this
      _ = (∫ x, wp x ^ 2 * gaussWeight x) + ∫ x, c ^ 2 * (wm x ^ 2 * gaussWeight x) :=
          integral_add Ip2 (Im2.const_mul _)
      _ = _ := by rw [integral_const_mul]
  -- the gradients
  have stamp : ∀ w : E d → ℝ, ∀ K : ℝ≥0, LipschitzWith K w → ∀ᵐ x, w x = 0 → ∇ w x = 0 := by
    intro w K hw
    have hW := (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hw.locallyLipschitz.locallyLipschitzOn).1
    have := hW.ae_eq_zero_of_eq_zero isOpen_univ
    rwa [Measure.restrict_univ] at this
  have hgrad : ∀ᵐ x, ‖∇ G x‖ ^ 2 = ‖∇ wp x‖ ^ 2 + c ^ 2 * ‖∇ wm x‖ ^ 2 := by
    filter_upwards [stamp wp L hwpL, stamp wm L hwmL, stamp G _ hGL] with x h1 h2 h3
    rcases lt_trichotomy (v x) 0 with hlt | heq | hgt
    · have hU : ∀ᶠ y in 𝓝 x, v y < 0 :=
        (isOpen_lt hv.continuous continuous_const).mem_nhds hlt
      have e1 : wp =ᶠ[𝓝 x] fun _ ↦ 0 := hU.mono fun y hy ↦ max_eq_right hy.le
      have e2 : G =ᶠ[𝓝 x] fun y ↦ (-c) * wm y := hU.mono fun y hy ↦ by
        simp only [hG, hwp, max_eq_right hy.le]; ring
      rw [gradient_eq_zero_of_eventuallyEq e1, gradient_congr_of_eventuallyEq e2,
        gradient_const_mul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
      simp
    · have hp : wp x = 0 := by simp [hwp, heq]
      have hm : wm x = 0 := by simp [hwm, heq]
      have hg : G x = 0 := by simp [hG, hp, hm]
      rw [h1 hp, h2 hm, h3 hg]
      simp
    · have hU : ∀ᶠ y in 𝓝 x, 0 < v y :=
        (isOpen_lt continuous_const hv.continuous).mem_nhds hgt
      have e1 : wm =ᶠ[𝓝 x] fun _ ↦ 0 := hU.mono fun y hy ↦ max_eq_right (by linarith)
      have e2 : G =ᶠ[𝓝 x] wp := hU.mono fun y hy ↦ by
        simp only [hG, hwm, max_eq_right (by linarith : -v y ≤ 0)]; ring
      rw [gradient_eq_zero_of_eventuallyEq e1, gradient_congr_of_eventuallyEq e2]
      simp
  have henergy : ∫ x, ‖∇ G x‖ ^ 2 * gaussWeight x =
      (∫ x, ‖∇ wp x‖ ^ 2 * gaussWeight x) + c ^ 2 * ∫ x, ‖∇ wm x‖ ^ 2 * gaussWeight x := by
    calc ∫ x, ‖∇ G x‖ ^ 2 * gaussWeight x
        = ∫ x, (‖∇ wp x‖ ^ 2 * gaussWeight x + c ^ 2 * (‖∇ wm x‖ ^ 2 * gaussWeight x)) := by
          refine integral_congr_ae ?_
          filter_upwards [hgrad] with x hx
          rw [hx]; ring
      _ = (∫ x, ‖∇ wp x‖ ^ 2 * gaussWeight x) +
            ∫ x, c ^ 2 * (‖∇ wm x‖ ^ 2 * gaussWeight x) :=
          integral_add (hgradint wp hwpL) ((hgradint wm hwmL).const_mul _)
      _ = _ := by rw [integral_const_mul]
  -- equality in the Gaussian Poincaré inequality
  have hEq : gaussMass d * ∫ x, ‖∇ G x‖ ^ 2 * gaussWeight x ≤ gaussVariance G := by
    rw [gaussVariance, hmean, henergy, Ep, Em, hsq]
    simp
  obtain ⟨p, q, hpq⟩ := exists_eq_inner_add_of_le_gaussVariance hGL hEq
  have hq : q = 0 := by
    have h0 := hpq 0
    simp only [hG, hwp, hwm, hv00, neg_zero, max_self, mul_zero, sub_zero, inner_zero_right,
      zero_add] at h0
    exact h0.symm
  have hGx : ∀ x, G x = inner ℝ x p := fun x ↦ by rw [hpq x, hq, add_zero, real_inner_comm]
  -- `v` from `G`
  have hvG : ∀ x, v x = max (G x) 0 - max (-G x) 0 / c := fun x ↦ by
    rcases le_total 0 (v x) with h | h
    · have hm : wm x = 0 := max_eq_right (by linarith)
      have hGv : G x = v x := by simp only [hG, hm, hwp, max_eq_left h]; ring
      rw [hGv, max_eq_left h, max_eq_right (by linarith : -v x ≤ 0), zero_div, sub_zero]
    · have hp : wp x = 0 := max_eq_right h
      have hGv : G x = c * v x := by
        simp only [hG, hp, hwm, max_eq_left (by linarith : (0 : ℝ) ≤ -v x)]; ring
      rw [hGv, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc0.le h),
        max_eq_left (by nlinarith : (0 : ℝ) ≤ -(c * v x))]
      field_simp
      ring
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := hvG xp
    rw [hGx, inner_zero_right] at this
    simp at this
    linarith
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
  refine ⟨‖p‖⁻¹ • p, ‖p‖, ‖p‖ / c, ?_, hpn, div_pos hpn hc0, fun x ↦ ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpn.ne']
  · have hi : 0 ≤ ‖p‖⁻¹ := inv_nonneg.2 hpn.le
    have key : ∀ a : ℝ, max (‖p‖⁻¹ * a) 0 = ‖p‖⁻¹ * max a 0 := fun a ↦ by
      rw [mul_max_of_nonneg _ _ hi, mul_zero]
    rw [hvG x, hGx, twoPlane, add_zero, inner_smul_right, ← mul_neg, key, key]
    field_simp

/-- **Homogeneous two-phase functions** for `d ≥ 2` (the form recorded in the plan; the
dimension hypothesis is not used, see `homogeneousTwoPhaseIn`). -/
public theorem homogeneousTwoPhaseIn_of_two_le {d : ℕ} (_hd : 2 ≤ d) :
    HomogeneousTwoPhaseIn d :=
  homogeneousTwoPhaseIn d

end EllipticBernoulli
