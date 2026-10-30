/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.GaussianPoincare.Lipschitz
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Blowup.Constancy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Gaussian Poincaré inequality with equality case

Write `γ` for the Gaussian `e^{-|x|²/2} dx / Z` on `ℝᵈ`, `Z = gaussMass d`.

* `gaussVariance_le_of_lipschitzWith` (`GaussianPoincare/Lipschitz.lean`): for `F` Lipschitz,
  `Var_γ F ≤ ∫ |∇F|² dγ`, in the form `gaussVariance F ≤ Z ∫ |∇F|² e^{-|x|²/2}`;
* `exists_eq_inner_add_of_le_gaussVariance`: if `F` is
  Lipschitz and `Z ∫ |∇F|² e^{-|x|²/2} ≤ gaussVariance F` (equality in the Gaussian Poincaré
  inequality), then `F` is affine: `F x = ⟨p, x⟩ + q`.

The converse (affine functions give equality) is not needed and not formalized.

## Proof of the equality case

By the defect bound (`lintegral_sin_mul_defect_le_of_lipschitzWith`) the defect integral
vanishes, so for a.e. `t ∈ (0, π/2]`, `∇F(x) = ∇F(x cos t + y sin t)` for a.e. `(x, y)`. Fix one
such `t` and (Fubini) one `x₀` with `∇F(x₀) = ∇F(x₀ cos t + y sin t)` for a.e. `y`. As
`y ↦ x₀ cos t + y sin t` is an affine bijection, `∇F = ∇F(x₀) =: p` a.e. Then `F - ⟨p, ·⟩` has
zero weak gradient, so it is a.e. constant (`exists_ae_eq_const_of_hasWeakGradient_zero`), hence
constant by continuity. Fixing `x₀` first means that only the affine map
`y ↦ x₀ cos t + y sin t` of `ℝᵈ` is used, not the map `(x, y) ↦ (x, x cos t + y sin t)` of
`ℝᵈ × ℝᵈ`.
-/

open Set Filter Topology MeasureTheory Real InnerProductSpace
open scoped Gradient NNReal ENNReal

namespace EllipticBernoulli

variable {d : ℕ} {F : E d → ℝ} {L : ℝ≥0}

/-- A Lipschitz function whose pointwise gradient is a.e. a constant `p` is affine. -/
public theorem exists_eq_inner_add_of_ae_gradient_eq (hL : LipschitzWith L F) {p : E d}
    (hp : ∀ᵐ x, ∇ F x = p) : ∃ q : ℝ, ∀ x, F x = inner ℝ p x + q := by
  set H : E d → ℝ := fun x ↦ F x - inner ℝ p x with hH
  have hHL : LipschitzWith (L + ‖innerSL ℝ p‖₊) H := hL.sub (innerSL ℝ p).lipschitzWith
  have hgH : ∀ᵐ x, ∇ H x = 0 := by
    filter_upwards [hp, hL.ae_differentiableAt] with x hx hd
    have hfd : HasFDerivAt H (fderiv ℝ F x - innerSL ℝ p) x :=
      hd.hasFDerivAt.sub (innerSL ℝ p).hasFDerivAt
    refine (inner_self_eq_zero (𝕜 := ℝ)).1 ?_
    rw [inner_gradient_left_eq_fderiv, hfd.fderiv, sub_apply,
      ← inner_gradient_left_eq_fderiv, hx, innerSL_apply_apply, sub_self]
  have hW : HasWeakGradient univ H (∇ H) :=
    (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hHL.locallyLipschitz.locallyLipschitzOn).1
  have hW0 : HasWeakGradient univ H 0 := by
    refine ⟨hW.1, locallyIntegrableOn_zero, fun φ hφ hφc hφU v ↦ ?_⟩
    rw [hW.2.2 φ hφ hφc hφU v]
    congr 1
    refine integral_congr_ae ?_
    rw [Measure.restrict_univ]
    filter_upwards [hgH] with x hx
    simp [hx]
  obtain ⟨q, hq⟩ := exists_ae_eq_const_of_hasWeakGradient_zero isOpen_univ
    isPreconnected_univ hW0
  rw [Measure.restrict_univ] at hq
  have hHq : H = fun _ ↦ q :=
    (Continuous.ae_eq_iff_eq volume hHL.continuous continuous_const).1 hq
  refine ⟨q, fun x ↦ ?_⟩
  have := congrFun hHq x
  simp only [hH] at this
  linarith

/-- **Equality in the Gaussian Poincaré inequality.**
If `F : ℝᵈ → ℝ` is Lipschitz and `Z ∫ |∇F|² e^{-|x|²/2} ≤ gaussVariance F` (that is,
`∫ |∇F|² dγ ≤ Var_γ F`, so equality holds), then `F` is affine. -/
public theorem exists_eq_inner_add_of_le_gaussVariance (hL : LipschitzWith L F)
    (heq : gaussMass d * ∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x ≤ gaussVariance F) :
    ∃ (p : E d) (q : ℝ), ∀ x, F x = inner ℝ p x + q := by
  set g : ℝ → E d × E d → ℝ≥0∞ := fun t p ↦
    ENNReal.ofReal (sin t * ‖∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 *
      gaussPairWeight p) with hg
  have hmeas : Measurable fun z : ℝ × (E d × E d) ↦ g z.1 z.2 := by
    refine ENNReal.measurable_ofReal.comp ?_
    refine ((continuous_sin.measurable.comp measurable_fst).mul ?_).mul
      (continuous_gaussPairWeight.measurable.comp measurable_snd)
    refine (((measurable_gradient F).comp (measurable_fst.comp measurable_snd)).sub
      ((measurable_gradient F).comp ?_)).norm.pow_const 2
    exact (by fun_prop : Continuous fun z : ℝ × (E d × E d) ↦
      cos z.1 • z.2.1 + sin z.1 • z.2.2).measurable
  have hzero : ∫⁻ t in Ioc 0 (π / 2), ∫⁻ p, g t p = 0 := by
    refine le_antisymm ((lintegral_sin_mul_defect_le_of_lipschitzWith hL).trans
      (le_of_eq (ENNReal.ofReal_eq_zero.2 (by linarith)))) bot_le
  rw [lintegral_eq_zero_iff hmeas.lintegral_prod_right'] at hzero
  -- choose `t`
  have hne : (ae (volume.restrict (Ioc (0 : ℝ) (π / 2)))).NeBot := by
    refine ae_neBot.2 ?_
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Ioc]
    simp [pi_pos]
  obtain ⟨t, ht, ht0⟩ := ((ae_restrict_mem measurableSet_Ioc).and hzero).exists
  have hs : 0 < sin t := sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans_lt (by linarith [pi_pos]))
  have ht0' : ∫⁻ p, g t p = 0 := ht0
  rw [lintegral_eq_zero_iff
    (show Measurable (Function.uncurry g) from hmeas).of_uncurry_left] at ht0'
  have hpair : ∀ᵐ p : E d × E d, ∇ F p.1 = ∇ F (cos t • p.1 + sin t • p.2) := by
    filter_upwards [ht0'] with p hp
    have hp' : ENNReal.ofReal (sin t * ‖∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 *
        gaussPairWeight p) = 0 := hp
    rw [ENNReal.ofReal_eq_zero] at hp'
    have hΦ := gaussPairWeight_pos p
    have hsq : ‖∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 ≤ 0 := by
      by_contra h
      have := mul_pos (mul_pos hs (lt_of_not_ge h)) hΦ
      linarith
    have : ‖∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2)‖ = 0 := by
      nlinarith [norm_nonneg (∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2))]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  -- choose `x₀`
  rw [Measure.volume_eq_prod] at hpair
  have hx := Measure.ae_ae_of_ae_prod hpair
  have hneE : (ae (volume : Measure (E d))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨x₀, hx₀⟩ := hx.exists
  -- `∇F = ∇F(x₀)` a.e.
  have hqmp : Measure.QuasiMeasurePreserving (fun z : E d ↦ (sin t)⁻¹ • (z - cos t • x₀))
      volume volume :=
    (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hs.ne')).comp
      (measurePreserving_sub_right volume (cos t • x₀)).quasiMeasurePreserving
  have hconst : ∀ᵐ z, ∇ F z = ∇ F x₀ := by
    filter_upwards [hqmp.ae hx₀] with z hz
    rw [hz, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
  obtain ⟨q, hq⟩ := exists_eq_inner_add_of_ae_gradient_eq hL hconst
  exact ⟨∇ F x₀, q, hq⟩

end EllipticBernoulli
