/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Setting
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.EMetricSpace.Lipschitz
import EllipticBernoulli.Sobolev.Lipschitz
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Euler's relation, integrated

* `homogeneous_of_ae_inner_gradient_eq`: if `v : ℝᵈ → ℝ` is Lipschitz and
  `x · ∇v(x) = v(x)` for a.e. `x`, then `v` is positively `1`-homogeneous: `v(t x) = t v(x)` for all
  `t > 0` and `x`.

## Proof

Let `G` be the set of points where `v` is differentiable and Euler's relation holds; its complement
is null (Rademacher). For `t ≠ 0` the set `{x | t x ∉ G}` is a dilate of a null set, hence null.
By Fubini (`Measure.ae_ae_comm`), for a.e. `x` we have `t x ∈ G` for a.e. `t`. For such `x`, the
function `ψ(t) = v(t x) / t` is absolutely continuous on every `[1, t]` (`t > 0`) and
`ψ'(t) = (t x · ∇v(t x) - v(t x)) / t² = 0` for a.e. `t`, so `ψ` is constant
(`AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`): `v(t x) = t v(x)`. Both sides are
continuous in `x`, so the identity holds for every `x`. (In the logarithmic variable `τ = log t`
this is the constancy of `e^{-τ} v(e^τ x)`.)
-/

open Set Filter Topology MeasureTheory Metric
open scoped Gradient NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Euler's relation, integrated.** If `v` is Lipschitz and
`x · ∇v(x) = v(x)` for a.e. `x`, then `v(t x) = t v(x)` for every `t > 0` and every `x`. -/
theorem homogeneous_of_ae_inner_gradient_eq {v : E d → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v)
    (h : ∀ᵐ x, inner ℝ x (∇ v x) = v x) : ∀ t : ℝ, 0 < t → ∀ x, v (t • x) = t * v x := by
  set G : Set (E d) := {y | DifferentiableAt ℝ v y ∧ inner ℝ y (∇ v y) = v y} with hGdef
  have hGm : MeasurableSet G := (measurableSet_of_differentiableAt ℝ v).inter
    (measurableSet_eq_fun (measurable_id.inner (measurable_gradient v)) hv.continuous.measurable)
  have hGae : ∀ᵐ y, y ∈ G := hv.ae_differentiableAt.and h
  -- for a.e. `t`, a.e. `x` has `t x ∈ G`
  have h1 : ∀ᵐ t : ℝ, ∀ᵐ x : E d, t • x ∈ G := by
    have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with t ht
    rw [ae_iff]
    change volume ((t • ·) ⁻¹' Gᶜ) = 0
    rw [Measure.addHaar_preimage_smul volume ht, show volume Gᶜ = 0 from ae_iff.1 hGae, mul_zero]
  have hS : MeasurableSet {p : ℝ × E d | p.1 • p.2 ∈ G} := hGm.preimage measurable_smul
  have h2 : ∀ᵐ x : E d, ∀ᵐ t : ℝ, t • x ∈ G := (Measure.ae_ae_comm hS).1 h1
  -- for such `x`, `t ↦ v (t x) / t` is constant on `(0, ∞)`
  have key : ∀ᵐ x : E d, ∀ t : ℝ, 0 < t → v (t • x) = t * v x := by
    filter_upwards [h2] with x hx t ht
    set ψ : ℝ → ℝ := fun s ↦ v (s • x) * s⁻¹ with hψ
    have hpos : ∀ s ∈ uIcc 1 t, 0 < s := fun s hs ↦
      (lt_min one_pos ht).trans_le (by simpa [uIcc] using hs.1)
    have hAC : AbsolutelyContinuousOnInterval ψ 1 t := by
      have hlin : LipschitzWith ‖x‖₊ fun s : ℝ ↦ s • x := LipschitzWith.of_dist_le_mul
        fun s s' ↦ by rw [dist_eq_norm, dist_eq_norm, ← sub_smul, norm_smul, coe_nnnorm, mul_comm]
      have hA : AbsolutelyContinuousOnInterval (fun s : ℝ ↦ v (s • x)) 1 t :=
        (hv.comp hlin).lipschitzOnWith.absolutelyContinuousOnInterval
      have hB : AbsolutelyContinuousOnInterval (fun s : ℝ ↦ s⁻¹) 1 t :=
        ContDiffOn.absolutelyContinuousOnInterval
          ((contDiffOn_inv ℝ).mono fun s hs ↦ (hpos s hs).ne')
      exact hA.mul hB
    have hd : ∀ᵐ s, s ∈ uIcc 1 t → HasDerivAt ψ 0 s := by
      filter_upwards [hx] with s hs hsI
      have hs0 := hpos s hsI
      obtain ⟨hdiff, heul⟩ := hs
      have hv' : HasDerivAt (fun s : ℝ ↦ v (s • x)) (fderiv ℝ v (s • x) x) s := by
        have hl : HasDerivAt (fun s : ℝ ↦ s • x) x s := by
          simpa using (hasDerivAt_id s).smul_const x
        exact hdiff.hasFDerivAt.comp_hasDerivAt s hl
      have hprod := hv'.mul (hasDerivAt_inv hs0.ne')
      convert hprod using 1
      rw [← inner_gradient_left_eq_fderiv, real_inner_comm]
      rw [inner_smul_left, RCLike.conj_to_real] at heul
      field_simp
      linear_combination (-1 : ℝ) * heul
    obtain ⟨C, hC⟩ := hAC.const_of_ae_hasDerivAt_zero hd
    have e1 := hC 1 left_mem_uIcc
    have e2 := hC t right_mem_uIcc
    simp only [hψ, one_smul, inv_one, mul_one] at e1 e2
    rw [← e1] at e2
    field_simp at e2
    linarith
  -- all `x`, by continuity
  intro t ht
  have hae : (fun x ↦ v (t • x)) =ᵐ[volume] fun x ↦ t * v x := key.mono fun x hx ↦ hx t ht
  exact congrFun ((Continuous.ae_eq_iff_eq volume (hv.continuous.comp (continuous_const_smul t))
    (continuous_const.mul hv.continuous)).1 hae)

end EllipticBernoulli
