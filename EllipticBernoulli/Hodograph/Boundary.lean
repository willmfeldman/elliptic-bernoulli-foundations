/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Field
import BasicElliptic.Div.Boundary.StrongToWeak
import BasicElliptic.Div.Quasilinear.Main
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Boundary regularity of the hodograph equation

The hodograph flux `Φ = field e` (`Hodograph/Field.lean`) is `C^∞` where `q · e ≠ 0`. Its
derivative is symmetric (it is the Hessian of the potential `Φ₀`), and on the ball
`|q - e| < 1/8` it is uniformly elliptic with constant `1/2` (`D²Φ₀(e) = 2I`). A `C¹` solution of
`div Φ(∇w) = 0` on a half ball with the conormal condition `Φ(∇w) · e = 0` on the flat part, and
with `|∇w - e| ≤ 1/16`, is therefore a weak quasilinear conormal solution, and the higher
regularity theorem for such solutions gives `w ∈ C^∞` up to the flat boundary.

This is the only module of the library that uses the elliptic Schauder theory dependency.

## Main results

* `Hodograph.inner_fderiv_field`: `⟪DΦ(q) h, k⟫ = (2/n) ⟪P h, P k⟫ - (2/n²)(h_n ⟪P q, P k⟫ +
  ⟪P q, P h⟫ k_n) + (2 (1 + |P q|²)/n³) h_n k_n`, where `n = q · e`.
* `Hodograph.half_mul_norm_sq_le_inner_fderiv_field`: ellipticity on `|q - e| < 1/8`.
* `hodograph_regularity`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli

open Hodograph

variable {d : ℕ}

namespace Hodograph

variable {e : E d}

theorem continuous_perpProj' (e : E d) : Continuous (perpProj e) := by
  have : perpProj e = fun z ↦ perpCLM e z := funext fun z ↦ (perpCLM_apply e z).symm
  rw [this]; exact (perpCLM e).continuous

theorem hasFDerivAt_perpProj (e q : E d) : HasFDerivAt (perpProj e) (perpCLM e) q := by
  have : perpProj e = fun z ↦ perpCLM e z := funext fun z ↦ (perpCLM_apply e z).symm
  rw [this]; exact (perpCLM e).hasFDerivAt

theorem hasFDerivAt_inner_e (e q : E d) :
    HasFDerivAt (fun q : E d ↦ ⟪q, e⟫) (innerSL ℝ e) q := by
  have : (fun q : E d ↦ ⟪q, e⟫) = fun q ↦ innerSL ℝ e q := by
    funext q; rw [innerSL_apply_apply, real_inner_comm]
  rw [this]; exact (innerSL ℝ e).hasFDerivAt

/-- The derivative of the hodograph flux, as a bilinear form. -/
theorem inner_fderiv_field (he : ‖e‖ = 1) {q : E d} (hq : ⟪q, e⟫ ≠ 0) (h k : E d) :
    ⟪fderiv ℝ (field e) q h, k⟫ =
      2 / ⟪q, e⟫ * ⟪perpProj e h, perpProj e k⟫ -
        2 / ⟪q, e⟫ ^ 2 * (⟪h, e⟫ * ⟪perpProj e q, perpProj e k⟫ +
          ⟪perpProj e q, perpProj e h⟫ * ⟪k, e⟫) +
        2 * (1 + ‖perpProj e q‖ ^ 2) / ⟪q, e⟫ ^ 3 * (⟪h, e⟫ * ⟪k, e⟫) := by
  have hfun : field e = fun q ↦ (2 * (⟪q, e⟫)⁻¹) • perpProj e q +
      (1 - (1 + ‖perpProj e q‖ ^ 2) * (⟪q, e⟫ ^ 2)⁻¹) • e := by
    funext q; simp only [field, div_eq_mul_inv]
  have hn := hasFDerivAt_inner_e e q
  have hP := hasFDerivAt_perpProj e q
  have hinv : HasFDerivAt (fun q : E d ↦ (⟪q, e⟫)⁻¹) _ q :=
    (hasDerivAt_inv hq).comp_hasFDerivAt (f := fun q : E d ↦ ⟪q, e⟫) q hn
  have hsq : HasFDerivAt (fun q : E d ↦ ⟪q, e⟫ ^ 2) _ q :=
    (hasDerivAt_pow 2 ⟪q, e⟫).comp_hasFDerivAt (f := fun q : E d ↦ ⟪q, e⟫) q hn
  have hinv2 : HasFDerivAt (fun q : E d ↦ (⟪q, e⟫ ^ 2)⁻¹) _ q :=
    (hasDerivAt_inv (pow_ne_zero 2 hq)).comp_hasFDerivAt (f := fun q : E d ↦ ⟪q, e⟫ ^ 2) q hsq
  have hA := hinv.const_mul (2 : ℝ)
  have hN := ((hasFDerivAt_const (1 : ℝ) q).add hP.norm_sq).mul hinv2
  have hB := (hasFDerivAt_const (1 : ℝ) q).sub hN
  have hD := (hA.smul hP).add (hB.smul_const e)
  have hD' : HasFDerivAt (fun q : E d ↦ (2 * (⟪q, e⟫)⁻¹) • perpProj e q +
      (1 - (1 + ‖perpProj e q‖ ^ 2) * (⟪q, e⟫ ^ 2)⁻¹) • e) _ q := hD
  rw [hfun, hD'.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, sub_apply,
    zero_apply, ContinuousLinearMap.comp_apply, perpCLM_apply, Pi.add_apply,
    nsmul_eq_mul,
    innerSL_apply_apply, smul_eq_mul, inner_add_left, real_inner_smul_left]
  have h1 : ⟪perpProj e h, k⟫ = ⟪perpProj e h, perpProj e k⟫ := by
    rw [inner_perpProj_eq, inner_perpProj_eq, perpProj_perpProj he]
  have h2 : ⟪perpProj e q, k⟫ = ⟪perpProj e q, perpProj e k⟫ := by
    rw [inner_perpProj_eq, inner_perpProj_eq, perpProj_perpProj he]
  have h3 : ⟪e, k⟫ = ⟪k, e⟫ := real_inner_comm _ _
  have h4 : ⟪e, h⟫ = ⟪h, e⟫ := real_inner_comm _ _
  rw [h1, h2, h3, h4]
  field_simp
  ring

theorem inner_e_of_mem_ball (he : ‖e‖ = 1) {p : E d} (hp : p ∈ ball e (1 / 8)) :
    7 / 8 < ⟪p, e⟫ ∧ ⟪p, e⟫ < 9 / 8 ∧ ‖perpProj e p‖ < 1 / 8 := by
  have hpe : ‖p - e‖ < 1 / 8 := by rwa [mem_ball, dist_eq_norm] at hp
  have h1 : ⟪p, e⟫ = 1 + ⟪p - e, e⟫ := by rw [inner_sub_left, inner_self_of_norm he]; ring
  have h2 := abs_real_inner_le_norm (p - e) e
  rw [he, mul_one] at h2
  have h3 : perpProj e p = perpProj e (p - e) := by
    rw [perpProj_sub, perpProj_self he, sub_zero]
  refine ⟨by linarith [neg_abs_le ⟪p - e, e⟫], by linarith [le_abs_self ⟪p - e, e⟫], ?_⟩
  rw [h3]; exact (norm_perpProj_le he _).trans_lt hpe

theorem contDiffOn_field (he : ‖e‖ = 1) : ContDiffOn ℝ ∞ (field e) (ball e (1 / 8)) := by
  have hne : ∀ q ∈ ball e (1 / 8), ⟪q, e⟫ ≠ 0 := fun q hq ↦ by
    linarith [(inner_e_of_mem_ball he hq).1]
  have hn : ContDiff ℝ ∞ (fun q : E d ↦ ⟪q, e⟫) := contDiff_id.inner ℝ contDiff_const
  have hP : ContDiff ℝ ∞ (perpProj e) := by
    have : perpProj e = fun z ↦ perpCLM e z := funext fun z ↦ (perpCLM_apply e z).symm
    rw [this]; exact (perpCLM e).contDiff
  have hfun : field e = fun q ↦ (2 / ⟪q, e⟫) • perpProj e q +
      (1 - (1 + ‖perpProj e q‖ ^ 2) / ⟪q, e⟫ ^ 2) • e := rfl
  rw [hfun]
  refine ((contDiffOn_const.div hn.contDiffOn hne).smul hP.contDiffOn).add
    ((contDiffOn_const.sub ((contDiffOn_const.add (hP.norm_sq ℝ).contDiffOn).div
      (hn.pow 2).contDiffOn fun q hq ↦ pow_ne_zero 2 (hne q hq))).smul contDiffOn_const)

theorem isSymmetric_fderiv_field (he : ‖e‖ = 1) {p : E d} (hp : ⟪p, e⟫ ≠ 0) :
    (fderiv ℝ (field e) p : E d →ₗ[ℝ] E d).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [real_inner_comm (fderiv ℝ (field e) p y) x, inner_fderiv_field he hp,
    inner_fderiv_field he hp,
    real_inner_comm (perpProj e x) (perpProj e y)]
  ring

/-- **Ellipticity of the hodograph flux** near `e`: `DΦ(p) ≥ 1/2` for `|p - e| < 1/8`. -/
theorem half_mul_norm_sq_le_inner_fderiv_field (he : ‖e‖ = 1) {p : E d}
    (hp : p ∈ ball e (1 / 8)) (ξ : E d) :
    1 / 2 * ‖ξ‖ ^ 2 ≤ ⟪fderiv ℝ (field e) p ξ, ξ⟫ := by
  obtain ⟨hn1, hn2, hm⟩ := inner_e_of_mem_ball he hp
  have hpn : ⟪p, e⟫ ≠ 0 := by linarith
  rw [inner_fderiv_field he hpn ξ ξ]
  set n := ⟪p, e⟫ with hndef
  set a := ‖perpProj e ξ‖ with hadef
  set s := ⟪ξ, e⟫ with hsdef
  set c := ⟪perpProj e p, perpProj e ξ⟫ with hcdef
  set m := ‖perpProj e p‖ with hmdef
  have hξ : ‖ξ‖ ^ 2 = a ^ 2 + s ^ 2 := by rw [hadef, norm_perpProj_sq he]; ring
  have haa : ⟪perpProj e ξ, perpProj e ξ⟫ = a ^ 2 := real_inner_self_eq_norm_sq _
  have hc : |c| ≤ a / 8 := by
    have := abs_real_inner_le_norm (perpProj e p) (perpProj e ξ)
    have ha0 : 0 ≤ a := norm_nonneg _
    nlinarith
  have hn0 : 0 < n := by linarith
  have h2n : 16 / 9 ≤ 2 / n := by rw [le_div_iff₀ hn0]; linarith
  have h3n : 1 ≤ 2 * (1 + m ^ 2) / n ^ 3 := by
    have hn3 : n ^ 3 ≤ (9 / 8) ^ 3 := pow_le_pow_left₀ hn0.le hn2.le 3
    rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg m]
  have h2n2 : 2 / n ^ 2 ≤ 128 / 49 := by
    have hn3 : (7 / 8) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (by norm_num) hn1.le 2
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hsc : |s * c + c * s| ≤ |s| * a / 4 := by
    rw [show s * c + c * s = 2 * (s * c) by ring, abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg s]
  have hsa : |s| * a ≤ (s ^ 2 + a ^ 2) / 2 := by
    nlinarith [sq_nonneg (|s| - a), sq_abs s]
  have hT2 : 2 / n ^ 2 * (s * c + c * s) ≤ 16 / 49 * (s ^ 2 + a ^ 2) := by
    have h0 : 0 ≤ 2 / n ^ 2 := by positivity
    calc 2 / n ^ 2 * (s * c + c * s) ≤ 2 / n ^ 2 * |s * c + c * s| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) h0
      _ ≤ 128 / 49 * (|s| * a / 4) :=
          mul_le_mul h2n2 hsc (abs_nonneg _) (by norm_num)
      _ ≤ 16 / 49 * (s ^ 2 + a ^ 2) := by nlinarith
  rw [haa, hξ]
  have hT1 : 16 / 9 * a ^ 2 ≤ 2 / n * a ^ 2 := mul_le_mul_of_nonneg_right h2n (sq_nonneg a)
  have hT3 : s * s ≤ 2 * (1 + m ^ 2) / n ^ 3 * (s * s) :=
    le_mul_of_one_le_left (mul_self_nonneg s) h3n
  nlinarith

end Hodograph

/-- **Boundary regularity of the hodograph equation.** There is `η > 0` such that, for every unit
`e` and `r > 0`, a function `w` which is `C¹` on `halfBall e 0 r` (derivatives within), `C²` in
the open half ball, with `|∇w - e| ≤ η`, `div Φ(∇w) = 0` in the open half ball and
`Φ(∇w) · e = 0` on the flat part (`Φ = field e`), is `C^∞` on `halfBall e 0 (r/2)`.

This is the strong-to-weak passage and the higher regularity theorem for quasilinear conormal
problems; near `q = e` the potential `Φ₀` satisfies `D²Φ₀(e) = 2I`, so `DΦ` is uniformly elliptic
on a convex neighbourhood of `e`. -/
theorem hodograph_regularity : ∃ η > 0, ∀ {e : E d} {r : ℝ} {w : E d → ℝ}, ‖e‖ = 1 → 0 < r →
    ContDiffOn ℝ 1 w (BasicElliptic.halfBall e 0 r) →
    ContDiffOn ℝ 2 w (ball 0 r ∩ BasicElliptic.openHalfSpace e) →
    (∀ z ∈ BasicElliptic.halfBall e 0 r,
      ‖gradientWithin w (BasicElliptic.halfBall e 0 r) z - e‖ ≤ η) →
    (∀ z ∈ ball 0 r ∩ BasicElliptic.openHalfSpace e, divergence (fun p ↦ field e (∇ w p)) z = 0) →
    (∀ z ∈ ball 0 r ∩ BasicElliptic.flatPart e,
      ⟪field e (gradientWithin w (BasicElliptic.halfBall e 0 r) z), e⟫ = 0) →
    ContDiffOn ℝ ∞ w (BasicElliptic.halfBall e 0 (r / 2)) := by
  refine ⟨1 / 16, by norm_num, fun {e r w} he hr h1 h2 hgrad hdiv hbc ↦ ?_⟩
  set U := ball e (1 / 8 : ℝ) with hUdef
  have hU : IsOpen U := isOpen_ball
  have hUc : Convex ℝ U := convex_ball e _
  have hΦ : ContDiffOn ℝ ∞ (field e) U := Hodograph.contDiffOn_field he
  have hrange : ∀ y ∈ BasicElliptic.halfBall e 0 r,
      gradientWithin w (BasicElliptic.halfBall e 0 r) y ∈ U := fun y hy ↦ by
    rw [hUdef, mem_ball, dist_eq_norm]; linarith [hgrad y hy]
  have hne : ∀ p ∈ U, ⟪p, e⟫ ≠ 0 := fun p hp ↦ by
    linarith [(Hodograph.inner_e_of_mem_ball he hp).1]
  have hsol := BasicElliptic.Div.isQuasilinearConormalSolOn_of_strong (E d) e 0 r (field e) U w he
    hr hU h1 h2 (hΦ.of_le (by exact_mod_cast le_top)) hrange hdiv hbc
  rw [contDiffOn_infty]
  intro n
  have := BasicElliptic.Div.contDiffOn_halfBall_of_quasilinear_conormal (E d) n e 0 r (field e) U
    (1 / 2) w he hr (by simp; linarith) hU hUc (by norm_num) (hΦ.of_le (by exact_mod_cast le_top))
    (fun p hp ξ ↦ Hodograph.half_mul_norm_sq_le_inner_fderiv_field he hp ξ)
    (fun p hp ↦ Hodograph.isSymmetric_fderiv_field he (hne p hp)) hrange hsol
  exact this.of_le (by exact_mod_cast Nat.le_succ n)

end EllipticBernoulli
