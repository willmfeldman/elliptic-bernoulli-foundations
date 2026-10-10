/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Equation
import EllipticBernoulli.Viscosity.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Tactic.Module

/-!
# Inverting the extended hodograph transform

Let `IsFlatChartData U u x₀ e ρ G`, let `w` be the partial hodograph transform, and let `W` be a
`C^∞` function on `B_R(0)` equal to `w` on `B_R(0) ∩ {z · e ≥ 0}` (a Seeley extension). The map
`Ψ(z) = x₀ + P z + W(z) e` has derivative `hodoCLM e ∇W(z)`, invertible near `0`, so by the inverse
function theorem it has a `C^∞` local inverse near `x₀ = Ψ(0)`. The function
`F(y) = Ψ⁻¹(y) · e` is the chart: `u = max(F, 0)` near `x₀`, with `∇F = gradVec e ∇W`.

## Main results

* `Hodograph.gradient_eq_gradientWithin`: `∇W = ∇w` (derivative within the half ball) on the
  closed half of `B_R(0)`.
* `Hodograph.isPreconnected_pos`: if `F(x₀) = 0` and `|∇F - e| ≤ 1/8` on `B_ρ(x₀)`, then
  `{F > 0} ∩ B_ρ(x₀)` is star-shaped with respect to `x₀ + (ρ/2) e`, hence preconnected.
* `IsFlatChartData.exists_chart_of_smooth`: the conclusion of `FlatChartStatement`.

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

public section

namespace EllipticBernoulli

open Hodograph

variable {d : ℕ}

/-- The derivative of the graph map `z ↦ x₀ + P z + W(z) e` is `hodoCLM e ∇W(z)`. -/
theorem Hodograph.hasFDerivAt_graphMap {W : E d → ℝ} {x₀ e z : E d}
    (hW : DifferentiableAt ℝ W z) :
    HasFDerivAt (fun z ↦ x₀ + perpCLM e z + W z • e) (hodoCLM e (∇ W z)) z := by
  have := ((perpCLM e).hasFDerivAt.const_add x₀).add (hW.hasFDerivAt.smul_const e)
  refine this.congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
  rw [hodoCLM_apply]
  simp [perpCLM_apply, gradient, toDual_symm_apply]

/-- On `B_R(0) ∩ {z · e ≥ 0}` (`R ≤ r`), the gradient of a smooth `W` equal to `w` there is the
gradient of `w` within `halfBall e 0 r`. -/
theorem Hodograph.gradient_eq_gradientWithin {e : E d} (he : ‖e‖ = 1) {W w : E d → ℝ} {R r : ℝ}
    (hR : 0 < R) (hRr : R ≤ r) (hW : ContDiffOn ℝ ∞ W (ball 0 R))
    (hWw : EqOn W w (ball 0 R ∩ {z | 0 ≤ ⟪z, e⟫})) {z : E d}
    (hz : z ∈ ball 0 R ∩ {z | 0 ≤ ⟪z, e⟫}) :
    ∇ W z = gradientWithin w (BasicElliptic.halfBall e 0 r) z := by
  set K := ball (0 : E d) R ∩ {z | 0 ≤ ⟪z, e⟫} with hK
  have hlin : IsLinearMap ℝ (fun z : E d ↦ ⟪z, e⟫) :=
    ⟨fun x y ↦ inner_add_left x y e, fun c x ↦ real_inner_smul_left x e c⟩
  have hKc : Convex ℝ K := (convex_ball 0 R).inter (convex_halfSpace_ge hlin 0)
  have hint : (R / 2) • e ∈ interior K := by
    have hO : IsOpen (ball (0 : E d) R ∩ {z | 0 < ⟪z, e⟫}) :=
      isOpen_ball.inter (isOpen_lt continuous_const (by fun_prop))
    refine interior_maximal (fun y (hy : y ∈ ball (0 : E d) R ∩ {z | 0 < ⟪z, e⟫}) ↦
      (⟨hy.1, show 0 ≤ ⟪y, e⟫ from le_of_lt hy.2⟩ : y ∈ K)) hO ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)]
      linarith
    · change 0 < ⟪(R / 2) • e, e⟫
      rw [real_inner_smul_left, inner_self_of_norm he]; linarith
  have hUK : UniqueDiffOn ℝ K := uniqueDiffOn_convex hKc ⟨_, hint⟩
  have hdiff : DifferentiableAt ℝ W z :=
    (hW.contDiffAt (isOpen_ball.mem_nhds hz.1)).differentiableAt (by simp)
  have h1 : fderivWithin ℝ W K z = fderiv ℝ W z :=
    hdiff.hasFDerivAt.hasFDerivWithinAt.fderivWithin (hUK z hz)
  have h2 : fderivWithin ℝ W K z = fderivWithin ℝ w K z := fderivWithin_congr hWw (hWw hz)
  have h3 : fderivWithin ℝ w (BasicElliptic.halfBall e 0 r) z = fderivWithin ℝ w K z := by
    refine fderivWithin_congr_set ?_
    filter_upwards [isOpen_ball.mem_nhds hz.1] with y hy
    exact propext ⟨fun h ↦ ⟨hy, h.2⟩,
      fun h ↦ ⟨ball_subset_closedBall (ball_subset_ball hRr hy), h.2⟩⟩
  rw [gradient, gradientWithin, h3, ← h2, h1]

theorem Hodograph.norm_perpProj_add_smul_sq {e : E d} (he : ‖e‖ = 1) (z : E d) (τ : ℝ) :
    ‖perpProj e z + τ • e‖ ^ 2 = ‖perpProj e z‖ ^ 2 + τ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, inner_perpProj he, norm_smul, he,
    Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- **Star-shapedness of the positive set.** If `F(x₀) = 0` and `F` is differentiable on
`B_ρ(x₀)` with `|∇F - e| ≤ 1/8`, then `{F > 0} ∩ B_ρ(x₀)` is star-shaped with respect to
`x₀ + (ρ/2) e`, hence preconnected. -/
theorem Hodograph.isPreconnected_pos {F : E d → ℝ} {x₀ e : E d} {ρ : ℝ} (he : ‖e‖ = 1)
    (hρ : 0 < ρ) (hF0 : F x₀ = 0) (g : E d → E d)
    (hF : ∀ y ∈ ball x₀ ρ, HasFDerivAt F (toDual ℝ (E d) (g y)) y)
    (hg : ∀ y ∈ ball x₀ ρ, ‖g y - e‖ ≤ 1 / 8) : IsPreconnected {x ∈ ball x₀ ρ | 0 < F x} := by
  have hlin : ∀ p ∈ ball x₀ ρ, ∀ q ∈ ball x₀ ρ, F p + ⟪q - p, e⟫ - 1 / 8 * ‖q - p‖ ≤ F q := by
    intro p hp q hq
    set Gf : E d → ℝ := fun y ↦ F y - toDual ℝ (E d) e y with hGf
    have hGd : ∀ y ∈ ball x₀ ρ,
        HasFDerivWithinAt Gf (toDual ℝ (E d) (g y - e) : StrongDual ℝ (E d)) (ball x₀ ρ) y := by
      intro y hy
      have := ((hF y hy).sub (toDual ℝ (E d) e).hasFDerivAt).hasFDerivWithinAt (s := ball x₀ ρ)
      rwa [← map_sub] at this
    have hb : ∀ y ∈ ball x₀ ρ, ‖(toDual ℝ (E d) (g y - e) : StrongDual ℝ (E d))‖ ≤ 1 / 8 :=
      fun y hy ↦ by rw [LinearIsometryEquiv.norm_map]; exact hg y hy
    have hmv := (convex_ball x₀ ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le hGd hb hp hq
    have hGq : Gf q - Gf p = F q - F p - ⟪q - p, e⟫ := by
      simp only [hGf, toDual_apply_apply, inner_sub_right, real_inner_comm e]; ring
    rw [hGq, Real.norm_eq_abs] at hmv
    linarith [neg_abs_le (F q - F p - ⟪q - p, e⟫)]
  set c : E d := x₀ + (ρ / 2) • e with hcdef
  have hc : c ∈ ball x₀ ρ := by
    rw [mem_ball, dist_eq_norm, hcdef, add_sub_cancel_left, norm_smul, he, mul_one,
      Real.norm_of_nonneg (by linarith)]; linarith
  have hx₀B : x₀ ∈ ball x₀ ρ := mem_ball_self hρ
  have hcS : 0 < F c := by
    have := hlin x₀ hx₀B c hc
    rw [hF0, hcdef, add_sub_cancel_left, real_inner_smul_left, inner_self_of_norm he, norm_smul, he,
      mul_one, Real.norm_of_nonneg (by linarith)] at this
    linarith
  have hstar : StarConvex ℝ c {x ∈ ball x₀ ρ | 0 < F x} := by
    intro y hy a b ha hb hab
    have hσB : a • c + b • y ∈ ball x₀ ρ := (convex_ball x₀ ρ) hc hy.1 ha hb hab
    refine ⟨hσB, ?_⟩
    have hb' : b = 1 - a := by linarith
    subst hb'
    set A := y - x₀ with hAdef
    have hA : ‖A‖ < ρ := by rw [hAdef, ← dist_eq_norm]; exact hy.1
    by_cases hn : ⟪A, e⟫ ≤ ρ / 4
    · have h := hlin y hy.1 _ hσB
      have hσy : a • c + (1 - a) • y - y = a • ((ρ / 2) • e - A) := by
        rw [hcdef, hAdef]; module
      rw [hσy, real_inner_smul_left, inner_sub_left, real_inner_smul_left, inner_self_of_norm he,
        norm_smul, Real.norm_of_nonneg ha] at h
      have hn2 : ‖(ρ / 2) • e - A‖ ≤ ρ / 2 + ‖A‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)]
      have : a * ‖(ρ / 2) • e - A‖ ≤ a * (3 * ρ / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) ha
      nlinarith [hy.2]
    · push Not at hn
      have h := hlin x₀ hx₀B _ hσB
      have hσx : a • c + (1 - a) • y - x₀ = (a * (ρ / 2)) • e + (1 - a) • A := by
        rw [hcdef, hAdef]; module
      rw [hσx, hF0, inner_add_left, real_inner_smul_left, inner_self_of_norm he,
        real_inner_smul_left] at h
      have hn2 : ‖(a * (ρ / 2)) • e + (1 - a) • A‖ ≤ a * (ρ / 2) + (1 - a) * ρ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity),
          Real.norm_of_nonneg (by linarith)]
        have : (1 - a) * ‖A‖ ≤ (1 - a) * ρ := mul_le_mul_of_nonneg_left hA.le (by linarith)
        linarith
      have : (1 - a) * (ρ / 4) ≤ (1 - a) * ⟪A, e⟫ := mul_le_mul_of_nonneg_left hn.le (by linarith)
      nlinarith
  exact (hstar.isPathConnected ⟨hc, hcS⟩).isConnected.isPreconnected

namespace IsFlatChartData

variable {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d} {ρ : ℝ} {G : E d → E d}

/-- **Inversion of the extended transform** (Kinderlehrer–Nirenberg (1977)). Given the hodograph
data, a radius `r` with `halfBall e 0 r` admissible, the transform `w` with `w(0) = 0`, `∇w(0) = e`
(derivatives within the half ball) and the conormal condition on the flat part, and a `C^∞`
function `W` on `B_{r/4}(0)` equal to `w` on `B_{r/4}(0) ∩ {z · e ≥ 0}`, the conclusion of
`FlatChartStatement` holds at `x₀`.

`F(y)` is the `e`-component of the local inverse of `z ↦ x₀ + P z + W(z) e`. -/
theorem exists_chart_of_smooth (H : IsFlatChartData U u x₀ e ρ G) {r : ℝ} (hr : 0 < r)
    (hA : BasicElliptic.halfBall e 0 r ⊆ Adm e ρ)
    (hbc : ∀ z ∈ ball 0 r ∩ BasicElliptic.flatPart e,
      ⟪field e (gradientWithin (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) z), e⟫ = 0)
    (hw0 : hodograph u x₀ e ρ 0 = 0)
    (hg0 : gradientWithin (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) 0 = e)
    {W : E d → ℝ} (hW : ContDiffOn ℝ ∞ W (ball 0 (r / 4)))
    (hWw : EqOn W (hodograph u x₀ e ρ) (ball 0 (r / 4) ∩ {z | 0 ≤ ⟪z, e⟫})) :
    ∃ ρ' > 0, ball x₀ ρ' ⊆ U ∧ ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ') ∧
      (∀ x ∈ ball x₀ ρ', u x = max (F x) 0) ∧ (∀ x ∈ ball x₀ ρ', ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ', F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ ball x₀ ρ', 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ' | 0 < F x} := by
  have he := H.norm_e
  have hρ := H.pos
  set w := hodograph u x₀ e ρ with hw
  set R := r / 4 with hRdef
  have hR : 0 < R := by positivity
  have hRr : R ≤ r := by linarith
  have h0K : (0 : E d) ∈ ball 0 R ∩ {z | 0 ≤ ⟪z, e⟫} := ⟨mem_ball_self hR, by simp⟩
  have hW0 : W 0 = 0 := (hWw h0K).trans hw0
  have hgradW : ∀ z ∈ ball 0 R ∩ {z | 0 ≤ ⟪z, e⟫},
      ∇ W z = gradientWithin w (BasicElliptic.halfBall e 0 r) z :=
    fun z hz ↦ gradient_eq_gradientWithin he hR hRr hW hWw hz
  have hgW0 : ∇ W 0 = e := (hgradW 0 h0K).trans hg0
  have hWd : ∀ z ∈ ball (0 : E d) R, DifferentiableAt ℝ W z := fun z hz ↦
    (hW.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hgc : ContinuousAt (∇ W) 0 := by
    have := (hW.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).continuousAt
      (isOpen_ball.mem_nhds (mem_ball_self hR))
    exact (toDual ℝ (E d)).symm.continuous.continuousAt.comp this
  have hWc : ContinuousAt W 0 := (hWd 0 (mem_ball_self hR)).continuousAt
  have hp0 : ⟪∇ W 0, e⟫ ≠ 0 := by rw [hgW0, inner_self_of_norm he]; norm_num
  have hqc : ContinuousAt (fun z ↦ gradVec e (∇ W z)) 0 :=
    ContinuousAt.comp (g := gradVec e) (continuousAt_gradVec hp0) hgc
  have hq0 : gradVec e (∇ W 0) = e := by rw [hgW0, gradVec_self he]
  -- a small ball `B_{R₂}(0)` where everything is controlled
  have hev1 : ∀ᶠ z in 𝓝 (0 : E d), ‖∇ W z - e‖ < 1 / 4 := by
    filter_upwards [hgc.eventually (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 4))] with z hz
    rwa [dist_eq_norm, hgW0] at hz
  have hev2 : ∀ᶠ z in 𝓝 (0 : E d), ‖gradVec e (∇ W z) - e‖ < 1 / 8 := by
    filter_upwards [hqc.eventually (ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 8))] with z hz
    rwa [dist_eq_norm, hq0] at hz
  have hev3 : ∀ᶠ z in 𝓝 (0 : E d), |W z| < ρ / 4 := by
    filter_upwards [hWc.eventually (ball_mem_nhds _ (by linarith : (0 : ℝ) < ρ / 4))] with z hz
    rwa [Real.dist_eq, hW0, sub_zero] at hz
  obtain ⟨R₃, hR₃, hR₃b⟩ := Metric.eventually_nhds_iff_ball.1 (hev1.and (hev2.and hev3))
  set R₂ := min R₃ (min R (ρ / 32)) with hR₂def
  have hR₂ : 0 < R₂ := lt_min hR₃ (lt_min hR (by linarith))
  have hR₂3 : R₂ ≤ R₃ := min_le_left _ _
  have hR₂R : R₂ ≤ R := (min_le_right _ _).trans (min_le_left _ _)
  have hR₂ρ : R₂ ≤ ρ / 32 := (min_le_right _ _).trans (min_le_right _ _)
  have hz1 : ∀ z ∈ ball (0 : E d) R₂, ‖∇ W z - e‖ < 1 / 4 := fun z hz ↦
    (hR₃b z (ball_subset_ball hR₂3 hz)).1
  have hz2 : ∀ z ∈ ball (0 : E d) R₂, ‖gradVec e (∇ W z) - e‖ < 1 / 8 := fun z hz ↦
    (hR₃b z (ball_subset_ball hR₂3 hz)).2.1
  have hz3 : ∀ z ∈ ball (0 : E d) R₂, |W z| < ρ / 4 := fun z hz ↦
    (hR₃b z (ball_subset_ball hR₂3 hz)).2.2
  have hzR : ∀ z ∈ ball (0 : E d) R₂, z ∈ ball (0 : E d) R := fun z hz ↦ ball_subset_ball hR₂R hz
  have hpe : ∀ z ∈ ball (0 : E d) R₂, 3 / 4 ≤ ⟪∇ W z, e⟫ := fun z hz ↦ by
    have h1 : ⟪∇ W z, e⟫ = 1 + ⟪∇ W z - e, e⟫ := by
      rw [inner_sub_left, inner_self_of_norm he]; ring
    have h2 := abs_real_inner_le_norm (∇ W z - e) e
    rw [he, mul_one] at h2
    linarith [neg_abs_le ⟪∇ W z - e, e⟫, hz1 z hz]
  have hpne : ∀ z ∈ ball (0 : E d) R₂, ⟪∇ W z, e⟫ ≠ 0 := fun z hz ↦ by
    linarith [hpe z hz]
  -- the graph map and its local inverse
  set Ψ : E d → E d := fun z ↦ x₀ + perpCLM e z + W z • e with hΨdef
  have hΨ0 : Ψ 0 = x₀ := by simp [hΨdef, hW0]
  have hΨd : ∀ z ∈ ball (0 : E d) R, HasFDerivAt Ψ (hodoCLM e (∇ W z)) z := fun z hz ↦
    hasFDerivAt_graphMap (hWd z hz)
  have hΨc : ∀ z ∈ ball (0 : E d) R, ContDiffAt ℝ ∞ Ψ z := fun z hz ↦
    (contDiffAt_const.add (perpCLM e).contDiff.contDiffAt).add
      ((hW.contDiffAt (isOpen_ball.mem_nhds hz)).smul contDiffAt_const)
  have hΨ' : ∀ z (hz : z ∈ ball (0 : E d) R₂),
      HasFDerivAt Ψ ((hodoEquiv he (hpne z hz) : E d ≃L[ℝ] E d) : E d →L[ℝ] E d) z :=
    fun z hz ↦ hΨd z (hzR z hz)
  have hstrict := (hΨc 0 (mem_ball_self hR)).hasStrictFDerivAt' (hΨ' 0 (mem_ball_self hR₂))
    (by simp)
  set Φ := hstrict.toOpenPartialHomeomorph Ψ with hΦdef
  have hΦΨ : ∀ z, Φ z = Ψ z := fun z ↦ rfl
  have h0src : (0 : E d) ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hx₀tgt : x₀ ∈ Φ.target := by
    have := hstrict.image_mem_toOpenPartialHomeomorph_target; rwa [hΨ0] at this
  have hsymm0 : Φ.symm x₀ = 0 := by
    have := Φ.left_inv h0src; rwa [hΦΨ, hΨ0] at this
  have hS : ∀ᶠ y in 𝓝 x₀, Φ.symm y ∈ ball (0 : E d) R₂ :=
    (Φ.continuousAt_symm hx₀tgt).preimage_mem_nhds (by rw [hsymm0]; exact ball_mem_nhds 0 hR₂)
  obtain ⟨ρ₁, hρ₁, hρ₁b⟩ := Metric.eventually_nhds_iff_ball.1
    ((show ∀ᶠ y in 𝓝 x₀, y ∈ Φ.target from Φ.open_target.mem_nhds hx₀tgt).and hS)
  set ρ' := min ρ₁ ρ with hρ'def
  have hρ' : 0 < ρ' := lt_min hρ₁ hρ
  have hyT : ∀ y ∈ ball x₀ ρ', y ∈ Φ.target := fun y hy ↦
    (hρ₁b y (ball_subset_ball (min_le_left _ _) hy)).1
  have hyz : ∀ y ∈ ball x₀ ρ', Φ.symm y ∈ ball (0 : E d) R₂ := fun y hy ↦
    (hρ₁b y (ball_subset_ball (min_le_left _ _) hy)).2
  have hΨy : ∀ y ∈ ball x₀ ρ', Ψ (Φ.symm y) = y := fun y hy ↦ Φ.right_inv (hyT y hy)
  have hBU : ball x₀ ρ' ⊆ U := (ball_subset_ball (min_le_right _ _)).trans H.ball_subset
  -- the chart
  set F : E d → ℝ := fun y ↦ ⟪Φ.symm y, e⟫ with hFdef
  have hFd : ∀ y ∈ ball x₀ ρ',
      HasFDerivAt F (toDual ℝ (E d) (gradVec e (∇ W (Φ.symm y)))) y := by
    intro y hy
    have hz := hyz y hy
    have hsD := Φ.hasFDerivAt_symm (hyT y hy) (hΨ' _ hz)
    have hfun : F = fun y ↦ innerSL ℝ e (Φ.symm y) := by
      funext y; rw [hFdef, innerSL_apply_apply, real_inner_comm]
    rw [hfun]
    refine ((innerSL ℝ e).hasFDerivAt.comp y hsD).congr_fderiv
      (ContinuousLinearMap.ext fun k ↦ ?_)
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, toDual_apply_apply]
    exact inner_hodoInvCLM he k
  have hFc : ∀ y ∈ ball x₀ ρ', ContDiffAt ℝ ∞ F y := by
    intro y hy
    have hz := hyz y hy
    have hsC := Φ.contDiffAt_symm (hyT y hy) (hΨ' _ hz) (hΨc _ (hzR _ hz))
    have hfun : F = fun y ↦ innerSL ℝ e (Φ.symm y) := by
      funext y; rw [hFdef, innerSL_apply_apply, real_inner_comm]
    rw [hfun]
    exact (innerSL ℝ e).contDiff.contDiffAt.comp y hsC
  have hgradF : ∀ y ∈ ball x₀ ρ', ∇ F y = gradVec e (∇ W (Φ.symm y)) := fun y hy ↦
    (hasGradientAt_iff_hasFDerivAt.2 (hFd y hy)).gradient
  -- `u = max(F, 0)`
  have hmax : ∀ y ∈ ball x₀ ρ', u y = max (F y) 0 := by
    intro y hy
    set z := Φ.symm y with hzdef
    have hz := hyz y hy
    have hyeq : y = x₀ + perpProj e z + W z • e := by
      rw [← perpCLM_apply]; exact (hΨy y hy).symm
    have hFy : F y = ⟪z, e⟫ := rfl
    by_cases ht : 0 ≤ ⟪z, e⟫
    · have hzK : z ∈ ball 0 R ∩ {z | 0 ≤ ⟪z, e⟫} := ⟨hzR z hz, ht⟩
      have hzA : z ∈ Adm e ρ :=
        hA ⟨ball_subset_closedBall (ball_subset_ball hRr (hzR z hz)), ht⟩
      have : y = hodographPt u x₀ e ρ z := by rw [hyeq, hWw hzK]; rfl
      have huy : u y = ⟪z, e⟫ := by rw [this]; exact H.apply_hodographPt hzA
      rw [huy, hFy, max_eq_left ht]
    · push Not at ht
      set Pz := perpProj e z with hPz
      have hzn : ‖z‖ < R₂ := by simpa using hz
      have hPzn : ‖Pz‖ ≤ ‖z‖ := norm_perpProj_le he z
      have hPzt : ⟪Pz, e⟫ = 0 := inner_perpProj he z
      have hPzK : Pz ∈ ball 0 R ∩ {z | 0 ≤ ⟪z, e⟫} :=
        ⟨by rw [mem_ball, dist_zero_right]; linarith, hPzt.ge⟩
      have hPzA : Pz ∈ Adm e ρ :=
        hA ⟨by rw [mem_closedBall, dist_zero_right]; linarith, hPzt.ge⟩
      -- the segment `Pz + τ e`, `τ ∈ [⟪z, e⟫, 0]`, lies in `B_{R₂}(0)`
      have hseg : ∀ τ, ⟪z, e⟫ ≤ τ → τ ≤ 0 → Pz + τ • e ∈ ball (0 : E d) R₂ := by
        intro τ h1 h2
        rw [mem_ball, dist_zero_right]
        have hsq := norm_perpProj_add_smul_sq he z τ
        have hzsq := norm_perpProj_add_smul_sq he z ⟪z, e⟫
        rw [perpProj_add_inner_smul] at hzsq
        have : ‖Pz + τ • e‖ ^ 2 ≤ ‖z‖ ^ 2 := by rw [hsq, hzsq]; nlinarith
        exact lt_of_le_of_lt
          ((pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this) hzn
      have hzPz : Pz + ⟪z, e⟫ • e = z := perpProj_add_inner_smul z
      have hlt : W z < W Pz := by
        obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun τ : ℝ ↦ W (Pz + τ • e))
          (fun τ ↦ ⟪∇ W (Pz + τ • e), e⟫) ht
          (fun τ hτ ↦ (ContinuousAt.comp (f := fun τ : ℝ ↦ Pz + τ • e)
            (hWd _ (hzR _ (hseg τ hτ.1 hτ.2))).continuousAt
            (by fun_prop : Continuous fun τ : ℝ ↦ Pz + τ • e).continuousAt).continuousWithinAt)
          (fun τ hτ ↦ hasDerivAt_line (hWd _ (hzR _ (hseg τ hτ.1.le hτ.2.le))))
        have hpos := hpe _ (hseg ξ hξ.1.le hξ.2.le)
        rw [hslope] at hpos
        simp only [zero_smul, add_zero, hzPz] at hpos
        have hden : 0 < 0 - ⟪z, e⟫ := by linarith
        rw [le_div_iff₀ hden] at hpos
        linarith
      have hWPz : W Pz = hodograph u x₀ e ρ Pz := hWw hPzK
      have hline : lineFn u x₀ e Pz (W z) = u y := by
        rw [lineFn, hPz, perpProj_perpProj he, hyeq]
      have hWz3 := hz3 z hz
      have hle : lineFn u x₀ e Pz (W z) ≤ ⟪Pz, e⟫ :=
        apply_le_of_lt_levelInf (by linarith) (H.lt_lineFn_half hPzA)
          (by linarith [(abs_lt.1 hWz3).1]) (hWPz ▸ hlt : W z < hodograph u x₀ e ρ Pz)
      rw [hline, hPzt] at hle
      rw [hFy, max_eq_right ht.le]
      linarith [H.nonneg y (hBU hy)]
  refine ⟨ρ', hρ', hBU, F, fun y hy ↦ (hFc y hy).contDiffWithinAt, hmax, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [hgradF y hy]
    exact gradVec_ne_zero he (hpne _ (hyz y hy))
  · intro y hy hF0
    rw [hgradF y hy]
    have hz := hyz y hy
    have hzt : ⟪Φ.symm y, e⟫ = 0 := hF0
    have hzK : Φ.symm y ∈ ball 0 R ∩ {z | 0 ≤ ⟪z, e⟫} := ⟨hzR _ hz, hzt.symm.le⟩
    rw [hgradW _ hzK]
    exact norm_gradVec_of_inner_field he (hbc _ ⟨ball_subset_ball hRr (hzR _ hz), hzt⟩)
  · intro y hy hFpos
    have hcont : ContinuousOn F (ball x₀ ρ') := fun y hy ↦
      (hFd y hy).continuousAt.continuousWithinAt
    have hO : IsOpen (ball x₀ ρ' ∩ F ⁻¹' Ioi 0) :=
      hcont.isOpen_inter_preimage isOpen_ball isOpen_Ioi
    have hev : F =ᶠ[𝓝 y] u := by
      filter_upwards [hO.mem_nhds ⟨hy, hFpos⟩] with y' hy'
      rw [hmax y' hy'.1, max_eq_left (le_of_lt hy'.2)]
    have hyP : y ∈ posSet u U :=
      ⟨hBU hy, by rw [hmax y hy, max_eq_left hFpos.le]; exact hFpos⟩
    rw [(laplacian_congr_nhds hev).self_of_nhds]
    simpa using (H.harmonic y hyP).2.self_of_nhds
  · have hF0 : F x₀ = 0 := by simp [hFdef, hsymm0]
    exact isPreconnected_pos he hρ' hF0 (fun y ↦ gradVec e (∇ W (Φ.symm y))) hFd
      fun y hy ↦ (hz2 _ (hyz y hy)).le

end IsFlatChartData

end EllipticBernoulli
