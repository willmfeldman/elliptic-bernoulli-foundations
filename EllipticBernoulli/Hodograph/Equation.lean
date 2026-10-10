/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Transform
import EllipticBernoulli.Classical.InnerVariationCalculus
import EllipticBernoulli.Viscosity.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.LinearAlgebra.Trace

/-!
# Regularity and the equation of the partial hodograph transform

Let `IsFlatChartData U u x₀ e ρ G` and let `w = hodograph u x₀ e ρ` be the partial hodograph
transform (`Hodograph/Transform.lean`).

## Main results

* `IsFlatChartData.continuousWithinAt_hodograph`: `w` is continuous on the admissible region,
  up to `t = 0`.
* `IsFlatChartData.hodograph_zero`: `w(0) = 0` (the free boundary passes through `x₀`).
* `IsFlatChartData.hodographPt_local`: for `t > 0`, `z ↦ x₀ + P z + w(z) e` is the local inverse of
  the hodograph map `y ↦ P(y - x₀) + u(y) e`; it is `C²` with derivative `hodoInvCLM e ∇u`.
* `IsFlatChartData.hasFDerivAt_hodograph`: `∇w = gradVec e ∇u` for `t > 0`.
* `IsFlatChartData.divergence_field_eq_zero`: `div Φ(∇w) = 0` for `t > 0`. Along the transform
  `Φ(∇w) = V(∇u)` with `V(p) = -2 P p + (1 - |p|²) e`, and `D(V ∘ ∇u) = -2 (hodoCLM e ∇u) ∘ D²u`;
  composing with the derivative `(hodoCLM e ∇u)⁻¹` of the transform, the trace is `-2 Δu = 0`.
* `IsFlatChartData.exists_hodograph`: on a closed half ball `halfBall e 0 r`, `w` is `C¹` (with
  derivatives within the half ball), `C²` in the interior, `|∇w - e| ≤ η`, `div Φ(∇w) = 0` inside,
  `Φ(∇w) · e = 0` on `t = 0`, `w(0) = 0` and `∇w(0) = e`. The `C¹` property up to `t = 0`
  comes from `hasFDerivWithinAt_closure_of_tendsto_fderiv`: the interior gradient
  `gradVec e (G(x₀ + P z + w(z) e))` extends continuously to `t = 0`.

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

public section

namespace EllipticBernoulli

open Hodograph

variable {d : ℕ} {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d} {ρ : ℝ} {G : E d → E d}

namespace IsFlatChartData

variable (H : IsFlatChartData U u x₀ e ρ G)
include H

theorem continuousAt_lineFn_left {z₀ : E d} {s : ℝ} (hz : ‖perpProj e z₀‖ < ρ / 2)
    (hs : |s| ≤ ρ / 2) : ContinuousAt (fun z ↦ lineFn u x₀ e z s) z₀ := by
  have hu : ContinuousAt u (x₀ + perpProj e z₀ + s • e) :=
    H.continuousOn.continuousAt (H.isOpen.mem_nhds (H.ball_subset (H.line_mem_ball hz hs)))
  have hc : Continuous fun z : E d ↦ x₀ + perpProj e z + s • e :=
    (continuous_const.add (continuous_perpProj e)).add continuous_const
  exact ContinuousAt.comp (f := fun z : E d ↦ x₀ + perpProj e z + s • e) hu hc.continuousAt

/-- **Continuity of the partial hodograph transform** on the admissible region, up to `t = 0`. -/
theorem continuousWithinAt_hodograph {z₀ : E d} (hz₀ : z₀ ∈ Adm e ρ) :
    ContinuousWithinAt (hodograph u x₀ e ρ) (Adm e ρ) z₀ := by
  have hρ := H.pos
  rw [ContinuousWithinAt, Metric.tendsto_nhds]
  intro ε hε
  set η := min (ε / 2) (ρ / 16) with hη
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hηε : η < ε := (min_le_left _ _).trans_lt (by linarith)
  have hηρ : η ≤ ρ / 16 := min_le_right _ _
  set s₀ := hodograph u x₀ e ρ z₀ with hs₀
  have hw := H.hodograph_mem hz₀
  have habs : ∀ s, -(ρ / 2) ≤ s → s ≤ ρ / 2 → |s| ≤ ρ / 2 := fun s h1 h2 ↦ abs_le.2 ⟨h1, h2⟩
  have hinner : Continuous fun z : E d ↦ ⟪z, e⟫ := by fun_prop
  have hup : ∀ᶠ z in 𝓝[Adm e ρ] z₀, hodograph u x₀ e ρ z ≤ s₀ + η := by
    have h1 : ⟪z₀, e⟫ < lineFn u x₀ e z₀ (s₀ + η) := H.lt_lineFn hz₀ (by linarith) (by linarith)
    have hc : ContinuousAt (fun z ↦ lineFn u x₀ e z (s₀ + η) - ⟪z, e⟫) z₀ :=
      (H.continuousAt_lineFn_left hz₀.1 (habs _ (by linarith) (by linarith))).sub
        hinner.continuousAt
    have hev := hc.eventually (lt_mem_nhds (sub_pos.2 h1))
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hz _
    exact levelInf_le ⟨by linarith, by linarith⟩ (sub_pos.1 hz)
  have hdown : ∀ᶠ z in 𝓝[Adm e ρ] z₀, s₀ - η ≤ hodograph u x₀ e ρ z := by
    have hφs₀ : lineFn u x₀ e z₀ s₀ = ⟪z₀, e⟫ := H.apply_hodographPt hz₀
    have hclaim : lineFn u x₀ e z₀ (s₀ - η / 2) < ⟪z₀, e⟫ + η / 4 := by
      by_cases hp : 0 < lineFn u x₀ e z₀ (s₀ - η / 2)
      · have := H.isGrowing hz₀.1 (s₀ - η / 2) s₀ (by linarith) (by linarith) (by linarith) hp
        linarith
      · push Not at hp; linarith [hz₀.2.1]
    have hc : ContinuousAt (fun z ↦ ⟪z, e⟫ + η / 4 - lineFn u x₀ e z (s₀ - η / 2)) z₀ :=
      (hinner.continuousAt.add continuousAt_const).sub
        (H.continuousAt_lineFn_left hz₀.1 (habs _ (by linarith) (by linarith)))
    have hev := hc.eventually (lt_mem_nhds (sub_pos.2 hclaim))
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with z hz hzA
    by_contra hlt
    push Not at hlt
    have h1 := H.lt_lineFn hzA hlt (by linarith)
    have h2 := H.isGrowing hzA.1 (s₀ - η) (s₀ - η / 2) (by linarith) (by linarith) (by linarith)
      (hzA.2.1.trans_lt h1)
    linarith [sub_pos.1 hz]
  filter_upwards [hup, hdown] with z h1 h2
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

theorem continuousOn_hodographPt : ContinuousOn (hodographPt u x₀ e ρ) (Adm e ρ) :=
  (continuousOn_const.add (continuous_perpProj e).continuousOn).add
    ((show ContinuousOn (hodograph u x₀ e ρ) (Adm e ρ) from
      fun _ hz ↦ H.continuousWithinAt_hodograph hz).smul continuousOn_const)

theorem apply_x₀ : u x₀ = 0 := by
  have hx := H.mem_freeBoundary
  have hP : IsOpen (posSet u U) := isOpen_posSet H.isOpen H.continuousOn
  have hnot : x₀ ∉ posSet u U := fun h ↦ hx.1.2 (hP.interior_eq.symm ▸ h)
  by_contra hne
  exact hnot ⟨hx.2, lt_of_le_of_ne (H.nonneg x₀ hx.2) (Ne.symm hne)⟩

theorem zero_mem_adm : (0 : E d) ∈ Adm e ρ := by
  have hρ := H.pos
  refine ⟨?_, by simp, by simp; linarith⟩
  simp [perpProj]; linarith

/-- The free boundary passes through `x₀`: `w(0) = 0`. -/
theorem hodograph_zero : hodograph u x₀ e ρ 0 = 0 := by
  have hρ := H.pos
  have he := H.norm_e
  have h0 := H.zero_mem_adm
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    set g := hodograph u x₀ e ρ 0 with hg
    obtain ⟨δ, hδ, hcont⟩ :=
      Metric.continuousWithinAt_iff.1 (H.continuousWithinAt_hodograph h0) (g / 2) (by linarith)
    have hm : 0 < min δ (min (g / 2) (ρ / 32)) := lt_min hδ (lt_min (by linarith) (by linarith))
    obtain ⟨y, hyP, hyd⟩ := Metric.mem_closure_iff.1 H.mem_freeBoundary.1.1 _ hm
    have hyx : ‖y - x₀‖ < min δ (min (g / 2) (ρ / 32)) := by rwa [← dist_eq_norm, dist_comm]
    have hyx1 : ‖y - x₀‖ < δ := hyx.trans_le (min_le_left _ _)
    have hyx2 : ‖y - x₀‖ < g / 2 := hyx.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hyx3 : ‖y - x₀‖ < ρ / 32 := hyx.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    set z := perpProj e (y - x₀) with hz
    have hzn : ‖z‖ ≤ ‖y - x₀‖ := norm_perpProj_le he _
    have hzt : ⟪z, e⟫ = 0 := inner_perpProj he _
    have hzA : z ∈ Adm e ρ :=
      ⟨by rw [hz, perpProj_perpProj he]; linarith, hzt.ge, by rw [hzt]; linarith⟩
    have hwz := hcont hzA (by rw [dist_zero_right]; linarith)
    set s := ⟪y - x₀, e⟫ with hs
    have hsabs : |s| ≤ ‖y - x₀‖ := by
      have := abs_real_inner_le_norm (y - x₀) e
      rwa [he, mul_one] at this
    have hline : lineFn u x₀ e z s = u y := by
      rw [lineFn, hz, perpProj_perpProj he, add_assoc, perpProj_add_inner_smul, add_sub_cancel]
    have hle : hodograph u x₀ e ρ z ≤ s :=
      levelInf_le ⟨by linarith [(abs_le.1 hsabs).1], by linarith [(abs_le.1 hsabs).2]⟩
        (by rw [hzt, hline]; exact hyP.2)
    rw [Real.dist_eq, abs_lt] at hwz
    linarith [(abs_le.1 hsabs).2]
  · by_contra hlt
    push Not at hlt
    have := H.lt_lineFn h0 hlt (by linarith)
    simp [lineFn, perpProj, H.apply_x₀] at this

theorem hodographPt_zero : hodographPt u x₀ e ρ 0 = x₀ := by
  simp [hodographPt, H.hodograph_zero, perpProj]

theorem hasFDerivAt_hodoMap {y₀ : E d} (hy₀ : y₀ ∈ posSet u U) :
    HasFDerivAt (hodoMap u x₀ e) (hodoCLM e (∇ u y₀)) y₀ := by
  have hu : DifferentiableAt ℝ u y₀ := (H.harmonic y₀ hy₀).1.differentiableAt (by norm_num)
  have hfun : hodoMap u x₀ e = fun y ↦ perpCLM e (y - x₀) + u y • e := by
    funext y; rw [hodoMap, perpCLM_apply]
  rw [hfun]
  have := ((perpCLM e).hasFDerivAt.comp y₀ ((hasFDerivAt_id y₀).sub_const x₀)).add
    (hu.hasFDerivAt.smul_const e)
  refine this.congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
  rw [hodoCLM_apply]
  simp [perpCLM_apply, gradient, toDual_symm_apply]

/-- **The transform is the local inverse of the hodograph map** for `t > 0`: it is `C²` near `z₀`
with derivative `hodoInvCLM e ∇u`. -/
theorem hodographPt_local {z₀ : E d} (hz₀ : z₀ ∈ Adm e ρ) (ht₀ : 0 < ⟪z₀, e⟫) :
    ⟪∇ u (hodographPt u x₀ e ρ z₀), e⟫ ≠ 0 ∧
      HasFDerivAt (hodographPt u x₀ e ρ) (hodoInvCLM e (∇ u (hodographPt u x₀ e ρ z₀))) z₀ ∧
      ContDiffAt ℝ 2 (hodographPt u x₀ e ρ) z₀ := by
  have he := H.norm_e
  have hρ := H.pos
  set y₀ := hodographPt u x₀ e ρ z₀ with hy₀def
  have hy₀P := H.hodographPt_mem_posSet hz₀ ht₀
  have hy₀B := H.hodographPt_mem_ball hz₀
  have hp : ⟪∇ u y₀, e⟫ ≠ 0 := by
    rw [← H.G_eq y₀ ⟨hy₀P, hy₀B⟩]
    have := H.inner_G y₀ ⟨subset_closure hy₀P, hy₀B⟩
    exact (by linarith : (0 : ℝ) < _).ne'
  refine ⟨hp, ?_⟩
  have hu2 : ContDiffAt ℝ 2 u y₀ := (H.harmonic y₀ hy₀P).1
  have hTc : ContDiffAt ℝ 2 (hodoMap u x₀ e) y₀ := by
    have hfun : hodoMap u x₀ e = fun y ↦ perpCLM e (y - x₀) + u y • e := by
      funext y; rw [hodoMap, perpCLM_apply]
    rw [hfun]
    exact ((perpCLM e).contDiff.contDiffAt.comp y₀ (contDiffAt_id.sub contDiffAt_const)).add
      (hu2.smul contDiffAt_const)
  have hT' : HasFDerivAt (hodoMap u x₀ e) ((hodoEquiv he hp : E d ≃L[ℝ] E d) : E d →L[ℝ] E d) y₀ :=
    H.hasFDerivAt_hodoMap hy₀P
  have hn : (2 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hstrict := hTc.hasStrictFDerivAt' hT' hn
  have hTy₀ : hodoMap u x₀ e y₀ = z₀ := H.hodoMap_hodographPt hz₀
  have hleft : ∀ᶠ y in 𝓝 y₀, hodographPt u x₀ e ρ (hodoMap u x₀ e y) = y := by
    have hw := H.hodograph_mem hz₀
    have hc1 : ContinuousAt (fun y ↦ ‖perpProj e (y - x₀)‖) y₀ :=
      ((continuous_perpProj e).comp (continuous_id.sub continuous_const)).norm.continuousAt
    have hc2 : ContinuousAt (fun y ↦ |⟪y - x₀, e⟫|) y₀ := by fun_prop
    have hP0 : ‖perpProj e (y₀ - x₀)‖ < ρ / 2 := by
      rw [← perpProj_hodoMap (u := u) he, hTy₀]; exact hz₀.1
    have hs0 : |⟪y₀ - x₀, e⟫| < ρ / 2 := by
      rw [← hodograph_eq_inner he, abs_lt]; constructor <;> linarith
    have huc : ContinuousAt u y₀ := H.continuousOn.continuousAt (H.isOpen.mem_nhds hy₀P.1)
    have hu0 : u y₀ = ⟪z₀, e⟫ := H.apply_hodographPt hz₀
    filter_upwards [hc1.eventually (gt_mem_nhds hP0), hc2.eventually (gt_mem_nhds hs0),
      huc.eventually (lt_mem_nhds (show (0 : ℝ) < u y₀ by rw [hu0]; exact ht₀)),
      huc.eventually (gt_mem_nhds (show u y₀ < ρ / 16 by rw [hu0]; exact hz₀.2.2))]
      with y h1 h2 h3 h4
    exact H.hodographPt_hodoMap h1 h2.le h3 h4
  have huniq := hstrict.localInverse_unique hleft
  rw [hTy₀] at huniq
  have hinv := hstrict.to_localInverse
  rw [hTy₀] at hinv
  refine ⟨hinv.hasFDerivAt.congr_of_eventuallyEq huniq, ?_⟩
  have hcd := hTc.to_localInverse hT' hn
  rw [hTy₀] at hcd
  exact hcd.congr_of_eventuallyEq huniq

/-- The gradient of the transform for `t > 0`: `∇w = gradVec e ∇u`, and `w` is `C²` there. -/
theorem hasFDerivAt_hodograph {z₀ : E d} (hz₀ : z₀ ∈ Adm e ρ) (ht₀ : 0 < ⟪z₀, e⟫) :
    HasFDerivAt (hodograph u x₀ e ρ)
      (toDual ℝ (E d) (gradVec e (∇ u (hodographPt u x₀ e ρ z₀)))) z₀ ∧
      ContDiffAt ℝ 2 (hodograph u x₀ e ρ) z₀ := by
  obtain ⟨_, hD, hC⟩ := H.hodographPt_local hz₀ ht₀
  have hfun : hodograph u x₀ e ρ = fun z ↦ innerSL ℝ e (hodographPt u x₀ e ρ z - x₀) := by
    funext z; rw [hodograph_eq_inner H.norm_e, innerSL_apply_apply, real_inner_comm]
  rw [hfun]
  refine ⟨?_, (innerSL ℝ e).contDiff.contDiffAt.comp z₀ (hC.sub contDiffAt_const)⟩
  have := (innerSL ℝ e).hasFDerivAt.comp z₀ (hD.sub_const x₀)
  refine this.congr_fderiv (ContinuousLinearMap.ext fun k ↦ ?_)
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, inner_hodoInvCLM H.norm_e,
    toDual_apply_apply]

/-- **The hodograph equation** `div Φ(∇w) = 0` for `t > 0`, by the chain rule. -/
theorem divergence_field_eq_zero {z₀ : E d} (hz₀ : z₀ ∈ Adm e ρ) (ht₀ : 0 < ⟪z₀, e⟫) :
    divergence (fun z ↦ field e (∇ (hodograph u x₀ e ρ) z)) z₀ = 0 := by
  have he := H.norm_e
  set O : Set (E d) := {z | ‖perpProj e z‖ < ρ / 2 ∧ 0 < ⟪z, e⟫ ∧ ⟪z, e⟫ < ρ / 16} with hOdef
  have hinner : Continuous fun z : E d ↦ ⟪z, e⟫ := by fun_prop
  have hO : IsOpen O :=
    (isOpen_lt ((continuous_perpProj e).norm) continuous_const).inter
      ((isOpen_lt continuous_const hinner).inter (isOpen_lt hinner continuous_const))
  have hOA : O ⊆ Adm e ρ := fun z hz ↦ ⟨hz.1, hz.2.1.le, hz.2.2⟩
  have hz₀O : z₀ ∈ O := ⟨hz₀.1, ht₀, hz₀.2.2⟩
  have hev : (fun z ↦ field e (∇ (hodograph u x₀ e ρ) z)) =ᶠ[𝓝 z₀]
      fun z ↦ fieldOf e (∇ u (hodographPt u x₀ e ρ z)) := by
    filter_upwards [hO.mem_nhds hz₀O] with z hz
    obtain ⟨hp, -⟩ := H.hodographPt_local (hOA hz) hz.2.1
    rw [(hasGradientAt_iff_hasFDerivAt.2 (H.hasFDerivAt_hodograph (hOA hz) hz.2.1).1).gradient,
      field_gradVec he hp]
  rw [divergence, hev.fderiv_eq]
  obtain ⟨hp, hD, -⟩ := H.hodographPt_local hz₀ ht₀
  set y₀ := hodographPt u x₀ e ρ z₀ with hy₀def
  have hy₀P := H.hodographPt_mem_posSet hz₀ ht₀
  have hu2 : ContDiffAt ℝ 2 u y₀ := (H.harmonic y₀ hy₀P).1
  have hdd : DifferentiableAt ℝ (fderiv ℝ u) y₀ :=
    (hu2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg : HasFDerivAt (∇ u) (fderiv ℝ (∇ u) y₀) y₀ := (differentiableAt_gradient hdd).hasFDerivAt
  set Hs := fderiv ℝ (∇ u) y₀ with hHs
  set p := ∇ u y₀ with hpdef
  have hV : HasFDerivAt (fun y ↦ fieldOf e (∇ u y)) ((-2 : ℝ) • (hodoCLM e p).comp Hs) y₀ := by
    have hfun : (fun y ↦ fieldOf e (∇ u y)) =
        fun y ↦ (-2 : ℝ) • perpCLM e (∇ u y) + (1 - ‖∇ u y‖ ^ 2) • e := by
      funext y; rw [fieldOf, perpCLM_apply]
    rw [hfun]
    have := (((perpCLM e).hasFDerivAt.comp y₀ hg).const_smul (-2 : ℝ)).add
      (((hasFDerivAt_const (1 : ℝ) y₀).sub hg.norm_sq).smul_const e)
    refine this.congr_fderiv (ContinuousLinearMap.ext fun k ↦ ?_)
    simp only [smul_apply, ContinuousLinearMap.comp_apply, hodoCLM_apply, add_apply,
      ContinuousLinearMap.smulRight_apply, perpCLM_apply, sub_apply, zero_apply,
      innerSL_apply_apply]
    simp only [neg_smul, two_smul, neg_add_rev, inner_gradient_left, zero_sub, smul_add, smul_smul,
      neg_mul, add_right_inj]
    have hpk : ⟪p, Hs k⟫ = fderiv ℝ u y₀ (Hs k) := by rw [hpdef, gradient, toDual_symm_apply]
    rw [hpk, ← neg_smul]
    congr 1
    ring
  have hcomp := hV.comp z₀ hD
  rw [show (fun z ↦ fieldOf e (∇ u (hodographPt u x₀ e ρ z))) =
    (fun y ↦ fieldOf e (∇ u y)) ∘ hodographPt u x₀ e ρ from rfl, hcomp.fderiv]
  have e1 : ((((-2 : ℝ) • (hodoCLM e p).comp Hs).comp (hodoInvCLM e p) : E d →L[ℝ] E d) :
      E d →ₗ[ℝ] E d) = (-2 : ℝ) • (((hodoCLM e p).comp Hs : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) ∘ₗ
        ((hodoInvCLM e p : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) := by
    ext k; simp
  rw [e1, map_smul, LinearMap.trace_comp_comm']
  have e2 : ((hodoInvCLM e p : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) ∘ₗ
      (((hodoCLM e p).comp Hs : E d →L[ℝ] E d) : E d →ₗ[ℝ] E d) = (Hs : E d →ₗ[ℝ] E d) := by
    ext k; simp [hodoInvCLM_hodoCLM he hp]
  rw [e2, trace_fderiv_gradient hdd, (H.harmonic y₀ hy₀P).2.self_of_nhds]
  simp

end IsFlatChartData

/-! ### Half balls -/

theorem Hodograph.isClosed_halfBall (e : E d) (r : ℝ) : IsClosed (BasicElliptic.halfBall e 0 r) :=
  isClosed_closedBall.inter (isClosed_le continuous_const (by fun_prop))

theorem Hodograph.convex_halfBall (e : E d) (r : ℝ) : Convex ℝ (BasicElliptic.halfBall e 0 r) :=
  (convex_closedBall 0 r).inter (convex_halfSpace_ge (f := fun z : E d ↦ ⟪z, e⟫)
    ⟨fun x y ↦ inner_add_left x y e, fun c x ↦ real_inner_smul_left x e c⟩ 0)

theorem Hodograph.convex_openHalfSpace (e : E d) : Convex ℝ (BasicElliptic.openHalfSpace e) :=
  convex_halfSpace_gt (f := fun z : E d ↦ ⟪z, e⟫)
    ⟨fun x y ↦ inner_add_left x y e, fun c x ↦ real_inner_smul_left x e c⟩ 0

theorem Hodograph.halfBall_subset_adm (hρ : 0 < ρ) (he : ‖e‖ = 1) {r : ℝ} (hr : r ≤ ρ / 32) :
    BasicElliptic.halfBall e 0 r ⊆ Adm e ρ := fun z hz ↦ by
  have hz1 : ‖z‖ ≤ r := by simpa using hz.1
  have hzt : ⟪z, e⟫ ≤ ‖z‖ := by
    have := real_inner_le_norm z e; rwa [he, mul_one] at this
  exact ⟨(norm_perpProj_le he z).trans_lt (by linarith), hz.2, by linarith⟩

/-- The closed half ball is the closure of the open one. -/
theorem Hodograph.halfBall_subset_closure (he : ‖e‖ = 1) {r : ℝ} (hr : 0 < r) :
    BasicElliptic.halfBall e 0 r ⊆ closure (ball 0 r ∩ BasicElliptic.openHalfSpace e) := by
  intro z hz
  set c : E d := (r / 2) • e with hc
  have hT : Tendsto (fun l : ℝ ↦ (1 - l) • z + l • c) (𝓝[>] 0) (𝓝 z) := by
    have : Continuous (fun l : ℝ ↦ (1 - l) • z + l • c) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with l hl
  have hz1 : ‖z‖ ≤ r := by simpa using hz.1
  have hzt : 0 ≤ ⟪z, e⟫ := hz.2
  constructor
  · rw [mem_ball, dist_zero_right]
    calc ‖(1 - l) • z + l • c‖ ≤ ‖(1 - l) • z‖ + ‖l • c‖ := norm_add_le _ _
      _ = (1 - l) * ‖z‖ + l * (r / 2) := by
          rw [hc, norm_smul, norm_smul, norm_smul, he, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos (by linarith [hl.2] : (0 : ℝ) < 1 - l), abs_of_pos hl.1,
            abs_of_pos (by linarith : (0 : ℝ) < r / 2), mul_one]
      _ < r := by nlinarith [hl.1, hl.2]
  · change 0 < ⟪(1 - l) • z + l • c, e⟫
    rw [inner_add_left, real_inner_smul_left, hc, real_inner_smul_left, real_inner_smul_left,
      inner_self_of_norm he]
    nlinarith [hl.1, hl.2]

namespace IsFlatChartData

variable (H : IsFlatChartData U u x₀ e ρ G)
include H

/-- The gradient of the transform up to `t = 0`, `gradVec e (G (x₀ + P z + w(z) e))`, is
continuous on the admissible region. -/
theorem continuousOn_gradVec_G :
    ContinuousOn (fun z ↦ gradVec e (G (hodographPt u x₀ e ρ z))) (Adm e ρ) := by
  have hGc : ContinuousOn (fun z ↦ G (hodographPt u x₀ e ρ z)) (Adm e ρ) :=
    H.continuousOn_G.comp H.continuousOn_hodographPt fun z hz ↦
      ⟨H.hodographPt_mem_closure hz, H.hodographPt_mem_ball hz⟩
  have hne : ∀ z ∈ Adm e ρ, ⟪G (hodographPt u x₀ e ρ z), e⟫ ≠ 0 := fun z hz ↦ by
    have := H.inner_G _ ⟨H.hodographPt_mem_closure hz, H.hodographPt_mem_ball hz⟩
    exact (by linarith : (0 : ℝ) < _).ne'
  have hin : ContinuousOn (fun z ↦ ⟪G (hodographPt u x₀ e ρ z), e⟫) (Adm e ρ) :=
    hGc.inner continuousOn_const
  unfold gradVec
  exact (hin.inv₀ hne).smul (continuousOn_const.sub ((continuous_perpProj e).comp_continuousOn hGc))

/-- **The partial hodograph transform on a half ball** (Kinderlehrer–Nirenberg (1977)). For every
`η > 0` there is `r > 0` such that on `halfBall e 0 r`:
* `w = hodograph u x₀ e ρ` is `C¹` (derivatives within the half ball) and `C²` inside;
* `|∇w - e| ≤ η`;
* `div Φ(∇w) = 0` inside, with `Φ = field e`;
* `Φ(∇w) · e = 0` on the flat part `{z · e = 0}` (this is `|∇u| = 1` on the free boundary);
* `w(0) = 0` and `∇w(0) = e`. -/
theorem exists_hodograph {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, BasicElliptic.halfBall e 0 r ⊆ Adm e ρ ∧
      ContDiffOn ℝ 1 (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) ∧
      ContDiffOn ℝ 2 (hodograph u x₀ e ρ) (ball 0 r ∩ BasicElliptic.openHalfSpace e) ∧
      (∀ z ∈ BasicElliptic.halfBall e 0 r,
        ‖gradientWithin (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) z - e‖ ≤ η) ∧
      (∀ z ∈ ball 0 r ∩ BasicElliptic.openHalfSpace e,
        divergence (fun p ↦ field e (∇ (hodograph u x₀ e ρ) p)) z = 0) ∧
      (∀ z ∈ ball 0 r ∩ BasicElliptic.flatPart e,
        ⟪field e (gradientWithin (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) z), e⟫ = 0) ∧
      hodograph u x₀ e ρ 0 = 0 ∧
      gradientWithin (hodograph u x₀ e ρ) (BasicElliptic.halfBall e 0 r) 0 = e := by
  have he := H.norm_e
  have hρ := H.pos
  set w := hodograph u x₀ e ρ with hw
  set q : E d → E d := fun z ↦ gradVec e (G (hodographPt u x₀ e ρ z)) with hq
  have hqc : ContinuousOn q (Adm e ρ) := H.continuousOn_gradVec_G
  have hq0 : q 0 = e := by simp only [hq, H.hodographPt_zero, H.G_x₀, gradVec_self he]
  obtain ⟨δ, hδ, hqδ⟩ := Metric.continuousWithinAt_iff.1 (hqc 0 H.zero_mem_adm) η hη
  set r := min (ρ / 32) (δ / 2) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by linarith)
  have hrρ : r ≤ ρ / 32 := min_le_left _ _
  have hrδ : r < δ := (min_le_right _ _).trans_lt (by linarith)
  have hHA : BasicElliptic.halfBall e 0 r ⊆ Adm e ρ := halfBall_subset_adm hρ he hrρ
  set S := ball (0 : E d) r ∩ BasicElliptic.openHalfSpace e with hS
  have hSH : S ⊆ BasicElliptic.halfBall e 0 r := fun z hz ↦
    ⟨ball_subset_closedBall hz.1, show 0 ≤ ⟪z, e⟫ from le_of_lt hz.2⟩
  have hSA : S ⊆ Adm e ρ := hSH.trans hHA
  have hinner : Continuous fun z : E d ↦ ⟪z, e⟫ := by fun_prop
  have hSo : IsOpen S := isOpen_ball.inter (isOpen_lt continuous_const hinner)
  have hSc : Convex ℝ S := (convex_ball 0 r).inter (convex_openHalfSpace e)
  have hHcl : BasicElliptic.halfBall e 0 r ⊆ closure S := halfBall_subset_closure he hr0
  have hclH : closure S ⊆ BasicElliptic.halfBall e 0 r :=
    closure_minimal hSH (isClosed_halfBall e r)
  have hG : ∀ z ∈ S, ∇ u (hodographPt u x₀ e ρ z) = G (hodographPt u x₀ e ρ z) := fun z hz ↦
    (H.G_eq _ ⟨H.hodographPt_mem_posSet (hSA hz) hz.2, H.hodographPt_mem_ball (hSA hz)⟩).symm
  have hderS : ∀ z ∈ S, HasFDerivAt w (toDual ℝ (E d) (q z)) z := fun z hz ↦ by
    have := (H.hasFDerivAt_hodograph (hSA hz) hz.2).1
    rwa [hG z hz] at this
  have hwithin : ∀ z ∈ BasicElliptic.halfBall e 0 r,
      HasFDerivWithinAt w (toDual ℝ (E d) (q z)) (BasicElliptic.halfBall e 0 r) z := by
    intro z hz
    have hL : ContinuousWithinAt (fun z ↦ toDual ℝ (E d) (q z)) S z :=
      ((toDual ℝ (E d)).continuous.continuousAt.comp_continuousWithinAt (hqc z (hHA hz))).mono
        hSA
    have hT : Tendsto (fderiv ℝ w) (𝓝[S] z) (𝓝 (toDual ℝ (E d) (q z))) := by
      refine hL.tendsto.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hderS y hy).fderiv.symm
    exact (hasFDerivWithinAt_closure_of_tendsto_fderiv
      (fun y hy ↦ (hderS y hy).differentiableAt.differentiableWithinAt) hSc hSo
      (fun y hy ↦ (H.continuousWithinAt_hodograph (hHA (hclH hy))).mono hSA) hT).mono hHcl
  have hcS : (r / 2) • e ∈ S := by
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_smul, he, mul_one, Real.norm_of_nonneg (by linarith)]
      linarith
    · change 0 < ⟪(r / 2) • e, e⟫
      rw [real_inner_smul_left, inner_self_of_norm he]; linarith
  have huniq : UniqueDiffOn ℝ (BasicElliptic.halfBall e 0 r) :=
    uniqueDiffOn_convex (convex_halfBall e r) ⟨(r / 2) • e, interior_maximal hSH hSo hcS⟩
  have hgw : ∀ z ∈ BasicElliptic.halfBall e 0 r,
      gradientWithin w (BasicElliptic.halfBall e 0 r) z = q z := fun z hz ↦ by
    rw [gradientWithin, (hwithin z hz).fderivWithin (huniq z hz),
      LinearIsometryEquiv.symm_apply_apply]
  refine ⟨r, hr0, hHA, ?_, ?_, ?_, ?_, ?_, H.hodograph_zero, ?_⟩
  · rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn huniq]
    refine ⟨by simp, fun z ↦ toDual ℝ (E d) (q z), ?_, hwithin⟩
    exact contDiffOn_zero.2 ((toDual ℝ (E d)).continuous.comp_continuousOn (hqc.mono hHA))
  · exact fun z hz ↦ (H.hasFDerivAt_hodograph (hSA hz) hz.2).2.contDiffWithinAt
  · intro z hz
    rw [hgw z hz]
    have hz1 : ‖z‖ ≤ r := by simpa using hz.1
    have := hqδ (hHA hz) (by rw [dist_zero_right]; exact hz1.trans_lt hrδ)
    rw [hq0, dist_eq_norm] at this
    exact this.le
  · exact fun z hz ↦ H.divergence_field_eq_zero (hSA hz) hz.2
  · intro z hz
    have hzt : ⟪z, e⟫ = 0 := hz.2
    have hzH : z ∈ BasicElliptic.halfBall e 0 r := ⟨ball_subset_closedBall hz.1, hzt.symm.le⟩
    rw [hgw z hzH]
    have hzA := hHA hzH
    have hfb := H.hodographPt_mem_freeBoundary hzA hzt
    have hB := H.hodographPt_mem_ball hzA
    have hne : ⟪G (hodographPt u x₀ e ρ z), e⟫ ≠ 0 := by
      have := H.inner_G _ ⟨H.hodographPt_mem_closure hzA, hB⟩
      exact (by linarith : (0 : ℝ) < _).ne'
    simp only [hq]
    rw [field_gradVec he hne, inner_fieldOf he, H.norm_G _ ⟨hfb, hB⟩]
    norm_num
  · rw [hgw 0 ⟨mem_closedBall_self hr0.le, by simp⟩, hq0]

end IsFlatChartData

end EllipticBernoulli
