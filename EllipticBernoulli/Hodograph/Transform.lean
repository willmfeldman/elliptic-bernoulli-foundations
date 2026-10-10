/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Flat
public import EllipticBernoulli.Hodograph.Line
public import EllipticBernoulli.Hodograph.Field
import EllipticBernoulli.Classical.InnerVariationCalculus
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Trace

/-!
# The partial hodograph transform

Let `IsFlatChartData U u x₀ e ρ G` (`Hodograph/Flat.lean`). Write points near `x₀` as
`x₀ + x' + s e` with `x' ⊥ e`. Along each vertical line `s ↦ u(x₀ + x' + s e)` (`lineFn`), `u`
vanishes below the free boundary and grows with slope at least `1/2` above it. The **partial
hodograph transform** `w = hodograph u x₀ e ρ` is the height of the level set `{u = t}`:
`u(x₀ + x' + w(x' + t e) e) = t` for `t ≥ 0` small (Kinderlehrer–Nirenberg (1977)). On `t = 0`
it is the free boundary.

## Main results

* `IsFlatChartData.apply_hodographPt`: `u(x₀ + P z + w(z) e) = z · e`.
* `IsFlatChartData.continuousWithinAt_hodograph`: `w` is continuous up to `t = 0`.
* `IsFlatChartData.hasFDerivAt_hodographPt`: for `t > 0`, `z ↦ x₀ + P z + w(z) e` is the local
  inverse of the hodograph map `y ↦ P(y - x₀) + u(y) e`, `C²` with derivative `(hodoCLM e ∇u)⁻¹`.
* `IsFlatChartData.divergence_field_eq_zero`: the hodograph equation `div Φ(∇w) = 0` for `t > 0`,
  proved pointwise by the chain rule: `Φ(∇w) = -2 P ∇u + (1 - |∇u|²) e` along the transform, whose
  divergence is `-2 Δu = 0`.
* `IsFlatChartData.exists_hodograph`: the bundled result on a half ball: `C¹` up to `t = 0`,
  `C²` inside, `|∇w - e| ≤ η`, the equation, and the conormal condition `Φ(∇w) · e = 0` on
  `t = 0` (which is `|∇u| = 1`).

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

@[expose] public noncomputable section

namespace EllipticBernoulli.Hodograph

variable {d : ℕ}

/-- The function `u` along the vertical line over `P z`: `s ↦ u(x₀ + P z + s e)`. -/
def lineFn (u : E d → ℝ) (x₀ e z : E d) (s : ℝ) : ℝ := u (x₀ + perpProj e z + s • e)

/-- **The partial hodograph transform**: for `z = x' + t e`, the first height `s ∈ [-ρ/2, ρ/2]`
above which `u(x₀ + x' + s e) > t`. -/
def hodograph (u : E d → ℝ) (x₀ e : E d) (ρ : ℝ) (z : E d) : ℝ :=
  levelInf (lineFn u x₀ e z) (-(ρ / 2)) (ρ / 2) ⟪z, e⟫

/-- The point `x₀ + P z + w(z) e` of the level set `{u = z · e}` over `P z`. -/
def hodographPt (u : E d → ℝ) (x₀ e : E d) (ρ : ℝ) (z : E d) : E d :=
  x₀ + perpProj e z + hodograph u x₀ e ρ z • e

/-- The hodograph map `y ↦ P(y - x₀) + u(y) e`. -/
def hodoMap (u : E d → ℝ) (x₀ e : E d) (y : E d) : E d := perpProj e (y - x₀) + u y • e

/-- The admissible region `{z | |P z| < ρ/2, 0 ≤ z · e < ρ/16}`. -/
def Adm (e : E d) (ρ : ℝ) : Set (E d) :=
  {z | ‖perpProj e z‖ < ρ / 2 ∧ 0 ≤ ⟪z, e⟫ ∧ ⟪z, e⟫ < ρ / 16}

end EllipticBernoulli.Hodograph

end

public section

namespace EllipticBernoulli

open Hodograph

variable {d : ℕ} {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d} {ρ : ℝ} {G : E d → E d}

theorem Hodograph.inner_line (he : ‖e‖ = 1) (z : E d) (s : ℝ) :
    ⟪perpProj e z + s • e, e⟫ = s := by
  rw [inner_add_left, inner_perpProj he, real_inner_smul_left, inner_self_of_norm he]; ring

theorem Hodograph.continuous_perpProj (e : E d) : Continuous (perpProj e) := by
  have : perpProj e = fun z ↦ perpCLM e z := funext fun z ↦ (perpCLM_apply e z).symm
  rw [this]; exact (perpCLM e).continuous

theorem Hodograph.hodograph_eq_inner (he : ‖e‖ = 1) (z : E d) :
    hodograph u x₀ e ρ z = ⟪hodographPt u x₀ e ρ z - x₀, e⟫ := by
  rw [hodographPt, show x₀ + perpProj e z + hodograph u x₀ e ρ z • e - x₀ =
    perpProj e z + hodograph u x₀ e ρ z • e by abel, inner_line he]

theorem Hodograph.perpProj_hodoMap (he : ‖e‖ = 1) (y : E d) :
    perpProj e (hodoMap u x₀ e y) = perpProj e (y - x₀) := by
  rw [hodoMap, perpProj_add_smul he, perpProj_perpProj he]

theorem Hodograph.inner_hodoMap (he : ‖e‖ = 1) (y : E d) : ⟪hodoMap u x₀ e y, e⟫ = u y := by
  rw [hodoMap, inner_line he]

namespace IsFlatChartData

variable (H : IsFlatChartData U u x₀ e ρ G)
include H

theorem line_mem_ball {z : E d} {s : ℝ} (hz : ‖perpProj e z‖ < ρ / 2) (hs : |s| ≤ ρ / 2) :
    x₀ + perpProj e z + s • e ∈ ball x₀ ρ := by
  have he := H.norm_e
  rw [mem_ball, dist_eq_norm,
    show x₀ + perpProj e z + s • e - x₀ = perpProj e z + s • e by abel]
  have h := norm_add_sq_real (perpProj e z) (s • e)
  rw [real_inner_smul_right, inner_perpProj he, norm_smul, he, Real.norm_eq_abs] at h
  have h2 : ‖perpProj e z + s • e‖ ^ 2 < ρ ^ 2 := by
    rw [h]
    have h1 : ‖perpProj e z‖ ^ 2 < (ρ / 2) ^ 2 :=
      pow_lt_pow_left₀ hz (norm_nonneg _) (by norm_num)
    have h3 : |s| ^ 2 ≤ (ρ / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg s) hs 2
    nlinarith [H.pos]
  exact lt_of_pow_lt_pow_left₀ 2 H.pos.le h2

theorem continuousOn_lineFn {z : E d} (hz : ‖perpProj e z‖ < ρ / 2) :
    ContinuousOn (lineFn u x₀ e z) (Icc (-(ρ / 2)) (ρ / 2)) :=
  H.continuousOn.comp (by fun_prop : Continuous fun s : ℝ ↦ x₀ + perpProj e z + s • e).continuousOn
    fun _ hs ↦ H.ball_subset (H.line_mem_ball hz (abs_le.2 hs))

theorem isGrowing {z : E d} (hz : ‖perpProj e z‖ < ρ / 2) :
    IsGrowing (lineFn u x₀ e z) (-(ρ / 2)) (ρ / 2) := by
  refine isGrowing_of_hasDerivAt (φ' := fun s ↦ ⟪∇ u (x₀ + perpProj e z + s • e), e⟫)
    (H.continuousOn_lineFn hz) fun s hs hpos ↦ ?_
  have hyB := H.line_mem_ball hz (abs_le.2 hs)
  have hyP : x₀ + perpProj e z + s • e ∈ posSet u U := ⟨H.ball_subset hyB, hpos⟩
  have hdiff : DifferentiableAt ℝ u (x₀ + perpProj e z + s • e) :=
    (H.harmonic _ hyP).1.differentiableAt (by norm_num)
  refine ⟨hasDerivAt_line hdiff, ?_⟩
  rw [← H.G_eq _ ⟨hyP, hyB⟩]
  exact H.inner_G _ ⟨subset_closure hyP, hyB⟩

theorem lineFn_eq_zero {z : E d} {s : ℝ} (hz : ‖perpProj e z‖ < ρ / 2) (hs : |s| ≤ ρ / 2)
    (hs4 : s ≤ -(ρ / 4)) : lineFn u x₀ e z s = 0 := by
  refine H.eq_zero _ (H.line_mem_ball hz hs) ?_
  rw [show x₀ + perpProj e z + s • e - x₀ = perpProj e z + s • e by abel, inner_line H.norm_e]
  exact hs4

theorem lineFn_pos {z : E d} {s : ℝ} (hz : ‖perpProj e z‖ < ρ / 2) (hs : |s| ≤ ρ / 2)
    (hs4 : ρ / 4 ≤ s) : 0 < lineFn u x₀ e z s := by
  refine H.pos_of_le _ (H.line_mem_ball hz hs) ?_
  rw [show x₀ + perpProj e z + s • e - x₀ = perpProj e z + s • e by abel, inner_line H.norm_e]
  exact hs4

theorem lineFn_ge {z : E d} (hz : ‖perpProj e z‖ < ρ / 2) :
    ρ / 16 ≤ lineFn u x₀ e z (3 * ρ / 8) ∧ ρ / 16 ≤ lineFn u x₀ e z (ρ / 2) := by
  have hρ := H.pos
  have hg := H.isGrowing hz
  have h1 := hg (ρ / 4) (3 * ρ / 8) (by linarith) (by linarith) (by linarith)
    (H.lineFn_pos hz (by rw [abs_le]; constructor <;> linarith) le_rfl)
  have h1' : ρ / 16 ≤ lineFn u x₀ e z (3 * ρ / 8) := by
    have := H.lineFn_pos (z := z) (s := ρ / 4) hz (by rw [abs_le]; constructor <;> linarith) le_rfl
    linarith
  refine ⟨h1', ?_⟩
  have h2 := hg (3 * ρ / 8) (ρ / 2) (by linarith) (by linarith) le_rfl (by linarith)
  linarith

variable {z : E d} (hz : z ∈ Adm e ρ)
include hz

theorem lt_lineFn_half : ⟪z, e⟫ < lineFn u x₀ e z (ρ / 2) :=
  hz.2.2.trans_le (H.lineFn_ge hz.1).2

theorem lt_lineFn {s : ℝ} (hs : hodograph u x₀ e ρ z < s) (hs2 : s ≤ ρ / 2) :
    ⟪z, e⟫ < lineFn u x₀ e z s :=
  lt_apply_of_levelInf_lt (by linarith [H.pos]) hz.2.1 (H.lt_lineFn_half hz) (H.isGrowing hz.1)
    hs2 hs

theorem hodograph_mem : -(ρ / 4) ≤ hodograph u x₀ e ρ z ∧ hodograph u x₀ e ρ z ≤ 3 * ρ / 8 := by
  have hρ := H.pos
  constructor
  · by_contra hlt
    push Not at hlt
    have := H.lt_lineFn hz hlt (by linarith)
    rw [H.lineFn_eq_zero hz.1 (by rw [abs_le]; constructor <;> linarith) le_rfl] at this
    linarith [hz.2.1]
  · exact levelInf_le ⟨by linarith, by linarith⟩ (hz.2.2.trans_le (H.lineFn_ge hz.1).1)

theorem abs_hodograph_le : |hodograph u x₀ e ρ z| ≤ ρ / 2 := by
  have := H.hodograph_mem hz
  rw [abs_le]; constructor <;> linarith [H.pos]

theorem apply_hodographPt : u (hodographPt u x₀ e ρ z) = ⟪z, e⟫ :=
  apply_levelInf (by linarith [H.pos]) hz.2.1 (H.lt_lineFn_half hz) (H.isGrowing hz.1)
    (H.continuousOn_lineFn hz.1)
    ((H.lineFn_eq_zero hz.1 (by rw [abs_neg, abs_of_pos (by linarith [H.pos])])
      (by linarith [H.pos])).le.trans hz.2.1)

theorem hodographPt_mem_ball : hodographPt u x₀ e ρ z ∈ ball x₀ ρ :=
  H.line_mem_ball hz.1 (H.abs_hodograph_le hz)

theorem hodographPt_mem_closure : hodographPt u x₀ e ρ z ∈ closure (posSet u U) := by
  have hρ := H.pos
  have hw := H.hodograph_mem hz
  have hT : Tendsto (fun s : ℝ ↦ x₀ + perpProj e z + s • e) (𝓝[>] (hodograph u x₀ e ρ z))
      (𝓝 (hodographPt u x₀ e ρ z)) :=
    ((by fun_prop : Continuous fun s : ℝ ↦ x₀ + perpProj e z + s • e).tendsto _).mono_left
      nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hT ?_
  filter_upwards [Ioo_mem_nhdsGT (show hodograph u x₀ e ρ z < ρ / 2 by linarith)] with s hs
  have hsabs : |s| ≤ ρ / 2 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
  exact ⟨H.ball_subset (H.line_mem_ball hz.1 hsabs),
    hz.2.1.trans_lt (H.lt_lineFn hz hs.1 hs.2.le)⟩

theorem hodographPt_mem_posSet (ht : 0 < ⟪z, e⟫) : hodographPt u x₀ e ρ z ∈ posSet u U :=
  ⟨H.ball_subset (H.hodographPt_mem_ball hz), (H.apply_hodographPt hz).symm ▸ ht⟩

theorem hodographPt_mem_freeBoundary (ht : ⟪z, e⟫ = 0) :
    hodographPt u x₀ e ρ z ∈ freeBoundary u U := by
  have hnot : hodographPt u x₀ e ρ z ∉ posSet u U := fun h ↦ by
    have := h.2; rw [H.apply_hodographPt hz, ht] at this; exact lt_irrefl _ this
  exact ⟨⟨H.hodographPt_mem_closure hz, fun hint ↦ hnot (interior_subset hint)⟩,
    H.ball_subset (H.hodographPt_mem_ball hz)⟩

theorem hodoMap_hodographPt : hodoMap u x₀ e (hodographPt u x₀ e ρ z) = z := by
  have he := H.norm_e
  rw [hodoMap, H.apply_hodographPt hz, hodographPt,
    show x₀ + perpProj e z + hodograph u x₀ e ρ z • e - x₀ =
      perpProj e z + hodograph u x₀ e ρ z • e by abel,
    perpProj_add_smul he, perpProj_perpProj he, perpProj_add_inner_smul]

omit hz in
/-- The transform inverts the hodograph map near the free boundary. -/
theorem hodographPt_hodoMap {y : E d} (hy : ‖perpProj e (y - x₀)‖ < ρ / 2)
    (hys : |⟪y - x₀, e⟫| ≤ ρ / 2) (hpos : 0 < u y) (hsmall : u y < ρ / 16) :
    hodographPt u x₀ e ρ (hodoMap u x₀ e y) = y := by
  have he := H.norm_e
  have hρ := H.pos
  set z := hodoMap u x₀ e y with hzdef
  have hPz : perpProj e z = perpProj e (y - x₀) := perpProj_hodoMap he y
  have hzt : ⟪z, e⟫ = u y := inner_hodoMap he y
  have hzA : z ∈ Adm e ρ := ⟨hPz ▸ hy, hzt ▸ hpos.le, hzt ▸ hsmall⟩
  have hline : lineFn u x₀ e z ⟪y - x₀, e⟫ = ⟪z, e⟫ := by
    rw [lineFn, hPz, hzt, add_assoc, perpProj_add_inner_smul, add_sub_cancel]
  have heq := eq_levelInf_of_apply_eq (by linarith) hzA.2.1 (H.lt_lineFn_half hzA)
    (H.isGrowing hzA.1) (H.continuousOn_lineFn hzA.1)
    ((H.lineFn_eq_zero hzA.1 (by rw [abs_neg, abs_of_pos (by linarith)])
      (by linarith)).le.trans hzA.2.1) (hzt ▸ hpos) (abs_le.1 hys) hline
  have heq' : hodograph u x₀ e ρ z = ⟪y - x₀, e⟫ := heq.symm
  rw [hodographPt, heq', hPz, add_assoc, perpProj_add_inner_smul, add_sub_cancel]

end IsFlatChartData

end EllipticBernoulli
