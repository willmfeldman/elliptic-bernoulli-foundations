/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import EllipticBernoulli.Common.Calculus
import EllipticBernoulli.Harmonic.GradientEstimate
import EllipticBernoulli.Harmonic.StrongMax
import EllipticBernoulli.Viscosity.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Interior gradient maximum of a supersolution

This is the rigidity step of the blow-up proof of the Alt–Caffarelli gradient bound
(Alt–Caffarelli, Remark 6.4, made uniform over the class of classical solutions). A continuous
`v ≥ 0` on
`E d` that is harmonic in `{v > 0}` and a viscosity supersolution with `Q ≡ 1` cannot have
`sup_{v > 0} ‖∇v‖ = ℓ₀ > 1` attained at an interior point of `{v > 0}`.

## Main results

* `false_of_isViscSuper_of_norm_gradient_attained`.

## Proof

Say the supremum `ℓ₀` is attained at `0`, and let `e = ∇v(0)/ℓ₀`.
1. `h = ⟪∇v, e⟫` is harmonic in `{v > 0}` (`HarmonicOnNhd.fderiv_apply`), `h ≤ ℓ₀` there and
   `h(0) = ℓ₀`. On the component `Ω` of `{v > 0}` containing `0`, the strong maximum principle
   (`HarmonicOnNhd.eqOn_of_isMaxOn`) gives `h ≡ ℓ₀`, and then `‖∇v − ℓ₀ e‖² ≤ 0`, so
   `∇v ≡ ℓ₀ e` and `v(z) = ℓ₀⟪e, z⟫ + v(0)` on `Ω`.
2. `Ω` is the half-space `H = {ℓ₀⟪e, z⟫ + v(0) > 0}`: `Ω ⊆ H`, and `Ω` is relatively closed in the
   connected set `H` (at a point of `H ∩ closure Ω`, `v > 0` by continuity, and a small ball
   around it joins the component).
3. At `p = −(v(0)/ℓ₀) e` we get `v(p) = 0`. The test function `φ = ℓ' t + t²`, `t = ⟪e, · − p⟫`,
   `ℓ' = (1 + ℓ₀)/2`, touches `v` from below at `p`, with `Δφ = 2 > 0` and `‖∇φ(p)‖ = ℓ' > 1`.
   This contradicts the supersolution property.

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The Laplacian of an affine function `y ↦ ⟪e, y⟫ + b` vanishes. -/
private theorem laplacian_inner_add (e : E d) (b : ℝ) (x : E d) :
    Δ (fun y ↦ ⟪e, y⟫ + b) x = 0 := by
  have hf : fderiv ℝ (fun y : E d ↦ ⟪e, y⟫ + b) = fun _ ↦ (innerSL ℝ e : E d →L[ℝ] ℝ) := by
    funext y
    exact ((innerSL ℝ e).hasFDerivAt.add_const b).fderiv
  rw [laplacian_eq_sum_fderiv_fderiv, hf]
  simp

/-- **Half-space rigidity.** Let `v ≥ 0` be continuous on `E d`, harmonic at each point of
`{v > 0}`, and a viscosity supersolution with `Q ≡ 1` on every ball `B_R(0)`. If `‖∇v‖ ≤ ℓ₀` on
`{v > 0}` for some `ℓ₀ > 1`, the bound cannot be attained at a point of `{v > 0}` (placed at
`0`). -/
theorem false_of_isViscSuper_of_norm_gradient_attained {v : E d → ℝ} (hvc : Continuous v)
    (hv0 : ∀ z, 0 ≤ v z) (hsuper : ∀ R, 0 < R → IsViscSuper (ball (0 : E d) R) (fun _ ↦ 1) v)
    (hharm : ∀ z, 0 < v z → HarmonicAt v z) {ℓ₀ : ℝ} (hℓ₀ : 1 < ℓ₀)
    (hgrad : ∀ z, 0 < v z → ‖∇ v z‖ ≤ ℓ₀) (hpos0 : 0 < v 0) (hgrad0 : ℓ₀ ≤ ‖∇ v 0‖) :
    False := by
  have hℓpos : 0 < ℓ₀ := by linarith
  set P : Set (E d) := {z | 0 < v z} with hP
  have hPo : IsOpen P := isOpen_lt continuous_const hvc
  have hPh : HarmonicOnNhd v P := fun z hz ↦ hharm z hz
  have hdiff : ∀ z ∈ P, DifferentiableAt ℝ v z := fun z hz ↦
    (hharm z hz).1.differentiableAt (by norm_num)
  -- the direction `e` of the maximal gradient
  have hg0 : ‖∇ v 0‖ = ℓ₀ := le_antisymm (hgrad 0 hpos0) hgrad0
  set e : E d := ℓ₀⁻¹ • ∇ v 0 with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, hg0, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hℓpos),
      inv_mul_cancel₀ hℓpos.ne']
  have hgv0 : ∇ v 0 = ℓ₀ • e := by
    rw [he, smul_smul, mul_inv_cancel₀ hℓpos.ne', one_smul]
  -- Step 1: `h = ⟪∇v, e⟫` is constant `= ℓ₀` on the component `Ω`
  set h : E d → ℝ := fun z ↦ fderiv ℝ v z e with hh
  have hhh : HarmonicOnNhd h P := HarmonicOnNhd.fderiv_apply hPo hPh e
  have hh_eq : ∀ z, h z = ⟪∇ v z, e⟫ := fun z ↦ fderiv_apply_eq_inner_gradient v z e
  have hh_le : ∀ z ∈ P, h z ≤ ℓ₀ := fun z hz ↦ by
    rw [hh_eq]
    calc ⟪∇ v z, e⟫ ≤ ‖∇ v z‖ * ‖e‖ := real_inner_le_norm _ _
      _ ≤ ℓ₀ := by rw [hen, mul_one]; exact hgrad z hz
  have hh0 : h 0 = ℓ₀ := by
    rw [hh_eq, hgv0, real_inner_smul_left, real_inner_self_eq_norm_sq, hen]; ring
  set Ω : Set (E d) := connectedComponentIn P 0 with hΩ
  have hΩo : IsOpen Ω := hPo.connectedComponentIn
  have hΩc : IsPreconnected Ω := isPreconnected_connectedComponentIn
  have hΩP : Ω ⊆ P := connectedComponentIn_subset P 0
  have h0Ω : (0 : E d) ∈ Ω := mem_connectedComponentIn hpos0
  have hhconst : ∀ z ∈ Ω, h z = ℓ₀ := by
    intro z hz
    have := HarmonicOnNhd.eqOn_of_isMaxOn hΩo hΩc (hhh.mono hΩP) h0Ω
      (fun y hy ↦ by rw [mem_setOf_eq, hh0]; exact hh_le y (hΩP hy)) hz
    rw [this, hh0]
  have hgradΩ : ∀ z ∈ Ω, ∇ v z = ℓ₀ • e := by
    intro z hz
    have hi : ⟪∇ v z, e⟫ = ℓ₀ := by rw [← hh_eq]; exact hhconst z hz
    have hn := hgrad z (hΩP hz)
    have hsq : ‖∇ v z - ℓ₀ • e‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, real_inner_smul_right, hi, norm_smul, Real.norm_eq_abs,
        abs_of_pos hℓpos, hen]
      linarith [pow_le_pow_left₀ (norm_nonneg (∇ v z)) hn 2]
    have : ‖∇ v z - ℓ₀ • e‖ = 0 := (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hsq (sq_nonneg _))
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  -- `v` is affine on `Ω`
  set A : E d →L[ℝ] ℝ := innerSL ℝ e with hA
  set aff : E d → ℝ := fun z ↦ ℓ₀ * A z + v 0 with haff
  have haffd : ∀ z, HasFDerivAt aff (ℓ₀ • A) z := fun z ↦
    (A.hasFDerivAt.const_mul ℓ₀).add_const _
  have haffc : Continuous aff := by
    rw [haff]; exact (continuous_const.mul A.continuous).add continuous_const
  have hvaff : EqOn v aff Ω := by
    refine hΩo.eqOn_of_fderiv_eq hΩc (fun z hz ↦ (hdiff z (hΩP hz)).differentiableWithinAt)
      (fun z _ ↦ (haffd z).differentiableAt.differentiableWithinAt) (fun z hz ↦ ?_) h0Ω
      (by simp [haff])
    rw [(haffd z).fderiv]
    ext w
    rw [fderiv_apply_eq_inner_gradient, hgradΩ z hz, real_inner_smul_left,
      ContinuousLinearMap.smul_apply, hA, innerSL_apply_apply, smul_eq_mul, real_inner_comm]
  -- Step 2: `Ω` is the half-space `H`
  set H : Set (E d) := {z | 0 < aff z} with hH
  have hHc : IsPreconnected H := by
    have : H = {z | -v 0 < (ℓ₀ • A) z} := by
      ext z; simp only [hH, haff, mem_setOf_eq, ContinuousLinearMap.smul_apply, smul_eq_mul]
      constructor <;> intro h <;> linarith
    rw [this]
    exact (convex_halfSpace_gt (ℓ₀ • A).isLinear _).isPreconnected
  have hΩH : Ω ⊆ H := fun z hz ↦ by
    have := hΩP hz
    simp only [hP, mem_setOf_eq] at this
    rwa [hvaff hz] at this
  have hHΩ : H ⊆ Ω := by
    refine hHc.subset_of_closure_inter_subset hΩo ⟨0, hΩH h0Ω, h0Ω⟩ ?_
    rintro z ⟨hzcl, hzH⟩
    have hvz : 0 < v z := by
      rw [hvaff.closure hvc haffc hzcl]; exact hzH
    obtain ⟨ε, hε, hεP⟩ := Metric.isOpen_iff.1 hPo z hvz
    obtain ⟨w, hwΩ, hwB⟩ := Metric.mem_closure_iff.1 hzcl ε hε
    have hsub : ball z ε ⊆ connectedComponentIn P w :=
      (convex_ball z ε).isPreconnected.subset_connectedComponentIn
        (mem_ball.2 (by rwa [dist_comm])) hεP
    rw [← connectedComponentIn_eq hwΩ] at hsub
    exact hsub (mem_ball_self hε)
  have hvH : ∀ z, 0 < aff z → v z = aff z := fun z hz ↦ hvaff (hHΩ hz)
  -- Step 3: the boundary point `p` and the test function
  set p : E d := -(v 0 / ℓ₀) • e with hp
  have haff_eq : ∀ z, aff z = ℓ₀ * ⟪e, z - p⟫ := by
    intro z
    have : ⟪e, z - p⟫ = A z + v 0 / ℓ₀ := by
      rw [inner_sub_right, hp, real_inner_smul_right, real_inner_self_eq_norm_sq, hen, hA,
        innerSL_apply_apply]
      ring
    rw [this, haff]; field_simp
  have hvp : v p = 0 := by
    have ht : Tendsto (fun t : ℝ ↦ v (p + t • e)) (𝓝[>] 0) (𝓝 (v p)) := by
      have : Tendsto (fun t : ℝ ↦ p + t • e) (𝓝 0) (𝓝 p) :=
        (continuous_const.add (continuous_id.smul continuous_const) :
          Continuous fun t : ℝ ↦ p + t • e).tendsto' 0 p (by
          change p + (0 : ℝ) • e = p; rw [zero_smul, add_zero])
      exact (hvc.tendsto p).comp (this.mono_left nhdsWithin_le_nhds)
    have hinner : ∀ t : ℝ, ⟪e, p + t • e - p⟫ = t := fun t ↦ by
      rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hen]; ring
    have ht' : Tendsto (fun t : ℝ ↦ v (p + t • e)) (𝓝[>] 0) (𝓝 0) := by
      have hlin : Tendsto (fun t : ℝ ↦ ℓ₀ * t) (𝓝[>] 0) (𝓝 0) := by
        have := ((continuous_const_mul ℓ₀).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      refine hlin.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t (htpos : 0 < t)
      rw [hvH _ (by rw [haff_eq, hinner]; positivity), haff_eq, hinner]
    exact tendsto_nhds_unique ht ht'
  set ℓ' : ℝ := (1 + ℓ₀) / 2 with hℓ'
  set T : E d → ℝ := fun y ↦ ⟪e, y⟫ + (-⟪e, p⟫) with hT
  have hTeq : ∀ y, T y = ⟪e, y - p⟫ := fun y ↦ by rw [hT, inner_sub_right]; ring
  set f : ℝ → ℝ := fun s ↦ ℓ' * s + s ^ 2 with hf
  set φ : E d → ℝ := fun y ↦ f (T y) with hφ
  have hTd : ∀ y, HasFDerivAt T A y := fun y ↦ by
    have := (innerSL ℝ e).hasFDerivAt.add_const (-⟪e, p⟫) (x := y)
    simpa [hT, hA] using this
  have hTc : ContDiff ℝ ∞ T := by
    rw [hT]; exact (contDiff_const.inner ℝ contDiff_id).add contDiff_const
  have hfc : ContDiff ℝ ∞ f := by rw [hf]; fun_prop
  have hφc : ContDiff ℝ ∞ φ := hfc.comp hTc
  have hTp : T p = 0 := by rw [hTeq, sub_self, inner_zero_right]
  have hfd : ∀ s, HasDerivAt f (ℓ' + 2 * s) s := fun s ↦ by
    have := ((hasDerivAt_id s).const_mul ℓ').add ((hasDerivAt_id s).pow 2)
    convert this using 1; simp
  have hdf : deriv f = fun s ↦ ℓ' + 2 * s := funext fun s ↦ (hfd s).deriv
  have hddf : deriv (deriv f) = fun _ ↦ 2 := by
    rw [hdf]; funext s
    simp
  have hgradT : ∇ T p = e := by
    rw [gradient, (hTd p).fderiv, hA]
    exact (InnerProductSpace.toDual ℝ (E d)).symm_apply_apply e
  have hlap : Δ φ p = 2 := by
    have h := laplacian_comp (g := T) (x := p) (hfc.contDiffAt.of_le (by norm_cast))
      (hTc.contDiffAt.of_le (by norm_cast))
    have hΔT : Δ T p = 0 := laplacian_inner_add e _ p
    rw [hddf, hdf, hgradT, hen, hΔT] at h
    simpa [hφ] using h
  have hφgrad : ‖∇ φ p‖ = ℓ' := by
    have hd : HasFDerivAt φ ((ℓ' + 2 * T p) • A) p := (hfd (T p)).comp_hasFDerivAt p (hTd p)
    rw [norm_gradient_eq_norm_fderiv, hd.fderiv, hTp, mul_zero, add_zero, norm_smul, hA,
      innerSL_apply_norm, hen, mul_one, Real.norm_eq_abs, abs_of_pos (by rw [hℓ']; linarith)]
  -- `φ` touches `v` from below at `p`
  set R : ℝ := ‖p‖ + 1 with hR
  have hpR : p ∈ ball (0 : E d) R := mem_ball_zero_iff.2 (by rw [hR]; linarith)
  set δ : ℝ := ℓ₀ - ℓ' with hδ
  have hδpos : 0 < δ := by rw [hδ, hℓ']; linarith
  have htouch : TouchesBelow φ v (ball (0 : E d) R) p := by
    refine ⟨hpR, by simp [hφ, hTp, hf, hvp], ?_⟩
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds p hδpos)] with y hy
    have hty : |T y| < δ := by
      rw [hTeq]
      calc |⟪e, y - p⟫| ≤ ‖e‖ * ‖y - p‖ := abs_real_inner_le_norm _ _
        _ < δ := by rw [hen, one_mul, ← dist_eq_norm]; exact mem_ball.1 hy
    have hφy : φ y = T y * (ℓ' + T y) := by simp only [hφ, hf]; ring
    rcases le_or_gt (T y) 0 with ht | ht
    · rw [hφy]
      have : 0 ≤ ℓ' + T y := by
        have := (abs_lt.1 hty).1
        rw [hδ, hℓ'] at this; rw [hℓ']; linarith
      exact (mul_nonpos_of_nonpos_of_nonneg ht this).trans (hv0 y)
    · have haffy : aff y = ℓ₀ * T y := by rw [haff_eq, hTeq]
      rw [hvH y (by rw [haffy]; positivity), haffy, hφy]
      have : T y < δ := (abs_lt.1 hty).2
      have h2 : T y * T y < (ℓ₀ - ℓ') * T y := mul_lt_mul_of_pos_right this ht
      linarith
  have hR0 : 0 < R := add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos
  rcases (hsuper R hR0).2.2 φ hφc p hpR htouch with h | ⟨-, h⟩
  · rw [hlap] at h; norm_num at h
  · rw [hφgrad, hℓ'] at h; linarith

end EllipticBernoulli
