/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.TwoPhase
import EllipticBernoulli.Classical.OneDim
import EllipticBernoulli.TwoPhase.FreeBoundaryCondition
import EllipticBernoulli.TwoPhase.Regularity
import EllipticBernoulli.Viscosity.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Global two-phase minimizers in dimension one

A Lipschitz local minimizer `u` of
`J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝ` that changes sign is a two-plane function
`a (x e + c)⁺ - b (x e + c)⁻` with `e = ±1`, `a, b > 0` and `a² - b² = 1`.

* `twoPhaseClassification_one`: the statement, in `E 1`.

## Proof

Write `g(s) = u(s e₁)`. By `IsLocalEnergyMinimizer.harmonicOnNhd_posSet`, `…_negSet` and
`…_interior_nonpos`, `u` is harmonic on `{u > 0}`, on `{u < 0}` and on the interior of `{u ≤ 0}`;
in dimension one, harmonic on a connected open set means affine there, so `g` is affine on every
open interval contained in `{g > 0}`, in `{g < 0}`, or in `{g ≤ 0}`.
* An affine function that is `≤ 0` at both ends of an interval is `≤ 0` inside, so `{g > 0}` and
  `{g < 0}` have no bounded components (`not_posBump`).
* Pick `x₋ < x₊` with `g(x₋) < 0 < g(x₊)` (otherwise reflect `s ↦ -s`), let `c₁` be the last zero
  of `g` in `[x₋, x₊]` and `c₂` the first. Then `g > 0` on `(c₁, ∞)`, `g < 0` on `(-∞, c₂)` and
  `g ≤ 0` on `(c₂, c₁)`.
* So `g` is affine on `(c₁, ∞)` and on `(-∞, c₁)`, vanishing at `c₁` and at `c₂`; since `g(x₋) < 0`,
  `c₁ = c₂`, and `g(s) = a (s - c)⁺ - b (s - c)⁻` with `a, b > 0`.
Finally `a² - b² = 1` by `sq_sub_sq_eq_one_of_isLocalEnergyMinimizer_twoPlane`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Laplacian NNReal

namespace EllipticBernoulli

/-! ### Affine on phases -/

/-- `g` is affine on every open connected set on which `p ∘ g` holds. -/
private def AffineOn (g : ℝ → ℝ) (p : ℝ → Prop) : Prop :=
  ∀ S : Set ℝ, IsOpen S → IsPreconnected S → (∀ s ∈ S, p (g s)) →
    ∃ m k : ℝ, ∀ s ∈ S, g s = m * s + k

private theorem AffineOn.comp_neg {g : ℝ → ℝ} {p : ℝ → Prop} (h : AffineOn g p) :
    AffineOn (fun s ↦ g (-s)) p := by
  intro S hS hSc hp
  have hS' : IsOpen ((fun s : ℝ ↦ -s) '' S) := (Homeomorph.neg ℝ).isOpenMap S hS
  obtain ⟨m, k, hmk⟩ := h _ hS' (hSc.image _ continuous_neg.continuousOn)
    (by rintro _ ⟨s, hs, rfl⟩; exact hp s hs)
  exact ⟨-m, k, fun s hs ↦ by simp only; rw [hmk (-s) ⟨s, hs, rfl⟩]; ring⟩

private theorem AffineOn.neg {g : ℝ → ℝ} (h : AffineOn g (· < 0)) :
    AffineOn (fun s ↦ -g s) (0 < ·) := by
  intro S hS hSc hp
  obtain ⟨m, k, hmk⟩ := h S hS hSc fun s hs ↦ neg_pos.1 (hp s hs)
  exact ⟨-m, -k, fun s hs ↦ by simp only; rw [hmk s hs]; ring⟩

/-- A continuous function affine on `Ioo α β` is affine on `Icc α β`. -/
private theorem eqOn_Icc_of_eqOn_Ioo {g : ℝ → ℝ} (hg : Continuous g) {α β m k : ℝ}
    (hαβ : α < β) (h : ∀ s ∈ Ioo α β, g s = m * s + k) : ∀ s ∈ Icc α β, g s = m * s + k := by
  have hcl : IsClosed {s | g s = m * s + k} :=
    isClosed_eq hg (continuous_const.mul continuous_id |>.add continuous_const)
  intro s hs
  rw [← closure_Ioo hαβ.ne] at hs
  exact (hcl.closure_subset_iff.2 h) hs

/-- **No positive bumps.** If `g` is affine on every interval of positivity, then `g` cannot be
`≤ 0` at `α`, positive at `z` and `≤ 0` at `β` with `α < z < β`. -/
private theorem not_posBump {g : ℝ → ℝ} (hg : Continuous g) (hP : AffineOn g (0 < ·))
    {α z β : ℝ} (hαz : α < z) (hzβ : z < β) (hα : g α ≤ 0) (hz : 0 < g z) (hβ : g β ≤ 0) :
    False := by
  -- the last nonpositive point before `z`
  set A := {s ∈ Icc α z | g s ≤ 0} with hA
  have hAc : IsClosed A := isClosed_Icc.inter (isClosed_le hg continuous_const)
  have hAb : BddAbove A := ⟨z, fun s hs ↦ hs.1.2⟩
  have hαA : α ∈ A := ⟨⟨le_rfl, hαz.le⟩, hα⟩
  set α' := sSup A
  have hα'A : α' ∈ A := hAc.csSup_mem ⟨α, hαA⟩ hAb
  have hα'z : α' < z := lt_of_le_of_ne hα'A.1.2 fun h ↦ by
    have := hα'A.2; rw [h] at this; linarith
  have hpos1 : ∀ s ∈ Ioc α' z, 0 < g s := fun s hs ↦ by
    by_contra h
    exact absurd (le_csSup hAb ⟨⟨hα'A.1.1.trans hs.1.le, hs.2⟩, not_lt.1 h⟩) (not_le.2 hs.1)
  -- the first nonpositive point after `z`
  set B := {s ∈ Icc z β | g s ≤ 0} with hB
  have hBc : IsClosed B := isClosed_Icc.inter (isClosed_le hg continuous_const)
  have hBb : BddBelow B := ⟨z, fun s hs ↦ hs.1.1⟩
  have hβB : β ∈ B := ⟨⟨hzβ.le, le_rfl⟩, hβ⟩
  set β' := sInf B
  have hβ'B : β' ∈ B := hBc.csInf_mem ⟨β, hβB⟩ hBb
  have hzβ' : z < β' := lt_of_le_of_ne hβ'B.1.1 fun h ↦ by
    have := hβ'B.2; rw [← h] at this; linarith
  have hpos2 : ∀ s ∈ Ico z β', 0 < g s := fun s hs ↦ by
    by_contra h
    exact absurd (csInf_le hBb ⟨⟨hs.1, hs.2.le.trans hβ'B.1.2⟩, not_lt.1 h⟩) (not_le.2 hs.2)
  -- `g` is affine on `(α', β')`
  have hpos : ∀ s ∈ Ioo α' β', 0 < g s := fun s hs ↦ by
    rcases le_or_gt s z with h | h
    · exact hpos1 s ⟨hs.1, h⟩
    · exact hpos2 s ⟨h.le, hs.2⟩
  obtain ⟨m, k, hmk⟩ := hP _ isOpen_Ioo isPreconnected_Ioo hpos
  have hmk' := eqOn_Icc_of_eqOn_Ioo hg (hα'z.trans hzβ') hmk
  have h1 := hmk' α' ⟨le_rfl, (hα'z.trans hzβ').le⟩
  have h2 := hmk' β' ⟨(hα'z.trans hzβ').le, le_rfl⟩
  have h3 := hmk' z ⟨hα'z.le, hzβ'.le⟩
  have hga := hα'A.2
  have hgb := hβ'B.2
  have hid : (z - α') * g β' + (β' - z) * g α' = (β' - α') * g z := by
    rw [h1, h2, h3]; ring
  nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hα'z.le) hgb,
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hzβ'.le) hga,
    mul_pos (sub_pos.2 (hα'z.trans hzβ')) hz]

private theorem eqOn_closure {g : ℝ → ℝ} (hg : Continuous g) {S : Set ℝ} {m k : ℝ}
    (h : ∀ s ∈ S, g s = m * s + k) : ∀ s ∈ closure S, g s = m * s + k := by
  have hcl : IsClosed {s | g s = m * s + k} :=
    isClosed_eq hg (continuous_const.mul continuous_id |>.add continuous_const)
  exact fun s hs ↦ (hcl.closure_subset_iff.2 h) hs

/-- **The one-dimensional classification**, for a continuous `g : ℝ → ℝ` affine on the open
intervals contained in `{g > 0}`, in `{g < 0}` and in `{g ≤ 0}`, negative at `xm` and positive at
`xp > xm`: `g(s) = a (s - c)⁺ - b (s - c)⁻` with `a, b > 0`. -/
private theorem eq_profile_of_affineOn {g : ℝ → ℝ} (hg : Continuous g) (hP : AffineOn g (0 < ·))
    (hN : AffineOn g (· < 0)) (hZ : AffineOn g (· ≤ 0)) {xm xp : ℝ} (hlt : xm < xp)
    (hxm : g xm < 0) (hxp : 0 < g xp) :
    ∃ c a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ s, g s = a * max (s - c) 0 - b * max (-(s - c)) 0 := by
  have hgn : Continuous fun s ↦ -g s := hg.neg
  -- `c₁`: the last point of `[xm, xp]` where `g ≤ 0`
  set A := {s ∈ Icc xm xp | g s ≤ 0} with hA
  have hAc : IsClosed A := isClosed_Icc.inter (isClosed_le hg continuous_const)
  have hAb : BddAbove A := ⟨xp, fun s hs ↦ hs.1.2⟩
  set c₁ := sSup A
  have hc₁A : c₁ ∈ A := hAc.csSup_mem ⟨xm, ⟨le_rfl, hlt.le⟩, hxm.le⟩ hAb
  have hc₁x : c₁ < xp := lt_of_le_of_ne hc₁A.1.2 fun h ↦ by
    have := hc₁A.2; rw [h] at this; linarith
  have hpos1 : ∀ s ∈ Ioc c₁ xp, 0 < g s := fun s hs ↦ by
    by_contra h
    exact absurd (le_csSup hAb ⟨⟨hc₁A.1.1.trans hs.1.le, hs.2⟩, not_lt.1 h⟩) (not_le.2 hs.1)
  have hgc₁ : g c₁ = 0 := by
    refine le_antisymm hc₁A.2 (ge_of_tendsto (x := 𝓝[>] c₁)
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_)
    filter_upwards [Ioc_mem_nhdsGT hc₁x] with s hs using (hpos1 s hs).le
  -- `c₂`: the first point of `[xm, xp]` where `g ≥ 0`
  set B := {s ∈ Icc xm xp | 0 ≤ g s} with hB
  have hBc : IsClosed B := isClosed_Icc.inter (isClosed_le continuous_const hg)
  have hBb : BddBelow B := ⟨xm, fun s hs ↦ hs.1.1⟩
  set c₂ := sInf B
  have hc₂B : c₂ ∈ B := hBc.csInf_mem ⟨xp, ⟨hlt.le, le_rfl⟩, hxp.le⟩ hBb
  have hxc₂ : xm < c₂ := lt_of_le_of_ne hc₂B.1.1 fun h ↦ by
    have := hc₂B.2; rw [← h] at this; linarith
  have hneg1 : ∀ s ∈ Ico xm c₂, g s < 0 := fun s hs ↦ by
    by_contra h
    exact absurd (csInf_le hBb ⟨⟨hs.1, hs.2.le.trans hc₂B.1.2⟩, not_lt.1 h⟩) (not_le.2 hs.2)
  have hgc₂ : g c₂ = 0 := by
    refine le_antisymm (le_of_tendsto (x := 𝓝[<] c₂)
      (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_) hc₂B.2
    filter_upwards [Ico_mem_nhdsLT hxc₂] with s hs using (hneg1 s hs).le
  have hc₂c₁ : c₂ ≤ c₁ := csInf_le hBb ⟨hc₁A.1, hgc₁.ge⟩
  -- the sign pattern
  have hright : ∀ s, c₁ < s → 0 < g s := fun s hs ↦ by
    by_contra h
    rcases le_or_gt s xp with h' | h'
    · exact h (hpos1 s ⟨hs, h'⟩)
    · exact not_posBump hg hP hc₁x h' hc₁A.2 hxp (not_lt.1 h)
  have hleft : ∀ s, s < c₂ → g s < 0 := fun s hs ↦ by
    by_contra h
    rcases le_or_gt xm s with h' | h'
    · exact h (hneg1 s ⟨h', hs⟩)
    · exact not_posBump hgn hN.neg h' hxc₂ (by linarith [not_lt.1 h]) (by linarith)
        (by rw [hgc₂, neg_zero])
  have hmid : ∀ s, c₂ < s → s < c₁ → g s ≤ 0 := fun s hs1 hs2 ↦ by
    by_contra h
    exact not_posBump hg hP hs1 hs2 hgc₂.le (not_le.1 h) hgc₁.le
  have hnonpos : ∀ s ∈ Iio c₁, g s ≤ 0 := fun s hs ↦ by
    rcases lt_trichotomy s c₂ with h | h | h
    · exact (hleft s h).le
    · rw [h, hgc₂]
    · exact hmid s h hs
  -- `g` is affine on both sides of `c₁`
  obtain ⟨m₁, k₁, h₁⟩ := hP _ isOpen_Ioi isPreconnected_Ioi fun s hs ↦ hright s hs
  obtain ⟨m₂, k₂, h₂⟩ := hZ _ isOpen_Iio isPreconnected_Iio hnonpos
  have h₁' := eqOn_closure hg h₁
  have h₂' := eqOn_closure hg h₂
  rw [closure_Ioi] at h₁'
  rw [closure_Iio] at h₂'
  have hk₁ : k₁ = -(m₁ * c₁) := by have := h₁' c₁ (mem_Ici.2 le_rfl); linarith
  have hk₂ : k₂ = -(m₂ * c₁) := by have := h₂' c₁ (mem_Iic.2 le_rfl); linarith
  have ha : 0 < m₁ := by
    have := h₁' xp hc₁x.le
    rw [hk₁] at this
    nlinarith
  have hb : 0 < m₂ := by
    have := h₂' xm (hxc₂.trans_le hc₂c₁).le
    rw [hk₂] at this
    nlinarith [hxc₂.trans_le hc₂c₁]
  refine ⟨c₁, m₁, m₂, ha, hb, fun s ↦ ?_⟩
  rcases le_total c₁ s with h | h
  · rw [h₁' s h, hk₁, max_eq_left (sub_nonneg.2 h), max_eq_right (by linarith)]
    ring
  · rw [h₂' s h, hk₂, max_eq_right (sub_nonpos.2 h), max_eq_left (by linarith)]
    ring

/-! ### Harmonic functions on the line -/

/-- The unit vector of `E 1`. -/
private noncomputable def e₁ : E 1 := EuclideanSpace.single 0 1

private theorem norm_e₁ : ‖e₁‖ = 1 := by simp [e₁]

private theorem eq_smul_e₁ (x : E 1) : x = x 0 • e₁ := by
  ext i
  rw [Subsingleton.elim i 0]
  simp [e₁]

private theorem inner_e₁ (x : E 1) : inner ℝ x e₁ = x 0 := by
  simp [e₁, EuclideanSpace.inner_single_right]

/-- A function harmonic along `S e₁`, `S ⊆ ℝ` open and connected, is affine there. -/
private theorem affine_of_harmonicAt {u : E 1 → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hSc : IsPreconnected S) (hH : ∀ s ∈ S, HarmonicAt u (s • e₁)) :
    ∃ m k : ℝ, ∀ s ∈ S, u (s • e₁) = m * s + k := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨s₀, hs₀⟩
  · exact ⟨0, 0, by simp⟩
  have hι : ∀ s : ℝ, HasDerivAt (fun s : ℝ ↦ s • e₁) e₁ s := fun s ↦ by
    have := (hasDerivAt_id s).smul_const e₁
    rwa [one_smul] at this
  set h : ℝ → ℝ := fun s ↦ fderiv ℝ u (s • e₁) e₁ with hh
  have hd1 : ∀ s ∈ S, HasDerivAt (fun s ↦ u (s • e₁)) (h s) s := fun s hs ↦
    ((hH s hs).1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt s (hι s)
  have hd2 : ∀ s ∈ S, HasDerivAt h 0 s := fun s hs ↦ by
    have hD : DifferentiableAt ℝ (fderiv ℝ u) (s • e₁) :=
      ((hH s hs).1.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    have h1 : HasDerivAt (fun s : ℝ ↦ fderiv ℝ u (s • e₁))
        (fderiv ℝ (fderiv ℝ u) (s • e₁) e₁) s :=
      hD.hasFDerivAt.comp_hasDerivAt s (hι s)
    rw [fderiv_fderiv_eq_zero_of_one (hH s hs)] at h1
    have h2 := (ContinuousLinearMap.apply ℝ ℝ e₁).hasFDerivAt.comp_hasDerivAt s h1
    have h0 : ((ContinuousLinearMap.apply ℝ ℝ) e₁) ((0 : E 1 →L[ℝ] E 1 →L[ℝ] ℝ) e₁) = 0 := by
      simp
    rw [h0] at h2
    exact h2.congr_of_eventuallyEq (Eventually.of_forall fun r ↦ by simp [hh])
  have hconst : ∀ s ∈ S, h s = h s₀ := fun s hs ↦
    hS.is_const_of_deriv_eq_zero hSc (fun r hr ↦ (hd2 r hr).differentiableAt.differentiableWithinAt)
      (fun r hr ↦ (hd2 r hr).deriv) hs hs₀
  set φ : ℝ → ℝ := fun s ↦ u (s • e₁) - h s₀ * s with hφ
  have hd3 : ∀ s ∈ S, HasDerivAt φ 0 s := fun s hs ↦ by
    have := (hd1 s hs).sub ((hasDerivAt_id s).const_mul (h s₀))
    rw [hconst s hs, mul_one, sub_self] at this
    exact this.congr_of_eventuallyEq (Eventually.of_forall fun r ↦ by simp [hφ])
  have hconst' : ∀ s ∈ S, φ s = φ s₀ := fun s hs ↦
    hS.is_const_of_deriv_eq_zero hSc (fun r hr ↦ (hd3 r hr).differentiableAt.differentiableWithinAt)
      (fun r hr ↦ (hd3 r hr).deriv) hs hs₀
  refine ⟨h s₀, φ s₀, fun s hs ↦ ?_⟩
  have := hconst' s hs
  simp only [hφ] at this ⊢
  linarith

/-! ### The classification -/

/-- **Classification of global two-phase minimizers in dimension one.** A Lipschitz local minimizer
`u : E 1 → ℝ` of `J(v, B) = ∫_B |∇v|² + 1_{v > 0}` taking a positive and a negative value is
`x ↦ a (x·e + c)⁺ - b (x·e + c)⁻` with `‖e‖ = 1`, `a, b > 0` and `a² - b² = 1`. -/
public theorem twoPhaseClassification_one {u : E 1 → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hpos : ∃ x, 0 < u x)
    (hneg : ∃ x, u x < 0) :
    ∃ (e : E 1) (c a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = 1 ∧
      ∀ x, u x = twoPlane a b e c x := by
  set g : ℝ → ℝ := fun s ↦ u (s • e₁) with hgdef
  have hg : Continuous g := hu.continuous.comp (continuous_id.smul continuous_const)
  have hx : ∀ x, u x = g (x 0) := fun x ↦ by rw [hgdef]; simp only; rw [← eq_smul_e₁]
  have hcoord : Continuous fun x : E 1 ↦ x 0 := (EuclideanSpace.proj (0 : Fin 1)).continuous
  have hP : AffineOn g (0 < ·) := fun S hS hSc hp ↦
    affine_of_harmonicAt hS hSc fun s hs ↦ hmin.harmonicOnNhd_posSet hu _ (hp s hs)
  have hN : AffineOn g (· < 0) := fun S hS hSc hp ↦
    affine_of_harmonicAt hS hSc fun s hs ↦ hmin.harmonicOnNhd_negSet hu _ (hp s hs)
  have hZ : AffineOn g (· ≤ 0) := fun S hS hSc hp ↦
    affine_of_harmonicAt hS hSc fun s hs ↦ hmin.harmonicOnNhd_interior_nonpos hu _
      (mem_interior.2 ⟨{x | x 0 ∈ S}, fun x hx' ↦ by rw [mem_ofPred_eq, hx]; exact hp _ hx',
        hS.preimage hcoord, by simpa [e₁] using hs⟩)
  obtain ⟨xp, hxp⟩ := hpos
  obtain ⟨xm, hxm⟩ := hneg
  rw [hx] at hxp hxm
  have key : ∃ (e : E 1) (c a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧
      ∀ x, u x = twoPlane a b e c x := by
    rcases lt_or_gt_of_ne (show xm 0 ≠ xp 0 from fun h ↦ by rw [h] at hxm; linarith)
      with h | h
    · obtain ⟨c, a, b, ha, hb, hgab⟩ := eq_profile_of_affineOn hg hP hN hZ h hxm hxp
      refine ⟨e₁, -c, a, b, norm_e₁, ha, hb, fun x ↦ ?_⟩
      rw [hx x, hgab, twoPlane, inner_e₁, ← sub_eq_add_neg]
    · have hg' : Continuous fun s ↦ g (-s) := hg.comp continuous_neg
      obtain ⟨c, a, b, ha, hb, hgab⟩ := eq_profile_of_affineOn hg' hP.comp_neg hN.comp_neg
        hZ.comp_neg (neg_lt_neg h) (by simpa using hxm) (by simpa using hxp)
      refine ⟨-e₁, -c, a, b, by rw [norm_neg, norm_e₁], ha, hb, fun x ↦ ?_⟩
      have := hgab (-x 0)
      simp only [neg_neg] at this
      rw [hx x, this, twoPlane, inner_neg_right, inner_e₁]
      ring_nf
  obtain ⟨e, c, a, b, he, ha, hb, hux⟩ := key
  have hfun : u = twoPlane a b e c := funext hux
  rw [hfun] at hmin
  exact ⟨e, c, a, b, he, ha, hb,
    sq_sub_sq_eq_one_of_isLocalEnergyMinimizer_twoPlane he ha hb hmin, hux⟩

end EllipticBernoulli
