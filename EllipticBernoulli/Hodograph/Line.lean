/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# Level sets of functions of one variable with slope at least `1/2` where positive

The one-variable part of the partial hodograph transform. Along a vertical line through the
free boundary, a solution `φ(s) = u(x' + s e)` vanishes below the free boundary and increases with
slope at least `1/2` above it. For `t ≥ 0` the level `levelInf φ a b t` is the first `s ∈ [a, b]`
with `φ s > t`.

* `IsGrowing φ a b`: `φ s₂ ≥ φ s₁ + (s₂ - s₁)/2` whenever `a ≤ s₁ ≤ s₂ ≤ b` and `φ s₁ > 0`.
* `isGrowing_of_hasDerivAt`: a function continuous on `[a, b]` with derivative `≥ 1/2` at every
  point of `[a, b]` where it is positive is growing.
* `apply_levelInf`: `φ (levelInf φ a b t) = t` when `φ a ≤ t < φ b`.
* `lt_apply_of_levelInf_lt`, `apply_le_of_lt_levelInf`: `φ > t` above the level and `φ ≤ t` below.
* `eq_levelInf_of_apply_eq`: for `t > 0` the level is the unique solution of `φ s = t`.
-/

open Set Filter Topology

public section

namespace EllipticBernoulli.Hodograph

/-- The first level: `inf {s ∈ [a, b] | t < φ s}`. -/
@[expose] noncomputable def levelInf (φ : ℝ → ℝ) (a b t : ℝ) : ℝ := sInf {s ∈ Icc a b | t < φ s}

/-- `φ` grows with slope at least `1/2` on `[a, b]` from every point where it is positive. -/
@[expose] def IsGrowing (φ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ s₁ s₂, a ≤ s₁ → s₁ ≤ s₂ → s₂ ≤ b → 0 < φ s₁ → φ s₁ + (s₂ - s₁) / 2 ≤ φ s₂

variable {φ : ℝ → ℝ} {a b t s : ℝ}

/-- A function continuous on `[a, b]`, with derivative at least `1/2` at every point of `[a, b]`
where it is positive, is growing. -/
theorem isGrowing_of_hasDerivAt {φ' : ℝ → ℝ} (hc : ContinuousOn φ (Icc a b))
    (hd : ∀ s ∈ Icc a b, 0 < φ s → HasDerivAt φ (φ' s) s ∧ 1 / 2 ≤ φ' s) :
    IsGrowing φ a b := by
  intro s₁ s₂ ha h12 h2b hpos
  set S : Set ℝ := {σ | φ s₁ + (σ - s₁) / 2 ≤ φ σ} with hS
  suffices Icc s₁ b ⊆ S from this ⟨h12, h2b⟩
  have hsub : Icc s₁ b ⊆ Icc a b := Icc_subset_Icc_left ha
  refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ (by simp [hS]) ?_
  · have hcont : ContinuousOn (fun σ ↦ φ σ - (φ s₁ + (σ - s₁) / 2)) (Icc s₁ b) :=
      (hc.mono hsub).sub (by fun_prop)
    have hcl := hcont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0 : ℝ)))
    convert hcl using 1
    ext σ
    simp only [hS, mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_Ici, sub_nonneg]
    exact and_comm
  · rintro σ ⟨hσS, hσ1, hσb⟩
    have hσ0 : 0 < φ σ := by
      have : φ s₁ ≤ φ σ := by
        have : 0 ≤ (σ - s₁) / 2 := by linarith
        simp only [hS, mem_ofPred_eq] at hσS
        linarith
      linarith
    have hσab : σ ∈ Icc a b := ⟨ha.trans hσ1, hσb.le⟩
    obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousWithinAt_iff.1 (hc σ hσab) (φ σ) hσ0
    have hposnear : ∀ σ' ∈ Icc a b, |σ' - σ| < δ → 0 < φ σ' := fun σ' hσ' hd' ↦ by
      have := hδφ hσ' (by rwa [Real.dist_eq])
      rw [Real.dist_eq] at this
      linarith [abs_lt.1 this]
    set σ'' := min (σ + δ / 2) b with hσ''
    have hσσ'' : σ < σ'' := lt_min (by linarith) hσb
    filter_upwards [Ioo_mem_nhdsGT hσσ''] with σ' hσ'
    have hσ'b : σ' ≤ b := hσ'.2.le.trans (min_le_right _ _)
    have hσ'δ : σ' < σ + δ / 2 := hσ'.2.trans_le (min_le_left _ _)
    -- every point of `[σ, σ']` is in `[a, b]` with `φ > 0`
    have hD : ∀ x ∈ Icc σ σ', x ∈ Icc a b ∧ 0 < φ x := fun x hx ↦ by
      have hxab : x ∈ Icc a b := ⟨hσab.1.trans hx.1, hx.2.trans hσ'b⟩
      refine ⟨hxab, hposnear x hxab ?_⟩
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hderiv : ∀ x ∈ Icc σ σ', HasDerivAt φ (φ' x) x ∧ 1 / 2 ≤ φ' x := fun x hx ↦
      hd x (hD x hx).1 (hD x hx).2
    have hmvt := (convex_Icc σ σ').mul_sub_le_image_sub_of_le_deriv
      (fun x hx ↦ (hderiv x hx).1.continuousAt.continuousWithinAt)
      (fun x hx ↦ (hderiv x (interior_subset hx)).1.differentiableAt.differentiableWithinAt)
      (fun x hx ↦ by
        rw [(hderiv x (interior_subset hx)).1.deriv]
        exact (hderiv x (interior_subset hx)).2)
      σ ⟨le_rfl, hσ'.1.le⟩ σ' ⟨hσ'.1.le, le_rfl⟩ hσ'.1.le
    simp only [hS, mem_ofPred_eq] at hσS ⊢
    linarith

section Level

variable (hab : a ≤ b) (ht : 0 ≤ t) (htb : t < φ b)
include hab htb

theorem levelInf_set_nonempty : {s ∈ Icc a b | t < φ s}.Nonempty := ⟨b, ⟨hab, le_rfl⟩, htb⟩

omit hab htb in
theorem levelInf_set_bddBelow : BddBelow {s ∈ Icc a b | t < φ s} := ⟨a, fun _ h ↦ h.1.1⟩

/-- The level lies in `[a, b]`. -/
theorem levelInf_mem_Icc : levelInf φ a b t ∈ Icc a b :=
  ⟨le_csInf (levelInf_set_nonempty hab htb) fun _ h ↦ h.1.1,
    csInf_le levelInf_set_bddBelow ⟨⟨hab, le_rfl⟩, htb⟩⟩

omit hab htb in
/-- The level is at most every `s ∈ [a, b]` with `φ s > t`. -/
theorem levelInf_le (hs : s ∈ Icc a b) (h : t < φ s) : levelInf φ a b t ≤ s :=
  csInf_le levelInf_set_bddBelow ⟨hs, h⟩

/-- Below the level, `φ ≤ t`. -/
theorem apply_le_of_lt_levelInf (hs : a ≤ s) (h : s < levelInf φ a b t) : φ s ≤ t := by
  by_contra hlt
  push Not at hlt
  exact (levelInf_le ⟨hs, h.le.trans (levelInf_mem_Icc hab htb).2⟩ hlt).not_gt h

include ht in
/-- Above the level (and up to `b`), `φ > t`. -/
theorem lt_apply_of_levelInf_lt (hg : IsGrowing φ a b) (hs : s ≤ b)
    (h : levelInf φ a b t < s) : t < φ s := by
  obtain ⟨s', ⟨hs'I, hs't⟩, hs's⟩ := exists_lt_of_csInf_lt (levelInf_set_nonempty hab htb) h
  have := hg s' s hs'I.1 hs's.le hs (ht.trans_lt hs't)
  linarith

include ht in
/-- At the level, `φ = t`, when `φ a ≤ t` and `φ` is continuous on `[a, b]`. -/
theorem apply_levelInf (hg : IsGrowing φ a b) (hc : ContinuousOn φ (Icc a b)) (ha : φ a ≤ t) :
    φ (levelInf φ a b t) = t := by
  set ℓ := levelInf φ a b t with hℓ
  have hℓI := levelInf_mem_Icc hab htb
  have hcℓ : ContinuousWithinAt φ (Icc a b) ℓ := hc ℓ hℓI
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    have haℓ : a < ℓ := by
      rcases hℓI.1.lt_or_eq with h | h
      · exact h
      · rw [h] at ha; exact absurd ha hlt.not_ge
    have hev : ∀ᶠ σ in 𝓝[Ioo a ℓ] ℓ, t < φ σ := by
      have h1 : 𝓝[Ioo a ℓ] ℓ ≤ 𝓝[Icc a b] ℓ :=
        nhdsWithin_mono _ fun x hx ↦ ⟨hx.1.le, hx.2.le.trans hℓI.2⟩
      exact h1 (hcℓ.eventually (lt_mem_nhds hlt))
    have : (𝓝[Ioo a ℓ] ℓ).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsLT haℓ]; infer_instance
    obtain ⟨σ, hσt, hσI⟩ := (hev.and self_mem_nhdsWithin).exists
    exact (apply_le_of_lt_levelInf hab htb hσI.1.le hσI.2).not_gt hσt
  · rcases hℓI.2.lt_or_eq with hℓb | hℓb
    · have : (𝓝[Ioo ℓ b] ℓ).NeBot := by
        rw [nhdsWithin_Ioo_eq_nhdsGT hℓb]; infer_instance
      have hT : Tendsto φ (𝓝[Ioo ℓ b] ℓ) (𝓝 (φ ℓ)) :=
        (hcℓ.mono fun x hx ↦ ⟨hℓI.1.trans hx.1.le, hx.2.le⟩).tendsto
      refine ge_of_tendsto hT ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      exact (lt_apply_of_levelInf_lt hab ht htb hg hσ.2.le hσ.1).le
    · rw [hℓ, hℓb]; exact htb.le

include ht in
/-- For `t > 0`, the level is the unique solution of `φ s = t` in `[a, b]`. -/
theorem eq_levelInf_of_apply_eq (hg : IsGrowing φ a b) (hc : ContinuousOn φ (Icc a b))
    (ha : φ a ≤ t) (ht0 : 0 < t) (hs : s ∈ Icc a b) (h : φ s = t) : s = levelInf φ a b t := by
  set ℓ := levelInf φ a b t with hℓ
  have hℓI := levelInf_mem_Icc hab htb
  have hφℓ := apply_levelInf hab ht htb hg hc ha
  rcases lt_trichotomy s ℓ with hlt | heq | hgt
  · have := hg s ℓ hs.1 hlt.le hℓI.2 (h ▸ ht0)
    linarith
  · exact heq
  · have := lt_apply_of_levelInf_lt hab ht htb hg hs.2 hgt
    linarith

end Level

end EllipticBernoulli.Hodograph
