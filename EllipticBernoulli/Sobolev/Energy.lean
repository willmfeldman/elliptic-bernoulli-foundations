/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.L2
public import EllipticBernoulli.Sobolev.Lattice

/-!
# Energy bookkeeping and lower semicontinuity of `energyJ`

For the Alt–Caffarelli energy `energyJ V Q v G = ∫⁻_V (‖G‖² + Q² 1_{posSet v V})` (the
coefficient enters squared; the weak gradient `G` is carried as data):

* `energyJ_congr`, `energyJ_congr_ae`: the energy only depends on `v` on `V` and on `G` a.e. on `V`;
* `energyJ_posPart_le`: `J_Q(v₊; V) ≤ J_Q(v; V)`;
* `energyJ_split`: additivity over `B ⊆ B'`;
* `energyJ_eq_add`: splitting into the Dirichlet term and the positivity term;
* `energyJ_lt_top`: finiteness on sets compactly contained in the domain of an `H¹_loc` function
  with bounded `Q`;
* `energyJ_le_liminf`: lower semicontinuity of `energyJ B Q` under a.e. convergence of
  the functions and weak `L²(B)` convergence of the gradients (weak lsc of the Dirichlet term plus
  Fatou for the positivity term).

The positivity term is relative to `V` (`posSet v V`); every statement keeps the same set `V`
throughout.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- `energyJ` only depends on the function on `V` and on the gradient a.e. on `V`. -/
theorem energyJ_congr {V : Set (E d)} {Q f₁ f₂ : E d → ℝ}
    {G₁ G₂ : E d → E d} (hf : EqOn f₁ f₂ V) (hG : ∀ᵐ x ∂(volume.restrict V), G₁ x = G₂ x) :
    energyJ V Q f₁ G₁ = energyJ V Q f₂ G₂ := by
  have hpos : posSet f₁ V = posSet f₂ V := by
    ext y; simp only [posSet, mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨h.1, hf h.1 ▸ h.2⟩, fun h ↦ ⟨h.1, (hf h.1).symm ▸ h.2⟩⟩
  unfold energyJ
  rw [hpos]
  refine lintegral_congr_ae ?_
  filter_upwards [hG] with x hx
  rw [hx]

/-- Positive part: `J_Q(v₊; V) ≤ J_Q(v; V)` with `∇v₊ = 1_{v > 0} ∇v`. -/
theorem energyJ_posPart_le (V : Set (E d)) (Q v : E d → ℝ) (G : E d → E d) :
    energyJ V Q (fun y ↦ max (v y) 0) ({y | 0 < v y}.indicator G) ≤ energyJ V Q v G := by
  have hpos : posSet (fun y ↦ max (v y) 0) V = posSet v V := by
    ext y; simp [posSet]
  unfold energyJ
  rw [hpos]
  refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
  gcongr
  by_cases hx : 0 < v x
  · simp [hx]
  · simp [hx]

/-- Splitting `energyJ` over `B ⊆ B'`. -/
theorem energyJ_split {B B' : Set (E d)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hBB' : B ⊆ B')
    (Q f : E d → ℝ) (G : E d → E d) :
    energyJ B' Q f G = energyJ B Q f G + energyJ (B' \ B) Q f G := by
  unfold energyJ
  rw [← lintegral_inter_add_sdiff _ B' hB, inter_eq_right.2 hBB']
  congr 1
  · refine setLIntegral_congr_fun hB fun x hx ↦ ?_
    have : x ∈ posSet f B' ↔ x ∈ posSet f B := by
      simp only [posSet, mem_ofPred_eq]; exact ⟨fun h ↦ ⟨hx, h.2⟩, fun h ↦ ⟨hBB' hx, h.2⟩⟩
    have hind : (posSet f B').indicator (1 : E d → ℝ) x = (posSet f B).indicator 1 x := by
      by_cases h : x ∈ posSet f B
      · rw [indicator_of_mem h, indicator_of_mem (this.2 h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (mt this.1 h)]
    rw [hind]
  · refine setLIntegral_congr_fun (hB'.diff hB) fun x hx ↦ ?_
    have : x ∈ posSet f B' ↔ x ∈ posSet f (B' \ B) := by
      simp only [posSet, mem_ofPred_eq]; exact ⟨fun h ↦ ⟨hx, h.2⟩, fun h ↦ ⟨hx.1, h.2⟩⟩
    have hind : (posSet f B').indicator (1 : E d → ℝ) x = (posSet f (B' \ B)).indicator 1 x := by
      by_cases h : x ∈ posSet f (B' \ B)
      · rw [indicator_of_mem h, indicator_of_mem (this.2 h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (mt this.1 h)]
    rw [hind]

/-- On `V`, the indicator of `posSet v V` is the indicator of `(0, ∞)` composed with `v`. -/
theorem posSet_indicator_one_eq {V : Set (E d)} {v : E d → ℝ} {x : E d} (hx : x ∈ V) :
    (posSet v V).indicator (1 : E d → ℝ) x = (Ioi (0 : ℝ)).indicator 1 (v x) := by
  by_cases h : 0 < v x
  · rw [indicator_of_mem (show x ∈ posSet v V from ⟨hx, h⟩),
      indicator_of_mem (show v x ∈ Ioi (0 : ℝ) from h)]
    rfl
  · rw [indicator_of_notMem (show x ∉ posSet v V from fun h' ↦ h h'.2),
      indicator_of_notMem (show v x ∉ Ioi (0 : ℝ) from h)]

/-- `energyJ` with the positivity indicator written as `1_{(0,∞)} ∘ v`. -/
theorem energyJ_eq_lintegral_indicator_Ioi {V : Set (E d)} (hV : MeasurableSet V)
    (Q v : E d → ℝ) (G : E d → E d) :
    energyJ V Q v G = ∫⁻ x in V,
      ENNReal.ofReal (‖G x‖ ^ 2 + Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (v x)) := by
  unfold energyJ
  refine setLIntegral_congr_fun hV fun x hx ↦ ?_
  rw [posSet_indicator_one_eq hx]

/-- `energyJ` is unchanged when `v` is changed on a null subset of `V` (and `G` a.e. on `V`). -/
theorem energyJ_congr_ae {V : Set (E d)} (hV : MeasurableSet V) {Q f₁ f₂ : E d → ℝ}
    {G₁ G₂ : E d → E d} (hf : ∀ᵐ x ∂(volume.restrict V), f₁ x = f₂ x)
    (hG : ∀ᵐ x ∂(volume.restrict V), G₁ x = G₂ x) :
    energyJ V Q f₁ G₁ = energyJ V Q f₂ G₂ := by
  rw [energyJ_eq_lintegral_indicator_Ioi hV, energyJ_eq_lintegral_indicator_Ioi hV]
  refine lintegral_congr_ae ?_
  filter_upwards [hf, hG] with x h1 h2
  rw [h1, h2]

/-- The positivity term of `energyJ` is a.e.-measurable when `Q` and `v` are. -/
theorem aemeasurable_posTerm {μ : Measure (E d)} {Q v : E d → ℝ} (hQ : AEMeasurable Q μ)
    (hv : AEMeasurable v μ) :
    AEMeasurable (fun x ↦ ENNReal.ofReal (Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (v x))) μ := by
  have hind : Measurable ((Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ)) :=
    measurable_const.indicator measurableSet_Ioi
  exact ENNReal.measurable_ofReal.comp_aemeasurable
    ((hQ.pow_const 2).mul (hind.comp_aemeasurable hv))

/-- **Splitting `energyJ`** into the Dirichlet term and the positivity term. -/
theorem energyJ_eq_add {V : Set (E d)} (Q v : E d → ℝ) {G : E d → E d}
    (hG : AEStronglyMeasurable G (volume.restrict V)) :
    energyJ V Q v G = (∫⁻ x in V, ENNReal.ofReal (‖G x‖ ^ 2)) +
      ∫⁻ x in V, ENNReal.ofReal (Q x ^ 2 * (posSet v V).indicator 1 x) := by
  unfold energyJ
  have hm : AEMeasurable (fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2)) (volume.restrict V) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hG.norm.aemeasurable.pow_const 2)
  rw [← lintegral_add_left' hm]
  refine lintegral_congr fun x ↦ ?_
  have h1 : 0 ≤ Q x ^ 2 * (posSet v V).indicator 1 x :=
    mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  exact ENNReal.ofReal_add (sq_nonneg _) h1

/-- **Finiteness of the energy.** If `v ∈ H¹_loc(U)`, `closure B` is a compact subset of `U` and `Q`
is bounded on `B`, then `J_Q(v; B) < ∞`. -/
theorem energyJ_lt_top {U B : Set (E d)} {Q v : E d → ℝ} {G : E d → E d} (hv : MemH1Loc U v G)
    (hBc : IsCompact (closure B)) (hBU : closure B ⊆ U) {CQ : ℝ} (hQ : ∀ x ∈ B, |Q x| ≤ CQ) :
    energyJ B Q v G < ⊤ := by
  have hG := (hv.2 _ hBU hBc).2
  have hpt : ∀ x, ENNReal.ofReal (‖G x‖ ^ 2 + Q x ^ 2 * (posSet v B).indicator 1 x) ≤
      ENNReal.ofReal (‖G x‖ ^ 2) + ENNReal.ofReal (CQ ^ 2) := by
    intro x
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    gcongr
    by_cases hx : x ∈ posSet v B
    · rw [indicator_of_mem hx, Pi.one_apply, mul_one]
      exact sq_le_sq' (abs_le.1 (hQ x hx.1)).1 (abs_le.1 (hQ x hx.1)).2
    · rw [indicator_of_notMem hx, mul_zero]; positivity
  calc energyJ B Q v G
      ≤ ∫⁻ x in B, (ENNReal.ofReal (‖G x‖ ^ 2) + ENNReal.ofReal (CQ ^ 2)) := lintegral_mono hpt
    _ ≤ ∫⁻ x in closure B, (ENNReal.ofReal (‖G x‖ ^ 2) + ENNReal.ofReal (CQ ^ 2)) :=
        lintegral_mono_set subset_closure
    _ = (∫⁻ x in closure B, ENNReal.ofReal (‖G x‖ ^ 2)) +
          ENNReal.ofReal (CQ ^ 2) * volume (closure B) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          hBc.measure_lt_top⟩
        exact hG.norm.integrable_sq.lintegral_lt_top

/-- Superadditivity of `liminf` for `ℝ≥0∞`-valued sequences. -/
theorem le_liminf_add_ennreal (u w : ℕ → ℝ≥0∞) :
    liminf u atTop + liminf w atTop ≤ liminf (u + w) atTop := by
  simp only [liminf_eq_iSup_iInf_of_nat]
  have hmono : ∀ f : ℕ → ℝ≥0∞, Monotone fun n ↦ ⨅ i ≥ n, f i :=
    fun f n m hnm ↦ biInf_mono fun i hi ↦ hnm.trans hi
  rw [ENNReal.iSup_add_iSup_of_monotone (hmono u) (hmono w)]
  exact iSup_mono fun n ↦ le_iInf₂ fun i hi ↦ add_le_add (iInf₂_le i hi) (iInf₂_le i hi)

/-- **Lower semicontinuity of `energyJ`.** Let `B` be measurable, `Q` a.e.-measurable
on `B`, `v k → v₀` a.e. on `B` with each `v k` a.e.-measurable on `B`, and `G k ⇀ G₀` weakly in
`L²(B)`. Then `J_Q(v₀, G₀; B) ≤ liminf_k J_Q(v k, G k; B)`. -/
theorem energyJ_le_liminf {B : Set (E d)} (hB : MeasurableSet B) {Q : E d → ℝ}
    (hQ : AEMeasurable Q (volume.restrict B)) {v : ℕ → E d → ℝ} {v₀ : E d → ℝ}
    {G : ℕ → E d → E d} {G₀ : E d → E d} (hvm : ∀ k, AEMeasurable (v k) (volume.restrict B))
    (hv : ∀ᵐ x ∂(volume.restrict B), Tendsto (fun k ↦ v k x) atTop (𝓝 (v₀ x)))
    (hG : TendstoWeakL2 volume B G G₀ atTop) :
    energyJ B Q v₀ G₀ ≤ liminf (fun k ↦ energyJ B Q (v k) (G k)) atTop := by
  set P : (E d → ℝ) → E d → ℝ≥0∞ :=
    fun w x ↦ ENNReal.ofReal (Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (w x)) with hP
  have hsplit : ∀ (w : E d → ℝ) (H : E d → E d), AEStronglyMeasurable H (volume.restrict B) →
      energyJ B Q w H = (∫⁻ x in B, ENNReal.ofReal (‖H x‖ ^ 2)) + ∫⁻ x in B, P w x := by
    intro w H hH
    rw [energyJ_eq_add Q w hH]
    congr 1
    refine setLIntegral_congr_fun hB fun x hx ↦ ?_
    rw [posSet_indicator_one_eq hx]
  have hA : (∫⁻ x in B, ENNReal.ofReal (‖G₀ x‖ ^ 2)) ≤
      liminf (fun k ↦ ∫⁻ x in B, ENNReal.ofReal (‖G k x‖ ^ 2)) atTop := by
    have h := lintegral_weighted_sq_le_liminf volume B G G₀ hG (fun _ ↦ (1 : ℝ))
      measurable_const (fun _ ↦ zero_le_one) 1 (fun _ ↦ le_rfl)
    simpa only [one_mul] using h
  have hPt : ∀ᵐ x ∂(volume.restrict B), P v₀ x ≤ liminf (fun k ↦ P (v k) x) atTop := by
    filter_upwards [hv] with x hx
    by_cases h0 : 0 < v₀ x
    · have hev : ∀ᶠ k in atTop, P (v k) x = P v₀ x := by
        filter_upwards [hx.eventually (lt_mem_nhds h0)] with k hk
        simp [hP, indicator, hk, h0]
      rw [(tendsto_const_nhds.congr' (hev.mono fun k hk ↦ hk.symm)).liminf_eq]
    · simp [hP, indicator_of_notMem (show v₀ x ∉ Ioi (0 : ℝ) from h0)]
  have hPl : (∫⁻ x in B, P v₀ x) ≤ liminf (fun k ↦ ∫⁻ x in B, P (v k) x) atTop :=
    (lintegral_mono_ae hPt).trans
      (lintegral_liminf_le' fun k ↦ aemeasurable_posTerm hQ (hvm k))
  rw [hsplit v₀ G₀ hG.2.1.aestronglyMeasurable]
  have heq : (fun k ↦ energyJ B Q (v k) (G k)) =
      (fun k ↦ ∫⁻ x in B, ENNReal.ofReal (‖G k x‖ ^ 2)) + fun k ↦ ∫⁻ x in B, P (v k) x := by
    funext k
    rw [hsplit (v k) (G k) (hG.1 k).aestronglyMeasurable, Pi.add_apply]
  rw [heq]
  exact (add_le_add hA hPl).trans (le_liminf_add_ennreal _ _)

end EllipticBernoulli
