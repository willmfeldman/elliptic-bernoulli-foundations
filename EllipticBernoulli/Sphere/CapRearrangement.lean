/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.Polarization
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The cap rearrangement

Fix a unit vector `N` (the north pole). For `f : 𝕊 → ℝ` let `μ_f(t) = σ{f > t}`. The cap
rearrangement of `f` is

`f*(ω) = sup {t ≥ 0 : μ_f(t) > σ(C(φ(ω)))}`, with `sup ∅ = 0`,

where `φ` is the colatitude and `C(θ) = sphCap N θ` the open cap. We write
`f*(ω) = F*(φ(ω))` with the profile `F* = capProfile N f`, which is antitone in `θ`
(`capProfile_antitone`).

Main results, for bounded `f`:

* `lt_capProfile_iff`: for `t ≥ 0`, `t < F*(θ) ↔ σ(C(θ)) < μ_f(t)` (this uses
  the right continuity of `μ_f`);
* `exists_setOf_lt_capRearrangement`: for `d ≥ 2` and `t ≥ 0`, `{f* > t}` is an open cap
  `C(θ_t)` with `σ(C(θ_t)) = μ_f(t)`;
* `toSphere_lt_capRearrangement`, `map_capRearrangement`: for `f ≥ 0`, `f*` and `f` are
  equimeasurable;
* `capRearrangement_isPolarOrdered`: `f*` is ordered with respect to every `e` with
  `⟨N, e⟩ > 0` (`IsPolarOrdered`), because `φ(ρ_e ω) ≥ φ(ω)` when `⟨ω, e⟩ ≥ 0`.

The cap measure `θ ↦ σ(C(θ))` is computed from the colatitude formula:
`σ(C(θ)) = c_d ∫_0^θ sin^{d-2}` for `θ ∈ [0, π]` (`toReal_toSphere_sphCap`). It is continuous and
strictly increasing on `[0, π]`, from `0` to `σ(𝕊)`.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace InnerProductGeometry
open scoped NNReal Real ENNReal

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public noncomputable section

/-- The profile `F*(θ) = sup {t ≥ 0 : σ(C(θ)) < σ{f > t}}` of the cap rearrangement
(`sup ∅ = 0`). -/
def capProfile (N : E d) (f : sphere (0 : E d) 1 → ℝ) (θ : ℝ) : ℝ :=
  sSup {t : ℝ | 0 ≤ t ∧ (volume : Measure (E d)).toSphere (sphCap N θ) <
    (volume : Measure (E d)).toSphere {ω | t < f ω}}

/-- The cap rearrangement `f*(ω) = F*(φ(ω))` of `f` about the pole `N`. -/
def capRearrangement (N : E d) (f : sphere (0 : E d) 1 → ℝ) (ω : sphere (0 : E d) 1) : ℝ :=
  capProfile N f (colatitude N ω)

end

public section

/-! ### The profile -/

section Profile

variable {N : E d} {f : sphere (0 : E d) 1 → ℝ}

theorem sphCap_mono (N : E d) {θ θ' : ℝ} (h : θ ≤ θ') : sphCap N θ ⊆ sphCap N θ' :=
  fun _ hω ↦ lt_of_lt_of_le hω h

theorem capProfile_nonneg (N : E d) (f : sphere (0 : E d) 1 → ℝ) (θ : ℝ) :
    0 ≤ capProfile N f θ :=
  Real.sSup_nonneg fun _ ht ↦ ht.1

theorem capRearrangement_nonneg (N : E d) (f : sphere (0 : E d) 1 → ℝ)
    (ω : sphere (0 : E d) 1) : 0 ≤ capRearrangement N f ω :=
  capProfile_nonneg N f _

/-- If `σ(C(θ)) < σ{f > t}` then `t < M` for every upper bound `M` of `f`. -/
private theorem lt_of_mem_capSet {M : ℝ} (hfM : ∀ ω, f ω ≤ M) {θ t : ℝ}
    (ht : (volume : Measure (E d)).toSphere (sphCap N θ) <
      (volume : Measure (E d)).toSphere {ω | t < f ω}) : t < M := by
  by_contra h
  have : {ω | t < f ω} = ∅ := by
    ext ω; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
    exact (hfM ω).trans (not_lt.1 h)
  rw [this, measure_empty] at ht
  exact ENNReal.not_lt_zero ht

private theorem bddAbove_capSet {M : ℝ} (hfM : ∀ ω, f ω ≤ M) (θ : ℝ) :
    BddAbove {t : ℝ | 0 ≤ t ∧ (volume : Measure (E d)).toSphere (sphCap N θ) <
      (volume : Measure (E d)).toSphere {ω | t < f ω}} :=
  ⟨M, fun _ ht ↦ (lt_of_mem_capSet hfM ht.2).le⟩

theorem capProfile_le {M : ℝ} (hM : 0 ≤ M) (hfM : ∀ ω, f ω ≤ M) (θ : ℝ) :
    capProfile N f θ ≤ M :=
  Real.sSup_le (fun _ ht ↦ (lt_of_mem_capSet hfM ht.2).le) hM

theorem capProfile_antitone {M : ℝ} (hfM : ∀ ω, f ω ≤ M) : Antitone (capProfile N f) := by
  intro θ θ' hθ
  set S' := {t : ℝ | 0 ≤ t ∧ (volume : Measure (E d)).toSphere (sphCap N θ') <
      (volume : Measure (E d)).toSphere {ω | t < f ω}}
  rcases S'.eq_empty_or_nonempty with h | h
  · change sSup S' ≤ _
    rw [h, Real.sSup_empty]
    exact capProfile_nonneg N f θ
  · refine csSup_le_csSup (bddAbove_capSet hfM θ) h fun t ht ↦ ⟨ht.1, ?_⟩
    exact lt_of_le_of_lt (measure_mono (sphCap_mono N hθ)) ht.2

theorem measurable_capRearrangement (hN : ‖N‖ = 1) {M : ℝ} (hfM : ∀ ω, f ω ≤ M) :
    Measurable (capRearrangement N f) :=
  (capProfile_antitone hfM).measurable.comp (continuous_colatitude hN).measurable

/-- `t ↦ σ{f > t}` is right continuous: if `c < σ{f > t}` then `c < σ{f > t + 1/(n+1)}` for some
`n`. -/
private theorem exists_lt_toSphere_lt {t : ℝ} {c : ℝ≥0∞}
    (hc : c < (volume : Measure (E d)).toSphere {ω | t < f ω}) :
    ∃ n : ℕ, c < (volume : Measure (E d)).toSphere {ω | t + 1 / ((n : ℝ) + 1) < f ω} := by
  have hU : {ω | t < f ω} = ⋃ n : ℕ, {ω | t + 1 / ((n : ℝ) + 1) < f ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩
      have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have hmono : Monotone fun n : ℕ ↦ {ω | t + 1 / ((n : ℝ) + 1) < f ω} := by
    intro m n hmn ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
    linarith
  have htend := tendsto_measure_iUnion_atTop (μ := (volume : Measure (E d)).toSphere) hmono
  rw [← hU] at htend
  exact (htend.eventually (lt_mem_nhds hc)).exists

/-- **Level sets of the profile.** For bounded `f` and `t ≥ 0`,
`t < F*(θ) ↔ σ(C(θ)) < σ{f > t}`. -/
theorem lt_capProfile_iff {M : ℝ} (hfM : ∀ ω, f ω ≤ M) {t θ : ℝ}
    (ht : 0 ≤ t) :
    t < capProfile N f θ ↔ (volume : Measure (E d)).toSphere (sphCap N θ) <
      (volume : Measure (E d)).toSphere {ω | t < f ω} := by
  set S := {t : ℝ | 0 ≤ t ∧ (volume : Measure (E d)).toSphere (sphCap N θ) <
      (volume : Measure (E d)).toSphere {ω | t < f ω}}
  constructor
  · intro h
    rcases S.eq_empty_or_nonempty with hS | hS
    · change t < sSup S at h
      rw [hS, Real.sSup_empty] at h
      exact absurd h (not_lt.2 ht)
    obtain ⟨s, hs, hts⟩ := exists_lt_of_lt_csSup hS h
    refine lt_of_lt_of_le hs.2 (measure_mono fun ω hω ↦ ?_)
    exact lt_trans hts hω
  · intro h
    obtain ⟨n, hn⟩ := exists_lt_toSphere_lt h
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hmem : t + 1 / ((n : ℝ) + 1) ∈ S := ⟨by linarith, hn⟩
    exact lt_of_lt_of_le (by linarith) (le_csSup (bddAbove_capSet hfM θ) hmem)

end Profile

/-! ### Ordering -/

theorem colatitude_le_colatitude_polarReflection {N e : E d} (hN : ‖N‖ = 1) (he : ‖e‖ = 1)
    (hNe : 0 < inner ℝ N e) {ω : sphere (0 : E d) 1} (hω : 0 ≤ inner ℝ (ω : E d) e) :
    colatitude N ω ≤ colatitude N (sphereMap (polarReflection e) ω) := by
  rw [colatitude_eq_arccos hN, colatitude_eq_arccos hN, coe_sphereMap, polarReflection_apply he]
  refine Real.arccos_le_arccos ?_
  rw [inner_sub_right, inner_smul_right]
  nlinarith

/-- **The cap rearrangement is ordered** with respect to every `e` with `⟨N, e⟩ > 0`. -/
theorem capRearrangement_isPolarOrdered {N e : E d} (hN : ‖N‖ = 1) (he : ‖e‖ = 1)
    (hNe : 0 < inner ℝ N e) {f : sphere (0 : E d) 1 → ℝ} {M : ℝ} (hfM : ∀ ω, f ω ≤ M) :
    IsPolarOrdered e (capRearrangement N f) := fun _ hω ↦
  capProfile_antitone hfM (colatitude_le_colatitude_polarReflection hN he hNe hω)

/-! ### The cap measure -/

section CapMeasure

variable {N : E d}

/-- **The measure of a cap**: `σ(C(θ)) = c_d ∫_0^θ sin^{d-2}` for `θ ∈ [0, π]`. -/
theorem toReal_toSphere_sphCap (hd : 2 ≤ d) (hN : ‖N‖ = 1) {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    ((volume : Measure (E d)).toSphere (sphCap N θ)).toReal =
      ((volume : Measure (E (d - 1))).toSphere univ).toReal *
        ∫ φ in 0..θ, Real.sin φ ^ (d - 2) := by
  have hg : Measurable ((Iio θ).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Iio
  have h := integral_toSphere_colatitude hd hN hg (fun φ ↦ indicator_nonneg (fun _ _ ↦
    zero_le_one) φ)
  have hl : (fun ω ↦ (Iio θ).indicator (1 : ℝ → ℝ) (colatitude N ω)) =
      (sphCap N θ).indicator 1 := by
    funext ω
    by_cases hω : colatitude N ω < θ
    · rw [indicator_of_mem (show colatitude N ω ∈ Iio θ from hω),
        indicator_of_mem (show ω ∈ sphCap N θ from hω), Pi.one_apply, Pi.one_apply]
    · rw [indicator_of_notMem (show colatitude N ω ∉ Iio θ from hω),
        indicator_of_notMem (show ω ∉ sphCap N θ from hω)]
  have hmeas : MeasurableSet (sphCap N θ) :=
    measurableSet_lt (continuous_colatitude hN).measurable measurable_const
  rw [hl, integral_indicator_one hmeas, measureReal_def] at h
  rw [h]
  congr 1
  have hr : (fun φ ↦ Real.sin φ ^ (d - 2) * (Iio θ).indicator (1 : ℝ → ℝ) φ) =
      (Iio θ).indicator fun φ ↦ Real.sin φ ^ (d - 2) := by
    funext φ
    by_cases hφ : φ ∈ Iio θ
    · simp [indicator_of_mem hφ]
    · simp [indicator_of_notMem hφ]
  rw [hr, setIntegral_indicator measurableSet_Iio,
    show Ioo 0 π ∩ Iio θ = Ioo 0 θ by
      ext φ; simp only [mem_inter_iff, mem_Ioo, mem_Iio]
      constructor
      · rintro ⟨⟨h0, -⟩, h⟩; exact ⟨h0, h⟩
      · rintro ⟨h0, h⟩; exact ⟨⟨h0, h.trans_le hθ.2⟩, h⟩,
    intervalIntegral.integral_of_le hθ.1, integral_Ioc_eq_integral_Ioo]

private theorem continuous_primitive_sin_pow (d : ℕ) :
    Continuous fun θ : ℝ ↦ ∫ φ in 0..θ, Real.sin φ ^ (d - 2) :=
  intervalIntegral.continuous_primitive
    (fun _ _ ↦ (Real.continuous_sin.pow _).intervalIntegrable _ _) 0

private theorem strictMonoOn_primitive_sin_pow (d : ℕ) :
    StrictMonoOn (fun θ : ℝ ↦ ∫ φ in 0..θ, Real.sin φ ^ (d - 2)) (Icc 0 π) := by
  intro a ha b hb hab
  have hint : ∀ x y : ℝ, IntervalIntegrable (fun φ ↦ Real.sin φ ^ (d - 2)) volume x y :=
    fun _ _ ↦ (Real.continuous_sin.pow _).intervalIntegrable _ _
  simp only
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a b),
    lt_add_iff_pos_right]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (hint a b) (fun φ hφ ↦ ?_) hab
  exact pow_pos (Real.sin_pos_of_pos_of_lt_pi (ha.1.trans_lt hφ.1) (hφ.2.trans_le hb.2)) _

private theorem colatConst_toReal_pos (hd : 2 ≤ d) :
    0 < ((volume : Measure (E (d - 1))).toSphere univ).toReal :=
  ENNReal.toReal_pos (colatConst_ne_zero hd) (colatConst_ne_top d)

/-- The real cap measure `θ ↦ σ(C(θ))` is strictly increasing on `[0, π]`. -/
theorem toReal_toSphere_sphCap_lt_iff (hd : 2 ≤ d) (hN : ‖N‖ = 1) {θ θ' : ℝ}
    (hθ : θ ∈ Icc 0 π) (hθ' : θ' ∈ Icc 0 π) :
    (volume : Measure (E d)).toSphere (sphCap N θ) <
      (volume : Measure (E d)).toSphere (sphCap N θ') ↔ θ < θ' := by
  rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _),
    toReal_toSphere_sphCap hd hN hθ, toReal_toSphere_sphCap hd hN hθ',
    mul_lt_mul_iff_right₀ (colatConst_toReal_pos hd)]
  exact (strictMonoOn_primitive_sin_pow d).lt_iff_lt hθ hθ'

theorem sphCap_zero (N : E d) : sphCap N 0 = ∅ := by
  ext ω
  simp only [sphCap, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
  exact colatitude_nonneg N ω

/-- The cap of colatitude `π` has full measure. -/
theorem toSphere_sphCap_pi (hd : 2 ≤ d) (hN : ‖N‖ = 1) :
    (volume : Measure (E d)).toSphere (sphCap N π) =
      (volume : Measure (E d)).toSphere univ := by
  have h := ae_colatitude_notMem hd hN (Z := {π}) (measure_singleton _)
  refine measure_congr ?_
  filter_upwards [h] with ω hω
  simp only [mem_singleton_iff] at hω
  change (colatitude N ω < π) = True
  simp only [eq_iff_iff, iff_true]
  exact lt_of_le_of_ne (colatitude_le_pi N ω) hω

/-- **Existence of a cap with prescribed measure.** For `m ≤ σ(𝕊)` there is `θ ∈ [0, π]` with
`σ(C(θ)) = m`. -/
theorem exists_toSphere_sphCap_eq (hd : 2 ≤ d) (hN : ‖N‖ = 1) {m : ℝ≥0∞}
    (hm : m ≤ (volume : Measure (E d)).toSphere univ) :
    ∃ θ ∈ Icc 0 π, (volume : Measure (E d)).toSphere (sphCap N θ) = m := by
  set c := ((volume : Measure (E (d - 1))).toSphere univ).toReal
  set G : ℝ → ℝ := fun θ ↦ c * ∫ φ in 0..θ, Real.sin φ ^ (d - 2)
  have hG : ContinuousOn G (Icc 0 π) :=
    (continuous_const.mul (continuous_primitive_sin_pow d)).continuousOn
  have hG0 : G 0 = 0 := by simp [G]
  have hGπ : G π = ((volume : Measure (E d)).toSphere univ).toReal := by
    change c * _ = _
    rw [← toReal_toSphere_sphCap hd hN ⟨Real.pi_pos.le, le_rfl⟩, toSphere_sphCap_pi hd hN]
  have hmt : m ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top _ _) hm
  obtain ⟨θ, hθ, hGθ⟩ := intermediate_value_Icc Real.pi_pos.le hG
    (show m.toReal ∈ Icc (G 0) (G π) from ⟨by rw [hG0]; exact ENNReal.toReal_nonneg,
      by rw [hGπ]; exact ENNReal.toReal_mono (measure_ne_top _ _) hm⟩)
  refine ⟨θ, hθ, ?_⟩
  rw [← ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) hmt, toReal_toSphere_sphCap hd hN hθ]
  exact hGθ

end CapMeasure

/-! ### Equimeasurability -/

section Equimeasurable

variable {N : E d} {f : sphere (0 : E d) 1 → ℝ}

/-- **Level sets of `f*` are caps.** For
`d ≥ 2`, bounded `f` and `t ≥ 0`, there is `θ ∈ [0, π]` with `{f* > t} = C(θ)` and
`σ(C(θ)) = σ{f > t}`. -/
theorem exists_setOf_lt_capRearrangement (hd : 2 ≤ d) (hN : ‖N‖ = 1)
    {M : ℝ} (hfM : ∀ ω, f ω ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ∃ θ ∈ Icc 0 π, {ω | t < capRearrangement N f ω} = sphCap N θ ∧
      (volume : Measure (E d)).toSphere (sphCap N θ) =
        (volume : Measure (E d)).toSphere {ω | t < f ω} := by
  obtain ⟨θ, hθ, hθm⟩ := exists_toSphere_sphCap_eq hd hN (N := N)
    (measure_mono (subset_univ {ω | t < f ω}))
  refine ⟨θ, hθ, ?_, hθm⟩
  ext ω
  simp only [mem_ofPred_eq, capRearrangement, lt_capProfile_iff hfM ht, ← hθm]
  exact toReal_toSphere_sphCap_lt_iff hd hN ⟨colatitude_nonneg N ω, colatitude_le_pi N ω⟩ hθ

/-- **Equimeasurability** of `f*` and `f ≥ 0`: `σ{f* > t} = σ{f > t}` for every `t`. -/
theorem toSphere_lt_capRearrangement (hd : 2 ≤ d) (hN : ‖N‖ = 1)
    (hf0 : ∀ ω, 0 ≤ f ω) {M : ℝ} (hfM : ∀ ω, f ω ≤ M) (t : ℝ) :
    (volume : Measure (E d)).toSphere {ω | t < capRearrangement N f ω} =
      (volume : Measure (E d)).toSphere {ω | t < f ω} := by
  rcases lt_or_ge t 0 with ht | ht
  · have h₁ : {ω | t < capRearrangement N f ω} = univ :=
      eq_univ_of_forall fun ω ↦ ht.trans_le (capRearrangement_nonneg N f ω)
    have h₂ : {ω | t < f ω} = univ := eq_univ_of_forall fun ω ↦ ht.trans_le (hf0 ω)
    rw [h₁, h₂]
  · obtain ⟨θ, -, h₁, h₂⟩ := exists_setOf_lt_capRearrangement hd hN hfM ht
    rw [h₁, h₂]

/-- **Equimeasurability** of `f*` and `f ≥ 0`: they have the same distribution under `σ`. -/
theorem map_capRearrangement (hd : 2 ≤ d) (hN : ‖N‖ = 1) (hf : Measurable f)
    (hf0 : ∀ ω, 0 ≤ f ω) {M : ℝ} (hfM : ∀ ω, f ω ≤ M) :
    ((volume : Measure (E d)).toSphere).map (capRearrangement N f) =
      ((volume : Measure (E d)).toSphere).map f := by
  have hm := measurable_capRearrangement hN hfM (f := f)
  refine Measure.ext_of_Iic _ _ fun a ↦ ?_
  rw [Measure.map_apply hm measurableSet_Iic, Measure.map_apply hf measurableSet_Iic]
  have hc : ∀ g : sphere (0 : E d) 1 → ℝ, g ⁻¹' Iic a = {ω | a < g ω}ᶜ := fun g ↦ by
    ext ω; simp
  rw [hc, hc, measure_compl (measurableSet_lt measurable_const hm) (measure_ne_top _ _),
    measure_compl (measurableSet_lt measurable_const hf) (measure_ne_top _ _),
    toSphere_lt_capRearrangement hd hN hf0 hfM]

end Equimeasurable

end

end EllipticBernoulli
