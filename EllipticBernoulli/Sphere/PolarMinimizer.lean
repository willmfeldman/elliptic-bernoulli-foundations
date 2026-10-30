/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.PolarHull
public import EllipticBernoulli.Sphere.CapRearrangement

/-!
# The cap rearrangement lies in the polarization hull

A step in the polarization proof of the Pólya–Szegő inequality (`Sphere/PolyaSzego.lean`). Let
`d ≥ 2`, `|N| = 1`, and let `f` be `L`-Lipschitz with values in `[0, M]`. The functional
`J(g) = ∫_𝕊 (g - f*)² dσ` attains its minimum on the compact hull `K = polarHull N f` at some `g₀`.
If `g₀ ≠ f*` on a set of positive measure, then for some `t ≥ 0` both `{g₀ > t} \ C` and
`C ∩ {g₀ ≤ t}` have positive measure, where `C = {f* > t}` is an open cap. Picking `x` in the first
set (off the closed cap) and `y` in the second, the polarization in `e = (y - x)/|y - x|` swaps `x`
and `y`, has `⟨N, e⟩ > 0`, and strictly decreases `J` (by the formula `integral_sq_sub_polarize`),
which contradicts minimality.

Main result: `exists_mem_polarHull_ae_eq_capRearrangement`.

In Lean, `J` is minimized in the clamped form `∫ (max 0 (min g C) - f*)²`, which is continuous on
all of `C(𝕊, ℝ)` and agrees with `J` on the hull.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped NNReal Real ENNReal

namespace EllipticBernoulli

variable {d : ℕ}

/-- Two real functions are a.e. equal if, for every rational `q`, their superlevel sets `{· > q}`
agree up to null sets. -/
private theorem ae_eq_of_forall_rat {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u v : X → ℝ}
    (h : ∀ q : ℚ, μ ({x | (q : ℝ) < u x} \ {x | (q : ℝ) < v x}) = 0 ∧
      μ ({x | (q : ℝ) < v x} \ {x | (q : ℝ) < u x}) = 0) : u =ᵐ[μ] v := by
  have hae : ∀ᵐ x ∂μ, ∀ q : ℚ, ((q : ℝ) < u x → (q : ℝ) < v x) ∧
      ((q : ℝ) < v x → (q : ℝ) < u x) := by
    rw [ae_all_iff]
    intro q
    have h₁ := measure_eq_zero_iff_ae_notMem.1 (h q).1
    have h₂ := measure_eq_zero_iff_ae_notMem.1 (h q).2
    filter_upwards [h₁, h₂] with x hx₁ hx₂
    simp only [Set.mem_sdiff, mem_ofPred_eq, not_and, not_lt] at hx₁ hx₂
    exact ⟨fun hq ↦ by by_contra hc; exact absurd (hx₁ hq) (by simpa using hc),
      fun hq ↦ by by_contra hc; exact absurd (hx₂ hq) (by simpa using hc)⟩
  filter_upwards [hae] with x hx
  rcases lt_trichotomy (u x) (v x) with hlt | heq | hgt
  · obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hlt
    exact absurd ((hx q).2 hq₂) (not_lt.2 hq₁.le)
  · exact heq
  · obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hgt
    exact absurd ((hx q).1 hq₂) (not_lt.2 hq₁.le)

/-- For a finite measure, sets of equal measure have differences of equal measure. -/
private theorem measure_sdiff_eq_of_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : μ A = μ B) : μ (A \ B) = μ (B \ A) := by
  have h₁ := measure_sdiff_add_inter (μ := μ) A hB
  have h₂ := measure_sdiff_add_inter (μ := μ) B hA
  rw [inter_comm] at h₂
  rw [← h₁, ← h₂] at h
  exact (ENNReal.add_left_inj (measure_ne_top _ _)).1 h

/-- The clamp `max 0 (min s C)`. -/
private noncomputable def clampC (C s : ℝ) : ℝ := max 0 (min s C)

private theorem clampC_of_mem {C s : ℝ} (hs : s ∈ Icc 0 C) : clampC C s = s := by
  rw [clampC, min_eq_left hs.2, max_eq_right hs.1]

private theorem continuous_clampC (C : ℝ) : Continuous (clampC C) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The clamped `L²` distance to a bounded measurable `h` is continuous on `C(𝕊, ℝ)`. -/
private theorem continuous_clampedDist {h : sphere (0 : E d) 1 → ℝ} (hh : Measurable h)
    {C : ℝ} (hC : 0 ≤ C) (hhC : ∀ ω, h ω ∈ Icc 0 C) :
    Continuous fun g : C(sphere (0 : E d) 1, ℝ) ↦
      ∫ ω, (clampC C (g ω) - h ω) ^ 2 ∂(volume : Measure (E d)).toSphere := by
  rw [continuous_iff_seqContinuous]
  intro g g₀ hg
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ C ^ 2) (fun n ↦ ?_)
    (integrable_const _) (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_)
  · exact ((((continuous_clampC C).comp (g n).continuous).measurable.sub hh).pow_const
      2).aestronglyMeasurable
  · have h₁ : clampC C (g n ω) ∈ Icc 0 C :=
      ⟨le_max_left _ _, max_le hC (min_le_right _ _)⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [abs_le]
    constructor <;> linarith [h₁.1, h₁.2, (hhC ω).1, (hhC ω).2]
  · refine ((((continuous_clampC C).tendsto _).comp ?_).sub tendsto_const_nhds).pow 2
    exact (continuous_eval_const ω).tendsto g₀ |>.comp hg

public section

/-- **The cap rearrangement lies in the hull.** Let `d ≥ 2`,
`|N| = 1` and `f` be `L`-Lipschitz with values in `[0, M]`. Then some `g₀ ∈ polarHull N f` is
`σ`-a.e. equal to the cap rearrangement `f*`. -/
theorem exists_mem_polarHull_ae_eq_capRearrangement (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1)
    {L : ℝ≥0} {f : sphere (0 : E d) 1 → ℝ} (hf : LipschitzWith L f) {M : ℝ}
    (hfM : ∀ ω, f ω ∈ Icc 0 M) :
    ∃ g ∈ polarHull N f, (g : sphere (0 : E d) 1 → ℝ) =ᵐ[(volume : Measure (E d)).toSphere]
      capRearrangement N f := by
  set σ := (volume : Measure (E d)).toSphere
  set h := capRearrangement N f
  set C := max M 0
  have hC : 0 ≤ C := le_max_right _ _
  have hfC : ∀ ω, f ω ∈ Icc 0 C := fun ω ↦ ⟨(hfM ω).1, (hfM ω).2.trans (le_max_left _ _)⟩
  have hfle : ∀ ω, f ω ≤ C := fun ω ↦ (hfC ω).2
  have hhm : Measurable h := measurable_capRearrangement hN hfle
  have hhC : ∀ ω, h ω ∈ Icc 0 C := fun ω ↦
    ⟨capRearrangement_nonneg N f ω, capProfile_le hC hfle _⟩
  have hfmeas : Measurable f := hf.continuous.measurable
  -- the minimizer
  set J : C(sphere (0 : E d) 1, ℝ) → ℝ := fun g ↦ ∫ ω, (clampC C (g ω) - h ω) ^ 2 ∂σ
  obtain ⟨g₀, hg₀, hmin⟩ := (isCompact_polarHull hf hfC (N := N)).exists_isMinOn
    ⟨_, mem_polarHull_self hf⟩ (continuous_clampedDist hhm hC hhC).continuousOn
  refine ⟨g₀, hg₀, ?_⟩
  have hJ : ∀ g ∈ polarHull N f, J g = ∫ ω, (g ω - h ω) ^ 2 ∂σ := fun g hg ↦ by
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only
    rw [clampC_of_mem (mem_Icc_of_mem_polarHull hfC hg ω)]
  have hg₀C : ∀ ω, g₀ ω ∈ Icc 0 C := mem_Icc_of_mem_polarHull hfC hg₀
  have hg₀m : Measurable g₀ := g₀.continuous.measurable
  -- equal measures of superlevel sets
  have hlev : ∀ t : ℝ, σ {ω | t < g₀ ω} = σ {ω | t < h ω} := fun t ↦ by
    have hmap := map_eq_of_mem_polarHull hfmeas hg₀ (N := N)
    have h₁ := congrArg (fun μ : Measure ℝ ↦ μ (Ioi t)) hmap
    simp only [Measure.map_apply hg₀m measurableSet_Ioi,
      Measure.map_apply hfmeas measurableSet_Ioi] at h₁
    rw [toSphere_lt_capRearrangement hd hN (fun ω ↦ (hfC ω).1) hfle]
    exact h₁
  by_contra hne
  have hq : ∃ q : ℚ, σ ({ω | (q : ℝ) < g₀ ω} \ {ω | (q : ℝ) < h ω}) ≠ 0 := by
    by_contra hall
    push Not at hall
    refine hne (ae_eq_of_forall_rat fun q ↦ ⟨hall q, ?_⟩)
    rw [← measure_sdiff_eq_of_eq (measurableSet_lt measurable_const hg₀m)
      (measurableSet_lt measurable_const hhm) (hlev q)]
    exact hall q
  obtain ⟨q, hq⟩ := hq
  set t : ℝ := (q : ℝ)
  have ht : 0 ≤ t := by
    by_contra htn
    push Not at htn
    refine hq (measure_mono_null (fun ω hω ↦ ?_) measure_empty)
    exact absurd (htn.trans_le (hhC ω).1) hω.2
  obtain ⟨θ, hθ, hcap, -⟩ := exists_setOf_lt_capRearrangement hd hN hfle ht (f := f)
  -- the two sets of positive measure
  set A := {ω | t < g₀ ω}
  have hA : σ (A \ sphCap N θ) ≠ 0 := by rwa [← hcap]
  have hB : σ (sphCap N θ \ A) ≠ 0 := by
    rwa [← hcap, ← measure_sdiff_eq_of_eq (measurableSet_lt measurable_const hg₀m)
      (measurableSet_lt measurable_const hhm) (hlev t)]
  have hbdry : σ {ω | colatitude N ω = θ} = 0 := by
    have := ae_colatitude_notMem hd hN (Z := {θ}) (measure_singleton _)
    exact measure_eq_zero_iff_ae_notMem.2 this
  have hA' : σ (A ∩ {ω | θ < colatitude N ω}) ≠ 0 := by
    intro h0
    refine hA (measure_mono_null (fun ω hω ↦ ?_) (measure_union_null h0 hbdry))
    rcases lt_or_eq_of_le (not_lt.1 (show ¬ colatitude N ω < θ from hω.2)) with hlt | heq
    · exact Or.inl ⟨hω.1, hlt⟩
    · exact Or.inr heq.symm
  obtain ⟨x, hxA, hxθ⟩ := nonempty_of_measure_ne_zero hA'
  obtain ⟨y, hyC, hyA⟩ := nonempty_of_measure_ne_zero hB
  have hxθ : θ < colatitude N x := hxθ
  have hyθ : colatitude N y < θ := hyC
  have hgx : t < g₀ x := hxA
  have hgy : g₀ y ≤ t := not_lt.1 hyA
  -- the polarization direction
  have hxy : (y : E d) ≠ x := fun h ↦ by
    have : colatitude N y = colatitude N x := by rw [colatitude, colatitude, h]
    linarith
  have hyx : 0 < ‖(y : E d) - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  set e : E d := ‖(y : E d) - x‖⁻¹ • ((y : E d) - x)
  have he : ‖e‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hyx.ne']
  have hNxy : inner ℝ N (x : E d) < inner ℝ N (y : E d) := by
    by_contra hle
    push Not at hle
    have := Real.arccos_le_arccos hle
    rw [← colatitude_eq_arccos hN, ← colatitude_eq_arccos hN] at this
    linarith
  have hNe : 0 < inner ℝ N e := by
    rw [inner_smul_right, inner_sub_right]
    exact mul_pos (inv_pos.2 hyx) (sub_pos.2 hNxy)
  have hnx : ‖(x : E d)‖ = 1 := norm_eq_of_mem_sphere x
  have hny : ‖(y : E d)‖ = 1 := norm_eq_of_mem_sphere y
  have hye : 0 < inner ℝ (y : E d) e := by
    rw [inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq, hny]
    refine mul_pos (inv_pos.2 hyx) ?_
    have h2 : ‖(y : E d) - x‖ ^ 2 = 2 - 2 * inner ℝ (y : E d) x := by
      rw [norm_sub_sq_real, hnx, hny]; ring
    nlinarith
  set ρ := sphereMap (polarReflection e)
  have hρy : ρ y = x := by
    ext1
    have hR : polarReflection e = (ℝ ∙ ((y : E d) - x))ᗮ.reflection := by
      unfold polarReflection
      simp only [e, Submodule.span_singleton_smul_eq (inv_pos.2 hyx).ne'.isUnit]
    rw [coe_sphereMap, hR]
    exact Submodule.reflection_sub (by rw [hnx, hny])
  -- the open set where the polarization gains
  have hρc : Continuous ρ := continuous_sphereMap _
  have hφc := continuous_colatitude hN
  set V : Set (sphere (0 : E d) 1) := {ω | 0 < inner ℝ (ω : E d) e} ∩
    {ω | g₀ ω < g₀ (ρ ω)} ∩ {ω | colatitude N ω < θ} ∩ {ω | θ < colatitude N (ρ ω)}
  have hVo : IsOpen V :=
    (((isOpen_lt continuous_const (continuous_subtype_val.inner continuous_const)).inter
      (isOpen_lt g₀.continuous (g₀.continuous.comp hρc))).inter
      (isOpen_lt hφc continuous_const)).inter (isOpen_lt continuous_const (hφc.comp hρc))
  have hyV : y ∈ V := by
    refine ⟨⟨⟨hye, ?_⟩, hyθ⟩, ?_⟩
    · change g₀ y < g₀ (ρ y); rw [hρy]; linarith
    · change θ < colatitude N (ρ y); rw [hρy]; exact hxθ
  have hVpos : 0 < σ V := toSphere_pos_of_isOpen hVo ⟨y, hyV⟩
  -- the gain
  set D : sphere (0 : E d) 1 → ℝ := fun ω ↦ max (g₀ (ρ ω) - g₀ ω) 0 * (h ω - h (ρ ω))
  have hord := capRearrangement_isPolarOrdered hN he hNe hfle (f := f)
  have hD0 : ∀ ω : sphere (0 : E d) 1, 0 ≤ inner ℝ (ω : E d) e → 0 ≤ D ω := fun ω hω ↦
    mul_nonneg (le_max_right _ _) (sub_nonneg.2 (hord ω hω))
  have hDpos : ∀ ω ∈ V, 0 < D ω := by
    rintro ω ⟨⟨⟨-, hg⟩, hφ⟩, hφρ⟩
    refine mul_pos (lt_max_of_lt_left (sub_pos.2 hg)) (sub_pos.2 ?_)
    have h₁ : t < h ω := by
      have : ω ∈ {ω | t < h ω} := by rw [hcap]; exact hφ
      exact this
    have h₂ : h (ρ ω) ≤ t := by
      by_contra hc
      have : ρ ω ∈ {ω | t < h ω} := not_le.1 hc
      rw [hcap] at this
      exact absurd (show colatitude N (ρ ω) < θ from this) (not_lt.2 hφρ.le)
    linarith
  have hρm : Measurable ρ := hρc.measurable
  have hDm : Measurable D :=
    ((hg₀m.comp hρm).sub hg₀m).max measurable_const |>.mul (hhm.sub (hhm.comp hρm))
  have hDint : Integrable D σ := by
    refine Integrable.of_bound hDm.aestronglyMeasurable (C * C) (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have e₁ : |max (g₀ (ρ ω) - g₀ ω) 0| ≤ C := by
      rw [abs_le]
      constructor
      · linarith [le_max_right (g₀ (ρ ω) - g₀ ω) 0]
      · exact max_le (by linarith [(hg₀C (ρ ω)).2, (hg₀C ω).1]) hC
    have e₂ : |h ω - h (ρ ω)| ≤ C := by
      rw [abs_le]
      constructor <;> linarith [(hhC ω).1, (hhC ω).2, (hhC (ρ ω)).1, (hhC (ρ ω)).2]
    exact mul_le_mul e₁ e₂ (abs_nonneg _) hC
  have hgain : 0 < ∫ ω in {ω | 0 < inner ℝ (ω : E d) e}, D ω ∂σ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_forall_mem (measurableSet_inner_pos e) fun ω hω ↦ hD0 ω (le_of_lt hω))
      hDint.integrableOn]
    refine lt_of_lt_of_le hVpos (measure_mono fun ω hω ↦ ⟨(hDpos ω hω).ne', hω.1.1.1⟩)
  -- contradiction with minimality
  have hdist := integral_sq_sub_polarize he hg₀m hhm (C := C)
    (fun ω ↦ by rw [abs_of_nonneg (hg₀C ω).1]; exact (hg₀C ω).2)
    (fun ω ↦ by rw [abs_of_nonneg (hhC ω).1]; exact (hhC ω).2)
  have hmem := polarizeCM_mem_polarHull he hNe hg₀
  have hle : J g₀ ≤ J (polarizeCM e g₀) := hmin hmem
  rw [hJ _ hmem, hJ _ hg₀] at hle
  simp only [coe_polarizeCM] at hle
  change ∫ ω, (g₀ ω - h ω) ^ 2 ∂σ =
    ∫ ω, (polarize e g₀ ω - h ω) ^ 2 ∂σ + 2 * ∫ ω in {ω | 0 < inner ℝ (ω : E d) e}, D ω ∂σ
    at hdist
  linarith

end

end EllipticBernoulli
