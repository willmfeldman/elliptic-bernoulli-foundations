/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.PolarMinimizer
import EllipticBernoulli.Sphere.DirichletLSC

/-!
# The Pólya–Szegő inequality on the sphere

Let `d ≥ 2`, `|N| = 1`, and let `f : 𝕊 → [0, ∞)` be `L`-Lipschitz (chordal
metric). Then there is an `L`-Lipschitz `F : ℝ → [0, ∞)`, nonincreasing on `[0, π]`, such that
`f* = F ∘ φ` (`φ` the colatitude) satisfies

* (i) `σ{f* > t} = σ{f > t}` for all `t`, and `∫ (f*)² = ∫ f²`;
* (ii) `∫_𝕊 |∇(f*)^|² ≤ ∫_𝕊 |∇f̂|²`;
* (iii) `F = 0` on `[θ_f, π]` whenever `0 ≤ θ_f < π` and `σ(C(θ_f)) = σ{f > 0}`.

The proof is by polarization (for the method, see Brock–Solynin). The polarization hull of `f`
(`Sphere/PolarHull.lean`) contains an element `g₀` with `g₀ = f*` a.e.
(`exists_mem_polarHull_ae_eq_capRearrangement`, `Sphere/PolarMinimizer.lean`). It is radial,
because for two points `ω ≠ ω'` of equal colatitude the reflection `ρ_e`, `e = (ω - ω')/|ω - ω'|`,
fixes `N` (hence preserves `f*`) and swaps `ω` and `ω'`; continuity upgrades `g₀ ∘ ρ_e = g₀` a.e.
to everywhere. No rotation fixing `N` is used, so the argument covers `d = 2`. We read off
`F(θ) = g₀(cos θ N + sin θ P)` along a meridian (`P ⊥ N` a unit vector), which is `L`-Lipschitz
because the meridian is `1`-Lipschitz. Property (ii) is the lower semicontinuity of the Dirichlet
energy (`sphDirichlet_le_of_tendsto`) along a sequence of the orbit converging to `g₀`.

In (iii) the Lean statement assumes `θ_f < π`, which is the case used by the Faber–Krahn
inequality. The profile `F` is defined on all of `ℝ` and is globally `L`-Lipschitz and
nonnegative.

## References

* F. Brock, A. Yu. Solynin, *An approach to symmetrization via polarization*, Trans. Amer. Math.
  Soc. 352 (2000).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace InnerProductGeometry
open scoped NNReal Real ENNReal

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Auxiliary facts -/

/-- For `d ≥ 2` there is a unit vector orthogonal to `N`. -/
private theorem exists_unit_orthogonal (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) :
    ∃ P : E d, ‖P‖ = 1 ∧ inner ℝ N P = 0 := by
  set K : Submodule ℝ (E d) := (ℝ ∙ N)ᗮ
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hrank := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ N)
  rw [finrank_span_singleton hN0, finrank_euclideanSpace_fin] at hrank
  have hK : K ≠ ⊥ := by
    intro h
    have h0 : Module.finrank ℝ K = 0 := Submodule.finrank_eq_zero.2 h
    rw [h0] at hrank
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv0
  refine ⟨‖v‖⁻¹ • v, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne'], ?_⟩
  rw [inner_smul_right, (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).1 hv,
    mul_zero]

/-- The meridian point `cos θ N + sin θ P` (for unit `N ⊥ P`). -/
private noncomputable def meridian {N P : E d} (hN : ‖N‖ = 1) (hP : ‖P‖ = 1)
    (hNP : inner ℝ N P = 0) (θ : ℝ) : sphere (0 : E d) 1 :=
  ⟨Real.cos θ • N + Real.sin θ • P, by
    rw [mem_sphere_zero_iff_norm]
    refine (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).1 ?_
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hNP, hN, hP]
    simp only [Real.norm_eq_abs, mul_one, RCLike.conj_to_real, mul_zero, add_zero, one_pow]
    rw [sq_abs, sq_abs]
    nlinarith [Real.cos_sq_add_sin_sq θ]⟩

private theorem colatitude_meridian {N P : E d} (hN : ‖N‖ = 1) (hP : ‖P‖ = 1)
    (hNP : inner ℝ N P = 0) {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    colatitude N (meridian hN hP hNP θ) = θ := by
  rw [colatitude_eq_arccos hN, meridian]
  simp only
  rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, hN, hNP,
    one_pow, mul_one, mul_zero, add_zero, Real.arccos_cos hθ.1 hθ.2]

private theorem dist_meridian_le {N P : E d} (hN : ‖N‖ = 1) (hP : ‖P‖ = 1)
    (hNP : inner ℝ N P = 0) (a b : ℝ) :
    dist (meridian hN hP hNP a) (meridian hN hP hNP b) ≤ dist a b := by
  rw [Subtype.dist_eq, dist_eq_norm, Real.dist_eq]
  simp only [meridian]
  rw [show Real.cos a • N + Real.sin a • P - (Real.cos b • N + Real.sin b • P) =
    (Real.cos a - Real.cos b) • N + (Real.sin a - Real.sin b) • P by module]
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).1 ?_
  rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hNP, hN, hP,
    sq_abs]
  simp only [Real.norm_eq_abs, mul_one, RCLike.conj_to_real, mul_zero, add_zero]
  rw [sq_abs, sq_abs]
  have hc := Real.one_sub_sq_div_two_le_cos (x := a - b)
  rw [Real.cos_sub] at hc
  nlinarith [Real.cos_sq_add_sin_sq a, Real.cos_sq_add_sin_sq b]

/-- An open nonempty subset of the sphere meets every set of full measure. -/
private theorem exists_mem_of_ae {P : sphere (0 : E d) 1 → Prop}
    (hP : ∀ᵐ ω ∂(volume : Measure (E d)).toSphere, P ω) {V : Set (sphere (0 : E d) 1)}
    (hV : IsOpen V) (hne : V.Nonempty) : ∃ ω ∈ V, P ω := by
  by_contra h
  push Not at h
  have h0 : (volume : Measure (E d)).toSphere V = 0 :=
    measure_mono_null (fun ω hω ↦ h ω hω) (ae_iff.1 hP)
  exact (toSphere_pos_of_isOpen hV hne).ne' h0

/-- **Radiality.** If a continuous `g` is a.e. equal to the cap rearrangement `f*`, then `g`
depends only on the colatitude. -/
private theorem eq_of_colatitude_eq {N : E d} (hN : ‖N‖ = 1) {f : sphere (0 : E d) 1 → ℝ}
    {g : C(sphere (0 : E d) 1, ℝ)}
    (hg : ⇑g =ᵐ[(volume : Measure (E d)).toSphere] capRearrangement N f)
    {ω ω' : sphere (0 : E d) 1} (h : colatitude N ω = colatitude N ω') : g ω = g ω' := by
  by_cases hωω : (ω : E d) = ω'
  · rw [Subtype.ext hωω]
  set x : E d := (ω : E d)
  set y : E d := (ω' : E d)
  have hxy : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hωω)
  set e : E d := ‖x - y‖⁻¹ • (x - y)
  set R := polarReflection e
  set ρ := sphereMap R
  have hnx : ‖x‖ = 1 := norm_eq_of_mem_sphere ω
  have hny : ‖y‖ = 1 := norm_eq_of_mem_sphere ω'
  -- `ρ` swaps `ω` and `ω'`
  have hR : R = (ℝ ∙ (x - y))ᗮ.reflection := by
    simp only [R, polarReflection, e, Submodule.span_singleton_smul_eq (inv_pos.2 hxy).ne'.isUnit]
  have hρω : ρ ω = ω' := by
    ext1
    rw [coe_sphereMap, hR]
    exact Submodule.reflection_sub (by rw [hnx, hny])
  -- `ρ` fixes `N`, hence preserves colatitudes
  have hin : inner ℝ N x = inner ℝ N y := by
    have hbd : ∀ z : E d, ‖z‖ = 1 → inner ℝ N z ∈ Icc (-1 : ℝ) 1 := fun z hz ↦
      abs_le.1 ((abs_real_inner_le_norm N z).trans (by rw [hN, hz, one_mul]))
    refine Real.arccos_injOn (hbd x hnx) (hbd y hny) ?_
    rw [← colatitude_eq_arccos hN, ← colatitude_eq_arccos hN]
    exact h
  have hRN : R N = N := by
    refine Submodule.reflection_mem_subspace_eq_self
      ((Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).2 ?_)
    rw [inner_smul_left, inner_sub_left, real_inner_comm N x, real_inner_comm N y, hin, sub_self,
      mul_zero]
  have hcol : ∀ ν, colatitude N (ρ ν) = colatitude N ν := fun ν ↦ by
    rw [colatitude, colatitude, coe_sphereMap]
    calc angle (R ν) N = angle (R ν) (R N) := by rw [hRN]
      _ = angle (ν : E d) N := R.toLinearIsometry.angle_map _ _
  have hfρ : capRearrangement N f ∘ ρ = capRearrangement N f := by
    funext ν; simp only [Function.comp_apply, capRearrangement, hcol]
  -- `g ∘ ρ = g` a.e., hence everywhere
  have hmp := measurePreserving_sphereMap R
  have hae : ⇑g ∘ ρ =ᵐ[(volume : Measure (E d)).toSphere] ⇑g := by
    have h1 := hmp.quasiMeasurePreserving.ae_eq_comp hg
    rw [hfρ] at h1
    exact h1.trans hg.symm
  have heq := (Continuous.ae_eq_iff_eq _ (g.continuous.comp (continuous_sphereMap R))
    g.continuous).1 hae
  have := congrFun heq ω
  simp only [Function.comp_apply] at this
  rw [show sphereMap R ω = ω' from hρω] at this
  exact this.symm

/-- A continuous `F` that agrees `σ`-a.e. (along the colatitude) with an antitone `G` is
antitone on `[0, π]`. -/
private theorem antitoneOn_of_ae_eq {N P : E d} (hN : ‖N‖ = 1) (hP : ‖P‖ = 1)
    (hNP : inner ℝ N P = 0) {F G : ℝ → ℝ} (hF : Continuous F) (hG : Antitone G)
    (hae : ∀ᵐ ω ∂(volume : Measure (E d)).toSphere,
      F (colatitude N ω) = G (colatitude N ω)) : AntitoneOn F (Icc 0 π) := by
  intro a ha b hb hab
  by_contra hlt
  push Not at hlt
  have hab' : a < b := lt_of_le_of_ne hab (by rintro rfl; exact lt_irrefl _ hlt)
  obtain ⟨c, hc₁, hc₂⟩ : ∃ c, F a < c ∧ c < F b := ⟨(F a + F b) / 2, by linarith, by linarith⟩
  obtain ⟨m, hm₁, hm₂⟩ : ∃ m, a < m ∧ m < b := ⟨(a + b) / 2, by linarith, by linarith⟩
  have hφ := continuous_colatitude hN
  have hVa : IsOpen {ω : sphere (0 : E d) 1 | F (colatitude N ω) < c ∧ colatitude N ω < m} :=
    (isOpen_lt (hF.comp hφ) continuous_const).inter (isOpen_lt hφ continuous_const)
  have hVb : IsOpen {ω : sphere (0 : E d) 1 | c < F (colatitude N ω) ∧ m < colatitude N ω} :=
    (isOpen_lt continuous_const (hF.comp hφ)).inter (isOpen_lt continuous_const hφ)
  obtain ⟨ωa, ⟨hωa₁, hωa₂⟩, hωa⟩ := exists_mem_of_ae hae hVa
    ⟨meridian hN hP hNP a, by
      simp only [mem_ofPred_eq, colatitude_meridian hN hP hNP ha]
      exact ⟨hc₁, hm₁⟩⟩
  obtain ⟨ωb, ⟨hωb₁, hωb₂⟩, hωb⟩ := exists_mem_of_ae hae hVb
    ⟨meridian hN hP hNP b, by
      simp only [mem_ofPred_eq, colatitude_meridian hN hP hNP hb]
      exact ⟨hc₂, hm₂⟩⟩
  have := hG (le_of_lt (hωa₂.trans hωb₂))
  rw [← hωa, ← hωb] at this
  linarith

/-! ### The theorem -/

public section

/-- **Pólya–Szegő on the sphere.** Let `d ≥ 2`, `|N| = 1` and let
`f : 𝕊 → [0, ∞)` be `L`-Lipschitz. Then there is an `L`-Lipschitz `F : ℝ → [0, ∞)`, antitone on
`[0, π]`, such that `f* = F ∘ φ` satisfies:

* (i) `σ{f* > t} = σ{f > t}` for every `t`, and `∫_𝕊 (f*)² = ∫_𝕊 f²`;
* (ii) `∫_𝕊 |∇(f*)^|² ≤ ∫_𝕊 |∇f̂|²`;
* (iii) if `0 ≤ θ < π` and `σ(C(θ)) = σ{f > 0}`, then `F = 0` on `[θ, π]`.

In (iii) the Lean statement assumes `θ < π`. -/
theorem polya_szego (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {L : ℝ≥0}
    {f : sphere (0 : E d) 1 → ℝ} (hf : LipschitzWith L f) (hf0 : ∀ ω, 0 ≤ f ω) :
    ∃ F : ℝ → ℝ, LipschitzWith L F ∧ AntitoneOn F (Icc 0 π) ∧ (∀ φ, 0 ≤ F φ) ∧
      (∀ t, (volume : Measure (E d)).toSphere {ω | t < F (colatitude N ω)} =
        (volume : Measure (E d)).toSphere {ω | t < f ω}) ∧
      sphL2Sq (fun ω ↦ F (colatitude N ω)) = sphL2Sq f ∧
      sphDirichlet (fun ω ↦ F (colatitude N ω)) ≤ sphDirichlet f ∧
      ∀ θ, 0 ≤ θ → θ < π → (volume : Measure (E d)).toSphere (sphCap N θ) =
        (volume : Measure (E d)).toSphere {ω | 0 < f ω} → ∀ φ ∈ Icc θ π, F φ = 0 := by
  set σ := (volume : Measure (E d)).toSphere
  -- an upper bound
  have hbdd : BddAbove (range f) := (isCompact_range hf.continuous).bddAbove
  set M := sSup (range f)
  have hfM : ∀ ω, f ω ∈ Icc 0 M := fun ω ↦ ⟨hf0 ω, le_csSup hbdd (mem_range_self ω)⟩
  have hfle : ∀ ω, f ω ≤ M := fun ω ↦ (hfM ω).2
  have hfm : Measurable f := hf.continuous.measurable
  obtain ⟨g₀, hg₀, hae⟩ := exists_mem_polarHull_ae_eq_capRearrangement hd hN hf hfM
  have hg₀L := lipschitzWith_of_mem_polarHull hf hg₀
  -- the profile along a meridian
  obtain ⟨P, hP, hNP⟩ := exists_unit_orthogonal hd hN
  set F : ℝ → ℝ := fun θ ↦ g₀ (meridian hN hP hNP θ)
  have hrad : ∀ ω, F (colatitude N ω) = g₀ ω := fun ω ↦
    eq_of_colatitude_eq hN hae (colatitude_meridian hN hP hNP
      ⟨colatitude_nonneg N ω, colatitude_le_pi N ω⟩)
  have hFφ : (fun ω ↦ F (colatitude N ω)) = ⇑g₀ := funext hrad
  have hFL : LipschitzWith L F := LipschitzWith.of_dist_le_mul fun a b ↦
    (hg₀L.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (dist_meridian_le hN hP hNP a b) L.2)
  have hF0 : ∀ φ, 0 ≤ F φ := fun φ ↦ (mem_Icc_of_mem_polarHull hfM hg₀ _).1
  have hlev : ∀ t, σ {ω | t < F (colatitude N ω)} = σ {ω | t < f ω} := fun t ↦ by
    have h₁ := congrArg (fun μ : Measure ℝ ↦ μ (Ioi t)) (map_eq_of_mem_polarHull hfm hg₀)
    simp only [Measure.map_apply g₀.continuous.measurable measurableSet_Ioi,
      Measure.map_apply hfm measurableSet_Ioi] at h₁
    simp only [hrad]
    exact h₁
  have hanti : AntitoneOn F (Icc 0 π) := by
    refine antitoneOn_of_ae_eq hN hP hNP hFL.continuous (capProfile_antitone (N := N) hfle) ?_
    filter_upwards [hae] with ω hω
    rw [hrad, hω]
    rfl
  refine ⟨F, hFL, hanti, hF0, hlev, ?_, ?_, ?_⟩
  · -- (i), the `L²` norm
    rw [hFφ, sphL2Sq, sphL2Sq]
    have hmap := map_eq_of_mem_polarHull hfm hg₀ (N := N)
    have h₁ := integral_map (μ := σ) g₀.continuous.aemeasurable
      (f := fun x : ℝ ↦ x ^ 2) (continuous_pow 2).aestronglyMeasurable
    have h₂ := integral_map (μ := σ) hfm.aemeasurable
      (f := fun x : ℝ ↦ x ^ 2) (continuous_pow 2).aestronglyMeasurable
    rw [← h₁, ← h₂, hmap]
  · -- (ii), the Dirichlet energy
    rw [hFφ]
    obtain ⟨g, hgO, hlim⟩ := mem_closure_iff_seq_limit.1 hg₀
    exact sphDirichlet_le_of_tendsto (by omega) (fun k ↦ PolarOrbit.lipschitzWith hf (hgO k))
      hg₀L hlim fun k ↦ (PolarOrbit.sphDirichlet_eq hd hf (hgO k)).le
  · -- (iii), the support
    intro θ hθ0 hθπ hθ φ₀ hφ₀
    by_contra hne
    have hpos : 0 < F φ₀ := lt_of_le_of_ne (hF0 φ₀) (Ne.symm hne)
    -- a point `φ₁ ∈ (θ, π]` with `F φ₁ > 0`
    obtain ⟨φ₁, hθφ₁, hφ₁π, hφ₁⟩ : ∃ φ₁, θ < φ₁ ∧ φ₁ ≤ π ∧ 0 < F φ₁ := by
      rcases lt_or_eq_of_le hφ₀.1 with hlt | rfl
      · exact ⟨φ₀, hlt, hφ₀.2, hpos⟩
      · obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
          (hFL.continuous.continuousAt.eventually (lt_mem_nhds hpos))
        refine ⟨min (θ + δ / 2) π, lt_min (by linarith) hθπ, min_le_right _ _, hball ?_⟩
        rw [Real.dist_eq, abs_lt]
        constructor
        · have := lt_min (show θ < θ + δ / 2 by linarith) hθπ
          linarith
        · linarith [min_le_left (θ + δ / 2) π]
    have hφ₁mem : φ₁ ∈ Icc 0 π := ⟨by linarith, hφ₁π⟩
    have hsub : sphCap N φ₁ ⊆ {ω | 0 < F (colatitude N ω)} := fun ω hω ↦ by
      have hω' : colatitude N ω < φ₁ := hω
      exact lt_of_lt_of_le hφ₁
        (hanti ⟨colatitude_nonneg N ω, colatitude_le_pi N ω⟩ hφ₁mem hω'.le)
    have hlt := (toReal_toSphere_sphCap_lt_iff hd hN ⟨hθ0, hθπ.le⟩ hφ₁mem).2 hθφ₁
    have hle := measure_mono (μ := σ) hsub
    rw [hlev 0, ← hθ] at hle
    exact absurd hlt (not_lt.2 hle)

end

end EllipticBernoulli
