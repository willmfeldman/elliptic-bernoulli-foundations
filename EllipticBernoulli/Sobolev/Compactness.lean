/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.LocalCompactness
public import EllipticBernoulli.Sobolev.TranslationEstimate
public import EllipticBernoulli.Sobolev.Lipschitz

/-!
# Local Rellich compactness

A sequence bounded in `H¹_loc(U)` (weak gradients carried as data) has a subsequence
converging in `L²_loc(U)`.

Proof: for a smooth cut-off `ζ` compactly supported in `U`, `w_n = ζ u_n` has the weak gradient
`Γ_n = ζ G_n + u_n ∇ζ` on the whole space, so `‖w_n(· + h) - w_n‖₂ ≤ |h| ‖Γ_n‖₂`
(`eLpNorm_comp_add_sub_le_of_weakGradient`), and `‖w_n‖₂, ‖Γ_n‖₂` are bounded by the `L²` bounds
on `tsupport ζ`. Conclude with `exists_tendstoLpLoc_subseq_of_cutoff`.

## Main results

* `hasWeakGradientUniv_mul_cutoff`: the product rule with a cut-off.
* `exists_tendstoLpLoc_subseq_of_H1Loc`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ContDiff Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- A function supported in a measurable set `T`, dominated there by `Z |g|` with `g ∈ L²(T)`, is
in `L²` with `‖f‖₂ ≤ Z ‖g‖_{L²(T)}`. -/
theorem memLp_two_and_eLpNorm_le_of_restrict {F F' : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup F'] {T : Set (E d)} (hT : MeasurableSet T) {g : E d → F} {f : E d → F'}
    (hg : MemLp g 2 (volume.restrict T)) (hf : AEStronglyMeasurable f (volume.restrict T))
    {Z : ℝ} (hfg : ∀ x, ‖f x‖ ≤ Z * ‖g x‖) (hf0 : ∀ x ∉ T, f x = 0) :
    MemLp f 2 volume ∧ eLpNorm f 2 volume ≤ ENNReal.ofReal Z * eLpNorm g 2 (volume.restrict T) := by
  have hind : T.indicator f = f := indicator_eq_self.2 fun x hx ↦ by
    by_contra h; exact hx (hf0 x h)
  constructor
  · rw [← hind, memLp_indicator_iff_restrict hT]
    exact hg.of_le_mul hf (Eventually.of_forall hfg)
  · rw [← hind, eLpNorm_indicator_eq_eLpNorm_restrict hT]
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul hf (Eventually.of_forall hfg) 2

/-- **Product rule with a cut-off.** If `G` is a weak gradient of `u` in `U`, `u, G` are locally
integrable on `U`, and `ζ ∈ C^∞_c` with `tsupport ζ ⊆ U`, then `ζ u` has the weak gradient
`ζ G + u ∇ζ` on the whole space. -/
theorem hasWeakGradientUniv_mul_cutoff {U : Set (E d)} {u : E d → ℝ}
    {G : E d → E d} (hG : HasWeakGradient U u G) {ζ : E d → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) (hζU : tsupport ζ ⊆ U) :
    HasWeakGradientUniv (fun x ↦ ζ x * u x) (fun x ↦ ζ x • G x + u x • ∇ ζ x) := by
  intro φ hφ hφc v
  set T := tsupport ζ
  have hT : IsCompact T := hζc
  have hTU : T ⊆ U := hζU
  have huT : IntegrableOn u T := hG.1.mono_set hTU |>.integrableOn_isCompact hT
  have hGT : IntegrableOn (fun x ↦ inner ℝ (G x) v) T :=
    ((hG.2.1.mono_set hTU).integrableOn_isCompact hT).inner_const v
  set ψ : E d → ℝ := fun x ↦ ζ x * φ x
  have hψ : ContDiff ℝ ∞ ψ := hζ.mul hφ
  have hψc : HasCompactSupport ψ := hζc.mul_right
  have hψT : tsupport ψ ⊆ T := tsupport_mul_subset_left
  have hdiff : ∀ x, fderiv ℝ ψ x v = ζ x * fderiv ℝ φ x v + φ x * fderiv ℝ ζ x v := by
    intro x
    have h1 : DifferentiableAt ℝ ζ x := hζ.differentiable (by simp) x
    have h2 : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
    rw [show ψ = fun y ↦ ζ y * φ y from rfl, fderiv_fun_mul h1 h2]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by exact_mod_cast le_top)
  have hcont_dζ : Continuous fun x ↦ fderiv ℝ ζ x v :=
    (hζ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcont_dψ : Continuous fun x ↦ fderiv ℝ ψ x v :=
    ((hψ.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 ψ).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  -- vanishing off `T`
  have hζ0 : ∀ x ∉ T, ζ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hdζ0 : ∀ x ∉ T, fderiv ℝ ζ x v = 0 := fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (tsupport_fderiv_subset ℝ h))]; rfl
  have hdψ0 : ∀ x ∉ T, fderiv ℝ ψ x v = 0 := fun x hx ↦ by
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hψT (tsupport_fderiv_subset ℝ h)))]; rfl
  -- integrability of the pieces (all supported in `T`)
  have hint : ∀ {g c : E d → ℝ}, IntegrableOn g T → Continuous c → (∀ x ∉ T, c x = 0) →
      Integrable fun x ↦ g x * c x := by
    intro g c hg hc hc0
    refine (hg.mul_continuousOn hc.continuousOn hT).integrable_of_forall_notMem_eq_zero
      fun x hx ↦ by rw [hc0 x hx, mul_zero]
  have i1 : Integrable fun x ↦ u x * fderiv ℝ ψ x v := hint huT hcont_dψ hdψ0
  have i2 : Integrable fun x ↦ u x * (φ x * fderiv ℝ ζ x v) :=
    hint huT (hφ.continuous.mul hcont_dζ) fun x hx ↦ by rw [hdζ0 x hx, mul_zero]
  have i3 : Integrable fun x ↦ inner ℝ (G x) v * (ζ x * φ x) :=
    hint hGT (hζ.continuous.mul hφ.continuous) fun x hx ↦ by rw [hζ0 x hx, zero_mul]
  -- the weak-gradient identity for the test function `ψ = ζ φ`
  have hwg := hG.2.2 ψ hψ hψc (hψT.trans hTU) v
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      rw [hdψ0 x (fun h ↦ hx (hTU h)), mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
      simp only [ψ, hζ0 x (fun h ↦ hx (hTU h)), zero_mul, mul_zero])] at hwg
  have eL : (fun x ↦ ζ x * u x * fderiv ℝ φ x v) =
      fun x ↦ u x * fderiv ℝ ψ x v - u x * (φ x * fderiv ℝ ζ x v) := by
    funext x; rw [hdiff]; ring
  have eR : (fun x ↦ inner ℝ (ζ x • G x + u x • ∇ ζ x) v * φ x) =
      fun x ↦ inner ℝ (G x) v * (ζ x * φ x) + u x * (φ x * fderiv ℝ ζ x v) := by
    funext x
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_gradient_left_eq_fderiv]
    ring
  rw [eL, eR, integral_sub i1 i2, integral_add i3 i2, hwg]
  ring

/-- Choice of `δ` for a linear translation modulus `|h| B`. -/
theorem exists_pos_ofReal_mul_le {B : ℝ≥0∞} (hB : B ≠ ⊤) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ r : ℝ, r < δ → ENNReal.ofReal r * B ≤ ε := by
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact ⟨1, one_pos, fun _ _ ↦ le_top⟩
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  refine ⟨ε.toReal / (B.toReal + 1), by positivity, fun r hr ↦ ?_⟩
  rcases le_or_gt r 0 with hr0 | hr0
  · rw [ENNReal.ofReal_of_nonpos hr0, zero_mul]; exact zero_le
  rw [← ENNReal.ofReal_toReal hB, ← ENNReal.ofReal_mul hr0.le, ← ENNReal.ofReal_toReal hεt]
  refine ENNReal.ofReal_le_ofReal ?_
  have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have : r * (B.toReal + 1) ≤ ε.toReal := by
    rw [lt_div_iff₀ (by positivity)] at hr; linarith
  nlinarith

/-- **Local Rellich compactness.** -/
theorem exists_tendstoLpLoc_subseq_of_H1Loc {U : Set (E d)} (hU : IsOpen U)
    (u : ℕ → E d → ℝ) (G : ℕ → E d → E d) (hG : ∀ n, MemH1Loc U (u n) (G n))
    (hbdd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ, ∀ n,
      eLpNorm (u n) 2 (volume.restrict K) ≤ ENNReal.ofReal C ∧
        eLpNorm (G n) 2 (volume.restrict K) ≤ ENNReal.ofReal C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ u₀ : E d → ℝ, Measurable u₀ ∧
      TendstoLpLoc 2 volume U (fun n ↦ u (φ n)) u₀ atTop := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  refine exists_tendstoLpLoc_subseq_of_cutoff (by norm_num) hU u ?_
  intro ζ hζ hζc hζU hζ01
  set T := tsupport ζ
  have hT : IsCompact T := hζc
  have hTm : MeasurableSet T := hT.measurableSet
  obtain ⟨C, hC⟩ := hbdd T hζU hT
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by exact_mod_cast le_top)
  obtain ⟨Z, hZ⟩ := (hζ1.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hζc.fderiv (𝕜 := ℝ))
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hZ 0)
  have hζ0 : ∀ x ∉ T, ζ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  have hgr0 : ∀ x ∉ T, ∇ ζ x = 0 := fun x hx ↦ by
    rw [← norm_eq_zero, norm_gradient_eq_norm_fderiv,
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (tsupport_fderiv_subset ℝ h)), norm_zero]
  have huT : ∀ n, MemLp (u n) 2 (volume.restrict T) := fun n ↦ ((hG n).2 T hζU hT).1
  have hGT : ∀ n, MemLp (G n) 2 (volume.restrict T) := fun n ↦ ((hG n).2 T hζU hT).2
  -- `w_n = ζ u_n`
  have hw : ∀ n, MemLp (fun x ↦ ζ x * u n x) 2 volume ∧
      eLpNorm (fun x ↦ ζ x * u n x) 2 volume ≤ ENNReal.ofReal 1 * eLpNorm (u n) 2
        (volume.restrict T) := fun n ↦
    memLp_two_and_eLpNorm_le_of_restrict (f := fun x ↦ ζ x * u n x) hTm (huT n)
      (hζ.continuous.aestronglyMeasurable.mul (huT n).aestronglyMeasurable)
      (fun x ↦ by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hζ01 x).1]
        exact mul_le_mul_of_nonneg_right (hζ01 x).2 (norm_nonneg _))
      (fun x hx ↦ by simp only [hζ0 x hx, zero_mul])
  -- `Γ_n = ζ G_n + u_n ∇ζ`
  have hΓ1 : ∀ n, MemLp (fun x ↦ ζ x • G n x) 2 volume ∧
      eLpNorm (fun x ↦ ζ x • G n x) 2 volume ≤ ENNReal.ofReal 1 * eLpNorm (G n) 2
        (volume.restrict T) := fun n ↦
    memLp_two_and_eLpNorm_le_of_restrict (f := fun x ↦ ζ x • G n x) hTm (hGT n)
      (hζ.continuous.aestronglyMeasurable.smul (hGT n).aestronglyMeasurable)
      (fun x ↦ by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hζ01 x).1]
        exact mul_le_mul_of_nonneg_right (hζ01 x).2 (norm_nonneg _))
      (fun x hx ↦ by simp only [hζ0 x hx, zero_smul])
  have hcgr : Continuous (∇ ζ) :=
    (InnerProductSpace.toDual ℝ (E d)).symm.continuous.comp
      (hζ1.continuous_fderiv one_ne_zero)
  have hΓ2 : ∀ n, MemLp (fun x ↦ u n x • ∇ ζ x) 2 volume ∧
      eLpNorm (fun x ↦ u n x • ∇ ζ x) 2 volume ≤ ENNReal.ofReal Z * eLpNorm (u n) 2
        (volume.restrict T) := fun n ↦
    memLp_two_and_eLpNorm_le_of_restrict (f := fun x ↦ u n x • ∇ ζ x) hTm (huT n)
      ((huT n).aestronglyMeasurable.smul hcgr.aestronglyMeasurable)
      (fun x ↦ by
        rw [norm_smul, norm_gradient_eq_norm_fderiv, mul_comm]
        exact mul_le_mul_of_nonneg_right (hZ x) (norm_nonneg _))
      (fun x hx ↦ by simp only [hgr0 x hx, smul_zero])
  set B : ℝ≥0∞ := ENNReal.ofReal C + ENNReal.ofReal Z * ENNReal.ofReal C
  have hBt : B ≠ ⊤ := by finiteness
  have hΓ : ∀ n, MemLp (fun x ↦ ζ x • G n x + u n x • ∇ ζ x) 2 volume ∧
      eLpNorm (fun x ↦ ζ x • G n x + u n x • ∇ ζ x) 2 volume ≤ B := by
    intro n
    refine ⟨(hΓ1 n).1.add (hΓ2 n).1, ?_⟩
    refine (eLpNorm_add_le (by norm_num)).trans (add_le_add ?_ ?_)
    · simpa using (hΓ1 n).2.trans (by rw [ENNReal.ofReal_one, one_mul]; exact (hC n).2)
    · exact (hΓ2 n).2.trans (mul_le_mul' le_rfl (hC n).1)
  refine ⟨fun n ↦ (hw n).1, ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun n ↦
    (hw n).2.trans (by rw [ENNReal.ofReal_one, one_mul]; exact (hC n).1)⟩, fun ε hε ↦ ?_⟩
  obtain ⟨δ, hδ, hδε⟩ := exists_pos_ofReal_mul_le hBt hε
  refine ⟨δ, hδ, fun n h hh ↦ ?_⟩
  have hwg := hasWeakGradientUniv_mul_cutoff (hG n).1 hζ hζc hζU
  refine (eLpNorm_comp_add_sub_le_of_weakGradient (hw n).1 (hΓ n).1 hwg h).trans ?_
  exact (mul_le_mul' le_rfl (hΓ n).2).trans (hδε _ hh)

end EllipticBernoulli
