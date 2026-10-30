/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Defs
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.TwoPhase.EnergyIdentity
import EllipticBernoulli.Sobolev.Uniqueness
import EllipticBernoulli.Sobolev.Energy
import EllipticBernoulli.Harmonic.Basic
import EllipticBernoulli.Harmonic.WeylWeakGradient
import EllipticBernoulli.Harmonic.StrongMax
import EllipticBernoulli.Sobolev.Lattice
import EllipticBernoulli.Sobolev.ZeroExtension
import EllipticBernoulli.Nondegeneracy.Minimizer
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Two-phase basics: gradients and harmonicity

Throughout, `u : ℝᵈ → ℝ` is `L`-Lipschitz and a local minimizer of
`J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ` (`IsLocalEnergyMinimizer univ (fun _ ↦ 1) u`), with no
sign condition.

* `HasWeakGradient.ae_eq_gradient_of_lipschitzWith`: a weak gradient of a
  Lipschitz function on `ℝᵈ` is its pointwise gradient a.e.; consequently
  `IsLocalEnergyMinimizer.energyJ_gradient_le`: minimality holds with the pointwise gradient.
* `IsLocalEnergyMinimizer.integral_norm_sq_gradient_le`: minimality tested with a Lipschitz
  competitor that has the same positivity set.
* `IsLocalEnergyMinimizer.harmonicOnNhd_of_pos` and
  `IsLocalEnergyMinimizer.harmonicOnNhd_of_nonpos`: `u` is harmonic on every open set where `u > 0`,
  and on every open set where `u ≤ 0`. Hence `u` is harmonic on `{u > 0}`
  (`IsLocalEnergyMinimizer.harmonicOnNhd_posSet`), on `{u < 0}`
  (`IsLocalEnergyMinimizer.harmonicOnNhd_negSet`) and on the interior of `{u ≤ 0}`.

## Proof of harmonicity

For `φ ∈ C^∞_c(V)` and `t ∈ ℝ`, the competitor is `u + tφ` when `u > 0` on `V` (for small `|t|`,
which keeps the positivity set unchanged), and `min(u + tφ, max(u, 0))`, which equals
`min(u + tφ, 0)` on `V` and `u` off `spt φ`, when `u ≤ 0` on `V`. In both cases the positivity set
is that of `u` and `|∇v| ≤ |∇u + t∇φ|` a.e., so `∫ |∇u|² ≤ ∫ |∇u + t∇φ|²`, which forces
`∫ ∇u · ∇φ = 0`. Weyl's lemma (`harmonic_of_hasWeakGradient`) concludes.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient Laplacian NNReal ContDiff ENNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The weak gradient is the gradient -/

/-- **The weak gradient of a Lipschitz function is its gradient.** If `u` is
Lipschitz on `ℝᵈ` and `G` is a weak gradient of `u` on `ℝᵈ`, then `G = ∇u` a.e. -/
theorem HasWeakGradient.ae_eq_gradient_of_lipschitzWith {u : E d → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) {G : E d → E d} (hG : HasWeakGradient univ u G) :
    ∀ᵐ x, G x = ∇ u x := by
  have h := hG.ae_eq_of_eqOn isOpen_univ isOpen_univ subset_rfl
    (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hu.locallyLipschitz.locallyLipschitzOn).1 fun _ _ ↦ rfl
  rwa [Measure.restrict_univ] at h

/-- Minimality of a Lipschitz local minimizer holds with the pointwise gradient: for every ball
`B` and every `v ∈ H¹_loc(ℝᵈ)` with `v = u` a.e. off `B`, `J(u, B) ≤ J(v, B)` with `∇u` in place
of a weak gradient of `u`. -/
theorem IsLocalEnergyMinimizer.energyJ_gradient_le {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) (x : E d)
    (r : ℝ) {v : E d → ℝ} {Gv : E d → E d} (hv : MemH1Loc univ v Gv)
    (hvu : ∀ᵐ y ∂(volume.restrict (ball x r)ᶜ), v y = u y) :
    energyJ (ball x r) (fun _ ↦ 1) u (∇ u) ≤ energyJ (ball x r) (fun _ ↦ 1) v Gv := by
  obtain ⟨G, hG, hle⟩ := isLocalEnergyMinimizer_univ_iff.1 hmin
  rw [← energyJ_congr (fun _ _ ↦ rfl)
    (ae_restrict_of_ae (HasWeakGradient.ae_eq_gradient_of_lipschitzWith hu hG.1))]
  exact hle x r v Gv hv hvu

/-- The squared gradient of a Lipschitz function is integrable on a ball. -/
theorem integrableOn_norm_sq_gradient_ball {f : E d → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (z : E d) (r : ℝ) : IntegrableOn (fun x ↦ ‖∇ f x‖ ^ 2) (ball z r) := by
  refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) measure_ball_lt_top.ne
    ((measurable_gradient f).norm.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  rw [norm_pow, norm_norm]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ hf

/-- **Minimality against a Lipschitz competitor with the same positivity set.** If `w` is
Lipschitz, `w = u` off the ball `B`, and `w > 0 ↔ u > 0` on `B`, then
`∫_B |∇u|² ≤ ∫_B |∇w|²`. -/
theorem IsLocalEnergyMinimizer.integral_norm_sq_gradient_le {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) {w : E d → ℝ}
    {K : ℝ≥0} (hw : LipschitzWith K w) (z : E d) (r : ℝ) (hwu : ∀ x ∉ ball z r, w x = u x)
    (hpos : ∀ x ∈ ball z r, 0 < w x ↔ 0 < u x) :
    ∫ x in ball z r, ‖∇ u x‖ ^ 2 ≤ ∫ x in ball z r, ‖∇ w x‖ ^ 2 := by
  have hle := hmin.energyJ_gradient_le hu z r
    (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ hw.locallyLipschitz.locallyLipschitzOn)
    (ae_restrict_of_forall_mem measurableSet_ball.compl fun x hx ↦ hwu x hx)
  rw [energyJ_eq_add _ _ (measurable_gradient u).aestronglyMeasurable,
    energyJ_eq_add _ _ (measurable_gradient w).aestronglyMeasurable] at hle
  have hps : posSet w (ball z r) = posSet u (ball z r) := by
    ext x
    exact ⟨fun h ↦ ⟨h.1, (hpos x h.1).1 h.2⟩, fun h ↦ ⟨h.1, (hpos x h.1).2 h.2⟩⟩
  rw [hps] at hle
  have hfin : ∫⁻ x in ball z r,
      ENNReal.ofReal ((fun _ ↦ (1 : ℝ)) x ^ 2 * (posSet u (ball z r)).indicator 1 x) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in ball z r, 1) ?_ (lintegral_mono fun x ↦ ?_)
    · rw [setLIntegral_one]; exact measure_ball_lt_top.ne
    · refine ENNReal.ofReal_le_one.2 ?_
      by_cases hx : x ∈ posSet u (ball z r) <;> simp [hx]
  have h2 := (ENNReal.add_le_add_iff_right hfin).1 hle
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_norm_sq_gradient_ball hu z r)
      (ae_of_all _ fun _ ↦ sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_norm_sq_gradient_ball hw z r)
      (ae_of_all _ fun _ ↦ sq_nonneg _)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun _ ↦ sq_nonneg _)).1 h2

/-! ### The first variation -/


private theorem gradient_add_const_mul {f g : E d → ℝ} {x : E d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (t : ℝ) :
    ∇ (fun y ↦ f y + t * g y) x = ∇ f x + t • ∇ g x := by
  have h := (hf.hasFDerivAt.add (hg.hasFDerivAt.const_mul t))
  rw [hasFDerivAt_iff_hasGradientAt] at h
  change ∇ (f + fun y ↦ t * g y) x = _
  rw [h.gradient, map_add, map_smul]
  rfl

/-- The first variation. If `w` is Lipschitz, equals `u` off `spt φ`, has the positivity set of
`u`, and `|∇w| ≤ |∇u + t∇φ|` a.e., then `0 ≤ 2t ∫ ∇u · ∇φ + t² ∫ |∇φ|²`. -/
private theorem variation_nonneg {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) {φ : E d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) {t : ℝ} {w : E d → ℝ} {K : ℝ≥0}
    (hw : LipschitzWith K w) (hwu : ∀ x ∉ tsupport φ, w x = u x)
    (hpos : ∀ x, 0 < w x ↔ 0 < u x) (hgrad : ∀ᵐ x, ‖∇ w x‖ ≤ ‖∇ u x + t • ∇ φ x‖) :
    0 ≤ 2 * t * (∫ x, inner ℝ (∇ u x) (∇ φ x)) + t ^ 2 * ∫ x, ‖∇ φ x‖ ^ 2 := by
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_ball 0
  set B := ball (0 : E d) R
  obtain ⟨Kφ, hKφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  have hgφ : ∀ x, ‖∇ φ x‖ ≤ Kφ := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hKφ
  have hgu : ∀ x, ‖∇ u x‖ ≤ L := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hu
  have hφ0 : ∀ x ∉ B, ∇ φ x = 0 := fun x hx ↦
    gradient_eq_zero_of_notMem_tsupport fun h ↦ hx (hR h)
  have h1 : ∫ x in B, ‖∇ u x‖ ^ 2 ≤ ∫ x in B, ‖∇ w x‖ ^ 2 :=
    hmin.integral_norm_sq_gradient_le hu hw 0 R (fun x hx ↦ hwu x fun h ↦ hx (hR h))
    fun x _ ↦ hpos x
  have hbd : ∀ {f : E d → ℝ}, Measurable f → ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) → IntegrableOn f B :=
    fun hf C hC ↦ Measure.integrableOn_of_bounded (M := C) measure_ball_lt_top.ne
      hf.aestronglyMeasurable (Eventually.of_forall hC)
  have hmg := measurable_gradient u
  have hmφ := measurable_gradient φ
  have hiA : IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2) B := integrableOn_norm_sq_gradient_ball hu 0 R
  have hiI : IntegrableOn (fun x ↦ 2 * t * inner ℝ (∇ u x) (∇ φ x)) B :=
    hbd (measurable_const.mul (Measurable.inner hmg hmφ)) (|2 * t| * (L * Kφ)) fun x ↦ by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
        (mul_le_mul (hgu x) (hgφ x) (norm_nonneg _) L.2)) (abs_nonneg _)
  have hiP : IntegrableOn (fun x ↦ t ^ 2 * ‖∇ φ x‖ ^ 2) B :=
    hbd (measurable_const.mul (hmφ.norm.pow_const 2)) (t ^ 2 * Kφ ^ 2) fun x ↦ by
      rw [norm_mul, norm_pow, norm_pow, norm_norm, Real.norm_eq_abs, sq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hgφ x) 2)
        (sq_nonneg _)
  have hiAI : IntegrableOn (fun x ↦ ‖∇ u x‖ ^ 2 + 2 * t * inner ℝ (∇ u x) (∇ φ x)) B :=
    hiA.add hiI
  have h2 : ∫ x in B, ‖∇ w x‖ ^ 2 ≤ ∫ x in B, ‖∇ u x + t • ∇ φ x‖ ^ 2 := by
    refine setIntegral_mono_ae (integrableOn_norm_sq_gradient_ball hw 0 R) ?_ ?_
    · refine IntegrableOn.congr_fun ((hiA.add hiI).add hiP) (fun x _ ↦ ?_) measurableSet_ball
      simp only [Pi.add_apply]
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    · filter_upwards [hgrad] with x hx
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have eI : ∫ x, inner ℝ (∇ u x) (∇ φ x) = ∫ x in B, inner ℝ (∇ u x) (∇ φ x) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [hφ0 x hx]).symm
  have eP : ∫ x, ‖∇ φ x‖ ^ 2 = ∫ x in B, ‖∇ φ x‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by simp [hφ0 x hx]).symm
  have h3 : ∫ x in B, ‖∇ u x + t • ∇ φ x‖ ^ 2 = (∫ x in B, ‖∇ u x‖ ^ 2) +
      2 * t * (∫ x, inner ℝ (∇ u x) (∇ φ x)) + t ^ 2 * ∫ x, ‖∇ φ x‖ ^ 2 := by
    rw [eI, eP, ← integral_const_mul, ← integral_const_mul, ← integral_add hiA hiI,
      ← integral_add hiAI hiP]
    refine setIntegral_congr_fun measurableSet_ball fun x _ ↦ ?_
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  linarith

/-- An elementary fact: if `2ta + t²b ≥ 0` and `-2ta + t²b ≥ 0` for all `t ∈ (0, δ)`, then
`a = 0`. -/
private theorem eq_zero_of_forall_quadratic_nonneg {a b δ : ℝ} (hδ : 0 < δ)
    (h₁ : ∀ t, 0 < t → t < δ → 0 ≤ 2 * t * a + t ^ 2 * b)
    (h₂ : ∀ t, 0 < t → t < δ → 0 ≤ -(2 * t * a) + t ^ 2 * b) : a = 0 := by
  by_contra ha
  have ha' : 0 < |a| := abs_pos.2 ha
  set t := min (δ / 2) (|a| / (|b| + 1))
  have ht0 : 0 < t := lt_min (by linarith) (by positivity)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have htb : t * |b| < |a| := by
    calc t * |b| ≤ |a| / (|b| + 1) * |b| := mul_le_mul_of_nonneg_right (min_le_right _ _)
          (abs_nonneg _)
      _ < |a| / (|b| + 1) * (|b| + 1) := by
          apply mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = |a| := div_mul_cancel₀ _ (by positivity)
  have e1 := h₁ t ht0 htδ
  have e2 := h₂ t ht0 htδ
  have hb : t * b ≤ t * |b| := mul_le_mul_of_nonneg_left (le_abs_self b) ht0.le
  have key : 2 * |a| ≤ t * b := by
    rcases abs_cases a with ⟨h, -⟩ | ⟨h, -⟩
    · nlinarith
    · nlinarith
  linarith

/-- From the first variation to weak harmonicity: if every test function `φ` supported in `V`
admits, for some `δ > 0` and every `t` with `|t| < δ`, a competitor as in `variation_nonneg`,
then `u` is harmonic on `V`. -/
private theorem harmonicOnNhd_of_variation {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) {V : Set (E d)}
    (hV : IsOpen V)
    (hcomp : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∃ (w : E d → ℝ) (K : ℝ≥0), LipschitzWith K w ∧
        (∀ x ∉ tsupport φ, w x = u x) ∧ (∀ x, 0 < w x ↔ 0 < u x) ∧
        ∀ᵐ x, ‖∇ w x‖ ≤ ‖∇ u x + t • ∇ φ x‖) :
    HarmonicOnNhd u V := by
  have hG : HasWeakGradient V u (∇ u) :=
    (memH1Loc_gradient_of_locallyLipschitzOn hV hu.locallyLipschitz.locallyLipschitzOn).1
  have hweak : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
      ∫ x in V, inner ℝ (∇ u x) (∇ φ x) = 0 := by
    intro φ hφ hφc hφV
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [gradient_eq_zero_of_notMem_tsupport fun h ↦ hx (hφV h), inner_zero_right]]
    obtain ⟨δ, hδ, hw⟩ := hcomp φ hφ hφc hφV
    have hvar : ∀ t, |t| < δ →
        0 ≤ 2 * t * (∫ x, inner ℝ (∇ u x) (∇ φ x)) + t ^ 2 * ∫ x, ‖∇ φ x‖ ^ 2 := by
      intro t ht
      obtain ⟨w, K, hwL, hwu, hpos, hgrad⟩ := hw t ht
      exact variation_nonneg hmin hu hφ hφc hwL hwu hpos hgrad
    refine eq_zero_of_forall_quadratic_nonneg hδ (fun t ht0 htδ ↦ hvar t ?_)
      (fun t ht0 htδ ↦ ?_)
    · rwa [abs_of_pos ht0]
    · have := hvar (-t) (by rwa [abs_neg, abs_of_pos ht0])
      rw [neg_sq] at this
      linarith
  obtain ⟨hsm, hΔ⟩ := harmonic_of_hasWeakGradient hV hu.continuous.continuousOn hG hweak
  exact (harmonicOnNhd_iff_contDiffOn_laplacian_eq_zero hV).2
    ⟨hsm.of_le (by norm_cast), hΔ⟩

/-! ### Harmonicity in the two phases -/

private theorem lipschitzWith_const_mul' (t : ℝ) {φ : E d → ℝ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) : LipschitzWith (‖t‖₊ * K) fun x ↦ t * φ x :=
  (lipschitzWith_smul t).comp hφ

/-- **Harmonicity in the positive phase.** If `u > 0` on the open
set `V`, then `u` is harmonic on `V`. -/
theorem IsLocalEnergyMinimizer.harmonicOnNhd_of_pos {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) {V : Set (E d)}
    (hV : IsOpen V) (hpos : ∀ x ∈ V, 0 < u x) : HarmonicOnNhd u V := by
  refine harmonicOnNhd_of_variation hmin hu hV fun φ hφ hφc hφV ↦ ?_
  obtain ⟨Kφ, hKφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφc
  -- a positive lower bound for `u` on `spt φ`
  obtain ⟨δ₀, hδ₀, hδ₀u⟩ : ∃ δ₀ > 0, ∀ x ∈ tsupport φ, δ₀ ≤ u x := by
    rcases (tsupport φ).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x₀, hx₀, hmin₀⟩ := hφc.isCompact.exists_isMinOn h hu.continuous.continuousOn
      exact ⟨u x₀, hpos x₀ (hφV hx₀), fun x hx ↦ hmin₀ hx⟩
  set M' := max M 1
  have hM' : 0 < M' := lt_max_of_lt_right one_pos
  refine ⟨δ₀ / M', by positivity, fun t ht ↦ ⟨fun x ↦ u x + t * φ x, L + ‖t‖₊ * Kφ, ?_, ?_, ?_, ?_⟩⟩
  · exact hu.add (lipschitzWith_const_mul' t hKφ)
  · intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · intro x
    by_cases hx : x ∈ tsupport φ
    · have h1 : |t * φ x| < δ₀ := by
        rw [abs_mul]
        calc |t| * |φ x| ≤ |t| * M' :=
              mul_le_mul_of_nonneg_left ((hM x).trans (le_max_left _ _)) (abs_nonneg _)
          _ < δ₀ / M' * M' := mul_lt_mul_of_pos_right ht hM'
          _ = δ₀ := div_mul_cancel₀ _ hM'.ne'
      have h2 := hδ₀u x hx
      have h3 := neg_abs_le (t * φ x)
      constructor <;> intro _ <;> linarith
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · filter_upwards [hu.ae_differentiableAt] with x hx
    rw [gradient_add_const_mul hx (hφ.differentiable (by simp) x)]

/-- **Harmonicity in the nonpositive phase.** If `u ≤ 0` on the open
set `V`, then `u` is harmonic on `V`. The competitor is `min(u + tφ, max(u, 0))`: it equals
`min(u + tφ, 0)` on `V` and `u` off `spt φ`. -/
theorem IsLocalEnergyMinimizer.harmonicOnNhd_of_nonpos {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) {V : Set (E d)}
    (hV : IsOpen V) (hneg : ∀ x ∈ V, u x ≤ 0) : HarmonicOnNhd u V := by
  refine harmonicOnNhd_of_variation hmin hu hV fun φ hφ hφc hφV ↦ ⟨1, one_pos, fun t _ ↦ ?_⟩
  obtain ⟨Kφ, hKφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  set f : E d → ℝ := fun x ↦ u x + t * φ x with hf_def
  have hfL : LipschitzWith (L + ‖t‖₊ * Kφ) f := hu.add (lipschitzWith_const_mul' t hKφ)
  set w : E d → ℝ := fun x ↦ min (f x) (max (u x) 0) with hw_def
  have hwL : LipschitzWith (max (L + ‖t‖₊ * Kφ) (max L 0)) w :=
    hfL.min (hu.max (LipschitzWith.const 0))
  have hwu : ∀ x ∉ tsupport φ, w x = u x := fun x hx ↦ by
    simp [w, f, image_eq_zero_of_notMem_tsupport hx]
  refine ⟨w, _, hwL, hwu, fun x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ tsupport φ
    · have hux := hneg x (hφV hx)
      have : w x ≤ 0 := (min_le_right _ _).trans (by simp [hux])
      constructor <;> intro h <;> linarith
    · rw [hwu x hx]
  · filter_upwards [hu.ae_differentiableAt, hwL.ae_differentiableAt] with x hux hwx
    have hφx : DifferentiableAt ℝ φ x := hφ.differentiable (by simp) x
    rw [← gradient_add_const_mul hux hφx]
    by_cases hx : x ∈ tsupport φ
    · -- near `x`, `u ≤ 0`, so `w = min(f, 0)`
      have hVn : V ∈ 𝓝 x := hV.mem_nhds (hφV hx)
      have hloc : w =ᶠ[𝓝 x] fun y ↦ min (f y) 0 := by
        filter_upwards [hVn] with y hy
        simp [w, max_eq_right (hneg y hy)]
      rcases lt_trichotomy (f x) 0 with hlt | heq | hgt
      · have : w =ᶠ[𝓝 x] f := by
          filter_upwards [hloc, (isOpen_lt hfL.continuous continuous_const).mem_nhds hlt]
            with y hy hy'
          rw [hy, min_eq_left (le_of_lt hy')]
        rw [this.gradient_eq]
      · have hmax : IsLocalMax w x := by
          filter_upwards [hloc] with y hy
          rw [hy, show w x = 0 by simp [w, heq, max_eq_right (hneg x (hφV hx))]]
          exact min_le_right _ _
        have : ∇ w x = 0 := by
          rw [gradient, hmax.fderiv_eq_zero, map_zero]
        rw [this, norm_zero]
        exact norm_nonneg _
      · have : w =ᶠ[𝓝 x] fun _ ↦ 0 := by
          filter_upwards [hloc, (isOpen_lt continuous_const hfL.continuous).mem_nhds hgt]
            with y hy hy'
          rw [hy, min_eq_right (le_of_lt hy')]
        rw [this.gradient_eq, gradient_fun_const, norm_zero]
        exact norm_nonneg _
    · have hloc : w =ᶠ[𝓝 x] f := by
        filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
        rw [hwu y hy]
        simp [f, image_eq_zero_of_notMem_tsupport hy]
      rw [hloc.gradient_eq]

/-- `u` is harmonic on `{u > 0}`. -/
theorem IsLocalEnergyMinimizer.harmonicOnNhd_posSet {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) :
    HarmonicOnNhd u {x | 0 < u x} :=
  hmin.harmonicOnNhd_of_pos hu (isOpen_lt continuous_const hu.continuous) fun _ hx ↦ hx

/-- `u` is harmonic on `{u < 0}`. -/
theorem IsLocalEnergyMinimizer.harmonicOnNhd_negSet {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) :
    HarmonicOnNhd u {x | u x < 0} :=
  hmin.harmonicOnNhd_of_nonpos hu (isOpen_lt hu.continuous continuous_const) fun _ hx ↦
    le_of_lt hx

/-- `u` is harmonic on the interior of `{u ≤ 0}`. -/
theorem IsLocalEnergyMinimizer.harmonicOnNhd_interior_nonpos {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) :
    HarmonicOnNhd u (interior {x | u x ≤ 0}) :=
  hmin.harmonicOnNhd_of_nonpos hu isOpen_interior fun x hx ↦
    (interior_subset hx : x ∈ {x | u x ≤ 0})

/-- `u` is `C^∞` on `{u > 0}`. -/
theorem IsLocalEnergyMinimizer.contDiffOn_posSet {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) :
    ContDiffOn ℝ ∞ u {x | 0 < u x} :=
  HarmonicOnNhd.contDiffOn_top (isOpen_lt continuous_const hu.continuous)
    (hmin.harmonicOnNhd_posSet hu)

/-- `u` is `C^∞` on `{u < 0}`. -/
theorem IsLocalEnergyMinimizer.contDiffOn_negSet {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) :
    ContDiffOn ℝ ∞ u {x | u x < 0} :=
  HarmonicOnNhd.contDiffOn_top (isOpen_lt hu.continuous continuous_const)
    (hmin.harmonicOnNhd_negSet hu)

/-- `u⁺ = max(u, 0)` is harmonic on `{u⁺ > 0}`. -/
theorem IsLocalEnergyMinimizer.harmonicOnNhd_posPart {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) :
    HarmonicOnNhd (fun x ↦ max (u x) 0) {x | 0 < max (u x) 0} := by
  intro x hx
  have hx' : 0 < u x := by
    rw [mem_ofPred_eq] at hx
    rcases lt_max_iff.1 hx with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  have hloc : (fun y ↦ max (u y) 0) =ᶠ[𝓝 x] u := by
    filter_upwards [(isOpen_lt continuous_const hu.continuous).mem_nhds hx'] with y hy
    exact max_eq_left (le_of_lt hy)
  exact (harmonicAt_congr_nhds hloc).2 (hmin.harmonicOnNhd_posSet hu x hx')

/-- `u⁻ = max(-u, 0)` is harmonic on `{u⁻ > 0}`. -/
theorem IsLocalEnergyMinimizer.harmonicOnNhd_negPart {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) :
    HarmonicOnNhd (fun x ↦ max (-u x) 0) {x | 0 < max (-u x) 0} := by
  intro x hx
  have hx' : u x < 0 := by
    rw [mem_ofPred_eq] at hx
    rcases lt_max_iff.1 hx with h | h
    · linarith
    · exact absurd h (lt_irrefl 0)
  have hloc : (fun y ↦ max (-u y) 0) =ᶠ[𝓝 x] -u := by
    filter_upwards [(isOpen_lt hu.continuous continuous_const).mem_nhds hx'] with y hy
    simp only [Pi.neg_apply]
    exact max_eq_left (by linarith [show u y < 0 from hy])
  exact (harmonicAt_congr_nhds hloc).2 (hmin.harmonicOnNhd_negSet hu x hx').neg

/-- The energy identity for `u⁺`. -/
theorem IsLocalEnergyMinimizer.integral_norm_sq_gradient_posPart_mul_eq_neg {u : E d → ℝ}
    {L : ℝ≥0} (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u)
    {η : E d → ℝ} {Kη : ℝ≥0} (hη : LipschitzWith Kη η) (hηc : HasCompactSupport η) :
    ∫ x, ‖∇ (fun y ↦ max (u y) 0) x‖ ^ 2 * η x =
      -∫ x, max (u x) 0 * inner ℝ (∇ (fun y ↦ max (u y) 0) x) (∇ η x) :=
  integral_norm_sq_gradient_mul_eq_neg (hu.max (LipschitzWith.const 0))
    (fun _ ↦ le_max_right _ _) (hmin.harmonicOnNhd_posPart hu) hη hηc

/-- The energy identity for `u⁻`. -/
theorem IsLocalEnergyMinimizer.integral_norm_sq_gradient_negPart_mul_eq_neg {u : E d → ℝ}
    {L : ℝ≥0} (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u)
    {η : E d → ℝ} {Kη : ℝ≥0} (hη : LipschitzWith Kη η) (hηc : HasCompactSupport η) :
    ∫ x, ‖∇ (fun y ↦ max (-u y) 0) x‖ ^ 2 * η x =
      -∫ x, max (-u x) 0 * inner ℝ (∇ (fun y ↦ max (-u y) 0) x) (∇ η x) :=
  integral_norm_sq_gradient_mul_eq_neg (hu.neg.max (LipschitzWith.const 0))
    (fun _ ↦ le_max_right _ _) (hmin.harmonicOnNhd_negPart hu) hη hηc

/-! ### The boundary of the negative phase -/

/-- **The negative phase borders the positive phase.** If
`x₀ ∈ ∂{u < 0}`, then `u x₀ = 0` and `x₀ ∈ closure {u > 0}`. -/
theorem IsLocalEnergyMinimizer.apply_eq_zero_and_mem_closure_of_mem_frontier {u : E d → ℝ}
    {L : ℝ≥0} (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u)
    {x₀ : E d} (hx₀ : x₀ ∈ frontier {x | u x < 0}) :
    u x₀ = 0 ∧ x₀ ∈ closure {x | 0 < u x} := by
  have hopen : IsOpen {x | u x < 0} := isOpen_lt hu.continuous continuous_const
  rw [hopen.frontier_eq] at hx₀
  obtain ⟨hcl, hnot⟩ := hx₀
  have hle : u x₀ ≤ 0 :=
    closure_minimal (fun x (hx : u x < 0) ↦ (le_of_lt hx : u x ≤ 0))
      (isClosed_le hu.continuous continuous_const) hcl
  have h0 : u x₀ = 0 := le_antisymm hle (not_lt.1 hnot)
  refine ⟨h0, ?_⟩
  by_contra hcl'
  obtain ⟨δ, hδ, hδs⟩ : ∃ δ > 0, ∀ y, dist x₀ y < δ → u y ≤ 0 := by
    rw [Metric.mem_closure_iff] at hcl'
    push Not at hcl'
    obtain ⟨δ, hδ, h⟩ := hcl'
    exact ⟨δ, hδ, fun y hy ↦ not_lt.1 fun hy' ↦ (not_le.2 hy) (h y hy')⟩
  have hball : ∀ y ∈ ball x₀ δ, u y ≤ 0 := fun y hy ↦
    hδs y (by rw [dist_comm]; exact hy)
  have hharm := hmin.harmonicOnNhd_of_nonpos hu isOpen_ball hball
  have hconst := HarmonicOnNhd.eqOn_of_isMaxOn isOpen_ball (convex_ball x₀ δ).isPreconnected
    hharm (mem_ball_self hδ) fun y hy ↦ by
      simp only [mem_ofPred_eq, h0]; exact hball y hy
  obtain ⟨y, hy, hyneg⟩ := Metric.mem_closure_iff.1 hcl δ hδ
  have := hconst (show y ∈ ball x₀ δ by rw [mem_ball, dist_comm]; exact hyneg)
  simp only [h0] at this
  exact absurd this (ne_of_lt hy)

/-! ### `u⁺` is a downward minimizer -/

private theorem max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total a 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring

private theorem posSet_univ_eq (f : E d → ℝ) : posSet f univ = {x | 0 < f x} := by
  ext x
  simp [posSet]

/-- **`u⁺` is a downward minimizer.** For a Lipschitz local
minimizer `u` of `J` on `ℝᵈ`, `u⁺ = max(u, 0)` satisfies
`IsDownwardMinimizer univ (fun _ ↦ 1) u⁺`. The competitor for `v ≤ u⁺` is `v⁺ - u⁻`. -/
theorem IsLocalEnergyMinimizer.isDownwardMinimizer_posPart {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) :
    IsDownwardMinimizer univ (fun _ ↦ 1) (fun x ↦ max (u x) 0) := by
  set up : E d → ℝ := fun x ↦ max (u x) 0 with hup_def
  set um : E d → ℝ := fun x ↦ max (-u x) 0 with hum_def
  have hupL : LipschitzWith (max L 0) up := hu.max (LipschitzWith.const 0)
  have humL : LipschitzWith (max L 0) um := hu.neg.max (LipschitzWith.const 0)
  have hH1 : ∀ {f : E d → ℝ} {K : ℝ≥0}, LipschitzWith K f → MemH1Loc univ f (∇ f) :=
    fun hf ↦ memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hf.locallyLipschitz.locallyLipschitzOn
  have hGu : HasWeakGradient univ u (∇ u) := (hH1 hu).1
  -- gradients of the two phases
  have g1 : ∀ᵐ y, {x | 0 < u x}.indicator (∇ u) y = ∇ up y :=
    HasWeakGradient.ae_eq_gradient_of_lipschitzWith hupL (hGu.posPart isOpen_univ)
  have g2 : ∀ᵐ y, {x | 0 < -u x}.indicator (fun x ↦ -∇ u x) y = ∇ um y :=
    HasWeakGradient.ae_eq_gradient_of_lipschitzWith humL (hGu.neg.posPart isOpen_univ)
  have g3 : ∀ᵐ y, u y = 0 → ∇ u y = 0 := by
    have h := hGu.ae_eq_zero_of_eq_zero isOpen_univ
    rwa [Measure.restrict_univ] at h
  have hps : posSet up univ = {x | 0 < up x} := posSet_univ_eq up
  have hpos_open : IsOpen {x | 0 < up x} := isOpen_lt continuous_const hupL.continuous
  have hharm : HarmonicOnNhd up {x | 0 < up x} := hmin.harmonicOnNhd_posPart hu
  refine ⟨⟨_, hH1 hupL⟩, hps ▸ hpos_open, hps ▸ hharm.contDiffOn,
    hps ▸ fun x hx ↦ (hharm x hx).2.eq_of_nhds, ?_⟩
  intro z r _ _ Gu v Gv hGu' hv hvle hvB
  rw [Measure.restrict_univ] at hvle
  rw [← compl_eq_univ_sdiff] at hvB
  set B := ball z r
  have hB : MeasurableSet B := measurableSet_ball
  -- the competitor `w = v⁺ - u⁻`
  set w : E d → ℝ := fun y ↦ max (v y) 0 - um y
  set Gw : E d → E d := fun y ↦ {y | 0 < v y}.indicator Gv y - ∇ um y
  have hw : MemH1Loc univ w Gw := (memH1Loc_posPart isOpen_univ hv).sub (hH1 humL)
  have hwu : ∀ᵐ y ∂(volume.restrict Bᶜ), w y = u y := by
    filter_upwards [hvB] with y hy
    simp only [w, hy, up, um, max_eq_left (le_max_right (u y) 0), max_sub_max_neg]
  have hle := hmin.energyJ_gradient_le hu z r hw hwu
  -- the Dirichlet energy of `u⁻`
  set D : ℝ≥0∞ := ∫⁻ y in B, ENNReal.ofReal (‖∇ um y‖ ^ 2)
  have hDm : Measurable fun y ↦ ENNReal.ofReal (‖∇ um y‖ ^ 2) :=
    ((measurable_gradient um).norm.pow_const 2).ennreal_ofReal
  have hD : D ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in B, ENNReal.ofReal ((max L 0 : ℝ≥0) ^ 2)) ?_
      (lintegral_mono fun y ↦ ENNReal.ofReal_le_ofReal ?_)
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
    · refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      rw [norm_gradient_eq_norm_fderiv]
      exact norm_fderiv_le_of_lipschitz ℝ humL
  have hind : ∀ {f : E d → ℝ} {y : E d}, y ∈ B →
      (posSet f B).indicator (1 : E d → ℝ) y = if 0 < f y then 1 else 0 := by
    intro f y hy
    rw [posSet_indicator_one_eq hy]
    by_cases h : 0 < f y <;> simp [h]
  -- `J(u, B) = J(u⁺, B) + D`
  have hA : energyJ B (fun _ ↦ 1) u (∇ u) = energyJ B (fun _ ↦ 1) up (∇ up) + D := by
    unfold energyJ
    rw [← lintegral_add_right _ hDm]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae g1, ae_restrict_of_ae g2, ae_restrict_of_ae g3,
      ae_restrict_mem hB] with y h1 h2 h3 hy
    rw [hind hy, hind hy, ← h1, ← h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rcases lt_trichotomy (u y) 0 with h | h | h
    · simp [indicator, h, not_lt.2 h.le, up, max_eq_right h.le]
    · simp [indicator, h, h3 h, up]
    · simp [indicator, h, not_lt.2 h.le, up, max_eq_left h.le]
  -- `J(w, B) = J(v⁺, B) + D`
  have hB' : energyJ B (fun _ ↦ 1) w Gw = energyJ B (fun _ ↦ 1) (fun y ↦ max (v y) 0)
      ({y | 0 < v y}.indicator Gv) + D := by
    unfold energyJ
    rw [← lintegral_add_right _ hDm]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae g2, ae_restrict_of_ae hvle, ae_restrict_mem hB]
      with y h2 hvy hy
    rw [hind hy, hind hy, ← h2, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    rcases lt_or_ge (u y) 0 with h | h
    · have h' : 0 < -u y := by linarith
      have hv0 : ¬ 0 < v y := fun hv0 ↦ by
        have : up y = 0 := max_eq_right h.le
        linarith
      have hw0 : ¬ 0 < w y := by
        simp only [w, um, max_eq_right (not_lt.1 hv0), max_eq_left h'.le]
        linarith
      simp [Gw, ← h2, indicator, h, hv0, hw0, max_eq_right (not_lt.1 hv0)]
    · have hwv : w y = max (v y) 0 := by
        simp only [w, um, max_eq_right (show -u y ≤ 0 by linarith), sub_zero]
      simp [Gw, ← h2, indicator, not_lt.2 h, hwv]
  -- conclude
  have hGu'' : energyJ B (fun _ ↦ 1) up Gu = energyJ B (fun _ ↦ 1) up (∇ up) :=
    energyJ_congr (fun _ _ ↦ rfl)
      (ae_restrict_of_ae (HasWeakGradient.ae_eq_gradient_of_lipschitzWith hupL hGu'.1))
  rw [hGu'']
  have hfin := (ENNReal.add_le_add_iff_right hD).1
    ((hA.symm.trans_le hle).trans (hB'.trans_le (add_le_add_left (energyJ_posPart_le _ _ _ _) _)))
  exact hfin

/-- **All-scales non-degeneracy of the positive phase.** For
`d ≥ 1`, every `z ∈ closure {u > 0}` and every `r > 0`, there is `y ∈ B̄_r(z)` with
`u(y) ≥ c_d r`, `c_d = 1 / (8 d e^{d/2})`. -/
theorem IsLocalEnergyMinimizer.exists_le_of_mem_closure_posSet (hd : 1 ≤ d) {u : E d → ℝ}
    {L : ℝ≥0} (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u)
    {z : E d} (hz : z ∈ closure {x | 0 < u x}) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ closedBall z r, 1 / (8 * d * Real.exp ((d : ℝ) / 2)) * r ≤ u y := by
  have hset : posSet (fun x ↦ max (u x) 0) univ = {x | 0 < u x} := by
    ext x
    simp [posSet]
  obtain ⟨y, hy, hle⟩ := IsDownwardMinimizer.exists_le_of_closedBall_subset hd isOpen_univ
    (hmin.isDownwardMinimizer_posPart hu)
    (hu.max (LipschitzWith.const 0)).locallyLipschitz.locallyLipschitzOn
    (fun _ _ ↦ le_max_right _ _) one_pos (fun _ _ ↦ le_rfl) ⟨1, fun _ _ ↦ le_rfl⟩
    measurable_const z (hset ▸ hz) r hr (subset_univ _)
  refine ⟨y, hy, ?_⟩
  have hc : 0 < 1 / (8 * d * Real.exp ((d : ℝ) / 2)) * r := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hpos : 0 < max (u y) 0 := hc.trans_le hle
  rwa [max_eq_left (le_of_lt (by
    rcases lt_max_iff.1 hpos with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)))] at hle

end EllipticBernoulli
