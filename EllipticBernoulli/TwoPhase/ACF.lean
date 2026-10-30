/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Regularity
public import EllipticBernoulli.Statements.TwoPhase
public import EllipticBernoulli.TwoPhase.ACFCore
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Alt–Caffarelli–Friedman monotonicity modulo Friedland–Hayman

* `acfMonotoneIn_of_friedlandHayman`: for `d ≥ 2`, the Friedland–Hayman inequality
  `FriedlandHaymanIn d` implies the ACF monotonicity formula `ACFMonotoneIn d`: for an ACF pair
  `(u₁, u₂)` at `x₀`, `r ↦ Φ(u₁, u₂, x₀, r) = r⁻⁴ I(u₁, x₀, r) I(u₂, x₀, r)` is nondecreasing on
  `(0, ∞)`.

Bounds and scaling, for `L`-Lipschitz functions:

* `acfIntegral_le`: `I(w, x₀, r) ≤ L² σ(𝕊) r²/2`, and `acfPhi_le`: `Φ ≤ L⁴ σ(𝕊)²/4`;
* `acfIntegral_blowup`: `I(w_{x₀,R}, 0, ρ) = R⁻² I(w, x₀, Rρ)` for the rescaling
  `w_{x₀,R}(y) = w(x₀ + Ry)/R` (`blowup`), and `acfPhi_blowup`:
  `Φ(u₁_{x₀,R}, u₂_{x₀,R}, 0, ρ) = Φ(u₁, u₂, x₀, Rρ)`.

## Proof

`Φ` is absolutely continuous on every `[a, b] ⊆ (0, ∞)`, since each `I(uᵢ, x₀, ·)` is Lipschitz
on `[0, b]`. For a.e. `r > 0`,
`r⁵ Φ'(r) = r I₁'(r) I₂(r) + r I₁(r) I₂'(r) - 4 I₁(r) I₂(r)` with `Iᵢ' = r qᵢ`. If some
`Γⁱ_r = {ω : uᵢ(x₀ + rω) > 0}` is empty, then `Iᵢ(r) = 0` and `r⁵ Φ' = r Iᵢ' Iⱼ ≥ 0`. Otherwise
`Γ¹_r, Γ²_r` are nonempty, open and disjoint, and the key inequality
(`two_mul_sphExponent_mul_acfIntegral_le`) and Friedland–Hayman give
`r⁵ Φ' ≥ (2 α_d(Γ¹_r) + 2 α_d(Γ²_r) - 4) I₁ I₂ ≥ 0`.

The statement and the strategy follow Salato (arXiv:2506.13473, v2), Theorem 1.1 and §5,
Steps 1–2; the key inequality is Salato's (38), proved here by completing a square.

Salato works on a ball `B₂ ⊆ ℝⁿ`, `n ≥ 3`, with continuous `u±` that are subharmonic in the
distributional sense on their positivity sets, and presents Step 1 for `C²` functions. Here an
ACF pair consists of globally Lipschitz functions on `ℝᵈ`, `d ≥ 2`, that are harmonic on their
positivity sets, monotonicity is asserted on `(0, ∞)`, and the argument is carried out for
Lipschitz functions throughout.

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473 (v2).
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and
  the growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
-/

open MeasureTheory Metric Set Filter Topology
open scoped Gradient NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

theorem acfIntegral_nonneg (w : E d → ℝ) (x₀ : E d) (r : ℝ) : 0 ≤ acfIntegral w x₀ r :=
  setIntegral_nonneg measurableSet_ball fun _ _ ↦
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)

/-- The numerator of `r⁵ Φ'(r)` is nonnegative: with `Dᵢ = r qᵢ(r) = Iᵢ'(r)`,
`r D₁ I₂ + r I₁ D₂ - 4 I₁ I₂ ≥ 0`, at every radius where the key inequality holds for both
members of the pair. -/
private theorem acf_numerator_nonneg {u₁ u₂ : E d → ℝ} {x₀ : E d} {L : ℝ≥0}
    (h : IsACFPair u₁ u₂ x₀ L) (hFH : FriedlandHaymanIn d) {r : ℝ} (hr : 0 < r)
    (hK₁ : {ω : sphere (0 : E d) 1 | 0 < u₁ (x₀ + r • (ω : E d))}.Nonempty →
      2 * sphExponent {ω : sphere (0 : E d) 1 | 0 < u₁ (x₀ + r • (ω : E d))} *
        acfIntegral u₁ x₀ r ≤ r * (r * radialQ u₁ x₀ r))
    (hK₂ : {ω : sphere (0 : E d) 1 | 0 < u₂ (x₀ + r • (ω : E d))}.Nonempty →
      2 * sphExponent {ω : sphere (0 : E d) 1 | 0 < u₂ (x₀ + r • (ω : E d))} *
        acfIntegral u₂ x₀ r ≤ r * (r * radialQ u₂ x₀ r))
    (hE₁ : {ω : sphere (0 : E d) 1 | 0 < u₁ (x₀ + r • (ω : E d))} = ∅ → acfIntegral u₁ x₀ r = 0)
    (hE₂ : {ω : sphere (0 : E d) 1 | 0 < u₂ (x₀ + r • (ω : E d))} = ∅ → acfIntegral u₂ x₀ r = 0) :
    0 ≤ r * (r * radialQ u₁ x₀ r) * acfIntegral u₂ x₀ r +
      r * acfIntegral u₁ x₀ r * (r * radialQ u₂ x₀ r) -
        4 * acfIntegral u₁ x₀ r * acfIntegral u₂ x₀ r := by
  have hI₁ := acfIntegral_nonneg u₁ x₀ r
  have hI₂ := acfIntegral_nonneg u₂ x₀ r
  have hq₁ := radialQ_nonneg u₁ x₀ r
  have hq₂ := radialQ_nonneg u₂ x₀ r
  rcases eq_empty_or_nonempty {ω : sphere (0 : E d) 1 | 0 < u₁ (x₀ + r • (ω : E d))} with
    hΓ₁ | hΓ₁
  · rw [hE₁ hΓ₁]
    have : 0 ≤ r * (r * radialQ u₁ x₀ r) * acfIntegral u₂ x₀ r := by positivity
    linarith
  rcases eq_empty_or_nonempty {ω : sphere (0 : E d) 1 | 0 < u₂ (x₀ + r • (ω : E d))} with
    hΓ₂ | hΓ₂
  · rw [hE₂ hΓ₂]
    have : 0 ≤ r * acfIntegral u₁ x₀ r * (r * radialQ u₂ x₀ r) := by positivity
    linarith
  have hopen : ∀ {u : E d → ℝ}, LipschitzWith L u →
      IsOpen {ω : sphere (0 : E d) 1 | 0 < u (x₀ + r • (ω : E d))} := fun hu ↦
    isOpen_lt continuous_const (hu.continuous.comp (by fun_prop))
  have hdisj : Disjoint {ω : sphere (0 : E d) 1 | 0 < u₁ (x₀ + r • (ω : E d))}
      {ω : sphere (0 : E d) 1 | 0 < u₂ (x₀ + r • (ω : E d))} :=
    disjoint_left.mpr fun ω h₁ h₂ ↦ by
      have := h.mul_eq_zero (x₀ + r • (ω : E d))
      have := mul_pos (show 0 < u₁ (x₀ + r • (ω : E d)) from h₁)
        (show 0 < u₂ (x₀ + r • (ω : E d)) from h₂)
      linarith
  have hfh := hFH _ _ (hopen h.lipschitz_left) (hopen h.lipschitz_right) hΓ₁ hΓ₂ hdisj
  nlinarith [mul_le_mul_of_nonneg_right (hK₁ hΓ₁) hI₂, mul_le_mul_of_nonneg_left (hK₂ hΓ₂) hI₁,
    mul_nonneg (sub_nonneg.mpr hfh) (mul_nonneg hI₁ hI₂)]

/-- **ACF monotonicity modulo Friedland–Hayman** (Alt–Caffarelli–Friedman 1984; Salato,
arXiv:2506.13473, Theorem 1.1). For `d ≥ 2`, the Friedland–Hayman inequality in dimension `d`
implies that `r ↦ Φ(u₁, u₂, x₀, r)` is nondecreasing on `(0, ∞)` for every ACF pair `(u₁, u₂)` at
`x₀`. An ACF pair consists of nonnegative, globally Lipschitz functions, harmonic on their
positivity sets, with disjoint positivity sets and vanishing at `x₀`; the sources assume
continuous functions that are subharmonic on their positivity sets. -/
theorem acfMonotoneIn_of_friedlandHayman (hd : 2 ≤ d) (hFH : FriedlandHaymanIn d) :
    ACFMonotoneIn d := by
  intro u₁ u₂ x₀ L h
  have hd1 : 1 ≤ d := by omega
  have hderiv : ∀ᵐ r, 0 < r → 0 ≤ deriv (fun r ↦ acfPhi u₁ u₂ x₀ r) r := by
    filter_upwards [ae_hasDerivAt_acfIntegral hd1 h.lipschitz_left x₀,
      ae_hasDerivAt_acfIntegral hd1 h.lipschitz_right x₀,
      ae_two_mul_sphExponent_mul_acfIntegral_le hd1 h.lipschitz_left h.nonneg_left
        h.harmonic_left h.left_apply_eq_zero,
      ae_two_mul_sphExponent_mul_acfIntegral_le hd1 h.lipschitz_right h.nonneg_right
        h.harmonic_right h.right_apply_eq_zero,
      ae_acfIntegral_eq_zero_of_eq_empty hd1 h.lipschitz_left h.nonneg_left
        h.harmonic_left h.left_apply_eq_zero,
      ae_acfIntegral_eq_zero_of_eq_empty hd1 h.lipschitz_right h.nonneg_right
        h.harmonic_right h.right_apply_eq_zero] with r hD₁ hD₂ hK₁ hK₂ hE₁ hE₂ hr
    have hΦ := ((hD₁ hr).mul (hD₂ hr)).div (hasDerivAt_pow 4 r) (by positivity)
    have heq : (fun r ↦ acfPhi u₁ u₂ x₀ r) = fun r ↦ acfIntegral u₁ x₀ r * acfIntegral u₂ x₀ r /
        r ^ 4 := rfl
    have hΦ' : HasDerivAt (fun r ↦ acfIntegral u₁ x₀ r * acfIntegral u₂ x₀ r / r ^ 4) _ r := hΦ
    rw [heq, hΦ'.deriv]
    refine div_nonneg ?_ (sq_nonneg _)
    simp only [Pi.mul_apply]
    have hnum := acf_numerator_nonneg h hFH hr (hK₁ hr) (hK₂ hr) (hE₁ hr) (hE₂ hr)
    have : (r * radialQ u₁ x₀ r * acfIntegral u₂ x₀ r +
        acfIntegral u₁ x₀ r * (r * radialQ u₂ x₀ r)) * r ^ 4 -
        acfIntegral u₁ x₀ r * acfIntegral u₂ x₀ r * (((4 : ℕ) : ℝ) * r ^ (4 - 1)) =
        r ^ 3 * (r * (r * radialQ u₁ x₀ r) * acfIntegral u₂ x₀ r +
          r * acfIntegral u₁ x₀ r * (r * radialQ u₂ x₀ r) -
            4 * acfIntegral u₁ x₀ r * acfIntegral u₂ x₀ r) := by
      push_cast; ring
    rw [this]
    positivity
  intro a ha b hb hab
  have ha : 0 < a := ha
  obtain ⟨K₁, hK₁⟩ := exists_lipschitzOnWith_acfIntegral hd1 h.lipschitz_left x₀ b
  obtain ⟨K₂, hK₂⟩ := exists_lipschitzOnWith_acfIntegral hd1 h.lipschitz_right x₀ b
  have hsub : uIcc a b ⊆ Icc 0 b := by
    rw [uIcc_of_le hab]; exact Icc_subset_Icc ha.le le_rfl
  have hinv : AbsolutelyContinuousOnInterval (fun r : ℝ ↦ (r ^ 4)⁻¹) a b :=
    ContDiffOn.absolutelyContinuousOnInterval fun r hr ↦ by
      rw [uIcc_of_le hab] at hr
      exact ((contDiff_id.pow 4).contDiffAt.inv
        (pow_ne_zero 4 (ha.trans_le hr.1).ne')).contDiffWithinAt
  have hAC : AbsolutelyContinuousOnInterval (fun r ↦ acfPhi u₁ u₂ x₀ r) a b :=
    (((hK₁.mono hsub).absolutelyContinuousOnInterval.fun_mul
      (hK₂.mono hsub).absolutelyContinuousOnInterval).fun_mul hinv).congr fun r _ ↦ by
        simp only [acfPhi, div_eq_mul_inv]
  have hFTC := hAC.integral_deriv_eq_sub
  have hnn : 0 ≤ ∫ r in a..b, deriv (fun r ↦ acfPhi u₁ u₂ x₀ r) r :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab (by
      rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [hderiv] with r hr hrI
      exact hr (ha.trans_le hrI.1))
  linarith

/-! ### Bounds and scaling -/

/-- `I(w, x₀, r) ≤ L² σ(𝕊) r²/2` for an `L`-Lipschitz `w` and `r ≥ 0`. -/
theorem acfIntegral_le (hd : 1 ≤ d) {w : E d → ℝ} {L : ℝ≥0} (hw : LipschitzWith L w) (x₀ : E d)
    {r : ℝ} (hr : 0 ≤ r) :
    acfIntegral w x₀ r ≤
      (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ * r ^ 2 / 2 := by
  set σ := (volume : Measure (E d)).toSphere.real univ
  rw [acfIntegral_eq_integral hd hw x₀ hr]
  have hint : IntervalIntegrable (fun τ ↦ τ * radialQ w x₀ τ) volume 0 r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hr]
    refine IntegrableOn.of_bound measure_Icc_lt_top
      ((stronglyMeasurable_id.mul (stronglyMeasurable_radialQ w x₀)).aestronglyMeasurable)
      (r * ((L : ℝ) ^ 2 * σ)) ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    refine ae_of_all _ fun τ hτ ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hτ.1, abs_of_nonneg (radialQ_nonneg w x₀ τ)]
    exact mul_le_mul hτ.2 (radialQ_le hw x₀ τ) (radialQ_nonneg w x₀ τ) hr
  calc ∫ τ in 0..r, τ * radialQ w x₀ τ ≤ ∫ τ in 0..r, τ * ((L : ℝ) ^ 2 * σ) :=
        intervalIntegral.integral_mono_on hr hint
          ((continuous_id.mul continuous_const).intervalIntegrable _ _) fun τ hτ ↦
          mul_le_mul_of_nonneg_left (radialQ_le hw x₀ τ) hτ.1
    _ = (L : ℝ) ^ 2 * σ * r ^ 2 / 2 := by
        rw [intervalIntegral.integral_mul_const, integral_id]; ring

/-- `Φ(u₁, u₂, x₀, r) ≤ L⁴ σ(𝕊)²/4` for `L`-Lipschitz `u₁, u₂` and `r > 0`. -/
theorem acfPhi_le (hd : 1 ≤ d) {u₁ u₂ : E d → ℝ} {L : ℝ≥0} (hu₁ : LipschitzWith L u₁)
    (hu₂ : LipschitzWith L u₂) (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    acfPhi u₁ u₂ x₀ r ≤ (L : ℝ) ^ 4 * (volume : Measure (E d)).toSphere.real univ ^ 2 / 4 := by
  set σ := (volume : Measure (E d)).toSphere.real univ
  have hσ : 0 ≤ σ := measureReal_nonneg
  rw [acfPhi, div_le_iff₀ (by positivity)]
  calc acfIntegral u₁ x₀ r * acfIntegral u₂ x₀ r ≤
        ((L : ℝ) ^ 2 * σ * r ^ 2 / 2) * ((L : ℝ) ^ 2 * σ * r ^ 2 / 2) :=
        mul_le_mul (acfIntegral_le hd hu₁ x₀ hr.le) (acfIntegral_le hd hu₂ x₀ hr.le)
          (acfIntegral_nonneg _ _ _) (by positivity)
    _ = (L : ℝ) ^ 4 * σ ^ 2 / 4 * r ^ 4 := by ring

/-- The gradient of the rescaling `w_{x₀,R}(y) = w(x₀ + Ry)/R` is `∇w(x₀ + Ry)`, for `R ≠ 0`. -/
theorem gradient_blowup (w : E d → ℝ) (x₀ : E d) {R : ℝ} (hR : R ≠ 0) (y : E d) :
    ∇ (blowup w x₀ R) y = ∇ w (x₀ + R • y) := by
  have h1 : blowup w x₀ R = R⁻¹ • fun y ↦ (fun z ↦ w (x₀ + z)) (R • y) := by
    funext y; simp [blowup, div_eq_inv_mul]
  rw [gradient, gradient, h1, fderiv_const_smul_field, Pi.smul_apply,
    fderiv_comp_smul (f := fun z ↦ w (x₀ + z)), fderiv_comp_add_left, smul_smul,
    inv_mul_cancel₀ hR, one_smul]

/-- **Scaling of the ACF integral**:
`I(w_{x₀,R}, 0, ρ) = R⁻² I(w, x₀, Rρ)` for `R > 0`. -/
theorem acfIntegral_blowup (w : E d → ℝ) (x₀ : E d) {R : ℝ} (hR : 0 < R) (ρ : ℝ) :
    acfIntegral (blowup w x₀ R) 0 ρ = acfIntegral w x₀ (R * ρ) / R ^ 2 := by
  set F : E d → ℝ := (ball x₀ (R * ρ)).indicator fun x ↦ ‖∇ w x‖ ^ 2 * ‖x - x₀‖ ^ (2 - (d : ℝ))
    with hF
  have hI : acfIntegral w x₀ (R * ρ) = ∫ x, F (x₀ + x) := by
    rw [integral_add_left_eq_self F x₀, hF, integral_indicator measurableSet_ball, acfIntegral]
  have hpt : ∀ y, F (x₀ + R • y) = R ^ (2 - (d : ℝ)) * (ball (0 : E d) ρ).indicator
      (fun y ↦ ‖∇ (blowup w x₀ R) y‖ ^ 2 * ‖y - 0‖ ^ (2 - (d : ℝ))) y := fun y ↦ by
    have hnorm : ‖x₀ + R • y - x₀‖ = R * ‖y‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hR.le]
    have hiff : x₀ + R • y ∈ ball x₀ (R * ρ) ↔ y ∈ ball (0 : E d) ρ := by
      rw [mem_ball, mem_ball, dist_eq_norm, dist_zero_right, hnorm, mul_lt_mul_iff_right₀ hR]
    by_cases hy : y ∈ ball (0 : E d) ρ
    · rw [hF, indicator_of_mem (hiff.mpr hy), indicator_of_mem hy, gradient_blowup w x₀ hR.ne',
        hnorm, sub_zero, Real.mul_rpow hR.le (norm_nonneg _)]
      ring
    · rw [hF, indicator_of_notMem (fun h ↦ hy (hiff.mp h)), indicator_of_notMem hy, mul_zero]
  have hmain : R ^ (2 - (d : ℝ)) * acfIntegral (blowup w x₀ R) 0 ρ =
      (R ^ d)⁻¹ * acfIntegral w x₀ (R * ρ) := by
    rw [acfIntegral, ← integral_indicator measurableSet_ball, ← integral_const_mul]
    simp_rw [← hpt]
    rw [Measure.integral_comp_smul (μ := (volume : Measure (E d))) (fun x ↦ F (x₀ + x)) R,
      finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hR d)), smul_eq_mul, hI]
  have hpow : R ^ (2 - (d : ℝ)) * R ^ d = R ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR, show 2 - (d : ℝ) + d = (2 : ℕ) by push_cast; ring,
      Real.rpow_natCast]
  have hRd : R ^ d ≠ 0 := pow_ne_zero d hR.ne'
  rw [eq_div_iff (pow_ne_zero 2 hR.ne'), ← hpow]
  calc acfIntegral (blowup w x₀ R) 0 ρ * (R ^ (2 - (d : ℝ)) * R ^ d)
      = (R ^ (2 - (d : ℝ)) * acfIntegral (blowup w x₀ R) 0 ρ) * R ^ d := by ring
    _ = acfIntegral w x₀ (R * ρ) := by rw [hmain]; field_simp

/-- **Scaling of the ACF functional**:
`Φ(u₁_{x₀,R}, u₂_{x₀,R}, 0, ρ) = Φ(u₁, u₂, x₀, Rρ)` for `R > 0`. -/
theorem acfPhi_blowup (u₁ u₂ : E d → ℝ) (x₀ : E d) {R : ℝ} (hR : 0 < R) (ρ : ℝ) :
    acfPhi (blowup u₁ x₀ R) (blowup u₂ x₀ R) 0 ρ = acfPhi u₁ u₂ x₀ (R * ρ) := by
  rw [acfPhi, acfPhi, acfIntegral_blowup u₁ x₀ hR, acfIntegral_blowup u₂ x₀ hR, mul_pow]
  ring

end EllipticBernoulli
