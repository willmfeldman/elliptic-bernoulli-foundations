/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Harmonic.GradientEstimate

/-!
# Liouville theorems for harmonic functions on `E d`

* `HarmonicOnNhd.eq_const_of_bounded`: a bounded harmonic function on all of `E d` is constant.
* `harmonic_liouville_affine`: a harmonic function on all of `E d` with linear growth
  `|h x| ≤ A (1 + ‖x‖)` is affine, `h x = a + ⟪b, x⟫`.

Used for the linearized problem (via reflection) and for blow-ups of classical solutions.

## Proof

Bounded case: the scaled gradient estimate on `B_R(x)` gives `‖∇h(x)‖ ≤ C sup|h| / R → 0`.
Linear growth: the second-derivative estimate on `B_R(x)` gives
`‖D²h(x)‖ ≤ C A (1 + ‖x‖ + R) / R² → 0`, so `Dh` is constant, and `h - Dh(0)` has zero
derivative.
-/

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- A quantity bounded by `K / R` for every `R > 0` is nonpositive. -/
private theorem nonpos_of_le_div {a K : ℝ} (h : ∀ R : ℝ, 0 < R → a ≤ K / R) : a ≤ 0 := by
  by_contra ha
  rw [not_le] at ha
  have hK : 0 ≤ K := by
    have := h 1 one_pos
    rw [div_one] at this
    linarith
  have := h (2 * (K + 1) / a) (by positivity)
  rw [div_div_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

/-- **Liouville's theorem.** A bounded harmonic function on `E d` is constant. -/
theorem HarmonicOnNhd.eq_const_of_bounded {h : E d → ℝ} (hh : HarmonicOnNhd h univ)
    {A : ℝ} (hA : ∀ x, |h x| ≤ A) (x y : E d) : h x = h y := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact congrArg h (Subsingleton.elim x y)
  obtain ⟨C, hC, hest⟩ := exists_norm_fderiv_le_div_of_harmonic hd
  have hdiff : Differentiable ℝ h := fun z ↦
    (hh z (mem_univ z)).1.differentiableAt (by norm_num)
  refine is_const_of_fderiv_eq_zero hdiff (fun z ↦ ?_) x y
  refine norm_le_zero_iff.1 (nonpos_of_le_div (K := C * A) fun R hR ↦ ?_)
  have := hest h z R A hR (hh.mono (subset_univ _)) fun w _ ↦ hA w
  simpa [mul_div_assoc] using this

/-- **Liouville's theorem, linear growth** (`harmonic_liouville_affine`). A harmonic function on
`E d` with `|h x| ≤ A (1 + ‖x‖)` is affine: `h x = a + ⟪b, x⟫`. -/
theorem harmonic_liouville_affine {h : E d → ℝ} (hh : HarmonicOnNhd h univ) {A : ℝ}
    (hA : ∀ x, |h x| ≤ A * (1 + ‖x‖)) : ∃ a : ℝ, ∃ b : E d, ∀ x, h x = a + ⟪b, x⟫ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨h 0, 0, fun x ↦ by rw [Subsingleton.elim x 0]; simp⟩
  obtain ⟨C, hC, hest⟩ := norm_hessian_le_of_harmonic hd
  have hsmooth : ContDiff ℝ ∞ h :=
    contDiffOn_univ.1 (HarmonicOnNhd.contDiffOn_top isOpen_univ hh)
  have hdiff : Differentiable ℝ h := hsmooth.differentiable (by simp)
  have hdiff' : Differentiable ℝ (fderiv ℝ h) :=
    (hsmooth.fderiv_right (m := 1) (by norm_cast)).differentiable one_ne_zero
  have hA0 : 0 ≤ A := by
    have := (abs_nonneg _).trans (hA 0)
    simpa only [norm_zero, add_zero, mul_one] using this
  -- the second derivative vanishes
  have hD2 : ∀ x, fderiv ℝ (fderiv ℝ h) x = 0 := by
    intro x
    refine norm_le_zero_iff.1 ?_
    -- `‖D²h(x)‖ ≤ C A (1 + ‖x‖ + R) / R²` for all `R > 0`
    have hbound : ∀ R : ℝ, 0 < R →
        ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ C * (A * (1 + ‖x‖ + R)) / R ^ 2 := by
      intro R hR
      refine hest h x R _ hR (hh.mono (subset_univ _)) fun y hy ↦ (hA y).trans ?_
      have : ‖y‖ ≤ ‖x‖ + R := by
        have := norm_le_norm_add_norm_sub' y x
        rw [mem_closedBall, dist_eq_norm] at hy
        linarith
      exact mul_le_mul_of_nonneg_left (by linarith) hA0
    by_contra hpos
    rw [not_le] at hpos
    set a := ‖fderiv ℝ (fderiv ℝ h) x‖
    -- choose `R` large
    set K := C * A * (1 + ‖x‖)
    set R : ℝ := (K + C * A + 1) * 2 / a + 1 with hR
    have hR0 : 0 < R := by positivity
    have hb := hbound R hR0
    have hK : 0 ≤ K := by positivity
    rw [le_div_iff₀ (by positivity)] at hb
    have e1 : C * (A * (1 + ‖x‖ + R)) = K + C * A * R := by ring
    rw [e1] at hb
    have hRa : a * R ≥ (K + C * A + 1) * 2 := by
      rw [hR, mul_add, mul_div_assoc', mul_div_cancel_left₀ _ hpos.ne']
      nlinarith
    have hR1 : 1 ≤ R := by rw [hR]; have : 0 ≤ (K + C * A + 1) * 2 / a := by positivity
                           linarith
    have h1 := mul_le_mul_of_nonneg_right hRa hR0.le
    nlinarith [mul_le_mul_of_nonneg_left hR1 hK, mul_nonneg hC hA0]
  -- so `Dh` is constant
  have hDconst : ∀ x, fderiv ℝ h x = fderiv ℝ h 0 := fun x ↦
    is_const_of_fderiv_eq_zero hdiff' hD2 x 0
  set L := fderiv ℝ h 0
  -- and `h - L` has zero derivative
  have hg : ∀ x, h x = h 0 + L x := by
    intro x
    have hgd : Differentiable ℝ (fun y ↦ h y - L y) := hdiff.sub L.differentiable
    have hgd' : ∀ y, fderiv ℝ (fun y ↦ h y - L y) y = 0 := fun y ↦ by
      rw [fderiv_fun_sub (hdiff y) L.differentiableAt, L.fderiv, hDconst y, sub_self]
    have := is_const_of_fderiv_eq_zero hgd hgd' x 0
    simp only [map_zero, sub_zero] at this
    linarith
  refine ⟨h 0, (toDual ℝ (E d)).symm L, fun x ↦ ?_⟩
  rw [hg x, toDual_symm_apply]

end EllipticBernoulli
