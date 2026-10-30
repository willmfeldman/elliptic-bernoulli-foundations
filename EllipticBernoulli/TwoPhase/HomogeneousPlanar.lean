/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.TwoPhase
import EllipticBernoulli.Blowup.Homogeneous

/-!
# Homogeneous two-phase functions in the plane

`homogeneousTwoPhaseIn_two : HomogeneousTwoPhaseIn 2`: a Lipschitz, positively `1`-homogeneous
`v : ℝ² → ℝ`, harmonic on `{v > 0}` and on `{v < 0}`, with both phases nonempty, is a two-plane
function `a (x·e)⁺ - b (x·e)⁻` with `‖e‖ = 1` and `a, b > 0`.

## Proof

Apply the planar classification `eq_halfPlanes_of_homogeneous` to `v⁺ = max v 0` and to
`v⁻ = max (-v) 0`. Each is nonzero, so `v⁺ = a (y·e)₊ + b (y·e)₋` and
`v⁻ = a' (y·e')₊ + b' (y·e')₋` with `a, a' > 0` and `b, b' ≥ 0`. Since `v⁺ v⁻ ≡ 0`:

* `b = 0`: otherwise `v⁺(e') = 0` forces `e·e' = 0`, and then both `v⁺` and `v⁻` are positive at
  `e + e'` (`coeff_eq_zero_of_mul_eq_zero`); symmetrically `b' = 0`.
* `e' = -e`: evaluating at `e + e'` gives `(1 + e·e')₊ = 0`, so `e·e' = -1`
  (`eq_neg_of_mul_eq_zero`).

The evaluation at `e + e'` is a pointwise form of the observation that a line has empty
interior.

This is the planar case of the classification of homogeneous two-phase functions; compare
De Philippis–Spolaor–Velichkov (arXiv:1911.02165), Lemma 2.2, which classifies blow-up limits at
two-phase points of minimizers of the two-phase functional.

## References

* G. De Philippis, L. Spolaor, B. Velichkov, *Regularity of the free boundary for the two-phase
  Bernoulli problem*, Invent. Math. 225 (2021), 347–394; arXiv:1911.02165.
-/

open Set Filter Topology InnerProductSpace
open scoped NNReal RealInnerProductSpace Laplacian

namespace EllipticBernoulli

namespace HomogeneousPlanar

/-- The positive part of a continuous, `1`-homogeneous function that is harmonic on its positivity
set and positive somewhere is `a (y·e)₊ + b (y·e)₋` with `‖e‖ = 1`, `a > 0`, `b ≥ 0`. -/
private theorem posPart_eq {w : E 2 → ℝ} (hw : Continuous w)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, w (t • x) = t * w x)
    (hH : HarmonicOnNhd w {x | 0 < w x}) (hpos : ∃ x, 0 < w x) :
    ∃ e : E 2, ‖e‖ = 1 ∧ ∃ a b : ℝ, 0 < a ∧ 0 ≤ b ∧
      ∀ y, max (w y) 0 = a * max ⟪y, e⟫ 0 + b * max (-⟪y, e⟫) 0 := by
  have hH' : HarmonicOnNhd (fun x ↦ max (w x) 0) {x | 0 < max (w x) 0} := by
    intro x hx
    have hx' : 0 < w x := by
      rw [mem_ofPred_eq] at hx
      rcases lt_max_iff.1 hx with h | h
      · exact h
      · exact absurd h (lt_irrefl 0)
    have hloc : (fun y ↦ max (w y) 0) =ᶠ[𝓝 x] w := by
      filter_upwards [(isOpen_lt continuous_const hw).mem_nhds hx'] with y hy
      exact max_eq_left (le_of_lt hy)
    exact (harmonicAt_congr_nhds hloc).2 (hH x hx')
  rcases eq_halfPlanes_of_homogeneous (v := fun x ↦ max (w x) 0)
      (hw.max continuous_const) (fun y ↦ le_max_right _ _) hH'.contDiffOn
      (fun y hy ↦ by simpa using (hH' y hy).2.self_of_nhds)
      (fun t ht y ↦ by
        simp only [hhom t ht y]
        rw [mul_max_of_nonneg _ _ ht.le, mul_zero]) with h0 | h
  · obtain ⟨x, hx⟩ := hpos
    have : max (w x) 0 = 0 := h0 x
    linarith [le_max_left (w x) 0]
  · exact h

/-- If `(a (y·e)₊ + b (y·e)₋) (a' (y·e')₊ + b' (y·e')₋) = 0` for every `y`, with unit vectors
`e, e'`, `a, a' > 0` and `b, b' ≥ 0`, then `b = 0`. -/
private theorem coeff_eq_zero_of_mul_eq_zero {e e' : E 2} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    {a b a' b' : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (ha' : 0 < a') (hb' : 0 ≤ b')
    (hprod : ∀ y : E 2, (a * max ⟪y, e⟫ 0 + b * max (-⟪y, e⟫) 0) *
      (a' * max ⟪y, e'⟫ 0 + b' * max (-⟪y, e'⟫) 0) = 0) : b = 0 := by
  by_contra hb0
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hee' : ⟪e', e'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he']; norm_num
  set c := ⟪e', e⟫ with hc
  have hc' : ⟪e, e'⟫ = c := real_inner_comm _ _
  -- At `y = e'` the second factor is `≥ a' > 0`, so the first vanishes and `c = 0`.
  have h1 := hprod e'
  rw [hee'] at h1
  have hg : 0 < a' * max (1 : ℝ) 0 + b' * max (-1 : ℝ) 0 := by
    rw [max_eq_left zero_le_one]
    nlinarith [le_max_right (-1 : ℝ) 0]
  have hf : a * max c 0 + b * max (-c) 0 = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact h
    · linarith
  have hc0 : c = 0 := by
    have h2 : 0 ≤ a * max c 0 := mul_nonneg ha.le (le_max_right _ _)
    have h3 : 0 ≤ b * max (-c) 0 := mul_nonneg hb (le_max_right _ _)
    have h4 : max c 0 = 0 := by
      have : a * max c 0 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h ha.ne'
      · exact h
    have h5 : max (-c) 0 = 0 := by
      have : b * max (-c) 0 = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hbpos.ne'
      · exact h
    have := le_max_left c 0
    have := le_max_left (-c) 0
    linarith
  -- At `y = e + e'` both factors are positive.
  have h6 := hprod (e + e')
  rw [inner_add_left, inner_add_left, hee, hee', hc', ← hc, hc0, add_zero, zero_add] at h6
  rw [max_eq_left zero_le_one] at h6
  have hp1 : 0 < a * 1 + b * max (-1 : ℝ) 0 := by nlinarith [le_max_right (-1 : ℝ) 0]
  have hp2 : 0 < a' * 1 + b' * max (-1 : ℝ) 0 := by nlinarith [le_max_right (-1 : ℝ) 0]
  exact (mul_pos hp1 hp2).ne' h6

/-- If `(y·e)₊ (y·e')₊ = 0` for every `y`, with unit vectors `e, e'`, then `e' = -e`. -/
private theorem eq_neg_of_mul_eq_zero {e e' : E 2} (he : ‖e‖ = 1) (he' : ‖e'‖ = 1)
    (hprod : ∀ y : E 2, max ⟪y, e⟫ 0 * max ⟪y, e'⟫ 0 = 0) : e' = -e := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hee' : ⟪e', e'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he']; norm_num
  have hc' : ⟪e, e'⟫ = ⟪e', e⟫ := real_inner_comm _ _
  have h := hprod (e + e')
  rw [inner_add_left, inner_add_left, hee, hee', hc', add_comm 1 ⟪e', e⟫, ← sq,
    sq_eq_zero_iff] at h
  have hc : ⟪e', e⟫ ≤ -1 := by linarith [le_max_left (⟪e', e⟫ + 1) 0]
  have hnorm : ‖e' + e‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right, hee,
      hee', ← hc']
    have hle : -1 ≤ ⟪e', e⟫ := by
      have := abs_real_inner_le_norm e' e
      rw [he, he', mul_one] at this
      linarith [neg_abs_le ⟪e', e⟫]
    linarith
  have : e' + e = 0 := by
    rw [sq_eq_zero_iff, norm_eq_zero] at hnorm
    exact hnorm
  exact eq_neg_of_add_eq_zero_left this

end HomogeneousPlanar

public section

open HomogeneousPlanar in
/-- **Homogeneous two-phase functions in the plane** (De Philippis–Spolaor–Velichkov,
arXiv:1911.02165, Lemma 2.2, case `d = 2`). -/
theorem homogeneousTwoPhaseIn_two : HomogeneousTwoPhaseIn 2 := by
  intro v L hv hhom hHpos hHneg hpos hneg
  have hcont := hv.continuous
  obtain ⟨e, he, a, b, ha, hb, hplus⟩ := posPart_eq hcont hhom hHpos hpos
  have hHneg' : HarmonicOnNhd (-v) {x | 0 < (-v) x} := fun x hx ↦
    hHneg.neg x (show v x < 0 by simpa using hx)
  obtain ⟨e', he', a', b', ha', hb', hminus⟩ := posPart_eq (w := -v) hcont.neg
    (fun t ht x ↦ by simp only [Pi.neg_apply, hhom t ht x]; ring) hHneg'
    (let ⟨x, hx⟩ := hneg; ⟨x, by simpa using hx⟩)
  simp only [Pi.neg_apply] at hminus
  have hprod0 : ∀ y, max (v y) 0 * max (-v y) 0 = 0 := fun y ↦ by
    rcases le_total (v y) 0 with h | h
    · rw [max_eq_right h, zero_mul]
    · rw [max_eq_right (by linarith : -v y ≤ 0), mul_zero]
  have hprod : ∀ y : E 2, (a * max ⟪y, e⟫ 0 + b * max (-⟪y, e⟫) 0) *
      (a' * max ⟪y, e'⟫ 0 + b' * max (-⟪y, e'⟫) 0) = 0 := fun y ↦ by
    rw [← hplus, ← hminus]; exact hprod0 y
  have hb0 : b = 0 := coeff_eq_zero_of_mul_eq_zero he he' ha hb ha' hb' hprod
  have hb'0 : b' = 0 := coeff_eq_zero_of_mul_eq_zero he' he ha' hb' ha hb
    fun y ↦ by rw [mul_comm]; exact hprod y
  have hee' : e' = -e := eq_neg_of_mul_eq_zero he he' fun y ↦ by
    have := hprod y
    rw [hb0, hb'0, zero_mul, zero_mul, add_zero, add_zero] at this
    have h2 : a * a' * (max ⟪y, e⟫ 0 * max ⟪y, e'⟫ 0) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h (mul_pos ha ha').ne'
    · exact h
  refine ⟨e, a, a', he, ha, ha', fun x ↦ ?_⟩
  have h1 := hplus x
  have h2 := hminus x
  rw [hb0, zero_mul, add_zero] at h1
  rw [hb'0, zero_mul, add_zero, hee', inner_neg_right] at h2
  have hsplit : v x = max (v x) 0 - max (-v x) 0 := by
    rcases le_total (v x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : (0 : ℝ) ≤ -v x)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith : -v x ≤ 0)]; ring
  rw [hsplit, h1, h2, twoPlane, add_zero]

end

end EllipticBernoulli
