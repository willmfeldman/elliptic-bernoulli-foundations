/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The hole-filling iteration lemma

M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic Systems*,
Ann. of Math. Stud. 105, Princeton Univ. Press, 1983, Ch. V, Lemma 3.1, with exponent `2` and
in the explicit form proved here: if `f` is bounded on `[ρ, R)` and
`f(s) ≤ θ f(t) + A (t - s)⁻² + B` for all `ρ ≤ s < t < R`, with `0 ≤ θ < 1`, then
`f(ρ) ≤ 16 (1 - θ)⁻⁴ (A (R - ρ)⁻² + B)`.

Pure real analysis.
-/

open Filter Topology Finset

@[expose] public noncomputable section

namespace EllipticBernoulli

private lemma iter_term (θ A B l D : ℝ) (i : ℕ) (hl : l ≠ 0) (hD : D ≠ 0) (h1l : 1 - l ≠ 0) :
    θ ^ i * (A / (l ^ i * D * (1 - l)) ^ 2 + B) =
      A / (D * (1 - l)) ^ 2 * (θ / l ^ 2) ^ i + B * θ ^ i := by
  rw [div_pow θ, ← pow_mul]
  field_simp
  ring

/-- **Iteration lemma** (Giaquinta Ch. V, Lemma 3.1, exponent `2`). -/
theorem iteration_lemma {f : ℝ → ℝ} {ρ R θ A B M : ℝ} (hρR : ρ < R) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hfM : ∀ t, ρ ≤ t → t < R → f t ≤ M)
    (h : ∀ s t, ρ ≤ s → s < t → t < R → f s ≤ θ * f t + A / (t - s) ^ 2 + B) :
    f ρ ≤ 16 / (1 - θ) ^ 4 * (A / (R - ρ) ^ 2 + B) := by
  set l : ℝ := (1 + θ) / 2 with hl
  set D : ℝ := R - ρ with hD
  have hD0 : 0 < D := sub_pos.2 hρR
  have hl0 : 0 < l := by rw [hl]; linarith
  have hl1 : l < 1 := by rw [hl]; linarith
  have h1l : 1 - l = (1 - θ) / 2 := by rw [hl]; ring
  set q : ℝ := θ / l ^ 2 with hq
  have hq0 : 0 ≤ q := div_nonneg hθ0 (sq_nonneg _)
  have hq1 : q < 1 := by
    rw [hq, div_lt_one (by positivity), hl]
    linarith [pow_pos (sub_pos.2 hθ1) 2]
  set t : ℕ → ℝ := fun i ↦ R - l ^ i * D with ht
  have ht0 : t 0 = ρ := by simp [ht, hD]
  have htρ : ∀ i, ρ ≤ t i := by
    intro i
    have : l ^ i ≤ 1 := pow_le_one₀ hl0.le hl1.le
    have := mul_le_of_le_one_left hD0.le this
    simp only [ht]
    linarith
  have htR : ∀ i, t i < R := by
    intro i
    have : 0 < l ^ i * D := mul_pos (pow_pos hl0 i) hD0
    simp only [ht]; linarith
  have hdiff : ∀ i, t (i + 1) - t i = l ^ i * D * (1 - l) := by
    intro i; simp only [ht, pow_succ]; ring
  have hlt : ∀ i, t i < t (i + 1) := by
    intro i
    have : 0 < l ^ i * D * (1 - l) := mul_pos (mul_pos (pow_pos hl0 i) hD0) (by linarith)
    linarith [hdiff i]
  set c : ℝ := A / (D * (1 - l)) ^ 2 with hc
  have hterm : ∀ i, θ ^ i * (A / (t (i + 1) - t i) ^ 2 + B) = c * q ^ i + B * θ ^ i := by
    intro i
    rw [hdiff i]
    exact iter_term θ A B l D i hl0.ne' hD0.ne' (by linarith)
  -- iterate
  have hind : ∀ k : ℕ, f ρ ≤ θ ^ k * f (t k) + ∑ i ∈ range k, (c * q ^ i + B * θ ^ i) := by
    intro k
    induction k with
    | zero => simp [ht0]
    | succ k ih =>
      have hstep := h (t k) (t (k + 1)) (htρ k) (hlt k) (htR (k + 1))
      have hθk : 0 ≤ θ ^ k := pow_nonneg hθ0 k
      rw [sum_range_succ, ← hterm k]
      calc f ρ ≤ θ ^ k * f (t k) + ∑ i ∈ range k, (c * q ^ i + B * θ ^ i) := ih
        _ ≤ θ ^ k * (θ * f (t (k + 1)) + A / (t (k + 1) - t k) ^ 2 + B) +
            ∑ i ∈ range k, (c * q ^ i + B * θ ^ i) :=
          add_le_add (mul_le_mul_of_nonneg_left hstep hθk) le_rfl
        _ = θ ^ (k + 1) * f (t (k + 1)) + (∑ i ∈ range k, (c * q ^ i + B * θ ^ i) +
            θ ^ k * (A / (t (k + 1) - t k) ^ 2 + B)) := by ring
  -- sum the geometric series
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hsum : ∀ k, ∑ i ∈ range k, (c * q ^ i + B * θ ^ i) ≤ c / (1 - q) + B / (1 - θ) := by
    intro k
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    have g1 : ∑ i ∈ range k, q ^ i ≤ 1 / (1 - q) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hq0 hq1
      simpa using this
    have g2 : ∑ i ∈ range k, θ ^ i ≤ 1 / (1 - θ) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hθ0 hθ1
      simpa using this
    have e1 : c / (1 - q) = c * (1 / (1 - q)) := by ring
    have e2 : B / (1 - θ) = B * (1 / (1 - θ)) := by ring
    rw [e1, e2]
    exact add_le_add (mul_le_mul_of_nonneg_left g1 hc0) (mul_le_mul_of_nonneg_left g2 hB)
  have hbound : ∀ k : ℕ, f ρ ≤ c / (1 - q) + B / (1 - θ) + θ ^ k * |M| := by
    intro k
    have hθk : 0 ≤ θ ^ k := pow_nonneg hθ0 k
    have : θ ^ k * f (t k) ≤ θ ^ k * |M| :=
      mul_le_mul_of_nonneg_left ((hfM _ (htρ k) (htR k)).trans (le_abs_self M)) hθk
    linarith [hind k, hsum k]
  have hlim : Tendsto (fun k : ℕ ↦ c / (1 - q) + B / (1 - θ) + θ ^ k * |M|) atTop
      (𝓝 (c / (1 - q) + B / (1 - θ))) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const |M|
    simpa using this.const_add (c / (1 - q) + B / (1 - θ))
  have hmain : f ρ ≤ c / (1 - q) + B / (1 - θ) := ge_of_tendsto' hlim hbound
  -- compare constants
  have h1θ : 0 < 1 - θ := by linarith
  have hkey1 : c / (1 - q) ≤ 16 / (1 - θ) ^ 4 * (A / D ^ 2) := by
    have h1θ' : 1 - θ ≠ 0 := h1θ.ne'
    have h1θ'' : 1 + θ ≠ 0 := by linarith
    have hD' : D ≠ 0 := hD0.ne'
    have h1q : 1 - q = (1 - θ) ^ 2 / (1 + θ) ^ 2 := by
      rw [hq, hl]; field_simp; ring
    have heq : c / (1 - q) = 4 * (1 + θ) ^ 2 / (1 - θ) ^ 4 * (A / D ^ 2) := by
      rw [hc, h1q, h1l]; field_simp; ring
    rw [heq]
    have h4 : 4 * (1 + θ) ^ 2 ≤ 16 := by
      have := pow_le_pow_left₀ (by linarith) (by linarith : 1 + θ ≤ 2) 2
      linarith
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right h4 (by positivity))
      (by positivity)
  have hkey2 : B / (1 - θ) ≤ 16 / (1 - θ) ^ 4 * B := by
    rw [div_le_iff₀ h1θ]
    have hp : (1 - θ) ^ 3 ≤ 1 := pow_le_one₀ h1θ.le (by linarith)
    have : 16 / (1 - θ) ^ 4 * B * (1 - θ) = 16 * B / (1 - θ) ^ 3 := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hp hB]
  calc f ρ ≤ c / (1 - q) + B / (1 - θ) := hmain
    _ ≤ 16 / (1 - θ) ^ 4 * (A / D ^ 2) + 16 / (1 - θ) ^ 4 * B := add_le_add hkey1 hkey2
    _ = 16 / (1 - θ) ^ 4 * (A / (R - ρ) ^ 2 + B) := by rw [hD]; ring

end EllipticBernoulli
