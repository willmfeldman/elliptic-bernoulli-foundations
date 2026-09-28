/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The De Giorgi numerical lemma

`degiorgi_seq_le`: if `Y_{j+1} ≤ N b^j Y_j^{1+α}` with `N > 0`, `b > 1`, `α > 0`, `Y_j ≥ 0`, and
`Y_0 ≤ N^{-1/α} b^{-1/α²}`, then `Y_j ≤ Y_0 (b^{-1/α})^j`; in particular `Y_j → 0`.

Pure real analysis.
-/

open Filter Topology

@[expose] public noncomputable section

namespace EllipticBernoulli

theorem degiorgi_seq_le {Y : ℕ → ℝ} {N b α : ℝ} (hN : 0 < N) (hb : 1 < b) (hα : 0 < α)
    (hY : ∀ j, 0 ≤ Y j) (hrec : ∀ j, Y (j + 1) ≤ N * b ^ j * Y j ^ (1 + α))
    (h0 : Y 0 ≤ N ^ (-1 / α) * b ^ (-1 / α ^ 2)) :
    ∀ j, Y j ≤ Y 0 * (b ^ (-1 / α)) ^ j := by
  have hb0 : 0 < b := by linarith
  set q := b ^ (-1 / α) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hb0 _
  have hY0 := hY 0
  -- `N Y₀^α ≤ q`
  have hNY : N * Y 0 ^ α ≤ q := by
    have h1 : Y 0 ^ α ≤ (N ^ (-1 / α) * b ^ (-1 / α ^ 2)) ^ α :=
      Real.rpow_le_rpow hY0 h0 hα.le
    have h2 : (N ^ (-1 / α) * b ^ (-1 / α ^ 2)) ^ α = N⁻¹ * q := by
      rw [Real.mul_rpow (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hb0.le _),
        ← Real.rpow_mul hN.le, ← Real.rpow_mul hb0.le, hq]
      have e1 : -1 / α * α = -1 := by field_simp
      have e2 : -1 / α ^ 2 * α = -1 / α := by field_simp
      rw [e1, e2, Real.rpow_neg_one]
    calc N * Y 0 ^ α ≤ N * (N⁻¹ * q) := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hN.le
      _ = q := by field_simp
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hqj : 0 ≤ q ^ j := pow_nonneg hq0.le j
    have h3 : Y j ^ (1 + α) ≤ (Y 0 * q ^ j) ^ (1 + α) :=
      Real.rpow_le_rpow (hY j) ih (by linarith)
    have h4 : (Y 0 * q ^ j) ^ (1 + α) = Y 0 * Y 0 ^ α * (q ^ (1 + α)) ^ j := by
      rw [Real.mul_rpow hY0 hqj, Real.rpow_add' hY0 (by linarith), Real.rpow_one,
        ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, mul_comm (j : ℝ), Real.rpow_mul hq0.le,
        Real.rpow_natCast]
    have h5 : b ^ j * (q ^ (1 + α)) ^ j = q ^ j := by
      rw [← mul_pow]
      congr 1
      rw [hq, ← Real.rpow_mul hb0.le]
      conv_lhs => arg 1; rw [← Real.rpow_one b]
      rw [← Real.rpow_add hb0]
      congr 1
      field_simp
      ring
    calc Y (j + 1) ≤ N * b ^ j * Y j ^ (1 + α) := hrec j
      _ ≤ N * b ^ j * (Y 0 * q ^ j) ^ (1 + α) := by
          gcongr
      _ = (N * Y 0 ^ α) * Y 0 * (b ^ j * (q ^ (1 + α)) ^ j) := by rw [h4]; ring
      _ ≤ q * Y 0 * (b ^ j * (q ^ (1 + α)) ^ j) := by
          gcongr
      _ = Y 0 * q ^ (j + 1) := by rw [h5]; ring

theorem degiorgi_seq_tendsto {Y : ℕ → ℝ} {N b α : ℝ} (hN : 0 < N) (hb : 1 < b) (hα : 0 < α)
    (hY : ∀ j, 0 ≤ Y j) (hrec : ∀ j, Y (j + 1) ≤ N * b ^ j * Y j ^ (1 + α))
    (h0 : Y 0 ≤ N ^ (-1 / α) * b ^ (-1 / α ^ 2)) :
    Tendsto Y atTop (𝓝 0) := by
  have hb0 : 0 < b := by linarith
  have hq1 : b ^ (-1 / α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hb (div_neg_of_neg_of_pos (by norm_num) hα)
  have hq0 : 0 ≤ b ^ (-1 / α) := Real.rpow_nonneg hb0.le _
  have hlim : Tendsto (fun j : ℕ ↦ Y 0 * (b ^ (-1 / α)) ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (Y 0)
  exact squeeze_zero hY (degiorgi_seq_le hN hb hα hY hrec h0) hlim

theorem four_pow_identity (j : ℕ) (α : ℝ) :
    ((4 : ℝ) ^ (j + 1)) ^ α * 4 ^ (j + 3) = (4 : ℝ) ^ (3 + α) * ((4 : ℝ) ^ (1 + α)) ^ j := by
  have h4 : (0 : ℝ) < 4 := by norm_num
  have e1 : ((4 : ℝ) ^ (j + 1)) = (4 : ℝ) ^ ((j : ℝ) + 1) := by
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  have e2 : ((4 : ℝ) ^ (j + 3)) = (4 : ℝ) ^ ((j : ℝ) + 3) := by
    rw [← Real.rpow_natCast]; push_cast; ring_nf
  have e3 : ((4 : ℝ) ^ (1 + α)) ^ j = (4 : ℝ) ^ ((1 + α) * j) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h4.le]
  rw [e1, e2, e3, ← Real.rpow_mul h4.le, ← Real.rpow_add h4, ← Real.rpow_add h4]
  congr 1
  ring

/-- The numerical core of one De Giorgi step. -/
theorem degiorgi_numeric {S Y I m C₀ C₁ c ρ H α : ℝ} (j : ℕ) (hY : 0 ≤ Y) (hI0 : 0 ≤ I)
    (hI : I ≤ Y) (hm0 : 0 ≤ m) (hm : m ≤ Y / (H / 2 ^ (j + 1)) ^ 2) (hC₀ : 0 ≤ C₀)
    (hC₁ : 0 ≤ C₁) (hρ : 0 < ρ) (hH : 0 < H) (hH1 : C₁ * ρ ^ 2 ≤ H ^ 2) (hα : 0 < α) :
    S ^ 2 * m ^ α * (2 * (C₀ / (ρ / 2 ^ (j + 3)) ^ 2 * I + C₁ * m) +
      2 * (c / (ρ / 2 ^ (j + 3))) ^ 2 * I) ≤
      (2 * (S ^ 2 + 1) * (C₀ + 1 + c ^ 2) * 4 ^ (3 + α)) / ((H ^ 2) ^ α * ρ ^ 2) *
        ((4 : ℝ) ^ (1 + α)) ^ j * Y ^ (1 + α) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hH2 : 0 < H ^ 2 := by positivity
  have h4j : (0 : ℝ) < 4 ^ (j + 1) := by positivity
  have e2 : ∀ n : ℕ, (2 : ℝ) ^ n * 2 ^ n = 4 ^ n := fun n ↦ by
    rw [← mul_pow]; norm_num
  set T := 4 ^ (j + 1) * Y / H ^ 2 with hT
  have hmT : m ≤ T := by
    refine hm.trans (le_of_eq ?_)
    rw [hT, div_pow, div_div_eq_mul_div, ← pow_mul, ← e2]
    ring_nf
  have hT0 : 0 ≤ T := by positivity
  have hdiv : ∀ x : ℝ, x / (ρ / 2 ^ (j + 3)) ^ 2 = x * 4 ^ (j + 3) / ρ ^ 2 := fun x ↦ by
    rw [div_pow, ← e2]; field_simp
  have hC₁m : C₁ * m ≤ 4 ^ (j + 3) * Y / ρ ^ 2 := by
    calc C₁ * m ≤ C₁ * T := mul_le_mul_of_nonneg_left hmT hC₁
      _ = C₁ * ρ ^ 2 * (4 ^ (j + 1) * Y) / (H ^ 2 * ρ ^ 2) := by
          rw [hT]; field_simp
      _ ≤ H ^ 2 * (4 ^ (j + 1) * Y) / (H ^ 2 * ρ ^ 2) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hH1 (by positivity))
            (by positivity)
      _ = 4 ^ (j + 1) * Y / ρ ^ 2 := by field_simp
      _ ≤ 4 ^ (j + 3) * Y / ρ ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hY) hρ2.le
  set Bk := 2 * (C₀ + 1 + c ^ 2) * (4 ^ (j + 3) * Y / ρ ^ 2) with hBk
  have hbr : 2 * (C₀ / (ρ / 2 ^ (j + 3)) ^ 2 * I + C₁ * m) +
      2 * (c / (ρ / 2 ^ (j + 3))) ^ 2 * I ≤ Bk := by
    have h1 : C₀ / (ρ / 2 ^ (j + 3)) ^ 2 * I ≤ C₀ * (4 ^ (j + 3) * Y / ρ ^ 2) := by
      rw [hdiv]
      calc C₀ * 4 ^ (j + 3) / ρ ^ 2 * I ≤ C₀ * 4 ^ (j + 3) / ρ ^ 2 * Y :=
            mul_le_mul_of_nonneg_left hI (by positivity)
        _ = C₀ * (4 ^ (j + 3) * Y / ρ ^ 2) := by ring
    have h2 : (c / (ρ / 2 ^ (j + 3))) ^ 2 * I ≤ c ^ 2 * (4 ^ (j + 3) * Y / ρ ^ 2) := by
      rw [div_pow, hdiv]
      calc c ^ 2 * 4 ^ (j + 3) / ρ ^ 2 * I ≤ c ^ 2 * 4 ^ (j + 3) / ρ ^ 2 * Y :=
            mul_le_mul_of_nonneg_left hI (by positivity)
        _ = c ^ 2 * (4 ^ (j + 3) * Y / ρ ^ 2) := by ring
    rw [hBk]
    linarith
  have hBk0 : 0 ≤ Bk := by positivity
  have hmα : m ^ α ≤ T ^ α := Real.rpow_le_rpow hm0 hmT hα.le
  have hTα : T ^ α = ((4 : ℝ) ^ (j + 1)) ^ α * Y ^ α / (H ^ 2) ^ α := by
    rw [hT, Real.div_rpow (by positivity) hH2.le, Real.mul_rpow h4j.le hY]
  calc S ^ 2 * m ^ α * (2 * (C₀ / (ρ / 2 ^ (j + 3)) ^ 2 * I + C₁ * m) +
        2 * (c / (ρ / 2 ^ (j + 3))) ^ 2 * I)
      ≤ (S ^ 2 + 1) * T ^ α * Bk :=
        mul_le_mul (mul_le_mul (by linarith) hmα (Real.rpow_nonneg hm0 _) (by positivity)) hbr
          (by positivity) (by positivity)
    _ = (2 * (S ^ 2 + 1) * (C₀ + 1 + c ^ 2)) / ((H ^ 2) ^ α * ρ ^ 2) *
          (((4 : ℝ) ^ (j + 1)) ^ α * 4 ^ (j + 3)) * (Y ^ α * Y) := by
        rw [hTα, hBk]
        have : (H ^ 2) ^ α ≠ 0 := (Real.rpow_pos_of_pos hH2 _).ne'
        field_simp
    _ = (2 * (S ^ 2 + 1) * (C₀ + 1 + c ^ 2) * 4 ^ (3 + α)) / ((H ^ 2) ^ α * ρ ^ 2) *
          ((4 : ℝ) ^ (1 + α)) ^ j * Y ^ (1 + α) := by
        rw [four_pow_identity, Real.rpow_add' hY (by linarith), Real.rpow_one]
        ring

theorem degiorgi_init_identity {A H ρ : ℝ} {d : ℕ} (hd : 1 ≤ d) (hA : 0 < A) (hH : 0 < H)
    (hρ : 0 < ρ) :
    (A / ((H ^ 2) ^ (2 / (d : ℝ)) * ρ ^ 2)) ^ (-1 / (2 / (d : ℝ))) =
      A ^ (-1 / (2 / (d : ℝ))) * H ^ 2 * ρ ^ d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set α : ℝ := 2 / (d : ℝ) with hα
  have hα0 : 0 < α := by positivity
  have hαe : α * (-1 / α) = -1 := by field_simp
  have h2e : (2 : ℝ) * (-1 / α) = -(d : ℝ) := by rw [hα]; field_simp
  have hH2 : 0 < H ^ 2 := by positivity
  have hρ2 : ρ ^ 2 = ρ ^ (2 : ℝ) := (Real.rpow_two ρ).symm
  rw [Real.div_rpow hA.le (by positivity), Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hH2.le, hαe, Real.rpow_neg_one, hρ2, ← Real.rpow_mul hρ.le, h2e,
    Real.rpow_neg hρ.le, Real.rpow_natCast]
  have : ρ ^ d ≠ 0 := by positivity
  field_simp

end EllipticBernoulli
