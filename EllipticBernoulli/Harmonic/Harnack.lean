/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Harmonic
public import EllipticBernoulli.Harmonic.MeanValue

/-!
# Harnack inequality on balls

* `HarmonicOnNhd.le_three_pow_mul_of_nonneg`: the local Harnack inequality `u x ≤ 3 ^ n * u y`
  on `ball c r`, for `u` harmonic and nonnegative on `ball c (4 * r)` (general `E`).
* `harnack_ball_explicit`, `harnack_ball` (`HarnackStatement`): every nonnegative harmonic
  function on `B_{2r}(x) ⊆ E d` satisfies `f(y) ≤ C f(z)` for `y, z ∈ B_r(x)`, with
  `C = (3 ^ d) ^ 8` (Gilbarg–Trudinger Thm 2.5). The hypothesis `1 ≤ d` of the statement is not
  needed by the proof.

## Proof of `harnack_ball`

Split the segment from `y` to `z` (which lies in `B_r(x)` and has length `< 2r`) into eight
pieces of length `< r / 4`, and chain the local estimate on `B_{r}(p_k) ⊆ B_{2r}(x)`.

## Provenance

* `HarmonicOnNhd.le_three_pow_mul_of_nonneg`: TauCeti, https://github.com/TauCetiProject/TauCeti,
  `TauCeti/Analysis/PDE/Harnack/Basic.lean`, commit 90cca67c0c8e91cd30b0d46cb58101f8c5c59236
  (Apache-2.0; `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`); unchanged
  up to the namespace. The rest of the file is original to this project.
-/

open InnerProductSpace Metric Set Module

public section

namespace EllipticBernoulli

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {u : E → ℝ} {x y c : E} {r : ℝ}

/-- **The local Harnack inequality.** If `u` is harmonic and nonnegative on `ball c (4 * r)`, then
any two of its values on `ball c r` are within the factor `3 ^ n` of each other, where `n` is the
dimension of `E`. -/
theorem HarmonicOnNhd.le_three_pow_mul_of_nonneg
    (hu : HarmonicOnNhd u (ball c (4 * r))) (hnonneg : ∀ z ∈ ball c (4 * r), 0 ≤ u z)
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) :
    u x ≤ 3 ^ finrank ℝ E * u y := by
  have hr : 0 < r := pos_of_mem_ball hx
  rw [mem_ball] at hx hy
  have hsub : closedBall y (3 * r) ⊆ ball c (4 * r) :=
    closedBall_subset_ball' (by linarith)
  have hxy : r + dist x y ≤ 3 * r := by linarith [dist_triangle_right x y c]
  have := HarmonicOnNhd.le_div_pow_mul_of_nonneg (hu.mono hsub)
    (fun z hz ↦ hnonneg z (hsub (ball_subset_closedBall hz))) hr hxy
  rwa [mul_div_cancel_right₀ 3 hr.ne'] at this

end General

/-- **Harnack inequality on concentric balls**, with the explicit constant `(3 ^ d) ^ 8`. -/
theorem harnack_ball_explicit {d : ℕ} (f : E d → ℝ) (x : E d) (r : ℝ) (_hr : 0 < r)
    (hf : HarmonicOnNhd f (ball x (2 * r))) (hf0 : ∀ y ∈ ball x (2 * r), 0 ≤ f y) :
    ∀ y ∈ ball x r, ∀ z ∈ ball x r, f y ≤ ((3 : ℝ) ^ d) ^ 8 * f z := by
  intro y hy z hz
  set p : ℕ → E d := fun k ↦ y + ((k : ℝ) / 8) • (z - y) with hp
  have hp_mem : ∀ k ≤ 8, p k ∈ ball x r := fun k hk ↦
    (convex_ball x r).add_smul_sub_mem hy hz
      ⟨by positivity, by rw [div_le_one (by norm_num)]; exact_mod_cast hk⟩
  have hzy : dist z y < 2 * r := by
    rw [mem_ball] at hy hz
    linarith [dist_triangle_right z y x]
  have hstep : ∀ k < 8, f (p k) ≤ 3 ^ d * f (p (k + 1)) := by
    intro k hk
    have hc := hp_mem k hk.le
    have hsub : ball (p k) (4 * (r / 4)) ⊆ ball x (2 * r) :=
      ball_subset_ball' (by rw [mem_ball] at hc; linarith)
    have hdiff : p (k + 1) - p k = (1 / 8 : ℝ) • (z - y) := by
      simp only [hp]
      push_cast
      module
    have hmem : p (k + 1) ∈ ball (p k) (r / 4) := by
      rw [mem_ball, dist_eq_norm, hdiff, norm_smul, ← dist_eq_norm]
      norm_num
      linarith
    have := HarmonicOnNhd.le_three_pow_mul_of_nonneg (c := p k) (r := r / 4)
      (hf.mono hsub) (fun w hw ↦ hf0 w (hsub hw))
      (mem_ball_self (by positivity)) hmem
    rwa [finrank_euclideanSpace_fin] at this
  have hind : ∀ k ≤ 8, f y ≤ ((3 : ℝ) ^ d) ^ k * f (p k) := by
    intro k hk
    induction k with
    | zero => simp [hp]
    | succ k ih =>
      calc f y ≤ ((3 : ℝ) ^ d) ^ k * f (p k) := ih (by omega)
        _ ≤ ((3 : ℝ) ^ d) ^ k * (3 ^ d * f (p (k + 1))) :=
          mul_le_mul_of_nonneg_left (hstep k (by omega)) (by positivity)
        _ = ((3 : ℝ) ^ d) ^ (k + 1) * f (p (k + 1)) := by ring
  have h8 : p 8 = z := by simp [hp]
  simpa [h8] using hind 8 le_rfl

/-- Harnack inequality on balls (`HarnackStatement`), with `C = (3 ^ d) ^ 8`. -/
theorem harnack_ball : HarnackStatement := fun {d} _ ↦
  ⟨((3 : ℝ) ^ d) ^ 8, harnack_ball_explicit⟩

end EllipticBernoulli
