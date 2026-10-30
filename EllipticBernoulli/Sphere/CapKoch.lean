/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.CapHadamard
import EllipticBernoulli.Sphere.CapODE
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Koch convexity of `Λ_d` for `d ≥ 5`

The convexity of the first eigenvalue `Λ_d(θ)` of a spherical cap as a function of the colatitude
`θ`, for `d ≥ 5`. This is Salato (arXiv:2506.13473), Proposition 4.1, whose proof follows Koch
(arXiv:1502.07290), Theorem 1: after the Liouville substitution `v = sin^k y`, `Λ_d(θ)` is the
ground state energy of a one-dimensional Schrödinger operator on `(0, θ)` whose potential is
convex when `d ≥ 5`, and the ground state energy is convex in the endpoint.

* `capShootFlux_mul_capShootDeriv_eq`: **Pohozaev identity** (written for `y` instead of the
  Liouville form `v = sin^k y`). If `m ≥ 3` and `y(θ, λ) = 0`, then
  `sin^m(θ) y'(θ)² = (m (m - 2) / 2) ∫_0^θ sin^{m-3} cos y²`. The energy is
  `E = sin^m y'² + m sin^{m-1} cos y y' + (m/2) sin^{m-2} y² + λ sin^m y²`, with
  `E' = (m (m - 2)/2) sin^{m-3} cos y²` and `E(0) = 0`.
* `hasDerivAt_capEigenvalue_eq`: with Hadamard, `Λ_d'(θ) = -(m (m-2)/2) ∫_0^θ f ρ_θ`, where
  `f = cos / sin³` (that is, `V' = -(m (m-2)/2) f` for the Liouville potential) and
  `ρ_θ = sin^m y_θ² / ∫_0^θ sin^m y_θ²`.
* `capKochRatio_le`: `θ ↦ ∫_0^θ f ρ_θ` is nonincreasing. For `θ₁ < θ₂` the ratio
  `y_{θ₂} / y_{θ₁}` is nondecreasing on `[0, θ₁)` (Wronskian identity), so `ρ_{θ₂} - ρ_{θ₁}`
  changes sign once, from `-` to `+`, at some `t₀`; since `f` is decreasing,
  `∫ f (ρ_{θ₂} - ρ_{θ₁}) = ∫ (f - f(t₀)) (ρ_{θ₂} - ρ_{θ₁}) ≤ 0`.
* `convexOn_capEigenvalue`: **Koch convexity.** For `d ≥ 5`, `Λ_d` is
  convex on `(0, π)`.
* `two_mul_sub_one_le_capEigenvalue_add`: `Λ_d(θ) + Λ_d(π - θ) ≥ 2 Λ_d(π/2) = 2 (d - 1)`.

Koch differentiates once more in the endpoint and uses that `w = ∂_θ v / v` changes sign once.
Here only `Λ_d'` is used: the monotonicity of the ratio `y_{θ₂} / y_{θ₁}` is the finite-difference
form of `w` increasing, and convexity follows from the monotonicity of `Λ_d'`. The argument works
with `y` rather than with the Liouville form, so no real powers of `sin` occur, and it covers every
`d ≥ 5`.

## References

* H. Koch, *Convexity and concavity of the ground state energy*, New York J. Math. 21 (2015),
  1003–1005; arXiv:1502.07290.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473 (v2).
-/

open Set Filter Topology MeasureTheory Real

public section

namespace EllipticBernoulli

variable {m d : ℕ}

/-! ### The Pohozaev identity -/

/-- `y'' = -λ y - m (cos / sin) y'` on `(0, π)`. -/
theorem hasDerivAt_capShootDeriv (m : ℕ) (lam : ℝ) {x : ℝ} (hx : x ∈ Ioo 0 π) :
    HasDerivAt (capShootDeriv m lam)
      (-(lam * capShoot m lam x) - m * cos x / sin x * capShootDeriv m lam x) x := by
  have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have h := (hasDerivAt_capShootFlux m lam hx).div ((hasDerivAt_sin x).pow m)
    (pow_pos hs m).ne'
  convert h using 1
  · funext y; simp [capShootDeriv]
  simp only [Pi.pow_apply]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp [capShootDeriv]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [capShootDeriv, Nat.add_sub_cancel]
  field_simp
  push_cast
  ring

/-- **Pohozaev identity.** Let `m ≥ 3`, `θ ∈ (0, π)` and
`y(θ, λ) = 0`. Then `H(θ) y'(θ) = (m (m - 2) / 2) ∫_0^θ sin^{m-3} cos y²`, where `H = sin^m y'`. -/
theorem capShootFlux_mul_capShootDeriv_eq (hm : 3 ≤ m) {lam θ : ℝ} (hθ : θ ∈ Ioo 0 π)
    (hy : capShoot m lam θ = 0) :
    capShootFlux m lam θ * capShootDeriv m lam θ =
      (m * ((m : ℝ) - 2) / 2) * ∫ t in 0..θ, sin t ^ (m - 3) * cos t * capShoot m lam t ^ 2 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
  set y := capShoot (j + 3) lam
  set D := capShootDeriv (j + 3) lam
  set E : ℝ → ℝ := fun x ↦ sin x ^ (j + 3) * D x ^ 2 +
    ((j : ℝ) + 3) * sin x ^ (j + 2) * cos x * y x * D x +
    ((j : ℝ) + 3) / 2 * sin x ^ (j + 1) * y x ^ 2 + lam * sin x ^ (j + 3) * y x ^ 2
  have hyc : ContinuousOn y (Icc 0 θ) :=
    (continuousOn_capShoot_left _ lam).mono fun x hx ↦ ⟨hx.1, hx.2.trans_lt hθ.2⟩
  have hDc : ContinuousOn D (Icc 0 θ) :=
    (continuousOn_capShootDeriv_left _ lam).mono fun x hx ↦ ⟨hx.1, hx.2.trans_lt hθ.2⟩
  have hEc : ContinuousOn E (Icc 0 θ) := by
    simp only [E]
    have hs : ∀ k, ContinuousOn (fun x : ℝ ↦ sin x ^ k) (Icc 0 θ) :=
      fun k ↦ (continuous_sin.pow k).continuousOn
    exact ((((hs _).mul (hDc.pow 2)).add
      ((((continuousOn_const.mul (hs _)).mul continuous_cos.continuousOn).mul hyc).mul hDc)).add
      ((continuousOn_const.mul (hs _)).mul (hyc.pow 2))).add
      ((continuousOn_const.mul (hs _)).mul (hyc.pow 2))
  have hEd : ∀ x ∈ Ioo 0 θ, HasDerivAt E
      (((j : ℝ) + 3) * ((j : ℝ) + 1) / 2 * (sin x ^ j * cos x * y x ^ 2)) x := by
    intro x hx
    have hxπ : x ∈ Ioo 0 π := ⟨hx.1, hx.2.trans hθ.2⟩
    have hs : 0 < sin x := sin_pos_of_pos_of_lt_pi hxπ.1 hxπ.2
    have hy' := hasDerivAt_capShoot (j + 3) lam hxπ
    have hD' := hasDerivAt_capShootDeriv (j + 3) lam hxπ
    have hsin := hasDerivAt_sin x
    have hcos := hasDerivAt_cos x
    have h := ((((hsin.pow (j + 3)).mul (hD'.pow 2)).add
      ((((((hsin.pow (j + 2)).const_mul ((j : ℝ) + 3)).mul hcos).mul hy').mul hD'))).add
      (((hsin.pow (j + 1)).const_mul (((j : ℝ) + 3) / 2)).mul (hy'.pow 2))).add
      (((hsin.pow (j + 3)).const_mul lam).mul (hy'.pow 2))
    convert h using 1
    simp only [Pi.mul_apply, Pi.pow_apply, show j + 3 - 1 = j + 2 by omega,
      show j + 2 - 1 = j + 1 by omega, show j + 1 - 1 = j by omega, show 2 - 1 = 1 by rfl,
      pow_one, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    have hc := sin_sq_add_cos_sq x
    simp only [y]
    generalize capShoot (j + 3) lam x = Y
    generalize capShootDeriv (j + 3) lam x = P
    have hS : sin x ≠ 0 := hs.ne'
    generalize sin x = S at hc hS ⊢
    generalize cos x = C at hc ⊢
    field_simp
    linear_combination (2 * ((j : ℝ) + 3) * S ^ (j + 2) * Y * P) * hc
  have hint : IntervalIntegrable
      (fun x ↦ ((j : ℝ) + 3) * ((j : ℝ) + 1) / 2 * (sin x ^ j * cos x * y x ^ 2)) volume 0 θ :=
    (continuousOn_const.mul ((((continuous_sin.pow j).continuousOn).mul
      continuous_cos.continuousOn).mul (hyc.pow 2))).intervalIntegrable_of_Icc hθ.1.le
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hθ.1.le hEc hEd hint
  have hE0 : E 0 = 0 := by simp [E]
  have hEθ : E θ = capShootFlux (j + 3) lam θ * D θ := by
    simp only [E, hy]
    have hs : sin θ ^ (j + 3) ≠ 0 := (pow_pos (sin_pos_of_pos_of_lt_pi hθ.1 hθ.2) _).ne'
    simp only [D, capShootDeriv]
    field_simp
    ring
  rw [hE0, sub_zero, hEθ, intervalIntegral.integral_const_mul] at hFTC
  simp only [D] at hFTC
  rw [← hFTC, show j + 3 - 3 = j by omega]
  push_cast
  ring_nf

/-! ### The derivative of `Λ_d` -/

/-- The ratio `∫_0^θ sin^{m-3} cos y_θ² / ∫_0^θ sin^m y_θ²` (with `m = d - 2` and
`y_θ = y(·, Λ_d(θ))`), that is `∫_0^θ f ρ_θ` with `f = cos / sin³`. -/
noncomputable def capKochRatio (d : ℕ) (θ : ℝ) : ℝ :=
  (∫ t in 0..θ, sin t ^ (d - 2 - 3) * cos t *
      (capShoot (d - 2) (capEigenvalue d θ) t * capShoot (d - 2) (capEigenvalue d θ) t)) /
    ∫ t in 0..θ, sin t ^ (d - 2) *
      (capShoot (d - 2) (capEigenvalue d θ) t * capShoot (d - 2) (capEigenvalue d θ) t)

/-- **The derivative of `Λ_d`** (Hadamard and Pohozaev). For `d ≥ 5`, `m = d - 2` and
`θ ∈ (0, π)`, `Λ_d'(θ) = -(m (m - 2) / 2) ∫_0^θ f ρ_θ`. -/
theorem hasDerivAt_capEigenvalue_eq (hd : 5 ≤ d) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (capEigenvalue d)
      (-(((d - 2 : ℕ) : ℝ) * (((d - 2 : ℕ) : ℝ) - 2) / 2) * capKochRatio d θ) θ := by
  have h := hasDerivAt_capEigenvalue (d := d) hθ
  have hy := (capShoot_capEigenvalue (d := d) hθ.1 hθ.2).2.2
  rw [capShootFlux_mul_capShootDeriv_eq (by omega) hθ hy] at h
  convert h using 1
  rw [capKochRatio]
  simp only [sq, mul_assoc]
  ring

/-! ### Monotonicity of the ratio -/

/-- `f = cos / sin³` is nonincreasing on `(0, π)`. -/
theorem antitoneOn_cos_div_sin_pow_three : AntitoneOn (fun t ↦ cos t / sin t ^ 3) (Ioo 0 π) := by
  have hd : ∀ t ∈ Ioo 0 π, HasDerivAt (fun t ↦ cos t / sin t ^ 3)
      ((-sin t * sin t ^ 3 - cos t * (3 * sin t ^ 2 * cos t)) / (sin t ^ 3) ^ 2) t := by
    intro t ht
    have hs := (pow_pos (sin_pos_of_pos_of_lt_pi ht.1 ht.2) 3).ne'
    convert (hasDerivAt_cos t).div ((hasDerivAt_sin t).pow 3) hs using 1
  refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 π) (fun t ht ↦ (hd t ht).continuousAt
    |>.continuousWithinAt) (fun t ht ↦ ?_) fun t ht ↦ ?_
  · rw [interior_Ioo] at ht
    exact (hd t ht).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo] at ht
    rw [(hd t ht).deriv]
    have hs := sin_pos_of_pos_of_lt_pi ht.1 ht.2
    refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
    nlinarith [pow_pos hs 4, sq_nonneg (cos t), sq_nonneg (sin t)]

/-- A linear combination of four interval integrals. -/
private theorem integral_lin_four {a b c₁ c₂ c₃ c₄ : ℝ} {f₁ f₂ f₃ f₄ : ℝ → ℝ}
    (h₁ : IntervalIntegrable f₁ volume a b) (h₂ : IntervalIntegrable f₂ volume a b)
    (h₃ : IntervalIntegrable f₃ volume a b) (h₄ : IntervalIntegrable f₄ volume a b) :
    ∫ x in a..b, (c₁ * f₁ x + c₂ * f₂ x + c₃ * f₃ x + c₄ * f₄ x) =
      c₁ * (∫ x in a..b, f₁ x) + c₂ * (∫ x in a..b, f₂ x) + c₃ * (∫ x in a..b, f₃ x) +
        c₄ * ∫ x in a..b, f₄ x := by
  rw [intervalIntegral.integral_add ((h₁.const_mul c₁).add (h₂.const_mul c₂) |>.add
      (h₃.const_mul c₃)) (h₄.const_mul c₄),
    intervalIntegral.integral_add ((h₁.const_mul c₁).add (h₂.const_mul c₂)) (h₃.const_mul c₃),
    intervalIntegral.integral_add (h₁.const_mul c₁) (h₂.const_mul c₂)]
  simp only [intervalIntegral.integral_const_mul]

/-- **Monotonicity of `∫ f ρ_θ`** (the one-sign-change argument, in finite-difference form). For
`d ≥ 5` and `0 < θ₁ < θ₂ < π`, `capKochRatio d θ₂ ≤ capKochRatio d θ₁`. -/
theorem capKochRatio_le (hd : 5 ≤ d) {θ₁ θ₂ : ℝ} (h₁ : 0 < θ₁) (h12 : θ₁ < θ₂) (h₂ : θ₂ < π) :
    capKochRatio d θ₂ ≤ capKochRatio d θ₁ := by
  set m := d - 2 with hm_def
  have hm : 3 ≤ m := by omega
  have h₁π : θ₁ < π := h12.trans h₂
  obtain ⟨-, hp₁, hz₁⟩ := capShoot_capEigenvalue (d := d) h₁ h₁π
  obtain ⟨-, hp₂, hz₂⟩ := capShoot_capEigenvalue (d := d) (h₁.trans h12) h₂
  set l₁ := capEigenvalue d θ₁
  set l₂ := capEigenvalue d θ₂
  set y₁ := capShoot m l₁
  set y₂ := capShoot m l₂
  have hl : l₂ ≤ l₁ := capEigenvalue_le_of_le h₁ h12.le h₂.le
  have hy₁c : ContinuousOn y₁ (Icc 0 θ₂) := (isCapSolution_capShoot m l₁ h₂).continuousOn
  have hy₂c : ContinuousOn y₂ (Icc 0 θ₂) := (isCapSolution_capShoot m l₂ h₂).continuousOn
  have hsub₁ : Icc 0 θ₁ ⊆ Icc 0 θ₂ := Icc_subset_Icc le_rfl h12.le
  have hsub₂ : Icc θ₁ θ₂ ⊆ Icc 0 θ₂ := Icc_subset_Icc h₁.le le_rfl
  -- the ratio `q = y₂ / y₁` is nondecreasing on `[0, θ₁)`
  set q : ℝ → ℝ := fun x ↦ y₂ x / y₁ x
  have hq : MonotoneOn q (Ico 0 θ₁) := by
    have hqd : ∀ x ∈ Ioo 0 θ₁, HasDerivAt q
        ((capShootDeriv m l₂ x * y₁ x - y₂ x * capShootDeriv m l₁ x) / y₁ x ^ 2) x :=
      fun x hx ↦ (hasDerivAt_capShoot m l₂ ⟨hx.1, hx.2.trans h₁π⟩).div
        (hasDerivAt_capShoot m l₁ ⟨hx.1, hx.2.trans h₁π⟩) (hp₁ x ⟨hx.1.le, hx.2⟩).ne'
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 θ₁) ?_ (fun x hx ↦ ?_) fun x hx ↦ ?_
    · exact (hy₂c.mono (Ico_subset_Icc_self.trans hsub₁)).div
        (hy₁c.mono (Ico_subset_Icc_self.trans hsub₁)) fun x hx ↦ (hp₁ x hx).ne'
    · rw [interior_Ico] at hx
      exact (hqd x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Ico] at hx
      rw [(hqd x hx).deriv]
      refine div_nonneg ?_ (sq_nonneg _)
      have hW := capShoot_wronskian m l₁ l₂ ⟨hx.1.le, hx.2.trans h₁π⟩
      have hs := pow_pos (sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans h₁π)) m
      have hI : 0 ≤ ∫ t in 0..x, sin t ^ m * (y₁ t * y₂ t) :=
        intervalIntegral.integral_nonneg hx.1.le fun t ht ↦ mul_nonneg
          (pow_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, hx.2])) m)
          (mul_nonneg (hp₁ t ⟨ht.1, ht.2.trans_lt hx.2⟩).le
            (hp₂ t ⟨ht.1, ht.2.trans_lt (hx.2.trans h12)⟩).le)
      have hnum : capShootDeriv m l₂ x * y₁ x - y₂ x * capShootDeriv m l₁ x =
          (y₁ x * capShootFlux m l₂ x - capShootFlux m l₁ x * y₂ x) / sin x ^ m := by
        simp only [capShootDeriv]; field_simp
      rw [hnum, hW]
      exact div_nonneg (mul_nonneg (sub_nonneg.2 hl) hI) hs.le
  have hq0 : q 0 = 1 := by simp [q, y₁, y₂]
  have hge : ∀ x ∈ Ico 0 θ₁, y₁ x ≤ y₂ x := fun x hx ↦ by
    have h := hq ⟨le_rfl, h₁⟩ hx hx.1
    rw [hq0] at h
    simp only [q] at h
    rwa [one_le_div (hp₁ x hx)] at h
  -- notation for the integrands
  set v : ℝ → ℝ := fun t ↦ sin t ^ m
  set w : ℝ → ℝ := fun t ↦ sin t ^ (m - 3) * cos t
  set f : ℝ → ℝ := fun t ↦ cos t / sin t ^ 3
  have hwv : ∀ t ∈ Ioo 0 π, w t = v t * f t := fun t ht ↦ by
    have hs := (sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    obtain ⟨j, hj⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    simp only [w, v, f, hj, Nat.add_sub_cancel]
    field_simp
    ring
  have hvc : Continuous v := continuous_sin.pow m
  have hwc : Continuous w := (continuous_sin.pow _).mul continuous_cos
  have hII : ∀ (g : ℝ → ℝ), ContinuousOn g (Icc 0 θ₂) → ∀ a ∈ Icc 0 θ₂, ∀ b ∈ Icc 0 θ₂,
      IntervalIntegrable g volume a b := fun g hg a ha b hb ↦
    (hg.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have h0 : (0 : ℝ) ∈ Icc 0 θ₂ := ⟨le_rfl, (h₁.trans h12).le⟩
  have hθ₁ : θ₁ ∈ Icc 0 θ₂ := ⟨h₁.le, h12.le⟩
  have hθ₂ : θ₂ ∈ Icc 0 θ₂ := ⟨(h₁.trans h12).le, le_rfl⟩
  have hc11 : ContinuousOn (fun t ↦ v t * (y₁ t * y₁ t)) (Icc 0 θ₂) :=
    hvc.continuousOn.mul (hy₁c.mul hy₁c)
  have hc22 : ContinuousOn (fun t ↦ v t * (y₂ t * y₂ t)) (Icc 0 θ₂) :=
    hvc.continuousOn.mul (hy₂c.mul hy₂c)
  have hd11 : ContinuousOn (fun t ↦ w t * (y₁ t * y₁ t)) (Icc 0 θ₂) :=
    hwc.continuousOn.mul (hy₁c.mul hy₁c)
  have hd22 : ContinuousOn (fun t ↦ w t * (y₂ t * y₂ t)) (Icc 0 θ₂) :=
    hwc.continuousOn.mul (hy₂c.mul hy₂c)
  set Z₁ := ∫ t in 0..θ₁, v t * (y₁ t * y₁ t)
  set Z₂a := ∫ t in 0..θ₁, v t * (y₂ t * y₂ t)
  set Z₂b := ∫ t in θ₁..θ₂, v t * (y₂ t * y₂ t)
  set N₁ := ∫ t in 0..θ₁, w t * (y₁ t * y₁ t)
  set N₂a := ∫ t in 0..θ₁, w t * (y₂ t * y₂ t)
  set N₂b := ∫ t in θ₁..θ₂, w t * (y₂ t * y₂ t)
  have hZ₂ : ∫ t in 0..θ₂, v t * (y₂ t * y₂ t) = Z₂a + Z₂b :=
    (intervalIntegral.integral_add_adjacent_intervals (hII _ hc22 0 h0 θ₁ hθ₁)
      (hII _ hc22 θ₁ hθ₁ θ₂ hθ₂)).symm
  have hN₂ : ∫ t in 0..θ₂, w t * (y₂ t * y₂ t) = N₂a + N₂b :=
    (intervalIntegral.integral_add_adjacent_intervals (hII _ hd22 0 h0 θ₁ hθ₁)
      (hII _ hd22 θ₁ hθ₁ θ₂ hθ₂)).symm
  have hZ₁pos : 0 < Z₁ := integral_sin_pow_mul_capShoot_pos (m := m) h₁ h₁π hp₁ hp₁
  have hZ₂a : Z₁ ≤ Z₂a := by
    refine intervalIntegral.integral_mono_on h₁.le (hII _ hc11 0 h0 θ₁ hθ₁)
      (hII _ hc22 0 h0 θ₁ hθ₁) fun t ht ↦ ?_
    have hv : 0 ≤ v t := pow_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2])) m
    rcases ht.2.lt_or_eq with h | h
    · have h1 := (hp₁ t ⟨ht.1, h⟩).le
      have h2 := hge t ⟨ht.1, h⟩
      exact mul_le_mul_of_nonneg_left (mul_le_mul h2 h2 h1 (h1.trans h2)) hv
    · rw [h] at hv ⊢
      rw [hz₁, mul_zero, mul_zero]
      exact mul_nonneg hv (mul_self_nonneg _)
  have hZ₂b : 0 < Z₂b := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hII _ hc22 θ₁ hθ₁ θ₂ hθ₂)
      (fun t ht ↦ ?_) h12
    have h2 := hp₂ t ⟨(h₁.trans ht.1).le, ht.2⟩
    exact mul_pos (pow_pos (sin_pos_of_pos_of_lt_pi (h₁.trans ht.1) (ht.2.trans h₂)) m)
      (mul_pos h2 h2)
  set Z₂ := Z₂a + Z₂b
  have hZ12 : Z₁ < Z₂ := by simp only [Z₂]; linarith
  have hZ₂pos : 0 < Z₂ := hZ₁pos.trans hZ12
  -- the crossing point `t₀`
  set φ : ℝ → ℝ := fun t ↦ Z₂ * (y₁ t * y₁ t) - Z₁ * (y₂ t * y₂ t)
  set A := {t : ℝ | t ∈ Ico 0 θ₁ ∧ 0 < φ t}
  have hφ0 : 0 < φ 0 := by simp only [φ, y₁, y₂, capShoot_zero_right]; linarith
  have hA0 : (0 : ℝ) ∈ A := ⟨⟨le_rfl, h₁⟩, hφ0⟩
  have hAbdd : BddAbove A := ⟨θ₁, fun t ht ↦ ht.1.2.le⟩
  set t₀ := sSup A
  have ht₀θ₁ : t₀ ≤ θ₁ := csSup_le ⟨0, hA0⟩ fun t ht ↦ ht.1.2.le
  have ht₀pos : 0 < t₀ := by
    have hφc : ContinuousWithinAt φ (Ioi 0) 0 := by
      have hc : ContinuousOn φ (Icc 0 θ₂) :=
        (continuousOn_const.mul (hy₁c.mul hy₁c)).sub (continuousOn_const.mul (hy₂c.mul hy₂c))
      exact (hc 0 h0).mono_of_mem_nhdsWithin
        (mem_of_superset (Ioo_mem_nhdsGT (h₁.trans h12)) fun t ht ↦ ⟨ht.1.le, ht.2.le⟩)
    obtain ⟨c, hc1, hc2⟩ := ((hφc.tendsto.eventually_const_lt hφ0).and
      (Ioo_mem_nhdsGT h₁)).exists
    exact hc2.1.trans_le (le_csSup hAbdd ⟨⟨hc2.1.le, hc2.2⟩, hc1⟩)
  have hft₀ := antitoneOn_cos_div_sin_pow_three
  set c₀ := f t₀
  -- sign on `(0, θ₁)`
  have hsignA : ∀ t ∈ Ioo 0 θ₁,
      (w t - c₀ * v t) * (Z₁ * (y₂ t * y₂ t) - Z₂ * (y₁ t * y₁ t)) ≤ 0 := by
    intro t ht
    have htπ : t ∈ Ioo 0 π := ⟨ht.1, ht.2.trans h₁π⟩
    have ht₀π : t₀ ∈ Ioo 0 π := ⟨ht₀pos, ht₀θ₁.trans_lt h₁π⟩
    have hv : 0 ≤ v t := (pow_pos (sin_pos_of_pos_of_lt_pi htπ.1 htπ.2) m).le
    rw [hwv t htπ, show v t * f t - c₀ * v t = v t * (f t - c₀) by ring]
    rcases lt_trichotomy t t₀ with h | h | h
    · -- `t < t₀`: `φ t > 0` and `f t ≥ f t₀`
      obtain ⟨a, haA, hta⟩ := exists_lt_of_lt_csSup ⟨0, hA0⟩ h
      have hy₁t := hp₁ t ⟨ht.1.le, ht.2⟩
      have hy₁a := hp₁ a haA.1
      have hqta : q t ≤ q a := hq ⟨ht.1.le, ht.2⟩ haA.1 hta.le
      have hq1 : 1 ≤ q t := by
        simp only [q]; rw [one_le_div hy₁t]; exact hge t ⟨ht.1.le, ht.2⟩
      have hφa := haA.2
      simp only [φ] at hφa
      have hφt : 0 < φ t := by
        simp only [φ]
        have e₁ : y₂ t = q t * y₁ t := by simp only [q]; field_simp
        have e₂ : y₂ a = q a * y₁ a := by simp only [q]; field_simp
        rw [e₂] at hφa
        rw [e₁]
        have hqa : q t * q t ≤ q a * q a := mul_le_mul hqta hqta (by linarith) (by linarith)
        have h' : Z₁ * (q a * q a) < Z₂ := by
          have := mul_pos hy₁a hy₁a
          nlinarith
        have h'' : Z₁ * (q t * q t) < Z₂ := lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left hqa hZ₁pos.le) h'
        have := mul_pos hy₁t hy₁t
        nlinarith
      have hf : c₀ ≤ f t := hft₀ htπ ht₀π h.le
      simp only [φ] at hφt
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hv (sub_nonneg.2 hf)) (by linarith)
    · rw [h, sub_self, mul_zero, zero_mul]
    · -- `t > t₀`: `φ t ≤ 0` and `f t ≤ f t₀`
      have hnA : t ∉ A := fun htA ↦ (lt_irrefl t₀) (h.trans_le (le_csSup hAbdd htA))
      have hφt : φ t ≤ 0 := by
        by_contra hcon
        exact hnA ⟨⟨ht.1.le, ht.2⟩, lt_of_not_ge hcon⟩
      have hf : f t ≤ c₀ := hft₀ ht₀π htπ h.le
      simp only [φ] at hφt
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hv (sub_nonpos.2 hf))
        (by linarith)
  -- sign on `(θ₁, θ₂)`
  have hsignB : ∀ t ∈ Ioo θ₁ θ₂, (w t - c₀ * v t) * (Z₁ * (y₂ t * y₂ t)) ≤ 0 := by
    intro t ht
    have htπ : t ∈ Ioo 0 π := ⟨h₁.trans ht.1, ht.2.trans h₂⟩
    have ht₀π : t₀ ∈ Ioo 0 π := ⟨ht₀pos, ht₀θ₁.trans_lt h₁π⟩
    have hv : 0 ≤ v t := (pow_pos (sin_pos_of_pos_of_lt_pi htπ.1 htπ.2) m).le
    rw [hwv t htπ, show v t * f t - c₀ * v t = v t * (f t - c₀) by ring]
    have hf : f t ≤ c₀ := hft₀ ht₀π htπ (ht₀θ₁.trans ht.1.le)
    exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hv (sub_nonpos.2 hf))
      (mul_nonneg hZ₁pos.le (mul_self_nonneg _))
  -- integrate the signs
  have hIA : ∫ t in 0..θ₁, (w t - c₀ * v t) * (Z₁ * (y₂ t * y₂ t) - Z₂ * (y₁ t * y₁ t)) ≤ 0 := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) h₁.le
      (g := fun _ ↦ (0 : ℝ)) (((hwc.continuousOn.sub (continuousOn_const.mul hvc.continuousOn)).mul
        ((continuousOn_const.mul (hy₂c.mul hy₂c)).sub
          (continuousOn_const.mul (hy₁c.mul hy₁c)))).mono hsub₁ |>.intervalIntegrable_of_Icc h₁.le)
      intervalIntegrable_const hsignA
    simpa using this
  have hIB : ∫ t in θ₁..θ₂, (w t - c₀ * v t) * (Z₁ * (y₂ t * y₂ t)) ≤ 0 := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) h12.le
      (g := fun _ ↦ (0 : ℝ)) (((hwc.continuousOn.sub (continuousOn_const.mul hvc.continuousOn)).mul
        (continuousOn_const.mul (hy₂c.mul hy₂c))).mono hsub₂ |>.intervalIntegrable_of_Icc h12.le)
      intervalIntegrable_const hsignB
    simpa using this
  have eA : ∫ t in 0..θ₁, (w t - c₀ * v t) * (Z₁ * (y₂ t * y₂ t) - Z₂ * (y₁ t * y₁ t)) =
      Z₁ * N₂a + (-Z₂) * N₁ + (-(c₀ * Z₁)) * Z₂a + (c₀ * Z₂) * Z₁ := by
    rw [← integral_lin_four (hII _ hd22 0 h0 θ₁ hθ₁) (hII _ hd11 0 h0 θ₁ hθ₁)
      (hII _ hc22 0 h0 θ₁ hθ₁) (hII _ hc11 0 h0 θ₁ hθ₁)]
    congr 1; funext t; ring
  have eB : ∫ t in θ₁..θ₂, (w t - c₀ * v t) * (Z₁ * (y₂ t * y₂ t)) =
      Z₁ * N₂b + (-(c₀ * Z₁)) * Z₂b + 0 * Z₂b + 0 * Z₂b := by
    rw [← integral_lin_four (hII _ hd22 θ₁ hθ₁ θ₂ hθ₂) (hII _ hc22 θ₁ hθ₁ θ₂ hθ₂)
      (hII _ hc22 θ₁ hθ₁ θ₂ hθ₂) (hII _ hc22 θ₁ hθ₁ θ₂ hθ₂)]
    congr 1; funext t; ring
  rw [eA] at hIA
  rw [eB] at hIB
  have key : Z₁ * (N₂a + N₂b) ≤ Z₂ * N₁ := by
    simp only [Z₂] at hIA ⊢
    nlinarith
  -- conclude
  have hR₁ : capKochRatio d θ₁ = N₁ / Z₁ := rfl
  have hR₂ : capKochRatio d θ₂ = (N₂a + N₂b) / Z₂ := by
    rw [capKochRatio, ← hN₂, ← hZ₂]
  rw [hR₁, hR₂, div_le_div_iff₀ hZ₂pos hZ₁pos]
  linarith

/-! ### Koch convexity -/

/-- **Koch convexity** (Koch, arXiv:1502.07290, Theorem 1; Salato, arXiv:2506.13473,
Proposition 4.1). For `d ≥ 5`,
`Λ_d` is convex on `(0, π)`. -/
theorem convexOn_capEigenvalue (hd : 5 ≤ d) : ConvexOn ℝ (Ioo 0 π) (capEigenvalue d) := by
  refine MonotoneOn.convexOn_of_deriv (convex_Ioo 0 π) (continuousOn_capEigenvalue d)
    (fun θ hθ ↦ ?_) ?_
  · rw [interior_Ioo] at hθ
    exact (hasDerivAt_capEigenvalue_eq hd hθ).differentiableAt.differentiableWithinAt
  · rw [interior_Ioo]
    intro a ha b hb hab
    rw [(hasDerivAt_capEigenvalue_eq hd ha).deriv, (hasDerivAt_capEigenvalue_eq hd hb).deriv]
    have hK : 0 ≤ ((d - 2 : ℕ) : ℝ) * (((d - 2 : ℕ) : ℝ) - 2) / 2 := by
      have : (3 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ d - 2)
      have h2 : (0 : ℝ) ≤ ((d - 2 : ℕ) : ℝ) - 2 := by linarith
      positivity
    rcases hab.lt_or_eq with h | h
    · have := capKochRatio_le hd ha.1 h hb.2
      nlinarith
    · rw [h]

/-- **The Koch bound** (a consequence of Koch convexity). For `d ≥ 5` and `θ ∈ (0, π)`,
`Λ_d(θ) + Λ_d(π - θ) ≥ 2 Λ_d(π/2) = 2 (d - 1)`. -/
theorem two_mul_sub_one_le_capEigenvalue_add (hd : 5 ≤ d) {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    2 * ((d : ℝ) - 1) ≤ capEigenvalue d θ + capEigenvalue d (π - θ) := by
  have h := (convexOn_capEigenvalue hd).2 hθ ⟨sub_pos.2 hθ.2, sub_lt_self π hθ.1⟩
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • θ + (1 / 2 : ℝ) • (π - θ) = π / 2 := by
    simp only [smul_eq_mul]; ring
  rw [e, capEigenvalue_pi_div_two (by omega)] at h
  simp only [smul_eq_mul] at h
  linarith

end EllipticBernoulli

end
