/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.CapPicone
import EllipticBernoulli.Sphere.CapODE

/-!
# The first eigenfunction of the cap, and continuity of `Λ_d`

For `θ ∈ (0, π)` the shooting solution at `λ = Λ_d(θ)` is
positive on `[0, θ)` and vanishes at `θ`. The proof takes `λ* = sup {λ ≥ 0 : y(·, λ) > 0 on
[0, θ]}`: by joint continuity `y(·, λ*) ≥ 0` on `[0, θ]` with a zero, an interior zero would be a
local minimum with `y' < 0`, so the zero is at `θ`, and the characterization of `Λ_d(θ)`
(`capEigenvalue_eq_of_isCapSolution`) identifies `λ* = Λ_d(θ)`.

## Main results

* `capShootFlux_neg`: `sin^m y' < 0` at `x` if `λ > 0` and `y ≥ 0` on `[0, x]`.
* `capShoot_capEigenvalue`: `Λ_d(θ) > 0`, `y(·, Λ_d(θ)) > 0` on `[0, θ)` and `y(θ, Λ_d(θ)) = 0`.
* `capShoot_pos_of_le`: `y(·, λ) > 0` on `[0, θ)` for every `λ ≤ Λ_d(θ)`.
* `le_capEigenvalue_of_capShoot_pos`: conversely, `y(·, λ) > 0` on `[0, θ)` gives `λ ≤ Λ_d(θ)`.
* `continuousOn_capEigenvalue`: `Λ_d` is continuous on `(0, π)`.
-/

open Set Filter Topology MeasureTheory Real

public section

namespace EllipticBernoulli

variable {m d : ℕ} {lam θ : ℝ}

/-- For every `x > 0` there is `c ∈ (0, x)` with `y(c, λ) > 0`. -/
theorem exists_capShoot_pos (m : ℕ) (lam : ℝ) {x : ℝ} (hx : 0 < x) :
    ∃ c ∈ Ioo 0 x, 0 < capShoot m lam c := by
  have hc : ContinuousWithinAt (capShoot m lam) (Ioi 0) 0 :=
    ((continuousOn_capShoot_left m lam) 0 ⟨le_rfl, pi_pos⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT pi_pos) fun t ht ↦ ⟨ht.1.le, ht.2⟩)
  have h := hc.tendsto.eventually_const_lt (show (0 : ℝ) < capShoot m lam 0 by simp)
  obtain ⟨c, hc1, hc2⟩ := (h.and (Ioo_mem_nhdsGT hx)).exists
  exact ⟨c, hc2, hc1⟩

/-- **Sign of the flux.** If `λ > 0`, `x ∈ (0, π)` and `y(·, λ) ≥ 0` on `[0, x]`, then
`sin^m y'(x) = -λ ∫_0^x sin^m y < 0`. -/
theorem capShootFlux_neg (hlam : 0 < lam) {x : ℝ} (hx : x ∈ Ioo 0 π)
    (hy : ∀ t ∈ Icc 0 x, 0 ≤ capShoot m lam t) : capShootFlux m lam x < 0 := by
  obtain ⟨c, hc, hyc⟩ := exists_capShoot_pos m lam hx.1
  have hcont : ContinuousOn (fun t ↦ sin t ^ m * capShoot m lam t) (Icc 0 x) :=
    (continuous_sin.pow m).continuousOn.mul
      ((continuousOn_capShoot_left m lam).mono fun t ht ↦ ⟨ht.1, ht.2.trans_lt hx.2⟩)
  have hint : (∫ t in 0..x, (0 : ℝ)) < ∫ t in 0..x, sin t ^ m * capShoot m lam t := by
    refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hx.1
      continuousOn_const hcont (fun t ht ↦ ?_) ⟨c, Ioo_subset_Icc_self hc, ?_⟩
    · exact mul_nonneg (pow_nonneg (sin_nonneg_of_nonneg_of_le_pi ht.1.le
        (ht.2.trans hx.2.le)) m) (hy t ⟨ht.1.le, ht.2⟩)
    · exact mul_pos (pow_pos (sin_pos_of_pos_of_lt_pi hc.1 (hc.2.trans hx.2)) m) hyc
  rw [intervalIntegral.integral_zero] at hint
  rw [capShootFlux]
  nlinarith

/-- `λ ↦ y(x, λ)` is continuous for `x ∈ [0, π)`. -/
theorem continuous_capShoot_right (m : ℕ) {x : ℝ} (hx : x ∈ Ico 0 π) :
    Continuous fun lam ↦ capShoot m lam x :=
  continuousOn_univ.1 <| (continuousOn_capShoot m).comp
    (continuous_const.prodMk continuous_id).continuousOn fun _ _ ↦ ⟨hx, mem_univ _⟩

theorem continuousAt_capShoot_left (m : ℕ) (lam : ℝ) {x : ℝ} (hx : x ∈ Ioo 0 π) :
    ContinuousAt (capShoot m lam) x :=
  (hasDerivAt_capShoot m lam hx).continuousAt

/-- **Existence of the first eigenfunction.** For `θ ∈ (0, π)`,
`Λ_d(θ) > 0`, `y(·, Λ_d(θ)) > 0` on `[0, θ)` and `y(θ, Λ_d(θ)) = 0`. -/
theorem capShoot_capEigenvalue (hθ : 0 < θ) (hθπ : θ < π) :
    0 < capEigenvalue d θ ∧ (∀ x ∈ Ico 0 θ, 0 < capShoot (d - 2) (capEigenvalue d θ) x) ∧
      capShoot (d - 2) (capEigenvalue d θ) θ = 0 := by
  set m := d - 2
  set S := {lam : ℝ | 0 ≤ lam ∧ ∀ x ∈ Icc 0 θ, 0 < capShoot m lam x}
  have h0S : (0 : ℝ) ∈ S := ⟨le_rfl, fun x _ ↦ by simp⟩
  have hbdd : ∀ lam ∈ S, lam ≤ capEigenvalue d θ := fun lam h ↦
    le_capEigenvalue_of_pos hθ hθπ.le (isCapSolution_capShoot m lam hθπ) h.2
  have hSbdd : BddAbove S := ⟨_, hbdd⟩
  set L := sSup S
  have hL0 : 0 ≤ L := le_csSup hSbdd h0S
  have hIco : ∀ x ∈ Icc 0 θ, x ∈ Ico 0 π := fun x hx ↦ ⟨hx.1, hx.2.trans_lt hθπ⟩
  -- (1) `y(·, L) ≥ 0` on `[0, θ]`
  have hnonneg : ∀ x ∈ Icc 0 θ, 0 ≤ capShoot m L x := by
    intro x hx
    by_contra hneg
    push Not at hneg
    have hev := ((continuous_capShoot_right m (hIco x hx)).tendsto L).eventually_lt_const hneg
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    obtain ⟨lam, hlamS, hlam⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ (show L - ε < L by linarith)
    have hle : lam ≤ L := le_csSup hSbdd hlamS
    have := hball (show dist lam L < ε by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    linarith [hlamS.2 x hx]
  -- (2) `y(·, L)` vanishes somewhere on `[0, θ]`
  have hzero : ∃ x₀ ∈ Icc 0 θ, capShoot m L x₀ = 0 := by
    by_contra hno
    push Not at hno
    have hpos : ∀ x ∈ Icc 0 θ, 0 < capShoot m L x := fun x hx ↦
      lt_of_le_of_ne (hnonneg x hx) (hno x hx).symm
    set b := (θ + π) / 2
    have hθb : θ < b := by simp only [b]; linarith
    have hb : b < π := by simp only [b]; linarith
    have hev : ∀ᶠ lam in 𝓝 L, ∀ x ∈ Icc 0 θ, x ∈ Icc 0 b → 0 < capShoot m lam x := by
      refine isCompact_Icc.eventually_forall_of_forall_eventually fun x hx ↦ ?_
      have hc := ((continuous_capShoot_clamp m hb).comp continuous_swap).continuousAt
        (x := (L, x))
      have hval : 0 < capShoot m L (max 0 (min x b)) := by
        rw [max_zero_min_eq ⟨hx.1, hx.2.trans hθb.le⟩]; exact hpos x hx
      filter_upwards [hc.eventually (eventually_gt_nhds hval)] with z hz hzb
      simpa [Function.comp_apply, max_zero_min_eq hzb] using hz
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hmem : L + ε / 2 ∈ S := ⟨by linarith, fun x hx ↦ hball
      (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith) x hx ⟨hx.1, hx.2.trans hθb.le⟩⟩
    linarith [le_csSup hSbdd hmem]
  obtain ⟨x₀, hx₀, hyx₀⟩ := hzero
  -- (3) `L > 0`
  have hLpos : 0 < L := by
    rcases hL0.eq_or_lt with h | h
    · rw [← h] at hyx₀; simp at hyx₀
    · exact h
  -- (4) no zero on `[0, θ)`
  have hnozero : ∀ x ∈ Ico 0 θ, 0 < capShoot m L x := by
    intro x hx
    refine lt_of_le_of_ne (hnonneg x ⟨hx.1, hx.2.le⟩) fun hz ↦ ?_
    rcases hx.1.eq_or_lt with h0 | hpos
    · rw [← h0] at hz; simp at hz
    · have hxπ : x ∈ Ioo 0 π := ⟨hpos, hx.2.trans hθπ⟩
      have hmin : IsLocalMin (capShoot m L) x := by
        filter_upwards [Ioo_mem_nhds hpos hx.2] with t ht
        rw [← hz]; exact hnonneg t ⟨ht.1.le, ht.2.le⟩
      have hd := hmin.hasDerivAt_eq_zero (hasDerivAt_capShoot m L hxπ)
      have hflux := capShootFlux_neg (m := m) hLpos hxπ fun t ht ↦
        hnonneg t ⟨ht.1, ht.2.trans hx.2.le⟩
      rw [capShootDeriv, div_eq_zero_iff] at hd
      rcases hd with hd | hd
      · linarith
      · exact (pow_pos (sin_pos_of_pos_of_lt_pi hxπ.1 hxπ.2) m).ne' hd
  have hx₀θ : x₀ = θ := by
    by_contra hne
    have := hnozero x₀ ⟨hx₀.1, lt_of_le_of_ne hx₀.2 hne⟩
    linarith
  have hyθ : capShoot m L θ = 0 := hx₀θ ▸ hyx₀
  have hΛ : capEigenvalue d θ = L :=
    capEigenvalue_eq_of_isCapSolution hθ hθπ (isCapSolution_capShoot m L hθπ) hnozero hyθ
      (hasDerivAt_capShoot m L ⟨hθ, hθπ⟩)
      (capShootFlux_neg hLpos ⟨hθ, hθπ⟩ hnonneg)
  rw [hΛ]
  exact ⟨hLpos, hnozero, hyθ⟩

theorem capEigenvalue_pos (hθ : 0 < θ) (hθπ : θ < π) : 0 < capEigenvalue d θ :=
  (capShoot_capEigenvalue hθ hθπ).1

/-- **Positivity below the eigenvalue.** If `λ ≤ Λ_d(θ)`, then `y(·, λ) > 0` on `[0, θ)`. -/
theorem capShoot_pos_of_le (hθ : 0 < θ) (hθπ : θ < π) (hlam : lam ≤ capEigenvalue d θ) :
    ∀ x ∈ Ico 0 θ, 0 < capShoot (d - 2) lam x := by
  intro x hx
  by_contra hneg
  push Not at hneg
  rcases hx.1.eq_or_lt with h0 | hxpos
  · rw [← h0] at hneg; simp at hneg; linarith
  obtain ⟨z, hz, hyz⟩ := intermediate_value_Icc' hx.1
    ((continuousOn_capShoot_left (d - 2) lam).mono fun t ht ↦ ⟨ht.1, ht.2.trans_lt
      (hx.2.trans hθπ)⟩) ⟨hneg, by simp⟩
  have hz0 : 0 < z := by
    rcases hz.1.eq_or_lt with h | h
    · rw [← h] at hyz; simp at hyz
    · exact h
  have hzθ : z < θ := hz.2.trans_lt hx.2
  have h1 : capEigenvalue d z ≤ lam :=
    capEigenvalue_le_of_eq_zero hz0 (hzθ.trans hθπ).le
      (isCapSolution_capShoot (d - 2) lam (hzθ.trans hθπ)) hyz (by simp)
  have h2 : capEigenvalue d θ ≤ capEigenvalue d z := capEigenvalue_le_of_le hz0 hzθ.le hθπ.le
  have heq : lam = capEigenvalue d θ := le_antisymm hlam (h2.trans h1)
  have := (capShoot_capEigenvalue (d := d) hθ hθπ).2.1 z ⟨hz0.le, hzθ⟩
  rw [← heq, hyz] at this
  exact lt_irrefl 0 this

/-- A function positive on `[0, θ)` and continuous at `θ` is nonnegative at `θ`. -/
private theorem capShoot_nonneg_of_pos_Ico (hθ : 0 < θ) (hθπ : θ < π)
    (hpos : ∀ x ∈ Ico 0 θ, 0 < capShoot m lam x) : 0 ≤ capShoot m lam θ := by
  refine ge_of_tendsto ((continuousAt_capShoot_left m lam ⟨hθ, hθπ⟩).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Iio θ))) ?_
  filter_upwards [Ioo_mem_nhdsLT hθ] with x hx
  exact (hpos x ⟨hx.1.le, hx.2⟩).le

/-- **Positivity bounds the eigenvalue.** If `y(·, λ) > 0` on `[0, θ)`, then `λ ≤ Λ_d(θ)`. -/
theorem le_capEigenvalue_of_capShoot_pos (hθ : 0 < θ) (hθπ : θ < π)
    (hpos : ∀ x ∈ Ico 0 θ, 0 < capShoot (d - 2) lam x) : lam ≤ capEigenvalue d θ := by
  rcases le_or_gt lam 0 with hlam | hlam
  · exact hlam.trans (capEigenvalue_nonneg hθ.le hθπ.le)
  have hnn := capShoot_nonneg_of_pos_Ico hθ hθπ hpos
  rcases hnn.lt_or_eq with h | h
  · refine le_capEigenvalue_of_pos hθ hθπ.le (isCapSolution_capShoot _ lam hθπ) fun x hx ↦ ?_
    rcases hx.2.lt_or_eq with h' | h'
    · exact hpos x ⟨hx.1, h'⟩
    · rwa [h']
  · exact (capEigenvalue_eq_of_isCapSolution hθ hθπ (isCapSolution_capShoot _ lam hθπ) hpos h.symm
      (hasDerivAt_capShoot _ lam ⟨hθ, hθπ⟩)
      (capShootFlux_neg hlam ⟨hθ, hθπ⟩ fun t ht ↦ by
        rcases ht.2.lt_or_eq with h' | h'
        · exact (hpos t ⟨ht.1, h'⟩).le
        · rw [h']; exact hnn)).ge

/-- Strictly below the eigenvalue, `y(·, λ) > 0` on the closed interval `[0, θ]`. -/
theorem capShoot_pos_of_lt (hθ : 0 < θ) (hθπ : θ < π) (hlam : lam < capEigenvalue d θ) :
    ∀ x ∈ Icc 0 θ, 0 < capShoot (d - 2) lam x := by
  have hpos := capShoot_pos_of_le hθ hθπ hlam.le
  intro x hx
  rcases hx.2.lt_or_eq with h | h
  · exact hpos x ⟨hx.1, h⟩
  rw [h]
  refine lt_of_le_of_ne (capShoot_nonneg_of_pos_Ico hθ hθπ hpos) fun h0 ↦ ?_
  have := capEigenvalue_le_of_eq_zero hθ hθπ.le (isCapSolution_capShoot (d - 2) lam hθπ)
    h0.symm (by simp)
  linarith

/-- **Continuity of `Λ_d`** on `(0, π)`. -/
theorem continuousOn_capEigenvalue (d : ℕ) : ContinuousOn (capEigenvalue d) (Ioo 0 π) := by
  intro θ hθ
  refine ContinuousAt.continuousWithinAt (tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩)
  · -- right: `y(·, λ) > 0` on `[0, θ₂]` for some `θ₂ > θ`
    set lam := (max a 0 + capEigenvalue d θ) / 2
    have hΛ := capEigenvalue_pos (d := d) hθ.1 hθ.2
    have hlam : lam < capEigenvalue d θ := by
      simp only [lam]; linarith [max_lt ha hΛ]
    have hal : a < lam := by simp only [lam]; linarith [le_max_left a 0, max_lt ha hΛ]
    have hposθ := capShoot_pos_of_lt hθ.1 hθ.2 hlam
    have hev := (continuousAt_capShoot_left (d - 2) lam hθ).eventually
      (eventually_gt_nhds (hposθ θ ⟨hθ.1.le, le_rfl⟩))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    set θ₂ := min (θ + ε / 2) ((θ + π) / 2)
    have hθθ₂ : θ < θ₂ := lt_min (by linarith) (by linarith [hθ.2])
    have hθ₂π : θ₂ < π := (min_le_right _ _).trans_lt (by linarith [hθ.2])
    have hpos₂ : ∀ x ∈ Icc 0 θ₂, 0 < capShoot (d - 2) lam x := by
      intro x hx
      rcases le_or_gt x θ with h | h
      · exact hposθ x ⟨hx.1, h⟩
      · refine hball ?_
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hx.2, min_le_left (θ + ε / 2) ((θ + π) / 2)]
    have h₂ : lam ≤ capEigenvalue d θ₂ :=
      le_capEigenvalue_of_pos (hθ.1.trans hθθ₂) hθ₂π.le
        (isCapSolution_capShoot (d - 2) lam hθ₂π) hpos₂
    filter_upwards [Ioo_mem_nhds hθ.1 hθθ₂] with θ' hθ'
    exact hal.trans_le (h₂.trans (capEigenvalue_le_of_le hθ'.1 hθ'.2.le hθ₂π.le))
  · -- left: some `θ₁ < θ` has `Λ_d(θ₁) < b`
    obtain ⟨θ₁, hθ₁, hθ₁b⟩ : ∃ θ₁ ∈ Ioo 0 θ, capEigenvalue d θ₁ < b := by
      by_contra hno
      push Not at hno
      set lam := (capEigenvalue d θ + b) / 2
      have hlam : capEigenvalue d θ < lam := by simp only [lam]; linarith
      have hpos : ∀ x ∈ Ico 0 θ, 0 < capShoot (d - 2) lam x := by
        intro x hx
        set θ₁ := (x + θ) / 2
        have hθ₁ : θ₁ ∈ Ioo 0 θ := ⟨by simp only [θ₁]; linarith [hx.1, hx.2],
          by simp only [θ₁]; linarith [hx.2]⟩
        exact capShoot_pos_of_le hθ₁.1 (hθ₁.2.trans hθ.2)
          ((show lam ≤ b by simp only [lam]; linarith).trans (hno θ₁ hθ₁))
          x ⟨hx.1, by simp only [θ₁]; linarith [hx.2]⟩
      linarith [le_capEigenvalue_of_capShoot_pos (d := d) hθ.1 hθ.2 hpos]
    filter_upwards [Ioo_mem_nhds hθ₁.2 hθ.2] with θ' hθ'
    exact (capEigenvalue_le_of_le hθ₁.1 hθ'.1.le hθ'.2.le).trans_lt hθ₁b

end EllipticBernoulli

end
