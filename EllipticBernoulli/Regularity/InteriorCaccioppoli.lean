/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.ObstacleCaccioppoli

/-!
# The two missing Caccioppoli inequalities for obstacle minimizers

Let `B = B_r(x₀)`, `B̄ ⊆ U`, and let `w ∈ H¹_loc(U)` with `w = u` on `U \ B` minimize `J_Q(·; B)`
among competitors with the same values off `B` and a pointwise constraint.
`Regularity/ObstacleCaccioppoli.lean` proves the two truncations needed at points of `∂B`: the
upper truncation for the lower obstacle `w ≥ u` (`step_above`) and the lower truncation for the
two-sided obstacle `0 ≤ w ≤ u` (`step_below`). The interior De Giorgi argument also needs the
other two:

* `step_above_twoSided` (two-sided obstacle `0 ≤ w ≤ u`): the competitor `v = w - η (w - k)₊` is
  admissible for every level `k ≥ 0` with `u ≤ k` on `B_t(z) \ B` (vacuous if `B_t(z) ⊆ B`), since
  `0 ≤ min(w, k) ≤ v ≤ w ≤ u`; and `{v > 0} ⊆ {w > 0}`, so there is no error term.
* `step_below_lower` (lower obstacle `u ≤ w`): the competitor `v = w + η (k - w)₊` is admissible for
  every level `k` with `k ≤ u` on `B_t(z) \ B`, since `v ≥ w ≥ u`; the positivity set grows, which
  gives the error term `sup Q² |{(k - w)₊ > 0} ∩ B_t|`.

With `caccioppoli_of_step` these give `isDeGiorgiAt_above_of_twoSided` (`w ∈ DG⁺`, levels `≥ 0`,
`C₁ = 0`) and `isDeGiorgiAt_below_of_lower` (`-w ∈ DG⁺`, all levels, `C₁ = 128 Cq`).

The proofs follow `step_above`/`step_below`; only the admissibility checks differ.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

section TwoSided

variable {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ}

/-- **One-step inequality, upper truncation for the two-sided obstacle** `0 ≤ w ≤ u`. Admissible
at every level `k ≥ 0` with `u ≤ k` on `B_t(z) \ B`; no error term. -/
theorem step_above_twoSided (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {z : E d} {t k : ℝ} (hzt : closedBall z t ⊆ U) (hk0 : 0 ≤ k)
    (hk : ∀ y ∈ ball z t, y ∉ ball x₀ r → u y ≤ k)
    {η : E d → ℝ} (hη : ContDiff ℝ ∞ η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hη0 : ∀ x ∉ ball z t, η x = 0 ∧ ∇ η x = 0) :
    ∫ x in ball z t, ‖{y | k < w y}.indicator Gw x‖ ^ 2 ≤
      ∫ x in ball z t, ‖(1 - η x) • {y | k < w y}.indicator Gw x -
        max (w x - k) 0 • ∇ η x‖ ^ 2 := by
  set F : E d → ℝ := fun y ↦ max (w y - k) 0 with hFdef
  set GF : E d → E d := {y | k < w y}.indicator Gw with hGFdef
  have hF : MemH1Loc U F GF := hGw.posPart_sub hU k
  have hηF := hF.mul_smooth hU hη
  have hv := hGw.sub hηF
  set v : E d → ℝ := fun x ↦ w x - η x * F x with hvdef
  set Gv : E d → E d := fun x ↦ Gw x - (η x • GF x + F x • ∇ η x) with hGvdef
  have hF0 : ∀ y, 0 ≤ F y := fun y ↦ le_max_right _ _
  have hFk : ∀ y, w y ≤ k → F y = 0 := fun y hy ↦ max_eq_right (by linarith)
  have hGFk : ∀ y, w y ≤ k → GF y = 0 := fun y hy ↦
    indicator_of_notMem (show y ∉ {y | k < w y} from not_lt.2 hy) _
  have hzU : ball z t ⊆ U := ball_subset_closedBall.trans hzt
  have hBm : MeasurableSet (ball x₀ r) := measurableSet_ball
  -- admissibility
  have hP1 : ∀ y ∈ U \ ball x₀ r, v y = u y := by
    intro y hy
    change w y - η y * F y = u y
    by_cases hyt : y ∈ ball z t
    · have : w y ≤ k := (hwout y hy).symm ▸ hk y hyt hy.2
      simp only [hFk y this, mul_zero, sub_zero]; exact hwout y hy
    · simp only [(hη0 y hyt).1, zero_mul, sub_zero]; exact hwout y hy
  have hP2 : ∀ y ∈ U, 0 ≤ v y ∧ v y ≤ u y := by
    intro y hy
    change 0 ≤ w y - η y * F y ∧ w y - η y * F y ≤ u y
    have hηF0 : 0 ≤ η y * F y := mul_nonneg (hη01 y).1 (hF0 y)
    refine ⟨?_, by linarith [(hwu y hy).2]⟩
    by_cases hwk : w y ≤ k
    · simp only [hFk y hwk, mul_zero, sub_zero]; exact (hwu y hy).1
    · have hFy : F y = w y - k := max_eq_left (by linarith)
      rw [hFy]
      have h01 := hη01 y
      nlinarith
  have hJ := hmin v Gv hv
    ((ae_restrict_iff' (hU.measurableSet.diff hBm)).2 (Eventually.of_forall hP1))
    ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall hP2))
  have hpos : posSet v (ball x₀ r) ⊆ posSet w (ball x₀ r) ∪ ∅ := by
    intro y hy
    refine Or.inl ⟨hy.1, ?_⟩
    have : 0 ≤ η y * F y := mul_nonneg (hη01 y).1 (hF0 y)
    simp only [hvdef] at *
    linarith [hy.2]
  have hcB : IsCompact (closedBall x₀ r) := isCompact_closedBall _ _
  have hGwB := (integrableOn_norm_sq_of_memH1Loc hGw hB hcB).mono_set ball_subset_closedBall
  have hGvB := (integrableOn_norm_sq_of_memH1Loc hv hB hcB).mono_set ball_subset_closedBall
  have hct : IsCompact (closedBall z t) := isCompact_closedBall _ _
  have hE := integral_norm_sq_le_of_energyJ_le hBm measure_ball_lt_top.ne
    (by simp) hCq (fun x hx ↦ hQ x (hB (ball_subset_closedBall hx))) hGwB hGvB hJ hpos
  simp only [measure_empty, ENNReal.toReal_zero, mul_zero, add_zero] at hE
  have := step_of_energy (X := 0) hBm hzU hGwB hGvB
    ((integrableOn_norm_sq_of_memH1Loc hGw hzt hct).mono_set ball_subset_closedBall)
    ((integrableOn_norm_sq_of_memH1Loc hv hzt hct).mono_set ball_subset_closedBall)
    ((integrableOn_norm_sq_of_memH1Loc hF hzt hct).mono_set ball_subset_closedBall)
    (by simpa using hE) (fun y hy ↦ ?_) (fun y hy hyB ↦ ?_) (fun y hy ↦ ?_) (η := η) (F := F)
  · simpa using this
  · simp [hGvdef, (hη0 y hy).1, (hη0 y hy).2]
  · have hwk : w y ≤ k := (hwout y ⟨hzU hy, hyB⟩).symm ▸ hk y hy hyB
    simp [hGvdef, hFk y hwk, hGFk y hwk]
  · by_cases hwk : w y ≤ k
    · simp [hGvdef, hFk y hwk, hGFk y hwk]
    · have hGF : GF y = Gw y := indicator_of_mem (show y ∈ {y | k < w y} from not_le.1 hwk) _
      simp only [hGvdef, hGF]
      congr 2
      rw [sub_smul, one_smul]
      abel_nf

/-- **`w ∈ DG⁺`** for the two-sided obstacle minimizer (`0 ≤ w ≤ u`), at levels `k ≥ K ≥ 0` with
`u ≤ K` on `B_{R₀}(z) \ B` (vacuous if `B_{R₀}(z) ⊆ B`), with no error term. -/
theorem isDeGiorgiAt_above_of_twoSided (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {z : E d} {R₀ K : ℝ} (hzR : closedBall z R₀ ⊆ U) (hK0 : 0 ≤ K)
    (hK : ∀ y ∈ ball z R₀, y ∉ ball x₀ r → u y ≤ K) :
    IsDeGiorgiAt w Gw z R₀ K caccConst 0 := by
  intro k hk ρ R hρ hρR hR
  have hc : IsCompact (closedBall z R₀) := isCompact_closedBall _ _
  have hF := hGw.posPart_sub hU k
  have h := caccioppoli_of_step (Er := 0) le_rfl
    ((integrableOn_norm_sq_of_memH1Loc hF hzR hc).mono_set ball_subset_closedBall)
    ((integrableOn_sq_of_memH1Loc hF hzR hc).mono_set ball_subset_closedBall)
    (fun t ht htR η hη hη01 hη0 ↦ by
      have := step_above_twoSided hU hCq hQ hB hGw hwout hwu hmin
        ((closedBall_subset_closedBall htR).trans hzR) (hK0.trans hk)
        (fun y hy hyB ↦ (hK y (ball_subset_ball htR hy) hyB).trans hk) hη hη01 hη0
      simpa using this) hρ hρR hR
  simpa [caccConst] using h

end TwoSided

section Lower

variable {U : Set (E d)} {Q u w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ}

/-- **One-step inequality, lower truncation for the lower obstacle** `u ≤ w`. Admissible at every
level `k` with `k ≤ u` on `B_t(z) \ B`; the error term comes from the growth of the positivity
set. -/
theorem step_below_lower (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, u y ≤ w y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {z : E d} {t k : ℝ} (hzt : closedBall z t ⊆ U)
    (hk : ∀ y ∈ ball z t, y ∉ ball x₀ r → k ≤ u y)
    {η : E d → ℝ} (hη : ContDiff ℝ ∞ η) (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hη0 : ∀ x ∉ ball z t, η x = 0 ∧ ∇ η x = 0) :
    ∫ x in ball z t, ‖{y | w y < k}.indicator (fun y ↦ -Gw y) x‖ ^ 2 ≤
      (∫ x in ball z t, ‖(1 - η x) • {y | w y < k}.indicator (fun y ↦ -Gw y) x -
        max (k - w x) 0 • ∇ η x‖ ^ 2) +
      Cq * (volume ({x | 0 < max (k - w x) 0} ∩ ball z t)).toReal := by
  set F : E d → ℝ := fun y ↦ max (k - w y) 0 with hFdef
  set GF : E d → E d := {y | w y < k}.indicator (fun y ↦ -Gw y) with hGFdef
  have hF : MemH1Loc U F GF := hGw.posPart_const_sub hU k
  have hηF := hF.mul_smooth hU hη
  have hv := hGw.add hηF
  set v : E d → ℝ := fun x ↦ w x + η x * F x with hvdef
  set Gv : E d → E d := fun x ↦ Gw x + (η x • GF x + F x • ∇ η x) with hGvdef
  have hF0 : ∀ y, 0 ≤ F y := fun y ↦ le_max_right _ _
  have hFk : ∀ y, k ≤ w y → F y = 0 := fun y hy ↦ max_eq_right (by linarith)
  have hGFk : ∀ y, k ≤ w y → GF y = 0 := fun y hy ↦
    indicator_of_notMem (show y ∉ {y | w y < k} from not_lt.2 hy) _
  have hzU : ball z t ⊆ U := ball_subset_closedBall.trans hzt
  have hBm : MeasurableSet (ball x₀ r) := measurableSet_ball
  have hP1 : ∀ y ∈ U \ ball x₀ r, v y = u y := by
    intro y hy
    change w y + η y * F y = u y
    by_cases hyt : y ∈ ball z t
    · have : k ≤ w y := (hwout y hy).symm ▸ hk y hyt hy.2
      simp only [hFk y this, mul_zero, add_zero]; exact hwout y hy
    · simp only [(hη0 y hyt).1, zero_mul, add_zero]; exact hwout y hy
  have hP2 : ∀ y ∈ U, u y ≤ v y := by
    intro y hy
    change u y ≤ w y + η y * F y
    have hηF0 : 0 ≤ η y * F y := mul_nonneg (hη01 y).1 (hF0 y)
    linarith [hwu y hy]
  have hJ := hmin v Gv hv
    ((ae_restrict_iff' (hU.measurableSet.diff hBm)).2 (Eventually.of_forall hP1))
    ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall hP2))
  have hpos : posSet v (ball x₀ r) ⊆ posSet w (ball x₀ r) ∪ ({x | 0 < F x} ∩ ball z t) := by
    intro y hy
    by_cases hwy : 0 < w y
    · exact Or.inl ⟨hy.1, hwy⟩
    · right
      have hvy : 0 < w y + η y * F y := hy.2
      have hηFy : 0 < η y * F y := by linarith
      have hFy : 0 < F y := by
        rcases (hF0 y).lt_or_eq with h | h
        · exact h
        · rw [← h, mul_zero] at hηFy; exact absurd hηFy (lt_irrefl 0)
      refine ⟨hFy, ?_⟩
      by_contra hyt
      rw [(hη0 y hyt).1, zero_mul] at hηFy
      exact lt_irrefl 0 hηFy
  have hcB : IsCompact (closedBall x₀ r) := isCompact_closedBall _ _
  have hGwB := (integrableOn_norm_sq_of_memH1Loc hGw hB hcB).mono_set ball_subset_closedBall
  have hGvB := (integrableOn_norm_sq_of_memH1Loc hv hB hcB).mono_set ball_subset_closedBall
  have hct : IsCompact (closedBall z t) := isCompact_closedBall _ _
  have hE := integral_norm_sq_le_of_energyJ_le hBm measure_ball_lt_top.ne
    (volume_inter_ball_ne_top _ z t) hCq (fun x hx ↦ hQ x (hB (ball_subset_closedBall hx)))
    hGwB hGvB hJ hpos
  refine step_of_energy hBm hzU hGwB hGvB
    ((integrableOn_norm_sq_of_memH1Loc hGw hzt hct).mono_set ball_subset_closedBall)
    ((integrableOn_norm_sq_of_memH1Loc hv hzt hct).mono_set ball_subset_closedBall)
    ((integrableOn_norm_sq_of_memH1Loc hF hzt hct).mono_set ball_subset_closedBall)
    hE (fun y hy ↦ ?_) (fun y hy hyB ↦ ?_) (fun y hy ↦ ?_)
  · simp [hGvdef, (hη0 y hy).1, (hη0 y hy).2]
  · have hwk : k ≤ w y := (hwout y ⟨hzU hy, hyB⟩).symm ▸ hk y hy hyB
    simp [hGvdef, hFk y hwk, hGFk y hwk]
  · by_cases hwk : k ≤ w y
    · have hm : max (k - w y) 0 = 0 := max_eq_right (sub_nonpos.2 hwk)
      simp [hGvdef, hFk y hwk, hGFk y hwk, hm]
    · have hGF : GF y = -Gw y :=
        indicator_of_mem (show y ∈ {y | w y < k} from not_le.1 hwk) (fun y ↦ -Gw y)
      have e : (1 - η y) • GF y - F y • ∇ η y = -(Gw y + (η y • GF y + F y • ∇ η y)) := by
        rw [hGF, sub_smul, one_smul]
        simp only [smul_neg]
        abel
      simp only [hGvdef]
      rw [e, norm_neg, hGF, norm_neg]

/-- **`-w ∈ DG⁺`** (i.e. `w ∈ DG⁻`) for the lower-obstacle minimizer (`u ≤ w`), at levels
`k ≥ K` with `-K ≤ u` on `B_{R₀}(z) \ B` (vacuous if `B_{R₀}(z) ⊆ B`), with error constant
`128 Cq`, `Q² ≤ Cq`. -/
theorem isDeGiorgiAt_below_of_lower (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, u y ≤ w y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {z : E d} {R₀ K : ℝ} (hzR : closedBall z R₀ ⊆ U)
    (hK : ∀ y ∈ ball z R₀, y ∉ ball x₀ r → -K ≤ u y) :
    IsDeGiorgiAt (fun x ↦ -w x) (fun x ↦ -Gw x) z R₀ K caccConst (128 * Cq) := by
  intro k hk ρ R hρ hρR hR
  have hc : IsCompact (closedBall z R₀) := isCompact_closedBall _ _
  have hF := hGw.neg.posPart_sub hU k
  have hset : {y | k < -w y} = {y | w y < -k} := by ext y; simp [lt_neg]
  have hmax : ∀ x, max (-k - w x) 0 = max (-w x - k) 0 := fun x ↦ by ring_nf
  have h := caccioppoli_of_step (Er := Cq) hCq
    ((integrableOn_norm_sq_of_memH1Loc hF hzR hc).mono_set ball_subset_closedBall)
    ((integrableOn_sq_of_memH1Loc hF hzR hc).mono_set ball_subset_closedBall)
    (fun t ht htR η hη hη01 hη0 ↦ by
      have := step_below_lower (k := -k) hU hCq hQ hB hGw hwout hwu hmin
        ((closedBall_subset_closedBall htR).trans hzR)
        (fun y hy hyB ↦ (neg_le_neg hk).trans (hK y (ball_subset_ball htR hy) hyB)) hη hη01 hη0
      simp only [hmax] at this
      rw [hset]
      exact this) hρ hρR hR
  rw [setOf_posPart_sub_pos] at h
  convert h using 2

end Lower

end EllipticBernoulli
