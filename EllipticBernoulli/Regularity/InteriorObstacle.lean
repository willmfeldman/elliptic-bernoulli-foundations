/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.InteriorOscillation
public import EllipticBernoulli.Regularity.InteriorCaccioppoli

/-!
# Interior oscillation decay for the two obstacle minimizers

Let `B = B_r(x₀)`, `B̄ ⊆ U`, `u` locally Lipschitz, `Q² ≤ Cq`, and let `w` minimize `J_Q(·; B)`
under the two-sided obstacle `0 ≤ w ≤ u` (`essOscVanishes_twoSided`) or the lower obstacle `u ≤ w`
(`essOscVanishes_lower`). Then at every `y ∈ B` the essential oscillation of `w` on small balls
centred at `y` tends to zero (`EssOscVanishes w y`).

Proof: at `y ∈ B` fix `R₀` with `B̄_{R₀}(y) ⊆ B` and a Lipschitz
constant `L` of `u` near `y`. On `B_R(y)`, `R ≤ R₀`, with bounds `m ≤ w ≤ M` and `k₀ = (m + M)/2`:
* problem (A), `m ≥ 0`: `w ∈ DG⁺` at level `k₀ ≥ 0` (`isDeGiorgiAt_above_of_twoSided`); `-w ∈ DG⁺`
  at level `-k₀` if `k₀ ≤ u(y) - LR ≤ inf_{B_R(y)} u` (`isDeGiorgiAt_below`), and otherwise
  `w ≤ u ≤ u(y) + LR < k₀ + 2LR` (the obstacle alternative);
* problem (B): `-w ∈ DG⁺` at every level (`isDeGiorgiAt_below_of_lower`); `w ∈ DG⁺` at level `k₀`
  if `k₀ ≥ u(y) + LR` (`isDeGiorgiAt_above`), and otherwise `w ≥ u ≥ u(y) - LR > k₀ - 2LR`.
`osc_step_interior` (with `β = 2LR`) and `essOscVanishes_of_step` conclude.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- `IsDeGiorgiAt` is monotone in the error constant. -/
theorem IsDeGiorgiAt.mono_const {f : E d → ℝ} {G : E d → E d} {z : E d} {R₀ K C₀ C₁ C₁' : ℝ}
    (h : IsDeGiorgiAt f G z R₀ K C₀ C₁) (hC : C₁ ≤ C₁') : IsDeGiorgiAt f G z R₀ K C₀ C₁' :=
  fun k hk ρ R h1 h2 h3 ↦ (h k hk ρ R h1 h2 h3).trans (by gcongr)

/-- A small closed ball around a point of an open ball, on which `u` has a Lipschitz bound
centred at `y`. -/
theorem exists_radius_interior {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hu : LocallyLipschitzOn U u) {x₀ : E d} {r : ℝ} (hB : closedBall x₀ r ⊆ U) {y : E d}
    (hy : y ∈ ball x₀ r) :
    ∃ R₀ > 0, ∃ L : ℝ, 0 ≤ L ∧ closedBall y R₀ ⊆ ball x₀ r ∧ closedBall y R₀ ⊆ U ∧
      ∀ ρ, ρ ≤ R₀ → ∀ x ∈ ball y ρ, |u x - u y| ≤ L * ρ := by
  obtain ⟨R₁, hR₁, L, hL, hyU, hLip⟩ := exists_lipschitz_ball hU hu (hB (ball_subset_closedBall hy))
  have hy' : 0 < r - dist y x₀ := sub_pos.2 (mem_ball.1 hy)
  refine ⟨min R₁ ((r - dist y x₀) / 2), lt_min hR₁ (by positivity), L, hL, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    have := dist_triangle x y x₀
    have := min_le_right R₁ ((r - dist y x₀) / 2)
    linarith
  · exact (closedBall_subset_closedBall (min_le_left _ _)).trans hyU
  · intro ρ hρ x hx
    exact hLip ρ x hx (ball_subset_ball (hρ.trans (min_le_left _ _)) hx)

/-- **Interior oscillation decay for the two-sided obstacle** `0 ≤ w ≤ u`. -/
theorem essOscVanishes_twoSided (hd : 1 ≤ d) {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hu : LocallyLipschitzOn U u)
    (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, 0 ≤ w y ∧ w y ≤ u y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y ∧ v y ≤ u y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {y : E d} (hy : y ∈ ball x₀ r) : EssOscVanishes w y := by
  obtain ⟨CS, hS⟩ := exists_sobolevSupport hd
  obtain ⟨R₀, hR₀, L, hL, hyB, hyU, hLip⟩ := exists_radius_interior hU hu hB hy
  set n := oscNI d CS caccConst with hn
  set θ : ℝ := 1 / 2 ^ (n + 2) with hθ
  have hp : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  have hθ0 : 0 < θ := by positivity
  have hθ2 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_div_iff₀ hp (by norm_num)]
    simp only [one_mul]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hC₁ : (0 : ℝ) ≤ 128 * Cq := by positivity
  set C : ℝ := 2 ^ n * √(128 * Cq) + 2 * L with hC
  have hC0 : 0 ≤ C := by positivity
  have hwU : ∀ x ∈ ball y R₀, x ∈ U := fun x hx ↦ hyU (ball_subset_closedBall hx)
  refine essOscVanishes_of_step hR₀ hθ0 hθ2 hC0 (fun m ↦ 0 ≤ m) (m₀ := 0) (M₀ := u y + L * R₀)
    le_rfl ?_ ?_
  · refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx ↦ ?_)
    have h1 := hwu x (hwU x hx)
    have h2 := hLip R₀ le_rfl x hx
    rw [abs_le] at h2
    exact ⟨h1.1, by linarith [h1.2, h2.2]⟩
  intro R hR hRR₀ m M hm hb
  have hmM : m ≤ M := le_of_ae_bounds hR hb
  set k₀ := (m + M) / 2 with hk₀
  have hk₀0 : 0 ≤ k₀ := by rw [hk₀]; linarith
  have hyR : closedBall y R ⊆ U := (closedBall_subset_closedBall hRR₀).trans hyU
  have hyRB : ∀ x ∈ ball y R, x ∈ ball x₀ r := fun x hx ↦
    hyB (ball_subset_closedBall (ball_subset_ball hRR₀ hx))
  have hup : IsDeGiorgiAt w Gw y R k₀ caccConst (128 * Cq) ∨
      ∀ᵐ x ∂(volume.restrict (ball y R)), k₀ - 2 * L * R ≤ w x :=
    Or.inl ((isDeGiorgiAt_above_of_twoSided hU hCq hQ hB hGw hwout hwu hmin hyR hk₀0
      fun x hx hxB ↦ absurd (hyRB x hx) hxB).mono_const hC₁)
  have hdn : IsDeGiorgiAt (fun x ↦ -w x) (fun x ↦ -Gw x) y R (-k₀) caccConst (128 * Cq) ∨
      ∀ᵐ x ∂(volume.restrict (ball y R)), w x ≤ k₀ + 2 * L * R := by
    by_cases hk : k₀ ≤ u y - L * R
    · refine Or.inl (isDeGiorgiAt_below hU hCq hQ hB hGw hwout hwu hmin hyR fun x hx ↦ ?_)
      have h2 := hLip R hRR₀ x hx
      rw [abs_le] at h2
      rw [neg_neg]; linarith [h2.1]
    · refine Or.inr ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx ↦ ?_))
      have h1 := hwu x (hwU x (ball_subset_ball hRR₀ hx))
      have h2 := hLip R hRR₀ x hx
      rw [abs_le] at h2
      linarith [h1.2, h2.2]
  obtain ⟨m', M', hmm', -, hb', hM'⟩ := osc_step_interior hd hS hU hGw hR hyR caccConst_pos.le
    hC₁ (by positivity : 0 ≤ 2 * L * R) hmM hb hup hdn
  refine ⟨m', M', hm.trans hmm', hb', ?_⟩
  rw [hθ]
  have : 2 ^ n * √(128 * Cq) * R + 2 * L * R = C * R := by rw [hC]; ring
  linarith

/-- **Interior oscillation decay for the lower obstacle** `u ≤ w`. -/
theorem essOscVanishes_lower (hd : 1 ≤ d) {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hu : LocallyLipschitzOn U u)
    (hB : closedBall x₀ r ⊆ U) (hGw : MemH1Loc U w Gw)
    (hwout : ∀ y ∈ U \ ball x₀ r, w y = u y) (hwu : ∀ y ∈ U, u y ≤ w y)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
      energyJ (ball x₀ r) Q w Gw ≤ energyJ (ball x₀ r) Q v Gv)
    {y : E d} (hy : y ∈ ball x₀ r) : EssOscVanishes w y := by
  obtain ⟨CS, hS⟩ := exists_sobolevSupport hd
  obtain ⟨R₁, hR₁, L, hL, hyB, hyU, hLip⟩ := exists_radius_interior hU hu hB hy
  -- the initial upper bound, on `B_{R₁/2}(y)`
  have hDG₁ : IsDeGiorgiAt w Gw y R₁ (u y + L * R₁) caccConst 0 :=
    isDeGiorgiAt_above hU hCq hQ hB hGw hwout hwu hmin hyU fun x hx ↦ by
      have h2 := hLip R₁ le_rfl x hx
      rw [abs_le] at h2
      linarith [h2.2]
  obtain ⟨M₀, hM₀⟩ := exists_ae_le_of_isDeGiorgiAt hd hS hU hGw hR₁ hyU hDG₁
    caccConst_pos.le le_rfl
  set R₀ := R₁ / 2 with hR₀def
  have hR₀ : 0 < R₀ := by positivity
  have hR₀R₁ : R₀ ≤ R₁ := by linarith
  set n := oscNI d CS caccConst with hn
  set θ : ℝ := 1 / 2 ^ (n + 2) with hθ
  have hp : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  have hθ0 : 0 < θ := by positivity
  have hθ2 : θ ≤ 1 / 2 := by
    rw [hθ, div_le_div_iff₀ hp (by norm_num)]
    simp only [one_mul]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hC₁ : (0 : ℝ) ≤ 128 * Cq := by positivity
  set C : ℝ := 2 ^ n * √(128 * Cq) + 2 * L with hC
  have hC0 : 0 ≤ C := by positivity
  have hwU : ∀ x ∈ ball y R₁, x ∈ U := fun x hx ↦ hyU (ball_subset_closedBall hx)
  refine essOscVanishes_of_step hR₀ hθ0 hθ2 hC0 (fun _ ↦ True) (m₀ := u y - L * R₁) (M₀ := M₀)
    trivial ?_ ?_
  · filter_upwards [hM₀, (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall
      fun x (hx : x ∈ ball y R₀) ↦ hx)] with x hx1 hx2
    have h1 := hwu x (hwU x (ball_subset_ball hR₀R₁ hx2))
    have h2 := hLip R₁ le_rfl x (ball_subset_ball hR₀R₁ hx2)
    rw [abs_le] at h2
    exact ⟨by linarith [h2.1], hx1⟩
  intro R hR hRR₀ m M _ hb
  have hRR₁ : R ≤ R₁ := hRR₀.trans hR₀R₁
  have hmM : m ≤ M := le_of_ae_bounds hR hb
  set k₀ := (m + M) / 2 with hk₀
  have hyR : closedBall y R ⊆ U := (closedBall_subset_closedBall hRR₁).trans hyU
  have hyRB : ∀ x ∈ ball y R, x ∈ ball x₀ r := fun x hx ↦
    hyB (ball_subset_closedBall (ball_subset_ball hRR₁ hx))
  have hup : IsDeGiorgiAt w Gw y R k₀ caccConst (128 * Cq) ∨
      ∀ᵐ x ∂(volume.restrict (ball y R)), k₀ - 2 * L * R ≤ w x := by
    by_cases hk : u y + L * R ≤ k₀
    · refine Or.inl ((isDeGiorgiAt_above hU hCq hQ hB hGw hwout hwu hmin hyR
        fun x hx ↦ ?_).mono_const hC₁)
      have h2 := hLip R hRR₁ x hx
      rw [abs_le] at h2
      linarith [h2.2]
    · refine Or.inr ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun x hx ↦ ?_))
      have h1 := hwu x (hwU x (ball_subset_ball hRR₁ hx))
      have h2 := hLip R hRR₁ x hx
      rw [abs_le] at h2
      linarith [h2.1]
  have hdn : IsDeGiorgiAt (fun x ↦ -w x) (fun x ↦ -Gw x) y R (-k₀) caccConst (128 * Cq) ∨
      ∀ᵐ x ∂(volume.restrict (ball y R)), w x ≤ k₀ + 2 * L * R :=
    Or.inl (isDeGiorgiAt_below_of_lower hU hCq hQ hB hGw hwout hwu hmin hyR
      fun x hx hxB ↦ absurd (hyRB x hx) hxB)
  obtain ⟨m', M', -, -, hb', hM'⟩ := osc_step_interior hd hS hU hGw hR hyR caccConst_pos.le
    hC₁ (by positivity : 0 ≤ 2 * L * R) hmM hb hup hdn
  refine ⟨m', M', trivial, hb', ?_⟩
  rw [hθ]
  have : 2 ^ n * √(128 * Cq) * R + 2 * L * R = C * R := by rw [hC]; ring
  linarith

end EllipticBernoulli
