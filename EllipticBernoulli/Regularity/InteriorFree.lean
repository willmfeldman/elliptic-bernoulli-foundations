/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.InteriorCaccioppoli
public import EllipticBernoulli.Regularity.InteriorOscillation
import EllipticBernoulli.Regularity.InteriorObstacle

/-!
# Interior oscillation decay for unconstrained energy minimizers

Let `u ∈ H¹_loc(U)` (weak gradient `Gu`) with `u ≥ 0` on `U` minimize `J_Q(·; B)` among all
competitors agreeing with `u` a.e. off `B`, for every ball `B` with `B̄ ⊆ U`, and let `Q² ≤ Cq`
on `U`. Then the essential oscillation of `u` on small balls centred at any `y ∈ U` tends to zero
(`essOscVanishes_of_free`).

Since there is no obstacle, every truncation level is admissible, and the two Caccioppoli
inequalities are special cases of the obstacle ones, with the obstacle ball `B = B_{R₀}(z)` and
the obstacle function `u` itself:

* `isDeGiorgiAt_above_of_free`: `u ∈ DG⁺` at every level `k ≥ 0`, with no error term
  (`isDeGiorgiAt_above_of_twoSided` with the constraint `0 ≤ v ≤ u`: the competitor
  `u - η (u - k)₊` satisfies it, and an unconstrained minimizer minimizes among constrained
  competitors);
* `isDeGiorgiAt_below_of_free`: `-u ∈ DG⁺` at every level, with error constant `128 Cq`
  (`isDeGiorgiAt_below_of_lower` with the constraint `u ≤ v`).

The iteration is that of `essOscVanishes_twoSided` without the obstacle alternative: the lower
bound `0` is preserved, and the initial upper bound comes from De Giorgi's `L^∞` lemma
(`exists_ae_le_of_isDeGiorgiAt`).

The route is De Giorgi's (Giusti, Ch. 7), as for the obstacle minimizers in this library; Alt and
Caffarelli (1981, §2) prove continuity by harmonic replacement instead.

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
* E. Giusti, *Direct Methods in the Calculus of Variations*, World Scientific, 2003, Ch. 7.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

public section

namespace EllipticBernoulli

variable {d : ℕ}

section Free

variable {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d}

/-- **`u ∈ DG⁺`** for an unconstrained minimizer `u ≥ 0`, at every level `k ≥ K ≥ 0`, with no
error term. -/
theorem isDeGiorgiAt_above_of_free (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hGu : MemH1Loc U u Gu) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    {z : E d} {R₀ K : ℝ} (hzR : closedBall z R₀ ⊆ U)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball z R₀)), v y = u y) →
      energyJ (ball z R₀) Q u Gu ≤ energyJ (ball z R₀) Q v Gv)
    (hK0 : 0 ≤ K) :
    IsDeGiorgiAt u Gu z R₀ K caccConst 0 :=
  isDeGiorgiAt_above_of_twoSided hU hCq hQ hzR hGu (fun _ _ ↦ rfl)
    (fun y hy ↦ ⟨hu0 y hy, le_rfl⟩) (fun v Gv hv hout _ ↦ hmin v Gv hv hout) hzR hK0
    fun _ hy hyB ↦ absurd hy hyB

/-- **`-u ∈ DG⁺`** (i.e. `u ∈ DG⁻`) for an unconstrained minimizer, at every level, with error
constant `128 Cq`. -/
theorem isDeGiorgiAt_below_of_free (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hGu : MemH1Loc U u Gu)
    {z : E d} {R₀ : ℝ} (hzR : closedBall z R₀ ⊆ U)
    (hmin : ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball z R₀)), v y = u y) →
      energyJ (ball z R₀) Q u Gu ≤ energyJ (ball z R₀) Q v Gv)
    (K : ℝ) :
    IsDeGiorgiAt (fun x ↦ -u x) (fun x ↦ -Gu x) z R₀ K caccConst (128 * Cq) :=
  isDeGiorgiAt_below_of_lower hU hCq hQ hzR hGu (fun _ _ ↦ rfl) (fun _ _ ↦ le_rfl)
    (fun v Gv hv hout _ ↦ hmin v Gv hv hout) hzR fun _ hy hyB ↦ absurd hy hyB

/-- **Interior oscillation decay for unconstrained minimizers.** If `u ≥ 0` on `U` minimizes
`J_Q(·; B)` among competitors agreeing with `u` a.e. off `B`, for every ball `B` with `B̄ ⊆ U`,
then the essential oscillation of `u` vanishes at every point of `U`. -/
theorem essOscVanishes_of_free (hd : 1 ≤ d) (hU : IsOpen U) {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hQ : ∀ x ∈ U, Q x ^ 2 ≤ Cq) (hGu : MemH1Loc U u Gu) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    (hmin : ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
      ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) →
      energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv)
    {y : E d} (hy : y ∈ U) : EssOscVanishes u y := by
  obtain ⟨CS, hS⟩ := exists_sobolevSupport hd
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU y hy
  set R₁ := ε / 2 with hR₁def
  have hR₁ : 0 < R₁ := by positivity
  have hyU : closedBall y R₁ ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  -- the initial upper bound, on `B_{R₁/2}(y)`
  obtain ⟨M₀, hM₀⟩ := exists_ae_le_of_isDeGiorgiAt hd hS hU hGu hR₁ hyU
    (isDeGiorgiAt_above_of_free hU hCq hQ hGu hu0 hyU (hmin y R₁ hR₁ hyU) le_rfl)
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
  set C : ℝ := 2 ^ n * √(128 * Cq) with hC
  have hC0 : 0 ≤ C := by positivity
  have huU : ∀ x ∈ ball y R₁, x ∈ U := fun x hx ↦ hyU (ball_subset_closedBall hx)
  refine essOscVanishes_of_step hR₀ hθ0 hθ2 hC0 (fun m ↦ 0 ≤ m) (m₀ := 0) (M₀ := M₀)
    le_rfl ?_ ?_
  · filter_upwards [hM₀, (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall
      fun x (hx : x ∈ ball y R₀) ↦ hx)] with x hx1 hx2
    exact ⟨hu0 x (huU x (ball_subset_ball hR₀R₁ hx2)), hx1⟩
  intro R hR hRR₀ m M hm hb
  have hRR₁ : R ≤ R₁ := hRR₀.trans hR₀R₁
  have hmM : m ≤ M := le_of_ae_bounds hR hb
  set k₀ := (m + M) / 2 with hk₀
  have hk₀0 : 0 ≤ k₀ := by rw [hk₀]; linarith
  have hyR : closedBall y R ⊆ U := (closedBall_subset_closedBall hRR₁).trans hyU
  have hup : IsDeGiorgiAt u Gu y R k₀ caccConst (128 * Cq) ∨
      ∀ᵐ x ∂(volume.restrict (ball y R)), k₀ - 0 ≤ u x :=
    Or.inl (IsDeGiorgiAt.mono_const
      (isDeGiorgiAt_above_of_free hU hCq hQ hGu hu0 hyR (hmin y R hR hyR) hk₀0) hC₁)
  have hdn : IsDeGiorgiAt (fun x ↦ -u x) (fun x ↦ -Gu x) y R (-k₀) caccConst (128 * Cq) ∨
      ∀ᵐ x ∂(volume.restrict (ball y R)), u x ≤ k₀ + 0 :=
    Or.inl (isDeGiorgiAt_below_of_free hU hCq hQ hGu hyR (hmin y R hR hyR) _)
  obtain ⟨m', M', hmm', -, hb', hM'⟩ := osc_step_interior hd hS hU hGu hR hyR caccConst_pos.le
    hC₁ le_rfl hmM hb hup hdn
  refine ⟨m', M', hm.trans hmm', hb', ?_⟩
  rw [hθ]
  have : 2 ^ n * √(128 * Cq) * R = C * R := by rw [hC]
  linarith

end Free

end EllipticBernoulli
