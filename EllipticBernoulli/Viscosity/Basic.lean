/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Viscosity.Jet

/-!
# Basic facts about viscosity super/subsolutions

* `contDiff_two_of_smooth`: smooth test functions are `C²`.
* Touching in open sets is touching on a full neighbourhood
  (`TouchesBelow.eventually_le_of_isOpen`, `TouchesAbove.eventually_le_of_isOpen`).
* `isOpen_posSet`: the positivity set of a function continuous on an open set is open.
* `isViscSuper_const`: nonnegative constants are viscosity supersolutions (used after
  Abedin–Feldman–Stinson, (2.4)).
* Strict sub/supersolutions (Abedin–Feldman–Stinson, Definition 2.2) with explicit constants:
  `isStrictSub_iff`, `isStrictSuper_iff`, and shifts by small constants (the remark after
  Definition 2.2).

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Touching in open sets -/

/-- A smooth (`C^∞`) test function is `C²`. -/
theorem contDiff_two_of_smooth {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : F → ℝ} (h : ContDiff ℝ ∞ φ) : ContDiff ℝ 2 φ :=
  h.of_le (by norm_cast)

/-- In an open set, touching from below is touching on a full neighbourhood. -/
theorem TouchesBelow.eventually_le_of_isOpen {U : Set (E d)} {φ u : E d → ℝ} {x : E d}
    (hU : IsOpen U) (h : TouchesBelow φ u U x) : ∀ᶠ y in 𝓝 x, φ y ≤ u y := by
  have := h.2.2
  rwa [hU.nhdsWithin_eq h.1] at this

/-- In an open set, touching from above is touching on a full neighbourhood. -/
theorem TouchesAbove.eventually_le_of_isOpen {U : Set (E d)} {φ u : E d → ℝ} {x : E d}
    (hU : IsOpen U) (h : TouchesAbove φ u U x) : ∀ᶠ y in 𝓝 x, u y ≤ φ y := by
  have := h.2.2
  rwa [hU.nhdsWithin_eq h.1] at this

/-- The positivity set of a function continuous on an open set is open. -/
theorem isOpen_posSet {U : Set (E d)} {f : E d → ℝ} (hU : IsOpen U) (hf : ContinuousOn f U) :
    IsOpen (posSet f U) :=
  hf.isOpen_inter_preimage hU isOpen_Ioi

/-! ### Constants -/

/-- A nonnegative constant is a viscosity supersolution in an open set. -/
theorem isViscSuper_const {U : Set (E d)} {Q : E d → ℝ} (hU : IsOpen U) {c : ℝ} (hc : 0 ≤ c) :
    IsViscSuper U Q (fun _ ↦ c) := by
  refine ⟨continuousOn_const, fun _ _ ↦ hc, ?_⟩
  intro φ hφ x _ h
  left
  have hmax : IsLocalMax φ x := by
    filter_upwards [h.eventually_le_of_isOpen hU] with y hy
    rw [h.2.1]; exact hy
  exact IsLocalMax.laplacian_nonpos (contDiff_two_of_smooth hφ) hmax

/-! ### Shifts of strict sub/supersolutions (the remark after Definition 2.2) -/

theorem isStrictSub_iff {U : Set (E d)} {Q g : E d → ℝ} :
    IsStrictSub U Q g ↔ ∃ a₀ δ₀, IsStrictSubWith U Q g a₀ δ₀ := by
  constructor
  · rintro ⟨hg, a₀, ha₀, δ₀, hδ₀, h1, h2⟩; exact ⟨a₀, δ₀, hg, ha₀, hδ₀, h1, h2⟩
  · rintro ⟨a₀, δ₀, hg, ha₀, hδ₀, h1, h2⟩; exact ⟨hg, a₀, ha₀, δ₀, hδ₀, h1, h2⟩

theorem isStrictSuper_iff {U : Set (E d)} {Q g : E d → ℝ} :
    IsStrictSuper U Q g ↔ ∃ a₀ δ₀, IsStrictSuperWith U Q g a₀ δ₀ := by
  constructor
  · rintro ⟨hg, a₀, ha₀, δ₀, hδ₀, h1, h2⟩; exact ⟨a₀, δ₀, hg, ha₀, hδ₀, h1, h2⟩
  · rintro ⟨a₀, δ₀, hg, ha₀, hδ₀, h1, h2⟩; exact ⟨hg, a₀, ha₀, δ₀, hδ₀, h1, h2⟩

/-- For `|a| ≤ a₀/2`, the shift `g + a` of a strict subsolution is a
strict subsolution with `a₀` replaced by `a₀/2` and the same `δ₀`. -/
theorem IsStrictSubWith.add_const {U : Set (E d)} {Q g : E d → ℝ} {a₀ δ₀ : ℝ}
    (h : IsStrictSubWith U Q g a₀ δ₀) {a : ℝ} (ha : |a| ≤ a₀ / 2) :
    IsStrictSubWith U Q (fun x ↦ g x + a) (a₀ / 2) δ₀ := by
  obtain ⟨hg, ha₀, hδ₀, h1, h2⟩ := h
  have hab := abs_le.1 ha
  refine ⟨hg.add contDiff_const, half_pos ha₀, hδ₀, fun x hx hgx ↦ ?_, fun x hx hgx ↦ ?_⟩
  · rw [laplacian_add_const hg.contDiffAt]
    exact h1 x hx (by linarith)
  · rw [gradient_add_const]
    refine h2 x hx ?_
    have := abs_le.1 hgx
    rw [abs_le]; constructor <;> linarith

/-- For `|a| ≤ a₀/2`, the shift `g + a` of a strict supersolution is a
strict supersolution with `a₀` replaced by `a₀/2` and the same `δ₀`. -/
theorem IsStrictSuperWith.add_const {U : Set (E d)} {Q g : E d → ℝ} {a₀ δ₀ : ℝ}
    (h : IsStrictSuperWith U Q g a₀ δ₀) {a : ℝ} (ha : |a| ≤ a₀ / 2) :
    IsStrictSuperWith U Q (fun x ↦ g x + a) (a₀ / 2) δ₀ := by
  obtain ⟨hg, ha₀, hδ₀, h1, h2⟩ := h
  have hab := abs_le.1 ha
  refine ⟨hg.add contDiff_const, half_pos ha₀, hδ₀, fun x hx hgx ↦ ?_, fun x hx hgx ↦ ?_⟩
  · rw [laplacian_add_const hg.contDiffAt]
    exact h1 x hx (by linarith)
  · rw [gradient_add_const]
    refine h2 x hx ?_
    have := abs_le.1 hgx
    rw [abs_le]; constructor <;> linarith

/-- Shifts of a strict subsolution by small constants are strict subsolutions. -/
theorem IsStrictSub.exists_add_const {U : Set (E d)} {Q g : E d → ℝ} (h : IsStrictSub U Q g) :
    ∃ a₀ > 0, ∀ a : ℝ, |a| ≤ a₀ / 2 → IsStrictSub U Q (fun x ↦ g x + a) := by
  obtain ⟨a₀, δ₀, hw⟩ := isStrictSub_iff.1 h
  exact ⟨a₀, hw.2.1, fun a ha ↦ isStrictSub_iff.2 ⟨_, _, hw.add_const ha⟩⟩

/-- Shifts of a strict supersolution by small constants are strict supersolutions. -/
theorem IsStrictSuper.exists_add_const {U : Set (E d)} {Q g : E d → ℝ}
    (h : IsStrictSuper U Q g) :
    ∃ a₀ > 0, ∀ a : ℝ, |a| ≤ a₀ / 2 → IsStrictSuper U Q (fun x ↦ g x + a) := by
  obtain ⟨a₀, δ₀, hw⟩ := isStrictSuper_iff.1 h
  exact ⟨a₀, hw.2.1, fun a ha ↦ isStrictSuper_iff.2 ⟨_, _, hw.add_const ha⟩⟩

end EllipticBernoulli

end
