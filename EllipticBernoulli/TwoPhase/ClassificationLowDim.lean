/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Classification
import EllipticBernoulli.Sphere.CapLift
import EllipticBernoulli.Sphere.FriedlandHayman

/-!
# Classification of global two-phase minimizers in dimensions `d ≤ 4`

In dimensions `2 ≤ d ≤ 4` the Friedland–Hayman inequality is proved directly (explicit cap
eigenvalues for `d = 2, 4`, and lifting from `d = 4` to `d = 3`), so the classification of global
Lipschitz two-phase minimizers holds unconditionally there; `d = 1` is proved directly and `d = 0`
is vacuous.
-/

@[expose] public section

namespace EllipticBernoulli

/-- **Classification of global two-phase minimizers for `d ≤ 4`**: a Lipschitz local minimizer of
`J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ`, `d ≤ 4`, that takes a positive and a negative value is a
two-plane function `a (x·e + c)⁺ - b (x·e + c)⁻` with `‖e‖ = 1`, `a, b > 0` and `a² - b² = 1`. -/
theorem twoPhaseClassificationIn_of_le_four {d : ℕ} (hd : d ≤ 4) : TwoPhaseClassificationIn d := by
  rcases Nat.lt_or_ge d 2 with h | h
  · interval_cases d
    · intro u L _ _ hpos hneg
      obtain ⟨x, hx⟩ := hpos
      obtain ⟨y, hy⟩ := hneg
      have : x = y := Subsingleton.elim x y
      subst this
      exact absurd (hx.trans hy) (lt_irrefl _)
    · exact twoPhaseClassificationIn_one
  · interval_cases d
    · exact twoPhaseClassification_of_friedlandHayman le_rfl friedlandHaymanIn_two
    · exact twoPhaseClassification_of_friedlandHayman (by norm_num) friedlandHaymanIn_three
    · exact twoPhaseClassification_of_friedlandHayman (by norm_num) friedlandHaymanIn_four

end EllipticBernoulli
