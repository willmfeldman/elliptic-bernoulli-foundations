module

public import EllipticBernoulli.TwoPhase.ClassificationMain

/-!
# Solution: classification of global two-phase minimizers

Discharges the challenge through the library module imported above: `twoPhaseClassification`
(`TwoPhaseClassificationStatement`), whose conclusion `u x = twoPlane a b e c x` unfolds to the
challenge's.

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace EllipticBernoulli

theorem challenge_twoPhaseClassification {d : ℕ} {u : E d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hpos : ∃ x, 0 < u x)
    (hneg : ∃ x, u x < 0) :
    ∃ (e : E d) (c a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = 1 ∧
      ∀ x, u x = a * max (inner ℝ x e + c) 0 - b * max (-(inner ℝ x e + c)) 0 :=
  twoPhaseClassification hu hmin hpos hneg

end EllipticBernoulli
