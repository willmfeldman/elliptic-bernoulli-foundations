module

public import EllipticBernoulli.TwoPhase.ClassificationMain

/-!
# Solution: the Alt–Caffarelli–Friedman monotonicity formula

Discharges the challenge through the library module imported above: `acfMonotoneIn`
(`ACFMonotoneIn d` for `d ≥ 2`), applied to the ACF pair `IsACFPair u₁ u₂ x₀ L` assembled from the
challenge's hypotheses.

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace EllipticBernoulli

theorem challenge_acfMonotoneIn {d : ℕ} (hd : 2 ≤ d) {u₁ u₂ : E d → ℝ} {x₀ : E d} {L : ℝ≥0}
    (hnn₁ : ∀ x, 0 ≤ u₁ x) (hnn₂ : ∀ x, 0 ≤ u₂ x)
    (hlip₁ : LipschitzWith L u₁) (hlip₂ : LipschitzWith L u₂)
    (hharm₁ : InnerProductSpace.HarmonicOnNhd u₁ {x | 0 < u₁ x})
    (hharm₂ : InnerProductSpace.HarmonicOnNhd u₂ {x | 0 < u₂ x})
    (hmul : ∀ x, u₁ x * u₂ x = 0) (hx₁ : u₁ x₀ = 0) (hx₂ : u₂ x₀ = 0) :
    MonotoneOn (fun r ↦ acfPhi u₁ u₂ x₀ r) (Ioi 0) :=
  acfMonotoneIn hd u₁ u₂ x₀ L
    ⟨hnn₁, hnn₂, hlip₁, hlip₂, hharm₁, hharm₂, hmul, hx₁, hx₂⟩

end EllipticBernoulli
