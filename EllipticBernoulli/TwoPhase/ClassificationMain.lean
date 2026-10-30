/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Classification
import EllipticBernoulli.Sphere.CapInequality
import EllipticBernoulli.TwoPhase.ACF

/-!
# ACF monotonicity and the classification of global two-phase minimizers in every dimension

The Friedland–Hayman inequality holds in every dimension `d ≥ 2` (`friedlandHayman`). Hence:

* `acfMonotoneIn`: the Alt–Caffarelli–Friedman monotonicity formula holds in every dimension
  `d ≥ 2`, with no Friedland–Hayman hypothesis;
* `twoPhaseClassification`: global Lipschitz two-phase minimizers are classified in every
  dimension.

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473.
-/

@[expose] public section

namespace EllipticBernoulli

/-- **Alt–Caffarelli–Friedman monotonicity** (Alt–Caffarelli–Friedman 1984; Salato,
arXiv:2506.13473, Theorem 1.1). For `d ≥ 2` and every ACF pair `(u₁, u₂)` at `x₀` (nonnegative,
Lipschitz, harmonic in their positivity sets, with `u₁ u₂ ≡ 0` and `u₁ x₀ = u₂ x₀ = 0`),
`r ↦ Φ(u₁, u₂, x₀, r) = r⁻⁴ I(u₁) I(u₂)` is nondecreasing on `(0, ∞)`. The proof uses the
Friedland–Hayman inequality (Friedland–Hayman 1976), proved here as `friedlandHayman`. -/
theorem acfMonotoneIn {d : ℕ} (hd : 2 ≤ d) : ACFMonotoneIn d :=
  acfMonotoneIn_of_friedlandHayman hd (friedlandHayman d hd)

/-- **Classification of global two-phase minimizers** (after Alt–Caffarelli–Friedman 1984): a
Lipschitz local minimizer of `J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ` that takes a positive and a
negative value is a two-plane function `a (x·e + c)⁺ - b (x·e + c)⁻` with `‖e‖ = 1`, `a, b > 0`
and `a² - b² = 1`. -/
theorem twoPhaseClassification : TwoPhaseClassificationStatement :=
  twoPhaseClassification_of_forall_friedlandHayman friedlandHayman

end EllipticBernoulli
