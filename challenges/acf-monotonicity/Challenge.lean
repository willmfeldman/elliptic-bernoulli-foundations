module

-- challenge-prep: split vocabulary (aux-proof reuse: a merged file fails the fingerprint diff)
-- One module per library file. Concatenating them lets later definitions reuse earlier auxiliary
-- `_proof_k` constants that the library mints per module, so the values would no longer match
-- (`scripts/fingerprint-challenges.sh`).
public import Vocabulary.Setting
public import Vocabulary.Sobolev
public import Vocabulary.Variational
public import Vocabulary.TwoPhase

@[expose] public section

/-!
# Challenge: the Alt–Caffarelli–Friedman monotonicity formula

Trusted statement surface for the Alt–Caffarelli–Friedman monotonicity formula
(Alt–Caffarelli–Friedman (1984); Salato, Theorem 1.1) in every dimension `d ≥ 2`. Let
`u₁, u₂ : ℝᵈ → ℝ` be nonnegative, `L`-Lipschitz and harmonic on the open sets `{uᵢ > 0}`, with
`u₁ u₂ ≡ 0` and `u₁(x₀) = u₂(x₀) = 0`. Then
`r ↦ Φ(u₁, u₂, x₀, r) = r⁻⁴ I(u₁, x₀, r) I(u₂, x₀, r)`, where
`I(w, x₀, r) = ∫_{B_r(x₀)} |∇w(x)|² |x - x₀|^{2-d} dx` (`acfPhi`, `acfIntegral`), is
nondecreasing on `(0, ∞)`.

Alt–Caffarelli–Friedman assume continuity and subharmonicity in the sense of distributions; here
the functions are Lipschitz and harmonic in their positivity sets. The statement assumes no
Friedland–Hayman inequality: the solution proves it (Friedland–Hayman (1976)) and uses it.

The hypotheses are written out; they are the fields of the vocabulary's `IsACFPair u₁ u₂ x₀ L`.
The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Defs/Variational.lean`, `Defs/TwoPhase.lean`), with
the library's names, definitions and order. Every file imports Mathlib modules only (the same ones
as the library file it restates).

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473.
-/

noncomputable section

open Set
open scoped NNReal

namespace EllipticBernoulli

/-- Challenge: the Alt–Caffarelli–Friedman monotonicity formula. For `d ≥ 2`, nonnegative
`L`-Lipschitz `u₁, u₂` harmonic in their positivity sets, with `u₁ u₂ ≡ 0` and
`u₁(x₀) = u₂(x₀) = 0`, `r ↦ Φ(u₁, u₂, x₀, r)` is nondecreasing on `(0, ∞)`
(Alt–Caffarelli–Friedman (1984)). -/
theorem challenge_acfMonotoneIn {d : ℕ} (hd : 2 ≤ d) {u₁ u₂ : E d → ℝ} {x₀ : E d} {L : ℝ≥0}
    (hnn₁ : ∀ x, 0 ≤ u₁ x) (hnn₂ : ∀ x, 0 ≤ u₂ x)
    (hlip₁ : LipschitzWith L u₁) (hlip₂ : LipschitzWith L u₂)
    (hharm₁ : InnerProductSpace.HarmonicOnNhd u₁ {x | 0 < u₁ x})
    (hharm₂ : InnerProductSpace.HarmonicOnNhd u₂ {x | 0 < u₂ x})
    (hmul : ∀ x, u₁ x * u₂ x = 0) (hx₁ : u₁ x₀ = 0) (hx₂ : u₂ x₀ = 0) :
    MonotoneOn (fun r ↦ acfPhi u₁ u₂ x₀ r) (Ioi 0) := by
  sorry

end EllipticBernoulli

end
