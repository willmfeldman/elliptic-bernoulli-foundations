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
# Challenge: the Friedland–Hayman inequality

Trusted statement surface for the Friedland–Hayman inequality (Friedland–Hayman (1976); Beck–Jerison,
Theorem 1.1, for homogeneous harmonic functions) in every dimension `d ≥ 2`: for nonempty,
relatively open, disjoint `Γ₁, Γ₂ ⊆ 𝕊^{d-1}`, the characteristic exponents satisfy
`α_d(Γ₁) + α_d(Γ₂) ≥ 2`.

Here `α_d(Γ) = sphExponent Γ = κ_d(λ₁(Γ))`, where `κ_d(λ)` is the nonnegative root of
`α (α + d - 2) = λ` and `λ₁(Γ) = sphEigenvalue Γ` is the infimum of the Rayleigh quotients
`∫_𝕊 |∇_𝕊 f|² dσ / ∫_𝕊 f² dσ` over functions `f` on the sphere that are Lipschitz for the chordal
metric, vanish off `Γ`, and have `∫_𝕊 f² dσ > 0`. The tangential gradient is the gradient of the
`0`-homogeneous extension `x ↦ f (x / ‖x‖)`, and `σ` is Mathlib's sphere measure
`(volume : Measure (E d)).toSphere`. The sources use `H¹₀(Γ)` trial functions instead of Lipschitz
ones.

The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Defs/Variational.lean`, `Defs/TwoPhase.lean`), with
the library's names, definitions and order. Every file imports Mathlib modules only (the same ones
as the library file it restates).

## References

* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* T. Beck, D. Jerison, *The Friedland–Hayman inequality and Caffarelli's contraction theorem*,
  arXiv:2102.00571.
-/

noncomputable section

open Metric

namespace EllipticBernoulli

/-- Challenge: the Friedland–Hayman inequality. For `d ≥ 2` and nonempty, relatively open, disjoint
`Γ₁, Γ₂ ⊆ 𝕊^{d-1}`, `α_d(Γ₁) + α_d(Γ₂) ≥ 2` (Friedland–Hayman (1976)). -/
theorem challenge_friedlandHayman {d : ℕ} (hd : 2 ≤ d) (Γ₁ Γ₂ : Set (sphere (0 : E d) 1))
    (hΓ₁ : IsOpen Γ₁) (hΓ₂ : IsOpen Γ₂) (hne₁ : Γ₁.Nonempty) (hne₂ : Γ₂.Nonempty)
    (hdisj : Disjoint Γ₁ Γ₂) :
    2 ≤ sphExponent Γ₁ + sphExponent Γ₂ := by
  sorry

end EllipticBernoulli

end
