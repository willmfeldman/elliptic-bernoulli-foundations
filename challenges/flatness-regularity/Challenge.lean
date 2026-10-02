module

-- challenge-prep: split vocabulary (aux-proof reuse: a merged file fails the fingerprint diff)
-- One module per library file. Concatenating them lets later definitions reuse earlier auxiliary
-- `_proof_k` constants that the library mints per module, so the values would no longer match
-- (`scripts/fingerprint-challenges.sh`).
public import Vocabulary.Setting
public import Vocabulary.Sobolev
public import Vocabulary.Touching
public import Vocabulary.Viscosity
public import Vocabulary.Regularity

@[expose] public section

/-!
# Challenge: flat free boundaries are regular (De Silva)

Trusted statement surface for De Silva's theorem (De Silva (2011), Theorem 1.1, with `f = 0`,
`g = Q`). De Silva allows a Hölder coefficient `g`; here `Q` is `L`-Lipschitz. For `2 ≤ d` and
`0 < qmin ≤ Q ≤ qmax`, there is `ε̄ > 0` such that a viscosity solution (Abedin–Feldman–Stinson,
Definition 2.1) which is two-sidedly `ε̄ r`-flat with slope `Q(x₀)` in `B_r(x₀) ⊆ U`, `0 < r ≤ ε̄`,
at a free boundary point `x₀` has a `C^{1,γ}` free boundary in `B_{r/2}(x₀)`
(`IsC1GammaHypersurfaceNear`), and is classical near `x₀` (`IsClassicalNear`: the free boundary is a
`C^{1,γ}` hypersurface, `u` is `C²` and harmonic in `{u > 0}`, `∇u` extends continuously to the free
boundary with `|∇u| = Q` there). The exponent `γ`, the Hölder constant and the `IsClassicalNear`
radius are existential for each solution; in De Silva they do not depend on the solution.

The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Basic/Touching.lean`,
`Defs/Viscosity.lean`, `Defs/Regularity.lean`), with the library's names, definitions and
order. Every file imports Mathlib modules only (the same ones as the library file it restates).

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

noncomputable section

open Set Filter Topology Metric
open scoped NNReal

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: flatness implies a `C^{1,γ}` free boundary (De Silva (2011), Theorem 1.1). -/
theorem challenge_isC1GammaHypersurfaceNear_of_flat (hd : 2 ≤ d) (L : ℝ≥0) (qmin qmax : ℝ)
    (hqmin : 0 < qmin) :
    ∃ εbar > 0, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsC1GammaHypersurfaceNear (freeBoundary u U) x₀ (r / 2) := by
  sorry

/-- Challenge: flatness implies classical regularity near the free boundary point. -/
theorem challenge_isClassicalNear_of_flat (hd : 2 ≤ d) (L : ℝ≥0) (qmin qmax : ℝ)
    (hqmin : 0 < qmin) :
    ∃ εbar > 0, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsClassicalNear U Q u x₀ := by
  sorry

end EllipticBernoulli
