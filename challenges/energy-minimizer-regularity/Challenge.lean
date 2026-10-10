module

-- challenge-prep: split vocabulary (aux-proof reuse: a merged file fails the fingerprint diff)
-- One module per library file. Concatenating them lets later definitions reuse earlier auxiliary
-- `_proof_k` constants that the library mints per module, so the values would no longer match
-- (`scripts/fingerprint-challenges.sh`).
public import Vocabulary.Setting
public import Vocabulary.Sobolev
public import Vocabulary.Variational
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

@[expose] public section

/-!
# Challenge: regularity of local energy minimizers

Trusted statement surface for the interior regularity of local minimizers of the Alt–Caffarelli
energy `J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}` (Alt–Caffarelli (1981), §§2–3; Velichkov, Ch. 3 and
Proposition 7.1). Let `Q` be continuous with `0 ≤ Q ≤ C` on the open set `U`, and let `u ≥ 0` a.e. on
`U` be a local minimizer (`IsLocalEnergyMinimizer`, energies compared on balls `B ⋐ U`). Then `u` has
an a.e.-equal representative `v` on `U` which is again a local minimizer, is locally Lipschitz and
non-negative on `U`, has open positivity set `{v > 0} ∩ U`, and is `C^∞` and harmonic there.
Continuity is proved by De Giorgi's method (Giusti, Ch. 7) rather than by the harmonic replacement
of Alt–Caffarelli.

The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Defs/Variational.lean`), with the library's names,
definitions and order. Every file imports Mathlib modules only (the same ones as the library file
it restates).

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
* E. Giusti, *Direct Methods in the Calculus of Variations*, World Scientific, 2003.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Laplacian

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: a local energy minimizer has a locally Lipschitz representative, smooth and harmonic
in its positivity set (Alt–Caffarelli (1981); Velichkov, Proposition 7.1). -/
theorem challenge_isLocalEnergyMinimizer_exists_regular_representative {U : Set (E d)}
    {Q u : E d → ℝ} (hU : IsOpen U) (hQc : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U Q u) :
    ∃ v : E d → ℝ, (∀ᵐ x ∂volume.restrict U, v x = u x) ∧ IsLocalEnergyMinimizer U Q v ∧
      LocallyLipschitzOn U v ∧ (∀ x ∈ U, 0 ≤ v x) ∧ IsOpen (posSet v U) ∧
      ContDiffOn ℝ ∞ v (posSet v U) ∧ ∀ x ∈ posSet v U, Δ v x = 0 := by
  sorry

end EllipticBernoulli
