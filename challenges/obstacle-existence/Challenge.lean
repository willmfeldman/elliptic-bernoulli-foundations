module

-- challenge-prep: split vocabulary (aux-proof reuse: a merged file fails the fingerprint diff)
-- One module per library file. Concatenating them lets later definitions reuse earlier auxiliary
-- `_proof_k` constants that the library mints per module, so the values would no longer match
-- (`scripts/fingerprint-challenges.sh`).
public import Vocabulary.Setting
public import Vocabulary.Sobolev
public import Vocabulary.Variational

@[expose] public section

/-!
# Challenge: existence and continuity for the obstacle problem

Trusted statement surface for the obstacle problem of the Alt–Caffarelli energy
`J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}` (Abedin–Feldman–Stinson, proof of Lemma 6.3).
`IsObstacleMinimizer U B Q u K w Gw` says that `w` minimizes `J_Q(·; B)` among `H¹_loc(U)`
competitors equal to `u` a.e. off `B` with `v y ∈ K y` a.e., and that `w` itself satisfies both
conditions pointwise. Minimizers exist for bounded measurable `Q` and closed constraints admitting
`u` (direct method); for the two constraints `0 ≤ v ≤ u` and `u ≤ v`, with `Q` Lipschitz and
`0 < c ≤ Q ≤ C` and `u ≥ 0` locally Lipschitz, every minimizer has a representative continuous on
all of `U`, including across `∂B` (De Giorgi; the interior continuity argument is new here).

The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Defs/Variational.lean`), with the library's names,
definitions and order. Every file imports Mathlib modules only (the same ones as the library file
it restates).

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: existence for the obstacle problem (direct method). -/
theorem challenge_exists_isObstacleMinimizer {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d}
    {K : E d → Set ℝ} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ C, ∀ x ∈ U, |Q x| ≤ C)
    (hQm : Measurable Q)
    (hu : MemH1Loc U u Gu) (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) (hK : ∀ y, IsClosed (K y))
    (huK : ∀ y ∈ U, u y ∈ K y) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), IsObstacleMinimizer U (ball x₀ r) Q u K w Gw := by
  sorry

/-- Challenge: continuity of obstacle minimizers on all of `U`, for the constraints `0 ≤ v ≤ u` and
`u ≤ v`. -/
theorem challenge_isObstacleMinimizer_exists_continuousOn {U : Set (E d)} {Q u : E d → ℝ}
    {K : E d → Set ℝ} {w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U)
    (hQ : ∃ L, LipschitzOnWith L Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y) (hB : closedBall x₀ r ⊆ U)
    (hr : 0 < r) (hK : K = (fun y ↦ Icc 0 (u y)) ∨ K = (fun y ↦ Ici (u y)))
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u K w Gw) :
    ∃ w' : E d → ℝ, (∀ᵐ y ∂volume.restrict U, w' y = w y) ∧
      IsObstacleMinimizer U (ball x₀ r) Q u K w' Gw ∧ ContinuousOn w' U := by
  sorry

end EllipticBernoulli
