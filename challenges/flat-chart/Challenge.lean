module

-- challenge-prep: split vocabulary (aux-proof reuse: a merged file fails the fingerprint diff)
-- One module per library file. Concatenating them lets later definitions reuse earlier auxiliary
-- `_proof_k` constants that the library mints per module, so the values would no longer match
-- (`scripts/fingerprint-challenges.sh`).
public import Vocabulary.Setting
public import Vocabulary.Sobolev
public import Vocabulary.Regularity
public import Vocabulary.Variational

@[expose] public section

/-!
# Challenge: smooth one-sided charts at flat free-boundary points

Trusted statement surface for the smoothness of the free boundary at flat points
(Kinderlehrer–Nirenberg (1977), with De Silva (2011) for the `C^{1,γ}` step). Let `d ≥ 2`, `U ⊆ ℝᵈ`
open, and `u` continuous and non-negative on `U`, a local minimizer (`IsLocalEnergyMinimizer`,
energies compared on balls `B ⋐ U`) of `J(v; B) = ∫_B |∇v|² + 1_{v>0}`. Let `x₀` be a free-boundary
point at which the half-plane solution `(y · e)₊` is a blow-up limit (`IsBlowupLimit`: the rescalings
`u(x₀ + r y)/r` converge to it locally uniformly along some sequence `r_n → 0⁺`), for a unit vector
`e`. Then near `x₀`, `u = max(F, 0)` for a function `F` which is `C^∞` on a ball `B_ρ(x₀) ⊆ U`, has
non-vanishing gradient there, is harmonic where it is positive, and satisfies `|∇F| = 1` on
`{F = 0}`; the positive side `{F > 0} ∩ B_ρ(x₀)` is preconnected. In particular the free boundary is
a `C^∞` hypersurface near `x₀`.

The coefficient is `Q ≡ 1`.

The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Defs/Regularity.lean`, `Defs/Variational.lean`), with
the library's names, definitions and order. Every file imports Mathlib modules only (the same ones
as the library file it restates).

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*, Proc. Amer. Math. Soc. 15
  (1964), 625–626.
-/

noncomputable section

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: a smooth one-sided chart at a flat free-boundary point of a local minimizer
(Kinderlehrer–Nirenberg (1977); De Silva (2011)). -/
theorem challenge_flat_chart (hd : 2 ≤ d) {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d}
    (hU : IsOpen U) (hc : ContinuousOn u U) (hnn : ∀ x ∈ U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) (hx₀ : x₀ ∈ freeBoundary u U) (he : ‖e‖ = 1)
    (hblow : IsBlowupLimit u x₀ (fun y ↦ max (inner ℝ y e) 0)) :
    ∃ ρ > 0, ball x₀ ρ ⊆ U ∧ ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ) ∧
      (∀ x ∈ ball x₀ ρ, u x = max (F x) 0) ∧ (∀ x ∈ ball x₀ ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ, F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ ball x₀ ρ, 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ | 0 < F x} := by
  sorry

end EllipticBernoulli
