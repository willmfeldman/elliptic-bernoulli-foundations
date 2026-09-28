import Challenge.Setting
import Challenge.Sobolev
import Challenge.Variational

/-!
# Challenge: planar 1-homogeneous inner variational solutions

Trusted statement surface for the classification of 1-homogeneous inner variational solutions in the
plane (after Jerison–Kamburov, §5, whose Propositions 5.3 and 5.4 assume stronger hypotheses). An
inner variational solution `(v, χ)` of the one-phase problem with constant `Q ≡ q > 0` on all of
`ℝ²` (Abedin–Feldman–Stinson, Definition 2.8, `IsInnerVarSolution`) with `v` 1-homogeneous is a
half-plane solution, a two-plane solution `α |x · e|` with `χ = 1` a.e., or trivial with `χ = 0`
a.e.

The project vocabulary is restated in `Challenge/*.lean`, one file per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Defs/Variational.lean`), with the library's names,
definitions and order. Every file imports Mathlib modules only (the same ones as the library file
it restates).

## References

* D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res.
  Not. IMRN 2016, no. 19, 5922–5987; arXiv:1412.4106.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace EllipticBernoulli

/-- Challenge: `PlanarHomogeneousClassificationStatement`. -/
theorem challenge_classification_homogeneous_planar {q : ℝ} (hq : 0 < q) {v χ : E 2 → ℝ}
    (h : IsInnerVarSolution univ (fun _ ↦ q) v χ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ y : E 2, v (t • y) = t * v y) :
    ∃ e : E 2, ‖e‖ = 1 ∧
      (((∀ y, v y = q * max (inner ℝ y e) 0) ∧
          ∀ᵐ y, χ y = {z : E 2 | 0 < inner ℝ z e}.indicator 1 y) ∨
        (∃ α : ℝ, 0 ≤ α ∧ (∀ y, v y = α * |inner ℝ y e|) ∧ ∀ᵐ y, χ y = 1) ∨
        ((∀ y, v y = 0) ∧ ∀ᵐ y, χ y = 0)) := by
  sorry

end EllipticBernoulli
