/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational

/-!
# Headline statements: blow-ups and their classification

The theorems proving them live in `EllipticBernoulli/Blowup/*`.

* `PlanarHomogeneousClassificationStatement` (after Jerison–Kamburov, §5) classifies 1-homogeneous
  global inner variational solutions in `ℝ²` with constant coefficient `q > 0`. The third
  alternative (`v ≡ 0`, `χ = 0` a.e.) is a genuine inner variational solution; it is missing from
  the list in the proof sketch of Abedin–Feldman–Stinson, Corollary 1.2. Jerison–Kamburov,
  Propositions 5.3 and 5.4, classify blow-ups and blow-downs under stronger hypotheses: `u` is
  Lipschitz, non-degenerate, and both a viscosity and a variational solution (`χ = 1_{u>0}`). The
  statement here follows the case analysis in the proof of Proposition 5.3; without those
  hypotheses there are more alternatives.

## References

* D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res.
  Not. IMRN 2016, no. 19, 5922–5987; arXiv:1412.4106.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric

@[expose] public section

namespace EllipticBernoulli

/-- **Planar 1-homogeneous inner variational solutions** (after Jerison–Kamburov, §5): a
1-homogeneous inner variational solution on `ℝ²` with constant coefficient `q > 0` is either a
half-plane solution `q (y·e)₊` with `χ = 1_{y·e>0}` a.e., or a two-plane function `α |y·e|`
(`α ≥ 0`) with `χ = 1` a.e., or `v ≡ 0` with `χ = 0` a.e. Proved by
`classification_homogeneous_planar` (`Blowup/PlanarClassification.lean`). -/
def PlanarHomogeneousClassificationStatement : Prop :=
  ∀ {q : ℝ}, 0 < q → ∀ {v χ : E 2 → ℝ},
    IsInnerVarSolution univ (fun _ ↦ q) v χ →
    (∀ t : ℝ, 0 < t → ∀ y : E 2, v (t • y) = t * v y) →
    ∃ e : E 2, ‖e‖ = 1 ∧
      (((∀ y, v y = q * max (inner ℝ y e) 0) ∧
          ∀ᵐ y, χ y = {z : E 2 | 0 < inner ℝ z e}.indicator 1 y) ∨
        (∃ α : ℝ, 0 ≤ α ∧ (∀ y, v y = α * |inner ℝ y e|) ∧ ∀ᵐ y, χ y = 1) ∨
        ((∀ y, v y = 0) ∧ ∀ᵐ y, χ y = 0))

end EllipticBernoulli
