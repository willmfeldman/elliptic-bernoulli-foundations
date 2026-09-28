/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Regularity

/-!
# Headline statements: classical solutions

`IsClassicalSolution U Q u` is the classical solution of Kriventsov–Weiss, Definition 9.1, with a
variable coefficient `Q`. The theorems proving the statements live in
`EllipticBernoulli/Classical/*`.

* `ClassicalViscStatement`: classical ⇒ viscosity.
* `ClassicalInnerVarStatement`: classical ⇒ the inner-variation identity (the remark after
  Kriventsov–Weiss, Definition 9.1), in the form of `innerVarIntegrand`, over `U`, for Lipschitz
  test fields.
* `ClassicalLipschitzBoundStatement`: the Alt–Caffarelli gradient bound in the form of
  Kriventsov–Weiss, Proposition 9.1, with `Q ≡ 1`.

Result numbers of Kriventsov–Weiss are those of arXiv:2306.10131v2.

## References

* D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

@[expose] public section

namespace EllipticBernoulli

/-- **Classical solutions are viscosity solutions.** The proof uses neither the continuity of `Q`
nor a sign condition on `Q`. Proved by `IsClassicalSolution.isViscSolution`
(`Classical/Viscosity.lean`). -/
def ClassicalViscStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}, IsClassicalSolution U Q u → ContinuousOn Q U →
    IsViscSolution U Q u

/-- **Classical solutions satisfy the inner-variation identity** (the remark after
Kriventsov–Weiss, Definition 9.1; the identity is (2.5) in Abedin–Feldman–Stinson,
Definition 2.8(iv)) with `χ = 1_{{u > 0} ∩ U}`, for Lipschitz `Q ≥ c > 0` and every Lipschitz
test field `ξ` compactly supported in `U`. Points with `{u > 0}` on both sides of the free boundary
are allowed.

Kriventsov–Weiss obtain the identity by integration by parts. That step needs `|∇u| → Q` up to the
free boundary, while the definition only gives a one-sided normal difference quotient at each free
boundary point; here it is supplied by a blow-up argument with a half-space Liouville theorem and
De Silva's flatness theorem (`d ≥ 2`), and a separate argument in `d = 1`. Proved by
`IsClassicalSolution.integral_innerVarIntegrand_eq_zero` (`Classical/InnerVariation.lean`). -/
def ClassicalInnerVarStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ} {ξ : E d → E d}, IsClassicalSolution U Q u →
    (∃ K, LipschitzOnWith K Q U) → (∃ c > 0, ∀ y ∈ U, c ≤ Q y) → (∃ K, LipschitzWith K ξ) →
    HasCompactSupport ξ → tsupport ξ ⊆ U →
    ∫ x in U, innerVarIntegrand Q u ((posSet u U).indicator 1) ξ x = 0

/-- **Alt–Caffarelli gradient bound for classical solutions** (Kriventsov–Weiss, Proposition 9.1,
which cites Alt–Caffarelli, Theorem 6.3), with `Q ≡ 1`: `u` is `(1 + ω(r))`-Lipschitz on `B_r`.

Weaker than Kriventsov–Weiss state it: the modulus `ω` (named `w`) may depend on the Lipschitz
bound `L`, where Kriventsov–Weiss claim it depends only on the dimension. Alt–Caffarelli prove
Theorem 6.3 only for their weak solutions, and a classical solution need not be one (`|x_n|` is
classical, with empty reduced boundary). The proof here uses instead the blow-up alternative of
Alt–Caffarelli, Remark 6.4, made uniform over the class of `L`-Lipschitz classical solutions with
`u(0) = 0`. Proved by `classical_lipschitz_bound` (`Classical/GradientBound.lean`). -/
def ClassicalLipschitzBoundStatement : Prop :=
  ∀ {n : ℕ} (L : ℝ≥0),
    ∃ w : ℝ → ℝ, ContinuousOn w (Ico 0 1) ∧ MonotoneOn w (Ico 0 1) ∧
      Tendsto w (𝓝[>] 0) (𝓝 0) ∧
      ∀ u : E n → ℝ, IsClassicalSolution (ball 0 1) (fun _ ↦ 1) u →
        LipschitzOnWith L u (ball 0 1) →
        u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r)

end EllipticBernoulli
