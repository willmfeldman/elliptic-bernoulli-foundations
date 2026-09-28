/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Defs.Regularity

/-!
# Headline statements: De Silva's flatness theory

De Silva (2011), with right-hand side `f = 0` and free boundary coefficient `g = Q`. The viscosity
notion here (Abedin–Feldman–Stinson, Definition 2.1) tests with globally `C^∞` functions, while
De Silva tests with `C²` functions, so every barrier is made globally smooth.

* `FlatHarnackStatement`: De Silva (2011), Theorem 3.1.
* `ImprovementStatement`: De Silva (2011), Lemma 4.1.
* `FlatClassicalStatement` and `FlatGraphStatement`: De Silva (2011), Theorem 1.1, at a free
  boundary point `x₀` of a solution that is flat in `B_r(x₀)`; the first concludes that `u` is
  classical near `x₀`, the second only the `C^{1,γ}` graph property.

The theorems proving them live in `EllipticBernoulli/Flatness/*`.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology Metric
open scoped NNReal

@[expose] public section

namespace EllipticBernoulli

/-- **De Silva's Harnack inequality for flat solutions** (De Silva (2011), Theorem 3.1, with the
one-step Lemma 3.3; `f = 0`, `g = Q`), in the normalization `Q ≈ 1`. Suppose `u` is a viscosity
solution in `U ⊇ B_r(x̄)` with `|Q - 1| ≤ ε²` there, and
`(y · e + a₀)₊ ≤ u(y) ≤ (y · e + b₀)₊` in `B_r(x̄)` with `a₀ ≤ b₀`, `b₀ - a₀ ≤ ε r` and `ε ≤ ε̄`.
Then the trapping improves on `B_{r/20}(x̄)`: `b₁ - a₁ ≤ (1 - c) ε r` with `a₀ ≤ a₁ ≤ b₁ ≤ b₀`.

De Silva assumes `x̄ ∈ Ω⁺(u) ∪ F(u)`, which forces `a₀ ≤ b₀`; here `a₀ ≤ b₀` is a hypothesis.
Without it the statement is false (`u ≡ 0`, `a₀ = -2`, `b₀ = -3`). Proved by `flat_harnack`
(`Flatness/Harnack.lean`). -/
def FlatHarnackStatement : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∃ εbar > 0, ∃ c ∈ Ioo (0 : ℝ) 1, ∀ (U : Set (E d)) (Q u : E d → ℝ)
    (e xbar : E d) (r ε a₀ b₀ : ℝ), IsOpen U → IsViscSolution U Q u → ‖e‖ = 1 → 0 < r →
    ball xbar r ⊆ U → 0 < ε → ε ≤ εbar → (∀ y ∈ ball xbar r, |Q y - 1| ≤ ε ^ 2) →
    a₀ ≤ b₀ → b₀ - a₀ ≤ ε * r →
    (∀ y ∈ ball xbar r, max (inner ℝ y e + a₀) 0 ≤ u y ∧ u y ≤ max (inner ℝ y e + b₀) 0) →
    ∃ a₁ b₁ : ℝ, a₀ ≤ a₁ ∧ a₁ ≤ b₁ ∧ b₁ ≤ b₀ ∧ b₁ - a₁ ≤ (1 - c) * ε * r ∧
      ∀ y ∈ ball xbar (r / 20),
        max (inner ℝ y e + a₁) 0 ≤ u y ∧ u y ≤ max (inner ℝ y e + b₁) 0

/-- **De Silva's improvement of flatness** (De Silva (2011), Lemma 4.1, with `f = 0`, `g = Q`).
There are universal `r₀, C` such that for each `0 < r ≤ r₀` there is `ε₀(r)` with the following
property. Suppose `u` is a viscosity solution in `U ⊇ B_1` with `0` a free boundary point,
`|Q - 1| ≤ ε²` on `B_1`, and `(y · e - ε)₊ ≤ u(y) ≤ (y · e + ε)₊` on `B_1` with `ε ≤ ε₀`. Then
`(y · ν - r ε / 2)₊ ≤ u(y) ≤ (y · ν + r ε / 2)₊` on `B_r` for some unit `ν` with `|ν - e| ≤ C ε`.

The smallness `|Q - 1| ≤ ε²` is De Silva's (3.2). De Silva prints `|ν - e| ≤ C ε²` in (4.2); the
proof gives `C ε`, and `C ε²` is false. Proved by `improvement_of_flatness`
(`Flatness/Improvement.lean`). -/
def ImprovementStatement : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∃ r₀ > 0, ∃ C > 0, ∀ r, 0 < r → r ≤ r₀ → ∃ ε₀ > 0,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U → ball 0 1 ⊆ U →
    IsViscSolution U Q u → (0 : E d) ∈ freeBoundary u U → ‖e‖ = 1 → 0 < ε → ε ≤ ε₀ →
    (∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2) →
    (∀ y ∈ ball (0 : E d) 1, max (inner ℝ y e - ε) 0 ≤ u y ∧ u y ≤ max (inner ℝ y e + ε) 0) →
    ∃ ν : E d, ‖ν‖ = 1 ∧ ‖ν - e‖ ≤ C * ε ∧ ∀ y ∈ ball (0 : E d) r,
      max (inner ℝ y ν - r * ε / 2) 0 ≤ u y ∧ u y ≤ max (inner ℝ y ν + r * ε / 2) 0

/-- **Flatness implies classical** (De Silva (2011), Theorem 1.1; the classical property near `x₀`
is then derived by interior estimates, without boundary Schauder theory). For `2 ≤ d`, a Lipschitz
constant `L` of `Q` and bounds `0 < qmin ≤ Q ≤ qmax` on `U`, there is `ε̄ > 0` such that every
viscosity solution which is two-sidedly `ε̄ r`-flat with slope `Q(x₀)` in `B_r(x₀) ⊆ U`,
`0 < r ≤ ε̄`, at a free boundary point `x₀` is classical near `x₀`.

De Silva allows a Hölder coefficient (`[g]_{C^{0,β}} ≤ ε̄`); here `Q` is Lipschitz, and after the
rescaling `u_r(y) = u(x₀ + r y) / (r Q(x₀))` with `r ≤ ε̄` its Lipschitz seminorm is at most
`ε̄ L / qmin`. De Silva's exponent and radius do not depend on the solution, whereas
`IsClassicalNear` chooses the exponent, the Hölder constant and the radius per solution. The proof
does not use `qmax`. Proved by `isClassicalNear_of_flat` (`Flatness/Classical.lean`). -/
def FlatClassicalStatement : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (L : ℝ≥0) (qmin qmax : ℝ), 0 < qmin → ∃ εbar > 0,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsClassicalNear U Q u x₀

/-- **Flatness implies a `C^{1,γ}` free boundary** (De Silva (2011), Theorem 1.1): same hypotheses
as `FlatClassicalStatement` (with the same remarks on the coefficient and the constants); the free
boundary is a `C^{1,γ}` graph in `B_{r/2}(x₀)`. Proved by `isC1GammaHypersurfaceNear_of_flat`
(`Flatness/Classical.lean`). -/
def FlatGraphStatement : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (L : ℝ≥0) (qmin qmax : ℝ), 0 < qmin → ∃ εbar > 0,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsC1GammaHypersurfaceNear (freeBoundary u U) x₀ (r / 2)

end EllipticBernoulli
