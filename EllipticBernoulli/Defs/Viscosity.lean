/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Touching
public import EllipticBernoulli.Basic.Sobolev
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Viscosity notions for the one-phase problem

* Viscosity super/sub/solutions (Abedin–Feldman–Stinson, Definition 2.1).
* Smooth strict sub/supersolutions (Abedin–Feldman–Stinson, Definition 2.2), and their forms
  `IsStrictSubWith`/`IsStrictSuperWith` with explicit constants.
* Relaxed subsolutions/solutions (Abedin–Feldman–Stinson, Definition 2.3).
* Local smallest supersolutions / largest subsolutions (Abedin–Feldman–Stinson, Definition 2.6).
* Viscosity sub/superharmonicity on a set.

Test functions are globally smooth `E d → ℝ` rather than `C^∞(U)`, and touching is non-strict.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian NNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Viscosity solutions -/

/-- **Abedin–Feldman–Stinson, Definition 2.1(i)**, with globally smooth test functions.
`u ∈ C(U)`, `u ≥ 0`, is a viscosity supersolution of (1.1) in `U`: whenever a smooth `φ` touches
`u` from below at `x ∈ U`, either `Δφ(x) ≤ 0`, or `φ(x) = 0` and `|∇φ(x)| ≤ Q(x)`. -/
def IsViscSuper (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  ContinuousOn u U ∧ (∀ x ∈ U, 0 ≤ u x) ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x ∈ U, TouchesBelow φ u U x →
      Δ φ x ≤ 0 ∨ (φ x = 0 ∧ ‖∇ φ x‖ ≤ Q x)

/-- **Abedin–Feldman–Stinson, Definition 2.1(ii)**, with globally smooth test functions.
`u ∈ C(U)`, `u ≥ 0`, is a viscosity subsolution of (1.1) in `U`: whenever `φ` is smooth and `φ₊`
touches `u` from above in `\overline{{u > 0}} ∩ U` at `x`, either `Δφ(x) ≥ 0`, or `φ(x) = 0` and
`|∇φ(x)| ≥ Q(x)`. -/
def IsViscSub (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  ContinuousOn u U ∧ (∀ x ∈ U, 0 ≤ u x) ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x,
      TouchesAbove (fun y ↦ max (φ y) 0) u (closure (posSet u U) ∩ U) x →
        0 ≤ Δ φ x ∨ (φ x = 0 ∧ Q x ≤ ‖∇ φ x‖)

/-- **Abedin–Feldman–Stinson, Definition 2.1(iii).** Viscosity solution: both a viscosity super-
and subsolution. -/
def IsViscSolution (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  IsViscSuper U Q u ∧ IsViscSub U Q u

/-! ### Smooth strict sub/supersolutions -/

/-- **Abedin–Feldman–Stinson, Definition 2.2**, with `g ∈ C²(ℝᵈ)` instead of `C²(Ū)`. `g` is a
smooth strict subsolution: there are `a₀, δ₀ > 0` with (i) `Δg ≥ 0` in `{g > -a₀}` and
(ii) `|∇g|² ≥ (1 + δ₀) Q²` on `{|g| ≤ a₀}` (both sets taken inside `Ū`, the domain of `g`). -/
def IsStrictSub (U : Set (E d)) (Q g : E d → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ ∃ a₀ > 0, ∃ δ₀ > 0,
    (∀ x ∈ closure U, -a₀ < g x → 0 ≤ Δ g x) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → (1 + δ₀) * Q x ^ 2 ≤ ‖∇ g x‖ ^ 2

/-- **Abedin–Feldman–Stinson, Definition 2.2**, with `g ∈ C²(ℝᵈ)`. `g` is a smooth strict
supersolution: there are `a₀, δ₀ > 0` with (i) `Δg ≤ 0` in `{g > -a₀}` and
(ii) `|∇g|² ≤ (1 - δ₀) Q²` on `{|g| ≤ a₀}` (both sets taken inside `Ū`). -/
def IsStrictSuper (U : Set (E d)) (Q g : E d → ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ ∃ a₀ > 0, ∃ δ₀ > 0,
    (∀ x ∈ closure U, -a₀ < g x → Δ g x ≤ 0) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → ‖∇ g x‖ ^ 2 ≤ (1 - δ₀) * Q x ^ 2

/-- `g` is a smooth strict subsolution (Abedin–Feldman–Stinson, Definition 2.2) with the explicit
constants `a₀, δ₀`. -/
def IsStrictSubWith (U : Set (E d)) (Q g : E d → ℝ) (a₀ δ₀ : ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ 0 < a₀ ∧ 0 < δ₀ ∧
    (∀ x ∈ closure U, -a₀ < g x → 0 ≤ Δ g x) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → (1 + δ₀) * Q x ^ 2 ≤ ‖∇ g x‖ ^ 2

/-- `g` is a smooth strict supersolution (Abedin–Feldman–Stinson, Definition 2.2) with the explicit
constants `a₀, δ₀`. -/
def IsStrictSuperWith (U : Set (E d)) (Q g : E d → ℝ) (a₀ δ₀ : ℝ) : Prop :=
  ContDiff ℝ 2 g ∧ 0 < a₀ ∧ 0 < δ₀ ∧
    (∀ x ∈ closure U, -a₀ < g x → Δ g x ≤ 0) ∧
    ∀ x ∈ closure U, |g x| ≤ a₀ → ‖∇ g x‖ ^ 2 ≤ (1 - δ₀) * Q x ^ 2

/-! ### Relaxed subsolutions -/

/-- **Abedin–Feldman–Stinson, Definition 2.3**, with globally smooth test functions. For `u ∈ C(U)`,
`u ≥ 0`, and `E` closed (in `Ū`, i.e. closed and `⊆ Ū`) containing `{u > 0}`, the pair `(u, E)` is
a relaxed subsolution: whenever a smooth `φ` touches `u` from above in `E ∩ U` at `x`, either
`Δφ(x) ≥ 0`, or `φ(x) = 0` and `|∇φ(x)| ≥ Q(x)`. (Literal: `φ`, not `φ₊`, touches.) -/
def IsRelaxedSub (U : Set (E d)) (Q u : E d → ℝ) (Eset : Set (E d)) : Prop :=
  ContinuousOn u U ∧ (∀ x ∈ U, 0 ≤ u x) ∧ IsClosed Eset ∧ Eset ⊆ closure U ∧
    posSet u U ⊆ Eset ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x, TouchesAbove φ u (Eset ∩ U) x →
      0 ≤ Δ φ x ∨ (φ x = 0 ∧ Q x ≤ ‖∇ φ x‖)

/-- **Abedin–Feldman–Stinson, Definition 2.3.** `(u, E)` is a relaxed solution: `u` is a viscosity
supersolution and `(u, E)` is a relaxed subsolution. -/
def IsRelaxedSolution (U : Set (E d)) (Q u : E d → ℝ) (Eset : Set (E d)) : Prop :=
  IsViscSuper U Q u ∧ IsRelaxedSub U Q u Eset

/-! ### Local extremal solutions -/

/-- **Abedin–Feldman–Stinson, Definition 2.6(i).** `u` is a (local) smallest
supersolution in `U`: a viscosity supersolution such that for every ball `B ⊂⊂ U` (here
`B = ball x r`, `closedBall x r ⊆ U`) and every viscosity supersolution `v ∈ C(U)` with `v = u` on
`U \ B`, `v ≥ u` in `U`. -/
def IsLocalSmallestSuper (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  IsViscSuper U Q u ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U → ∀ v : E d → ℝ, IsViscSuper U Q v →
      (∀ y ∈ U \ ball x r, v y = u y) → ∀ y ∈ U, u y ≤ v y

/-- **Abedin–Feldman–Stinson, Definition 2.6(ii).** `u` is a (local) largest
subsolution in `U`: a viscosity subsolution such that for every ball `B ⊂⊂ U` and every viscosity
subsolution `v ∈ C(U)` with `v = u` on `U \ B`, `v ≤ u` in `U`. -/
def IsLocalLargestSub (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  IsViscSub U Q u ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U → ∀ v : E d → ℝ, IsViscSub U Q v →
      (∀ y ∈ U \ ball x r, v y = u y) → ∀ y ∈ U, v y ≤ u y

/-! ### Viscosity sub/superharmonicity -/

/-- `u` is viscosity subharmonic on `Ω`: whenever a smooth `φ` touches `u`
from above in `Ω` at `x ∈ Ω` (non-strict, relative to `Ω`), `Δφ(x) ≥ 0`. No continuity of `u` is
built in; theorems assume it where needed. For open `Ω`, touching relative to `Ω` is touching on a
full neighbourhood. -/
def IsViscSubharmonicOn (u : E d → ℝ) (Ω : Set (E d)) : Prop :=
  ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x ∈ Ω, TouchesAbove φ u Ω x → 0 ≤ Δ φ x

/-- `u` is viscosity superharmonic on `Ω`: whenever a smooth `φ` touches `u`
from below in `Ω` at `x ∈ Ω`, `Δφ(x) ≤ 0`. -/
def IsViscSuperharmonicOn (u : E d → ℝ) (Ω : Set (E d)) : Prop :=
  ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x ∈ Ω, TouchesBelow φ u Ω x → Δ φ x ≤ 0

end EllipticBernoulli
