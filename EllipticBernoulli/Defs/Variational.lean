/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Variational notions for the one-phase problem

* Inner variational solutions (Abedin–Feldman–Stinson, Definition 2.8).
* Upward/downward minimizers (Abedin–Feldman–Stinson, Definition 2.11).
* Obstacle minimizers with a pointwise constraint set `K : E d → Set ℝ`, and local energy
  minimizers.

## Obstacle encoding

The constraint of an obstacle problem is a pointwise constraint set `K y ⊆ ℝ`: `Icc 0 (u y)` is
the two-sided problem `0 ≤ v ≤ u` of Abedin–Feldman–Stinson, (6.1), `Ici (u y)` the one-sided
problem `u ≤ v` of (6.3), `univ` the unconstrained problem, and `Icc (ψ₁ y) (ψ₂ y)` the general
two-sided problem. Closedness (`∀ y, IsClosed (K y)`) and order-convexity
(`∀ y, (K y).OrdConnected`) are theorem hypotheses, not fields of the definition.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian NNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Inner variational solutions -/

/-- The integrand of the inner variation identity (Abedin–Feldman–Stinson, (2.5)):
`(|∇u|² + Q²χ) div ξ - 2 ∇u · Dξ ∇u + ∇(Q²) · ξ χ`.
Gradients are pointwise (`0` where not differentiable); for locally Lipschitz `u`, Lipschitz
`Q` and `ξ` they agree a.e. with the weak ones (Rademacher). -/
noncomputable def innerVarIntegrand (Q u χ : E d → ℝ) (ξ : E d → E d) (x : E d) : ℝ :=
  (‖∇ u x‖ ^ 2 + Q x ^ 2 * χ x) * divergence ξ x
    - 2 * inner ℝ (∇ u x) (fderiv ℝ ξ x (∇ u x))
    + fderiv ℝ (fun y ↦ Q y ^ 2) x (ξ x) * χ x

/-- **Abedin–Feldman–Stinson, Definition 2.8.** `(u, χ)` is an inner variational solution of (1.1)
in the open set `U`:
(i) `u ≥ 0`, `u ∈ C^{0,1}_loc(U) ∩ C²({u > 0})` and `Δu = 0` in `{u > 0}`;
(ii) `χ` is Borel measurable with values in `{0, 1}` on `U`;
(iii) `1_{u > 0} ≤ χ` a.e. on `U`;
(iv) the inner variation identity (2.5) holds for every `ξ ∈ C^{0,1}_c(U; ℝᵈ)`.

Since `u` is locally Lipschitz, `ξ` Lipschitz with compact support, `χ` bounded measurable and
`Q` Lipschitz, the integrand of (iv) is bounded, measurable and compactly supported in `U`, so the
Bochner integral in (iv) is a genuine Lebesgue integral. -/
structure IsInnerVarSolution (U : Set (E d)) (Q u χ : E d → ℝ) : Prop where
  nonneg : ∀ x ∈ U, 0 ≤ u x
  locLip : LocallyLipschitzOn U u
  c2 : ContDiffOn ℝ 2 u (posSet u U)
  harmonic : ∀ x ∈ posSet u U, Δ u x = 0
  meas : Measurable χ
  zero_one : ∀ x ∈ U, χ x = 0 ∨ χ x = 1
  pos_le : ∀ᵐ x ∂(volume.restrict U), 0 < u x → χ x = 1
  stationary : ∀ ξ : E d → E d, (∃ K, LipschitzWith K ξ) → HasCompactSupport ξ →
    tsupport ξ ⊆ U → ∫ x in U, innerVarIntegrand Q u χ ξ x = 0

/-! ### Directional minimizers -/

/-- **Abedin–Feldman–Stinson, Definition 2.11**, downward case. The paper uses `H¹(U)` and compares
energies on `U`; here competitors are in `H¹_loc(U)` and energies are compared on the ball `B`
only, the boundary condition `u - v ∈ H¹₀(B)` is encoded as `v = u` a.e. on `U \ B`, and weak
gradients are carried as data.
(i) `{u > 0}` is open and `u` is harmonic (classically: `C²` with `Δu = 0`) in `{u > 0}`;
(ii) for every ball `B = ball x r ⊂⊂ U` and every `v ∈ H¹_loc(U)` with `v ≤ u` a.e. and `v = u`
a.e. on `U \ B`, `J_Q(u; B) ≤ J_Q(v; B)`. -/
def IsDownwardMinimizer (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  (∃ G, MemH1Loc U u G) ∧ IsOpen (posSet u U) ∧ ContDiffOn ℝ 2 u (posSet u U) ∧
    (∀ x ∈ posSet u U, Δ u x = 0) ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
      ∀ (Gu : E d → E d) (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U u Gu → MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict U), v y ≤ u y) →
        (∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) →
        energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv

/-- **Abedin–Feldman–Stinson, Definition 2.11**, upward case; same encoding as
`IsDownwardMinimizer`, with competitors `v ≥ u` a.e. -/
def IsUpwardMinimizer (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  (∃ G, MemH1Loc U u G) ∧ IsOpen (posSet u U) ∧ ContDiffOn ℝ 2 u (posSet u U) ∧
    (∀ x ∈ posSet u U, Δ u x = 0) ∧
    ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
      ∀ (Gu : E d → E d) (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U u Gu → MemH1Loc U v Gv →
        (∀ᵐ y ∂(volume.restrict U), u y ≤ v y) →
        (∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) →
        energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv

/-! ### Obstacle and local energy minimizers -/

/-- `w` (with weak gradient `Gw`) minimizes `J_Q(·; B)` among `H¹_loc(U)`
competitors that agree with `u` a.e. off `B` and satisfy the pointwise constraint `v y ∈ K y` a.e.
on `U`. The minimizer itself satisfies both conditions *pointwise* (a good representative).

The boundary condition `w - u ∈ H¹₀(B)` is encoded as `v = u` a.e. on `U \ B`, and energies are
compared on `B` only. With `K = fun y ↦ Icc 0 (u y)` (resp. `Ici (u y)`) this is the obstacle
problem (6.1) (resp. (6.3)) of Abedin–Feldman–Stinson. -/
def IsObstacleMinimizer (U B : Set (E d)) (Q u : E d → ℝ) (K : E d → Set ℝ)
    (w : E d → ℝ) (Gw : E d → E d) : Prop :=
  MemH1Loc U w Gw ∧ (∀ y ∈ U \ B, w y = u y) ∧ (∀ y ∈ U, w y ∈ K y) ∧
    ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ B)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), v y ∈ K y) →
      energyJ B Q w Gw ≤ energyJ B Q v Gv

/-- `u` is a local minimizer of `J_Q` in `U`: for some weak gradient `Gu`,
`u ∈ H¹_loc(U)` and, on every ball `B = ball x r` with `closedBall x r ⊆ U`, `u` minimizes
`J_Q(·; B)` among unconstrained competitors agreeing with `u` a.e. off `B`. -/
def IsLocalEnergyMinimizer (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  ∃ Gu, MemH1Loc U u Gu ∧ ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
    IsObstacleMinimizer U (ball x r) Q u (fun _ ↦ Set.univ) u Gu

end EllipticBernoulli
