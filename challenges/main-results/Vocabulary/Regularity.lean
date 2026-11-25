/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Vocabulary.Setting
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.MetricSpace.Holder
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Regularity notions near the free boundary

* Blow-ups and classical regularity near a free boundary point (Abedin–Feldman–Stinson,
  Theorem 1.1 and Corollary 1.2): `blowup`, `IsBlowupLimit`, `IsC1GammaHypersurfaceNear`,
  `IsClassicalNear`.
* Non-degeneracy (Abedin–Feldman–Stinson, Appendix B): `IsNondegenerateAt`,
  `IsUniformlyNondegenerateNear`.
* Classical solutions with variable coefficient `Q`: `IsClassicalSolution`, the classical
  solutions of Kriventsov–Weiss, Definition 9.1 (numbering of arXiv:2306.10131v2), with the
  constant `1` replaced by `Q x`.

The constants in these predicates (`c` and `ρ`; `γ`, the Hölder constant and the radius) are
existential for each function, so the predicates carry no uniformity across families of solutions,
while the sources' constants depend only on the data. The quantitative non-degeneracy statements
recover data-only constants.

Challenge vocabulary: a Mathlib-only restatement of the library file
`EllipticBernoulli/Defs/Regularity.lean`, with its theorems dropped. The definitions are verbatim and in the
library order, so Comparator can check that they are the library's definitions.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian NNReal

noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Blow-ups and classical regularity -/

/-- The blow-up `u_{x₀,r}(y) = r⁻¹ u(x₀ + r y)` (Abedin–Feldman–Stinson, proof sketch of
Corollary 1.2, and Corollary 2.13). -/
noncomputable def blowup (u : E d → ℝ) (x₀ : E d) (r : ℝ) (y : E d) : ℝ :=
  u (x₀ + r • y) / r

/-- `v` is a (subsequential) blow-up limit of `u` at `x₀`: `u_{x₀,r_n} → v` locally uniformly on
`ℝᵈ` along some sequence `r_n → 0⁺` (Abedin–Feldman–Stinson, proof sketch of Corollary 1.2). -/
def IsBlowupLimit (u : E d → ℝ) (x₀ : E d) (v : E d → ℝ) : Prop :=
  ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Tendsto r atTop (𝓝 0) ∧
    TendstoLocallyUniformly (fun n ↦ blowup u x₀ (r n)) v atTop

/-- `S` is a `C^{1,γ}` hypersurface in `ball x₀ r` (Abedin–Feldman–Stinson, Corollary 1.2(i),
footnote):
for some `γ ∈ (0, 1]`, unit vector `e` and `f ∈ C¹` with `γ`-Hölder derivative, `S ∩ ball x₀ r` is
the graph `{y : (y - x₀) · e = f(P(y - x₀))}` over the hyperplane `e^⊥`, where
`P z = z - (z · e) e` is the orthogonal projection onto `e^⊥`. -/
def IsC1GammaHypersurfaceNear (S : Set (E d)) (x₀ : E d) (r : ℝ) : Prop :=
  ∃ γ : ℝ≥0, 0 < γ ∧ γ ≤ 1 ∧ ∃ e : E d, ‖e‖ = 1 ∧ ∃ (f : E d → ℝ) (C : ℝ≥0),
    ContDiff ℝ 1 f ∧ HolderWith C γ (fderiv ℝ f) ∧
    S ∩ ball x₀ r =
      {y ∈ ball x₀ r | inner ℝ (y - x₀) e = f (y - x₀ - inner ℝ (y - x₀) e • e)}

/-- `u` is a classical solution of (1.1) near the free boundary point `x₀` (Abedin–Feldman–Stinson,
Corollary 1.2(i) and its footnote): for some `r > 0` with `ball x₀ r ⊆ U`,
* the free boundary `∂{u > 0} ∩ U` is a `C^{1,γ}` hypersurface in `ball x₀ r`;
* `u` is `C²` and harmonic in `{u > 0} ∩ ball x₀ r`;
* `∇u` extends continuously (as `G`) to `\overline{{u > 0}} ∩ ball x₀ r` and the free boundary
  condition `|∇u| = Q` holds classically on `∂{u > 0} ∩ ball x₀ r`. -/
def IsClassicalNear (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) : Prop :=
  ∃ r > 0, ball x₀ r ⊆ U ∧ IsC1GammaHypersurfaceNear (freeBoundary u U) x₀ r ∧
    ContDiffOn ℝ 2 u (posSet u U ∩ ball x₀ r) ∧ (∀ y ∈ posSet u U ∩ ball x₀ r, Δ u y = 0) ∧
    ∃ G : E d → E d, ContinuousOn G (closure (posSet u U) ∩ ball x₀ r) ∧
      (∀ y ∈ posSet u U ∩ ball x₀ r, G y = ∇ u y) ∧
      ∀ y ∈ freeBoundary u U ∩ ball x₀ r, ‖G y‖ = Q y

/-! ### Non-degeneracy -/

/-- Non-degeneracy at `x₀` (Abedin–Feldman–Stinson, Theorem B.1, local form): there are
`c, ρ > 0` such that for `0 < r ≤ ρ`, `sup_{B̄_r(x₀)} u ≥ c r`. -/
def IsNondegenerateAt (u : E d → ℝ) (x₀ : E d) : Prop :=
  ∃ c > 0, ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ → ∃ y ∈ closedBall x₀ r, c * r ≤ u y

/-- Uniform non-degeneracy near `x₀` (Alt–Caffarelli form): there are `c, ρ > 0` such that for
every `z ∈ \overline{{u > 0}}` with `|z - x₀| < ρ` and `0 < r ≤ ρ`, `sup_{B̄_r(z)} u ≥ c r`. -/
def IsUniformlyNondegenerateNear (U : Set (E d)) (u : E d → ℝ) (x₀ : E d) : Prop :=
  ∃ c > 0, ∃ ρ > 0, ∀ z ∈ closure (posSet u U) ∩ ball x₀ ρ, ∀ r, 0 < r → r ≤ ρ →
    ∃ y ∈ closedBall z r, c * r ≤ u y

/-! ### Classical solutions with variable coefficient -/

/-- `u` is a classical solution of `Δu = 0` in `{u > 0}`, `|∇u| = Q` on the free boundary, in the
open set `U`. This is Kriventsov–Weiss, Definition 9.1, with the constant `1` replaced by `Q x`;
the free boundary is `freeBoundary u U = frontier (posSet u U) ∩ U`.

`u : U → [0, ∞)` is Lipschitz and harmonic on `{u > 0}`. Near each free boundary point `x`, the
free boundary is the zero set of a smooth `F` with `∇F(x) ≠ 0`. For each unit normal
`ν = ±∇F(x)/|∇F(x)|` with `u(x + tν) > 0` for small `t > 0`, `(u(x + tν) − u(x)) / t → Q(x)` as
`t → 0+`. Points with `{u > 0}` on both sides of the free boundary are allowed. -/
structure IsClassicalSolution (U : Set (E d)) (Q u : E d → ℝ) : Prop where
  /-- `U` is open. -/
  isOpen : IsOpen U
  /-- `u` is Lipschitz on `U`. -/
  lipschitzOnWith : ∃ L, LipschitzOnWith L u U
  /-- `u ≥ 0` on `U`. -/
  nonneg : ∀ x ∈ U, 0 ≤ u x
  /-- `u` is harmonic on `U ∩ {u > 0}`. -/
  harmonicAt : ∀ x ∈ U, 0 < u x → InnerProductSpace.HarmonicAt u x
  /-- Smooth free boundary with the free boundary condition `∂_ν u = Q` along both unit normals
  pointing into `{u > 0}`. -/
  free_boundary : ∀ x ∈ freeBoundary u U, ∃ r, 0 < r ∧ ∃ F : E d → ℝ,
    ContDiff ℝ ∞ F ∧ ∇ F x ≠ 0 ∧
    ball x r ∩ freeBoundary u U = ball x r ∩ {y | F y = 0} ∧
    ∀ s : ℝ, (s = 1 ∨ s = -1) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x)) →
      Tendsto (fun t ↦ (u (x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x) - u x) / t) (𝓝[>] 0) (𝓝 (Q x))

end EllipticBernoulli

end
