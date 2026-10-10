/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Regularity

/-!
# Headline statement: smooth one-sided charts at flat free-boundary points

`FlatChartStatement`: at a free-boundary point `x₀` of a continuous, non-negative local minimizer
of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` whose blow-up along some sequence of scales is the half-plane
solution `(y · e)₊`, the minimizer is, near `x₀`, the positive part of a `C^∞` function `F` with
non-vanishing gradient, harmonic where it is positive, with `|∇F| = 1` on `{F = 0}`.

The route is the classical one. Flatness at a small scale (from the blow-up and non-degeneracy)
gives a `C^{1,γ}` free boundary (De Silva (2011)); the partial hodograph transform of
Kinderlehrer–Nirenberg (1977) turns the free boundary problem into a quasilinear conormal problem
on a half ball, whose solutions are `C^∞` up to the flat boundary; a Seeley extension (Seeley
(1964)) and the inverse function theorem then give `F`.

The coefficient is `Q ≡ 1` (a variable `Q` makes the hodograph equation depend on the point).

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*, Proc. Amer. Math. Soc. 15
  (1964), 625–626.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace EllipticBernoulli

/-- **Smooth one-sided chart at a flat free-boundary point** (Kinderlehrer–Nirenberg (1977), with
De Silva (2011) for the `C^{1,γ}` step). Let `d ≥ 2`, `U ⊆ ℝᵈ` open, and `u` continuous and
non-negative on `U`, a local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` in `U`. Let `x₀` be a
free-boundary point at which `(y · e)₊` is a blow-up limit, for a unit vector `e`. Then for some
`ρ > 0` with `B_ρ(x₀) ⊆ U` there is `F ∈ C^∞(B_ρ(x₀))` with
* `u = max(F, 0)` on `B_ρ(x₀)`;
* `∇F ≠ 0` on `B_ρ(x₀)`, and `|∇F| = 1` on `{F = 0} ∩ B_ρ(x₀)`;
* `ΔF = 0` on `{F > 0} ∩ B_ρ(x₀)`;
* `{F > 0} ∩ B_ρ(x₀)` is preconnected.

The minimality is local (`IsLocalEnergyMinimizer`, energies compared on balls `B ⋐ U`) and the
coefficient is `Q ≡ 1`. -/
def FlatChartStatement : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d}, IsOpen U →
    ContinuousOn u U → (∀ x ∈ U, 0 ≤ u x) → IsLocalEnergyMinimizer U (fun _ ↦ 1) u →
    x₀ ∈ freeBoundary u U → ‖e‖ = 1 → IsBlowupLimit u x₀ (fun y ↦ max (inner ℝ y e) 0) →
    ∃ ρ > 0, ball x₀ ρ ⊆ U ∧ ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ) ∧
      (∀ x ∈ ball x₀ ρ, u x = max (F x) 0) ∧ (∀ x ∈ ball x₀ ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ, F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ ball x₀ ρ, 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ | 0 < F x}

end EllipticBernoulli
