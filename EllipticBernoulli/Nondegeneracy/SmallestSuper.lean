/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Nondegeneracy
import EllipticBernoulli.Nondegeneracy.Barriers
import EllipticBernoulli.Viscosity.Lattice
import EllipticBernoulli.Viscosity.Local

/-!
# Non-degeneracy of local smallest supersolutions (Caffarelli–Salsa, Lemma 6.9)

`IsLocalSmallestSuper.exists_le_of_closedBall_subset` (`SmallestSuperNondegQuantStatement`): if
`u` is a local smallest supersolution in the open set `U` and `Q ≥ q₀ > 0` on `U`, then
`sup_{B̄_r(z)} u ≥ q₀ r/(8d)` for every `z ∈ \overline{{u > 0}}` and every ball `B̄_r(z) ⊆ U`.

`IsLocalSmallestSuper.isUniformlyNondegenerateNear` (`SmallestSuperNondegStatement`): if `u` is a
local smallest supersolution in the open set `U` and `Q ≥ q₀ > 0` on `U`, then near every free
boundary point `x₀` the function `u` is uniformly non-degenerate, with the explicit constants
`c = q₀ / (8d)` and `ρ = R/4`, where `B_R(x₀) ⊆ U`:
for every `z ∈ \overline{{u > 0}} ∩ B_{R/4}(x₀)` and `0 < r ≤ R/4`, `sup_{B̄_r(z)} u ≥ q₀ r/(8d)`.

## Proof

If `u < c r` on `B̄_r(z)`, replace `u` in `B_r(z)` by `min(u, w)`, where
`w = nondegBarrier z (r/2) (q₀ r/(2d))` is the radial supersolution vanishing on `B̄_{r/2}(z)`
(`isViscSuper_nondegBarrier`, `IsViscSuper.min`). Off `B̄_{3r/4}(z)` one has `w ≥ 5A/13 > c r > u`
(`le_nondegProfile`), so the replacement agrees with `u` near `∂B_r(z)` and the glued function is a
supersolution in `U` (`isViscSuper_piecewise`). Minimality gives `u ≤ min(u, w)`, hence `u = 0` on
`B_{r/2}(z)`, contradicting `z ∈ \overline{{u > 0}}`.

The free-boundary hypothesis on `x₀` is used only through `x₀ ∈ U`.

## References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud.
  Math. 68, Amer. Math. Soc., 2005.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Local smallest supersolutions are non-degenerate on every ball**
(`SmallestSuperNondegQuantStatement`; Caffarelli–Salsa, Lemma 6.9). For
`z ∈ \overline{{u > 0}}` and `B̄_r(z) ⊆ U`, `sup_{B̄_r(z)} u ≥ q₀ r / (8d)`. Assumes `1 ≤ d`. -/
theorem IsLocalSmallestSuper.exists_le_of_closedBall_subset :
    SmallestSuperNondegQuantStatement := by
  classical
  intro d U Q u q₀ hd hU hls hq₀ hQ z hzcl r hr hball
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set σ := r / 2 with hσ_def
  have hσ : 0 < σ := by positivity
  set A := q₀ * σ / d with hA_def
  have hA : 0 < A := by positivity
  have hWsub : ball z r ⊆ U := ball_subset_closedBall.trans hball
  have hbar : IsViscSuper (ball z r) Q (nondegBarrier z σ A) := by
    refine isViscSuper_nondegBarrier isOpen_ball hA hσ hd fun x hx ↦ ?_
    have : A * d / σ = q₀ := by rw [hA_def]; field_simp
    rw [this]
    exact hQ x (hWsub hx)
  have hmin : IsViscSuper (ball z r) Q (fun y ↦ min (u y) (nondegBarrier z σ A y)) :=
    IsViscSuper.min (hls.1.mono isOpen_ball hWsub) hbar
  have heq : ∀ y ∈ ball z r \ closedBall z (3 * r / 4),
      min (u y) (nondegBarrier z σ A y) = u y := by
    rintro y ⟨hy1, hy2⟩
    rw [mem_closedBall, not_le, dist_eq_norm] at hy2
    refine min_eq_left ((hcon y (ball_subset_closedBall hy1)).le.trans ?_)
    have h1 := le_nondegProfile (z := z) hA.le hσ hd (y := y) (by rw [hσ_def]; linarith)
    refine le_trans ?_ (h1.trans (le_max_left _ _))
    rw [hA_def, hσ_def]
    have hX : 0 < q₀ * r / d := by positivity
    have e1 : q₀ / (8 * d) * r = (q₀ * r / d) / 8 := by field_simp
    have e2 : 5 * (q₀ * (r / 2) / d) / 13 = 5 * (q₀ * r / d) / 26 := by
      field_simp; ring
    rw [e1, e2]; linarith
  have hK : closedBall z (3 * r / 4) ⊆ ball z r := closedBall_subset_ball (by linarith)
  have hv := isViscSuper_piecewise hU isOpen_ball hWsub isClosed_closedBall hK hls.1 hmin heq
  have hcomp := hls.2 z r hr hball _ hv fun y hy ↦ piecewise_eq_of_notMem _ _ _ hy.2
  -- `u` vanishes on `B_σ(z)`, contradicting `z ∈ \overline{{u > 0}}`
  obtain ⟨y, hyσ, hyU, hypos⟩ := mem_closure_iff_nhds.1 hzcl (ball z σ) (ball_mem_nhds z hσ)
  have hyr : y ∈ ball z r := ball_subset_ball (by linarith) hyσ
  have h1 := hcomp y (hWsub hyr)
  rw [piecewise_eq_of_mem _ _ _ hyr] at h1
  have h2 : nondegBarrier z σ A y = 0 :=
    nondegBarrier_eq_zero hA hσ hd (by rw [← dist_eq_norm]; exact (mem_ball.1 hyσ).le)
  have h3 := h1.trans ((min_le_right _ _).trans h2.le)
  exact absurd hypos (not_lt.2 h3)

/-- **Local smallest supersolutions are uniformly non-degenerate** (`SmallestSuperNondegStatement`;
Caffarelli–Salsa, Lemma 6.9).
Constants: `c = q₀ / (8d)`, `ρ = R/4` for any `R > 0` with `B_R(x₀) ⊆ U`. Assumes `1 ≤ d`.
Derived from `IsLocalSmallestSuper.exists_le_of_closedBall_subset`. -/
theorem IsLocalSmallestSuper.isUniformlyNondegenerateNear : SmallestSuperNondegStatement := by
  intro d U Q u x₀ hd hU hls hQ hx₀
  obtain ⟨q₀, hq₀, hQ⟩ := hQ
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀.2
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨q₀ / (8 * d), by positivity, R / 4, by positivity, ?_⟩
  rintro z ⟨hzcl, hzB⟩ r hr hrρ
  rw [mem_ball] at hzB
  refine IsLocalSmallestSuper.exists_le_of_closedBall_subset hd hU hls hq₀ hQ z hzcl r hr
    fun y hy ↦ hRU ?_
  rw [mem_closedBall] at hy
  rw [mem_ball]
  linarith [dist_triangle y z x₀]

end EllipticBernoulli
