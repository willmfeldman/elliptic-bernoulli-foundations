/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Hodograph
public import EllipticBernoulli.Hodograph.Boundary
public import EllipticBernoulli.Hodograph.Equation
public import EllipticBernoulli.Hodograph.Inverse
public import EllipticBernoulli.Hodograph.Seeley

/-!
# Smooth one-sided charts at flat free-boundary points

`flat_chart : FlatChartStatement`, assembled from:
1. `exists_isFlatChartData` (`Hodograph/Flat.lean`): flat blow-up gives the hodograph data.
2. `IsFlatChartData.exists_hodograph` (`Hodograph/Equation.lean`): the partial hodograph transform
   `w` is `C¹` up to the flat boundary of a half ball, `C²` inside, `|∇w - e|` small, and solves
   `div Φ(∇w) = 0` with the conormal condition `Φ(∇w) · e = 0`.
3. `hodograph_regularity` (`Hodograph/Boundary.lean`): boundary regularity for the quasilinear
   conormal problem (`w ∈ C^∞` up to the flat boundary).
4. `exists_contDiffOn_extension_halfSpace` (`Hodograph/Seeley.lean`): a `C^∞` function on a
   closed half ball extends to a `C^∞` function on a ball (Seeley (1964)).
5. `IsFlatChartData.exists_chart_of_smooth` (`Hodograph/Inverse.lean`): inversion of the
   extended transform and the properties of `F`.

`chart_of_flat_blowup_univ` is the specialization `U = univ`.

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*, Proc. Amer. Math. Soc. 15
  (1964), 625–626.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

public section

namespace EllipticBernoulli

open Hodograph

variable {d : ℕ}

/-- **Smooth one-sided chart at a flat free-boundary point** (`FlatChartStatement`). -/
theorem flat_chart : FlatChartStatement := by
  intro d hd U u x₀ e hU hc hnn hmin hx₀ he hblow
  obtain ⟨ρ, G, H⟩ := exists_isFlatChartData hd hU hc hnn hmin hx₀ he hblow
  obtain ⟨η, hη, hreg⟩ := hodograph_regularity (d := d)
  obtain ⟨r, hr, hA, h1, h2, hgrad, hdiv, hbc, hw0, hg0⟩ := H.exists_hodograph hη
  have hsmooth := hreg he hr h1 h2 hgrad hdiv hbc
  obtain ⟨W, hW, hWw⟩ := exists_contDiffOn_extension_halfSpace (x := 0) he (by simp)
    (by positivity : 0 < r / 2) hsmooth
  have hr4 : r / 2 / 2 = r / 4 := by ring
  rw [hr4] at hW hWw
  exact H.exists_chart_of_smooth hr hA hbc hw0 hg0 hW hWw

/-- **Smooth one-sided chart at a flat free-boundary point**, on the whole space. -/
theorem chart_of_flat_blowup_univ {d : ℕ} (hd : 2 ≤ d) {u : E d → ℝ} (hc : Continuous u)
    (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u)
    {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u Set.univ) {e : E d} (he : ‖e‖ = 1)
    (hU₀ : IsBlowupLimit u x₀ (fun y ↦ max (inner ℝ y e) 0)) :
    ∃ ρ > 0, ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ) ∧
      (∀ x ∈ ball x₀ ρ, u x = max (F x) 0) ∧
      (∀ x ∈ ball x₀ ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ, F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball x₀ ρ, 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ | 0 < F x} := by
  obtain ⟨ρ, hρ, -, F, hF⟩ := flat_chart hd isOpen_univ hc.continuousOn (fun x _ ↦ hnn x) hmin
    hx₀ he hU₀
  exact ⟨ρ, hρ, F, hF⟩

end EllipticBernoulli
