module

public import EllipticBernoulli.Nondegeneracy.SmallestSuper
public import EllipticBernoulli.Nondegeneracy.ExteriorBall
public import EllipticBernoulli.Nondegeneracy.Equivalences
public import EllipticBernoulli.Nondegeneracy.Minimizer
public import EllipticBernoulli.Nondegeneracy.LargestSub2D

/-!
# Solution: non-degeneracy

Discharges the challenge through the library modules imported above, by the library's
non-degeneracy theorems.
-/

@[expose] public noncomputable section

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Laplacian NNReal

namespace EllipticBernoulli

variable {d : ℕ}

theorem challenge_isLocalSmallestSuper_exists_le_of_closedBall_subset {U : Set (E d)}
    {Q u : E d → ℝ} {q₀ : ℝ} (hd : 1 ≤ d) (hU : IsOpen U) (hu : IsLocalSmallestSuper U Q u)
    (hq₀ : 0 < q₀) (hQ : ∀ y ∈ U, q₀ ≤ Q y) :
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, q₀ / (8 * d) * r ≤ u y :=
  IsLocalSmallestSuper.exists_le_of_closedBall_subset hd hU hu hq₀ hQ

theorem challenge_exists_le_of_exteriorBall_sameRadius (hd : 1 ≤ d) {Q v : E d → ℝ}
    {x₀ p : E d} {s q₀ : ℝ} (hs : 0 < s) (hq₀ : 0 < q₀) (hv : IsViscSub (ball x₀ s) Q v)
    (hQ : ∀ y ∈ ball x₀ s, q₀ ≤ Q y) (hx₀ : x₀ ∈ freeBoundary v (ball x₀ s))
    (hp : ‖x₀ - p‖ = s) (hball : ∀ y ∈ ball p s ∩ ball x₀ s, v y = 0) :
    ∃ y ∈ ball x₀ s, q₀ / (128 * d * Real.exp (3 * d)) * s ≤ v y :=
  exists_le_of_exteriorBall_sameRadius hd hs hq₀ hv hQ hx₀ hp hball

theorem challenge_nondegenerate_sup_iff_average (hd : 1 ≤ d) (L : ℝ≥0) (c : ℝ) (hc : 0 < c) :
    ∃ c' > 0, ∀ (u : E d → ℝ) (x₀ : E d),
      (∀ y ∈ ball x₀ 1, 0 ≤ u y) → LipschitzOnWith L u (ball x₀ 1) →
      HarmonicOnNhd u (posSet u (ball x₀ 1)) → x₀ ∈ freeBoundary u (ball x₀ 1) →
      ((∀ r ∈ Ioo (0 : ℝ) 1,
          c * r ≤ ⨍ z, u (x₀ + r • (z : E d)) ∂(volume : Measure (E d)).toSphere) →
        ∀ r ∈ Ioo (0 : ℝ) 1, ∃ y ∈ sphere x₀ r, c' * r ≤ u y) ∧
      ((∀ r ∈ Ioo (0 : ℝ) 1, ∃ y ∈ sphere x₀ r, c * r ≤ u y) →
        ∀ r ∈ Ioo (0 : ℝ) 1,
          c' * r ≤ ⨍ z, u (x₀ + r • (z : E d)) ∂(volume : Measure (E d)).toSphere) :=
  nondegenerate_sup_iff_average hd L c hc

theorem challenge_isDownwardMinimizer_exists_le_of_closedBall_subset {U : Set (E d)}
    {Q u : E d → ℝ} {q₀ : ℝ} (hd : 1 ≤ d) (hU : IsOpen U) (hu : IsDownwardMinimizer U Q u)
    (hlip : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y) (hq₀ : 0 < q₀)
    (hQ : ∀ y ∈ U, q₀ ≤ Q y) (hQb : ∃ C, ∀ y ∈ U, Q y ≤ C) (hQm : Measurable Q) :
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, q₀ / (8 * d * Real.exp ((d : ℝ) / 2)) * r ≤ u y :=
  IsDownwardMinimizer.exists_le_of_closedBall_subset hd hU hu hlip hu0 hq₀ hQ hQb hQm

theorem challenge_exists_pos_le_of_isLocalLargestSub (q₀ : ℝ) (K : ℝ≥0) (hq₀ : 0 < q₀) :
    ∃ c > 0, ∀ {Q u : E 2 → ℝ} {x₀ : E 2} {R : ℝ}, 0 < R →
      (∀ y ∈ ball x₀ R, q₀ ≤ Q y) → IsLocalLargestSub (ball x₀ R) Q u →
      LipschitzOnWith K u (ball x₀ R) → ContDiffOn ℝ 2 u (posSet u (ball x₀ R)) →
      (∀ y ∈ posSet u (ball x₀ R), Δ u y = 0) → x₀ ∈ freeBoundary u (ball x₀ R) →
      ∀ r, 0 < r → r ≤ R / 2 → ∃ y ∈ closedBall x₀ r, c * r ≤ u y :=
  exists_pos_le_of_isLocalLargestSub q₀ K hq₀

end EllipticBernoulli
