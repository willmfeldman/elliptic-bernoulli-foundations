import Challenge.Setting
import Challenge.Sobolev
import Challenge.Touching
import Challenge.Viscosity
import Challenge.Regularity
import Challenge.Variational
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Average

/-!
# Challenge: non-degeneracy

Trusted statement surface for the non-degeneracy results of the one-phase problem, in
quantitative form: every constant depends only on the data (`d`, `q₀`, and the Lipschitz
constant `K` in the planar case), never on the solution.

* Local smallest viscosity supersolutions (Caffarelli–Salsa, Lemma 6.9):
  `sup_{B̄_r(z)} u ≥ q₀ r / (8d)` on every closed ball `B̄_r(z) ⊆ U` centred in
  `\overline{{u > 0}}`.
* The exterior-ball lemma (Abedin–Feldman–Stinson, Lemma B.2), with domain and exterior ball of the
  same radius `s`: `sup_{B_s(x₀)} v ≥ q₀ s / (128 d e^{3d})`.
* The equivalence of the sphere-average and sphere-sup forms of non-degeneracy
  (Abedin–Feldman–Stinson, Lemma B.3 (i)⇔(ii)). Sphere averages are written with Mathlib's
  polar-decomposition measure `(volume : Measure (E d)).toSphere`.
* Downward minimizers (Alt–Caffarelli, Lemma 3.4): `sup_{B̄_r(z)} u ≥ q₀ r / (8 d e^{d/2})` on the
  same balls.
* Local largest subsolutions in `d = 2` (Abedin–Feldman–Stinson, Theorem B.1, after Orcan-Ekmekci):
  for `u` that is `K`-Lipschitz, `C²` and harmonic in `{u > 0}` (hypotheses Abedin–Feldman–Stinson
  do not state), `sup_{B̄_r(x₀)} u ≥ c r` for `r ≤ R/2`, with `c = c(q₀, K)`.

The project vocabulary is restated in `Challenge/*.lean`, one file per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Basic/Touching.lean`, `Defs/Viscosity.lean`,
`Defs/Regularity.lean`, `Defs/Variational.lean`), with the library's names, definitions and
order. Every file imports Mathlib modules only (the same ones as the library file it restates).

## References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
* B. Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary
  problem in ℝ²: elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3–4,
  937–962.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Laplacian NNReal

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: a local smallest supersolution with `Q ≥ q₀ > 0` satisfies
`sup_{B̄_r(z)} u ≥ q₀ r / (8d)` for every `z ∈ \overline{{u > 0}}` and every `B̄_r(z) ⊆ U`
(Caffarelli–Salsa, Lemma 6.9). -/
theorem challenge_isLocalSmallestSuper_exists_le_of_closedBall_subset {U : Set (E d)}
    {Q u : E d → ℝ} {q₀ : ℝ} (hd : 1 ≤ d) (hU : IsOpen U) (hu : IsLocalSmallestSuper U Q u)
    (hq₀ : 0 < q₀) (hQ : ∀ y ∈ U, q₀ ≤ Q y) :
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, q₀ / (8 * d) * r ≤ u y := by
  sorry

/-- Challenge: the exterior-ball lemma with domain and exterior ball of the same radius
(Abedin–Feldman–Stinson, Lemma B.2). -/
theorem challenge_exists_le_of_exteriorBall_sameRadius (hd : 1 ≤ d) {Q v : E d → ℝ}
    {x₀ p : E d} {s q₀ : ℝ} (hs : 0 < s) (hq₀ : 0 < q₀) (hv : IsViscSub (ball x₀ s) Q v)
    (hQ : ∀ y ∈ ball x₀ s, q₀ ≤ Q y) (hx₀ : x₀ ∈ freeBoundary v (ball x₀ s))
    (hp : ‖x₀ - p‖ = s) (hball : ∀ y ∈ ball p s ∩ ball x₀ s, v y = 0) :
    ∃ y ∈ ball x₀ s, q₀ / (128 * d * Real.exp (3 * d)) * s ≤ v y := by
  sorry

/-- Challenge: sphere-average and sphere-sup non-degeneracy are equivalent for Lipschitz
functions harmonic in `{u > 0}` (Abedin–Feldman–Stinson, Lemma B.3 (i)⇔(ii)). -/
theorem challenge_nondegenerate_sup_iff_average (hd : 1 ≤ d) (L : ℝ≥0) (c : ℝ) (hc : 0 < c) :
    ∃ c' > 0, ∀ (u : E d → ℝ) (x₀ : E d),
      (∀ y ∈ ball x₀ 1, 0 ≤ u y) → LipschitzOnWith L u (ball x₀ 1) →
      HarmonicOnNhd u (posSet u (ball x₀ 1)) → x₀ ∈ freeBoundary u (ball x₀ 1) →
      ((∀ r ∈ Ioo (0 : ℝ) 1,
          c * r ≤ ⨍ z, u (x₀ + r • (z : E d)) ∂(volume : Measure (E d)).toSphere) →
        ∀ r ∈ Ioo (0 : ℝ) 1, ∃ y ∈ sphere x₀ r, c' * r ≤ u y) ∧
      ((∀ r ∈ Ioo (0 : ℝ) 1, ∃ y ∈ sphere x₀ r, c * r ≤ u y) →
        ∀ r ∈ Ioo (0 : ℝ) 1,
          c' * r ≤ ⨍ z, u (x₀ + r • (z : E d)) ∂(volume : Measure (E d)).toSphere) := by
  sorry

/-- Challenge: a locally Lipschitz downward minimizer `u ≥ 0` with `0 < q₀ ≤ Q ≤ C` satisfies
`sup_{B̄_r(z)} u ≥ q₀ r / (8 d e^{d/2})` for every `z ∈ \overline{{u > 0}}` and every
`B̄_r(z) ⊆ U` (Alt–Caffarelli, Lemma 3.4). -/
theorem challenge_isDownwardMinimizer_exists_le_of_closedBall_subset {U : Set (E d)}
    {Q u : E d → ℝ} {q₀ : ℝ} (hd : 1 ≤ d) (hU : IsOpen U) (hu : IsDownwardMinimizer U Q u)
    (hlip : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y) (hq₀ : 0 < q₀)
    (hQ : ∀ y ∈ U, q₀ ≤ Q y) (hQb : ∃ C, ∀ y ∈ U, Q y ≤ C) (hQm : Measurable Q) :
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, q₀ / (8 * d * Real.exp ((d : ℝ) / 2)) * r ≤ u y := by
  sorry

/-- Challenge: non-degeneracy of local largest subsolutions in `d = 2` with a constant depending
only on `q₀` and `K` (Abedin–Feldman–Stinson, Theorem B.1, after Orcan-Ekmekci), for `u`
`K`-Lipschitz, `C²` and harmonic in `{u > 0}`. -/
theorem challenge_exists_pos_le_of_isLocalLargestSub (q₀ : ℝ) (K : ℝ≥0) (hq₀ : 0 < q₀) :
    ∃ c > 0, ∀ {Q u : E 2 → ℝ} {x₀ : E 2} {R : ℝ}, 0 < R →
      (∀ y ∈ ball x₀ R, q₀ ≤ Q y) → IsLocalLargestSub (ball x₀ R) Q u →
      LipschitzOnWith K u (ball x₀ R) → ContDiffOn ℝ 2 u (posSet u (ball x₀ R)) →
      (∀ y ∈ posSet u (ball x₀ R), Δ u y = 0) → x₀ ∈ freeBoundary u (ball x₀ R) →
      ∀ r, 0 < r → r ≤ R / 2 → ∃ y ∈ closedBall x₀ r, c * r ≤ u y := by
  sorry

end EllipticBernoulli
