/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Regularity
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Headline statements: non-degeneracy

The theorems proving them live in `EllipticBernoulli/Nondegeneracy/*`.

* `SmallestSuperNondegStatement`: local smallest supersolutions are uniformly non-degenerate
  (Caffarelli–Salsa, Lemma 6.9).
* `ExteriorBallNondegStatement`: non-degeneracy of subsolutions at a free boundary point with an
  exterior touching ball (Abedin–Feldman–Stinson, Lemma B.2).
* `NondegEquivStatement`: Abedin–Feldman–Stinson, Lemma B.3 (i)⇔(ii) (sphere average vs. sphere
  sup).
* `DownwardNondegStatement`: downward minimizers are uniformly non-degenerate (Alt–Caffarelli,
  Lemma 3.4; Velichkov, Lemma 4.4).
* `LargestSubNondeg2DStatement`: local largest subsolutions in `d = 2` (Abedin–Feldman–Stinson,
  Theorem B.1, after Orcan-Ekmekci), for `u` that is `K`-Lipschitz, `C²` and harmonic in
  `{u > 0}`, which Abedin–Feldman–Stinson do not assume.

Quantitative forms, with constants depending only on the data and never on `u`:

* `SmallestSuperNondegQuantStatement`: `c = q₀ / (8d)` on every ball `B̄_r(z) ⊆ U` centred in
  `\overline{{u > 0}}`.
* `DownwardNondegQuantStatement`: `c = q₀ / (8d e^{d/2})`, on the same balls.
* `LargestSubNondeg2DQuantStatement`: `c = c(q₀, K)` for `r ≤ R/2`.
* `ExteriorBallSameRadiusStatement`: the exterior-ball lemma with domain and exterior ball of the
  same radius, `c = q₀ / (128 d e^{3d})`.

Sphere averages `⨍_{∂B_r(x₀)} u` are written with Mathlib's polar-decomposition measure
`(volume : Measure (E d)).toSphere` on the unit sphere (rotation invariant, hence proportional to
surface measure), as `⨍ z, u (x₀ + r • z) ∂volume.toSphere`.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* B. Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary
  problem in ℝ²: elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3–4,
  937–962.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian NNReal

@[expose] public section

namespace EllipticBernoulli

/-- **Non-degeneracy of local smallest supersolutions** (Caffarelli–Salsa, Lemma 6.9): if
`Q ≥ q₀ > 0` on `U`, a local smallest supersolution is uniformly non-degenerate near each free
boundary point. The constants are chosen per solution; see `SmallestSuperNondegQuantStatement`
for the data-only constant. Proved by `IsLocalSmallestSuper.isUniformlyNondegenerateNear`
(`Nondegeneracy/SmallestSuper.lean`). -/
def SmallestSuperNondegStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ} {x₀ : E d}, 1 ≤ d → IsOpen U →
    IsLocalSmallestSuper U Q u → (∃ q₀ > 0, ∀ y ∈ U, q₀ ≤ Q y) → x₀ ∈ freeBoundary u U →
    IsUniformlyNondegenerateNear U u x₀

/-- **Exterior-ball non-degeneracy** (Abedin–Feldman–Stinson, Lemma B.2), quantitative form: a
subsolution in `B_{4s}(x₀)` with `Q ≥ q₀ > 0` and an exterior touching ball `B_s(p)` at the free
boundary point `x₀` satisfies `sup_{B_{4s}(x₀)} v ≥ q₀ s / (32 d e^{3d})`. The paper takes domain
and exterior ball of the same radius (see `ExteriorBallSameRadiusStatement`) and gives no explicit
constant. Proved by `exists_le_of_exteriorBall` (`Nondegeneracy/ExteriorBall.lean`). -/
def ExteriorBallNondegStatement : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ {Q v : E d → ℝ} {x₀ p : E d} {s q₀ : ℝ},
    0 < s → 0 < q₀ → IsViscSub (ball x₀ (4 * s)) Q v →
    (∀ y ∈ ball x₀ (4 * s), q₀ ≤ Q y) → x₀ ∈ freeBoundary v (ball x₀ (4 * s)) →
    ‖x₀ - p‖ = s → (∀ y ∈ ball p s ∩ ball x₀ (4 * s), v y = 0) →
    ∃ y ∈ ball x₀ (4 * s), q₀ / (32 * d * Real.exp (3 * d)) * s ≤ v y

/-- **Sphere-average and sphere-sup non-degeneracy are equivalent** (Abedin–Feldman–Stinson,
Lemma B.3 (i)⇔(ii)). Let `u ≥ 0` be `L`-Lipschitz on `B_1(x₀)`, harmonic in `{u > 0}`, with `x₀` a
free boundary point. If `⨍_{∂B_r(x₀)} u ≥ c r` for all `0 < r < 1` then `sup_{∂B_r(x₀)} u ≥ c' r`
for all `0 < r < 1`, and conversely, with `c'` depending only on `c`, `d` and `L`. The paper says
the constants depend on `L` without introducing it; here `L` is the Lipschitz constant. The proof
uses neither harmonicity nor `x₀ ∈ ∂{u > 0}`. The Δ-mass form (iii) is not included (it needs the
Riesz measure of `u`). Proved by `nondegenerate_sup_iff_average`
(`Nondegeneracy/Equivalences.lean`). -/
def NondegEquivStatement : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ (L : ℝ≥0) (c : ℝ), 0 < c → ∃ c' > 0, ∀ (u : E d → ℝ) (x₀ : E d),
    (∀ y ∈ ball x₀ 1, 0 ≤ u y) → LipschitzOnWith L u (ball x₀ 1) →
    HarmonicOnNhd u (posSet u (ball x₀ 1)) → x₀ ∈ freeBoundary u (ball x₀ 1) →
    ((∀ r ∈ Ioo (0 : ℝ) 1,
        c * r ≤ ⨍ z, u (x₀ + r • (z : E d)) ∂(volume : Measure (E d)).toSphere) →
      ∀ r ∈ Ioo (0 : ℝ) 1, ∃ y ∈ sphere x₀ r, c' * r ≤ u y) ∧
    ((∀ r ∈ Ioo (0 : ℝ) 1, ∃ y ∈ sphere x₀ r, c * r ≤ u y) →
      ∀ r ∈ Ioo (0 : ℝ) 1,
        c' * r ≤ ⨍ z, u (x₀ + r • (z : E d)) ∂(volume : Measure (E d)).toSphere)

/-- **Non-degeneracy of downward minimizers** (Alt–Caffarelli, Lemma 3.4; Velichkov, Lemma 4.4):
downward minimizers with `0 < q₀ ≤ Q ≤ C` are uniformly non-degenerate near each free boundary
point. This form assumes `2 ≤ d`, and its constants are chosen per solution;
`DownwardNondegQuantStatement` needs only `1 ≤ d` and has a data-only constant. Proved by
`IsDownwardMinimizer.isUniformlyNondegenerateNear` (`Nondegeneracy/Minimizer.lean`). -/
def DownwardNondegStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ} {x₀ : E d}, 2 ≤ d → IsOpen U →
    IsDownwardMinimizer U Q u → LocallyLipschitzOn U u → (∀ y ∈ U, 0 ≤ u y) →
    (∃ q₀ > 0, ∀ y ∈ U, q₀ ≤ Q y) → (∃ C, ∀ y ∈ U, Q y ≤ C) → Measurable Q →
    x₀ ∈ freeBoundary u U → IsUniformlyNondegenerateNear U u x₀

/-- **Non-degeneracy of local largest subsolutions in `d = 2`** (Abedin–Feldman–Stinson,
Theorem B.1, after Orcan-Ekmekci), local form. The paper assumes only that `u` is a largest
subsolution; here `u` is also assumed `K`-Lipschitz, `C²` and harmonic in `{u > 0}`, with
`Q ≥ q₀ > 0`. `IsNondegenerateAt` chooses its constant per solution; see
`LargestSubNondeg2DQuantStatement` for `c = c(q₀, K)`. Proved by
`isNondegenerateAt_of_isLocalLargestSub` (`Nondegeneracy/LargestSub2D.lean`). -/
def LargestSubNondeg2DStatement : Prop :=
  ∀ {Q u : E 2 → ℝ} {x₀ : E 2} {R q₀ : ℝ} {K : ℝ≥0}, 0 < R → 0 < q₀ →
    (∀ y ∈ ball x₀ R, q₀ ≤ Q y) → IsLocalLargestSub (ball x₀ R) Q u →
    LipschitzOnWith K u (ball x₀ R) → ContDiffOn ℝ 2 u (posSet u (ball x₀ R)) →
    (∀ y ∈ posSet u (ball x₀ R), Δ u y = 0) → x₀ ∈ freeBoundary u (ball x₀ R) →
    IsNondegenerateAt u x₀


/-! ### Quantitative forms

The qualitative predicates `IsNondegenerateAt` and `IsUniformlyNondegenerateNear` choose their
constants after `u`. The statements below fix the constant in terms of the data (`d`, `q₀`, and the
Lipschitz constant `K` in the planar case), as the sources state it.
-/

/-- **Quantitative non-degeneracy of local smallest supersolutions** (Caffarelli–Salsa,
Lemma 6.9). Let `u` be a local smallest
supersolution in the open set `U ⊆ ℝ^d`, `d ≥ 1`, with `Q ≥ q₀ > 0` on `U`. For every
`z ∈ \overline{{u > 0}}` and every closed ball `B̄_r(z) ⊆ U`, `sup_{B̄_r(z)} u ≥ q₀ r / (8d)`.
Proved by `IsLocalSmallestSuper.exists_le_of_closedBall_subset`
(`Nondegeneracy/SmallestSuper.lean`). -/
def SmallestSuperNondegQuantStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ} {q₀ : ℝ}, 1 ≤ d → IsOpen U →
    IsLocalSmallestSuper U Q u → 0 < q₀ → (∀ y ∈ U, q₀ ≤ Q y) →
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, q₀ / (8 * d) * r ≤ u y

/-- **Quantitative non-degeneracy of downward minimizers** (Alt–Caffarelli, Lemma 3.4;
Velichkov, Lemma 4.4). Let `u ≥ 0` be a locally Lipschitz downward minimizer in the open
set `U ⊆ ℝ^d`, `d ≥ 1`, with `q₀ ≤ Q ≤ C` on `U`, `q₀ > 0`, and `Q` measurable. For every
`z ∈ \overline{{u > 0}}` and every closed ball `B̄_r(z) ⊆ U`,
`sup_{B̄_r(z)} u ≥ q₀ r / (8 d e^{d/2})`. The constant does not depend on the upper bound `C`.
Alt–Caffarelli use a trace inequality on a sphere; the proof here avoids traces, and uses neither
`2 ≤ d` nor harmonicity of `u` in `{u > 0}`. Proved by
`IsDownwardMinimizer.exists_le_of_closedBall_subset` (`Nondegeneracy/Minimizer.lean`). -/
def DownwardNondegQuantStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ} {q₀ : ℝ}, 1 ≤ d → IsOpen U →
    IsDownwardMinimizer U Q u → LocallyLipschitzOn U u → (∀ y ∈ U, 0 ≤ u y) → 0 < q₀ →
    (∀ y ∈ U, q₀ ≤ Q y) → (∃ C, ∀ y ∈ U, Q y ≤ C) → Measurable Q →
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, q₀ / (8 * d * Real.exp ((d : ℝ) / 2)) * r ≤ u y

/-- **Quantitative non-degeneracy of local largest subsolutions in `d = 2`**
(Abedin–Feldman–Stinson, Theorem B.1, after Orcan-Ekmekci). For every `q₀ > 0` and `K ≥ 0` there
is `c > 0` such that: if `u` is a local largest subsolution in `B_R(x₀) ⊆ ℝ²` with `Q ≥ q₀` there,
`u` is `K`-Lipschitz on `B_R(x₀)`, `C²` and harmonic in `{u > 0}`, and `x₀ ∈ ∂{u > 0}`, then
`sup_{B̄_r(x₀)} u ≥ c r` for `0 < r ≤ R/2`. The paper assumes only that `u` is a largest
subsolution in `B_1`, and concludes for the sup over `∂B_r` for all `r ≤ 1`; here the Lipschitz,
`C²` and harmonicity hypotheses are added, the scales are `r ≤ R/2`, and no scaling reduction is
used. Proved by `exists_pos_le_of_isLocalLargestSub` (`Nondegeneracy/LargestSub2D.lean`). -/
def LargestSubNondeg2DQuantStatement : Prop :=
  ∀ (q₀ : ℝ) (K : ℝ≥0), 0 < q₀ → ∃ c > 0, ∀ {Q u : E 2 → ℝ} {x₀ : E 2} {R : ℝ}, 0 < R →
    (∀ y ∈ ball x₀ R, q₀ ≤ Q y) → IsLocalLargestSub (ball x₀ R) Q u →
    LipschitzOnWith K u (ball x₀ R) → ContDiffOn ℝ 2 u (posSet u (ball x₀ R)) →
    (∀ y ∈ posSet u (ball x₀ R), Δ u y = 0) → x₀ ∈ freeBoundary u (ball x₀ R) →
    ∀ r, 0 < r → r ≤ R / 2 → ∃ y ∈ closedBall x₀ r, c * r ≤ u y

/-- **Exterior-ball non-degeneracy, same radius** (Abedin–Feldman–Stinson, Lemma B.2, in the
paper's form, where `s = 1`). A viscosity subsolution in `B_s(x₀)`, `d ≥ 1`, with `Q ≥ q₀ > 0`
there and an exterior ball `B_s(p)` of the same radius touching the free boundary at `x₀`,
satisfies `sup_{B_s(x₀)} v ≥ q₀ s / (128 d e^{3d})`. The paper bounds `max_{∂B_1} u`, which
presumes `u` defined up to `∂B_1`; here the supremum is over the open ball.
Proved by `exists_le_of_exteriorBall_sameRadius'` (`Nondegeneracy/ExteriorBall.lean`). -/
def ExteriorBallSameRadiusStatement : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ {Q v : E d → ℝ} {x₀ p : E d} {s q₀ : ℝ},
    0 < s → 0 < q₀ → IsViscSub (ball x₀ s) Q v → (∀ y ∈ ball x₀ s, q₀ ≤ Q y) →
    x₀ ∈ freeBoundary v (ball x₀ s) → ‖x₀ - p‖ = s → (∀ y ∈ ball p s ∩ ball x₀ s, v y = 0) →
    ∃ y ∈ ball x₀ s, q₀ / (128 * d * Real.exp (3 * d)) * s ≤ v y

end EllipticBernoulli
