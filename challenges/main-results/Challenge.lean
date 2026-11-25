module

-- challenge-prep: split vocabulary (aux-proof reuse: a merged file fails the fingerprint diff)
-- One module per library file. Concatenating them lets later definitions reuse earlier auxiliary
-- `_proof_k` constants that the library mints per module, so the values would no longer match
-- (`scripts/fingerprint-challenges.sh`).
public import Vocabulary.Setting
public import Vocabulary.Sobolev
public import Vocabulary.Touching
public import Vocabulary.Viscosity
public import Vocabulary.Regularity
public import Vocabulary.Variational
public import Vocabulary.TwoPhase
public import Mathlib.MeasureTheory.Integral.Average

@[expose] public section

/-!
# Challenge: the main results of the library

Trusted statement surface for the library's main results, in one workspace. Each section below
states one result (or a group of closely related results) with `sorry`; `Solution.lean` proves the
same statements from the library. The sections are, in order: existence and continuity for the
obstacle problem; energy-decreasing perturbations; one-sided minimizers as viscosity solutions;
regularity of local energy minimizers; the Lipschitz estimate; non-degeneracy; De Silva's flatness
theorem; smooth charts at flat free-boundary points; classical solutions; the planar
classification of `1`-homogeneous inner variational solutions; the Friedland–Hayman inequality;
the Alt–Caffarelli–Friedman monotonicity formula; the classification of global two-phase
minimizers; Weiss monotonicity in a ball; and the quantitative charts at flat free boundaries.

The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Basic/Touching.lean`, `Defs/Viscosity.lean`,
`Defs/Regularity.lean`, `Defs/Variational.lean`, `Defs/TwoPhase.lean`), with the library's names,
definitions and order. Every file imports Mathlib modules only (the same ones as the library file
it restates).
-/

noncomputable section

namespace EllipticBernoulli

/-!
## Existence and continuity for the obstacle problem

Trusted statement surface for the obstacle problem of the Alt–Caffarelli energy
`J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}` (Abedin–Feldman–Stinson, proof of Lemma 6.3).
`IsObstacleMinimizer U B Q u K w Gw` says that `w` minimizes `J_Q(·; B)` among `H¹_loc(U)`
competitors equal to `u` a.e. off `B` with `v y ∈ K y` a.e., and that `w` itself satisfies both
conditions pointwise. Minimizers exist for bounded measurable `Q` and closed constraints admitting
`u` (direct method); for the two constraints `0 ≤ v ≤ u` and `u ≤ v`, with `Q` Lipschitz and
`0 < c ≤ Q ≤ C` and `u ≥ 0` locally Lipschitz, every minimizer has a representative continuous on
all of `U`, including across `∂B` (De Giorgi; the interior continuity argument is new here).

### References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

section ObstacleExistence

open Set Filter Topology MeasureTheory Metric

variable {d : ℕ}

/-- Challenge: existence for the obstacle problem (direct method). -/
theorem challenge_exists_isObstacleMinimizer {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d}
    {K : E d → Set ℝ} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ C, ∀ x ∈ U, |Q x| ≤ C)
    (hQm : Measurable Q)
    (hu : MemH1Loc U u Gu) (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) (hK : ∀ y, IsClosed (K y))
    (huK : ∀ y ∈ U, u y ∈ K y) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), IsObstacleMinimizer U (ball x₀ r) Q u K w Gw := by
  sorry

/-- Challenge: continuity of obstacle minimizers on all of `U`, for the constraints `0 ≤ v ≤ u` and
`u ≤ v`. -/
theorem challenge_isObstacleMinimizer_exists_continuousOn {U : Set (E d)} {Q u : E d → ℝ}
    {K : E d → Set ℝ} {w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U)
    (hQ : ∃ L, LipschitzOnWith L Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y) (hB : closedBall x₀ r ⊆ U)
    (hr : 0 < r) (hK : K = (fun y ↦ Icc 0 (u y)) ∨ K = (fun y ↦ Ici (u y)))
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u K w Gw) :
    ∃ w' : E d → ℝ, (∀ᵐ y ∂volume.restrict U, w' y = w y) ∧
      IsObstacleMinimizer U (ball x₀ r) Q u K w' Gw ∧ ContinuousOn w' U := by
  sorry

end ObstacleExistence

/-!
## Energy-decreasing perturbations (the proof of Feldman–Kim–Požár, Lemma 3.3)

Trusted statement surface for the perturbation step in the proof of Feldman–Kim–Požár, Lemma 3.3,
together with their Lemma A.1; Abedin–Feldman–Stinson use it in the proof of their Lemma 6.3. The
statements are the key step of that proof, not the lemma itself (minimizers are viscosity
solutions), which is certified in `challenges/viscosity-minimizers`.

Let `w ≥ 0` be continuous on the open set `U`, with weak gradient `Gw`, and let a smooth `φ`
touch `w` strictly from below, or `φ₊` touch `w` strictly from above relative to
`\overline{{w > 0}}`, at a point `x₀` of an open `B ⊂⊂ U`, where the supersolution (resp.
subsolution) test of the one-phase problem `|∇u| = Q` fails. Let `Q` be Lipschitz with
`0 < c ≤ Q ≤ C` on `U`. Then for every `ρ, η > 0` a local perturbation of `w` inside
`B_ρ(x₀) ⊆ B`, trapped between `w` and `max(w, φ + η)` (resp. `min(w, (φ − η)₊)` and `w`), has
strictly smaller Alt–Caffarelli energy `J_Q(·; B) = ∫_B |∇·|² + Q² 1_{·>0}`.

### References

* W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

section EnergyPerturbation

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

variable {d : ℕ}

/-- Challenge: energy decrease when the supersolution test fails at a strict touching point
from below (proof of Feldman–Kim–Požár, Lemma 3.3). -/
theorem challenge_energy_decrease_of_not_super {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (htouch : φ x₀ = w x₀ ∧ ∀ᶠ y in 𝓝[≠] x₀, φ y < w y)
    (hfail : 0 < Δ φ x₀ ∧ (φ x₀ = 0 → Q x₀ < ‖∇ φ x₀‖)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, w y ≤ w' y ∧ w' y ≤ max (w y) (φ y + η)) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  sorry

/-- Challenge: energy decrease when the subsolution test fails at a strict touching point
from above (proof of Feldman–Kim–Požár, Lemma 3.3). -/
theorem challenge_energy_decrease_of_not_sub {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (hx₀pos : x₀ ∈ closure (posSet w U))
    (htouch : max (φ x₀) 0 = w x₀ ∧
      ∀ᶠ y in 𝓝[(closure (posSet w U) ∩ U) \ {x₀}] x₀, w y < max (φ y) 0)
    (hfail : Δ φ x₀ < 0 ∧ (φ x₀ = 0 → ‖∇ φ x₀‖ < Q x₀)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, min (w y) (max (φ y - η) 0) ≤ w' y ∧ w' y ≤ w y) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  sorry

end EnergyPerturbation

/-!
## Minimizers are viscosity solutions

Trusted statement surface for the passage from energy minimality to the viscosity sense of the
one-phase problem `Δu = 0` in `{u > 0}`, `|∇u| = Q` on `∂{u > 0}`, for the Alt–Caffarelli energy
`J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}`.

* One-sided minimizers (Feldman–Kim–Požár, Lemma 3.3; Velichkov, Proposition 7.1): for continuous
  `Q ≥ 0` and continuous `u ≥ 0`, upward minimizers are viscosity supersolutions, downward
  minimizers are viscosity subsolutions, and local energy minimizers are viscosity solutions. Upward
  and downward minimizers are harmonic and `C²` in `{u > 0}` by definition.
* Obstacle minimizers (Abedin–Feldman–Stinson, Lemma 6.3, Steps 1–2): for `Q` Lipschitz with
  `0 < c ≤ Q ≤ C`, a continuous minimizer of `J_Q(·; B_r(x₀))` under the constraint `0 ≤ w ≤ u`
  below a supersolution `u` is a supersolution in `U`, and a continuous minimizer under `u ≤ w`
  above a subsolution `u` is a subsolution in `U`.

### References

* W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

section ViscosityMinimizers

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

variable {d : ℕ}

/-- Challenge: upward minimizers are viscosity supersolutions (Feldman–Kim–Požár, Lemma 3.3).
`Q ≥ 0` is needed: the energy sees only `Q²`, while the viscosity test sees `Q`. -/
theorem challenge_isUpwardMinimizer_isViscSuper {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ y ∈ U, 0 ≤ Q y) (hu : ContinuousOn u U)
    (hu0 : ∀ y ∈ U, 0 ≤ u y) (hmin : IsUpwardMinimizer U Q u) : IsViscSuper U Q u := by
  sorry

/-- Challenge: downward minimizers are viscosity subsolutions (Feldman–Kim–Požár,
Lemma 3.3). -/
theorem challenge_isDownwardMinimizer_isViscSub {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hu : ContinuousOn u U) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    (hmin : IsDownwardMinimizer U Q u) : IsViscSub U Q u := by
  sorry

/-- Challenge: continuous local energy minimizers are viscosity solutions (Velichkov,
Proposition 7.1). -/
theorem challenge_isLocalEnergyMinimizer_isViscSolution {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ y ∈ U, 0 ≤ Q y) (hu : ContinuousOn u U)
    (hu0 : ∀ y ∈ U, 0 ≤ u y) (hmin : IsLocalEnergyMinimizer U Q u) : IsViscSolution U Q u := by
  sorry

/-- Challenge: a continuous obstacle minimizer below a supersolution, under the constraint
`0 ≤ w ≤ u`, is a supersolution (Abedin–Feldman–Stinson, Lemma 6.3, Step 1). -/
theorem challenge_isObstacleMinimizer_isViscSuper_of_upper {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : IsViscSuper U Q u) (hr : closedBall x₀ r ⊆ U)
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Icc 0 (u y)) w Gw)
    (hwc : ContinuousOn w U) : IsViscSuper U Q w := by
  sorry

/-- Challenge: a continuous obstacle minimizer above a subsolution, under the constraint
`u ≤ w`, is a subsolution (Abedin–Feldman–Stinson, Lemma 6.3, Step 2). -/
theorem challenge_isObstacleMinimizer_isViscSub_of_lower {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : IsViscSub U Q u) (hr : closedBall x₀ r ⊆ U)
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Ici (u y)) w Gw)
    (hwc : ContinuousOn w U) : IsViscSub U Q w := by
  sorry

end ViscosityMinimizers

/-!
## Regularity of local energy minimizers

Trusted statement surface for the interior regularity of local minimizers of the Alt–Caffarelli
energy `J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}` (Alt–Caffarelli (1981), §§2–3; Velichkov, Ch. 3 and
Proposition 7.1). Let `Q` be continuous with `0 ≤ Q ≤ C` on the open set `U`, and let `u ≥ 0` a.e. on
`U` be a local minimizer (`IsLocalEnergyMinimizer`, energies compared on balls `B ⋐ U`). Then `u` has
an a.e.-equal representative `v` on `U` which is again a local minimizer, is locally Lipschitz and
non-negative on `U`, has open positivity set `{v > 0} ∩ U`, and is `C^∞` and harmonic there.
Continuity is proved by De Giorgi's method (Giusti, Ch. 7) rather than by the harmonic replacement
of Alt–Caffarelli.

### References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
* E. Giusti, *Direct Methods in the Calculus of Variations*, World Scientific, 2003.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

section EnergyMinimizerRegularity

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Laplacian

variable {d : ℕ}

/-- Challenge: a local energy minimizer has a locally Lipschitz representative, smooth and harmonic
in its positivity set (Alt–Caffarelli (1981); Velichkov, Proposition 7.1). -/
theorem challenge_isLocalEnergyMinimizer_exists_regular_representative {U : Set (E d)}
    {Q u : E d → ℝ} (hU : IsOpen U) (hQc : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U Q u) :
    ∃ v : E d → ℝ, (∀ᵐ x ∂volume.restrict U, v x = u x) ∧ IsLocalEnergyMinimizer U Q v ∧
      LocallyLipschitzOn U v ∧ (∀ x ∈ U, 0 ≤ v x) ∧ IsOpen (posSet v U) ∧
      ContDiffOn ℝ ∞ v (posSet v U) ∧ ∀ x ∈ posSet v U, Δ v x = 0 := by
  sorry

end EnergyMinimizerRegularity

/-!
## The Lipschitz estimate for viscosity supersolutions

Trusted statement surface for the Lipschitz estimate of the one-phase problem (Caffarelli–Salsa,
Lemma 11.19). Viscosity super/subsolutions are those of Abedin–Feldman–Stinson, Definition 2.1
(`IsViscSuper`, `IsViscSub`, `IsViscSolution`): tests are globally smooth functions touching
non-strictly, and at a free boundary point either `Δφ ≤ 0` or `φ = 0` and `|∇φ| ≤ Q`
(supersolution). A viscosity supersolution which is harmonic in `{u > 0}` is Lipschitz,
quantitatively on balls and locally on `U`.

### References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

section LipschitzEstimate

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped NNReal

variable {d : ℕ}

/-- Challenge: the quantitative Lipschitz estimate (Caffarelli–Salsa Lemma 11.19): for `1 ≤ d`
there is `C` such that a viscosity supersolution in `U ⊇ B_{2r}(x₀)`, harmonic in `{u > 0}`, with
`Q ≤ Qmax` and `u ≤ M` on `B_{2r}(x₀)`, is `C (Qmax + M / r)`-Lipschitz on `B_r(x₀)`. -/
theorem challenge_lipschitzOnWith_of_isViscSuper (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) (r Qmax M : ℝ),
      IsOpen U → 0 < r → ball x₀ (2 * r) ⊆ U → IsViscSuper U Q u →
      HarmonicOnNhd u (posSet u U) → (∀ y ∈ ball x₀ (2 * r), Q y ≤ Qmax) → 0 ≤ Qmax →
      (∀ y ∈ ball x₀ (2 * r), u y ≤ M) →
      LipschitzOnWith (C * (Qmax + M / r)).toNNReal u (ball x₀ r) := by
  sorry

/-- Challenge: local Lipschitz regularity of viscosity supersolutions harmonic in `{u > 0}`, for
continuous `Q`. -/
theorem challenge_locallyLipschitzOn_of_isViscSuper {U : Set (E d)} {Q u : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) (hharm : HarmonicOnNhd u (posSet u U)) (hQ : ContinuousOn Q U) :
    LocallyLipschitzOn U u := by
  sorry

end LipschitzEstimate

/-!
## Non-degeneracy

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

### References

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

section Nondegeneracy

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Laplacian NNReal

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

end Nondegeneracy

/-!
## Flat free boundaries are regular (De Silva)

Trusted statement surface for De Silva's theorem (De Silva (2011), Theorem 1.1, with `f = 0`,
`g = Q`). De Silva allows a Hölder coefficient `g`; here `Q` is `L`-Lipschitz. For `2 ≤ d` and
`0 < qmin ≤ Q ≤ qmax`, there is `ε̄ > 0` such that a viscosity solution (Abedin–Feldman–Stinson,
Definition 2.1) which is two-sidedly `ε̄ r`-flat with slope `Q(x₀)` in `B_r(x₀) ⊆ U`, `0 < r ≤ ε̄`,
at a free boundary point `x₀` has a `C^{1,γ}` free boundary in `B_{r/2}(x₀)`
(`IsC1GammaHypersurfaceNear`), and is classical near `x₀` (`IsClassicalNear`: the free boundary is a
`C^{1,γ}` hypersurface, `u` is `C²` and harmonic in `{u > 0}`, `∇u` extends continuously to the free
boundary with `|∇u| = Q` there). The exponent `γ`, the Hölder constant and the `IsClassicalNear`
radius are existential for each solution; in De Silva they do not depend on the solution.

### References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

section FlatnessRegularity

open Set Filter Topology Metric
open scoped NNReal

variable {d : ℕ}

/-- Challenge: flatness implies a `C^{1,γ}` free boundary (De Silva (2011), Theorem 1.1). -/
theorem challenge_isC1GammaHypersurfaceNear_of_flat (hd : 2 ≤ d) (L : ℝ≥0) (qmin qmax : ℝ)
    (hqmin : 0 < qmin) :
    ∃ εbar > 0, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsC1GammaHypersurfaceNear (freeBoundary u U) x₀ (r / 2) := by
  sorry

/-- Challenge: flatness implies classical regularity near the free boundary point. -/
theorem challenge_isClassicalNear_of_flat (hd : 2 ≤ d) (L : ℝ≥0) (qmin qmax : ℝ)
    (hqmin : 0 < qmin) :
    ∃ εbar > 0, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsClassicalNear U Q u x₀ := by
  sorry

end FlatnessRegularity

/-!
## Smooth one-sided charts at flat free-boundary points

Trusted statement surface for the smoothness of the free boundary at flat points
(Kinderlehrer–Nirenberg (1977), with De Silva (2011) for the `C^{1,γ}` step). Let `d ≥ 2`, `U ⊆ ℝᵈ`
open, and `u` continuous and non-negative on `U`, a local minimizer (`IsLocalEnergyMinimizer`,
energies compared on balls `B ⋐ U`) of `J(v; B) = ∫_B |∇v|² + 1_{v>0}`. Let `x₀` be a free-boundary
point at which the half-plane solution `(y · e)₊` is a blow-up limit (`IsBlowupLimit`: the rescalings
`u(x₀ + r y)/r` converge to it locally uniformly along some sequence `r_n → 0⁺`), for a unit vector
`e`. Then near `x₀`, `u = max(F, 0)` for a function `F` which is `C^∞` on a ball `B_ρ(x₀) ⊆ U`, has
non-vanishing gradient there, is harmonic where it is positive, and satisfies `|∇F| = 1` on
`{F = 0}`; the positive side `{F > 0} ∩ B_ρ(x₀)` is preconnected. In particular the free boundary is
a `C^∞` hypersurface near `x₀`.

The coefficient is `Q ≡ 1`.

### References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*, Proc. Amer. Math. Soc. 15
  (1964), 625–626.
-/

section FlatChart

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

variable {d : ℕ}

/-- Challenge: a smooth one-sided chart at a flat free-boundary point of a local minimizer
(Kinderlehrer–Nirenberg (1977); De Silva (2011)). -/
theorem challenge_flat_chart (hd : 2 ≤ d) {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d}
    (hU : IsOpen U) (hc : ContinuousOn u U) (hnn : ∀ x ∈ U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) (hx₀ : x₀ ∈ freeBoundary u U) (he : ‖e‖ = 1)
    (hblow : IsBlowupLimit u x₀ (fun y ↦ max (inner ℝ y e) 0)) :
    ∃ ρ > 0, ball x₀ ρ ⊆ U ∧ ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ) ∧
      (∀ x ∈ ball x₀ ρ, u x = max (F x) 0) ∧ (∀ x ∈ ball x₀ ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ, F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ ball x₀ ρ, 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ | 0 < F x} := by
  sorry

end FlatChart

/-!
## Classical solutions

Trusted statement surface for classical solutions of the one-phase problem (`IsClassicalSolution`:
the classical solutions of Kriventsov–Weiss, Definition 9.1, with a variable coefficient `Q`; `u`
Lipschitz, harmonic in `{u > 0}`, the free boundary locally the zero set of a smooth `F` with
`∇F ≠ 0`, and the normal difference quotient into `{u > 0}` tending to `Q`). Classical solutions are
viscosity solutions (Abedin–Feldman–Stinson, Definition 2.1); for Lipschitz `Q ≥ c > 0` they satisfy
the inner-variation identity (Abedin–Feldman–Stinson, (2.5), with `χ = 1_{{u>0} ∩ U}`, for Lipschitz
test fields compactly supported in `U`); and, for `Q ≡ 1`, they satisfy the Alt–Caffarelli gradient
bound `sup_{B_r} |∇u| ≤ 1 + ω(r)` with a modulus `ω` depending on the Lipschitz bound `L`
(Alt–Caffarelli, Thm 6.3, as cited in Kriventsov–Weiss, Proposition 9.1; Kriventsov–Weiss numbers
are those of arXiv:2306.10131v2). Kriventsov–Weiss state the modulus as depending only on the
dimension.

### References

* D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
-/

section ClassicalSolutions

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

variable {d : ℕ}

/-- Challenge: classical solutions are viscosity solutions. -/
theorem challenge_isClassicalSolution_isViscSolution {U : Set (E d)} {Q u : E d → ℝ}
    (hu : IsClassicalSolution U Q u) (hQ : ContinuousOn Q U) : IsViscSolution U Q u := by
  sorry

/-- Challenge: classical solutions satisfy the inner-variation identity with
`χ = 1_{{u>0} ∩ U}`. -/
theorem challenge_isClassicalSolution_integral_innerVarIntegrand_eq_zero {U : Set (E d)}
    {Q u : E d → ℝ} {ξ : E d → E d}
    (hu : IsClassicalSolution U Q u) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ y ∈ U, c ≤ Q y) (hξ : ∃ K, LipschitzWith K ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ U) :
    ∫ x in U, innerVarIntegrand Q u ((posSet u U).indicator 1) ξ x = 0 := by
  sorry

/-- Challenge: the Alt–Caffarelli gradient bound for `L`-Lipschitz classical solutions with `Q ≡ 1`
and `u(0) = 0` on `B_1`, encoded as a Lipschitz bound `1 + ω(r)` on `B_r`. -/
theorem challenge_classical_lipschitz_bound (L : ℝ≥0) :
    ∃ w : ℝ → ℝ, ContinuousOn w (Ico 0 1) ∧ MonotoneOn w (Ico 0 1) ∧
      Tendsto w (𝓝[>] 0) (𝓝 0) ∧
      ∀ u : E d → ℝ, IsClassicalSolution (ball 0 1) (fun _ ↦ 1) u →
        LipschitzOnWith L u (ball 0 1) →
        u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r) := by
  sorry

end ClassicalSolutions

/-!
## Planar 1-homogeneous inner variational solutions

Trusted statement surface for the classification of 1-homogeneous inner variational solutions in the
plane (after Jerison–Kamburov, §5, whose Propositions 5.3 and 5.4 assume stronger hypotheses). An
inner variational solution `(v, χ)` of the one-phase problem with constant `Q ≡ q > 0` on all of
`ℝ²` (Abedin–Feldman–Stinson, Definition 2.8, `IsInnerVarSolution`) with `v` 1-homogeneous is a
half-plane solution, a two-plane solution `α |x · e|` with `χ = 1` a.e., or trivial with `χ = 0`
a.e.

### References

* D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res.
  Not. IMRN 2016, no. 19, 5922–5987; arXiv:1412.4106.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

section PlanarClassification

open Set Filter Topology MeasureTheory

/-- Challenge: `PlanarHomogeneousClassificationStatement`. -/
theorem challenge_classification_homogeneous_planar {q : ℝ} (hq : 0 < q) {v χ : E 2 → ℝ}
    (h : IsInnerVarSolution univ (fun _ ↦ q) v χ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ y : E 2, v (t • y) = t * v y) :
    ∃ e : E 2, ‖e‖ = 1 ∧
      (((∀ y, v y = q * max (inner ℝ y e) 0) ∧
          ∀ᵐ y, χ y = {z : E 2 | 0 < inner ℝ z e}.indicator 1 y) ∨
        (∃ α : ℝ, 0 ≤ α ∧ (∀ y, v y = α * |inner ℝ y e|) ∧ ∀ᵐ y, χ y = 1) ∨
        ((∀ y, v y = 0) ∧ ∀ᵐ y, χ y = 0)) := by
  sorry

end PlanarClassification

/-!
## The Friedland–Hayman inequality

Trusted statement surface for the Friedland–Hayman inequality (Friedland–Hayman (1976); Beck–Jerison,
Theorem 1.1, for homogeneous harmonic functions) in every dimension `d ≥ 2`: for nonempty,
relatively open, disjoint `Γ₁, Γ₂ ⊆ 𝕊^{d-1}`, the characteristic exponents satisfy
`α_d(Γ₁) + α_d(Γ₂) ≥ 2`.

Here `α_d(Γ) = sphExponent Γ = κ_d(λ₁(Γ))`, where `κ_d(λ)` is the nonnegative root of
`α (α + d - 2) = λ` and `λ₁(Γ) = sphEigenvalue Γ` is the infimum of the Rayleigh quotients
`∫_𝕊 |∇_𝕊 f|² dσ / ∫_𝕊 f² dσ` over functions `f` on the sphere that are Lipschitz for the chordal
metric, vanish off `Γ`, and have `∫_𝕊 f² dσ > 0`. The tangential gradient is the gradient of the
`0`-homogeneous extension `x ↦ f (x / ‖x‖)`, and `σ` is Mathlib's sphere measure
`(volume : Measure (E d)).toSphere`. The sources use `H¹₀(Γ)` trial functions instead of Lipschitz
ones.

### References

* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* T. Beck, D. Jerison, *The Friedland–Hayman inequality and Caffarelli's contraction theorem*,
  arXiv:2102.00571.
-/

section FriedlandHayman

open Metric

/-- Challenge: the Friedland–Hayman inequality. For `d ≥ 2` and nonempty, relatively open, disjoint
`Γ₁, Γ₂ ⊆ 𝕊^{d-1}`, `α_d(Γ₁) + α_d(Γ₂) ≥ 2` (Friedland–Hayman (1976)). -/
theorem challenge_friedlandHayman {d : ℕ} (hd : 2 ≤ d) (Γ₁ Γ₂ : Set (sphere (0 : E d) 1))
    (hΓ₁ : IsOpen Γ₁) (hΓ₂ : IsOpen Γ₂) (hne₁ : Γ₁.Nonempty) (hne₂ : Γ₂.Nonempty)
    (hdisj : Disjoint Γ₁ Γ₂) :
    2 ≤ sphExponent Γ₁ + sphExponent Γ₂ := by
  sorry

end FriedlandHayman

/-!
## The Alt–Caffarelli–Friedman monotonicity formula

Trusted statement surface for the Alt–Caffarelli–Friedman monotonicity formula
(Alt–Caffarelli–Friedman (1984); Salato, Theorem 1.1) in every dimension `d ≥ 2`. Let
`u₁, u₂ : ℝᵈ → ℝ` be nonnegative, `L`-Lipschitz and harmonic on the open sets `{uᵢ > 0}`, with
`u₁ u₂ ≡ 0` and `u₁(x₀) = u₂(x₀) = 0`. Then
`r ↦ Φ(u₁, u₂, x₀, r) = r⁻⁴ I(u₁, x₀, r) I(u₂, x₀, r)`, where
`I(w, x₀, r) = ∫_{B_r(x₀)} |∇w(x)|² |x - x₀|^{2-d} dx` (`acfPhi`, `acfIntegral`), is
nondecreasing on `(0, ∞)`.

Alt–Caffarelli–Friedman assume continuity and subharmonicity in the sense of distributions; here
the functions are Lipschitz and harmonic in their positivity sets. The statement assumes no
Friedland–Hayman inequality: the solution proves it (Friedland–Hayman (1976)) and uses it.

The hypotheses are written out; they are the fields of the vocabulary's `IsACFPair u₁ u₂ x₀ L`.
The project vocabulary is restated in `Vocabulary/*.lean`, one module per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Defs/Variational.lean`, `Defs/TwoPhase.lean`), with
the library's names, definitions and order. Every file imports Mathlib modules only (the same ones
as the library file it restates).

### References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473.
-/

section AcfMonotonicity

open Set
open scoped NNReal

/-- Challenge: the Alt–Caffarelli–Friedman monotonicity formula. For `d ≥ 2`, nonnegative
`L`-Lipschitz `u₁, u₂` harmonic in their positivity sets, with `u₁ u₂ ≡ 0` and
`u₁(x₀) = u₂(x₀) = 0`, `r ↦ Φ(u₁, u₂, x₀, r)` is nondecreasing on `(0, ∞)`
(Alt–Caffarelli–Friedman (1984)). -/
theorem challenge_acfMonotoneIn {d : ℕ} (hd : 2 ≤ d) {u₁ u₂ : E d → ℝ} {x₀ : E d} {L : ℝ≥0}
    (hnn₁ : ∀ x, 0 ≤ u₁ x) (hnn₂ : ∀ x, 0 ≤ u₂ x)
    (hlip₁ : LipschitzWith L u₁) (hlip₂ : LipschitzWith L u₂)
    (hharm₁ : InnerProductSpace.HarmonicOnNhd u₁ {x | 0 < u₁ x})
    (hharm₂ : InnerProductSpace.HarmonicOnNhd u₂ {x | 0 < u₂ x})
    (hmul : ∀ x, u₁ x * u₂ x = 0) (hx₁ : u₁ x₀ = 0) (hx₂ : u₂ x₀ = 0) :
    MonotoneOn (fun r ↦ acfPhi u₁ u₂ x₀ r) (Ioi 0) := by
  sorry

end AcfMonotonicity

/-!
## Classification of global two-phase minimizers

Trusted statement surface for the classification of global minimizers of the two-phase problem
(after Alt–Caffarelli–Friedman (1984)). Let `u : ℝᵈ → ℝ` be Lipschitz and a local minimizer
(`IsLocalEnergyMinimizer univ (fun _ ↦ 1) u`) of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` on `ℝᵈ`: for some
weak gradient, `u ∈ H¹_loc(ℝᵈ)`, and on every ball `B`, `J(u; B) ≤ J(v; B)` for every
`v ∈ H¹_loc(ℝᵈ)` with `v = u` a.e. off `B`. Only the positive phase is penalized, and `u` may
change sign. If `u` takes a positive and a negative value, then there are a unit vector `e`,
`c ∈ ℝ` and `a, b > 0` with `a² - b² = 1` such that
`u(x) = a (x·e + c)⁺ - b (x·e + c)⁻` for every `x`. The statement covers every dimension `d`.

Alt–Caffarelli–Friedman work with continuous functions; here `u` is Lipschitz. The proof combines
the Alt–Caffarelli–Friedman monotonicity formula, the Friedland–Hayman inequality (Friedland–Hayman
(1976)), Weiss monotonicity (Weiss (1999)) and the classification of `1`-homogeneous two-phase
functions (after De Philippis–Spolaor–Velichkov, Lemma 2.2).

### References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* G. De Philippis, L. Spolaor, B. Velichkov, *Regularity of the free boundary for the two-phase
  Bernoulli problem*, Invent. Math. 225 (2021), 347–394; arXiv:1911.02165.
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.
-/

section TwoPhaseClassification

open Set
open scoped NNReal

/-- Challenge: a Lipschitz local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` on `ℝᵈ` that takes a
positive and a negative value is a two-plane function `a (x·e + c)⁺ - b (x·e + c)⁻` with
`‖e‖ = 1`, `a, b > 0` and `a² - b² = 1` (after Alt–Caffarelli–Friedman (1984)). -/
theorem challenge_twoPhaseClassification {d : ℕ} {u : E d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hpos : ∃ x, 0 < u x)
    (hneg : ∃ x, u x < 0) :
    ∃ (e : E d) (c a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = 1 ∧
      ∀ x, u x = a * max (inner ℝ x e + c) 0 - b * max (-(inner ℝ x e + c)) 0 := by
  sorry

end TwoPhaseClassification

/-!
## Weiss monotonicity in a ball, with rigidity

Trusted statement surface for Weiss's monotonicity formula (Weiss (1999)) localized to a ball. Let
`d ≥ 2`, `U ⊆ ℝᵈ` open with `B_R(x₀) ⊆ U`, and `u` a local minimizer in `U`
(`IsLocalEnergyMinimizer`, energies compared on balls `B ⋐ U`) of `J(v; B) = ∫_B |∇v|² + 1_{v>0}`,
with no sign condition, `L`-Lipschitz on `B_R(x₀)` and with `u(x₀) = 0`. Write `W(r) = weissW u x₀ r`
for the Weiss energy and `D(r, s) = weissDefect u x₀ r s` for the integrated homogeneity defect.
Then:
* for `0 < r < s < R`, `W(s) - W(r) ≥ D(r, s) ≥ 0`;
* for `0 < r < R`, `|W(r)| ≤ (L² + 1) |B₁| + L² σ(𝕊)`;
* for `0 < r < s < R`, if `W(r) = W(s)`, then `u` is `1`-homogeneous about `x₀` on the annulus
  `r < |x - x₀| < s`: `u(x₀ + τ (x - x₀)) = τ u(x)` whenever `x` and `x₀ + τ (x - x₀)` (`τ > 0`) both
  lie in the annulus.

The coefficient is `Q ≡ 1`.

### References

* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.
-/

section WeissLocal

open Set Metric MeasureTheory
open scoped NNReal

/-- Challenge: Weiss monotonicity in a ball `B_R(x₀) ⊆ U` for a local minimizer in `U` that is
Lipschitz on the ball and vanishes at `x₀`, with the uniform bound on `W` and rigidity: equality
`W(r) = W(s)` forces `1`-homogeneity on the annulus (Weiss (1999)). -/
theorem challenge_weissMonotoneLocal {d : ℕ} (hd : 2 ≤ d) {U : Set (E d)} {u : E d → ℝ} {L : ℝ≥0}
    {x₀ : E d} {R : ℝ} (hU : IsOpen U) (hB : ball x₀ R ⊆ U)
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) (hlip : LipschitzOnWith L u (ball x₀ R))
    (hu : u x₀ = 0) :
    (∀ r s : ℝ, 0 < r → r < s → s < R →
      weissDefect u x₀ r s ≤ weissW u x₀ s - weissW u x₀ r ∧ 0 ≤ weissDefect u x₀ r s) ∧
    (∀ r : ℝ, 0 < r → r < R →
      |weissW u x₀ r| ≤ ((L : ℝ) ^ 2 + 1) * volume.real (ball (0 : E d) 1) +
        (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ) ∧
    ∀ r s : ℝ, 0 < r → r < s → s < R → weissW u x₀ r = weissW u x₀ s →
      ∀ x : E d, r < ‖x - x₀‖ → ‖x - x₀‖ < s → ∀ τ : ℝ, 0 < τ → r < τ * ‖x - x₀‖ →
        τ * ‖x - x₀‖ < s → u (x₀ + τ • (x - x₀)) = τ * u x := by
  sorry

end WeissLocal

/-!
## The quantitative `C^{2,α}` chart at a flat free boundary

Trusted statement surface for the quantitative smooth chart at a flat free boundary, on `B_{1/2}`
(Kinderlehrer–Nirenberg (1977), with De Silva (2011) for the flatness step). For `d ≥ 2` there are
`ε₀ > 0`, `α > 0` and `C > 0` with the following property. Let `u` be continuous and non-negative on
`B_1`, a local minimizer in `B_1` (`IsLocalEnergyMinimizer`, energies compared on balls `B ⋐ B_1`)
of `J(v; B) = ∫_B |∇v|² + 1_{v>0}`, and let `‖e‖ = 1` and `ε ≤ ε₀` with `|u(x) - (x · e)₊| ≤ ε` on
`B_1`. Then there is `F`, `C^∞` on `B_{1/2}`, with `u = max(F, 0)`, `|∇F| = 1` on `{F = 0}` and
`ΔF = 0` on `{F > 0}` in `B_{1/2}`; on `{F ≥ 0} ∩ B_{1/2}`, `∇F · e ≥ 1/2`, `|∇F| ≤ C`,
`|D²F| ≤ C`, and `|D²F(x) - D²F(y)| ≤ C |x - y|^α`.

The coefficient is `Q ≡ 1`.

### References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

section QuantFlatChart

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

/-- Challenge: the quantitative `C^{2,α}` chart at a flat free boundary, with constants depending
on the dimension only (Kinderlehrer–Nirenberg (1977); De Silva (2011)). -/
theorem challenge_quantFlatChart :
    ∀ {d : ℕ}, 2 ≤ d → ∃ ε₀ > 0, ∃ α > 0, ∃ C > 0, ∀ {u : E d → ℝ} {e : E d} {ε : ℝ},
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 → ε ≤ ε₀ →
    (∀ x ∈ ball (0 : E d) 1, |u x - max (inner ℝ x e) 0| ≤ ε) →
    ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball 0 (1 / 2)) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), u x = max (F x) 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), 0 < F x → Δ F x = 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), 0 ≤ F x →
        1 / 2 ≤ inner ℝ (∇ F x) e ∧ ‖∇ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), ∀ y ∈ ball (0 : E d) (1 / 2), 0 ≤ F x → 0 ≤ F y →
        ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ ≤ C * ‖x - y‖ ^ α) := by
  sorry

end QuantFlatChart

/-!
## The quantitative third-derivative bound at a flat free boundary

Trusted statement surface for the third-derivative bound of the smooth chart at a flat free
boundary, on `B_{1/4}` (Kinderlehrer–Nirenberg (1977), with De Silva (2011) for the flatness step).
For `d ≥ 2` there are `ε₀ > 0` and `C₀ > 0` with the following property. Let `u` be continuous and
non-negative on `B_1`, a local minimizer in `B_1` (`IsLocalEnergyMinimizer`, energies compared on
balls `B ⋐ B_1`) of `J(v; B) = ∫_B |∇v|² + 1_{v>0}`, and let `‖e‖ = 1` and `ε ≤ ε₀` with
`|u(x) - (x · e)₊| ≤ ε` on `B_1`. Then there is `F`, `C^∞` on `B_{1/4}`, with `u = max(F, 0)`,
`|∇F| = 1` on `{F = 0}` and `ΔF = 0` on `{F > 0}` in `B_{1/4}`; on `{F ≥ 0} ∩ B_{1/4}`,
`∇F · e ≥ 1/2` and `|D³F| ≤ C₀`.

The coefficient is `Q ≡ 1`.

### References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

section QuantFlatChartThree

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

/-- Challenge: the quantitative third-derivative bound at a flat free boundary, with constants
depending on the dimension only (Kinderlehrer–Nirenberg (1977); De Silva (2011)). -/
theorem challenge_quantFlatChartThree :
    ∀ {d : ℕ}, 2 ≤ d → ∃ ε₀ > 0, ∃ C₀ > 0, ∀ {u : E d → ℝ} {e : E d} {ε : ℝ},
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 → ε ≤ ε₀ →
    (∀ x ∈ ball (0 : E d) 1, |u x - max (inner ℝ x e) 0| ≤ ε) →
    ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball 0 (1 / 4)) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), u x = max (F x) 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), 0 < F x → Δ F x = 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), 0 ≤ F x →
        1 / 2 ≤ inner ℝ (∇ F x) e ∧ ‖iteratedFDeriv ℝ 3 F x‖ ≤ C₀) := by
  sorry

end QuantFlatChartThree

end EllipticBernoulli

end
