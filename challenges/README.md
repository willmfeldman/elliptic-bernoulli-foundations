# Comparator Challenges

This directory contains a single release comparator workspace, `main-results`, for the library's
main results. It is a standalone Lake workspace with:

- `Vocabulary/*.lean`, re-exported by `Vocabulary.lean`: the library's vocabulary restated over
  Mathlib (see below);
- `Challenge.lean`: the trusted statement surface, one section per result (see the table below).
  It imports Mathlib modules and its own `Vocabulary/*.lean` only;
- `Solution.lean`: the solution, importing the library modules that prove the statements;
- `config.json`: comparator module names, the 30 theorem names and the permitted axioms;
- `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`: workspace metadata pinned through the
  parent project.

Every `.lean` file is a Lean module.

The workspace certifies a selection of the library's headline statements
(`EllipticBernoulli/Statements/*`), not all of them. Left out:

- the harmonic toolkit (`Statements/Harmonic.lean`: Harnack's inequality, gradient estimates,
  the Dirichlet problem on a ball, viscosity-harmonic ⇒ harmonic, comparison principles, Weyl's
  lemma, limits of harmonic functions);
- the viscosity toolkit (`Statements/Viscosity.lean`: super/subharmonicity in `{u > 0}`,
  stability under locally uniform limits, `min`/`max`);
- De Silva's Harnack inequality for flat solutions and improvement of flatness
  (`FlatHarnackStatement`, `ImprovementStatement`), the intermediate steps of the flatness
  theorem; the challenge certifies only the final theorem;
- the qualitative non-degeneracy statements (`SmallestSuperNondegStatement`,
  `DownwardNondegStatement`, `LargestSubNondeg2DStatement`), whose constants may depend on the
  solution. The quantitative forms in the `Nondegeneracy` section imply them;
- the exterior-ball lemma with domain `B_{4s}(x₀)` (`ExteriorBallNondegStatement`). The
  challenge certifies instead the same-radius form, which is the statement of
  Abedin–Feldman–Stinson, Lemma B.2; its constant `q₀/(128 d e^{3d})` is smaller than the `B_{4s}`
  form's `q₀/(32 d e^{3d})`;
- global Weiss monotonicity (`WeissMonotoneStatement`) and the classification of `1`-homogeneous
  two-phase functions (`HomogeneousTwoPhaseIn`), the intermediate steps of the two-phase
  classification; the challenge certifies the final theorem, its two other inputs (the
  `FriedlandHayman` and `AcfMonotonicity` sections), and Weiss monotonicity in a ball
  (`WeissLocal`);
- the classification of global two-phase minimizers in dimensions `d ≤ 4` with the explicit
  low-dimensional Friedland–Hayman inequality, which the every-dimension statement implies.

`EllipticBernoulli/Comparator.lean` restates every headline statement, including these, as a
library-side regression test.

## Vocabulary files

The project vocabulary is restated with the library's names, the library's definitions verbatim,
and the library's declaration order, one part per library vocabulary file:

| Vocabulary part | Library file | Definitions |
|---|---|---|
| `Setting` | `Basic/Setting.lean` | `E`, `posSet`, `freeBoundary`, `CompactlyContained`, `divergence` |
| `Sobolev` | `Basic/Sobolev.lean` | `HasWeakGradient`, `MemH1`, `MemH1Loc`, `energyJ`, `energyJχ`, `TendstoLpLoc`, `TendstoWeakL2` |
| `Touching` | `Basic/Touching.lean` | `TouchesBelow`, `TouchesAbove` |
| `Viscosity` | `Defs/Viscosity.lean` | viscosity super/sub/solutions (Abedin–Feldman–Stinson, Definition 2.1) and the related notions |
| `Regularity` | `Defs/Regularity.lean` | `blowup`, `IsC1GammaHypersurfaceNear`, `IsClassicalNear`, non-degeneracy, `IsClassicalSolution` |
| `Variational` | `Defs/Variational.lean` | `innerVarIntegrand`, `IsInnerVarSolution`, directional, obstacle and local energy minimizers |
| `TwoPhase` | `Defs/TwoPhase.lean` | eigenvalues and characteristic exponents on the sphere (`sphEigenvalue`, `charExponent`, `sphExponent`) and on caps, the ACF functional (`acfIntegral`, `acfPhi`) and `IsACFPair`, the Weiss functional and defect, `twoPlane` |

Each part drops the library file's theorems and imports the same Mathlib modules as the library
file. `Challenge.lean` imports the vocabulary modules (it is marked
`challenge-prep: split vocabulary`, so `scripts/challenge-prep.py sync` leaves it alone and
`scripts/challenge-prep.py check` checks its imports). Two cautions, both checked by
`scripts/fingerprint-challenges.sh`:

- Comparator checks that every restated definition is exactly the library's. That includes the
  names of the auxiliary proofs Lean creates inside definitions (for example
  `HasWeakGradient._proof_1`), and Lean shares those within a module. Merged into one file, later
  definitions reuse earlier auxiliary proofs where the library has its own. So the workspace
  keeps its vocabulary split along the library's module boundaries, as `Vocabulary/*.lean`.
- The challenge statements do **not** import all of `Mathlib`. With the whole library in scope,
  instance search can elaborate a statement differently from the library. For example,
  `Fintype (Fin 2)` inside `E 2` resolves through a `SimplexCategory` instance, and Comparator
  would reject the statement. The workspace imports the vocabulary's Mathlib modules, plus those
  of the `Statements/*` files it restates.

## Challenge set

| Section of `Challenge.lean` | Statements (library `Statements/*`) | Library theorems used by the solution |
|---|---|---|
| `ObstacleExistence` | `ObstacleExistenceStatement`, `ObstacleContinuityStatement`: existence (direct method) and continuity on all of `U` of obstacle minimizers of `J_Q`, for `Q` Lipschitz with `0 < c ≤ Q ≤ C` and `u ≥ 0` locally Lipschitz (Abedin–Feldman–Stinson, proof of Lemma 6.3) | `exists_isObstacleMinimizer`, `IsObstacleMinimizer.exists_continuousOn` |
| `EnergyPerturbation` | `EnergyDecreaseSuperStatement`, `EnergyDecreaseSubStatement`: energy-decreasing perturbations where the viscosity test fails, the key step of the proof of Feldman–Kim–Požár, Lemma 3.3, with their Lemma A.1 | `energy_decrease_of_not_super`, `energy_decrease_of_not_sub` |
| `ViscosityMinimizers` | `OneSidedViscStatement` (upward minimizers are supersolutions, downward minimizers subsolutions, local energy minimizers solutions; Feldman–Kim–Požár, Lemma 3.3; Velichkov, Prop 7.1) and `ObstacleViscStatement` (obstacle minimizers are super/subsolutions; Abedin–Feldman–Stinson, Lemma 6.3, Steps 1–2) | `IsUpwardMinimizer.isViscSuper`, `IsDownwardMinimizer.isViscSub`, `IsLocalEnergyMinimizer.isViscSolution`, `IsObstacleMinimizer.isViscSuper_of_upper`, `IsObstacleMinimizer.isViscSub_of_lower` |
| `EnergyMinimizerRegularity` | `EnergyMinimizerRegularityStatement`: a local minimizer `u ≥ 0` of `J_Q`, for `Q` continuous with `0 ≤ Q ≤ C`, has an a.e.-equal representative which is a local minimizer, locally Lipschitz and non-negative, with open positivity set on which it is `C^∞` and harmonic (Alt–Caffarelli, §§2–3; Velichkov, Ch. 3 and Prop 7.1; continuity by De Giorgi's method) | `IsLocalEnergyMinimizer.exists_regular_representative` |
| `LipschitzEstimate` | `LipschitzEstimateStatement`, `LocalLipschitzStatement` (Caffarelli–Salsa, Lemma 11.19; the constant `C = C(d)`) | `lipschitzOnWith_of_isViscSuper`, `locallyLipschitzOn_of_isViscSuper` |
| `Nondegeneracy` | `SmallestSuperNondegQuantStatement` (Caffarelli–Salsa, Lemma 6.9, `c = q₀/(8d)`), `ExteriorBallSameRadiusStatement` (Abedin–Feldman–Stinson, Lemma B.2, same radius), `NondegEquivStatement` (Lemma B.3 (i)⇔(ii)), `DownwardNondegQuantStatement` (Alt–Caffarelli, Lemma 3.4, `c = q₀/(8d e^{d/2})`), `LargestSubNondeg2DQuantStatement` (Abedin–Feldman–Stinson, Theorem B.1, after Orcan-Ekmekci, `d = 2`, `c = c(q₀, K)`, for `u` `K`-Lipschitz, `C²` and harmonic in `{u > 0}`; the statement asks for `r ≤ R/2` and a sup over the closed ball `B̄_r`, where Theorem B.1 has `0 < r ≤ R` and a sup over `∂B_r`, which is equivalent up to halving `c`) | `IsLocalSmallestSuper.exists_le_of_closedBall_subset`, `exists_le_of_exteriorBall_sameRadius`, `nondegenerate_sup_iff_average`, `IsDownwardMinimizer.exists_le_of_closedBall_subset`, `exists_pos_le_of_isLocalLargestSub` |
| `FlatnessRegularity` | `FlatGraphStatement`, `FlatClassicalStatement` (De Silva (2011), Theorem 1.1, with `Q` Lipschitz instead of Hölder, and the `IsClassicalNear` conclusion; `γ`, the Hölder constant and the `IsClassicalNear` radius are chosen per solution, whereas De Silva's do not depend on the solution) | `isC1GammaHypersurfaceNear_of_flat`, `isClassicalNear_of_flat` |
| `FlatChart` | `FlatChartStatement`: at a free-boundary point of a continuous local minimizer `u ≥ 0` of `J_1` (`d ≥ 2`) at which the half-plane solution `(y · e)₊` is a blow-up limit, `u = max(F, 0)` near the point for a `C^∞` function `F` with `∇F ≠ 0`, harmonic where positive, with `|∇F| = 1` on `{F = 0}` (Kinderlehrer–Nirenberg's partial hodograph transform; De Silva (2011) for the `C^{1,γ}` step; Seeley's extension) | `flat_chart` |
| `ClassicalSolutions` | `ClassicalViscStatement`, `ClassicalInnerVarStatement`, `ClassicalLipschitzBoundStatement` (classical ⇒ viscosity; the inner-variation identity, for `Q` Lipschitz with `Q ≥ c > 0`; the gradient bound of Alt–Caffarelli, Thm 6.3 / Remark 6.4, as cited in Kriventsov–Weiss, Proposition 9.1, with a modulus depending on the Lipschitz bound) | `IsClassicalSolution.isViscSolution`, `IsClassicalSolution.integral_innerVarIntegrand_eq_zero`, `classical_lipschitz_bound` |
| `FriedlandHayman` | `FriedlandHaymanStatement`: for `d ≥ 2` and nonempty, relatively open, disjoint `Γ₁, Γ₂ ⊆ 𝕊^{d-1}`, `α_d(Γ₁) + α_d(Γ₂) ≥ 2`, with eigenvalues over chordally Lipschitz trial functions (Friedland–Hayman; Beck–Jerison, Theorem 1.1) | `friedlandHayman` |
| `AcfMonotonicity` | `ACFMonotoneIn d` for every `d ≥ 2`, with no Friedland–Hayman hypothesis: for `u₁, u₂ ≥ 0` `L`-Lipschitz, harmonic in their positivity sets, with `u₁ u₂ ≡ 0` and `u₁(x₀) = u₂(x₀) = 0`, `r ↦ r⁻⁴ I(u₁) I(u₂)` is nondecreasing on `(0, ∞)` (Alt–Caffarelli–Friedman; Salato, Theorem 1.1). The hypotheses are written out rather than bundled as `IsACFPair` | `acfMonotoneIn` |
| `TwoPhaseClassification` | `TwoPhaseClassificationStatement`: in every dimension, a Lipschitz local minimizer of `∫ \|∇v\|² + 1_{v>0}` on `ℝᵈ` that takes a positive and a negative value is `a (x·e + c)⁺ - b (x·e + c)⁻` with `‖e‖ = 1`, `a, b > 0`, `a² - b² = 1` (after Alt–Caffarelli–Friedman). The conclusion is written out rather than through `twoPlane` | `twoPhaseClassification` |
| `WeissLocal` | `WeissMonotoneLocalStatement`: Weiss monotonicity in a ball `B_R(x₀) ⊆ U` for a local minimizer of `∫ \|∇v\|² + 1_{v>0}` in an open `U` that is Lipschitz on the ball and vanishes at `x₀`: `W(s) - W(r) ≥ D(r, s) ≥ 0`, the uniform bound on `\|W\|`, and rigidity: `W(r) = W(s)` forces `1`-homogeneity about `x₀` on the annulus (Weiss (1999)) | `weissMonotoneLocal` |
| `QuantFlatChart` | `QuantFlatChartStatement`: for `d ≥ 2` there are `ε₀, α, C > 0` such that a continuous local minimizer `u ≥ 0` of `J_1` in `B_1` that is `ε`-close to `(x · e)₊` (`ε ≤ ε₀`) is `max(F, 0)` on `B_{1/2}` for a `C^∞` function `F` with `\|∇F\| = 1` on `{F = 0}`, harmonic where positive, and, on `{F ≥ 0} ∩ B_{1/2}`, `∇F · e ≥ 1/2`, `\|∇F\|, \|D²F\| ≤ C` and `D²F` `α`-Hölder with constant `C` | `quantFlatChart` |
| `QuantFlatChartThree` | `QuantFlatChartThreeStatement`: the same chart on `B_{1/4}`, with `∇F · e ≥ 1/2` and `\|D³F\| ≤ C₀` on `{F ≥ 0} ∩ B_{1/4}` | `quantFlatChartThree` |
| `PlanarClassification` | `PlanarHomogeneousClassificationStatement` (after Jerison–Kamburov, §5: the case analysis in the proof of Proposition 5.3, which assumes in addition a Lipschitz, non-degenerate solution that is both viscosity and variational) | `classification_homogeneous_planar` |

In the `Nondegeneracy` section, every constant depends only on the data (`d`, `q₀`, and `K` in the planar
case; and `L`, `c` for the equivalence `NondegEquivStatement`), never on the solution.

The statements are spelled out in full in `Challenge.lean`; they do not refer to the
`…Statement` definitions.

## References

- F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
- H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
- H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
- T. Beck, D. Jerison, *The Friedland–Hayman inequality and Caffarelli's contraction theorem*,
  arXiv:2102.00571.
- L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
- D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
- W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
- S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
- D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res.
  Not. IMRN 2016, no. 19, 5922–5987; arXiv:1412.4106.
- D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
- D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131. Result numbers are those of arXiv:2306.10131v2.
- B. Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary
  problem in ℝ²: elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3–4, 937–962.
- E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473.
- R. T. Seeley, *Extension of `C^∞` functions defined in a half space*, Proc. Amer. Math. Soc. 15
  (1964), 625–626.
- B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
- G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.

## Toolchain

- Lean: `leanprover/lean4:v4.36.0`
- Mathlib: `v4.36.0` (`fc4f59e`)
- viscosity_solns `v0.5.0`, AleksandrovDifferentiability `v0.5.0` and basic_elliptic_theory
  `v0.2.1`: pinned through the parent `lake-manifest.json`
- Comparator: the toolchain's `lake comparator` (recorded as `engine: "lake comparator"` in
  `formalization.yaml`), so the Lean toolchain pin is also the comparator pin. The release run
  uses `--paranoid`, which also replays the proofs with every checker shipped in the toolchain.

The workspace sets `packagesDir = "../../.lake/packages"` in its `lakefile.toml` (and records
the same folder in its `lake-manifest.json`), so it shares the root workspace's dependency
checkouts and builds. Its manifest locks the same revisions as the root manifest. It defaults to
its `Vocabulary` and `Challenge` targets only, so a plain `lake build` never elaborates
`Solution.lean`. It sets `autoImplicit = false`.

## Acceptance

In a trusted checkout, build the root library first, then the workspace, then run the local
checks:

```sh
lake build
./scripts/check-challenges.sh
./scripts/fingerprint-challenges.sh
```

`scripts/check-challenges.sh` (run by CI) builds `Vocabulary`, `Challenge` and `Solution` in the workspace and
checks that every solution theorem depends on exactly `propext`, `Classical.choice` and
`Quot.sound`. It does not compare statements. `scripts/build-challenges.sh --trusted-all` builds
the same targets without the axiom check.

`scripts/fingerprint-challenges.sh` emulates Comparator's statement and definition-equality
check. It hashes the types and definition values of the challenge theorems and
of every `EllipticBernoulli` constant they depend on, once in the `Challenge` environment and once
in the `Solution` environment, and diffs the results. It does not replay proofs or check axioms.

For a Comparator release run, treat `Solution.lean` as potentially adversarial, and review and
trust the workspace's `Vocabulary.lean`, `Vocabulary/*.lean`, `Challenge.lean`, `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain` and `config.json`. The release workflow
`.github/workflows/release-comparator.yml` (dispatched by hand, and run on `release/**` branches) then:

1. validates the challenge inventory against `formalization.yaml`
   (`scripts/check-formalization-manifest.rb --metadata-only`);
2. prepares the comparator sandbox: bubblewrap, with unprivileged user namespaces allowed
   (`scripts/release-comparator.sh install`);
3. builds only the trusted `Vocabulary` and `Challenge` targets outside the sandbox;
4. runs `lake comparator --paranoid` in its bubblewrap sandbox on the workspace's `config.json`,
   without first building `Solution` (`scripts/release-comparator.sh run`), which checks statement and definition
   equality and that each theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`;
5. uploads an attestation (`comparator-report/attestation.json` and the logs).

**Status (2026-11-24).**
- Both build-challenges modes are green locally.
- `fingerprint-challenges.sh` reports the workspace IDENTICAL (407 constants).
- `#print axioms` on each solution theorem's library counterpart (`EllipticBernoulli.Comparator`)
  shows only the three permitted axioms.
- Each release is checked by a Comparator run on the public commit, and its attestation is
  attached to the GitHub release.
