# Comparator Challenges

This directory contains release comparator workspaces for the headline theorems of
`EllipticBernoulli`, following the convention of
[viscosity-solution-theory](https://github.com/willmfeldman/viscosity-solution-theory) v0.2.0.
Each subdirectory is a standalone Lake workspace with:

- `Challenge.lean` and `Challenge/*.lean`: the trusted statement surface, importing Mathlib
  modules only;
- `Solution.lean`: the solution, importing the library modules that prove the statements;
- `config.json`: comparator module names, theorem names and permitted axioms;
- `lakefile.toml` and `lake-manifest.json`: workspace metadata pinned through the parent project.

The challenges certify a selection of the library's headline statements
(`EllipticBernoulli/Statements/*`), not all of them. Left out:

- the harmonic toolkit (`Statements/Harmonic.lean`: Harnack's inequality, gradient estimates,
  the Dirichlet problem on a ball, viscosity-harmonic ⇒ harmonic, comparison principles, Weyl's
  lemma, limits of harmonic functions);
- the viscosity toolkit (`Statements/Viscosity.lean`: super/subharmonicity in `{u > 0}`,
  stability under locally uniform limits, `min`/`max`);
- De Silva's Harnack inequality for flat solutions and improvement of flatness
  (`FlatHarnackStatement`, `ImprovementStatement`), the intermediate steps of the flatness
  theorem; the flatness challenge certifies only the final theorem;
- the qualitative non-degeneracy statements (`SmallestSuperNondegStatement`,
  `DownwardNondegStatement`, `LargestSubNondeg2DStatement`), whose constants may depend on the
  solution. The quantitative forms in the `nondegeneracy` challenge imply them;
- the exterior-ball lemma with domain `B_{4s}(x₀)` (`ExteriorBallNondegStatement`). The
  challenge certifies instead the same-radius form, which is the statement of
  Abedin–Feldman–Stinson, Lemma B.2; its constant `q₀/(128 d e^{3d})` is smaller than the `B_{4s}`
  form's `q₀/(32 d e^{3d})`.

`EllipticBernoulli/Comparator.lean` restates every headline statement, including these, as a
library-side regression test.

## Vocabulary files

The project vocabulary is restated in `Challenge/*.lean`, one file per library vocabulary file,
with the library's names, the library's definitions verbatim, and the library's declaration
order:

| Challenge file | Library file | Definitions |
|---|---|---|
| `Challenge/Setting.lean` | `Basic/Setting.lean` | `E`, `posSet`, `freeBoundary`, `CompactlyContained`, `divergence` |
| `Challenge/Sobolev.lean` | `Basic/Sobolev.lean` | `HasWeakGradient`, `MemH1`, `MemH1Loc`, `energyJ`, `energyJχ`, `TendstoLpLoc`, `TendstoWeakL2` |
| `Challenge/Touching.lean` | `Basic/Touching.lean` | `TouchesBelow`, `TouchesAbove` |
| `Challenge/Viscosity.lean` | `Defs/Viscosity.lean` | viscosity super/sub/solutions (Abedin–Feldman–Stinson, Definition 2.1) and the related notions |
| `Challenge/Regularity.lean` | `Defs/Regularity.lean` | `blowup`, `IsC1GammaHypersurfaceNear`, `IsClassicalNear`, non-degeneracy, `IsClassicalSolution` |
| `Challenge/Variational.lean` | `Defs/Variational.lean` | `innerVarIntegrand`, `IsInnerVarSolution`, directional, obstacle and local energy minimizers |

Each vocabulary file drops the module-system syntax (`module`, `public`, `@[expose]`) and the
library file's theorems, and imports the same Mathlib modules as the library file. Two cautions,
both checked by `scripts/fingerprint-challenges.sh`:

- Comparator checks that every restated definition is exactly the library's. That includes the
  names of the auxiliary proofs Lean creates inside definitions (for example
  `HasWeakGradient._proof_1`), and Lean shares those only within a file. So the vocabulary is
  split along the library's file boundaries, in the library's order.
- `Challenge.lean` does **not** import all of `Mathlib`. With the whole library in scope, instance
  search can elaborate a statement differently from the library. For example, `Fintype (Fin 2)`
  inside `E 2` resolves through a `SimplexCategory` instance, and Comparator would reject the
  statement. `Challenge.lean` imports the vocabulary files, plus the Mathlib modules of the
  corresponding `Statements/*` file.

## Challenge set

| Directory | Statements (library `Statements/*`) | Library theorems used by the solution |
|---|---|---|
| `obstacle-existence` | `ObstacleExistenceStatement`, `ObstacleContinuityStatement`: existence (direct method) and continuity on all of `U` of obstacle minimizers of `J_Q`, for `Q` Lipschitz with `0 < c ≤ Q ≤ C` and `u ≥ 0` locally Lipschitz (Abedin–Feldman–Stinson, proof of Lemma 6.3) | `exists_isObstacleMinimizer`, `IsObstacleMinimizer.exists_continuousOn` |
| `energy-perturbation` | `EnergyDecreaseSuperStatement`, `EnergyDecreaseSubStatement`: energy-decreasing perturbations where the viscosity test fails, the key step of the proof of Feldman–Kim–Požár, Lemma 3.3, with their Lemma A.1 | `energy_decrease_of_not_super`, `energy_decrease_of_not_sub` |
| `viscosity-minimizers` | `OneSidedViscStatement` (upward minimizers are supersolutions, downward minimizers subsolutions, local energy minimizers solutions; Feldman–Kim–Požár, Lemma 3.3; Velichkov, Prop 7.1) and `ObstacleViscStatement` (obstacle minimizers are super/subsolutions; Abedin–Feldman–Stinson, Lemma 6.3, Steps 1–2) | `IsUpwardMinimizer.isViscSuper`, `IsDownwardMinimizer.isViscSub`, `IsLocalEnergyMinimizer.isViscSolution`, `IsObstacleMinimizer.isViscSuper_of_upper`, `IsObstacleMinimizer.isViscSub_of_lower` |
| `lipschitz-estimate` | `LipschitzEstimateStatement`, `LocalLipschitzStatement` (Caffarelli–Salsa, Lemma 11.19; the constant `C = C(d)`) | `lipschitzOnWith_of_isViscSuper`, `locallyLipschitzOn_of_isViscSuper` |
| `nondegeneracy` | `SmallestSuperNondegQuantStatement` (Caffarelli–Salsa, Lemma 6.9, `c = q₀/(8d)`), `ExteriorBallSameRadiusStatement` (Abedin–Feldman–Stinson, Lemma B.2, same radius), `NondegEquivStatement` (Lemma B.3 (i)⇔(ii)), `DownwardNondegQuantStatement` (Alt–Caffarelli, Lemma 3.4, `c = q₀/(8d e^{d/2})`), `LargestSubNondeg2DQuantStatement` (Abedin–Feldman–Stinson, Theorem B.1, after Orcan-Ekmekci, `d = 2`, `c = c(q₀, K)`, for `u` `K`-Lipschitz, `C²` and harmonic in `{u > 0}`; the statement asks for `r ≤ R/2` and a sup over the closed ball `B̄_r`, where Theorem B.1 has `0 < r ≤ R` and a sup over `∂B_r`, which is equivalent up to halving `c`) | `IsLocalSmallestSuper.exists_le_of_closedBall_subset`, `exists_le_of_exteriorBall_sameRadius`, `nondegenerate_sup_iff_average`, `IsDownwardMinimizer.exists_le_of_closedBall_subset`, `exists_pos_le_of_isLocalLargestSub` |
| `flatness-regularity` | `FlatGraphStatement`, `FlatClassicalStatement` (De Silva (2011), Theorem 1.1, with `Q` Lipschitz instead of Hölder, and the `IsClassicalNear` conclusion; `γ`, the Hölder constant and the `IsClassicalNear` radius are chosen per solution, whereas De Silva's do not depend on the solution) | `isC1GammaHypersurfaceNear_of_flat`, `isClassicalNear_of_flat` |
| `classical-solutions` | `ClassicalViscStatement`, `ClassicalInnerVarStatement`, `ClassicalLipschitzBoundStatement` (classical ⇒ viscosity; the inner-variation identity, for `Q` Lipschitz with `Q ≥ c > 0`; the gradient bound of Alt–Caffarelli, Thm 6.3 / Remark 6.4, as cited in Kriventsov–Weiss, Proposition 9.1, with a modulus depending on the Lipschitz bound) | `IsClassicalSolution.isViscSolution`, `IsClassicalSolution.integral_innerVarIntegrand_eq_zero`, `classical_lipschitz_bound` |
| `planar-classification` | `PlanarHomogeneousClassificationStatement` (after Jerison–Kamburov, §5: the case analysis in the proof of Proposition 5.3, which assumes in addition a Lipschitz, non-degenerate solution that is both viscosity and variational) | `classification_homogeneous_planar` |

In `nondegeneracy`, every constant depends only on the data (`d`, `q₀`, and `K` in the planar
case; and `L`, `c` for the equivalence `NondegEquivStatement`), never on the solution.

The statements are spelled out in full in each `Challenge.lean`; they do not refer to the
`…Statement` definitions.

## References

- F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
- H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
- L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
- D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
- W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
- D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res.
  Not. IMRN 2016, no. 19, 5922–5987; arXiv:1412.4106.
- D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131. Result numbers are those of arXiv:2306.10131v2.
- B. Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary
  problem in ℝ²: elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3–4, 937–962.
- B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.

## Toolchain

- Lean: `leanprover/lean4:v4.30.0`
- Mathlib: `v4.30.0` (`c5ea003`)
- viscosity_solns `v0.2.0` and AleksandrovDifferentiability: pinned through the parent
  `lake-manifest.json`
- Comparator: `leanprover/comparator` at `d03acab`, with lean4export `a3e35a5` and landrun
  `5ed4a3d`, pinned in `scripts/release-comparator.sh` and recorded in `formalization.yaml`

Every workspace sets `packagesDir = "../../.lake/packages"` in its `lakefile.toml` (and records
the same folder in its `lake-manifest.json`), so all eight share the root workspace's dependency
checkouts and builds. The manifests lock the same revisions as the root manifest. Each workspace
defaults to its `Challenge` target only, so a plain `lake build` never elaborates
`Solution.lean`. The workspaces set `autoImplicit = false`.

## Acceptance

In a trusted checkout, build the root library first, then the workspaces, then run the local
checks:

```sh
lake build
./scripts/check-challenges.sh
./scripts/fingerprint-challenges.sh
```

`scripts/check-challenges.sh` (run by CI) builds `Challenge` and `Solution` in every workspace and
checks that every solution theorem depends on exactly `propext`, `Classical.choice` and
`Quot.sound`. It does not compare statements. `scripts/build-challenges.sh --trusted-all` builds
the same targets without the axiom check.

`scripts/fingerprint-challenges.sh` emulates Comparator's statement and definition-equality
check. For each workspace, it hashes the types and definition values of the challenge theorems and
of every `EllipticBernoulli` constant they depend on, once in the `Challenge` environment and once
in the `Solution` environment, and diffs the results. It does not replay proofs or check axioms.

For a Comparator release run, treat `Solution.lean` as potentially adversarial, and review and
trust each workspace's `Challenge.lean`, `Challenge/*.lean`, `lakefile.toml`,
`lake-manifest.json`, `lean-toolchain` and `config.json`. The release workflow
`.github/workflows/release-comparator.yml` (dispatched by hand, and run on `release/**` branches
and `v*` tags) then:

1. validates the challenge inventory against `formalization.yaml`
   (`scripts/check-formalization-manifest.rb --metadata-only`);
2. installs the pinned Comparator tools (`scripts/release-comparator.sh install`);
3. builds only the trusted `Challenge` targets outside the sandbox;
4. runs Comparator in its sandbox on each workspace's `config.json`, without first building
   `Solution` (`scripts/release-comparator.sh run`), which checks statement and definition
   equality and that each theorem depends only on `propext`, `Classical.choice` and
   `Quot.sound`;
5. uploads an attestation (`comparator-report/attestation.json` and the logs).

**Status (2026-09-27).**
- Both build-challenges modes are green locally.
- `fingerprint-challenges.sh` reports every workspace IDENTICAL.
- `#print axioms` on each solution theorem's library counterpart (`EllipticBernoulli.Comparator`)
  shows only the three permitted axioms.
- **A Comparator run has not been made yet.** The release workflow will be run on the release
  commit, and its result recorded here.
