# elliptic-bernoulli-foundations

`EllipticBernoulli` is a Lean 4 / Mathlib formalization of foundational results for the elliptic one-phase
Bernoulli free boundary problem

  Δu = 0 in {u > 0},   |∇u| = Q(x) on ∂{u > 0},

with a variable coefficient 0 < Qmin ≤ Q ≤ Qmax. It covers:
- obstacle problems for the Alt–Caffarelli energy `J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}`;
- energy-decreasing perturbations and one-sided minimizers;
- the Lipschitz estimate;
- non-degeneracy;
- De Silva's flatness theory, up to classical regularity;
- classical solutions;
- the classification of planar 1-homogeneous inner variational solutions.

The library has about 33,000 lines of Lean. Every file is a Lean module, and everything lives in the namespace
`EllipticBernoulli`. It is sorry-free, and the headline theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Headline theorems

Each headline is a `…Statement : Prop` in `EllipticBernoulli/Statements/*`, proved by the theorem listed.
`EllipticBernoulli/Comparator.lean` restates all of them as a regression surface. The source keys are expanded under
[References](#references), and result numbers are those of the cited version. `formalization.yaml` states the
certified results in words.

| Result | Source | Lean theorem |
|---|---|---|
| Existence for the obstacle problem (direct method) | Abedin–Feldman–Stinson, Lemma 6.3 | `exists_isObstacleMinimizer` |
| Continuity of obstacle minimizers on all of `U`, for `u ≥ 0` locally Lipschitz (De Giorgi; the interior argument is new) | Abedin–Feldman–Stinson, Lemma 6.3 | `IsObstacleMinimizer.exists_continuousOn` |
| Energy-decreasing perturbations | Feldman–Kim–Požár, proof of Lemma 3.3; Lemma A.1 | `energy_decrease_of_not_super`, `energy_decrease_of_not_sub` |
| One-sided and energy minimizers are viscosity super/sub/solutions | Feldman–Kim–Požár, Lemma 3.3; Velichkov, Prop 7.1 | `IsUpwardMinimizer.isViscSuper`, `IsDownwardMinimizer.isViscSub`, `IsLocalEnergyMinimizer.isViscSolution` |
| Obstacle minimizers are super/subsolutions off the obstacle | Abedin–Feldman–Stinson, Lemma 6.3 | `IsObstacleMinimizer.isViscSuper_of_upper`, `IsObstacleMinimizer.isViscSub_of_lower` |
| Lipschitz estimate for viscosity supersolutions | Caffarelli–Salsa, Lemma 11.19 | `lipschitzOnWith_of_isViscSuper`, `locallyLipschitzOn_of_isViscSuper` |
| Non-degeneracy of local smallest supersolutions | Caffarelli–Salsa, Lemma 6.9 | `IsLocalSmallestSuper.isUniformlyNondegenerateNear` |
| Non-degeneracy of local smallest supersolutions on every ball `B̄_r(z) ⊆ U`, `c = q₀/(8d)` | Caffarelli–Salsa, Lemma 6.9 | `IsLocalSmallestSuper.exists_le_of_closedBall_subset` |
| Exterior-ball non-degeneracy (domain `B_{4s}`) | variant of Abedin–Feldman–Stinson, Lemma B.2 | `exists_le_of_exteriorBall` |
| Exterior-ball non-degeneracy, domain and exterior ball of the same radius, `c = q₀/(128 d e^{3d})` | Abedin–Feldman–Stinson, Lemma B.2 | `exists_le_of_exteriorBall_sameRadius` |
| Sphere-average ⇔ sphere-sup non-degeneracy | Abedin–Feldman–Stinson, Lemma B.3 (i)⇔(ii) | `nondegenerate_sup_iff_average` |
| Non-degeneracy of downward minimizers | Alt–Caffarelli, Lemma 3.4 | `IsDownwardMinimizer.isUniformlyNondegenerateNear` |
| Non-degeneracy of downward minimizers on every ball `B̄_r(z) ⊆ U`, `c = q₀/(8d e^{d/2})` | Alt–Caffarelli, Lemma 3.4 | `IsDownwardMinimizer.exists_le_of_closedBall_subset` |
| Non-degeneracy of local largest subsolutions, `d = 2`, for `u` `K`-Lipschitz, `C²` and harmonic in `{u > 0}` | Abedin–Feldman–Stinson, Theorem B.1 (after Orcan-Ekmekci) | `isNondegenerateAt_of_isLocalLargestSub` |
| The same with a constant `c = c(q₀, K)` chosen before `u` | Abedin–Feldman–Stinson, Theorem B.1 (after Orcan-Ekmekci) | `exists_pos_le_of_isLocalLargestSub` |
| Harnack inequality for flat solutions; improvement of flatness | De Silva (2011), Theorem 3.1, Lemma 4.1 | `flat_harnack`, `improvement_of_flatness` |
| Flatness ⇒ `C^{1,γ}` free boundary, and classical near the point | De Silva (2011), Theorem 1.1 | `isC1GammaHypersurfaceNear_of_flat`, `isClassicalNear_of_flat` |
| Classical solutions are viscosity solutions | — | `IsClassicalSolution.isViscSolution` |
| Inner-variation identity for classical solutions | Kriventsov–Weiss, remark after Definition 9.1 | `IsClassicalSolution.integral_innerVarIntegrand_eq_zero` |
| Alt–Caffarelli gradient bound (modulus depending on `L`) | Alt–Caffarelli, Thm 6.3 / Remark 6.4; Kriventsov–Weiss, Proposition 9.1 | `classical_lipschitz_bound` |
| Planar 1-homogeneous inner variational solutions | after Jerison–Kamburov, §5 (case analysis in the proof of Prop 5.3) | `classification_homogeneous_planar` |
| Harmonic and viscosity toolkits: Harnack, gradient estimates, Dirichlet problem on a ball, Weyl's lemma, harmonic limits, comparison, stability, lattice operations | standard | see `EllipticBernoulli/Statements/{Harmonic,Viscosity}.lean` |

## Deviations from the sources

Where a statement deviates from its source, its docstring says so. The main deviations:
- The energy is `∫|∇u|² + Q² 1_{u>0}`, so the free boundary condition is `|∇u| = Q`. Feldman–Kim–Požár write
  `∫|∇u|² + Q 1_{u>0}` with `|∇u|² = Q`. Since the energy sees only `Q²`, "upward minimizers are supersolutions"
  and "energy minimizers are viscosity solutions" need `Q ≥ 0` here.
- De Silva allows a Hölder coefficient; here `Q` is Lipschitz.
- Kriventsov–Weiss state the gradient bound with a modulus depending only on the dimension, citing Alt–Caffarelli,
  Theorem 6.3, which is proved for Alt–Caffarelli's weak solutions; classical solutions need not be such (`u = |x_d|`
  is classical). Here the modulus may depend on the Lipschitz bound `L`, and the proof is the blow-up argument of
  Alt–Caffarelli, Remark 6.4, made uniform over the class.
- The planar classification has three alternatives: a half-plane solution, a two-plane solution `α |x · e|` with
  `χ = 1` a.e. (`α = 0` allowed), and `v ≡ 0` with `χ = 0` a.e. Jerison–Kamburov, Propositions 5.3 and 5.4,
  classify blow-ups under stronger hypotheses (a Lipschitz, non-degenerate solution that is both viscosity and
  variational, with `χ = 1_{u>0}`). Those hypotheses exclude `v ≡ 0` and bound the two-plane coefficient; the Lean
  theorem follows the case analysis in the proof of Proposition 5.3.
- Abedin–Feldman–Stinson state Theorem B.1 for largest subsolutions with no further hypotheses. Here `u` is also
  assumed `K`-Lipschitz, `C²` and harmonic in `{u > 0}`. The Lean statement asks for `r ≤ R/2` and a sup over the
  closed ball `B̄_r`, where Theorem B.1 has `0 < r ≤ R` and a sup over `∂B_r`; the two forms are equivalent up to
  halving the constant.
- The qualitative non-degeneracy and flatness statements have constants that may depend on the solution. The
  quantitative non-degeneracy statements have constants depending only on the data.

## Verification

- **No `sorry`.** The library contains no `sorry`, `admit`, `native_decide` or `axiom` declaration. CI scans the
  sources with comments and strings masked.
- **Axioms.** Each declaration listed in `formalization.yaml` depends on exactly `propext`, `Classical.choice` and
  `Quot.sound`. CI checks this with `#print axioms` (`scripts/check-formalization-manifest.rb`).
- **No assumed literature results.** `EllipticBernoulli/Registry/`, the place for results assumed without proof,
  contains none.
- **CI.** `.github/workflows/ci.yml` runs on every push and pull request. It:
  - fetches the Mathlib cache, and builds the library and the `EllipticBernoulliComparator` target, treating warnings
    as errors;
  - scans the library sources (comments and strings masked) for `sorry`, `admit`, `axiom` and `native_decide`;
  - checks that no library file reaches 1000 lines and that every file is a Lean module
    (`scripts/check_integrity.py`);
  - validates `formalization.yaml`: every Lean name resolves, each target depends on exactly the three axioms above,
    and the challenge inventory matches `challenges/*/config.json` (`scripts/check-formalization-manifest.rb`);
  - checks the challenge vocabulary files and solutions for `sorry`, `axiom`, `admit` and `native_decide`;
  - elaborates every challenge workspace and checks the axioms of every solution theorem
    (`scripts/check-challenges.sh`).

## Comparator challenges

`challenges/` holds eight standalone [Comparator](https://github.com/leanprover/comparator) workspaces. They restate
a selection of the headline statements over Mathlib only, and `formalization.yaml` lists them. In each,
`Challenge/*.lean` restates the library's definitions over Mathlib, `Challenge.lean` states the theorems with
`sorry`, and `Solution.lean` proves them from the library. See [`challenges/README.md`](challenges/README.md) for the
challenge set, what is left out, and the acceptance procedure.
- Ordinary CI only elaborates these files. Exact statement and definition equality, and the permitted-axiom check,
  are established by the release workflow `.github/workflows/release-comparator.yml`
  (`scripts/release-comparator.sh`). It runs Comparator with pinned tool revisions and uploads an attestation.
- `scripts/build-challenges.sh --trusted-all` builds the workspaces locally (`--challenge-only` never elaborates the
  untrusted `Solution.lean` files).
- `scripts/fingerprint-challenges.sh` emulates Comparator's statement and definition-equality check locally. It
  reports every workspace identical.
- Each release is checked by a Comparator run on the public commit, and the attestation is attached to the
  GitHub release.

## Building

The toolchain and dependencies are pinned in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`:
- Lean `v4.34.1`;
- Mathlib `v4.34.1` (commit `d13f23b`),
  [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4);
- viscosity-solution-theory `v0.3.0` (Lake package `viscosity_solns`, commit `067e254`),
  [willmfeldman/viscosity-solution-theory](https://github.com/willmfeldman/viscosity-solution-theory). It is used
  only in `EllipticBernoulli/Harmonic/`. It pulls in aleksandrov-differentiability `v0.3.0` (commit `6b31824`),
  [willmfeldman/aleksandrov-differentiability](https://github.com/willmfeldman/aleksandrov-differentiability),
  which this library does not import directly.

Lake fetches both from their public Git repositories at the release tags and downloads each release's prebuilt build
archive when one is available for your platform; otherwise it builds them from source. Releases of this library
likewise carry prebuilt build archives (Linux x86-64 and macOS arm64), which Lake downloads for projects that require
it at a release tag.

The other packages in `lake-manifest.json` (batteries, aesop, Qq, ProofWidgets, plausible, LeanSearchClient,
import-graph, lean4-cli) are Mathlib's own dependencies. All dependencies are Apache-2.0.

```bash
lake exe cache get
lake build
```

`lake build` builds the root module `EllipticBernoulli`, which imports every module of the library.
`lake build EllipticBernoulliComparator` builds the regression target `EllipticBernoulli/Comparator.lean`.

## Using the library

- **Definitions** (`E d`, `posSet`, `freeBoundary`, `IsViscSolution`, `MemH1Loc`, `energyJ`, …) live in
  `EllipticBernoulli/Basic/` and `EllipticBernoulli/Defs/`.
  - Energies are `ℝ≥0∞`-valued lower integrals, and weak gradients are carried as data.
  - The free boundary condition is `|∇u| = Q`.
- **Copying files.** Files are small and self-contained, with few internal imports.
  - The library uses the Lean module system. A non-module project copying a file must strip `module`, the `public`
    import modifiers, `@[expose]`, and `public section` (replace it with `section`). This is mechanical.
  - Keep the attribution header, and see [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md).

## Layout

| Path | Contents |
|---|---|
| `EllipticBernoulli/Common/`, `Basic/`, `Defs/` | Vocabulary: setting, Sobolev notions and energies, viscosity, regularity and variational notions |
| `EllipticBernoulli/Statements/` | Headline statements |
| `EllipticBernoulli/Harmonic/`, `Viscosity/`, `Sobolev/` | Toolkits |
| `EllipticBernoulli/Variational/`, `Regularity/` | Direct method, De Giorgi continuity, perturbations, one-sided minimizers |
| `EllipticBernoulli/Lipschitz/`, `Nondegeneracy/` | Lipschitz estimate, non-degeneracy |
| `EllipticBernoulli/Flatness/` | De Silva's theory |
| `EllipticBernoulli/Classical/` | Classical solutions |
| `EllipticBernoulli/Blowup/` | Planar classification |
| `EllipticBernoulli/Registry/` | Reserved for results assumed without proof (empty) |
| `EllipticBernoulli/Comparator.lean` | Regression restatement of every headline statement |
| `challenges/`, `formalization.yaml` | Comparator workspaces and the theorem manifest |
| `scripts/` | Integrity, manifest, challenge, fingerprint and release-comparator checks used by CI and the release workflow |

## References

- F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in the Bernoulli
  one-phase problem*, arXiv:2609.14981.
- H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*, J. Reine Angew.
  Math. 325 (1981), 105–144.
- L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math. 68, Amer. Math.
  Soc., 2005.
- D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound. 13 (2011),
  no. 2, 223–238; arXiv:0912.2057.
- W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*, Calc. Var. Partial
  Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656. Result numbers are those of
  arXiv:2310.03656v2.
- D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res. Not. IMRN 2016,
  no. 19, 5922–5987; arXiv:1412.4106.
- D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for non-minimizing
  Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591; arXiv:2306.10131. Result numbers
  are those of arXiv:2306.10131v2.
- B. Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary problem in ℝ²:
  elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3–4, 937–962.
- B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione Matematica Italiana 28,
  Springer, 2023.

Standard results in the toolkits are cited by short key in the docstrings:
- H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Universitext, Springer, New
  York, 2011.
- L. C. Evans, *Partial Differential Equations*, 2nd ed., Grad. Stud. Math. 19, Amer. Math. Soc., 2010.
- L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised ed., CRC Press, 2015.
- M. Giaquinta, *Multiple Integrals in the Calculus of Variations and Nonlinear Elliptic Systems*, Ann. of Math. Stud.
  105, Princeton Univ. Press, 1983.
- M. Giaquinta, E. Giusti, *Quasi-minima*, Ann. Inst. H. Poincaré Anal. Non Linéaire 1 (1984), no. 2, 79–107.
- D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics in Mathematics,
  Springer, 2001 (reprint of the 1998 edition).
- H. Hanche-Olsen, H. Holden, *The Kolmogorov–Riesz compactness theorem*, Expo. Math. 28 (2010), no. 4, 385–394.

## Credits

Some files contain code adapted from other Apache-2.0 Lean projects: TauCeti
(<https://github.com/TauCetiProject/TauCeti>) and EllipticPDE
(<https://github.com/alejandro-soto-franco/EllipticPDE>). Each such file keeps the upstream copyright line and has a
`## Provenance` section. [`THIRD_PARTY_NOTICES.md`](THIRD_PARTY_NOTICES.md) lists them.

The Lean proofs were written by AI coding agents (Claude, by Anthropic) under the author's mathematical direction and
review. The theorem statements and proof routes were reviewed by the author. Correctness rests on Lean's kernel
check, together with the comparator challenges in `challenges/`.

## Citation

If you use this formalization, please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0 ([LICENSE](LICENSE)). Adapted third-party code is listed in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
