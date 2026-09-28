# Third-party code

This project is released under the Apache License 2.0 (`LICENSE`).
- **Adapted files.** Some files contain code adapted from other Apache-2.0 Lean projects. Each keeps the upstream
  copyright holder in its header's copyright line. Its module docstring has a `## Provenance` section that names the
  upstream file and commit and says what was changed (Apache-2.0 §4).

| Upstream | License | Upstream copyright | Files here |
|---|---|---|---|
| EllipticPDE, https://github.com/alejandro-soto-franco/EllipticPDE (commit eaf821d31b200bb6ea235f19eecc50cf0f38c294) | Apache-2.0 | © 2026 Alejandro Soto Franco | `EllipticBernoulli/Sobolev/Mollify.lean`, `EllipticBernoulli/Sobolev/Lattice.lean` (adapted) |
| TauCeti, https://github.com/TauCetiProject/TauCeti (commit 91f66a0514e6523efdccddb9e35fb82c96dd6405) | Apache-2.0 | © 2026 The Tau Ceti contributors | `EllipticBernoulli/Sobolev/BallAverage.lean`, `EllipticBernoulli/Sobolev/FrechetKolmogorov.lean` (ported/adapted) |
| TauCeti, https://github.com/TauCetiProject/TauCeti (commit 90cca67c0c8e91cd30b0d46cb58101f8c5c59236) | Apache-2.0 | © 2026 The Tau Ceti contributors | `EllipticBernoulli/Harmonic/Basic.lean` (Green's identity, weak harmonicity), `EllipticBernoulli/Harmonic/MeanValue.lean` (ball mean value, nested-ball comparison), `EllipticBernoulli/Harmonic/Harnack.lean` (local Harnack inequality) (adapted) |
| TauCeti, https://github.com/TauCetiProject/TauCeti (commit 91f66a0514e6523efdccddb9e35fb82c96dd6405) | Apache-2.0 | © 2026 The Tau Ceti contributors | `EllipticBernoulli/Flatness/LinearizedRegularity.lean` (`iteratedFDeriv_comp_linearIsometryEquiv_apply`, `laplacian_comp_linearIsometryEquiv`; adapted; via viscosity-solution-theory v0.2.0 `ViscositySolns/Applications/Laplace/Weyl/LaplacianInvariance.lean`, commit 3a93109) |

Everything else is original to this project. It uses these Lake dependencies as ordinary libraries, with no code
copied:
- Mathlib;
- viscosity-solution-theory (https://github.com/willmfeldman/viscosity-solution-theory, v0.2.0), which pulls in
  aleksandrov-differentiability.

All are Apache-2.0.
