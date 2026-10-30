/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.TwoPhase

/-!
# Headline statements: the two-phase problem

* `FriedlandHaymanIn d`, `FriedlandHaymanStatement`: the Friedland–Hayman inequality
  `α_d(Γ₁) + α_d(Γ₂) ≥ 2` for disjoint nonempty open `Γ₁, Γ₂ ⊆ 𝕊^{d-1}`.
* `ACFMonotoneIn d`: the Alt–Caffarelli–Friedman monotonicity formula for an ACF pair. It is stated
  without the Friedland–Hayman inequality; the theorem proving it takes `FriedlandHaymanIn d` as a
  hypothesis.
* `WeissMonotoneStatement`: Weiss monotonicity, in integrated form, for sign-changing local
  minimizers of `J(u, B) = ∫_B |∇u|² + 1_{u > 0}`.
* `HomogeneousTwoPhaseIn d`: a Lipschitz, `1`-homogeneous function, harmonic in both phases, with
  both phases nonempty, is a two-plane function.
* `TwoPhaseClassificationStatement`: global Lipschitz local minimizers of `J` that change sign are
  two-plane functions `a (x·e + c)⁺ - b (x·e + c)⁻` with `a² - b² = 1`.

The `…In d` statements carry no dimension hypothesis; the theorems proving them assume `2 ≤ d`.
`TwoPhaseClassificationStatement` covers every dimension. The sources work with continuous
functions, `H¹₀` trial functions and distributional subharmonicity; here the functions are
Lipschitz (see `Defs/TwoPhase.lean`).

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* T. Beck, D. Jerison, *The Friedland–Hayman inequality and Caffarelli's contraction theorem*,
  arXiv:2102.00571.
* G. De Philippis, L. Spolaor, B. Velichkov, *Regularity of the free boundary for the two-phase
  Bernoulli problem*, Invent. Math. 225 (2021), 347–394; arXiv:1911.02165.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473.
* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.
-/

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

@[expose] public section

namespace EllipticBernoulli

/-! ### Friedland–Hayman -/

/-- **Friedland–Hayman inequality** in `𝕊^{d-1}` (Friedland–Hayman 1976; Beck–Jerison,
arXiv:2102.00571, Theorem 1.1, for homogeneous harmonic functions): for nonempty, relatively open,
disjoint `Γ₁, Γ₂ ⊆ 𝕊^{d-1}`, `α_d(Γ₁) + α_d(Γ₂) ≥ 2`. The exponents use Lipschitz trial
functions (`sphEigenvalue`). -/
def FriedlandHaymanIn (d : ℕ) : Prop :=
  ∀ Γ₁ Γ₂ : Set (sphere (0 : E d) 1), IsOpen Γ₁ → IsOpen Γ₂ → Γ₁.Nonempty → Γ₂.Nonempty →
    Disjoint Γ₁ Γ₂ → 2 ≤ sphExponent Γ₁ + sphExponent Γ₂

/-- **Friedland–Hayman inequality** in every dimension `d ≥ 2`. -/
def FriedlandHaymanStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → FriedlandHaymanIn d

/-! ### Alt–Caffarelli–Friedman -/

/-- **Alt–Caffarelli–Friedman monotonicity** (Alt–Caffarelli–Friedman 1984; Salato,
arXiv:2506.13473, Theorem 1.1): for an ACF pair `(u₁, u₂)` at `x₀`, `r ↦ Φ(u₁, u₂, x₀, r)` is
nondecreasing on `(0, ∞)`. The theorem proving it assumes `2 ≤ d` and `FriedlandHaymanIn d`. -/
def ACFMonotoneIn (d : ℕ) : Prop :=
  ∀ (u₁ u₂ : E d → ℝ) (x₀ : E d) (L : ℝ≥0), IsACFPair u₁ u₂ x₀ L →
    MonotoneOn (fun r ↦ acfPhi u₁ u₂ x₀ r) (Ioi 0)

/-! ### Weiss -/

/-- **Weiss monotonicity**, integrated form (after Weiss 1999). Let `d ≥ 2` and let `u` be
`L`-Lipschitz and a local minimizer of `J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ` (no sign
condition), with `u(x₀) = 0`. Then for `0 < r < s`,
`W(u, x₀, s) - W(u, x₀, r) ≥ D(u, x₀; r, s) ≥ 0`, and for `r > 0`,
`|W(u, x₀, r)| ≤ (L² + 1) |B₁| + L² σ(𝕊)`. -/
def WeissMonotoneStatement : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ {u : E d → ℝ} {L : ℝ≥0} {x₀ : E d}, LipschitzWith L u →
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) u → u x₀ = 0 →
    (∀ r s : ℝ, 0 < r → r < s →
      weissDefect u x₀ r s ≤ weissW u x₀ s - weissW u x₀ r ∧ 0 ≤ weissDefect u x₀ r s) ∧
    ∀ r : ℝ, 0 < r →
      |weissW u x₀ r| ≤ ((L : ℝ) ^ 2 + 1) * volume.real (ball (0 : E d) 1) +
        (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ

/-! ### Homogeneous classification -/

/-- **Homogeneous two-phase functions** (after De Philippis–Spolaor–Velichkov, arXiv:1911.02165,
Lemma 2.2): if `v : ℝᵈ → ℝ` is Lipschitz, `1`-homogeneous, harmonic on `{v > 0}` and on `{v < 0}`,
and takes a positive and a negative value, then `v(x) = a (x·e)⁺ - b (x·e)⁻` with `‖e‖ = 1` and
`a, b > 0`. No minimality is assumed. The theorem proving it assumes `2 ≤ d`. -/
def HomogeneousTwoPhaseIn (d : ℕ) : Prop :=
  ∀ (v : E d → ℝ) (L : ℝ≥0), LipschitzWith L v →
    (∀ t : ℝ, 0 < t → ∀ x, v (t • x) = t * v x) →
    InnerProductSpace.HarmonicOnNhd v {x | 0 < v x} →
    InnerProductSpace.HarmonicOnNhd v {x | v x < 0} →
    (∃ x, 0 < v x) → (∃ x, v x < 0) →
    ∃ (e : E d) (a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ ∀ x, v x = twoPlane a b e 0 x

/-! ### Classification of global two-phase minimizers -/

/-- **Classification of global two-phase minimizers** (after Alt–Caffarelli–Friedman 1984). Let
`u : ℝᵈ → ℝ` be Lipschitz and a local minimizer of `J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ`:
for some weak gradient `G`, `u ∈ H¹_loc(ℝᵈ)` and for every ball `B` and every `v ∈ H¹_loc(ℝᵈ)`
with `v = u` a.e. off `B`, `J(u, B) ≤ J(v, B)`. If `u` takes a positive and a negative value,
then there are a unit vector `e`, `c ∈ ℝ` and `a, b > 0` with `a² - b² = 1` such that
`u(x) = a (x·e + c)⁺ - b (x·e + c)⁻` for every `x`. Only the positive phase is penalized, and
there is no sign condition on `u`. -/
def TwoPhaseClassificationStatement : Prop :=
  ∀ {d : ℕ} {u : E d → ℝ} {L : ℝ≥0}, LipschitzWith L u →
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) u → (∃ x, 0 < u x) → (∃ x, u x < 0) →
    ∃ (e : E d) (c a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = 1 ∧
      ∀ x, u x = twoPlane a b e c x

end EllipticBernoulli
