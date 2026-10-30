/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Definitions for the two-phase problem

Vocabulary for the Alt–Caffarelli–Friedman (ACF) monotonicity formula, the Friedland–Hayman
inequality, Weiss monotonicity, and the classification of global two-phase minimizers.

## Functions on the sphere

Functions on the unit sphere `𝕊 = sphere (0 : E d) 1` are functions on the subtype, and the
admissible ones are Lipschitz for the chordal (subtype) metric. Gradients on the sphere are taken
through the `0`-homogeneous extension `homogExt0 f`, `x ↦ f (x / ‖x‖)`: the tangential gradient of
`f` at `ω ∈ 𝕊` is `∇ (homogExt0 f) ω`. The sphere measure is Mathlib's
`(volume : Measure (E d)).toSphere`.

## Eigenvalues and exponents

* `sphEigenvalue Γ` (`λ₁(Γ)`) is the infimum of the Rayleigh quotients `sphRayleigh f` over the
  functions `f` admissible for `Γ` (`IsSphAdmissible Γ f`).
* `capEigenvalue d θ` (`Λ_d(θ)`) is the infimum of the one-dimensional colatitude Rayleigh quotients
  `capRayleigh d θ F` over `F` admissible for `θ` (`IsCapAdmissible θ F`).
* Three exponents get three names: `charExponent d λ` (`κ_d(λ)`, the nonnegative root of
  `α (α + d - 2) = λ`), `sphExponent Γ = κ_d(λ₁(Γ))` (`α_d(Γ)`) and
  `capExponent d θ = κ_d(Λ_d(θ))` (`ᾱ_d(θ)`).

The sources define `λ₁(Γ)` with trial functions in `H¹₀(Γ)`. Here the trial functions are chordally
Lipschitz on the sphere and vanish off `Γ`. Caps enter only through `Λ_d(θ)`.

## Functionals

* `acfIntegral w x₀ r = ∫_{B_r(x₀)} |∇w|² |x - x₀|^{2-d}` (a real power), and
  `acfPhi u₁ u₂ x₀ r = r⁻⁴ I(u₁) I(u₂)`.
* `weissW u x₀ r = r^{-d} J(u, B_r(x₀)) - r^{-2} ∫_𝕊 u(x₀ + rω)² dσ(ω)`, with
  `J = energyJ · (fun _ ↦ 1)` (so `Q ≡ 1`), and the defect `weissDefect u x₀ r s`.

For Lipschitz functions, the integrands are bounded (or bounded by an integrable weight), so all
the integrals here are genuine Bochner integrals.

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* T. Beck, D. Jerison, *The Friedland–Hayman inequality and Caffarelli's contraction theorem*,
  arXiv:2102.00571.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473.
* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.
-/

open Set Filter Topology MeasureTheory Metric
open scoped Gradient NNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Functions on the sphere -/

/-- The `0`-homogeneous extension of a function on the unit sphere: `x ↦ f (x / ‖x‖)` for
`x ≠ 0`, and `0` at `x = 0`. The tangential gradient of `f` at `ω ∈ 𝕊` is
`∇ (homogExt0 f) ω`. -/
def homogExt0 (f : sphere (0 : E d) 1 → ℝ) (x : E d) : ℝ :=
  if hx : x = 0 then 0
  else f ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

/-- The Dirichlet energy on the sphere, `∫_𝕊 |∇_𝕊 f|² dσ`, with the tangential gradient taken
through the `0`-homogeneous extension. -/
def sphDirichlet (f : sphere (0 : E d) 1 → ℝ) : ℝ :=
  ∫ ω, ‖∇ (homogExt0 f) (ω : E d)‖ ^ 2 ∂(volume : Measure (E d)).toSphere

/-- The squared `L²` norm on the sphere, `∫_𝕊 f² dσ`. -/
def sphL2Sq (f : sphere (0 : E d) 1 → ℝ) : ℝ :=
  ∫ ω, f ω ^ 2 ∂(volume : Measure (E d)).toSphere

/-- The Rayleigh quotient `R(f) = ∫_𝕊 |∇_𝕊 f|² dσ / ∫_𝕊 f² dσ`. -/
def sphRayleigh (f : sphere (0 : E d) 1 → ℝ) : ℝ :=
  sphDirichlet f / sphL2Sq f

/-- `f` is admissible for `Γ ⊆ 𝕊`: it is Lipschitz for the chordal metric, vanishes on `𝕊 \ Γ`,
and `∫_𝕊 f² dσ > 0`. The sources use `H¹₀(Γ)` instead of the Lipschitz class. -/
structure IsSphAdmissible (Γ : Set (sphere (0 : E d) 1)) (f : sphere (0 : E d) 1 → ℝ) :
    Prop where
  lipschitz : ∃ K, LipschitzWith K f
  eq_zero : ∀ ω ∉ Γ, f ω = 0
  sphL2Sq_pos : 0 < sphL2Sq f

/-- The first Dirichlet eigenvalue `λ₁(Γ)` of `Γ ⊆ 𝕊`: the infimum of the Rayleigh quotients of
the functions admissible for `Γ`.

Statements about `sphEigenvalue Γ` must assume that `Γ` is (relatively) open and nonempty: then
admissible functions exist, while `sInf ∅ = 0`. -/
def sphEigenvalue (Γ : Set (sphere (0 : E d) 1)) : ℝ :=
  sInf (sphRayleigh '' {f | IsSphAdmissible Γ f})

/-! ### Exponents -/

/-- The characteristic exponent `κ_d(λ) = (-(d - 2) + √((d - 2)² + 4λ)) / 2`, the nonnegative root
of `α (α + d - 2) = λ` for `λ ≥ 0` and `d ≥ 2`. -/
def charExponent (d : ℕ) (lam : ℝ) : ℝ :=
  (-((d : ℝ) - 2) + √(((d : ℝ) - 2) ^ 2 + 4 * lam)) / 2

/-- The characteristic exponent of `Γ ⊆ 𝕊^{d-1}`: `α_d(Γ) = κ_d(λ₁(Γ))`. -/
def sphExponent (Γ : Set (sphere (0 : E d) 1)) : ℝ :=
  charExponent d (sphEigenvalue Γ)

/-- The colatitude Rayleigh quotient of `F` on `[0, θ]` with weight `sin^{d-2}`:
`∫₀^θ F'² sin^{d-2} / ∫₀^θ F² sin^{d-2}`. -/
def capRayleigh (d : ℕ) (θ : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∫ φ in 0..θ, deriv F φ ^ 2 * Real.sin φ ^ (d - 2)) /
    ∫ φ in 0..θ, F φ ^ 2 * Real.sin φ ^ (d - 2)

/-- `F` is admissible for the cap of colatitude `θ`: it is Lipschitz on `[0, θ]`, `F θ = 0`, and
`F` does not vanish identically on `[0, θ]`. Values of `F` outside `[0, θ]` play no role. -/
structure IsCapAdmissible (θ : ℝ) (F : ℝ → ℝ) : Prop where
  lipschitzOn : ∃ K, LipschitzOnWith K F (Icc 0 θ)
  apply_right_eq_zero : F θ = 0
  exists_ne_zero : ∃ φ ∈ Icc 0 θ, F φ ≠ 0

/-- The radial cap eigenvalue `Λ_d(θ)`, for `d ≥ 2` and `θ ∈ (0, π]`: the infimum of
`capRayleigh d θ F` over the `F` admissible for `θ`. -/
def capEigenvalue (d : ℕ) (θ : ℝ) : ℝ :=
  sInf (capRayleigh d θ '' {F | IsCapAdmissible θ F})

/-- The cap exponent `ᾱ_d(θ) = κ_d(Λ_d(θ))`. -/
def capExponent (d : ℕ) (θ : ℝ) : ℝ :=
  charExponent d (capEigenvalue d θ)

/-! ### The ACF functional -/

/-- `I(w, x₀, r) = ∫_{B_r(x₀)} |∇w(x)|² |x - x₀|^{2-d} dx`, with the weight a real power. -/
def acfIntegral (w : E d → ℝ) (x₀ : E d) (r : ℝ) : ℝ :=
  ∫ x in ball x₀ r, ‖∇ w x‖ ^ 2 * ‖x - x₀‖ ^ (2 - (d : ℝ))

/-- The ACF functional `Φ(u₁, u₂, x₀, r) = r⁻⁴ I(u₁, x₀, r) I(u₂, x₀, r)`. -/
def acfPhi (u₁ u₂ : E d → ℝ) (x₀ : E d) (r : ℝ) : ℝ :=
  acfIntegral u₁ x₀ r * acfIntegral u₂ x₀ r / r ^ 4

/-- `(u₁, u₂)` is an ACF pair at `x₀` with Lipschitz constant `L`: each `uᵢ` is nonnegative,
`L`-Lipschitz and harmonic on the open set `{uᵢ > 0}`; `u₁ u₂ ≡ 0`; and `u₁ x₀ = u₂ x₀ = 0`.
Alt–Caffarelli–Friedman assume continuity and subharmonicity in the sense of distributions instead
of the Lipschitz bound and harmonicity in the positivity sets. -/
structure IsACFPair (u₁ u₂ : E d → ℝ) (x₀ : E d) (L : ℝ≥0) : Prop where
  nonneg_left : ∀ x, 0 ≤ u₁ x
  nonneg_right : ∀ x, 0 ≤ u₂ x
  lipschitz_left : LipschitzWith L u₁
  lipschitz_right : LipschitzWith L u₂
  harmonic_left : InnerProductSpace.HarmonicOnNhd u₁ {x | 0 < u₁ x}
  harmonic_right : InnerProductSpace.HarmonicOnNhd u₂ {x | 0 < u₂ x}
  mul_eq_zero : ∀ x, u₁ x * u₂ x = 0
  left_apply_eq_zero : u₁ x₀ = 0
  right_apply_eq_zero : u₂ x₀ = 0

/-! ### The Weiss functional -/

/-- The Weiss functional
`W(u, x₀, r) = r^{-d} J(u, B_r(x₀)) - r^{-2} ∫_𝕊 u(x₀ + rω)² dσ(ω)`, with
`J(u, B) = ∫_B |∇u|² + 1_{u > 0}` the energy `energyJ` with `Q ≡ 1` and the pointwise gradient. -/
def weissW (u : E d → ℝ) (x₀ : E d) (r : ℝ) : ℝ :=
  (energyJ (ball x₀ r) (fun _ ↦ 1) u (gradient u)).toReal / r ^ d -
    (∫ ω, u (x₀ + r • (ω : E d)) ^ 2 ∂(volume : Measure (E d)).toSphere) / r ^ 2

/-- The Weiss defect
`D(u, x₀; r, s) = ∫_{B_s(x₀) \ B_r(x₀)} |x - x₀|^{-d-2} ((x - x₀) · ∇u(x) - u(x))² dx`. -/
def weissDefect (u : E d → ℝ) (x₀ : E d) (r s : ℝ) : ℝ :=
  ∫ x in ball x₀ s \ ball x₀ r,
    ‖x - x₀‖ ^ (-(d : ℝ) - 2) * (inner ℝ (x - x₀) (∇ u x) - u x) ^ 2

/-! ### Two-plane functions -/

/-- The two-plane function `x ↦ a (x·e + c)⁺ - b (x·e + c)⁻`. -/
def twoPlane (a b : ℝ) (e : E d) (c : ℝ) (x : E d) : ℝ :=
  a * max (inner ℝ x e + c) 0 - b * max (-(inner ℝ x e + c)) 0

end EllipticBernoulli
