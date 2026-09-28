/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Headline statements: harmonic toolkit

One `def …Statement : Prop` per headline result. The theorems proving them live in
`EllipticBernoulli/Harmonic/*`.

Dimension hypotheses: `1 ≤ d` is assumed wherever the statement is false or
meaningless in `E 0` (a one-point space). In particular the comparison statements need it: in
`E 0` the set `{0}` is open, bounded, with empty frontier, and every function is viscosity
subharmonic there.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

universe u

@[expose] public section

namespace EllipticBernoulli

/-- **Harnack inequality on balls.** For `1 ≤ d` there is `C` such that every nonnegative harmonic
`f` on `B_{2r}(x)` satisfies `f y ≤ C f z` for `y, z ∈ B_r(x)`. Proved by `harnack_ball`
(`Harmonic/Harnack.lean`). -/
def HarnackStatement : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∃ C : ℝ, ∀ (f : E d → ℝ) (x : E d) (r : ℝ), 0 < r →
    HarmonicOnNhd f (ball x (2 * r)) → (∀ y ∈ ball x (2 * r), 0 ≤ f y) →
    ∀ y ∈ ball x r, ∀ z ∈ ball x r, f y ≤ C * f z

/-- **Interior gradient estimate.** For `1 ≤ d` there is `C` such that a harmonic `u` on a
neighbourhood of `B̄_r(x₀)` with `|u| ≤ M` there satisfies `|∇u(x₀)| ≤ C M / r`. Proved by
`norm_gradient_le_of_harmonic` (`Harmonic/GradientEstimate.lean`). -/
def GradientEstimateStatement : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∃ C : ℝ, ∀ (u : E d → ℝ) (x₀ : E d) (r M : ℝ), 0 < r →
    HarmonicOnNhd u (closedBall x₀ r) → (∀ y ∈ closedBall x₀ r, |u y| ≤ M) →
    ‖∇ u x₀‖ ≤ C * M / r

/-- **Dirichlet problem on a ball** with continuous boundary data. Proved by
`exists_harmonic_ball_boundary` (`Harmonic/DirichletBall.lean`). -/
def DirichletBallStatement : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∀ (x : E d) (r : ℝ) (g : E d → ℝ), 0 < r → ContinuousOn g (sphere x r) →
    ∃ h : E d → ℝ, ContinuousOn h (closedBall x r) ∧ HarmonicOnNhd h (ball x r) ∧
      EqOn h g (sphere x r)

/-- **Viscosity-harmonic functions are harmonic.** A continuous function which is viscosity sub-
and superharmonic on an open set is (classically) harmonic there. Proved by
`harmonicOnNhd_of_isViscHarmonic` (`Harmonic/ViscosityHarmonic.lean`). -/
def ViscHarmonicStatement : Prop :=
  ∀ {d : ℕ} {Ω : Set (E d)} {u : E d → ℝ}, IsOpen Ω → ContinuousOn u Ω →
    IsViscSubharmonicOn u Ω → IsViscSuperharmonicOn u Ω → HarmonicOnNhd u Ω

/-- **Comparison, subharmonic side.** On a bounded open set, a continuous viscosity subharmonic
`w` lies below a harmonic `h` if it does so on the frontier. Assumes `1 ≤ d` (false in
`E 0`, see the module docstring). Proved by `IsViscSubharmonicOn.le_of_frontier_le`
(`Harmonic/Comparison.lean`). -/
def ViscSubComparisonStatement : Prop :=
  ∀ {d : ℕ} {Ω : Set (E d)} {w h : E d → ℝ}, 1 ≤ d → IsOpen Ω → Bornology.IsBounded Ω →
    ContinuousOn w (closure Ω) → IsViscSubharmonicOn w Ω → ContinuousOn h (closure Ω) →
    HarmonicOnNhd h Ω → (∀ x ∈ frontier Ω, w x ≤ h x) → ∀ x ∈ closure Ω, w x ≤ h x

/-- **Comparison, superharmonic side** (dual of `ViscSubComparisonStatement`). Proved by
`IsViscSuperharmonicOn.le_of_le_frontier` (`Harmonic/Comparison.lean`). -/
def ViscSuperComparisonStatement : Prop :=
  ∀ {d : ℕ} {Ω : Set (E d)} {w h : E d → ℝ}, 1 ≤ d → IsOpen Ω → Bornology.IsBounded Ω →
    ContinuousOn w (closure Ω) → IsViscSuperharmonicOn w Ω → ContinuousOn h (closure Ω) →
    HarmonicOnNhd h Ω → (∀ x ∈ frontier Ω, h x ≤ w x) → ∀ x ∈ closure Ω, h x ≤ w x

/-- Both comparison statements. -/
def ViscComparisonStatement : Prop :=
  ViscSubComparisonStatement ∧ ViscSuperComparisonStatement

/-- **Weyl's lemma, weak-gradient form**: a continuous `u` with weak gradient `G` (carried as
data) that is weakly harmonic is `C^∞` and harmonic. Proved by `harmonic_of_hasWeakGradient`
(`Harmonic/WeylWeakGradient.lean`). -/
def WeakHarmonicStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {u : E d → ℝ} {G : E d → E d},
    IsOpen U → ContinuousOn u U → HasWeakGradient U u G →
    (∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, inner ℝ (G x) (∇ φ x) = 0) →
    ContDiffOn ℝ ∞ u U ∧ ∀ x ∈ U, Δ u x = 0

/-- **Locally uniform limits of harmonic functions** are harmonic, with locally uniform convergence
of the derivatives. Proved by `harmonicOnNhd_of_tendstoLocallyUniformlyOn`
(`Harmonic/Limit.lean`). -/
def HarmonicLimitStatement : Prop :=
  ∀ {d : ℕ} {ι : Type u} {p : Filter ι} [p.NeBot] {U : Set (E d)}, IsOpen U →
    ∀ {F : ι → E d → ℝ} {f : E d → ℝ}, (∀ k, HarmonicOnNhd (F k) U) →
      TendstoLocallyUniformlyOn F f p U →
      HarmonicOnNhd f U ∧ TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (F k)) (fderiv ℝ f) p U

end EllipticBernoulli
