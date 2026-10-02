/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Vocabulary: energy-decreasing perturbations (the proof of Feldman–Kim–Požár, Lemma 3.3)

Challenge vocabulary: a Mathlib-only restatement of the library files
`EllipticBernoulli/Basic/Setting.lean`, `EllipticBernoulli/Basic/Sobolev.lean`, in this order, one
part per file. Each part keeps the library's names, definitions and order, with the theorems
dropped, and keeps its `open` commands inside its own section. `scripts/challenge-prep.py sync`
copies this file into the generated block of `Challenge.lean`; Comparator checks each copied
declaration against the library by name and value.
-/

@[expose] public section

/-!
# Standing setting

The ambient space, positivity sets, free boundaries, compact containment and the divergence,
following Abedin–Feldman–Stinson. There is no global setting: statements are local, with explicit
hypotheses on `U` and `Q`.

## Conventions

* All functions are total (`E d → ℝ`); every predicate restricts to its domain explicitly, and
  values outside the domain are never used.

Restates the library file `EllipticBernoulli/Basic/Setting.lean`, with its theorems dropped. The
definitions are verbatim and in the library order, so Comparator can check that they are the
library's definitions.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

section

open Set Filter Topology
open scoped Gradient Laplacian

noncomputable section

namespace EllipticBernoulli

/-- The ambient Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The positivity set `{u > 0}` of `u` inside the domain `U` (the set `{u > 0}` of
Abedin–Feldman–Stinson, with `u` defined on `U` only). -/
def posSet (u : E d → ℝ) (U : Set (E d)) : Set (E d) := {x ∈ U | 0 < u x}

/-- The free boundary `∂{u > 0} ∩ U` (Abedin–Feldman–Stinson, (1.1) and Theorem 1.1). -/
def freeBoundary (u : E d → ℝ) (U : Set (E d)) : Set (E d) := frontier (posSet u U) ∩ U

section CompactlyContained

variable {X : Type*} [TopologicalSpace X]

/-- `A ⊂⊂ B`: the closure of `A` is compact and contained in `B`. -/
def CompactlyContained (A B : Set X) : Prop := IsCompact (closure A) ∧ closure A ⊆ B

end CompactlyContained

/-! ### Differential operators -/

/-- The divergence `∇ · ξ = tr (Dξ)` of a vector field `ξ : ℝᵈ → ℝᵈ` (pointwise, via `fderiv`;
`0` where `ξ` is not differentiable). -/
noncomputable def divergence (ξ : E d → E d) (x : E d) : ℝ :=
  LinearMap.trace ℝ (E d) (fderiv ℝ ξ x).toLinearMap

end EllipticBernoulli

end

end

/-!
# Minimal Sobolev notions and the Alt–Caffarelli energy

* `HasWeakGradient U u G`, `MemH1 U u G`, `MemH1Loc U u G` (the weak gradient is carried as
  explicit data `G`).
* `energyJ V Q u G` — the Alt–Caffarelli energy `J_Q(u; V)` (Abedin–Feldman–Stinson, (1.2)), and
  `energyJχ V Q G χ` — the energy `J(u, χ; V)` of a pair (Abedin–Feldman–Stinson, §3.4).
* `TendstoLpLoc` (strong `L^p_loc` convergence) and `TendstoWeakL2` (weak `L²` convergence).

Energies are `ℝ≥0∞`-valued lower Lebesgue integrals, so no integrability side conditions are
needed. The free boundary condition of this energy is `|∇u| = Q`; the coefficient enters squared.

Restates the library file `EllipticBernoulli/Basic/Sobolev.lean`, with its theorems dropped. The
definitions are verbatim and in the library order, so Comparator can check that they are the
library's definitions.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

section

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff

noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- `G` is a weak gradient of `u` in the open set `U`: `u` and `G` are locally
integrable on `U` and `∫_U u ∂_v φ = - ∫_U (G · v) φ` for every `φ ∈ C_c^∞(U)` and direction `v`. -/
def HasWeakGradient (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) : Prop :=
  LocallyIntegrableOn u U ∧ LocallyIntegrableOn G U ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : E d,
      ∫ x in U, u x * fderiv ℝ φ x v = -∫ x in U, inner ℝ (G x) v * φ x

/-- `u ∈ H¹(U)` with weak gradient `G`: `u, G ∈ L²(U)` and `G` is a weak gradient of `u` in `U`.
The weak gradient is carried as data. -/
def MemH1 (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) : Prop :=
  MemLp u 2 (volume.restrict U) ∧ MemLp G 2 (volume.restrict U) ∧ HasWeakGradient U u G

/-- `u ∈ H¹_loc(U)` with weak gradient `G`: `G` is a weak gradient of `u` in `U` and
`u, G ∈ L²(K)` for every compact `K ⊆ U`. The weak gradient is carried as data. -/
def MemH1Loc (U : Set (E d)) (u : E d → ℝ) (G : E d → E d) : Prop :=
  HasWeakGradient U u G ∧ ∀ K ⊆ U, IsCompact K →
    MemLp u 2 (volume.restrict K) ∧ MemLp G 2 (volume.restrict K)

/-- The Alt–Caffarelli energy `J_Q(u; V) = ∫_V |∇u|² + Q² 1_{u>0}` (Abedin–Feldman–Stinson,
(1.2)), with the gradient supplied as data `G`. Valued in `ℝ≥0∞`. -/
noncomputable def energyJ (V : Set (E d)) (Q u : E d → ℝ) (G : E d → E d) : ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal (‖G x‖ ^ 2 + Q x ^ 2 * (posSet u V).indicator 1 x)

/-- The energy of a pair, `J(u, χ; V) = ∫_V |∇u|² + Q² χ` (Abedin–Feldman–Stinson, §3.4), with
the gradient supplied as data `G`. Valued in `ℝ≥0∞`. -/
noncomputable def energyJχ (V : Set (E d)) (Q : E d → ℝ) (G : E d → E d) (χ : E d → ℝ) :
    ℝ≥0∞ :=
  ∫⁻ x in V, ENNReal.ofReal (‖G x‖ ^ 2 + Q x ^ 2 * χ x)

section Convergence

variable {X F ι : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- Strong `L^p_loc(Ω)` convergence `f i → f₀` along `l`: `‖f i - f₀‖_{L^p(K)} → 0` for every
compact `K ⊆ Ω`. -/
def TendstoLpLoc [NormedAddCommGroup F] (p : ℝ≥0∞) (μ : Measure X) (Ω : Set X)
    (f : ι → X → F) (f₀ : X → F) (l : Filter ι) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → Tendsto (fun i ↦ eLpNorm (f i - f₀) p (μ.restrict K)) l (𝓝 0)

/-- Weak `L²(Ω)` convergence `f i ⇀ f₀` along `l`: all functions are in `L²(Ω)` and
`∫_Ω ⟨f i, φ⟩ → ∫_Ω ⟨f₀, φ⟩` for every `φ ∈ L²(Ω)`. -/
def TendstoWeakL2 [NormedAddCommGroup F] [InnerProductSpace ℝ F] (μ : Measure X) (Ω : Set X)
    (f : ι → X → F) (f₀ : X → F) (l : Filter ι) : Prop :=
  (∀ i, MemLp (f i) 2 (μ.restrict Ω)) ∧ MemLp f₀ 2 (μ.restrict Ω) ∧
    ∀ φ : X → F, MemLp φ 2 (μ.restrict Ω) →
      Tendsto (fun i ↦ ∫ x in Ω, inner ℝ (f i x) (φ x) ∂μ) l
        (𝓝 (∫ x in Ω, inner ℝ (f₀ x) (φ x) ∂μ))

end Convergence

end EllipticBernoulli

end

end
