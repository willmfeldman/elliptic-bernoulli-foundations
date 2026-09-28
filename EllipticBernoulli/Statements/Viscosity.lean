/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Basic.KLimit
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Headline statements: viscosity toolkit

One `def …Statement : Prop` per headline result. The theorems proving them live in
`EllipticBernoulli/Viscosity/*`.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

universe u

@[expose] public section

namespace EllipticBernoulli

/-- **Supersolutions are viscosity superharmonic in their positivity set.** Proved by
`IsViscSuper.isViscSuperharmonicOn_posSet` (`Viscosity/Harmonic.lean`). -/
def ViscSuperharmonicPosSetStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}, IsOpen U → IsViscSuper U Q u →
    IsViscSuperharmonicOn u (posSet u U)

/-- **Subsolutions are viscosity subharmonic in their positivity set** (dual of
`ViscSuperharmonicPosSetStatement`). Proved by `IsViscSub.isViscSubharmonicOn_posSet`
(`Viscosity/Harmonic.lean`). -/
def ViscSubharmonicPosSetStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}, IsOpen U → IsViscSub U Q u →
    IsViscSubharmonicOn u (posSet u U)

/-- **Viscosity solutions are harmonic in their positivity set.** Proved by
`IsViscSolution.harmonicOnNhd_posSet` (`Viscosity/Harmonic.lean`). -/
def ViscSolutionHarmonicStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}, IsOpen U → IsViscSolution U Q u →
    HarmonicOnNhd u (posSet u U)

/-- **Stability of supersolutions** (Abedin–Feldman–Stinson, Lemma 2.4(i)). Proved by
`isViscSuper_of_tendstoLocallyUniformlyOn` (`Viscosity/Stability.lean`). -/
def ViscSuperStabilityStatement : Prop :=
  ∀ {d : ℕ} {ι : Type u} {l : Filter ι} [l.NeBot] {U : Set (E d)}, IsOpen U →
    ∀ {Q : E d → ℝ}, ContinuousOn Q U →
    ∀ {uk : ι → E d → ℝ} {u : E d → ℝ}, (∀ᶠ k in l, IsViscSuper U Q (uk k)) →
      TendstoLocallyUniformlyOn uk u l U → IsViscSuper U Q u

/-- **Stability of relaxed subsolutions** (Abedin–Feldman–Stinson, Lemma 2.4(ii)), with
`E* = upperKLimit Es l`. Proved by `isRelaxedSub_of_tendstoLocallyUniformlyOn`
(`Viscosity/Stability.lean`). -/
def RelaxedSubStabilityStatement : Prop :=
  ∀ {d : ℕ} {ι : Type u} {l : Filter ι} [l.NeBot] {U : Set (E d)}, IsOpen U →
    ∀ {Q : E d → ℝ}, ContinuousOn Q U →
    ∀ {uk : ι → E d → ℝ} {u : E d → ℝ} {Es : ι → Set (E d)},
      (∀ᶠ k in l, IsRelaxedSub U Q (uk k) (Es k)) →
      TendstoLocallyUniformlyOn uk u l U → IsRelaxedSub U Q u (upperKLimit Es l)

/-- Both stability statements. -/
def ViscStabilityStatement : Prop :=
  ViscSuperStabilityStatement.{u} ∧ RelaxedSubStabilityStatement.{u}

/-- **The minimum of two supersolutions is a supersolution.** Proved by `IsViscSuper.min`
(`Viscosity/Lattice.lean`). -/
def ViscMinStatement : Prop :=
  ∀ {d : ℕ} {W : Set (E d)} {Q u w : E d → ℝ}, IsViscSuper W Q u → IsViscSuper W Q w →
    IsViscSuper W Q (fun y ↦ min (u y) (w y))

/-- **The maximum of two subsolutions is a subsolution** (dual of `ViscMinStatement`). Proved by
`IsViscSub.max` (`Viscosity/Lattice.lean`). -/
def ViscMaxStatement : Prop :=
  ∀ {d : ℕ} {W : Set (E d)} {Q u w : E d → ℝ}, IsViscSub W Q u → IsViscSub W Q w →
    IsViscSub W Q (fun y ↦ max (u y) (w y))

/-- Both lattice statements. -/
def ViscMinMaxStatement : Prop :=
  ViscMinStatement ∧ ViscMaxStatement

end EllipticBernoulli
