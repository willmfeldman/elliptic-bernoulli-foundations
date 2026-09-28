/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Viscosity
public import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Harmonic.ViscosityHarmonic

/-!
# Viscosity super/subsolutions in their positivity set

* `IsViscSuper.isViscSuperharmonicOn_posSet` (`ViscSuperharmonicPosSetStatement`): a viscosity
  supersolution is viscosity superharmonic in `posSet u U`.
* `IsViscSub.isViscSubharmonicOn_posSet` (`ViscSubharmonicPosSetStatement`): a viscosity
  subsolution is viscosity subharmonic in `posSet u U`.
* `IsViscSolution.harmonicOnNhd_posSet` (`ViscSolutionHarmonicStatement`): a viscosity solution is
  harmonic in `posSet u U`, via `harmonicOnNhd_of_isViscHarmonic`.

`posSet u U` is open (`isOpen_posSet`), so touching relative to it is touching on a
neighbourhood. At a touching point `x ∈ posSet u U` the free-boundary alternative `φ x = 0` of
Abedin–Feldman–Stinson, Definition 2.1, is impossible, because `φ x = u x > 0`.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

/-- Supersolutions are viscosity superharmonic in `posSet` (`ViscSuperharmonicPosSetStatement`). -/
theorem IsViscSuper.isViscSuperharmonicOn_posSet : ViscSuperharmonicPosSetStatement := by
  intro d U Q u hU hu φ hφ x hx htouch
  have hev : ∀ᶠ y in 𝓝 x, φ y ≤ u y :=
    htouch.eventually_le_of_isOpen (isOpen_posSet hU hu.1)
  rcases hu.2.2 φ hφ x hx.1 ⟨hx.1, htouch.2.1, mem_nhdsWithin_of_mem_nhds hev⟩ with h | ⟨h, -⟩
  · exact h
  · have : 0 < u x := hx.2
    rw [← htouch.2.1, h] at this
    exact absurd this (lt_irrefl 0)

/-- Subsolutions are viscosity subharmonic in `posSet` (`ViscSubharmonicPosSetStatement`). -/
theorem IsViscSub.isViscSubharmonicOn_posSet : ViscSubharmonicPosSetStatement := by
  intro d U Q u hU hu φ hφ x hx htouch
  have hev : ∀ᶠ y in 𝓝 x, u y ≤ φ y :=
    htouch.eventually_le_of_isOpen (isOpen_posSet hU hu.1)
  have hφx : φ x = u x := htouch.2.1
  have hpos : 0 < φ x := hφx ▸ hx.2
  have htouch' : TouchesAbove (fun y ↦ max (φ y) 0) u (closure (posSet u U) ∩ U) x :=
    ⟨⟨subset_closure hx, hx.1⟩, by change max (φ x) 0 = u x; rw [max_eq_left hpos.le, hφx],
      mem_nhdsWithin_of_mem_nhds (hev.mono fun y hy ↦ hy.trans (le_max_left _ _))⟩
  rcases hu.2.2 φ hφ x htouch' with h | ⟨h, -⟩
  · exact h
  · exact absurd h hpos.ne'

/-- Viscosity solutions are harmonic in `posSet` (`ViscSolutionHarmonicStatement`), by
`harmonicOnNhd_of_isViscHarmonic`. -/
theorem IsViscSolution.harmonicOnNhd_posSet : ViscSolutionHarmonicStatement := by
  intro d U Q u hU hu
  exact harmonicOnNhd_of_isViscHarmonic (isOpen_posSet hU hu.1.1)
    (hu.1.1.mono fun _ hy ↦ hy.1) (IsViscSub.isViscSubharmonicOn_posSet hU hu.2)
    (IsViscSuper.isViscSuperharmonicOn_posSet hU hu.1)

end EllipticBernoulli

end
