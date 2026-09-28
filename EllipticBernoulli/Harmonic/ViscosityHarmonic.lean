/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Harmonic
public import EllipticBernoulli.Harmonic.Comparison
public import EllipticBernoulli.Harmonic.DirichletBall

/-!
# Viscosity-harmonic functions are harmonic

* `IsViscSubharmonicOn.mono`, `IsViscSuperharmonicOn.mono`: restriction to an open subset.
* `harmonicOnNhd_of_isViscHarmonic` (`ViscHarmonicStatement`): a continuous function which is
  viscosity sub- and superharmonic on an open set is harmonic there.

## Proof

For `x ∈ Ω` choose `closedBall x r ⊆ Ω` and let `h` be the harmonic function on `ball x r` with
boundary values `u` on `sphere x r` (`exists_harmonic_ball_boundary`). The comparison principle
(`IsViscSubharmonicOn.le_of_frontier_le`, `IsViscSuperharmonicOn.le_of_le_frontier`) on
`ball x r` gives `u = h` on `closedBall x r`, so `u` is harmonic at `x`. In dimension `0` every
function is harmonic.
-/

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- Viscosity subharmonicity passes to open subsets. -/
theorem IsViscSubharmonicOn.mono {w : E d → ℝ} {Ω V : Set (E d)}
    (hw : IsViscSubharmonicOn w Ω) (hV : IsOpen V) (hVΩ : V ⊆ Ω) :
    IsViscSubharmonicOn w V := by
  intro φ hφ x hx ⟨_, heq, hle⟩
  rw [hV.nhdsWithin_eq hx] at hle
  exact hw φ hφ x (hVΩ hx) ⟨hVΩ hx, heq, mem_nhdsWithin_of_mem_nhds hle⟩

/-- Viscosity superharmonicity passes to open subsets. -/
theorem IsViscSuperharmonicOn.mono {w : E d → ℝ} {Ω V : Set (E d)}
    (hw : IsViscSuperharmonicOn w Ω) (hV : IsOpen V) (hVΩ : V ⊆ Ω) :
    IsViscSuperharmonicOn w V := by
  intro φ hφ x hx ⟨_, heq, hle⟩
  rw [hV.nhdsWithin_eq hx] at hle
  exact hw φ hφ x (hVΩ hx) ⟨hVΩ hx, heq, mem_nhdsWithin_of_mem_nhds hle⟩

/-- Continuous viscosity-harmonic functions are harmonic (`ViscHarmonicStatement`). -/
theorem harmonicOnNhd_of_isViscHarmonic : ViscHarmonicStatement := by
  intro d Ω u hΩ hu hsub hsuper x hx
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- in dimension zero every function is constant, hence harmonic
    have hconst : u =ᶠ[𝓝 x] fun _ ↦ u x :=
      Eventually.of_forall fun y ↦ congrArg u (Subsingleton.elim y x)
    exact (harmonicAt_congr_nhds hconst).2 (harmonicAt_const _)
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ x hx
  set ρ := r / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hB : closedBall x ρ ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hrΩ
  obtain ⟨h, hhc, hhh, hhu⟩ := exists_harmonic_ball_boundary hd x ρ u hρ0
    (hu.mono (sphere_subset_closedBall.trans hB))
  have hcl : closure (ball x ρ) = closedBall x ρ := closure_ball x hρ0.ne'
  have hfr : frontier (ball x ρ) = sphere x ρ := frontier_ball x hρ0.ne'
  have huc : ContinuousOn u (closure (ball x ρ)) := by rw [hcl]; exact hu.mono hB
  have hhc' : ContinuousOn h (closure (ball x ρ)) := by rwa [hcl]
  have hBΩ : ball x ρ ⊆ Ω := ball_subset_closedBall.trans hB
  have hle : ∀ y ∈ closure (ball x ρ), u y ≤ h y :=
    IsViscSubharmonicOn.le_of_frontier_le hd isOpen_ball isBounded_ball huc
      (hsub.mono isOpen_ball hBΩ) hhc' hhh (fun y hy ↦ by rw [hfr] at hy; rw [hhu hy])
  have hge : ∀ y ∈ closure (ball x ρ), h y ≤ u y :=
    IsViscSuperharmonicOn.le_of_le_frontier hd isOpen_ball isBounded_ball huc
      (hsuper.mono isOpen_ball hBΩ) hhc' hhh (fun y hy ↦ by rw [hfr] at hy; rw [hhu hy])
  have heq : u =ᶠ[𝓝 x] h := by
    filter_upwards [ball_mem_nhds x hρ0] with y hy
    exact le_antisymm (hle y (subset_closure hy)) (hge y (subset_closure hy))
  exact (harmonicAt_congr_nhds heq).2 (hhh x (mem_ball_self hρ0))

end EllipticBernoulli
