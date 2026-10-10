/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Variational
import EllipticBernoulli.Regularity.InteriorFree
import EllipticBernoulli.Regularity.Representative
import EllipticBernoulli.Variational.Continuity
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Lipschitz.Estimate
import EllipticBernoulli.Harmonic.Basic
import EllipticBernoulli.Sobolev.Energy

/-!
# Regularity of local energy minimizers

Proves `EnergyMinimizerRegularityStatement`
(`IsLocalEnergyMinimizer.exists_regular_representative`): a local minimizer `u ≥ 0` of
`J_Q(v; B) = ∫_B |∇v|² + Q² 1_{v>0}` in an open set `U`, with `Q`
continuous and `0 ≤ Q ≤ C`, has an a.e.-equal representative `v` which is again a local energy
minimizer, is locally Lipschitz and nonnegative on `U`, and is `C^∞` and harmonic in the open set
`{v > 0} ∩ U` (Alt–Caffarelli, §§2–3; Velichkov, Ch. 3 and Proposition 7.1).
`exists_regular_representative_univ` is the case `U = ℝᵈ`, `Q ≡ 1`.

## Proof

* **Representative.** Replace `u` by `u₀ = max(u, 0)`, which is a.e. equal to `u` on `U` and
  hence again a local energy minimizer (`IsLocalEnergyMinimizer.congr_ae`), and nonnegative
  everywhere. Set `v = max(lim_{s → 0⁺} ⨍_{B̄_s(x)} u₀, 0)` on `U` (`ballLimit`) and `v = u₀`
  off `U`. By Lebesgue differentiation `v = u₀` a.e. on `U`.
* **Continuity** (`Regularity/InteriorFree.lean`): with no obstacle every truncation level is
  admissible, so `u₀ ∈ DG⁺` at levels `≥ 0` and `-u₀ ∈ DG⁺` at every level, and the interior
  De Giorgi argument (Giusti, Ch. 7) shows that the essential oscillation of `u₀` vanishes at every
  point of `U`. Hence `v` is continuous on `U` (`continuousOn_ballLimit`). Alt and Caffarelli
  (§2) prove continuity by harmonic replacement instead.
* **Viscosity solution.** A continuous nonnegative local energy minimizer is a viscosity solution
  (`IsLocalEnergyMinimizer.isViscSolution`; Velichkov, Proposition 7.1), hence harmonic in its
  positivity set (`IsViscSolution.harmonicOnNhd_posSet`), hence `C^∞` there (Weyl), and locally
  Lipschitz (`locallyLipschitzOn_of_isViscSolution`).

No dimension hypothesis is needed: for `d = 0` every function on `E 0` is continuous.

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
* E. Giusti, *Direct Methods in the Calculus of Variations*, World Scientific, 2003, Ch. 7.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- `H¹_loc(U)` membership (with a fixed weak gradient) is invariant under a.e. equality on
`U`. -/
theorem MemH1Loc.congr_ae {U : Set (E d)} {u w : E d → ℝ} {G : E d → E d}
    (hu : MemH1Loc U u G) (hae : ∀ᵐ x ∂volume.restrict U, w x = u x) : MemH1Loc U w G :=
  ⟨hu.1.congr_fun_ae (hae.mono fun _ hx ↦ hx.symm), fun L hL hLc ↦
    ⟨(hu.2 L hL hLc).1.ae_eq
      ((ae_restrict_of_ae_restrict_of_subset hL hae).mono fun _ hx ↦ hx.symm),
      (hu.2 L hL hLc).2⟩⟩

/-- Being a local energy minimizer is invariant under a.e. equality on `U`. -/
theorem IsLocalEnergyMinimizer.congr_ae {U : Set (E d)} {Q u w : E d → ℝ}
    (hmin : IsLocalEnergyMinimizer U Q u) (hae : ∀ᵐ x ∂volume.restrict U, w x = u x) :
    IsLocalEnergyMinimizer U Q w := by
  obtain ⟨Gu, hGu, hm⟩ := hmin
  have hGw := hGu.congr_ae hae
  refine ⟨Gu, hGw, fun x r hr hB ↦
    ⟨hGw, fun _ _ ↦ rfl, fun _ _ ↦ mem_univ _, fun v Gv hv hvout hvK ↦ ?_⟩⟩
  have hBU : ball x r ⊆ U := ball_subset_closedBall.trans hB
  rw [energyJ_congr_ae measurableSet_ball (ae_restrict_of_ae_restrict_of_subset hBU hae)
    (ae_of_all _ fun _ ↦ rfl)]
  refine (hm x r hr hB).2.2.2 v Gv hv ?_ hvK
  filter_upwards [hvout, ae_restrict_of_ae_restrict_of_subset sdiff_subset hae] with y h1 h2
  rw [h1, h2]

/-- A property holding a.e. on a ball around each point of an open set `U` holds a.e. on `U`. -/
theorem ae_restrict_of_forall_ball {U : Set (E d)} {p : E d → Prop}
    (h : ∀ x ∈ U, ∃ r > 0, ball x r ⊆ U ∧ ∀ᵐ y ∂volume.restrict (ball x r), p y) :
    ∀ᵐ y ∂volume.restrict U, p y := by
  choose! r hr hrU hp using h
  have hcov : U = ⋃ x ∈ U, ball x (r x) := by
    ext y
    refine ⟨fun hy ↦ mem_biUnion hy (mem_ball_self (hr y hy)), fun hy ↦ ?_⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hy
    exact hrU x hx hyx
  obtain ⟨T, hTU, hTc, hT⟩ :=
    TopologicalSpace.isOpen_biUnion_countable U (fun x ↦ ball x (r x)) fun _ _ ↦ isOpen_ball
  rw [hcov, ← hT, ae_restrict_biUnion_iff _ hTc]
  exact fun x hx ↦ hp x (hTU hx)

/-- **Regularity of local energy minimizers** (`EnergyMinimizerRegularityStatement`;
Alt–Caffarelli, §§2–3; Velichkov, Ch. 3 and Proposition 7.1). -/
theorem IsLocalEnergyMinimizer.exists_regular_representative :
    EnergyMinimizerRegularityStatement := by
  intro d U Q u hU hQc hQ0 hQb hu0 hmin
  classical
  obtain ⟨C, hC⟩ := hQb
  have hCq : 0 ≤ C ^ 2 := sq_nonneg _
  have hQq : ∀ x ∈ U, Q x ^ 2 ≤ C ^ 2 := fun x hx ↦ pow_le_pow_left₀ (hQ0 x hx) (hC x hx) 2
  -- the nonnegative truncation
  set u₀ : E d → ℝ := fun x ↦ max (u x) 0 with hu₀
  have hae₀ : ∀ᵐ x ∂volume.restrict U, u₀ x = u x := hu0.mono fun _ hx ↦ max_eq_left hx
  obtain ⟨Gu, hGu, hm⟩ := hmin.congr_ae hae₀
  have hu₀0 : ∀ x, 0 ≤ u₀ x := fun _ ↦ le_max_right _ _
  have hball : ∀ x ∈ U, ∃ r > 0, closedBall x r ⊆ U := fun x hx ↦ by
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
    exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
  -- the representative
  set v : E d → ℝ := fun x ↦ if x ∈ U then max (ballLimit u₀ x) 0 else u₀ x with hv
  have hv0 : ∀ x, 0 ≤ v x := fun x ↦ by
    simp only [hv]
    split_ifs
    exacts [le_max_right _ _, hu₀0 x]
  have haev : ∀ᵐ x ∂volume.restrict U, v x = u₀ x := by
    refine ae_restrict_of_forall_ball fun x hx ↦ ?_
    obtain ⟨r, hr, hB⟩ := hball x hx
    refine ⟨r, hr, ball_subset_closedBall.trans hB, ?_⟩
    filter_upwards [ballLimit_ae_eq isOpen_ball (integrableOn_ball_of_memH1Loc hGu hB),
      ae_restrict_mem measurableSet_ball] with y hy hyB
    simp only [hv, ite_eq_left (hB (ball_subset_closedBall hyB)), hy]
    exact max_eq_left (hu₀0 y)
  have haevu : ∀ᵐ x ∂volume.restrict U, v x = u x := by
    filter_upwards [haev, hae₀] with x h1 h2
    rw [h1, h2]
  have hvmin : IsLocalEnergyMinimizer U Q v := hmin.congr_ae haevu
  -- continuity
  have hvc : ContinuousOn v U := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact continuousOn_of_dim_zero v U
    have hosc : ∀ y ∈ U, EssOscVanishes u₀ y := fun y hy ↦
      essOscVanishes_of_free hd hU hCq hQq hGu (fun y _ ↦ hu₀0 y)
        (fun x r hr hB w Gw hw hout ↦
          (hm x r hr hB).2.2.2 w Gw hw hout (ae_of_all _ fun _ ↦ mem_univ _)) hy
    intro x hx
    obtain ⟨r, hr, hB⟩ := hball x hx
    have hBU : ball x r ⊆ U := ball_subset_closedBall.trans hB
    have hc : ContinuousOn (fun y ↦ max (ballLimit u₀ y) 0) (ball x r) :=
      (continuousOn_ballLimit isOpen_ball (integrableOn_ball_of_memH1Loc hGu hB)
        fun y hy ↦ hosc y (hBU hy)).sup continuousOn_const
    have hc' : ContinuousOn v (ball x r) :=
      hc.congr fun y hy ↦ by simp only [hv, ite_eq_left (hBU hy)]
    exact (hc'.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).continuousWithinAt
  -- viscosity solution, harmonicity and the Lipschitz bound
  have hvisc : IsViscSolution U Q v :=
    IsLocalEnergyMinimizer.isViscSolution hU hQc hQ0 hvc (fun x _ ↦ hv0 x) hvmin
  have hpos : IsOpen (posSet v U) := isOpen_posSet hU hvc
  have hharm : HarmonicOnNhd v (posSet v U) := IsViscSolution.harmonicOnNhd_posSet hU hvisc
  refine ⟨v, haevu, hvmin, locallyLipschitzOn_of_isViscSolution hU hQc hvisc,
    fun x _ ↦ hv0 x, hpos, HarmonicOnNhd.contDiffOn_top hpos hharm, fun x hx ↦ ?_⟩
  simpa using (hharm x hx).2.eq_of_nhds

/-- **Regularity of local energy minimizers in `ℝᵈ` with `Q ≡ 1`.** A local minimizer
`u ≥ 0` a.e. of `∫ |∇v|² + 1_{v>0}` on every ball has an a.e.-equal representative which is
locally Lipschitz and nonnegative on `ℝᵈ`, and `C^∞` and harmonic on `{v > 0}`. No dimension
hypothesis is needed. -/
theorem exists_regular_representative_univ {u : E d → ℝ}
    (hnn : ∀ᵐ x ∂(volume : Measure (E d)), 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u) :
    ∃ v : E d → ℝ, v =ᵐ[volume] u ∧ LocallyLipschitz v ∧ (∀ x, 0 ≤ v x) ∧
      ContDiffOn ℝ ∞ v {x | 0 < v x} ∧ (∀ x, 0 < v x → Δ v x = 0) := by
  obtain ⟨v, hae, -, hlip, hv0, -, hsmooth, hΔ⟩ :=
    IsLocalEnergyMinimizer.exists_regular_representative isOpen_univ continuousOn_const
      (fun _ _ ↦ zero_le_one) ⟨1, fun _ _ ↦ le_rfl⟩ (by rwa [Measure.restrict_univ]) hmin
  have hpos : posSet v univ = {x | 0 < v x} := by ext x; simp [posSet]
  rw [Measure.restrict_univ] at hae
  refine ⟨v, hae, locallyLipschitzOn_univ.1 hlip, fun x ↦ hv0 x (mem_univ x), hpos ▸ hsmooth,
    fun x hx ↦ hΔ x ⟨mem_univ x, hx⟩⟩

end EllipticBernoulli
