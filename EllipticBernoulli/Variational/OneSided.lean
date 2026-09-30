/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Variational
public import EllipticBernoulli.Variational.Perturbation
import EllipticBernoulli.Viscosity.Stability

/-!
# One-sided minimizers and obstacle minimizers are viscosity sub/supersolutions

Corollaries of the energy-decreasing perturbations of `Variational/Perturbation.lean`.

* `exists_energy_lt_of_touchesBelow` / `exists_energy_lt_of_touchesAbove`: the perturbations for
  the **non-strict** touching of Abedin–Feldman–Stinson, Definition 2.1. Touching is made strict
  with the quartic perturbation `φ ∓ |y - x|⁴` (`touchesBelow_strict_perturb`, `jet_add_quartic`).
  For `φ₊` touching from above, strictness holds because `φ ≥ 0` on `closure {w > 0}` near the
  touching point.
* `energyJ_lt_of_lt_of_eqOn_compl`: an energy decrease on `B' ⊇ B` by a perturbation that does
  not change `w` off `B` is an energy decrease on `B`.
* `IsUpwardMinimizer.isViscSuper`, `IsDownwardMinimizer.isViscSub`,
  `IsLocalEnergyMinimizer.isViscSolution` (Feldman–Kim–Požár, Lemma 3.3; Velichkov, Prop 7.1).
* `IsObstacleMinimizer.isViscSuper_of_upper`, `IsObstacleMinimizer.isViscSub_of_lower`
  (Abedin–Feldman–Stinson, proof of Lemma 6.3, Steps 1–2), including the case where the touching
  point lies on `∂B` (Step 2, case (ii)). There `u ≡ 0` near the point, so the
  perturbation `min(w, (φ - δ)₊)` does not change `w = u = 0` outside `B`. The energy decrease is
  proved on `B ∪ ball x ρ` and transferred to `B` by `energyJ_lt_of_lt_of_eqOn_compl`.

**No harmonicity is used**, neither of `w` nor of the minimizer. The perturbation theorems cover
the case `φ(x) > 0` directly (only `Δφ(x) ≠ 0` is needed there), so the interior case of the
viscosity test needs no comparison with `Δu = 0`. In particular `EnergyMinimizerViscStatement`
does not depend on Weyl's lemma.

## References

* W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- A ball whose closure lies in `U` is compactly contained in `U`. -/
theorem compactlyContained_ball {U : Set (E d)} {x : E d} {r : ℝ} (h : closedBall x r ⊆ U) :
    CompactlyContained (ball x r) U :=
  ⟨(isCompact_closedBall x r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall,
    closure_ball_subset_closedBall.trans h⟩

private theorem exists_closedBall_subset_of_mem {U : Set (E d)} (hU : IsOpen U) {x : E d}
    (hx : x ∈ U) : ∃ r > 0, closedBall x r ⊆ U := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
  exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩

/-- **Supersolution perturbation for non-strict touching.** As
`energy_decrease_of_not_super_of_continuousOn`, with `φ` touching `w` from below at `x` in the
sense of Abedin–Feldman–Stinson, Definition 2.1 (non-strict, relative to `U`). -/
theorem exists_energy_lt_of_touchesBelow {U B : Set (E d)} {Q w φ : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x)
    (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x) (hwH : MemH1Loc U w Gw)
    (hB : IsOpen B) (hBU : CompactlyContained B U) (hφ : ContDiff ℝ ∞ φ) {x : E d}
    (hxB : x ∈ B) (htouch : TouchesBelow φ w U x)
    (hfail : 0 < Δ φ x ∧ (φ x = 0 → Q x < ‖∇ φ x‖))
    {ρ : ℝ} (hρ : 0 < ρ) (hρB : ball x ρ ⊆ B) {η : ℝ} (hη : 0 < η) :
    ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x ρ, w' y = w y) ∧
      (∀ y ∈ U, w y ≤ w' y ∧ w' y ≤ max (w y) (φ y + η)) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  obtain ⟨hψ, hgrad, hlap, -, -⟩ := touchesBelow_strict_perturb hφ htouch
  set ψ : E d → ℝ := fun y ↦ φ y - (‖y - x‖ ^ 2) ^ 2 with hψdef
  have hψx : ψ x = φ x := by simp [hψdef]
  have hψle : ∀ y, ψ y ≤ φ y := fun y ↦ by
    have : 0 ≤ (‖y - x‖ ^ 2) ^ 2 := by positivity
    simp only [hψdef]; linarith
  have hstrict : ∀ᶠ y in 𝓝[≠] x, ψ y < w y := by
    have h := htouch.2.2
    rw [hU.nhdsWithin_eq htouch.1] at h
    rw [eventually_nhdsWithin_iff]
    filter_upwards [h] with y hy hyx
    have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
    have : 0 < (‖y - x‖ ^ 2) ^ 2 := by positivity
    simp only [hψdef]; linarith
  obtain ⟨w', Gw', h1, h2, h3, h4⟩ := energy_decrease_of_not_super_of_continuousOn hU hQ hQ0 hw
    hw0 hwH hB hBU hψ hxB ⟨hψx.trans htouch.2.1, hstrict⟩
    ⟨by rw [hlap]; exact hfail.1, fun h0 ↦ by rw [hgrad]; exact hfail.2 (hψx ▸ h0)⟩ hρ hρB hη
  exact ⟨w', Gw', h1, h2, fun y hy ↦ ⟨(h3 y hy).1,
    (h3 y hy).2.trans (max_le_max le_rfl (by linarith [hψle y]))⟩, h4⟩

/-- **Subsolution perturbation for non-strict touching.** As
`energy_decrease_of_not_sub_of_continuousOn`, with `φ₊` touching `w` from above at `x` in
`closure {w > 0} ∩ U` (non-strict). -/
theorem exists_energy_lt_of_touchesAbove {U B : Set (E d)} {Q w φ : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hw : ContinuousOn w U) (hwH : MemH1Loc U w Gw)
    (hB : IsOpen B) (hBU : CompactlyContained B U) (hφ : ContDiff ℝ ∞ φ) {x : E d}
    (hxB : x ∈ B) (htouch : TouchesAbove (fun y ↦ max (φ y) 0) w (closure (posSet w U) ∩ U) x)
    (hfail : Δ φ x < 0 ∧ (φ x = 0 → ‖∇ φ x‖ < Q x))
    {ρ : ℝ} (hρ : 0 < ρ) (hρB : ball x ρ ⊆ B) {η : ℝ} (hη : 0 < η) :
    ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x ρ, w' y = w y) ∧
      (∀ y ∈ U, min (w y) (max (φ y - η) 0) ≤ w' y ∧ w' y ≤ w y) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  set P := posSet w U with hPdef
  obtain ⟨hψ, hψx', hgrad, hlap⟩ := jet_add_quartic hφ x 1
  set ψ : E d → ℝ := fun y ↦ φ y + 1 * (‖y - x‖ ^ 2) ^ 2 with hψdef
  have hψx : ψ x = φ x := hψx'
  have hψge : ∀ y, φ y ≤ ψ y := fun y ↦ by
    have : 0 ≤ (‖y - x‖ ^ 2) ^ 2 := by positivity
    simp only [hψdef]; linarith
  have hxU : x ∈ U := htouch.1.2
  have hxP : x ∈ closure P := htouch.1.1
  have hev : ∀ᶠ y in 𝓝 x, y ∈ closure P ∩ U → w y ≤ max (φ y) 0 :=
    eventually_nhdsWithin_iff.1 htouch.2.2
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.1 (hev.and (hU.mem_nhds hxU))
  -- `φ ≥ 0` on `closure P` near `x`, since `0 < w ≤ φ₊` on `P` near `x`
  have hφnn : ∀ y ∈ ball x ε ∩ closure P, 0 ≤ φ y := by
    have hsub : ball x ε ∩ P ⊆ {y | 0 ≤ φ y} := fun y hy ↦ by
      have h1 := (hεP y hy.1).1 ⟨subset_closure hy.2, hy.2.1⟩
      by_contra hneg
      rw [mem_ofPred_eq, not_le] at hneg
      rw [max_eq_right hneg.le] at h1
      exact absurd hy.2.2 (not_lt.2 h1)
    intro y hy
    exact closure_minimal hsub (isClosed_le continuous_const hφ.continuous)
      (isOpen_ball.inter_closure hy)
  have hstrict : ∀ᶠ y in 𝓝[(closure P ∩ U) \ {x}] x, w y < max (ψ y) 0 := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds x hε] with y hy hyS
    have h0 := hφnn y ⟨hy, hyS.1.1⟩
    have h1 := (hεP y hy).1 hyS.1
    rw [max_eq_left h0] at h1
    have hyx : y ≠ x := hyS.2
    have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
    have hq : 0 < (‖y - x‖ ^ 2) ^ 2 := by positivity
    have : φ y < ψ y := by simp only [hψdef]; linarith
    exact (h1.trans_lt this).trans_le (le_max_left _ _)
  obtain ⟨w', Gw', h1, h2, h3, h4⟩ := energy_decrease_of_not_sub_of_continuousOn hU hQ hw hwH hB
    hBU hψ hxB hxP ⟨by rw [hψx]; exact htouch.2.1, hstrict⟩
    ⟨by rw [hlap]; exact hfail.1, fun h0 ↦ by rw [hgrad]; exact hfail.2 (hψx ▸ h0)⟩ hρ hρB hη
  exact ⟨w', Gw', h1, h2, fun y hy ↦ ⟨(min_le_min le_rfl
    (max_le_max (by linarith [hψge y]) le_rfl)).trans (h3 y hy).1, (h3 y hy).2⟩, h4⟩

/-- **Localizing an energy decrease.** If `w' = w` on `U \ B` and `J_Q(w'; B') < J_Q(w; B')` for
some `B' ⊇ B` with `B' ⋐ U` and `Q` bounded on `B'`, then `J_Q(w'; B) < J_Q(w; B)`. -/
theorem energyJ_lt_of_lt_of_eqOn_compl {U B B' : Set (E d)} {Q w w' : E d → ℝ}
    {Gw Gw' : E d → E d} (hU : IsOpen U) (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hBB' : B ⊆ B') (hB'c : IsCompact (closure B')) (hB'U : closure B' ⊆ U) {C : ℝ}
    (hQ : ∀ x ∈ B', |Q x| ≤ C) (hw : MemH1Loc U w Gw) (hw' : MemH1Loc U w' Gw')
    (heq : ∀ y ∈ U \ B, w' y = w y) (hlt : energyJ B' Q w' Gw' < energyJ B' Q w Gw) :
    energyJ B Q w' Gw' < energyJ B Q w Gw := by
  have hB'U' : B' ⊆ U := subset_closure.trans hB'U
  have htop := energyJ_lt_top hw hB'c hB'U hQ
  rw [energyJ_split hB hB' hBB' Q w', energyJ_split hB hB' hBB' Q w] at hlt
  rw [energyJ_split hB hB' hBB' Q w] at htop
  have hGae := (hw'.1.sub hw.1).ae_eq_zero_of_eq_zero hU
  have hout : energyJ (B' \ B) Q w' Gw' = energyJ (B' \ B) Q w Gw := by
    refine energyJ_congr (fun y hy ↦ heq y ⟨hB'U' hy.1, hy.2⟩) ?_
    have :=
      ae_restrict_of_ae_restrict_of_subset (show B' \ B ⊆ U from sdiff_subset.trans hB'U') hGae
    rw [ae_restrict_iff' (hB'.diff hB)] at this ⊢
    filter_upwards [this] with y hy hyB
    exact sub_eq_zero.1 (hy hyB (by rw [heq y ⟨hB'U' hyB.1, hyB.2⟩, sub_self]))
  rw [hout] at hlt
  exact (ENNReal.add_lt_add_iff_right (lt_of_le_of_lt le_add_self htop).ne).1 hlt

/-- Upward minimizers are supersolutions (`UpwardViscSuperStatement`; Feldman–Kim–Požár,
Lemma 3.3, Velichkov, Prop 7.1). By contradiction with `exists_energy_lt_of_touchesBelow` on a
ball around the touching point; harmonicity in `{u > 0}` is not used. Feldman–Kim–Požár state
this for the energy with `Q 1_{u>0}` and `Q > 0` constant; since the energy here sees only `Q²`,
the hypothesis `Q ≥ 0` is needed (the statement fails for `Q ≡ −1`, `u = y₊` in `d = 1`). -/
theorem IsUpwardMinimizer.isViscSuper : UpwardViscSuperStatement := by
  intro d U Q u hU hQ hQ0 hu hu0 hmin
  refine ⟨hu, hu0, fun φ hφ x hxU htouch ↦ ?_⟩
  by_contra hcon
  simp only [not_or, not_and, not_le] at hcon
  obtain ⟨Gu, hGu⟩ := hmin.1
  obtain ⟨r, hr, hrU⟩ := exists_closedBall_subset_of_mem hU hxU
  obtain ⟨w', Gw', h1, h2, h3, h4⟩ := exists_energy_lt_of_touchesBelow hU hQ hQ0 hu hu0 hGu
    isOpen_ball (compactlyContained_ball hrU) hφ (mem_ball_self hr) htouch hcon hr subset_rfl
    one_pos
  have := hmin.2.2.2.2 x r hr hrU Gu w' Gw' hGu h1
    ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun y hy ↦ (h3 y hy).1))
    ((ae_restrict_iff' (hU.measurableSet.diff measurableSet_ball)).2
      (Eventually.of_forall fun y hy ↦ h2 y hy))
  exact absurd h4 (not_lt.2 this)

/-- Downward minimizers are subsolutions (`DownwardViscSubStatement`; Feldman–Kim–Požár,
Lemma 3.3, Velichkov, Prop 7.1). By contradiction with `exists_energy_lt_of_touchesAbove`. -/
theorem IsDownwardMinimizer.isViscSub : DownwardViscSubStatement := by
  intro d U Q u hU hQ hu hu0 hmin
  refine ⟨hu, hu0, fun φ hφ x htouch ↦ ?_⟩
  by_contra hcon
  simp only [not_or, not_and, not_le] at hcon
  obtain ⟨Gu, hGu⟩ := hmin.1
  obtain ⟨r, hr, hrU⟩ := exists_closedBall_subset_of_mem hU htouch.1.2
  obtain ⟨w', Gw', h1, h2, h3, h4⟩ := exists_energy_lt_of_touchesAbove hU hQ hu hGu
    isOpen_ball (compactlyContained_ball hrU) hφ (mem_ball_self hr) htouch hcon hr subset_rfl
    one_pos
  have := hmin.2.2.2.2 x r hr hrU Gu w' Gw' hGu h1
    ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall fun y hy ↦ (h3 y hy).2))
    ((ae_restrict_iff' (hU.measurableSet.diff measurableSet_ball)).2
      (Eventually.of_forall fun y hy ↦ h2 y hy))
  exact absurd h4 (not_lt.2 this)

/-- Continuous local energy minimizers are viscosity solutions (`EnergyMinimizerViscStatement`;
Velichkov, Prop 7.1). Both halves by contradiction with the perturbation theorems; harmonicity in
`{u > 0}` (and hence Weyl's lemma) is not needed. As for upward minimizers, `Q ≥ 0` is needed,
because the energy sees only `Q²`. -/
theorem IsLocalEnergyMinimizer.isViscSolution : EnergyMinimizerViscStatement := by
  intro d U Q u hU hQ hQ0 hu hu0 ⟨Gu, hGu, hmin⟩
  refine ⟨⟨hu, hu0, fun φ hφ x hxU htouch ↦ ?_⟩, ⟨hu, hu0, fun φ hφ x htouch ↦ ?_⟩⟩
  · by_contra hcon
    simp only [not_or, not_and, not_le] at hcon
    obtain ⟨r, hr, hrU⟩ := exists_closedBall_subset_of_mem hU hxU
    obtain ⟨w', Gw', h1, h2, -, h4⟩ := exists_energy_lt_of_touchesBelow hU hQ hQ0 hu hu0 hGu
      isOpen_ball (compactlyContained_ball hrU) hφ (mem_ball_self hr) htouch hcon hr subset_rfl
      one_pos
    have := (hmin x r hr hrU).2.2.2 w' Gw' h1
      ((ae_restrict_iff' (hU.measurableSet.diff measurableSet_ball)).2
        (Eventually.of_forall fun y hy ↦ h2 y hy)) (Eventually.of_forall fun _ ↦ mem_univ _)
    exact absurd h4 (not_lt.2 this)
  · by_contra hcon
    simp only [not_or, not_and, not_le] at hcon
    obtain ⟨r, hr, hrU⟩ := exists_closedBall_subset_of_mem hU htouch.1.2
    obtain ⟨w', Gw', h1, h2, -, h4⟩ := exists_energy_lt_of_touchesAbove hU hQ hu hGu
      isOpen_ball (compactlyContained_ball hrU) hφ (mem_ball_self hr) htouch hcon hr subset_rfl
      one_pos
    have := (hmin x r hr hrU).2.2.2 w' Gw' h1
      ((ae_restrict_iff' (hU.measurableSet.diff measurableSet_ball)).2
        (Eventually.of_forall fun y hy ↦ h2 y hy)) (Eventually.of_forall fun _ ↦ mem_univ _)
    exact absurd h4 (not_lt.2 this)

/-- Obstacle minimizers below a supersolution are supersolutions (`ObstacleViscSuperStatement`;
Abedin–Feldman–Stinson, proof of Lemma 6.3, Step 1). At a contact point `w = u` the test
function touches `u`; elsewhere `w < u` near the point, which lies in `B`, and the supersolution
perturbation stays below `u`. -/
theorem IsObstacleMinimizer.isViscSuper_of_upper : ObstacleViscSuperStatement := by
  intro d U Q u w Gw x₀ r hU ⟨L, hL⟩ ⟨c, hc, hcQ⟩ _ hu hr hmin hw
  have hQc : ContinuousOn Q U := hL.continuousOn
  have hQ0 : ∀ y ∈ U, 0 ≤ Q y := fun y hy ↦ hc.le.trans (hcQ y hy)
  obtain ⟨hwH, hwbd, hwK, hwmin⟩ := hmin
  have hw0 : ∀ y ∈ U, 0 ≤ w y := fun y hy ↦ (hwK y hy).1
  have hwu : ∀ y ∈ U, w y ≤ u y := fun y hy ↦ (hwK y hy).2
  refine ⟨hw, hw0, fun φ hφ x hxU htouch ↦ ?_⟩
  by_contra hcon
  have hfail := hcon
  simp only [not_or, not_and, not_le] at hfail
  rcases (hwu x hxU).lt_or_eq with hlt | heq
  · -- `w(x) < u(x)`: then `x ∈ B`, and the perturbation stays below `u`
    have hxB : x ∈ ball x₀ r := by
      by_contra hxB
      exact hlt.ne (hwbd x ⟨hxU, hxB⟩)
    set η := (u x - w x) / 2 with hηdef
    have hη : 0 < η := by rw [hηdef]; linarith
    have hucont : ContinuousAt u x := hu.1.continuousAt (hU.mem_nhds hxU)
    have hφc : ContinuousAt (fun y ↦ φ y + η) x := (hφ.continuous.add continuous_const).continuousAt
    have hev : ∀ᶠ y in 𝓝 x, φ y + η < u y :=
      hφc.eventually_lt hucont (by rw [htouch.2.1, hηdef]; linarith)
    obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff_ball.1
      (hev.and (isOpen_ball.mem_nhds hxB))
    obtain ⟨w', Gw', h1, h2, h3, h4⟩ := exists_energy_lt_of_touchesBelow hU hQc hQ0 hw hw0 hwH
      isOpen_ball (compactlyContained_ball hr) hφ hxB htouch hfail hρ
      (fun y hy ↦ (hρP y hy).2) hη
    have hoff : ∀ y ∈ U \ ball x₀ r, w' y = u y := fun y hy ↦ by
      have : y ∉ ball x ρ := fun h ↦ hy.2 (hρP y h).2
      rw [h2 y ⟨hy.1, this⟩, hwbd y hy]
    have hK : ∀ y ∈ U, w' y ∈ Icc 0 (u y) := fun y hy ↦ by
      refine ⟨(hw0 y hy).trans (h3 y hy).1, ?_⟩
      by_cases hyρ : y ∈ ball x ρ
      · exact (h3 y hy).2.trans (max_le (hwu y hy) (hρP y hyρ).1.le)
      · rw [h2 y ⟨hy, hyρ⟩]; exact hwu y hy
    have := hwmin w' Gw' h1
      ((ae_restrict_iff' (hU.measurableSet.diff measurableSet_ball)).2 (Eventually.of_forall hoff))
      ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall hK))
    exact absurd h4 (not_lt.2 this)
  · -- contact point: `φ` touches the supersolution `u`
    apply hcon
    refine hu.2.2 φ hφ x hxU ⟨hxU, htouch.2.1.trans heq, ?_⟩
    filter_upwards [htouch.2.2, self_mem_nhdsWithin] with y hy hyU using hy.trans (hwu y hyU)

/-- Obstacle minimizers above a subsolution are subsolutions (`ObstacleViscSubStatement`;
Abedin–Feldman–Stinson, proof of Lemma 6.3, Step 2). Cases:
(i) `w(x) > u(x)`: then `x ∈ B` and `(φ - η)₊ > u` near `x`, so the subsolution perturbation
stays above `u`;
(ii) `w(x) = u(x)`, `x ∉ closure {u > 0}`: `u ≡ 0` near `x`, so the perturbation stays above `u`
and does not change `w = u = 0` outside `B`, even when `x ∈ ∂B`;
(iii) `w(x) = u(x)`, `x ∈ closure {u > 0}`: `φ₊` touches the subsolution `u`. -/
theorem IsObstacleMinimizer.isViscSub_of_lower : ObstacleViscSubStatement := by
  intro d U Q u w Gw x₀ r hU ⟨L, hL⟩ _ _ hu hr hmin hw
  have hQc : ContinuousOn Q U := hL.continuousOn
  obtain ⟨hwH, hwbd, hwK, hwmin⟩ := hmin
  have huw : ∀ y ∈ U, u y ≤ w y := fun y hy ↦ hwK y hy
  have hu0 : ∀ y ∈ U, 0 ≤ u y := hu.2.1
  have hw0 : ∀ y ∈ U, 0 ≤ w y := fun y hy ↦ (hu0 y hy).trans (huw y hy)
  refine ⟨hw, hw0, fun φ hφ x htouch ↦ ?_⟩
  have hxU : x ∈ U := htouch.1.2
  by_contra hcon
  have hfail := hcon
  simp only [not_or, not_and, not_le] at hfail
  -- the common finishing step: an admissible perturbation on `B ∪ ball x ρ`
  have finish : ∀ ρ > 0, closedBall x ρ ⊆ U → ∀ η > 0,
      (∀ y ∈ U ∩ ball x ρ, u y ≤ min (w y) (max (φ y - η) 0)) →
      (∀ y ∈ (U ∩ ball x ρ) \ ball x₀ r, w y = 0) → False := by
    intro ρ hρ hρU η hη hAu hAw
    set B' := ball x₀ r ∪ ball x ρ with hB'def
    have hB'o : IsOpen B' := isOpen_ball.union isOpen_ball
    have hB'c : IsCompact (closure B') := by
      rw [hB'def, closure_union]
      exact (compactlyContained_ball hr).1.union (compactlyContained_ball hρU).1
    have hB'U : closure B' ⊆ U := by
      rw [hB'def, closure_union]
      exact union_subset (compactlyContained_ball hr).2 (compactlyContained_ball hρU).2
    obtain ⟨w', Gw', h1, h2, h3, h4⟩ := exists_energy_lt_of_touchesAbove hU hQc hw hwH hB'o
      ⟨hB'c, hB'U⟩ hφ (Or.inr (mem_ball_self hρ)) htouch hfail hρ subset_union_right hη
    have heqB : ∀ y ∈ U \ ball x₀ r, w' y = w y := fun y hy ↦ by
      by_cases hyρ : y ∈ ball x ρ
      · have hw0y := hAw y ⟨⟨hy.1, hyρ⟩, hy.2⟩
        have hlo := (h3 y hy.1).1
        have hhi := (h3 y hy.1).2
        rw [hw0y, min_eq_left (le_max_right _ _)] at hlo
        rw [hw0y] at hhi ⊢
        exact le_antisymm hhi hlo
      · exact h2 y ⟨hy.1, hyρ⟩
    obtain ⟨C, hC⟩ := hB'c.exists_bound_of_continuousOn (hQc.mono hB'U)
    have hltB := energyJ_lt_of_lt_of_eqOn_compl hU measurableSet_ball hB'o.measurableSet
      subset_union_left hB'c hB'U (C := C)
      (fun y hy ↦ by simpa [Real.norm_eq_abs] using hC y (subset_closure hy)) hwH h1 heqB h4
    have hoff : ∀ y ∈ U \ ball x₀ r, w' y = u y := fun y hy ↦ by
      rw [heqB y hy, hwbd y hy]
    have hK : ∀ y ∈ U, w' y ∈ Ici (u y) := fun y hy ↦ by
      by_cases hyρ : y ∈ ball x ρ
      · exact (hAu y ⟨hy, hyρ⟩).trans (h3 y hy).1
      · rw [mem_Ici, h2 y ⟨hy, hyρ⟩]; exact huw y hy
    have := hwmin w' Gw' h1
      ((ae_restrict_iff' (hU.measurableSet.diff measurableSet_ball)).2 (Eventually.of_forall hoff))
      ((ae_restrict_iff' hU.measurableSet).2 (Eventually.of_forall hK))
    exact absurd hltB (not_lt.2 this)
  rcases (huw x hxU).lt_or_eq with hlt | heq
  · -- case (i): `u(x) < w(x)`
    have hxB : x ∈ ball x₀ r := by
      by_contra hxB
      exact hlt.ne (hwbd x ⟨hxU, hxB⟩).symm
    have hφx : φ x = w x := by
      have h : max (φ x) 0 = w x := htouch.2.1
      rcases le_total (φ x) 0 with hle | hle
      · rw [max_eq_right hle] at h
        linarith [hu0 x hxU]
      · rwa [max_eq_left hle] at h
    set η := (w x - u x) / 2 with hηdef
    have hη : 0 < η := by rw [hηdef]; linarith
    have hucont : ContinuousAt u x := hu.1.continuousAt (hU.mem_nhds hxU)
    have hφc : ContinuousAt (fun y ↦ φ y - η) x := (hφ.continuous.sub continuous_const).continuousAt
    have hev : ∀ᶠ y in 𝓝 x, u y < φ y - η :=
      hucont.eventually_lt hφc (by rw [hφx, hηdef]; linarith)
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.1
      (hev.and (isOpen_ball.mem_nhds hxB))
    refine finish (ε / 2) (by positivity)
      ((closedBall_subset_ball (by linarith)).trans
        (fun y hy ↦ (compactlyContained_ball hr).2 (subset_closure (hεP y hy).2)))
      η hη (fun y hy ↦ ?_) (fun y hy ↦ ?_)
    · have hyε : y ∈ ball x ε := ball_subset_ball (by linarith) hy.2
      exact le_min (huw y hy.1) (((hεP y hyε).1.le).trans (le_max_left _ _))
    · exact absurd (hεP y (ball_subset_ball (by linarith) hy.1.2)).2 hy.2
  · by_cases hxPu : x ∈ closure (posSet u U)
    · -- case (iii): contact point in `closure {u > 0}`: `φ₊` touches the subsolution `u`
      apply hcon
      have hPuw : closure (posSet u U) ⊆ closure (posSet w U) :=
        closure_mono fun y hy ↦ ⟨hy.1, hy.2.trans_le (huw y hy.1)⟩
      refine hu.2.2 φ hφ x ⟨⟨hxPu, hxU⟩, htouch.2.1.trans heq.symm, ?_⟩
      have h := nhdsWithin_mono x (inter_subset_inter_left U hPuw) htouch.2.2
      filter_upwards [h, self_mem_nhdsWithin] with y hy hyS using (huw y hyS.2).trans hy
    · -- case (ii): `u ≡ 0` near `x` (possibly `x ∈ ∂B`)
      have hev : ∀ᶠ y in 𝓝 x, y ∉ posSet u U :=
        Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds hxPu)
          fun y hy h ↦ hy (subset_closure h)
      obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.1 hev
      have hu0' : ∀ y ∈ U ∩ ball x ε, u y = 0 := fun y hy ↦
        le_antisymm (not_lt.1 fun h ↦ hεP y hy.2 ⟨hy.1, h⟩) (hu0 y hy.1)
      obtain ⟨r', hr', hr'U⟩ := exists_closedBall_subset_of_mem hU hxU
      set ρ := min r' (ε / 2) with hρdef
      have hρ : 0 < ρ := lt_min hr' (by positivity)
      have hρε : ∀ y ∈ ball x ρ, y ∈ ball x ε := fun y hy ↦
        ball_subset_ball ((min_le_right _ _).trans (by linarith)) hy
      refine finish ρ hρ ((closedBall_subset_closedBall (min_le_left _ _)).trans hr'U) 1 one_pos
        (fun y hy ↦ ?_) (fun y hy ↦ ?_)
      · rw [hu0' y ⟨hy.1, hρε y hy.2⟩]
        exact le_min (hw0 y hy.1) (le_max_right _ _)
      · rw [hwbd y ⟨hy.1.1, hy.2⟩]
        exact hu0' y ⟨hy.1.1, hρε y hy.1.2⟩

end EllipticBernoulli
