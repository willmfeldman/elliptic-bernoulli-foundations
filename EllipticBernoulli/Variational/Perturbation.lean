/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Variational
public import EllipticBernoulli.Variational.PerturbationCalculus
import EllipticBernoulli.Viscosity.Jet
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Common.Calculus

/-!
# Energy-decreasing perturbations

If a smooth `φ` touches a continuous `w ∈ H¹_loc(U)`, `w ≥ 0`, strictly at `x₀` and the viscosity
test of Abedin–Feldman–Stinson, Definition 2.1, fails at `x₀`, then a local perturbation of `w`
near `x₀` strictly lowers the energy `J_Q(·; B)`, `J_Q = ∫ |∇v|² + Q² 1_{v>0}`.

* `energy_decrease_of_not_super_of_continuousOn` (general form: `Q` continuous and `≥ 0` on `U`):
  supersolution test fails at a strict touching point from below. Perturbation
  `w' = max(w, φ + δ)` near `x₀`.
* `energy_decrease_of_not_sub_of_continuousOn` (general form: `Q` continuous on `U`): subsolution
  test fails at a strict touching point from above, relative to `closure {w > 0}`. Perturbation
  `w' = min(w, (φ - δ)₊)` near `x₀`.
* `energy_decrease_of_not_super`, `energy_decrease_of_not_sub`: the headline statements
  (`EnergyDecreaseSuperStatement`, `EnergyDecreaseSubStatement`), from the general forms. They
  assume `Q` Lipschitz with `0 < c ≤ Q`; the proofs use only continuity of `Q` (and `Q ≥ 0` for
  the supersolution case), and the subsolution case does not need `w ≥ 0`.

## Construction

Localize to `ball x₀ ε` where `Δφ` has a strict sign and the free-boundary alternative fails. With
`r₁ < r₀ < ε`, strict touching and compactness give `δ₀ > 0` with a gap `≥ δ₀` between `w` and
`φ` (resp. `φ₊`) on the annulus `closedBall x₀ r₀ \ ball x₀ r₁` (for the subsolution case, only on
`closure {w > 0}`). For `δ < δ₀` and a smooth cut-off `χ = 1` on `closedBall x₀ r₁` supported in
`ball x₀ r₀`, the perturbations are
`w' = w + χ (φ + δ - w)₊` and `w' = w - χ (w - (φ - δ)₊)₊`.
Both are in `H¹_loc(U)` by the lattice rules, and `w' ≠ w` only inside `ball x₀ r₁`, where `χ = 1`.
The weak gradient of `w'` is identified a.e. by Stampacchia's lemma on the sets `{w' = w}`,
`{w' = φ ± δ}` and `{w' = 0}`; its explicit formula is never needed. In particular no nullness of
`{φ = δ}` is used. The energy comparison is `energyJ_lt_of_le_add_inner`.

**No harmonicity of `w` is used.** Only continuity, `w ≥ 0`, `w ∈ H¹_loc`, and Stampacchia's lemma
`∇w = 0` a.e. on `{w = 0}` are needed.

The computation follows Feldman–Kim–Požár, proof of Lemma 3.3, and Lemma A.1. Their energy is
`∫ |∇v|² + Q 1_{v>0}`, with free boundary condition `|∇u|² = Q`; here the coefficient enters
squared and the condition is `|∇u| = Q`. Their proof compares against a sub/superharmonic
extension, which uses harmonicity of `u` in `{u > 0}`, and treats only touching points on the free
boundary with `∇φ ≠ 0`. The computation here integrates by parts against `φ` itself and covers
every test point through the sign of `Δφ` alone.

## References

* W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- A function continuous and positive on a compact set is bounded below there by a positive
constant. -/
theorem exists_pos_le_of_isCompact {K : Set (E d)} (hK : IsCompact K) {f : E d → ℝ}
    (hf : ContinuousOn f K) (hpos : ∀ x ∈ K, 0 < f x) : ∃ c > 0, ∀ x ∈ K, c ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf
    exact ⟨f x, hpos x hx, fun y hy ↦ hmin hy⟩

/-- `max a 0 - δ ≤ max (a - δ) 0` for `δ ≥ 0`. -/
private theorem max_sub_le_max_sub {a δ : ℝ} (hδ : 0 ≤ δ) : max a 0 - δ ≤ max (a - δ) 0 := by
  rw [sub_le_iff_le_add]
  exact max_le (by linarith [le_max_left (a - δ) 0]) (by linarith [le_max_right (a - δ) 0])

private theorem continuousOn_max_zero {f : E d → ℝ} {s : Set (E d)} (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ max (f x) 0) s :=
  (continuous_id.max continuous_const).comp_continuousOn hf

/-- `2⟪a, b⟫ ≤ ‖a‖² + ‖b‖²`. -/
private theorem inner_le_aux (a b : E d) : 2 * inner ℝ a b ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h := norm_sub_sq_real a b
  nlinarith [sq_nonneg ‖a - b‖]

/-- **Supersolution perturbation, general form.** Let `U` be open, `Q` continuous and `≥ 0` on `U`,
and `w ≥ 0` continuous on `U` with `w ∈ H¹_loc(U)`. Let `B ⋐ U` be open, and let the smooth `φ`
touch `w` strictly from below at `x₀ ∈ B` with `Δφ(x₀) > 0` and, if `φ(x₀) = 0`, `|∇φ(x₀)| > Q(x₀)`.
Then for every `ρ > 0` with `ball x₀ ρ ⊆ B` and every `η > 0` there is `w' ∈ H¹_loc(U)` with
`w' = w` off `ball x₀ ρ`, `w ≤ w' ≤ max(w, φ + η)` on `U` and `J_Q(w'; B) < J_Q(w; B)`. -/
theorem energy_decrease_of_not_super_of_continuousOn {U : Set (E d)} {Q w : E d → ℝ}
    {Gw : E d → E d} (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x)
    (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x) (hwH : MemH1Loc U w Gw)
    {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (htouch : φ x₀ = w x₀ ∧ ∀ᶠ y in 𝓝[≠] x₀, φ y < w y)
    (hfail : 0 < Δ φ x₀ ∧ (φ x₀ = 0 → Q x₀ < ‖∇ φ x₀‖))
    {ρ : ℝ} (hρ : 0 < ρ) (hρB : ball x₀ ρ ⊆ B) {η : ℝ} (hη : 0 < η) :
    ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, w y ≤ w' y ∧ w' y ≤ max (w y) (φ y + η)) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  have hBU' : B ⊆ U := subset_closure.trans hBU.2
  have hx₀U : x₀ ∈ U := hBU' hx₀
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hΔc : Continuous (Δ φ) := continuous_laplacian (contDiff_two_of_smooth hφ)
  have hgc : Continuous (∇ φ) := continuous_gradient hφ1
  have hwc : ContinuousAt w x₀ := hw.continuousAt (hU.mem_nhds hx₀U)
  -- localization
  have hQev : ∀ᶠ y in 𝓝 x₀, w y = 0 → Q y ≤ ‖∇ φ y‖ := by
    by_cases h0 : φ x₀ = 0
    · filter_upwards [(hQ.continuousAt (hU.mem_nhds hx₀U)).eventually_lt hgc.norm.continuousAt
        (hfail.2 h0)] with y hy _ using hy.le
    · have hpos : 0 < w x₀ :=
        lt_of_le_of_ne (hw0 x₀ hx₀U) fun h ↦ h0 (htouch.1.trans h.symm)
      filter_upwards [continuousAt_const.eventually_lt hwc hpos] with y hy hy0
      exact absurd hy0 hy.ne'
  have hΔev : ∀ᶠ y in 𝓝 x₀, 0 < Δ φ y :=
    continuousAt_const.eventually_lt hΔc.continuousAt hfail.1
  have htev : ∀ᶠ y in 𝓝 x₀, y ∈ ({x₀}ᶜ : Set (E d)) → φ y < w y :=
    eventually_nhdsWithin_iff.1 htouch.2
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff_ball.1
    (hQev.and (hΔev.and (htev.and (ball_mem_nhds x₀ hρ))))
  have hεU : ball x₀ ε ⊆ U := fun y hy ↦ hBU' (hρB (hP y hy).2.2.2)
  set r₀ := ε / 2 with hr₀
  set r₁ := ε / 4 with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁₀ : r₁ < r₀ := by rw [hr₀, hr₁]; linarith
  have hr₀ε : r₀ < ε := by rw [hr₀]; linarith
  have hcb : closedBall x₀ r₀ ⊆ ball x₀ ε := closedBall_subset_ball hr₀ε
  have hcb₁ : closedBall x₀ r₁ ⊆ ball x₀ ε := closedBall_subset_ball (hr₁₀.trans hr₀ε)
  -- the gap on the annulus
  have hAnnc : IsCompact (closedBall x₀ r₀ \ ball x₀ r₁) :=
    (isCompact_closedBall x₀ r₀).diff isOpen_ball
  have hAnnU : closedBall x₀ r₀ \ ball x₀ r₁ ⊆ U := fun y hy ↦ hεU (hcb hy.1)
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_of_isCompact hAnnc (f := fun y ↦ w y - φ y)
    ((hw.mono hAnnU).sub hφ.continuous.continuousOn) fun y hy ↦ by
      have hne : y ≠ x₀ := by
        rintro rfl; exact hy.2 (mem_ball_self hr₁0)
      exact sub_pos.2 ((hP y (hcb hy.1)).2.2.1 hne)
  set δ := min δ₀ η / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hδδ₀ : δ < δ₀ := by
    rw [hδdef]; linarith [min_le_left δ₀ η, lt_min hδ₀ hη]
  have hδη : δ < η := by
    rw [hδdef]; linarith [min_le_right δ₀ η, lt_min hδ₀ hη]
  -- the cut-off and the perturbation
  obtain ⟨χ, hχ, -, hχs, hχ01, hχ1⟩ :=
    exists_smooth_cutoff (isCompact_closedBall x₀ r₁) isOpen_ball (closedBall_subset_ball hr₁₀)
  set w' : E d → ℝ := fun y ↦ w y + χ y * max (φ y + δ - w y) 0 with hw'def
  have hφH : MemH1Loc U φ (∇ φ) := memH1Loc_gradient_of_contDiff hU hφ1
  have hφδ : MemH1Loc U (fun y ↦ φ y + δ) (∇ φ) := by
    simpa [sub_neg_eq_add] using hφH.sub_const (-δ)
  obtain ⟨Gw', hw'H⟩ : ∃ G, MemH1Loc U w' G :=
    ⟨_, hwH.add ((memH1Loc_posPart hU (hφδ.sub hwH)).mul_smooth hU hχ)⟩
  have hdiff : ∀ y, w' y - w y = χ y * max (φ y + δ - w y) 0 := fun y ↦ by
    simp only [hw'def]; ring
  -- where `w'` differs from `w`
  have hkey : ∀ y, w' y ≠ w y → y ∈ ball x₀ r₁ ∧ w' y = φ y + δ ∧ w y < φ y + δ := by
    intro y hy
    have hne : χ y * max (φ y + δ - w y) 0 ≠ 0 := by
      intro h; apply hy; rw [← sub_eq_zero, hdiff, h]
    have hχne : χ y ≠ 0 := left_ne_zero_of_mul hne
    have hmx : max (φ y + δ - w y) 0 ≠ 0 := right_ne_zero_of_mul hne
    have hlt : w y < φ y + δ := by
      by_contra h
      exact hmx (max_eq_right (by linarith))
    have hyr₀ : y ∈ closedBall x₀ r₀ :=
      ball_subset_closedBall (hχs (subset_tsupport _ hχne))
    have hyr₁ : y ∈ ball x₀ r₁ := by
      by_contra h
      have := hδ₀le y ⟨hyr₀, h⟩
      linarith
    refine ⟨hyr₁, ?_, hlt⟩
    have h1 := hχ1 y (ball_subset_closedBall hyr₁)
    simp only [hw'def, h1, one_mul, max_eq_left (by linarith : 0 ≤ φ y + δ - w y)]
    ring
  have hr₁ρ : ∀ y ∈ ball x₀ r₁, y ∈ ball x₀ ρ := fun y hy ↦
    (hP y (hcb₁ (ball_subset_closedBall hy))).2.2.2
  have hKB : closedBall x₀ r₁ ⊆ B := fun y hy ↦ hρB (hP y (hcb₁ hy)).2.2.2
  have hKU : closedBall x₀ r₁ ⊆ U := hKB.trans hBU'
  refine ⟨w', Gw', hw'H, fun y hy ↦ ?_, fun y hy ↦ ⟨?_, ?_⟩, ?_⟩
  · by_contra h
    exact hy.2 (hr₁ρ y (hkey y h).1)
  · have := mul_nonneg (hχ01 y).1 (le_max_right (φ y + δ - w y) 0)
    linarith [hdiff y]
  · by_cases h : w' y = w y
    · rw [h]; exact le_max_left _ _
    · rw [(hkey y h).2.1]; exact le_max_of_le_right (by linarith)
  -- the energy comparison
  obtain ⟨C, hC⟩ := hBU.1.exists_bound_of_continuousOn (hQ.mono hBU.2)
  refine energyJ_lt_of_le_add_inner hU hB.measurableSet hBU.1 hBU.2 (isCompact_closedBall x₀ r₁)
    hKB hQ (C := C) (fun x hx ↦ by simpa [Real.norm_eq_abs] using hC x (subset_closure hx))
    hwH hw'H hφ (fun x hx ↦ ?_) ?_ ?_
  · by_contra h
    exact hx.2 (ball_subset_closedBall (hkey x h).1)
  · -- the pointwise inequality
    have ha := (hw'H.1.sub hwH.1).ae_eq_zero_of_eq_zero hU
    have hb := (hw'H.1.sub hφH.1).ae_eq_zero_of_eq_const hU δ
    have hc := hwH.1.ae_eq_zero_of_eq_zero hU
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU ha,
      ae_restrict_of_ae_restrict_of_subset hKU hb, ae_restrict_of_ae_restrict_of_subset hKU hc,
      ae_restrict_mem measurableSet_closedBall] with x ha hb hc hxK
    have hxU := hKU hxK
    by_cases h : w' x = w x
    · have hG : Gw' x = Gw x := sub_eq_zero.1 (ha (by rw [h, sub_self]))
      rw [h, hG, sub_self, inner_zero_left, mul_zero, add_zero]
    · obtain ⟨hxb, hw'x, hlt⟩ := hkey x h
      have hG : Gw' x = ∇ φ x := sub_eq_zero.1 (hb (by rw [hw'x]; ring))
      have hw'pos : 0 < w' x := by rw [hw'x]; linarith [hw0 x hxU]
      rw [hG, indicator_of_mem (show w' x ∈ Ioi (0 : ℝ) from hw'pos), Pi.one_apply, mul_one,
        inner_sub_left, real_inner_self_eq_norm_sq]
      have haux := inner_le_aux (Gw x) (∇ φ x)
      rcases (hw0 x hxU).lt_or_eq with hpos | hzero
      · rw [indicator_of_mem (show w x ∈ Ioi (0 : ℝ) from hpos), Pi.one_apply]
        linarith
      · have hGw : Gw x = 0 := hc hzero.symm
        have hQle := (hP x (hcb₁ hxK)).1 hzero.symm
        rw [← hzero, hGw, indicator_of_notMem (show (0 : ℝ) ∉ Ioi (0 : ℝ) by simp)]
        simp only [norm_zero, inner_zero_left]
        linarith [pow_le_pow_left₀ (hQ0 x hxU) hQle 2]
  · -- positivity of `∫ (w' - w) Δφ`
    refine integral_pos_of_continuousOn hU (isCompact_closedBall x₀ r₁) hKU (y := x₀) ?_ ?_ ?_
      hx₀U ?_
    · have h1 : ContinuousOn (fun x ↦ φ x + δ - w x) U :=
        (hφ.continuous.add continuous_const).continuousOn.sub hw
      have hc : ContinuousOn (fun x ↦ χ x * max (φ x + δ - w x) 0 * Δ φ x) U :=
        (hχ.continuous.continuousOn.mul (continuousOn_max_zero h1)).mul hΔc.continuousOn
      exact hc.congr fun x _ ↦ by rw [hdiff]
    · intro x hx
      by_cases h : w' x = w x
      · rw [h, sub_self, zero_mul]
      · obtain ⟨hxb, hw'x, hlt⟩ := hkey x h
        exact mul_nonneg (by linarith) (hP x (hcb₁ (ball_subset_closedBall hxb))).2.1.le
    · intro x hx
      have : w' x = w x := by
        by_contra h; exact hx.2 (ball_subset_closedBall (hkey x h).1)
      rw [this, sub_self, zero_mul]
    · rw [hdiff, hχ1 x₀ (mem_closedBall_self hr₁0.le), one_mul, htouch.1,
        show w x₀ + δ - w x₀ = δ by ring, max_eq_left hδ.le]
      exact mul_pos hδ hfail.1

/-- **Subsolution perturbation, general form.** Let `U` be open, `Q` continuous on `U`, and `w`
continuous on `U` with `w ∈ H¹_loc(U)` (the sign of `w` is not needed here). Let `B ⋐ U` be open,
`x₀ ∈ B ∩ closure {w > 0}`, and let `φ₊` touch `w` strictly from above at `x₀` relative to
`closure {w > 0} ∩ U`, with `Δφ(x₀) < 0` and, if `φ(x₀) = 0`, `|∇φ(x₀)| < Q(x₀)`. Then for every
`ρ > 0` with `ball x₀ ρ ⊆ B` and every `η > 0` there is `w' ∈ H¹_loc(U)` with `w' = w` off
`ball x₀ ρ`, `min(w, (φ - η)₊) ≤ w' ≤ w` on `U` and `J_Q(w'; B) < J_Q(w; B)`. -/
theorem energy_decrease_of_not_sub_of_continuousOn {U : Set (E d)} {Q w : E d → ℝ}
    {Gw : E d → E d} (hU : IsOpen U) (hQ : ContinuousOn Q U)
    (hw : ContinuousOn w U) (hwH : MemH1Loc U w Gw)
    {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (hx₀P : x₀ ∈ closure (posSet w U))
    (htouch : max (φ x₀) 0 = w x₀ ∧
      ∀ᶠ y in 𝓝[(closure (posSet w U) ∩ U) \ {x₀}] x₀, w y < max (φ y) 0)
    (hfail : Δ φ x₀ < 0 ∧ (φ x₀ = 0 → ‖∇ φ x₀‖ < Q x₀))
    {ρ : ℝ} (hρ : 0 < ρ) (hρB : ball x₀ ρ ⊆ B) {η : ℝ} (hη : 0 < η) :
    ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, min (w y) (max (φ y - η) 0) ≤ w' y ∧ w' y ≤ w y) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  set P := posSet w U with hPdef
  have hBU' : B ⊆ U := subset_closure.trans hBU.2
  have hx₀U : x₀ ∈ U := hBU' hx₀
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hΔc : Continuous (Δ φ) := continuous_laplacian (contDiff_two_of_smooth hφ)
  have hgc : Continuous (∇ φ) := continuous_gradient hφ1
  have hwc : ContinuousAt w x₀ := hw.continuousAt (hU.mem_nhds hx₀U)
  have htev : ∀ᶠ y in 𝓝 x₀, y ∈ (closure P ∩ U) \ {x₀} → w y < max (φ y) 0 :=
    eventually_nhdsWithin_iff.1 htouch.2
  -- `φ(x₀) ≥ 0`: otherwise `φ₊ = 0` near `x₀` while `w > 0` at points of `P` near `x₀`
  have hφ0 : 0 ≤ φ x₀ := by
    by_contra hneg
    rw [not_le] at hneg
    have hw0x : w x₀ = 0 := by rw [← htouch.1, max_eq_right hneg.le]
    have hev : ∀ᶠ y in 𝓝 x₀, φ y < 0 :=
      hφ.continuous.continuousAt.eventually_lt continuousAt_const hneg
    obtain ⟨y, ⟨hy1, hy2⟩, hyP⟩ := mem_closure_iff_nhds.1 hx₀P _ (hev.and htev)
    have hyx : y ≠ x₀ := by
      rintro rfl; exact absurd hyP.2 (by rw [hw0x]; exact lt_irrefl 0)
    have := hy2 ⟨⟨subset_closure hyP, hyP.1⟩, hyx⟩
    rw [max_eq_right hy1.le] at this
    exact absurd hyP.2 (not_lt.2 this.le)
  have hwx₀ : w x₀ = φ x₀ := by rw [← htouch.1, max_eq_left hφ0]
  -- the threshold `θ` below which the free-boundary inequality `|∇φ| ≤ Q` holds
  obtain ⟨θ, hθ, hθev⟩ : ∃ θ > 0, ∀ᶠ y in 𝓝 x₀, φ y ≤ θ → ‖∇ φ y‖ ≤ Q y := by
    rcases hφ0.lt_or_eq with hpos | hzero
    · refine ⟨φ x₀ / 2, by linarith, ?_⟩
      filter_upwards [continuousAt_const.eventually_lt hφ.continuous.continuousAt
        (show φ x₀ / 2 < φ x₀ by linarith)] with y hy hle
      exact absurd hle (not_le.2 hy)
    · refine ⟨1, one_pos, ?_⟩
      filter_upwards [hgc.norm.continuousAt.eventually_lt (hQ.continuousAt (hU.mem_nhds hx₀U))
        (hfail.2 hzero.symm)] with y hy _ using hy.le
  have hΔev : ∀ᶠ y in 𝓝 x₀, Δ φ y < 0 :=
    hΔc.continuousAt.eventually_lt continuousAt_const hfail.1
  obtain ⟨ε, hε, hP⟩ := Metric.eventually_nhds_iff_ball.1
    (hθev.and (hΔev.and (htev.and (ball_mem_nhds x₀ hρ))))
  have hεU : ball x₀ ε ⊆ U := fun y hy ↦ hBU' (hρB (hP y hy).2.2.2)
  set r₀ := ε / 2 with hr₀
  set r₁ := ε / 4 with hr₁
  have hr₁0 : 0 < r₁ := by positivity
  have hr₁₀ : r₁ < r₀ := by rw [hr₀, hr₁]; linarith
  have hr₀ε : r₀ < ε := by rw [hr₀]; linarith
  have hcb : closedBall x₀ r₀ ⊆ ball x₀ ε := closedBall_subset_ball hr₀ε
  have hcb₁ : closedBall x₀ r₁ ⊆ ball x₀ ε := closedBall_subset_ball (hr₁₀.trans hr₀ε)
  -- the gap on the annulus, relative to `closure P`
  have hSc : IsCompact ((closedBall x₀ r₀ \ ball x₀ r₁) ∩ closure P) :=
    ((isCompact_closedBall x₀ r₀).diff isOpen_ball).inter_right isClosed_closure
  have hSU : (closedBall x₀ r₀ \ ball x₀ r₁) ∩ closure P ⊆ U := fun y hy ↦ hεU (hcb hy.1.1)
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_of_isCompact hSc (f := fun y ↦ max (φ y) 0 - w y)
    ((continuousOn_max_zero hφ.continuous.continuousOn).sub (hw.mono hSU)) fun y hy ↦ by
      have hne : y ≠ x₀ := by
        rintro rfl; exact hy.1.2 (mem_ball_self hr₁0)
      exact sub_pos.2 ((hP y (hcb hy.1.1)).2.2.1 ⟨⟨hy.2, hSU hy⟩, hne⟩)
  set δ := min (min δ₀ η) θ / 2 with hδdef
  have hmin : 0 < min (min δ₀ η) θ := lt_min (lt_min hδ₀ hη) hθ
  have hδ : 0 < δ := by positivity
  have hδδ₀ : δ < δ₀ := by
    rw [hδdef]; linarith [min_le_left (min δ₀ η) θ, min_le_left δ₀ η]
  have hδη : δ < η := by
    rw [hδdef]; linarith [min_le_left (min δ₀ η) θ, min_le_right δ₀ η]
  have hδθ : δ < θ := by
    rw [hδdef]; linarith [min_le_right (min δ₀ η) θ]
  -- the cut-off and the perturbation
  obtain ⟨χ, hχ, -, hχs, hχ01, hχ1⟩ :=
    exists_smooth_cutoff (isCompact_closedBall x₀ r₁) isOpen_ball (closedBall_subset_ball hr₁₀)
  set m : E d → ℝ := fun y ↦ max (φ y - δ) 0 with hmdef
  set w' : E d → ℝ := fun y ↦ w y - χ y * max (w y - m y) 0 with hw'def
  have hφH : MemH1Loc U φ (∇ φ) := memH1Loc_gradient_of_contDiff hU hφ1
  obtain ⟨Gm, hmH⟩ : ∃ G, MemH1Loc U m G := ⟨_, hφH.posPart_sub hU δ⟩
  obtain ⟨Gw', hw'H⟩ : ∃ G, MemH1Loc U w' G :=
    ⟨_, hwH.sub ((memH1Loc_posPart hU (hwH.sub hmH)).mul_smooth hU hχ)⟩
  have hdiff : ∀ y, w' y - w y = -(χ y * max (w y - m y) 0) := fun y ↦ by
    simp only [hw'def]; ring
  have hm0 : ∀ y, 0 ≤ m y := fun y ↦ le_max_right _ _
  -- where `w'` differs from `w`
  have hkey : ∀ y, w' y ≠ w y → y ∈ ball x₀ r₁ ∧ w' y = m y ∧ m y < w y := by
    intro y hy
    have hne : χ y * max (w y - m y) 0 ≠ 0 := by
      intro h; apply hy; rw [← sub_eq_zero, hdiff, h, neg_zero]
    have hχne : χ y ≠ 0 := left_ne_zero_of_mul hne
    have hmx : max (w y - m y) 0 ≠ 0 := right_ne_zero_of_mul hne
    have hlt : m y < w y := by
      by_contra h
      exact hmx (max_eq_right (by linarith))
    have hyr₀ : y ∈ closedBall x₀ r₀ :=
      ball_subset_closedBall (hχs (subset_tsupport _ hχne))
    have hyr₁ : y ∈ ball x₀ r₁ := by
      by_contra h
      have hyP : y ∈ P := ⟨hεU (hcb hyr₀), (hm0 y).trans_lt hlt⟩
      have h1 := hδ₀le y ⟨⟨hyr₀, h⟩, subset_closure hyP⟩
      have h2 := max_sub_le_max_sub (a := φ y) hδ.le
      simp only [hmdef] at hlt
      linarith
    refine ⟨hyr₁, ?_, hlt⟩
    have h1 := hχ1 y (ball_subset_closedBall hyr₁)
    simp only [hw'def, h1, one_mul, max_eq_left (by linarith : 0 ≤ w y - m y)]
    ring
  have hr₁ρ : ∀ y ∈ ball x₀ r₁, y ∈ ball x₀ ρ := fun y hy ↦
    (hP y (hcb₁ (ball_subset_closedBall hy))).2.2.2
  have hKB : closedBall x₀ r₁ ⊆ B := fun y hy ↦ hρB (hP y (hcb₁ hy)).2.2.2
  have hKU : closedBall x₀ r₁ ⊆ U := hKB.trans hBU'
  refine ⟨w', Gw', hw'H, fun y hy ↦ ?_, fun y hy ↦ ⟨?_, ?_⟩, ?_⟩
  · by_contra h
    exact hy.2 (hr₁ρ y (hkey y h).1)
  · by_cases h : w' y = w y
    · rw [h]; exact min_le_left _ _
    · rw [(hkey y h).2.1]
      exact (min_le_right _ _).trans (max_le_max (by linarith) le_rfl)
  · have := mul_nonneg (hχ01 y).1 (le_max_right (w y - m y) 0)
    linarith [hdiff y]
  -- the energy comparison
  obtain ⟨C, hC⟩ := hBU.1.exists_bound_of_continuousOn (hQ.mono hBU.2)
  refine energyJ_lt_of_le_add_inner hU hB.measurableSet hBU.1 hBU.2 (isCompact_closedBall x₀ r₁)
    hKB hQ (C := C) (fun x hx ↦ by simpa [Real.norm_eq_abs] using hC x (subset_closure hx))
    hwH hw'H hφ (fun x hx ↦ ?_) ?_ ?_
  · by_contra h
    exact hx.2 (ball_subset_closedBall (hkey x h).1)
  · -- the pointwise inequality
    have ha := (hw'H.1.sub hwH.1).ae_eq_zero_of_eq_zero hU
    have hb := (hw'H.1.sub hφH.1).ae_eq_zero_of_eq_const hU (-δ)
    have hc := hw'H.1.ae_eq_zero_of_eq_zero hU
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU ha,
      ae_restrict_of_ae_restrict_of_subset hKU hb, ae_restrict_of_ae_restrict_of_subset hKU hc,
      ae_restrict_mem measurableSet_closedBall] with x ha hb hc hxK
    by_cases h : w' x = w x
    · have hG : Gw' x = Gw x := sub_eq_zero.1 (ha (by rw [h, sub_self]))
      rw [h, hG, sub_self, inner_zero_left, mul_zero, add_zero]
    · obtain ⟨hxb, hw'x, hlt⟩ := hkey x h
      have hwpos : 0 < w x := (hm0 x).trans_lt hlt
      rw [indicator_of_mem (show w x ∈ Ioi (0 : ℝ) from hwpos), Pi.one_apply, mul_one]
      have haux := inner_le_aux (Gw x) (∇ φ x)
      by_cases hφδ : δ < φ x
      · have hmx : m x = φ x - δ := max_eq_left (by linarith)
        have hG : Gw' x = ∇ φ x := sub_eq_zero.1 (hb (by rw [hw'x, hmx]; ring))
        have hw'pos : 0 < w' x := by rw [hw'x, hmx]; linarith
        rw [hG, indicator_of_mem (show w' x ∈ Ioi (0 : ℝ) from hw'pos), Pi.one_apply, mul_one,
          inner_sub_left, real_inner_self_eq_norm_sq]
        linarith
      · have hmx : m x = 0 := max_eq_right (by linarith)
        have hw'0 : w' x = 0 := by rw [hw'x, hmx]
        have hG : Gw' x = 0 := hc hw'0
        have hQle := (hP x (hcb₁ hxK)).1 (by linarith)
        rw [hG, hw'0, indicator_of_notMem (show (0 : ℝ) ∉ Ioi (0 : ℝ) by simp),
          zero_sub, inner_neg_left]
        simp only [norm_zero]
        have hsq : ‖∇ φ x‖ ^ 2 ≤ Q x ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hQle 2
        linarith
  · -- positivity of `∫ (w' - w) Δφ`
    obtain ⟨y₀, ⟨hy₁, hy₂, hy₃⟩, hy₀P⟩ := mem_closure_iff_nhds.1 hx₀P _
      ((show ∀ᶠ y in 𝓝 x₀, y ∈ ball x₀ r₁ from ball_mem_nhds x₀ hr₁0).and
        ((continuousAt_const.eventually_lt hwc (show w x₀ - δ / 2 < w x₀ by linarith)).and
          (hφ.continuous.continuousAt.eventually_lt continuousAt_const
            (show φ x₀ < φ x₀ + δ / 2 by linarith))))
    have hmy₀ : m y₀ < w y₀ := max_lt (by linarith [hy₂, hy₃]) hy₀P.2
    refine integral_pos_of_continuousOn hU (isCompact_closedBall x₀ r₁) hKU (y := y₀) ?_ ?_ ?_
      hy₀P.1 ?_
    · have h1 : ContinuousOn m U :=
        continuousOn_max_zero (hφ.continuous.sub continuous_const).continuousOn
      have hc : ContinuousOn (fun x ↦ -(χ x * max (w x - m x) 0) * Δ φ x) U :=
        ((hχ.continuous.continuousOn.mul (continuousOn_max_zero (hw.sub h1))).neg).mul
          hΔc.continuousOn
      exact hc.congr fun x _ ↦ by rw [hdiff]
    · intro x hx
      by_cases h : w' x = w x
      · rw [h, sub_self, zero_mul]
      · obtain ⟨hxb, hw'x, hlt⟩ := hkey x h
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith)
          (hP x (hcb₁ (ball_subset_closedBall hxb))).2.1.le
    · intro x hx
      have : w' x = w x := by
        by_contra h; exact hx.2 (ball_subset_closedBall (hkey x h).1)
      rw [this, sub_self, zero_mul]
    · rw [hdiff, hχ1 y₀ (ball_subset_closedBall hy₁), one_mul, max_eq_left (by linarith)]
      exact mul_pos_of_neg_of_neg (by linarith)
        (hP y₀ (hcb₁ (ball_subset_closedBall hy₁))).2.1

/-- The supersolution perturbation (`EnergyDecreaseSuperStatement`), from
`energy_decrease_of_not_super_of_continuousOn`. -/
theorem energy_decrease_of_not_super : EnergyDecreaseSuperStatement := by
  intro d U Q w Gw hU ⟨_, hK⟩ ⟨c, hc, hcQ⟩ _ hw hw0 hwH B hB hBU φ hφ x₀ hx₀ htouch hfail ρ hρ
    hρB η hη
  exact energy_decrease_of_not_super_of_continuousOn hU hK.continuousOn
    (fun x hx ↦ hc.le.trans (hcQ x hx)) hw hw0 hwH hB hBU hφ hx₀ htouch hfail hρ hρB hη

/-- The subsolution perturbation (`EnergyDecreaseSubStatement`), from
`energy_decrease_of_not_sub_of_continuousOn`. -/
theorem energy_decrease_of_not_sub : EnergyDecreaseSubStatement := by
  intro d U Q w Gw hU ⟨_, hK⟩ _ _ hw _ hwH B hB hBU φ hφ x₀ hx₀ hx₀P htouch hfail ρ hρ hρB η
    hη
  exact energy_decrease_of_not_sub_of_continuousOn hU hK.continuousOn hw hwH hB hBU hφ hx₀
    hx₀P htouch hfail hρ hρB hη

end EllipticBernoulli
