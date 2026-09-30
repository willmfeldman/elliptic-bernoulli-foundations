/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Harmonic.MeanValue

/-!
# The strong maximum principle for harmonic functions

Let `E` be a finite-dimensional real inner product space.

* `HarmonicOnNhd.eqOn_ball_of_isMaxOn`: the local step. If `h` is harmonic near
  `closedBall x r` and attains its maximum over `ball x r` at the centre, it is constant on
  `ball x r` (ball mean-value property).
* `HarmonicOnNhd.eqOn_of_isMaxOn`, `HarmonicOnNhd.eqOn_of_isMinOn`: the strong maximum
  (minimum) principle on a preconnected open set (Gilbarg–Trudinger Thm 2.2).
* `HarmonicOnNhd.eq_zero_of_nonneg_of_eq_zero`, `HarmonicOnNhd.pos_of_nonneg`: a nonnegative
  harmonic function on a preconnected open set vanishing at one point vanishes identically;
  otherwise it is strictly positive.

Used for smallest supersolutions (strict positivity) and the flat Harnack inequality.

## Proof

Local step: `∫_{B} (h x - h) = |B| h x - ∫_B h = 0` by the mean-value property, and the integrand
is continuous and nonnegative on the open ball, so it vanishes there. Global step: the sets
`{y ∈ Ω | h y = h x₀}` and `{y ∈ Ω | h y < h x₀}` are open (local step, continuity), disjoint and
cover `Ω`; preconnectedness forces the first to be all of `Ω`.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology

public section

namespace EllipticBernoulli

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local strong maximum principle.** If `h` is harmonic on a neighbourhood of
`closedBall x r` and `h ≤ h x` on `ball x r`, then `h = h x` on `ball x r`. -/
theorem HarmonicOnNhd.eqOn_ball_of_isMaxOn {h : E → ℝ} {x : E} {r : ℝ} (_hr : 0 < r)
    (hh : HarmonicOnNhd h (closedBall x r)) (hmax : ∀ y ∈ ball x r, h y ≤ h x) :
    ∀ y ∈ ball x r, h y = h x := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have hcont : ContinuousOn h (closedBall x r) := hh.contDiffOn.continuousOn
  have hint : IntegrableOn h (ball x r) μ :=
    (hcont.integrableOn_compact (isCompact_closedBall x r)).mono_set ball_subset_closedBall
  have hfin : μ (ball x r) ≠ ⊤ := measure_ball_lt_top.ne
  have hintc : IntegrableOn (fun _ ↦ h x) (ball x r) μ := integrableOn_const hfin
  have hzero : ∫ y in ball x r, (h x - h y) ∂μ = 0 := by
    rw [integral_sub hintc hint, HarmonicOnNhd.setIntegral_ball_eq hh, setIntegral_const,
      smul_eq_mul, sub_self]
  have hnn : 0 ≤ᵐ[μ.restrict (ball x r)] fun y ↦ h x - h y :=
    (ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ fun y hy ↦ sub_nonneg.2 (hmax y hy))
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae hnn (hintc.sub hint)).1 hzero
  have heq := Measure.eqOn_open_of_ae_eq (μ := μ) hae isOpen_ball
    (continuousOn_const.sub (hcont.mono ball_subset_closedBall)) continuousOn_const
  intro y hy
  have := heq hy
  simp only [Pi.zero_apply] at this
  linarith

/-- **Strong maximum principle** (Gilbarg–Trudinger Thm 2.2). A harmonic function on a
preconnected open set `Ω` attaining its maximum over `Ω` at a point of `Ω` is constant on `Ω`. -/
theorem HarmonicOnNhd.eqOn_of_isMaxOn {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {h : E → ℝ} (hh : HarmonicOnNhd h Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) (hmax : IsMaxOn h Ω x₀) :
    EqOn h (fun _ ↦ h x₀) Ω := by
  have hcont : ContinuousOn h Ω := hh.contDiffOn.continuousOn
  set u : Set E := {y ∈ Ω | h y = h x₀}
  set v : Set E := {y ∈ Ω | h y < h x₀}
  have hu : IsOpen u := by
    refine isOpen_iff_mem_nhds.2 fun y ⟨hyΩ, hyeq⟩ ↦ ?_
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ y hyΩ
    have hB : closedBall y (r / 2) ⊆ Ω := (closedBall_subset_ball (by linarith)).trans hrΩ
    have hloc := HarmonicOnNhd.eqOn_ball_of_isMaxOn (by positivity : (0 : ℝ) < r / 2)
      (hh.mono hB) fun z hz ↦ by
        rw [hyeq]; exact hmax (hB (ball_subset_closedBall hz))
    filter_upwards [ball_mem_nhds y (by positivity : (0 : ℝ) < r / 2)] with z hz
    exact ⟨hB (ball_subset_closedBall hz), (hloc z hz).trans hyeq⟩
  have hv : IsOpen v := hcont.isOpen_inter_preimage hΩ isOpen_Iio
  have huv : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro y ⟨_, hy1⟩ ⟨_, hy2⟩
    exact (lt_irrefl _ (hy1 ▸ hy2))
  have hcover : Ω ⊆ u ∪ v := fun y hy ↦
    (hmax hy).eq_or_lt.elim (fun h1 ↦ Or.inl ⟨hy, h1⟩) fun h2 ↦ Or.inr ⟨hy, h2⟩
  have hsub := hΩc.subset_left_of_subset_union hu hv huv hcover ⟨x₀, hx₀, hx₀, rfl⟩
  exact fun y hy ↦ (hsub hy).2

/-- **Strong minimum principle.** A harmonic function on a preconnected open set `Ω` attaining its
minimum over `Ω` at a point of `Ω` is constant on `Ω`. -/
theorem HarmonicOnNhd.eqOn_of_isMinOn {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {h : E → ℝ} (hh : HarmonicOnNhd h Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) (hmin : IsMinOn h Ω x₀) :
    EqOn h (fun _ ↦ h x₀) Ω := by
  have hmax : IsMaxOn (-h) Ω x₀ := fun y hy ↦ by
    simp only [mem_ofPred_eq, Pi.neg_apply, neg_le_neg_iff]; exact hmin hy
  have := HarmonicOnNhd.eqOn_of_isMaxOn hΩ hΩc hh.neg hx₀ hmax
  intro y hy
  have h1 := this hy
  simp only [Pi.neg_apply, neg_inj] at h1
  exact h1

/-- A nonnegative harmonic function on a preconnected open set which vanishes at one point
vanishes identically. -/
theorem HarmonicOnNhd.eq_zero_of_nonneg_of_eq_zero {Ω : Set E} (hΩ : IsOpen Ω)
    (hΩc : IsPreconnected Ω) {h : E → ℝ} (hh : HarmonicOnNhd h Ω) (h0 : ∀ y ∈ Ω, 0 ≤ h y)
    {x₀ : E} (hx₀ : x₀ ∈ Ω) (hz : h x₀ = 0) : ∀ y ∈ Ω, h y = 0 := by
  have hmin : IsMinOn h Ω x₀ := fun y hy ↦ by
    simp only [mem_ofPred_eq, hz]; exact h0 y hy
  intro y hy
  rw [HarmonicOnNhd.eqOn_of_isMinOn hΩ hΩc hh hx₀ hmin hy, hz]

/-- **Strict positivity.** A nonnegative harmonic function on a preconnected open set which does
not vanish at some point is strictly positive everywhere on the set. -/
theorem HarmonicOnNhd.pos_of_nonneg {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {h : E → ℝ} (hh : HarmonicOnNhd h Ω) (h0 : ∀ y ∈ Ω, 0 ≤ h y) {x₁ : E} (hx₁ : x₁ ∈ Ω)
    (hne : h x₁ ≠ 0) : ∀ y ∈ Ω, 0 < h y := by
  intro y hy
  refine (h0 y hy).lt_of_ne fun hy0 ↦ hne ?_
  exact HarmonicOnNhd.eq_zero_of_nonneg_of_eq_zero hΩ hΩc hh h0 hy hy0.symm x₁ hx₁

end EllipticBernoulli
