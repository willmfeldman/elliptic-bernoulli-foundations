/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Flatness
public import EllipticBernoulli.Flatness.OneStep
import EllipticBernoulli.Harmonic.Harnack
import EllipticBernoulli.Viscosity.Affine
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic

/-!
# De Silva's Harnack inequality for flat solutions

De Silva (2011), §3 (Theorem 3.1, Corollary 3.2), with `f = 0`, `a_{ij} = δ_{ij}`, `g = Q`.

* `flat_harnack_unit`: Theorem 3.1 on `B_1` (the normalized case, from the one-step lemmas).
* `flat_harnack_of_le`: Theorem 3.1 at every center and scale, in the form of
  `FlatHarnackStatement` (by the rescaling `IsViscSolution.rescale`).
* `flat_harnack_iterate`: Corollary 3.2 in discrete form, the trapping at every level `r / 20^m`
  with `ε 20^m ≤ ε̄`.
* `flat_harnack_oscillation`: Corollary 3.2 in Hölder form,
  `|ũ(y) - ũ(x₀)| ≤ C ε r (|y - x₀|/r)^γ` for `ũ = u - ⟪·, e⟫` on `closure {u > 0}`, down to
  scale `ε r / ε̄` (the compactness input of `linearized_limit`);
  `trap_of_mem_closure_posSet`: the trapping without positive parts on `closure {u > 0}`.
* `flat_harnack`: the headline `FlatHarnackStatement`, which is `flat_harnack_of_le`.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The zero function is a viscosity solution for every coefficient. -/
private theorem isViscSolution_zero {U : Set (E d)} (hU : IsOpen U) (Q : E d → ℝ) :
    IsViscSolution U Q (fun _ ↦ 0) := by
  refine ⟨isViscSuper_const hU le_rfl, continuousOn_const, fun _ _ ↦ le_rfl, ?_⟩
  intro φ _ x hx
  have : posSet (fun _ : E d ↦ (0 : ℝ)) U = ∅ := by ext; simp [posSet]
  rw [this, closure_empty, empty_inter] at hx
  exact absurd hx.1 (notMem_empty x)

/-- `max (s + min A B) 0 ≥ u` from the two bounds. -/
private theorem le_max_add_min {w s A B : ℝ} (hA : w ≤ max (s + A) 0) (hB : w ≤ max (s + B) 0) :
    w ≤ max (s + min A B) 0 := by
  rcases le_total A B with h | h
  · rwa [min_eq_left h]
  · rwa [min_eq_right h]

/-- **De Silva (2011), Theorem 3.1 on `B_1`** (`x₀ = 0`, `r = 1`): the flat trapping improves
from `B_1` to `B_{1/20}`. Cases: `a₀ ≤ -1/10` (then `u ≡ 0` on `B_{1/20}`), `a₀ ≥ 1/10`
(classical Harnack, `B_{1/10} ⊆ {u > 0}`), `|a₀| < 1/10` (`flat_lower_step`/`flat_upper_step`
with the dichotomy at `e/5`). De Silva's case split omits `|a₀| = 1/10`, and leaves implicit the
choice of `a₁, b₁` with `a₀ ≤ a₁ ≤ b₁ ≤ b₀`; both are handled here. -/
theorem flat_harnack_unit (hd : 2 ≤ d) : ∃ εbar > 0, ∃ c ∈ Ioo (0 : ℝ) 1,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (ε a₀ b₀ : ℝ), IsOpen U →
    ball (0 : E d) 1 ⊆ U → IsViscSolution U Q u → ‖e‖ = 1 → 0 < ε → ε ≤ εbar →
    (∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2) → a₀ ≤ b₀ → b₀ - a₀ ≤ ε →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ + a₀) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + b₀) 0) →
    ∃ a₁ b₁ : ℝ, a₀ ≤ a₁ ∧ a₁ ≤ b₁ ∧ b₁ ≤ b₀ ∧ b₁ - a₁ ≤ (1 - c) * ε ∧
      ∀ y ∈ ball (0 : E d) (1 / 20),
        max (⟪y, e⟫ + a₁) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + b₁) 0 := by
  obtain ⟨ε₁, hε₁, c₁, hc₁, hlowstep⟩ := flat_lower_step hd
  obtain ⟨ε₂, hε₂, c₂, hc₂, hupstep⟩ := flat_upper_step hd
  set CH : ℝ := ((3 : ℝ) ^ d) ^ 8 with hCH
  have hCH1 : 1 ≤ CH := one_le_harnackConst
  have hCH0 : 0 < CH := by linarith
  set cH : ℝ := 1 / (2 * CH) with hcH
  have hcH0 : 0 < cH := by positivity
  have hcH1 : cH ≤ 1 / 2 := by
    rw [hcH, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set c : ℝ := min (min c₁ c₂) cH with hc
  have hc0 : 0 < c := lt_min (lt_min hc₁.1 hc₂.1) hcH0
  have hc1 : c ≤ 1 / 2 := (min_le_right _ _).trans hcH1
  have hcc₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hcc₂ : c ≤ c₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hccH : c ≤ cH := min_le_right _ _
  refine ⟨min (min ε₁ ε₂) (1 / 20), lt_min (lt_min hε₁ hε₂) (by norm_num), c,
    ⟨hc0, by linarith⟩, ?_⟩
  intro U Q u e ε a₀ b₀ hU hB hu he hε hεbar hQ hab hba htrap
  have hεε₁ : ε ≤ ε₁ := hεbar.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεε₂ : ε ≤ ε₂ := hεbar.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε20 : ε ≤ 1 / 20 := hεbar.trans (min_le_right _ _)
  have hinner : ∀ y : E d, |⟪y, e⟫| ≤ ‖y‖ := fun y ↦ by
    simpa [he] using abs_real_inner_le_norm y e
  have hu0 : ∀ y ∈ ball (0 : E d) 1, 0 ≤ u y := fun y hy ↦ hu.1.2.1 y (hB hy)
  have h20 : ball (0 : E d) (1 / 20) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have hcHδ : ∀ δ : ℝ, δ / 2 / CH = cH * δ := fun δ ↦ by rw [hcH]; field_simp
  clear_value cH
  clear hcH
  rcases le_or_gt a₀ (-(1 / 10)) with ha | ha
  · -- `a₀ ≤ -1/10`: `u ≡ 0` on `B_{1/20}`.
    refine ⟨a₀, a₀, le_rfl, le_rfl, hab, by rw [sub_self]; exact mul_nonneg (by linarith) hε.le,
      fun y hy ↦ ?_⟩
    have hy1 : ‖y‖ < 1 / 20 := mem_ball_zero_iff.1 hy
    have hy' := (abs_le.1 (hinner y)).2
    have h1 : max (⟪y, e⟫ + a₀) 0 = 0 := max_eq_right (by linarith)
    have h2 : max (⟪y, e⟫ + b₀) 0 = 0 := max_eq_right (by linarith)
    have := (htrap y (h20 hy)).2
    rw [h2] at this
    rw [h1]
    exact ⟨hu0 y (h20 hy), this⟩
  rcases le_or_gt (1 / 10) a₀ with ha' | ha'
  · -- `a₀ ≥ 1/10`: classical Harnack in `B_{1/10} ⊆ {u > 0}`.
    set δ := b₀ - a₀ with hδ
    have hδ0 : 0 ≤ δ := by linarith
    have h10 : ball (0 : E d) (1 / 10) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
    have hpos : ball (0 : E d) (1 / 10) ⊆ posSet u U := fun y hy ↦ by
      refine ⟨hB (h10 hy), ?_⟩
      have hy1 : ‖y‖ < 1 / 10 := mem_ball_zero_iff.1 hy
      have hy' := (abs_le.1 (hinner y)).1
      have := (le_max_left _ _).trans (htrap y (h10 hy)).1
      linarith
    have hup : ∀ y ∈ ball (0 : E d) (1 / 10), u y ≤ ⟪y, e⟫ + b₀ := fun y hy ↦ by
      have h := (htrap y (h10 hy)).2
      rcases le_total (⟪y, e⟫ + b₀) 0 with h' | h'
      · rw [max_eq_right h'] at h; linarith [(hpos hy).2]
      · rwa [max_eq_left h'] at h
    have hlo : ∀ y ∈ ball (0 : E d) (1 / 10), ⟪y, e⟫ + a₀ ≤ u y := fun y hy ↦
      (le_max_left _ _).trans (htrap y (h10 hy)).1
    have huH := IsViscSolution.harmonicOnNhd_posSet hU hu
    have hHl : HarmonicOnNhd (fun y ↦ u y - (⟪y, e⟫ + a₀)) (ball 0 (1 / 10)) :=
      fun y hy ↦ (huH y (hpos hy)).sub (harmonicAt_inner_add e a₀ y)
    have hHu : HarmonicOnNhd (fun y ↦ (⟪y, e⟫ + b₀) - u y) (ball 0 (1 / 10)) :=
      fun y hy ↦ (harmonicAt_inner_add e b₀ y).sub (huH y (hpos hy))
    have h0 : (0 : E d) ∈ ball (0 : E d) (1 / 10) := mem_ball_self (by norm_num)
    rcases le_total (δ / 2) (u 0 - (⟪(0 : E d), e⟫ + a₀)) with hx | hx
    · have hH := harnack_ball_tenth hHl (fun y hy ↦ by linarith [hlo y hy]) hx
      refine ⟨a₀ + δ / 2 / CH, b₀, le_add_of_nonneg_right (by positivity), ?_, le_rfl, ?_,
        fun y hy ↦ ⟨?_, ?_⟩⟩
      · have : δ / 2 / CH ≤ δ := by
          rw [div_div, div_le_iff₀ (by positivity)]
          linarith [mul_le_mul_of_nonneg_left (show 1 ≤ 2 * CH by linarith) hδ0]
        linarith
      · rw [hcHδ δ]
        have : c * ε ≤ cH * ε := mul_le_mul_of_nonneg_right hccH hε.le
        linarith [mul_le_mul_of_nonneg_left hba (show 0 ≤ 1 - cH by linarith)]
      · refine max_le ?_ (hu0 y (h20 hy))
        have := hH y hy
        linarith
      · exact (htrap y (h20 hy)).2
    · have hx' : δ / 2 ≤ (⟪(0 : E d), e⟫ + b₀) - u 0 := by
        simp only [inner_zero_left] at hx ⊢; linarith
      have hH := harnack_ball_tenth hHu (fun y hy ↦ by linarith [hup y hy]) hx'
      refine ⟨a₀, b₀ - δ / 2 / CH, le_rfl, ?_, by linarith [show 0 ≤ δ / 2 / CH by positivity],
        ?_, fun y hy ↦ ⟨(htrap y (h20 hy)).1, ?_⟩⟩
      · have : δ / 2 / CH ≤ δ := by
          rw [div_div, div_le_iff₀ (by positivity)]
          linarith [mul_le_mul_of_nonneg_left (show 1 ≤ 2 * CH by linarith) hδ0]
        linarith
      · rw [hcHδ δ]
        have : c * ε ≤ cH * ε := mul_le_mul_of_nonneg_right hccH hε.le
        linarith [mul_le_mul_of_nonneg_left hba (show 0 ≤ 1 - cH by linarith)]
      · refine le_max_of_le_left ?_
        have := hH y hy
        linarith
  -- `|a₀| < 1/10`: De Silva's Lemma 3.3 with `σ = a₀`.
  have hσ : |a₀| < 1 / 10 := abs_lt.2 ⟨ha, ha'⟩
  have hQ1 : ∀ y ∈ ball (0 : E d) 1, Q y ≤ 1 + ε ^ 2 := fun y hy ↦ by
    linarith [(abs_le.1 (hQ y hy)).2]
  have hQ2 : ∀ y ∈ ball (0 : E d) 1, 1 - ε ^ 2 ≤ Q y := fun y hy ↦ by
    linarith [(abs_le.1 (hQ y hy)).1]
  have h12 : ball (0 : E d) (1 / 20) ⊆ closedBall 0 (1 / 2) :=
    (ball_subset_ball (by norm_num)).trans ball_subset_closedBall
  rcases le_or_gt (1 / 5 + a₀ + ε / 2) (u ((1 / 5 : ℝ) • e)) with hx | hx
  · have hL := hlowstep U Q u e a₀ ε hU hB hu he hε hεε₁ hQ1 hσ (fun y hy ↦ (htrap y hy).1) hx
    refine ⟨min (a₀ + c * ε) b₀, b₀, le_min (le_add_of_nonneg_right (mul_nonneg hc0.le hε.le)) hab,
      min_le_right _ _, le_rfl, ?_,
      fun y hy ↦ ⟨?_, (htrap y (h20 hy)).2⟩⟩
    · rcases le_total (a₀ + c * ε) b₀ with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h, sub_self]; exact mul_nonneg (by linarith) hε.le
    · refine le_trans ?_ (hL y (h12 hy))
      have : min (a₀ + c * ε) b₀ ≤ a₀ + c₁ * ε :=
        (min_le_left _ _).trans ((add_le_add_iff_left a₀).2 (mul_le_mul_of_nonneg_right hcc₁ hε.le))
      exact max_le_max (by linarith) le_rfl
  · have hU' := hupstep U Q u e a₀ ε hU hB hu he hε hεε₂ hQ2 hσ
      (fun y hy ↦ ⟨(htrap y hy).1, (htrap y hy).2.trans (max_le_max (by linarith) le_rfl)⟩)
      hx.le
    refine ⟨a₀, min b₀ (a₀ + (1 - c) * ε), le_rfl,
      le_min hab (le_add_of_nonneg_right (mul_nonneg (by linarith) hε.le)),
      min_le_left _ _, by linarith [min_le_right b₀ (a₀ + (1 - c) * ε)],
      fun y hy ↦ ⟨(htrap y (h20 hy)).1, le_max_add_min (htrap y (h20 hy)).2 ?_⟩⟩
    refine (hU' y (h12 hy)).trans (max_le_max ?_ le_rfl)
    have : (1 - c₂) * ε ≤ (1 - c) * ε := mul_le_mul_of_nonneg_right (by linarith) hε.le
    linarith

/-! ### Theorem 3.1 at every center and scale -/

/-- `max (⟪x̄ + r y, e⟫ + a) 0 = r · max (⟪y, e⟫ + (⟪x̄, e⟫ + a)/r) 0` for `r > 0`. -/
private theorem max_inner_rescale {r : ℝ} (hr : 0 < r) (xbar y e : E d) (a : ℝ) :
    max (⟪xbar + r • y, e⟫ + a) 0 = r * max (⟪y, e⟫ + (⟪xbar, e⟫ + a) / r) 0 := by
  rw [mul_max_of_nonneg _ _ hr.le, mul_zero, inner_add_left, real_inner_smul_left]
  congr 1
  field_simp
  ring

/-- **De Silva (2011), Theorem 3.1** (Harnack inequality for flat solutions), in the form of
`FlatHarnackStatement`. The hypothesis `a₀ ≤ b₀` is needed (`u ≡ 0`, `a₀ = -2`, `b₀ = -3` is a
counterexample without it); De Silva's assumption `x̄ ∈ Ω⁺(u) ∪ F(u)` forces it. Reduced to
`flat_harnack_unit` by `u ↦ u(x̄ + r ·)/r` (`IsViscSolution.rescale`); the smallness
`|Q - 1| ≤ ε²` is scale-invariant. -/
theorem flat_harnack_of_le (hd : 2 ≤ d) : ∃ εbar > 0, ∃ c ∈ Ioo (0 : ℝ) 1,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e xbar : E d) (r ε a₀ b₀ : ℝ), IsOpen U →
    IsViscSolution U Q u → ‖e‖ = 1 → 0 < r → ball xbar r ⊆ U → 0 < ε → ε ≤ εbar →
    (∀ y ∈ ball xbar r, |Q y - 1| ≤ ε ^ 2) → a₀ ≤ b₀ → b₀ - a₀ ≤ ε * r →
    (∀ y ∈ ball xbar r, max (inner ℝ y e + a₀) 0 ≤ u y ∧ u y ≤ max (inner ℝ y e + b₀) 0) →
    ∃ a₁ b₁ : ℝ, a₀ ≤ a₁ ∧ a₁ ≤ b₁ ∧ b₁ ≤ b₀ ∧ b₁ - a₁ ≤ (1 - c) * ε * r ∧
      ∀ y ∈ ball xbar (r / 20),
        max (inner ℝ y e + a₁) 0 ≤ u y ∧ u y ≤ max (inner ℝ y e + b₁) 0 := by
  obtain ⟨εbar, hεbar, c, hc, H⟩ := flat_harnack_unit hd
  refine ⟨εbar, hεbar, c, hc, ?_⟩
  intro U Q u e xbar r ε a₀ b₀ hU hu he hr hB hε hεb hQ hab hba htrap
  set A : E d → E d := fun y ↦ xbar + r • y with hA
  have hAc : Continuous A := by fun_prop
  have hball : ∀ y ∈ ball (0 : E d) 1, A y ∈ ball xbar r := fun y hy ↦ by
    rw [mem_ball, dist_zero_right] at hy
    rw [mem_ball, dist_eq_norm, hA]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_of_lt_one_right hr hy
  have hu' := hu.rescale xbar hr one_pos
  simp only [div_one, mul_one] at hu'
  set a₀' := (⟪xbar, e⟫ + a₀) / r
  set b₀' := (⟪xbar, e⟫ + b₀) / r
  obtain ⟨a₁', b₁', h1, h2, h3, h4, h5⟩ := H (A ⁻¹' U) (fun y ↦ Q (A y)) (fun y ↦ u (A y) / r) e
    ε a₀' b₀' (hU.preimage hAc) (fun y hy ↦ hB (hball y hy)) hu' he hε hεb
    (fun y hy ↦ hQ _ (hball y hy)) (div_le_div_of_nonneg_right (by linarith) hr.le)
    (by rw [div_sub_div_same, div_le_iff₀ hr]; linarith)
    (fun y hy ↦ by
      obtain ⟨hl, hu⟩ := htrap _ (hball y hy)
      rw [hA, max_inner_rescale hr] at hl hu
      exact ⟨by rw [le_div_iff₀ hr, mul_comm]; exact hl,
        by rw [div_le_iff₀ hr, mul_comm]; exact hu⟩)
  refine ⟨r * a₁' - ⟪xbar, e⟫, r * b₁' - ⟪xbar, e⟫, ?_, ?_, ?_, ?_, fun y hy ↦ ?_⟩
  · have := (div_le_iff₀ hr).1 h1; linarith
  · linarith [mul_le_mul_of_nonneg_left h2 hr.le]
  · have := (le_div_iff₀ hr).1 h3; linarith
  · have := mul_le_mul_of_nonneg_left h4 hr.le; linarith
  · set y' : E d := r⁻¹ • (y - xbar)
    have hAy : A y' = y := by
      simp only [hA, y', smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
    have hy' : y' ∈ ball (0 : E d) (1 / 20) := by
      rw [mem_ball, dist_eq_norm] at hy
      rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
        inv_mul_lt_iff₀ hr]
      linarith
    obtain ⟨hl, hu⟩ := h5 y' hy'
    have e1 : (⟪xbar, e⟫ + (r * a₁' - ⟪xbar, e⟫)) / r = a₁' := by field_simp; ring
    have e2 : (⟪xbar, e⟫ + (r * b₁' - ⟪xbar, e⟫)) / r = b₁' := by field_simp; ring
    have k1 := max_inner_rescale hr xbar y' e (r * a₁' - ⟪xbar, e⟫)
    have k2 := max_inner_rescale hr xbar y' e (r * b₁' - ⟪xbar, e⟫)
    rw [e1] at k1; rw [e2] at k2
    change xbar + r • y' = y at hAy
    rw [hAy] at k1 k2
    change max (⟪y', e⟫ + a₁') 0 ≤ u (A y') / r at hl
    change u (A y') / r ≤ max (⟪y', e⟫ + b₁') 0 at hu
    rw [hA] at hl hu
    simp only at hl hu
    rw [hAy] at hl hu
    constructor
    · rw [k1]; rw [le_div_iff₀ hr] at hl; linarith
    · rw [k2]; rw [div_le_iff₀ hr] at hu; linarith

/-- **De Silva (2011), Theorem 3.1** (`FlatHarnackStatement`). -/
theorem flat_harnack : FlatHarnackStatement := fun hd ↦ flat_harnack_of_le hd

/-! ### Corollary 3.2: iteration -/

/-- **De Silva (2011), Corollary 3.2, discrete form.** Iterating Theorem 3.1 at a fixed center: the
trapping holds on `B_{r/20^m}(x̄)` with `b - a ≤ (1 - c)^m ε r` for every `m` with `ε 20^m ≤ ε̄`.
The constant `c` is at most `1/2`, so that the effective flatness `ε_m = ε ((1 - c) 20)^m` at
step `m` is `≥ ε` and the hypothesis `|Q - 1| ≤ ε_m²` persists (De Silva leaves this unstated). -/
theorem flat_harnack_iterate (hd : 2 ≤ d) : ∃ εbar > 0, ∃ c ∈ Ioc (0 : ℝ) (1 / 2),
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e xbar : E d) (r ε a₀ b₀ : ℝ), IsOpen U →
    IsViscSolution U Q u → ‖e‖ = 1 → 0 < r → ball xbar r ⊆ U → 0 < ε →
    (∀ y ∈ ball xbar r, |Q y - 1| ≤ ε ^ 2) → a₀ ≤ b₀ → b₀ - a₀ ≤ ε * r →
    (∀ y ∈ ball xbar r, max (⟪y, e⟫ + a₀) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + b₀) 0) →
    ∀ m : ℕ, ε * 20 ^ m ≤ εbar → ∃ a b : ℝ, a₀ ≤ a ∧ a ≤ b ∧ b ≤ b₀ ∧
      b - a ≤ (1 - c) ^ m * ε * r ∧ ∀ y ∈ ball xbar (r / 20 ^ m),
        max (⟪y, e⟫ + a) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + b) 0 := by
  obtain ⟨εH, hεH, cH, hcH, H⟩ := flat_harnack_of_le hd
  set c := min cH (1 / 2) with hc
  have hc0 : 0 < c := lt_min hcH.1 (by norm_num)
  have hc1 : c ≤ 1 / 2 := min_le_right _ _
  have hccH : c ≤ cH := min_le_left _ _
  refine ⟨εH, hεH, c, ⟨hc0, hc1⟩, ?_⟩
  intro U Q u e xbar r ε a₀ b₀ hU hu he hr hB hε hQ hab hba htrap m
  induction m with
  | zero =>
    intro _
    exact ⟨a₀, b₀, le_rfl, hab, le_rfl, by simpa using hba, by simpa using htrap⟩
  | succ m ih =>
    intro hm
    have h20 : (1 : ℝ) ≤ 20 := by norm_num
    have hm' : ε * 20 ^ m ≤ εH :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h20 m.le_succ) hε.le) hm
    obtain ⟨a, b, ha₀, hab', hb₀, hba', htr⟩ := ih hm'
    set q : ℝ := (1 - c) * 20 with hq
    have hq1 : 1 ≤ q := by rw [hq]; linarith
    have hq20 : q ≤ 20 := by rw [hq]; linarith
    set εm := ε * q ^ m with hεm
    set rm : ℝ := r / 20 ^ m with hrm
    have hrm0 : 0 < rm := by positivity
    have hrmr : rm ≤ r := div_le_self hr.le (one_le_pow₀ h20)
    have hεεm : ε ≤ εm := le_mul_of_one_le_right hε.le (one_le_pow₀ hq1)
    have hεmH : εm ≤ εH :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hq20 m) hε.le) hm'
    have hmr : (1 - c) ^ m * ε * r = εm * rm := by
      rw [hεm, hrm, hq, mul_pow]; field_simp
    obtain ⟨a', b', h1, h2, h3, h4, h5⟩ := H U Q u e xbar rm εm a b hU hu he hrm0
      ((ball_subset_ball hrmr).trans hB) (by positivity) hεmH
      (fun y hy ↦ (hQ y (ball_subset_ball hrmr hy)).trans
        (pow_le_pow_left₀ hε.le hεεm 2)) hab' (hmr ▸ hba') htr
    refine ⟨a', b', ha₀.trans h1, h2, h3.trans hb₀, ?_, ?_⟩
    · calc b' - a' ≤ (1 - cH) * εm * rm := h4
        _ ≤ (1 - c) * εm * rm := by
          have h : 1 - cH ≤ 1 - c := by linarith
          have : 0 ≤ εm := by positivity
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h this) hrm0.le
        _ = (1 - c) ^ (m + 1) * ε * r := by
          rw [pow_succ, show (1 - c) ^ m * (1 - c) * ε * r = (1 - c) * ((1 - c) ^ m * ε * r) by
            ring, hmr]; ring
    · have : r / 20 ^ (m + 1) = rm / 20 := by rw [hrm, pow_succ, div_div]
      rw [this]
      exact h5

/-- On `closure {u > 0} ∩ B`, the flat trapping holds without positive parts:
`⟪z, e⟫ + a ≤ u z ≤ ⟪z, e⟫ + b` (the upper bound by continuity from `{u > 0}`). -/
theorem trap_of_mem_closure_posSet {U : Set (E d)} {u : E d → ℝ} {e x₀ : E d} {ρ a b : ℝ}
    (hcu : ContinuousOn u U) (hB : ball x₀ ρ ⊆ U)
    (htrap : ∀ y ∈ ball x₀ ρ, max (⟪y, e⟫ + a) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + b) 0)
    {z : E d} (hz : z ∈ closure (posSet u U) ∩ ball x₀ ρ) :
    ⟪z, e⟫ + a ≤ u z ∧ u z ≤ ⟪z, e⟫ + b := by
  refine ⟨(le_max_left _ _).trans (htrap z hz.2).1, ?_⟩
  have hz' : z ∈ closure (ball x₀ ρ ∩ posSet u U) := isOpen_ball.inter_closure ⟨hz.2, hz.1⟩
  refine ContinuousWithinAt.closure_le (f := u) (g := fun w ↦ ⟪w, e⟫ + b) hz'
    ((hcu z (hB hz.2)).mono fun w hw ↦ hB hw.1) (by fun_prop) ?_
  rintro w ⟨hw1, hw⟩
  have h := (htrap w hw1).2
  rcases le_total (⟪w, e⟫ + b) 0 with h' | h'
  · rw [max_eq_right h'] at h; linarith [hw.2]
  · rwa [max_eq_left h'] at h

/-- `((20^n)⁻¹)^γ = (1 - c)^n` for `γ = -log (1 - c) / log 20`. -/
private theorem inv_pow_rpow_eq {c : ℝ} (hc : c < 1) (n : ℕ) :
    (((20 : ℝ) ^ n)⁻¹) ^ (-Real.log (1 - c) / Real.log 20) = (1 - c) ^ n := by
  have h1c : 0 < 1 - c := by linarith
  have hl : 0 < Real.log 20 := Real.log_pos (by norm_num)
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    Real.rpow_def_of_pos (by norm_num)]
  have : Real.log 20 * (n * (-Real.log (1 - c) / Real.log 20)) = -Real.log ((1 - c) ^ n) := by
    rw [Real.log_pow]; field_simp
  rw [this, Real.exp_neg, Real.exp_log (by positivity), inv_inv]

/-- **De Silva (2011), Corollary 3.2 (Hölder form).** There are `ε̄, C > 0` and `γ ∈ (0, 1)`
(depending on `d` only) such that, under the hypotheses of Theorem 3.1 on `B_r(x₀)` and
`x₀ ∈ closure {u > 0}` (the centre condition of Theorem 3.1), the
function `ũ = u - ⟪·, e⟫` satisfies
`|ũ(y) - ũ(x₀)| ≤ C ε r (|y - x₀|/r)^γ` for `y ∈ closure {u > 0} ∩ B_r(x₀)` with
`|y - x₀| ≥ ε r / ε̄`, i.e. `ũ/ε` is `γ`-Hölder at `x₀` down to scale `ε r / ε̄`. (For `ε > ε̄`
the conclusion is vacuous.) This is the equicontinuity input of the compactness step
(De Silva (2011), Lemma 4.1, Step 1, (4.5)). -/
theorem flat_harnack_oscillation (hd : 2 ≤ d) : ∃ εbar > 0, ∃ C > 0, ∃ γ ∈ Ioo (0 : ℝ) 1,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e x₀ : E d) (r ε a₀ b₀ : ℝ), IsOpen U →
    IsViscSolution U Q u → ‖e‖ = 1 → 0 < r → ball x₀ r ⊆ U → 0 < ε →
    (∀ y ∈ ball x₀ r, |Q y - 1| ≤ ε ^ 2) → a₀ ≤ b₀ → b₀ - a₀ ≤ ε * r →
    (∀ y ∈ ball x₀ r, max (⟪y, e⟫ + a₀) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + b₀) 0) →
    x₀ ∈ closure (posSet u U) →
    ∀ y ∈ closure (posSet u U) ∩ ball x₀ r, ε * r / εbar ≤ ‖y - x₀‖ →
      |(u y - ⟪y, e⟫) - (u x₀ - ⟪x₀, e⟫)| ≤ C * ε * r * (‖y - x₀‖ / r) ^ γ := by
  obtain ⟨εI, hεI, c, hc, H⟩ := flat_harnack_iterate hd
  have h1c : 0 < 1 - c := by linarith [hc.2]
  have hl20 : 0 < Real.log 20 := Real.log_pos (by norm_num)
  have hlc : Real.log (1 - c) < 0 := Real.log_neg h1c (by linarith [hc.1])
  set γ := -Real.log (1 - c) / Real.log 20 with hγ
  have hγ0 : 0 < γ := div_pos (by linarith) hl20
  have hγ1 : γ < 1 := by
    rw [hγ, div_lt_one hl20, neg_lt, ← Real.log_inv]
    exact Real.log_lt_log (by positivity) (by have := hc.2; norm_num; linarith)
  refine ⟨εI, hεI, 1 / (1 - c), by positivity, γ, ⟨hγ0, hγ1⟩, ?_⟩
  intro U Q u e x₀ r ε a₀ b₀ hU hu he hr hB hε hQ hab hba htrap hx₀ y hy hdist
  set ρ := ‖y - x₀‖ with hρ
  have hρr : ρ < r := by rw [hρ, ← dist_eq_norm]; exact hy.2
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by positivity) hdist
  -- the level `m` with `r / 20^(m+1) ≤ ρ < r / 20^m`
  have hex : ∃ n : ℕ, r / 20 ^ (n + 1) ≤ ρ := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (r / ρ) (by norm_num : (1 : ℝ) < 20)
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hρ0] at hn
    have : (20 : ℝ) ^ n ≤ 20 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) n.le_succ
    linarith [mul_le_mul_of_nonneg_left this hρ0.le]
  set m := Nat.find hex with hm
  have hm1 : r / 20 ^ (m + 1) ≤ ρ := Nat.find_spec hex
  have hm2 : ρ < r / 20 ^ m := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, pow_zero, div_one]; exact hρr
    · have := Nat.find_min hex (show m - 1 < m by omega)
      rw [not_le] at this
      have e : m - 1 + 1 = m := by omega
      rwa [e] at this
  have hεm : ε * 20 ^ m ≤ εI := by
    have h := lt_of_le_of_lt hdist hm2
    rw [div_lt_div_iff₀ hεI (by positivity)] at h
    have : ε * 20 ^ m * r < εI * r := by linarith
    exact (lt_of_mul_lt_mul_right this hr.le).le
  obtain ⟨a, b, -, -, -, hba', htr⟩ := H U Q u e x₀ r ε a₀ b₀ hU hu he hr hB hε hQ hab hba htrap
    m hεm
  have hBm : ball x₀ (r / 20 ^ m) ⊆ U :=
    (ball_subset_ball (div_le_self hr.le (one_le_pow₀ (by norm_num)))).trans hB
  have hty := trap_of_mem_closure_posSet hu.1.1 hBm htr
    ⟨hy.1, by rw [mem_ball, dist_eq_norm]; exact hm2⟩
  have htx := trap_of_mem_closure_posSet hu.1.1 hBm htr ⟨hx₀, mem_ball_self (by positivity)⟩
  have hosc : |(u y - ⟪y, e⟫) - (u x₀ - ⟪x₀, e⟫)| ≤ (1 - c) ^ m * ε * r := by
    rw [abs_le]; constructor <;> linarith [hty.1, hty.2, htx.1, htx.2]
  refine hosc.trans ?_
  -- `(ρ/r)^γ ≥ ((20^(m+1))⁻¹)^γ = (1 - c)^(m+1)`
  have hpow : (1 - c) ^ (m + 1) ≤ (ρ / r) ^ γ := by
    rw [← inv_pow_rpow_eq (by linarith [hc.2]) (m + 1)]
    refine Real.rpow_le_rpow (by positivity) ?_ hγ0.le
    rw [le_div_iff₀ hr, ← div_eq_inv_mul]
    exact hm1
  calc (1 - c) ^ m * ε * r = 1 / (1 - c) * ε * r * (1 - c) ^ (m + 1) := by
        rw [pow_succ]; field_simp
    _ ≤ 1 / (1 - c) * ε * r * (ρ / r) ^ γ :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

end EllipticBernoulli
