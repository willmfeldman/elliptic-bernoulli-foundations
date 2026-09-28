/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Lipschitz
public import EllipticBernoulli.Viscosity.Calculus
public import Mathlib.Analysis.Convex.Basic
import EllipticBernoulli.Lipschitz.LinearGrowth
import EllipticBernoulli.Harmonic.GradientEstimate
import EllipticBernoulli.Viscosity.Harmonic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Lipschitz estimate for viscosity supersolutions (Caffarelli–Salsa, Lemma 11.19)

Let `u` be a viscosity supersolution in `U` (Abedin–Feldman–Stinson, Definition 2.1(i); only the
supersolution half is used), harmonic in `{u > 0}`, with `Q ≤ Qmax` and `u ≤ M` on
`B_{2r}(x₀) ⊆ U`. The proof has three steps; Step 1, linear growth away from the zero set, is
`Lipschitz/LinearGrowth.lean`.

* `exists_norm_gradient_le` (Step 2): `|∇u| ≤ C₂ (Qmax + M / r)` on `B_r(x₀) ∩ {u > 0}`. Near the
  zero set this combines the linear growth of `Lipschitz/LinearGrowth.lean` with the interior
  gradient estimate (`norm_gradient_le_of_harmonic`) on `B_{δ/2}(x)`, `δ` the distance to the
  nearest zero; away from it the gradient estimate alone gives `C M / r`.
* `sub_le_mul_dist_of_norm_gradient_le` (Step 3): a continuous `u ≥ 0` on a convex set whose
  gradient is bounded by `L` on `{u > 0}` is `L`-Lipschitz. Along `[a, b]` with `u(a) > 0`, apply
  the mean value inequality up to the first zero of `u` (or up to `b`).
* `lipschitzOnWith_of_isViscSuper` (`LipschitzEstimateStatement`) and
  `locallyLipschitzOn_of_isViscSuper` (`LocalLipschitzStatement`): the headline statements.
* `locallyLipschitzOn_of_isViscSolution`: the form for viscosity solutions (harmonicity in
  `{u > 0}` from `IsViscSolution.harmonicOnNhd_posSet`, which uses viscosity-harmonic ⇒
  harmonic).

Dimension: `1 ≤ d` in the quantitative statements; the local statement holds for all `d` (in `E 0`
every function is Lipschitz).

## References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Step 3: Lipschitz across the zero set -/

/-- **Lipschitz bound across the zero set.** Let `S` be convex and `u ≥ 0` continuous on `S`,
differentiable with `|∇u| ≤ L` at the points of `S` where `u > 0`. Then
`u(a) - u(b) ≤ L |a - b|` for `a, b ∈ S`. -/
theorem sub_le_mul_dist_of_norm_gradient_le {S : Set (E d)} (hS : Convex ℝ S) {u : E d → ℝ}
    {L : ℝ} (hL : 0 ≤ L) (hc : ContinuousOn u S) (hnn : ∀ p ∈ S, 0 ≤ u p)
    (hdiff : ∀ p ∈ S, 0 < u p → DifferentiableAt ℝ u p)
    (hgrad : ∀ p ∈ S, 0 < u p → ‖∇ u p‖ ≤ L) {a b : E d} (ha : a ∈ S) (hb : b ∈ S) :
    u a - u b ≤ L * dist a b := by
  have hLd : 0 ≤ L * dist a b := mul_nonneg hL dist_nonneg
  rcases (hnn a ha).lt_or_eq with hua | hua
  swap
  · rw [← hua]; linarith [hnn b hb]
  set ℓ : ℝ → E d := fun t ↦ a + t • (b - a) with hℓ
  set g : ℝ → ℝ := fun t ↦ u (ℓ t) with hg
  have hℓS : ∀ t ∈ Icc (0 : ℝ) 1, ℓ t ∈ S := fun t ht ↦ hS.add_smul_sub_mem ha hb ht
  have hℓc : Continuous ℓ := continuous_const.add (continuous_id.smul continuous_const)
  have hgc : ContinuousOn g (Icc 0 1) := hc.comp hℓc.continuousOn hℓS
  have hg0 : g 0 = u a := by simp [hg, hℓ]
  have hg1 : g 1 = u b := by simp [hg, hℓ]
  have hgnn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t := fun t ht ↦ hnn _ (hℓS t ht)
  -- `t`: the first zero of `g` on `[0, 1]`, or `1` if there is none
  obtain ⟨t, ht, hgt, hpos⟩ : ∃ t ∈ Icc (0 : ℝ) 1, g t ≤ g 1 ∧ ∀ s ∈ Ico 0 t, 0 < g s := by
    set T := Icc (0 : ℝ) 1 ∩ g ⁻¹' {0} with hT
    have hTc : IsClosed T := hgc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hTk : IsCompact T := isCompact_Icc.of_isClosed_subset hTc inter_subset_left
    by_cases hTne : T.Nonempty
    · obtain ⟨t, ⟨ht, hgt⟩, hmin⟩ := hTk.exists_isMinOn hTne continuousOn_id
      have hgt' : g t = 0 := hgt
      refine ⟨t, ht, by rw [hgt']; exact hgnn 1 (right_mem_Icc.2 zero_le_one), fun s hs ↦ ?_⟩
      have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le.trans ht.2⟩
      refine lt_of_le_of_ne (hgnn s hs1) fun h ↦ ?_
      have : t ≤ s := hmin ⟨hs1, h.symm⟩
      linarith [hs.2]
    · refine ⟨1, right_mem_Icc.2 zero_le_one, le_rfl, fun s hs ↦ ?_⟩
      have hs1 : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      exact lt_of_le_of_ne (hgnn s hs1) fun h ↦ hTne ⟨s, hs1, h.symm⟩
  -- mean value inequality on `[0, t]`
  have hsub : Icc 0 t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_right ht.2
  have hderiv : ∀ s ∈ Ico 0 t, HasDerivWithinAt g (fderiv ℝ u (ℓ s) (b - a)) (Ici s) s := by
    intro s hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := hsub (Ico_subset_Icc_self hs)
    have hℓd : HasDerivAt ℓ (b - a) s := by
      have := ((hasDerivAt_id s).smul_const (b - a)).const_add a
      rwa [one_smul] at this
    exact ((hdiff _ (hℓS s hs1) (hpos s hs)).hasFDerivAt.comp_hasDerivAt s hℓd).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico 0 t, ‖fderiv ℝ u (ℓ s) (b - a)‖ ≤ L * ‖b - a‖ := by
    intro s hs
    have hs1 : s ∈ Icc (0 : ℝ) 1 := hsub (Ico_subset_Icc_self hs)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [← norm_gradient_eq_norm_fderiv]
    exact mul_le_mul_of_nonneg_right (hgrad _ (hℓS s hs1) (hpos s hs)) (norm_nonneg _)
  have hmvt := norm_image_sub_le_of_norm_deriv_right_le_segment (hgc.mono hsub) hderiv hbound t
    (right_mem_Icc.2 ht.1)
  rw [Real.norm_eq_abs, hg0, sub_zero] at hmvt
  have h1 : u a - g t ≤ L * ‖b - a‖ * t := by
    have := neg_abs_le (g t - u a)
    linarith
  have h2 : L * ‖b - a‖ * t ≤ L * dist a b := by
    rw [dist_comm, dist_eq_norm]
    exact mul_le_of_le_one_right (mul_nonneg hL (norm_nonneg _)) ht.2
  rw [← hg1]
  linarith

/-! ### Step 2: gradient bound on the positivity set -/

/-- **Gradient bound** (Caffarelli–Salsa, Lemma 11.19; Step 2). For `1 ≤ d` there is `C₂ ≥ 0` such
that, under the hypotheses of `LipschitzEstimateStatement`, `|∇u(x)| ≤ C₂ (Qmax + M / r)` at every
`x ∈ B_r(x₀)` with `u(x) > 0`. -/
theorem exists_norm_gradient_le (hd : 1 ≤ d) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) (r Qmax M : ℝ),
      IsOpen U → 0 < r → ball x₀ (2 * r) ⊆ U → IsViscSuper U Q u →
      HarmonicOnNhd u (posSet u U) → (∀ y ∈ ball x₀ (2 * r), Q y ≤ Qmax) → 0 ≤ Qmax →
      (∀ y ∈ ball x₀ (2 * r), u y ≤ M) →
      ∀ x ∈ ball x₀ r, 0 < u x → ‖∇ u x‖ ≤ C₂ * (Qmax + M / r) := by
  obtain ⟨C₁, hC₁, hlin⟩ := exists_le_mul_of_isViscSuper hd
  obtain ⟨Cg, hCg⟩ := norm_gradient_le_of_harmonic hd
  set Cg' := max Cg 0 with hCg'
  have hCg'0 : 0 ≤ Cg' := le_max_right _ _
  refine ⟨Cg' * (3 * C₁ + 2), by positivity, ?_⟩
  intro U Q u x₀ r Qmax M hU hr hB hu hh hQ hQmax hM x hx hux
  have hnn : ∀ z ∈ U, 0 ≤ u z := hu.2.1
  -- balls around `x` of radius `≤ r` stay in `B_{2r}(x₀)`
  have hball : ∀ t ≤ r, closedBall x t ⊆ ball x₀ (2 * r) := by
    intro t ht z hz
    rw [mem_ball] at hx ⊢
    have := dist_triangle z x x₀
    have := mem_closedBall.1 hz
    linarith
  have hM0 : 0 ≤ M := (hnn x (hB (hball r le_rfl (mem_closedBall_self hr.le)))).trans
    (hM x (hball r le_rfl (mem_closedBall_self hr.le)))
  have hMr : 0 ≤ M / r := div_nonneg hM0 hr.le
  have hCg_le : ∀ K ρ : ℝ, 0 ≤ K → 0 < ρ → Cg * K / ρ ≤ Cg' * K / ρ := fun K ρ hK hρ ↦
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hK) hρ.le
  by_cases hZ : ∃ y ∈ closedBall x (r / 2), u y = 0
  · -- near the zero set: linear growth + gradient estimate on `B_{δ/2}(x)`
    obtain ⟨y, hyB, huy, hδ, hpos⟩ :=
      exists_nearest_zero hu.1 hnn ((hball _ (by linarith)).trans hB) hux hZ
    set δ := dist y x with hδdef
    have hδs : δ ≤ r / 2 := mem_closedBall.1 hyB
    have hH : HarmonicOnNhd u (closedBall x (δ / 2)) := fun z hz ↦ by
      have hz' : z ∈ ball x δ := mem_ball.2 ((mem_closedBall.1 hz).trans_lt (by linarith))
      exact hh z ⟨hB (hball r (by linarith) (ball_subset_closedBall
        (ball_subset_ball (by linarith) hz'))), hpos z hz'⟩
    have hbd : ∀ z ∈ closedBall x (δ / 2), |u z| ≤ C₁ * Qmax * (3 * δ / 2) := by
      intro z hz
      have hzx : dist z x ≤ δ / 2 := mem_closedBall.1 hz
      have hsub : closedBall z (3 * δ / 2) ⊆ ball x₀ (2 * r) := by
        refine (closedBall_subset_closedBall' ?_).trans (hball r le_rfl)
        linarith
      rw [abs_of_nonneg (hnn z (hB (hsub (mem_closedBall_self (by positivity)))))]
      refine hlin U Q u z (3 * δ / 2) Qmax hU hu hh (hsub.trans hB) (fun w hw ↦ hQ w (hsub hw))
        hQmax ⟨y, ?_, huy⟩
      rw [mem_closedBall]
      have := dist_triangle y x z
      rw [dist_comm x z] at this
      linarith
    have h1 := hCg u x (δ / 2) _ (by positivity) hH hbd
    have h2 : Cg' * (C₁ * Qmax * (3 * δ / 2)) / (δ / 2) = Cg' * (3 * C₁) * Qmax := by
      field_simp
    have h3 := hCg_le (C₁ * Qmax * (3 * δ / 2)) (δ / 2) (by positivity) (by positivity)
    calc ‖∇ u x‖ ≤ Cg' * (3 * C₁) * Qmax := by rw [← h2]; exact h1.trans h3
      _ ≤ Cg' * (3 * C₁ + 2) * (Qmax + M / r) := by
        have : 3 * C₁ * Qmax ≤ (3 * C₁ + 2) * (Qmax + M / r) := by
          linarith [mul_nonneg hC₁ hMr]
        calc Cg' * (3 * C₁) * Qmax = Cg' * (3 * C₁ * Qmax) := by ring
          _ ≤ Cg' * ((3 * C₁ + 2) * (Qmax + M / r)) := mul_le_mul_of_nonneg_left this hCg'0
          _ = _ := by ring
  · -- away from the zero set: gradient estimate on `B_{r/2}(x)`
    push Not at hZ
    have hsub := hball (r / 2) (by linarith)
    have hH : HarmonicOnNhd u (closedBall x (r / 2)) := fun z hz ↦
      hh z ⟨hB (hsub hz), lt_of_le_of_ne (hnn z (hB (hsub hz))) (hZ z hz).symm⟩
    have hbd : ∀ z ∈ closedBall x (r / 2), |u z| ≤ M := fun z hz ↦ by
      rw [abs_of_nonneg (hnn z (hB (hsub hz)))]; exact hM z (hsub hz)
    have h1 := (hCg u x (r / 2) M (by positivity) hH hbd).trans
      (hCg_le M (r / 2) hM0 (by positivity))
    have h2 : Cg' * M / (r / 2) = Cg' * 2 * (M / r) := by field_simp
    calc ‖∇ u x‖ ≤ Cg' * 2 * (M / r) := by rw [← h2]; exact h1
      _ ≤ Cg' * (3 * C₁ + 2) * (Qmax + M / r) := by
        have : 2 * (M / r) ≤ (3 * C₁ + 2) * (Qmax + M / r) := by nlinarith
        calc Cg' * 2 * (M / r) = Cg' * (2 * (M / r)) := by ring
          _ ≤ Cg' * ((3 * C₁ + 2) * (Qmax + M / r)) := mul_le_mul_of_nonneg_left this hCg'0
          _ = _ := by ring

/-! ### The headline statements -/

/-- **Quantitative Lipschitz estimate** (`LipschitzEstimateStatement`; Caffarelli–Salsa
Lemma 11.19, `1 ≤ d`). -/
theorem lipschitzOnWith_of_isViscSuper : LipschitzEstimateStatement := by
  intro d hd
  obtain ⟨C₂, hC₂, hgrad⟩ := exists_norm_gradient_le hd
  refine ⟨C₂, ?_⟩
  intro U Q u x₀ r Qmax M hU hr hB hu hh hQ hQmax hM
  have hsub : ball x₀ r ⊆ U := (ball_subset_ball (by linarith)).trans hB
  have hM0 : 0 ≤ M := (hu.2.1 x₀ (hsub (mem_ball_self hr))).trans
    (hM x₀ (mem_ball_self (by linarith)))
  have hL : 0 ≤ C₂ * (Qmax + M / r) := by positivity
  have key : ∀ a ∈ ball x₀ r, ∀ b ∈ ball x₀ r, u a - u b ≤ C₂ * (Qmax + M / r) * dist a b :=
    fun a ha b hb ↦ sub_le_mul_dist_of_norm_gradient_le (convex_ball x₀ r) hL
      (hu.1.mono hsub) (fun p hp ↦ hu.2.1 p (hsub hp))
      (fun p hp hup ↦ (hh p ⟨hsub hp, hup⟩).1.differentiableAt (by norm_num))
      (fun p hp hup ↦ hgrad U Q u x₀ r Qmax M hU hr hB hu hh hQ hQmax hM p hp hup) ha hb
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [Real.coe_toNNReal _ hL, Real.dist_eq, abs_sub_le_iff]
  exact ⟨key a ha b hb, by rw [dist_comm]; exact key b hb a ha⟩

/-- **Local Lipschitz regularity** (`LocalLipschitzStatement`) of viscosity supersolutions
harmonic in `{u > 0}`, for continuous `Q`. -/
theorem locallyLipschitzOn_of_isViscSuper : LocalLipschitzStatement := by
  intro d U Q u hU hu hh hQc x hx
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨0, U, self_mem_nhdsWithin, LipschitzOnWith.of_dist_le_mul fun a _ b _ ↦ ?_⟩
    have : a = b := by ext i; exact i.elim0
    simp [this]
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
  set r := ε / 4 with hr
  have hr0 : 0 < r := by positivity
  have hcl : closedBall x (2 * r) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  obtain ⟨CQ, hCQ⟩ := (isCompact_closedBall x (2 * r)).exists_bound_of_continuousOn
    (hQc.mono hcl)
  obtain ⟨CU, hCU⟩ := (isCompact_closedBall x (2 * r)).exists_bound_of_continuousOn
    (hu.1.mono hcl)
  obtain ⟨C, hC⟩ := lipschitzOnWith_of_isViscSuper hd
  refine ⟨_, ball x r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hr0),
    hC U Q u x r (max CQ 0) CU hU hr0 (ball_subset_closedBall.trans hcl) hu hh
      (fun y hy ↦ ?_) (le_max_right _ _) (fun y hy ↦ ?_)⟩
  · exact (le_abs_self _).trans ((hCQ y (ball_subset_closedBall hy)).trans (le_max_left _ _))
  · exact (le_abs_self _).trans (hCU y (ball_subset_closedBall hy))

/-- **Viscosity solutions are locally Lipschitz.** A viscosity solution with continuous `Q` is
locally Lipschitz. Harmonicity in `{u > 0}` comes from `IsViscSolution.harmonicOnNhd_posSet`
(hence `harmonicOnNhd_of_isViscHarmonic`). -/
theorem locallyLipschitzOn_of_isViscSolution {U : Set (E d)} {Q u : E d → ℝ} (hU : IsOpen U)
    (hQ : ContinuousOn Q U) (hu : IsViscSolution U Q u) : LocallyLipschitzOn U u :=
  locallyLipschitzOn_of_isViscSuper hU hu.1 (IsViscSolution.harmonicOnNhd_posSet hU hu) hQ

end EllipticBernoulli
