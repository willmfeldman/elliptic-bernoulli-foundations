/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.QuantChart.Wide
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Harmonic.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Lipschitz bound for the Hessian on the positive phase

`exists_hessian_lipschitz_of_flat`: for an `ε`-flat minimizer `u` in `B_1` (`ε ≤ ε₇(d)`),
`‖D²u(x) - D²u(y)‖ ≤ C ‖x - y‖` for `x, y ∈ {u > 0} ∩ B_{1/2}`.

For `δ = ‖x - y‖ < 1/256`, follow the path `x → x + t e → y + t e → y` with `t = 8δ`. Along
`e`, `u` grows (`∇u · e ≥ 1/2`). Along the horizontal segment it drops by at most `2δ < t/2`.
So the path stays in `{u > 0} ∩ B_{9/16}` (`pos_of_deriv_ge`), where `‖D³u‖ ≤ C`, and the mean
value theorem applies on each segment. For `δ ≥ 1/256`, the bound `‖D²u‖ ≤ C` suffices.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Staying positive.** Let `g` be continuous on `[0, 1]`, with `0 < g 0` and `0 < g 0 + m`, and
differentiable with `g' ≥ m` at every point of `[0, 1]` where `g > 0`. Then `g ≥ g 0 + m s > 0`
on `[0, 1]`. -/
theorem pos_of_deriv_ge {g g' : ℝ → ℝ} {m : ℝ} (hc : ContinuousOn g (Icc 0 1)) (hg0 : 0 < g 0)
    (hm : 0 < g 0 + m) (hd : ∀ s ∈ Icc (0 : ℝ) 1, 0 < g s → HasDerivAt g (g' s) s ∧ m ≤ g' s) :
    ∀ s ∈ Icc (0 : ℝ) 1, 0 < g s ∧ g 0 + m * s ≤ g s := by
  -- the lower bound on any initial interval where `g > 0`
  have hlow : ∀ b ∈ Icc (0 : ℝ) 1, (∀ s ∈ Ico 0 b, 0 < g s) → g 0 + m * b ≤ g b := by
    intro b hb hpos
    rcases hb.1.eq_or_lt with hb0 | hb0
    · rw [← hb0]; simp
    set h : ℝ → ℝ := fun s ↦ g s - m * s with hh
    have hmono : MonotoneOn h (Icc 0 b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
        ((hc.mono (Icc_subset_Icc le_rfl hb.2)).sub (continuousOn_const.mul continuousOn_id))
        (fun s hs ↦ ?_) (fun s hs ↦ ?_)
      · rw [interior_Icc] at hs
        have := (hd s ⟨hs.1.le, hs.2.le.trans hb.2⟩ (hpos s ⟨hs.1.le, hs.2⟩)).1
        exact (this.sub ((hasDerivAt_id s).const_mul m)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hs
        obtain ⟨hd1, hd2⟩ := hd s ⟨hs.1.le, hs.2.le.trans hb.2⟩ (hpos s ⟨hs.1.le, hs.2⟩)
        have h3 : HasDerivAt (fun s ↦ g s - m * s) (g' s - m * 1) s :=
          hd1.sub ((hasDerivAt_id s).const_mul m)
        rw [h3.deriv]; linarith
    have := hmono ⟨le_rfl, hb0.le⟩ ⟨hb0.le, le_rfl⟩ hb0.le
    simp only [hh, mul_zero, sub_zero] at this
    linarith
  -- `g` stays positive
  have hpos_all : ∀ s ∈ Icc (0 : ℝ) 1, 0 < g s := by
    by_contra hcon
    push Not at hcon
    set S := {s ∈ Icc (0 : ℝ) 1 | g s ≤ 0} with hS
    have hSne : S.Nonempty := hcon
    have hScl : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSbdd : BddBelow S := ⟨0, fun s hs ↦ hs.1.1⟩
    set s₀ := sInf S
    have hs₀ : s₀ ∈ S := hScl.csInf_mem hSne hSbdd
    have hbefore : ∀ s ∈ Ico 0 s₀, 0 < g s := fun s hs ↦ by
      by_contra hle
      push Not at hle
      have : s₀ ≤ s := csInf_le hSbdd ⟨⟨hs.1, hs.2.le.trans hs₀.1.2⟩, hle⟩
      linarith [hs.2]
    have h1 := hlow s₀ hs₀.1 hbefore
    have h2 : 0 < g 0 + m * s₀ := by
      rcases le_total 0 m with hm0 | hm0
      · nlinarith [hs₀.1.1]
      · nlinarith [hs₀.1.1, hs₀.1.2]
    linarith [hs₀.2]
  intro s hs
  exact ⟨hpos_all s hs, hlow s hs fun s' hs' ↦ hpos_all s' ⟨hs'.1, hs'.2.le.trans hs.2⟩⟩

/-- **Lipschitz bound for the Hessian on the positive phase.** -/
theorem exists_hessian_lipschitz_of_flat (hd : 2 ≤ d) : ∃ ε₇ > 0, ∃ C ≥ 0,
    ∀ {u : E d → ℝ} {e : E d} {ε : ℝ}, 0 < ε → ε ≤ ε₇ →
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ x ∈ posSet u (ball 0 1) ∩ ball 0 (1 / 2), ∀ y ∈ posSet u (ball 0 1) ∩ ball 0 (1 / 2),
      ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖ ≤ C * ‖x - y‖ := by
  obtain ⟨ε₆, hε₆, CW, hCW, HW⟩ := exists_bounds_of_flat_wide (d := d) hd
  refine ⟨min ε₆ (1 / (4 * (CW + 1))), lt_min hε₆ (by positivity), 512 * CW, by positivity,
    fun {u e ε} hε hεle hc hnn hmin he hflat x hx y hy ↦ ?_⟩
  have hε6 : ε ≤ ε₆ := hεle.trans (min_le_left _ _)
  have hεC : CW * ε ≤ 1 / 4 := by
    have := hεle.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; nlinarith
  set P : Set (E d) := posSet u (ball 0 1) ∩ ball 0 (9 / 16) with hP
  have hW := HW hε hε6 hc hnn hmin he hflat
  have hH : HarmonicOnNhd u (posSet u (ball 0 1)) :=
    IsViscSolution.harmonicOnNhd_posSet isOpen_ball (IsLocalEnergyMinimizer.isViscSolution
      isOpen_ball continuousOn_const (fun _ _ ↦ zero_le_one) hc hnn hmin)
  have hsm : ∀ z ∈ posSet u (ball 0 1), ContDiffAt ℝ ∞ u z := fun z hz ↦
    (HarmonicOnNhd.contDiffOn_top (isOpen_posSet isOpen_ball hc) hH).contDiffAt
      ((isOpen_posSet isOpen_ball hc).mem_nhds hz)
  have hgr : ∀ z ∈ P, ‖∇ u z - e‖ ≤ 1 / 4 := fun z hz ↦ (hW z hz).1.trans hεC
  -- the mean value theorem along a segment in `P`
  have hseg : ∀ p q : E d, (∀ l ∈ Icc (0 : ℝ) 1, p + l • (q - p) ∈ P) →
      ‖iteratedFDeriv ℝ 2 u q - iteratedFDeriv ℝ 2 u p‖ ≤ CW * ‖q - p‖ := by
    intro p q hpq
    have hder : ∀ l ∈ Icc (0 : ℝ) 1, HasDerivAt (fun l : ℝ ↦ iteratedFDeriv ℝ 2 u (p + l • (q - p)))
        (fderiv ℝ (iteratedFDeriv ℝ 2 u) (p + l • (q - p)) (q - p)) l := by
      intro l hl
      have hz := hpq l hl
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) (p + l • (q - p)) :=
        ((hsm _ hz.1).iteratedFDeriv_right (m := 1) (i := 2) (by simp)).differentiableAt
          (by simp)
      have hl' : HasDerivAt (fun l : ℝ ↦ p + l • (q - p)) (q - p) l := by
        simpa using ((hasDerivAt_id l).smul_const (q - p)).const_add p
      exact hdiff.hasFDerivAt.comp_hasDerivAt l hl'
    have := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun l : ℝ ↦ iteratedFDeriv ℝ 2 u (p + l • (q - p)))
      (fun l hl ↦ (hder l hl).hasDerivWithinAt) (C := CW * ‖q - p‖) (fun l hl ↦ by
        have hz := hpq l (Ico_subset_Icc_self hl)
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_fderiv_iteratedFDeriv]
        exact mul_le_mul_of_nonneg_right (hW _ hz).2.2 (norm_nonneg _))
    simpa using this
  -- positivity along a segment
  have hpath : ∀ p q : E d, (∀ l ∈ Icc (0 : ℝ) 1, ‖p + l • (q - p)‖ < 9 / 16) → 0 < u p →
      ∀ m : ℝ, 0 < u p + m → (∀ z ∈ P, m ≤ ⟪∇ u z, q - p⟫) →
      ∀ l ∈ Icc (0 : ℝ) 1, p + l • (q - p) ∈ P ∧ u p + m * l ≤ u (p + l • (q - p)) := by
    intro p q hn hp m hm hmz
    have hB : ∀ l ∈ Icc (0 : ℝ) 1, p + l • (q - p) ∈ ball (0 : E d) 1 := fun l hl ↦ by
      rw [mem_ball, dist_zero_right]; linarith [hn l hl]
    have hgc : ContinuousOn (fun l : ℝ ↦ u (p + l • (q - p))) (Icc 0 1) :=
      hc.comp (by fun_prop) fun l hl ↦ hB l hl
    have key := pos_of_deriv_ge (g := fun l : ℝ ↦ u (p + l • (q - p)))
      (g' := fun l ↦ ⟪∇ u (p + l • (q - p)), q - p⟫) (m := m) hgc (by simpa using hp)
      (by simpa using hm) (fun l hl hpos ↦ by
        have hzP : p + l • (q - p) ∈ P :=
          ⟨⟨hB l hl, hpos⟩, by rw [mem_ball, dist_zero_right]; exact hn l hl⟩
        refine ⟨?_, hmz _ hzP⟩
        have hdiff : DifferentiableAt ℝ u (p + l • (q - p)) :=
          (hsm _ hzP.1).differentiableAt (by simp)
        have hl' : HasDerivAt (fun l : ℝ ↦ p + l • (q - p)) (q - p) l := by
          simpa using ((hasDerivAt_id l).smul_const (q - p)).const_add p
        have := hdiff.hasFDerivAt.comp_hasDerivAt l hl'
        rwa [← inner_gradient_left_eq_fderiv] at this)
    intro l hl
    obtain ⟨h1, h2⟩ := key l hl
    simp only [zero_smul, add_zero] at h2
    exact ⟨⟨⟨hB l hl, h1⟩, by rw [mem_ball, dist_zero_right]; exact hn l hl⟩, h2⟩
  set δ := ‖x - y‖ with hδ
  have hxn : ‖x‖ < 1 / 2 := by simpa using hx.2
  have hyn : ‖y‖ < 1 / 2 := by simpa using hy.2
  have hxP : x ∈ P := ⟨hx.1, ball_subset_ball (by norm_num) hx.2⟩
  have hyP : y ∈ P := ⟨hy.1, ball_subset_ball (by norm_num) hy.2⟩
  by_cases hδs : 1 / 256 ≤ δ
  · calc ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖
        ≤ ‖iteratedFDeriv ℝ 2 u x‖ + ‖iteratedFDeriv ℝ 2 u y‖ := norm_sub_le _ _
      _ ≤ CW + CW := add_le_add (hW x hxP).2.1 (hW y hyP).2.1
      _ ≤ 512 * CW * δ := by nlinarith
  push Not at hδs
  set t := 8 * δ with ht
  have hδ0 : 0 ≤ δ := norm_nonneg _
  -- the gradient along `e` and along `y - x`
  have hge : ∀ z ∈ P, 3 / 4 * t ≤ ⟪∇ u z, t • e⟫ := fun z hz ↦ by
    have h1 : ⟪∇ u z, e⟫ = 1 + ⟪∇ u z - e, e⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, he]; ring
    have h2 := abs_real_inner_le_norm (∇ u z - e) e
    rw [he, mul_one] at h2
    have h3 := hgr z hz
    rw [real_inner_smul_right]
    nlinarith [neg_abs_le ⟪∇ u z - e, e⟫]
  have hgn : ∀ z ∈ P, ‖∇ u z‖ ≤ 2 := fun z hz ↦ by
    have := norm_le_norm_add_norm_sub' (∇ u z) e
    rw [he] at this; linarith [hgr z hz]
  have hvert : ∀ p ∈ P, ‖p‖ < 1 / 2 → ∀ l ∈ Icc (0 : ℝ) 1,
      p + l • (p + t • e - p) ∈ P ∧ u p + 3 / 4 * t * l ≤ u (p + l • (p + t • e - p)) := by
    intro p hp hpn
    refine hpath p (p + t • e) (fun l hl ↦ ?_) hp.1.2 (3 / 4 * t) (by have := hp.1.2; positivity)
      (fun z hz ↦ by rw [add_sub_cancel_left]; exact hge z hz)
    rw [add_sub_cancel_left, smul_smul]
    calc ‖p + (l * t) • e‖ ≤ ‖p‖ + ‖(l * t) • e‖ := norm_add_le _ _
      _ = ‖p‖ + l * t := by
          rw [norm_smul, he, mul_one, Real.norm_of_nonneg (mul_nonneg hl.1 (by positivity))]
      _ < 9 / 16 := by nlinarith [hl.2]
  have hvx := hvert x hxP hxn
  have hvy := hvert y hyP hyn
  have hxt : x + t • e ∈ P := by simpa using (hvx 1 ⟨zero_le_one, le_rfl⟩).1
  have hyt : y + t • e ∈ P := by simpa using (hvy 1 ⟨zero_le_one, le_rfl⟩).1
  have hux : u x + 3 / 4 * t ≤ u (x + t • e) := by simpa using (hvx 1 ⟨zero_le_one, le_rfl⟩).2
  -- the horizontal segment
  have hhor := hpath (x + t • e) (y + t • e) (fun l hl ↦ by
      rw [add_sub_add_right_eq_sub]
      calc ‖x + t • e + l • (y - x)‖ ≤ ‖x‖ + ‖t • e‖ + ‖l • (y - x)‖ := norm_add₃_le
        _ = ‖x‖ + t + l * δ := by
            rw [norm_smul, norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity),
              Real.norm_of_nonneg hl.1, norm_sub_rev]
        _ < 9 / 16 := by nlinarith [hl.2])
    hxt.1.2 (-(2 * δ)) (by have := hx.1.2; linarith) (fun z hz ↦ by
      rw [add_sub_add_right_eq_sub]
      have h1 := real_inner_le_norm (∇ u z) (y - x)
      have h2 := neg_abs_le ⟪∇ u z, y - x⟫
      have h3 := abs_real_inner_le_norm (∇ u z) (y - x)
      rw [norm_sub_rev] at h3
      nlinarith [hgn z hz])
  have s1 := hseg x (x + t • e) fun l hl ↦ (hvx l hl).1
  have s2 := hseg (x + t • e) (y + t • e) fun l hl ↦ (hhor l hl).1
  have s3 := hseg y (y + t • e) fun l hl ↦ (hvy l hl).1
  rw [add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_of_nonneg (by positivity)] at s1 s3
  rw [add_sub_add_right_eq_sub] at s2
  have s2' : ‖iteratedFDeriv ℝ 2 u (y + t • e) - iteratedFDeriv ℝ 2 u (x + t • e)‖ ≤ CW * δ :=
    s2.trans (le_of_eq (by rw [hδ, norm_sub_rev]))
  calc ‖iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u y‖
      = ‖(iteratedFDeriv ℝ 2 u x - iteratedFDeriv ℝ 2 u (x + t • e)) +
          (iteratedFDeriv ℝ 2 u (x + t • e) - iteratedFDeriv ℝ 2 u (y + t • e)) +
          (iteratedFDeriv ℝ 2 u (y + t • e) - iteratedFDeriv ℝ 2 u y)‖ := by abel_nf
    _ ≤ CW * t + CW * δ + CW * t := by
        refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) s3)
        · rw [norm_sub_rev]; exact s1
        · rw [norm_sub_rev]; exact s2'
    _ ≤ 512 * CW * δ := by nlinarith

end EllipticBernoulli
