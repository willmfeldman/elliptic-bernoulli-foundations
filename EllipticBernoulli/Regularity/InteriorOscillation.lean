/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.ObstacleBoundary
public import EllipticBernoulli.Regularity.Isoperimetric

/-!
# Interior oscillation decay for De Giorgi classes

The interior counterpart of the boundary oscillation decay (`Regularity/Oscillation.lean`), with
the geometric vanishing set `B_ρ(z) \ B` replaced by a density hypothesis.

* `measure_shrink_step_interior`: one measure-shrinking step, from the isoperimetric lemma
  `measure_zero_mul_integral_le`.
* `oscillation_main_interior`, `oscillation_decay_interior`: if `f ∈ DG⁺` on balls centred at `z`
  (levels `≥ K`), `f ≤ M` a.e. on `B_ρ(z)` and `|{f ≤ K} ∩ B_{ρ/2}(z)| ≥ ½ |B_{ρ/2}(z)|`, then
  `f ≤ K + (1 - 2^{-(n+1)}) (M - K) + 2ⁿ √C₁ ρ` a.e. on `B_{ρ/4}(z)`, `n = oscNI d CS C₀`.
* `osc_step_interior`: one two-sided step. Given `m ≤ f ≤ M` a.e. on `B_R(y)` and, at the middle
  level `k₀ = (m + M)/2`, either `f ∈ DG⁺` or a lower bound `f ≥ k₀ - β`, and either `-f ∈ DG⁺`
  or an upper bound `f ≤ k₀ + β` (the **obstacle alternative**), the oscillation on `B_{R/4}(y)`
  is at most `(1 - 2^{-(n+2)}) (M - m) + 2ⁿ √C₁ R + β`.
* `EssOscVanishes`, `essOscVanishes_of_step`: iterating a one-step decay on the radii `R₀ 4^{-i}`,
  the essential oscillation of `f` on small balls centred at `y` tends to zero.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Measure shrinking -/

/-- **One step of measure shrinking in the interior.** For levels `a < b`, `λ > 0` and a ball
`B = B_ρ(z)` with `B̄ ⊆ U`:
`(b - a) |{f > b} ∩ B| |{f ≤ a} ∩ B| ≤`
`2ρ 2ᵈ |B| (λ/2 |{a < f ≤ b} ∩ B| + (2λ)⁻¹ ∫_B |∇(f - a)₊|²)`. -/
theorem measure_shrink_step_interior {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    {G : E d → E d} (hf : MemH1Loc U f G) {z : E d} {ρ : ℝ} (hρ : 0 < ρ)
    (hzU : closedBall z ρ ⊆ U) {a b : ℝ} (hab : a < b) {lam : ℝ} (hlam : 0 < lam) :
    (b - a) * (volume ({x | b < f x} ∩ ball z ρ)).toReal *
        (volume ({x | f x ≤ a} ∩ ball z ρ)).toReal ≤
      2 * ρ * (2 ^ d * (volume (ball z ρ)).toReal) *
        (lam / 2 * (volume ({x | a < f x ∧ f x ≤ b} ∩ ball z ρ)).toReal +
          1 / (2 * lam) * ∫ x in ball z ρ, ‖{y | a < f y}.indicator G x‖ ^ 2) := by
  set c := b - a with hcdef
  have hc : 0 < c := sub_pos.2 hab
  set F : E d → ℝ := fun y ↦ max (f y - a) 0 with hFdef
  set GF : E d → E d := {y | a < f y}.indicator G with hGFdef
  have hF : MemH1Loc U F GF := hf.posPart_sub hU a
  have hF2 := hF.posPart_sub hU c
  have hg := hF.sub hF2
  set g : E d → ℝ := fun x ↦ F x - max (F x - c) 0 with hgdef
  set Gg : E d → E d := fun x ↦ GF x - {y | c < F y}.indicator GF x with hGgdef
  have hg_nn : ∀ x, 0 ≤ g x := by
    intro x
    simp only [hgdef]
    rcases le_or_gt (F x) c with h | h
    · rw [max_eq_right (by linarith)]; simp only [sub_zero, hFdef]; exact le_max_right _ _
    · rw [max_eq_left (by linarith)]; linarith
  have hg_zero : ∀ x, f x ≤ a → g x = 0 := by
    intro x hx
    have hF0 : F x = 0 := max_eq_right (by linarith)
    simp only [hgdef, hF0, zero_sub]
    rw [max_eq_right (by linarith)]; simp
  have hg_ge : ∀ x, b < f x → c ≤ g x := by
    intro x hx
    have hFx : F x = f x - a := max_eq_left (by linarith)
    simp only [hgdef, hFx]
    rw [max_eq_left (by linarith)]; linarith
  set D := {x | a < f x ∧ f x ≤ b} with hDdef
  have hGg : ∀ x, ‖Gg x‖ ≤ D.indicator (fun _ ↦ lam / 2) x + ‖GF x‖ ^ 2 / (2 * lam) := by
    intro x
    by_cases hxD : x ∈ D
    · have hFx : F x = f x - a := max_eq_left (by linarith [hxD.1])
      have hnc : x ∉ {y | c < F y} := by
        simp only [mem_ofPred_eq, not_lt, hFx, hcdef]; linarith [hxD.2]
      rw [indicator_of_mem hxD]
      simp only [hGgdef, indicator_of_notMem hnc, sub_zero]
      exact le_amgm hlam
    · rw [indicator_of_notMem hxD, zero_add]
      have : Gg x = 0 := by
        by_cases hfa : f x ≤ a
        · have h1 : GF x = 0 :=
            indicator_of_notMem (show x ∉ {y | a < f y} from not_lt.2 hfa) _
          have hF0 : F x = 0 := max_eq_right (by linarith)
          have h2 : x ∉ {y | c < F y} := by simp [hF0, hc.le]
          simp [hGgdef, h1, indicator_of_notMem h2]
        · have hfb : b < f x := by
            by_contra hfb; exact hxD ⟨not_le.1 hfa, not_lt.1 hfb⟩
          have hFx : F x = f x - a := max_eq_left (by linarith)
          have h2 : x ∈ {y | c < F y} := by simp only [mem_ofPred_eq, hFx, hcdef]; linarith
          simp [hGgdef, indicator_of_mem h2]
      rw [this, norm_zero]; positivity
  set B := ball z ρ with hBdef
  have hKc : IsCompact (closedBall z ρ) := isCompact_closedBall _ _
  -- the isoperimetric lemma
  have hiso := measure_zero_mul_integral_le hU hg.1 hρ hzU
  have hZ : (volume ({x | f x ≤ a} ∩ B)).toReal ≤ (volume ({y | g y = 0} ∩ B)).toReal :=
    ENNReal.toReal_mono (volume_inter_ball_ne_top _ z _)
      (measure_mono (inter_subset_inter_left _ fun x hx ↦ hg_zero x hx))
  -- Markov
  have hgi : IntegrableOn g B :=
    (hg.1.1.integrableOn_compact_subset hzU hKc).mono_set ball_subset_closedBall
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict B)
    (ae_of_all _ hg_nn) hgi c
  have hL : c * (volume ({x | b < f x} ∩ B)).toReal ≤ ∫ x in B, ‖g x‖ := by
    have e : ∫ x in B, ‖g x‖ = ∫ x in B, g x :=
      integral_congr_ae (ae_of_all _ fun x ↦ by
        simp only [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)])
    rw [e]
    refine le_trans ?_ hMarkov
    gcongr
    rw [measureReal_def, Measure.restrict_apply' measurableSet_ball]
    exact ENNReal.toReal_mono (volume_inter_ball_ne_top _ z _)
      (measure_mono (inter_subset_inter_left _ fun x hx ↦ hg_ge x hx))
  -- the gradient
  have hDm : NullMeasurableSet D (volume.restrict B) :=
    (aemeasurable_of_memH1Loc hf hzU le_rfl).nullMeasurable measurableSet_Ioc
  have hGgi : IntegrableOn (fun x ↦ ‖Gg x‖) B :=
    ((hg.1.2.1.integrableOn_compact_subset hzU hKc).mono_set ball_subset_closedBall).norm
  have hGFi : IntegrableOn (fun x ↦ ‖GF x‖ ^ 2) B :=
    (integrableOn_norm_sq_of_memH1Loc hF hzU hKc).mono_set ball_subset_closedBall
  have hIi := integrableOn_indicator_const₀ measure_ball_lt_top.ne hDm (lam / 2)
  have hR : ∫ x in B, ‖Gg x‖ ≤ lam / 2 * (volume (D ∩ B)).toReal +
      1 / (2 * lam) * ∫ x in B, ‖GF x‖ ^ 2 := by
    calc ∫ x in B, ‖Gg x‖
        ≤ ∫ x in B, (D.indicator (fun _ ↦ lam / 2) x + ‖GF x‖ ^ 2 / (2 * lam)) :=
          setIntegral_mono hGgi (hIi.add (hGFi.div_const _)) hGg
      _ = _ := by
          rw [integral_add hIi (hGFi.div_const _),
            setIntegral_indicator_const₀ hDm, integral_div]
          ring
  have hA0 : 0 ≤ (volume ({x | b < f x} ∩ B)).toReal := ENNReal.toReal_nonneg
  have hZ0 : 0 ≤ (volume ({x | f x ≤ a} ∩ B)).toReal := ENNReal.toReal_nonneg
  have hgI0 : 0 ≤ ∫ x in B, ‖g x‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have hK0 : 0 ≤ 2 * ρ * (2 ^ d * (volume B).toReal) := by positivity
  calc c * (volume ({x | b < f x} ∩ B)).toReal * (volume ({x | f x ≤ a} ∩ B)).toReal
      ≤ (∫ x in B, ‖g x‖) * (volume ({y | g y = 0} ∩ B)).toReal :=
        mul_le_mul hL hZ hZ0 hgI0
    _ = (volume ({y | g y = 0} ∩ B)).toReal * ∫ x in B, ‖g x‖ := mul_comm _ _
    _ ≤ 2 * ρ * (2 ^ d * (volume B).toReal) * ∫ x in B, ‖Gg x‖ := hiso
    _ ≤ _ := mul_le_mul_of_nonneg_left hR hK0

/-! ### Constants -/

/-- The factor `P = 2^{d+1}` of the interior measure-shrinking step. -/
noncomputable def oscPI (d : ℕ) : ℝ := 2 ^ (d + 1)

theorem oscPI_pos : 0 < oscPI d := by unfold oscPI; positivity

/-- The parameter `τ = 8 P ω A 2ᵈ / ε₀` of the interior measure-shrinking steps. -/
noncomputable def oscTauI (d : ℕ) (CS : ℝ≥0) (C₀ : ℝ) : ℝ :=
  8 * oscPI d * unitBallVol d * oscA C₀ * 2 ^ d / degiorgiEps d CS C₀

/-- The number of interior measure-shrinking steps. -/
noncomputable def oscNI (d : ℕ) (CS : ℝ≥0) (C₀ : ℝ) : ℕ :=
  ⌈8 * oscPI d * unitBallVol d * oscTauI d CS C₀ * 2 ^ d / degiorgiEps d CS C₀⌉₊ + 1

theorem oscNI_pos (CS : ℝ≥0) (C₀ : ℝ) : 0 < oscNI d CS C₀ := Nat.succ_pos _

/-- Numerics: after `oscNI` steps the level set is small enough for the `L^∞` lemma on
`B_{ρ/2}`. -/
theorem oscillation_numeric_interior {CS : ℝ≥0} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {a V ρ : ℝ}
    (hρ : 0 ≤ ρ) (hV : V = ρ ^ d * unitBallVol d)
    (ha : a ≤ oscPI d * (oscTauI d CS C₀ * V / oscNI d CS C₀ + oscA C₀ * V / oscTauI d CS C₀)) :
    4 * a ≤ degiorgiEps d CS C₀ * (ρ / 2) ^ d := by
  set ε := degiorgiEps d CS C₀ with hε
  set w0 := unitBallVol d with hw0
  set A := oscA C₀ with hA
  set P := oscPI d with hP
  set τ := oscTauI d CS C₀ with hτ
  set n := oscNI d CS C₀ with hn
  have hε0 : 0 < ε := degiorgiEps_pos hC₀
  have hw0' : 0 < w0 := unitBallVol_pos
  have hA0 : 0 < A := by rw [hA, oscA]; linarith
  have hP0 : 0 < P := oscPI_pos
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  have hτ0 : 0 < τ := by rw [hτ, oscTauI]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast oscNI_pos CS C₀
  have hnbig : 8 * P * w0 * τ * 2 ^ d / ε ≤ n := by
    rw [hn, oscNI]; push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  have e1 : P * w0 * A / τ = ε / (8 * 2 ^ d) := by
    rw [hτ, oscTauI, ← hA, ← hw0, ← hε, ← hP]; field_simp
  have e2 : P * w0 * τ / n ≤ ε / (8 * 2 ^ d) := by
    rw [div_le_div_iff₀ hn0 (by positivity)]
    rw [div_le_iff₀ hε0] at hnbig
    linarith
  have hρd : 0 ≤ ρ ^ d := by positivity
  calc 4 * a ≤ 4 * (P * (τ * V / n + A * V / τ)) := by linarith
    _ = 4 * ρ ^ d * (P * w0 * τ / n) + 4 * ρ ^ d * (P * w0 * A / τ) := by
        rw [hV]; field_simp
    _ ≤ 4 * ρ ^ d * (ε / (8 * 2 ^ d)) + 4 * ρ ^ d * (ε / (8 * 2 ^ d)) := by
        rw [e1]; exact add_le_add (mul_le_mul_of_nonneg_left e2 (by positivity)) le_rfl
    _ = ε * (ρ / 2) ^ d := by rw [div_pow]; field_simp; ring

/-! ### Oscillation decay -/

/-- **Interior oscillation decay, main case.** If `K < M`, `f ≤ M` a.e. on `B_ρ(z)`,
`|{f ≤ K} ∩ B_{ρ/2}(z)| ≥ ½ |B_{ρ/2}(z)|` and `C₁ ρ² ≤ ((M - K) 2^{-n})²` (`n = oscNI`), then
`f ≤ M - (M - K) 2^{-(n+1)}` a.e. on `B_{ρ/4}(z)`. -/
theorem oscillation_main_interior (hd : 1 ≤ d) {CS : ℝ≥0} (hS : SobolevSupport d CS)
    {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d} (hf : MemH1Loc U f G)
    {z : E d} {ρ : ℝ} (hρ : 0 < ρ) (hzU : closedBall z ρ ⊆ U)
    {K C₀ C₁ M : ℝ} (hDG : IsDeGiorgiAt f G z ρ K C₀ C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hdens : (volume (ball z (ρ / 2))).toReal ≤
      2 * (volume ({x | f x ≤ K} ∩ ball z (ρ / 2))).toReal)
    (hM : ∀ᵐ x ∂(volume.restrict (ball z ρ)), f x ≤ M) (hKM : K < M)
    (hC₁ρ : C₁ * ρ ^ 2 ≤ ((M - K) / 2 ^ oscNI d CS C₀) ^ 2) :
    ∀ᵐ x ∂(volume.restrict (ball z (ρ / 4))),
      f x ≤ M - (M - K) / 2 ^ (oscNI d CS C₀ + 1) := by
  set n := oscNI d CS C₀ with hn
  set δ := M - K with hδ
  have hδ0 : 0 < δ := sub_pos.2 hKM
  set τ := oscTauI d CS C₀ with hτ
  set A := oscA C₀ with hA
  set P := oscPI d with hP
  have hP0 : 0 < P := oscPI_pos
  have hτ0 : 0 < τ := by
    rw [hτ, oscTauI]
    have := degiorgiEps_pos (d := d) (CS := CS) hC₀
    have := unitBallVol_pos (d := d)
    have : 0 < oscA C₀ := by rw [oscA]; linarith
    have := oscPI_pos (d := d)
    positivity
  have hp : ∀ j : ℕ, (0 : ℝ) < 2 ^ j := fun j ↦ by positivity
  set kk : ℕ → ℝ := fun j ↦ M - δ / 2 ^ j with hkk
  have hkk0 : kk 0 = K := by simp [hkk, hδ]
  have hkk_diff : ∀ j, kk (j + 1) - kk j = δ / 2 ^ j / 2 := fun j ↦ by
    simp only [hkk]; rw [pow_succ]; field_simp; ring
  have hkk_mono : Monotone kk := by
    refine monotone_nat_of_le_succ fun j ↦ ?_
    have := hkk_diff j; have : 0 < δ / 2 ^ j / 2 := by have := hp j; positivity
    linarith
  have hkK : ∀ j, K ≤ kk j := fun j ↦ hkk0 ▸ hkk_mono (Nat.zero_le j)
  have hMkk : ∀ j, M - kk j = δ / 2 ^ j := fun j ↦ by simp [hkk]
  set V := (volume (ball z ρ)).toReal with hV
  have hVeq : V = ρ ^ d * unitBallVol d := volume_ball_toReal hd z hρ.le
  set V' := (volume (ball z (ρ / 2))).toReal with hV'
  have hV'0 : 0 < V' :=
    ENNReal.toReal_pos (measure_ball_pos _ _ (by positivity)).ne' measure_ball_lt_top.ne
  have hV'V : V' ≤ V :=
    ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono (ball_subset_ball (by linarith)))
  have hKc : IsCompact (closedBall z ρ) := isCompact_closedBall _ _
  have hzU2 : closedBall z (ρ / 2) ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hzU
  set a : ℕ → ℝ := fun j ↦ (volume ({x | kk j < f x} ∩ ball z (ρ / 2))).toReal with ha
  set m : ℕ → ℝ :=
    fun j ↦ (volume ({x | kk j < f x ∧ f x ≤ kk (j + 1)} ∩ ball z (ρ / 2))).toReal with hm
  -- Caccioppoli bound on each level (as in `oscillation_main`)
  have hX : ∀ j, j ≤ n → ∫ x in ball z (ρ / 2), ‖{y | kk j < f y}.indicator G x‖ ^ 2 ≤
      A * (δ / 2 ^ j) ^ 2 / ρ ^ 2 * V := by
    intro j hj
    have hc := hDG (kk j) (hkK j) (ρ / 2) ρ (by positivity) (by linarith) le_rfl
    have hI : ∫ x in ball z ρ, (max (f x - kk j) 0) ^ 2 ≤ (δ / 2 ^ j) ^ 2 * V := by
      have hint := (integrableOn_posPart_sq hU hf hzU hKc (kk j)).mono_set
        (ball_subset_closedBall (x := z) (ε := ρ))
      calc ∫ x in ball z ρ, (max (f x - kk j) 0) ^ 2 ≤ ∫ x in ball z ρ, (δ / 2 ^ j) ^ 2 := by
            refine integral_mono_ae hint (integrableOn_const measure_ball_lt_top.ne) ?_
            filter_upwards [hM] with x hx
            have h0 : 0 ≤ max (f x - kk j) 0 := le_max_right _ _
            have h1 : max (f x - kk j) 0 ≤ δ / 2 ^ j := by
              rw [← hMkk j]; exact max_le (by linarith) (by rw [hMkk]; have := hp j; positivity)
            exact pow_le_pow_left₀ h0 h1 2
        _ = (δ / 2 ^ j) ^ 2 * V := by
            rw [setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]
    have hμ : (volume ({x | kk j < f x} ∩ ball z ρ)).toReal ≤ V :=
      ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono inter_subset_right)
    have hC₁' : C₁ ≤ (δ / 2 ^ j) ^ 2 / ρ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      refine hC₁ρ.trans ?_
      exact pow_le_pow_left₀ (div_nonneg hδ0.le (hp n).le)
        (div_le_div_of_nonneg_left hδ0.le (hp j) (pow_le_pow_right₀ (by norm_num) hj)) 2
    have hρ2 : ρ - ρ / 2 = ρ / 2 := by ring
    rw [hρ2] at hc
    have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
    calc _ ≤ C₀ / (ρ / 2) ^ 2 * (∫ x in ball z ρ, (max (f x - kk j) 0) ^ 2) +
          C₁ * (volume ({x | kk j < f x} ∩ ball z ρ)).toReal := hc
      _ ≤ C₀ / (ρ / 2) ^ 2 * ((δ / 2 ^ j) ^ 2 * V) + (δ / 2 ^ j) ^ 2 / ρ ^ 2 * V :=
          add_le_add (mul_le_mul_of_nonneg_left hI (by positivity))
            (mul_le_mul hC₁' hμ ENNReal.toReal_nonneg (by positivity))
      _ = A * (δ / 2 ^ j) ^ 2 / ρ ^ 2 * V := by rw [hA, oscA]; field_simp; ring
  -- one step
  have hstep : ∀ j, j < n → a (j + 1) ≤ P * (τ * m j + A * V / τ) := by
    intro j hj
    have hej : 0 < δ / 2 ^ j := by have := hp j; positivity
    have hlt : kk j < kk (j + 1) := by
      have := hkk_diff j; have : 0 < δ / 2 ^ j / 2 := by positivity
      linarith
    have h := measure_shrink_step_interior hU hf (ρ := ρ / 2) (by positivity) hzU2 hlt
      (lam := τ * (δ / 2 ^ j) / ρ) (by positivity)
    rw [hkk_diff] at h
    -- the density at level `kk j ≥ K`
    have hZ : V' / 2 ≤ (volume ({x | f x ≤ kk j} ∩ ball z (ρ / 2))).toReal := by
      have : (volume ({x | f x ≤ K} ∩ ball z (ρ / 2))).toReal ≤
          (volume ({x | f x ≤ kk j} ∩ ball z (ρ / 2))).toReal :=
        ENNReal.toReal_mono (volume_inter_ball_ne_top _ z _)
          (measure_mono (inter_subset_inter_left _ fun x hx ↦ le_trans hx (hkK j)))
      linarith
    set Z := (volume ({x | f x ≤ kk j} ∩ ball z (ρ / 2))).toReal with hZdef
    set T := (τ * (δ / 2 ^ j) / ρ) / 2 * m j +
      1 / (2 * (τ * (δ / 2 ^ j) / ρ)) *
        ∫ x in ball z (ρ / 2), ‖{y | kk j < f y}.indicator G x‖ ^ 2 with hT
    have hT0 : 0 ≤ T := by
      have : 0 ≤ ∫ x in ball z (ρ / 2), ‖{y | kk j < f y}.indicator G x‖ ^ 2 :=
        integral_nonneg fun _ ↦ sq_nonneg _
      have : 0 ≤ m j := ENNReal.toReal_nonneg
      have hl : 0 < τ * (δ / 2 ^ j) / ρ := div_pos (mul_pos hτ0 hej) hρ
      exact add_nonneg (mul_nonneg (half_pos hl).le ‹_›)
        (mul_nonneg (one_div_pos.2 (mul_pos two_pos hl)).le ‹_›)
    have ha0 : 0 ≤ a (j + 1) := ENNReal.toReal_nonneg
    -- divide by `|B_{ρ/2}| / 2`
    have h' : δ / 2 ^ j / 2 * (a (j + 1) / (4 * P)) ≤ ρ / 4 * T := by
      have h1 : δ / 2 ^ j / 2 * a (j + 1) * (V' / 2) ≤ 2 * (ρ / 2) * (2 ^ d * V') * T :=
        le_trans (mul_le_mul_of_nonneg_left hZ (mul_nonneg (by positivity) ha0)) h
      have h2 : δ / 2 ^ j / 2 * a (j + 1) ≤ 2 ^ (d + 1) * ρ * T := by
        have e : 2 * (ρ / 2) * (2 ^ d * V') * T = (2 ^ (d + 1) * ρ * T) * (V' / 2) := by
          rw [pow_succ]; ring
        rw [e] at h1
        exact le_of_mul_le_mul_right h1 (by positivity)
      rw [hP, oscPI]
      have e2 : δ / 2 ^ j / 2 * (a (j + 1) / (4 * 2 ^ (d + 1))) =
          (δ / 2 ^ j / 2 * a (j + 1)) / (4 * 2 ^ (d + 1)) := by ring
      rw [e2, div_le_iff₀ (by positivity)]
      exact h2.trans_eq (by ring)
    have := shrink_algebra hej hρ hτ0 (hX j hj.le) h'
    rw [div_le_iff₀ (by positivity)] at this
    exact this.trans_eq (by ring)
  -- summation
  have ha_mono : ∀ j, j < n → a n ≤ a (j + 1) := by
    intro j hj
    refine ENNReal.toReal_mono (volume_inter_ball_ne_top _ z _) (measure_mono ?_)
    exact inter_subset_inter_left _ fun x hx ↦ lt_of_le_of_lt (hkk_mono (by omega : j + 1 ≤ n)) hx
  have hmsum : ∑ j ∈ Finset.range n, m j ≤ V :=
    (sum_measure_slab_le measurableSet_ball measure_ball_lt_top.ne
      (aemeasurable_of_memH1Loc hf hzU (by linarith : ρ / 2 ≤ ρ)) hkk_mono n).trans hV'V
  have hn0 : (0 : ℝ) < n := by exact_mod_cast oscNI_pos CS C₀
  have han : a n ≤ P * (τ * V / n + A * V / τ) := by
    have h1 : (n : ℝ) * a n ≤ ∑ j ∈ Finset.range n, P * (τ * m j + A * V / τ) := by
      calc (n : ℝ) * a n = ∑ j ∈ Finset.range n, a n := by simp
        _ ≤ ∑ j ∈ Finset.range n, a (j + 1) :=
            Finset.sum_le_sum fun j hj ↦ ha_mono j (Finset.mem_range.1 hj)
        _ ≤ _ := Finset.sum_le_sum fun j hj ↦ hstep j (Finset.mem_range.1 hj)
    have h2 : ∑ j ∈ Finset.range n, P * (τ * m j + A * V / τ) =
        P * (τ * ∑ j ∈ Finset.range n, m j + n * (A * V / τ)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]; simp
    rw [h2] at h1
    have h3 : (n : ℝ) * a n ≤ P * (τ * V + n * (A * V / τ)) := h1.trans
      (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hmsum hτ0.le) le_rfl)
        hP0.le)
    have e : P * (τ * V / n + A * V / τ) = P * (τ * V + n * (A * V / τ)) / n := by
      rw [mul_div_assoc P, add_div, mul_div_cancel_left₀ _ hn0.ne']
    rw [e, le_div_iff₀ hn0]; linarith
  have h4 := oscillation_numeric_interior hC₀ hρ.le hVeq han
  -- the `L²` smallness on `B_{ρ/2}`
  set H := δ / 2 ^ (n + 1) with hH
  have hH0 : 0 < H := by have := hp (n + 1); positivity
  have hsmall : ∫ x in ball z (ρ / 2), (max (f x - kk n) 0) ^ 2 ≤
      degiorgiEps d CS C₀ * H ^ 2 * (ρ / 2) ^ d := by
    have hAm : NullMeasurableSet {x | kk n < f x} (volume.restrict (ball z (ρ / 2))) :=
      (aemeasurable_of_memH1Loc hf hzU (by linarith : ρ / 2 ≤ ρ)).nullMeasurable
        measurableSet_Ioi
    have hint := (integrableOn_posPart_sq hU hf hzU hKc (kk n)).mono_set
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ ρ)))
    have hM2 : ∀ᵐ x ∂(volume.restrict (ball z (ρ / 2))), f x ≤ M :=
      ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hM
    calc ∫ x in ball z (ρ / 2), (max (f x - kk n) 0) ^ 2
        ≤ ∫ x in ball z (ρ / 2), {x | kk n < f x}.indicator (fun _ ↦ (δ / 2 ^ n) ^ 2) x := by
          refine integral_mono_ae hint
            (integrableOn_indicator_const₀ measure_ball_lt_top.ne hAm _) ?_
          filter_upwards [hM2] with x hx
          by_cases hxk : kk n < f x
          · rw [indicator_of_mem (show x ∈ {x | kk n < f x} from hxk)]
            have h1 : max (f x - kk n) 0 ≤ δ / 2 ^ n := by
              rw [← hMkk n]; exact max_le (by linarith) (by rw [hMkk]; have := hp n; positivity)
            exact pow_le_pow_left₀ (le_max_right _ _) h1 2
          · rw [indicator_of_notMem (show x ∉ {x | kk n < f x} from hxk),
              max_eq_right (by linarith [not_lt.1 hxk])]
            norm_num
      _ = (δ / 2 ^ n) ^ 2 * a n := setIntegral_indicator_const₀ hAm _
      _ = H ^ 2 * (4 * a n) := by rw [hH, pow_succ]; ring
      _ ≤ H ^ 2 * (degiorgiEps d CS C₀ * (ρ / 2) ^ d) := mul_le_mul_of_nonneg_left h4 (sq_nonneg H)
      _ = _ := by ring
  have hC₁2 : C₁ * (ρ / 2) ^ 2 ≤ H ^ 2 := by
    have : H = δ / 2 ^ n / 2 := by rw [hH, pow_succ]; field_simp
    rw [this]
    have e1 : C₁ * (ρ / 2) ^ 2 = C₁ * ρ ^ 2 / 4 := by ring
    have e2 : (δ / 2 ^ n / 2) ^ 2 = (δ / 2 ^ n) ^ 2 / 4 := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right hC₁ρ (by norm_num)
  have hL := degiorgi_linfty hd hU hf (ρ := ρ / 2) (by positivity) (hDG.mono (by linarith))
    hC₀ hC₁ hzU2 hS (hkK n) hH0 hC₁2 hsmall
  have e4 : ρ / 2 / 2 = ρ / 4 := by ring
  rw [e4] at hL
  filter_upwards [hL] with x hx
  have : kk n + H = M - δ / 2 ^ (n + 1) := by
    simp only [hkk, hH]; rw [pow_succ]; field_simp; ring
  linarith

/-- **Interior oscillation decay.** With `n = oscNI d CS C₀`, under the density hypothesis
`|{f ≤ K} ∩ B_{ρ/2}(z)| ≥ ½ |B_{ρ/2}(z)|`,
`f ≤ K + (1 - 2^{-(n+1)}) (M - K) + 2ⁿ √C₁ ρ` a.e. on `B_{ρ/4}(z)`. -/
theorem oscillation_decay_interior (hd : 1 ≤ d) {CS : ℝ≥0} (hS : SobolevSupport d CS)
    {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d} (hf : MemH1Loc U f G)
    {z : E d} {ρ : ℝ} (hρ : 0 < ρ) (hzU : closedBall z ρ ⊆ U)
    {K C₀ C₁ M : ℝ} (hDG : IsDeGiorgiAt f G z ρ K C₀ C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hdens : (volume (ball z (ρ / 2))).toReal ≤
      2 * (volume ({x | f x ≤ K} ∩ ball z (ρ / 2))).toReal)
    (hM : ∀ᵐ x ∂(volume.restrict (ball z ρ)), f x ≤ M) :
    ∀ᵐ x ∂(volume.restrict (ball z (ρ / 4))), f x ≤
      K + (1 - 1 / 2 ^ (oscNI d CS C₀ + 1)) * (M - K) + 2 ^ oscNI d CS C₀ * √C₁ * ρ := by
  set n := oscNI d CS C₀ with hn
  have hp : ∀ j : ℕ, (0 : ℝ) < 2 ^ j := fun j ↦ by positivity
  have hM4 : ∀ᵐ x ∂(volume.restrict (ball z (ρ / 4))), f x ≤ M :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hM
  have hΛ : 0 ≤ 2 ^ n * √C₁ * ρ := by positivity
  have hlam : 1 / (2 : ℝ) ^ (n + 1) ≤ 1 := by
    rw [div_le_one (hp _)]; exact one_le_pow₀ (by norm_num)
  rcases le_or_gt M K with hMK | hKM
  · filter_upwards [hM4] with x hx
    have := mul_nonneg (show (0 : ℝ) ≤ 1 / 2 ^ (n + 1) by have := hp (n + 1); positivity)
      (sub_nonneg.2 hMK)
    linarith
  by_cases hC : C₁ * ρ ^ 2 ≤ ((M - K) / 2 ^ n) ^ 2
  · filter_upwards [oscillation_main_interior hd hS hU hf hρ hzU hDG hC₀ hC₁ hdens hM hKM hC]
      with x hx
    have : M - (M - K) / 2 ^ (n + 1) = K + (1 - 1 / 2 ^ (n + 1)) * (M - K) := by ring
    linarith
  · have h1 : (M - K) / 2 ^ n < √C₁ * ρ := by
      have hpos : 0 < (M - K) / 2 ^ n := by have := hp n; have := sub_pos.2 hKM; positivity
      have h2 : ((M - K) / 2 ^ n) ^ 2 < (√C₁ * ρ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC₁]; linarith [not_le.1 hC]
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
    have h3 : M - K < 2 ^ n * √C₁ * ρ := by
      rw [div_lt_iff₀ (hp n)] at h1; linarith
    filter_upwards [hM4] with x hx
    have h4 : 0 ≤ 1 / (2 : ℝ) ^ (n + 1) * (M - K) := by
      have := hp (n + 1); have := sub_pos.2 hKM; positivity
    linarith [mul_le_mul_of_nonneg_right hlam (sub_pos.2 hKM).le]

/-! ### One two-sided step, and the iteration -/

/-- One of `{f ≤ k}` and `{f ≥ k}` fills at least half of a ball. -/
theorem half_measure_or (f : E d → ℝ) (y : E d) (r k : ℝ) :
    (volume (ball y r)).toReal ≤ 2 * (volume ({x | f x ≤ k} ∩ ball y r)).toReal ∨
      (volume (ball y r)).toReal ≤ 2 * (volume ({x | -f x ≤ -k} ∩ ball y r)).toReal := by
  have hsub : ball y r ⊆ ({x | f x ≤ k} ∩ ball y r) ∪ ({x | -f x ≤ -k} ∩ ball y r) := by
    intro x hx
    rcases le_total (f x) k with h | h
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨neg_le_neg h, hx⟩
  have h1 : (volume (ball y r)).toReal ≤ (volume ({x | f x ≤ k} ∩ ball y r)).toReal +
      (volume ({x | -f x ≤ -k} ∩ ball y r)).toReal := by
    rw [← ENNReal.toReal_add (volume_inter_ball_ne_top _ y r) (volume_inter_ball_ne_top _ y r)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨volume_inter_ball_ne_top _ y r,
      volume_inter_ball_ne_top _ y r⟩) ((measure_mono hsub).trans (measure_union_le _ _))
  rcases le_total (volume ({x | f x ≤ k} ∩ ball y r)).toReal
    (volume ({x | -f x ≤ -k} ∩ ball y r)).toReal with h | h
  · right; linarith
  · left; linarith

/-- An a.e. two-sided bound on a ball of positive radius forces `m ≤ M`. -/
theorem le_of_ae_bounds {f : E d → ℝ} {y : E d} {ρ : ℝ} (hρ : 0 < ρ) {m M : ℝ}
    (h : ∀ᵐ x ∂(volume.restrict (ball y ρ)), m ≤ f x ∧ f x ≤ M) : m ≤ M := by
  have : (ae (volume.restrict (ball y ρ))).NeBot := by
    rw [ae_neBot, Ne, Measure.restrict_eq_zero]
    exact (measure_ball_pos volume y hρ).ne'
  obtain ⟨x, hx⟩ := h.exists
  exact hx.1.trans hx.2

/-- **One two-sided oscillation step with the obstacle alternative.** Let `m ≤ f ≤ M` a.e. on
`B_R(y)`, `k₀ = (m + M)/2`. Suppose `f ∈ DG⁺` at levels `≥ k₀` or `f ≥ k₀ - β` a.e. on `B_R(y)`,
and `-f ∈ DG⁺` at levels `≥ -k₀` or `f ≤ k₀ + β` a.e. on `B_R(y)`. Then there are bounds
`m ≤ m' ≤ f ≤ M' ≤ M` a.e. on `B_{R/4}(y)` with
`M' - m' ≤ (1 - 2^{-(n+2)}) (M - m) + 2ⁿ √C₁ R + β`, `n = oscNI d CS C₀`. -/
theorem osc_step_interior (hd : 1 ≤ d) {CS : ℝ≥0} (hS : SobolevSupport d CS)
    {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d} (hf : MemH1Loc U f G)
    {y : E d} {R : ℝ} (hR : 0 < R) (hyU : closedBall y R ⊆ U)
    {C₀ C₁ β m M : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hβ : 0 ≤ β) (hmM : m ≤ M)
    (hb : ∀ᵐ x ∂(volume.restrict (ball y R)), m ≤ f x ∧ f x ≤ M)
    (hup : IsDeGiorgiAt f G y R ((m + M) / 2) C₀ C₁ ∨
      ∀ᵐ x ∂(volume.restrict (ball y R)), (m + M) / 2 - β ≤ f x)
    (hdn : IsDeGiorgiAt (fun x ↦ -f x) (fun x ↦ -G x) y R (-((m + M) / 2)) C₀ C₁ ∨
      ∀ᵐ x ∂(volume.restrict (ball y R)), f x ≤ (m + M) / 2 + β) :
    ∃ m' M', m ≤ m' ∧ M' ≤ M ∧
      (∀ᵐ x ∂(volume.restrict (ball y (R / 4))), m' ≤ f x ∧ f x ≤ M') ∧
      M' - m' ≤ (1 - 1 / 2 ^ (oscNI d CS C₀ + 2)) * (M - m) + 2 ^ oscNI d CS C₀ * √C₁ * R + β := by
  set n := oscNI d CS C₀ with hn
  set k₀ := (m + M) / 2 with hk₀
  set lam : ℝ := 1 - 1 / 2 ^ (n + 1) with hlam
  set Λ : ℝ := 2 ^ n * √C₁ with hΛ
  have hΛR : 0 ≤ Λ * R := by positivity
  have hp : (0 : ℝ) < 2 ^ (n + 2) := by positivity
  have e1 : (1 + lam) / 2 = 1 - 1 / 2 ^ (n + 2) := by
    rw [hlam, pow_succ 2 (n + 1)]; field_simp; ring
  have hθ : 1 / (2 : ℝ) ^ (n + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hp (by norm_num)]
    simp only [one_mul]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmM' : 0 ≤ M - m := sub_nonneg.2 hmM
  have hθ' : (M - m) / 2 ≤ (1 - 1 / 2 ^ (n + 2)) * (M - m) := by
    linarith [mul_le_mul_of_nonneg_right hθ hmM']
  have hb4 : ∀ᵐ x ∂(volume.restrict (ball y (R / 4))), m ≤ f x ∧ f x ≤ M :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hb
  have hsub : ball y (R / 4) ⊆ ball y R := ball_subset_ball (by linarith)
  rcases half_measure_or f y (R / 2) k₀ with hd1 | hd2
  · rcases hup with hDG | hlow
    · have h := oscillation_decay_interior hd hS hU hf hR hyU hDG hC₀ hC₁ hd1
        (hb.mono fun x hx ↦ hx.2)
      refine ⟨m, min M (k₀ + lam * (M - k₀) + Λ * R), le_rfl, min_le_left _ _, ?_, ?_⟩
      · filter_upwards [hb4, h] with x hx1 hx2
        exact ⟨hx1.1, le_min hx1.2 (by rw [hlam, hΛ]; exact hx2)⟩
      · have : min M (k₀ + lam * (M - k₀) + Λ * R) ≤ k₀ + lam * (M - k₀) + Λ * R :=
          min_le_right _ _
        have e2 : k₀ + lam * (M - k₀) - m = (1 + lam) / 2 * (M - m) := by rw [hk₀]; ring
        rw [e1] at e2
        linarith
    · refine ⟨max m (k₀ - β), M, le_max_left _ _, le_rfl, ?_, ?_⟩
      · filter_upwards [hb4, ae_restrict_of_ae_restrict_of_subset hsub hlow] with x hx1 hx2
        exact ⟨max_le hx1.1 hx2, hx1.2⟩
      · have : k₀ - β ≤ max m (k₀ - β) := le_max_right _ _
        have e2 : M - k₀ = (M - m) / 2 := by rw [hk₀]; ring
        linarith
  · rcases hdn with hDG | hupp
    · have h := oscillation_decay_interior hd hS hU hf.neg hR hyU hDG hC₀ hC₁ hd2
        (M := -m) (hb.mono fun x hx ↦ neg_le_neg hx.1)
      refine ⟨max m (k₀ - lam * (k₀ - m) - Λ * R), M, le_max_left _ _, le_rfl, ?_, ?_⟩
      · filter_upwards [hb4, h] with x hx1 hx2
        refine ⟨max_le hx1.1 ?_, hx1.2⟩
        rw [hlam, hΛ] at *
        linarith
      · have : k₀ - lam * (k₀ - m) - Λ * R ≤ max m (k₀ - lam * (k₀ - m) - Λ * R) :=
          le_max_right _ _
        have e2 : M - (k₀ - lam * (k₀ - m)) = (1 + lam) / 2 * (M - m) := by rw [hk₀]; ring
        rw [e1] at e2
        linarith
    · refine ⟨m, min M (k₀ + β), le_rfl, min_le_left _ _, ?_, ?_⟩
      · filter_upwards [hb4, ae_restrict_of_ae_restrict_of_subset hsub hupp] with x hx1 hx2
        exact ⟨hx1.1, le_min hx1.2 hx2⟩
      · have : min M (k₀ + β) ≤ k₀ + β := min_le_right _ _
        have e2 : k₀ - m = (M - m) / 2 := by rw [hk₀]; ring
        linarith

/-- The essential oscillation of `f` on small balls centred at `y` tends to zero. -/
def EssOscVanishes (f : E d → ℝ) (y : E d) : Prop :=
  ∀ ε > 0, ∃ ρ > 0, ∃ m M : ℝ, M - m ≤ ε ∧
    ∀ᵐ x ∂(volume.restrict (ball y ρ)), m ≤ f x ∧ f x ≤ M

/-- **Iteration.** A one-step decay `ω(R/4) ≤ (1 - θ) ω(R) + C R` for all `R ≤ R₀`, under an
invariant `P` on the lower bound, gives `EssOscVanishes f y`. -/
theorem essOscVanishes_of_step {f : E d → ℝ} {y : E d} {R₀ θ C : ℝ} (hR₀ : 0 < R₀)
    (hθ0 : 0 < θ) (hθ : θ ≤ 1 / 2) (hC : 0 ≤ C) (P : ℝ → Prop) {m₀ M₀ : ℝ} (hP₀ : P m₀)
    (h₀ : ∀ᵐ x ∂(volume.restrict (ball y R₀)), m₀ ≤ f x ∧ f x ≤ M₀)
    (hstep : ∀ R, 0 < R → R ≤ R₀ → ∀ m M, P m →
      (∀ᵐ x ∂(volume.restrict (ball y R)), m ≤ f x ∧ f x ≤ M) →
      ∃ m' M', P m' ∧ (∀ᵐ x ∂(volume.restrict (ball y (R / 4))), m' ≤ f x ∧ f x ≤ M') ∧
        M' - m' ≤ (1 - θ) * (M - m) + C * R) :
    EssOscVanishes f y := by
  set q : ℝ := 1 / 4 with hq
  set e : ℕ → ℝ := fun i ↦ Nat.rec (motive := fun _ ↦ ℝ) (M₀ - m₀)
    (fun j ej ↦ (1 - θ) * ej + (C * R₀) * q ^ j) i with he
  have he0 : e 0 = M₀ - m₀ := rfl
  have hesucc : ∀ i, e (i + 1) = (1 - θ) * e i + (C * R₀) * q ^ i := fun i ↦ rfl
  have hq0 : 0 < q := by norm_num [hq]
  have hRi : ∀ i, 0 < R₀ * q ^ i := fun i ↦ by positivity
  have hRle : ∀ i, R₀ * q ^ i ≤ R₀ := fun i ↦
    mul_le_of_le_one_right hR₀.le (pow_le_one₀ hq0.le (by norm_num [hq]))
  have hind : ∀ i, ∃ m M, P m ∧ (∀ᵐ x ∂(volume.restrict (ball y (R₀ * q ^ i))),
      m ≤ f x ∧ f x ≤ M) ∧ M - m ≤ e i := by
    intro i
    induction i with
    | zero => exact ⟨m₀, M₀, hP₀, by simpa using h₀, le_of_eq he0.symm⟩
    | succ i ih =>
      obtain ⟨m, M, hPm, hb, hMm⟩ := ih
      obtain ⟨m', M', hPm', hb', hM'⟩ := hstep _ (hRi i) (hRle i) m M hPm hb
      refine ⟨m', M', hPm', ?_, ?_⟩
      · have e1 : R₀ * q ^ (i + 1) = R₀ * q ^ i / 4 := by rw [pow_succ, hq]; ring
        rw [e1]; exact hb'
      · rw [hesucc]
        have h1 : (1 - θ) * (M - m) ≤ (1 - θ) * e i := mul_le_mul_of_nonneg_left hMm (by linarith)
        have h2 : C * (R₀ * q ^ i) = (C * R₀) * q ^ i := by ring
        linarith
  have hbound := le_of_recursion (e := e) (lam := 1 - θ) (q := q) (Bc := C * R₀) (by linarith)
    (by linarith) hq0.le (by rw [hq]; linarith) (by positivity)
    (fun i ↦ le_of_eq (hesucc i))
  intro ε hε
  set μ := (1 + (1 - θ)) / 2 with hμ
  set E := |e 0| + 2 * (C * R₀) / (1 - (1 - θ)) with hE
  have hE0 : 0 ≤ E := by
    have : 0 < 1 - (1 - θ) := by linarith
    positivity
  obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (E + 1) by positivity)
    (show μ < 1 by rw [hμ]; linarith)
  obtain ⟨m, M, -, hb, hMm⟩ := hind i
  refine ⟨R₀ * q ^ i, hRi i, m, M, ?_, hb⟩
  have h1 := hbound i
  have hμ0 : 0 ≤ μ ^ i := pow_nonneg (by rw [hμ]; linarith) _
  have h3 : μ ^ i * (E + 1) < ε := by rwa [lt_div_iff₀ (by positivity)] at hi
  linarith

end EllipticBernoulli
