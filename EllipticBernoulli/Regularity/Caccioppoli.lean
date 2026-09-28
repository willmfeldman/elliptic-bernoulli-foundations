/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.Lattice
public import EllipticBernoulli.Regularity.Iteration
public import EllipticBernoulli.Regularity.Cutoff

/-!
# Caccioppoli inequalities and De Giorgi classes

* `integral_norm_sq_le_of_energyJ_le`: from `J_Q(w; B) ≤ J_Q(v; B)` and
  `{v > 0} ⊆ {w > 0} ∪ A` to `∫_B |∇w|² ≤ ∫_B |∇v|² + sup Q² |A|`.
* `caccioppoli_of_step`: hole filling. If `F ≥ 0` satisfies the one-step inequality
  `∫_{B_t} |∇F|² ≤ ∫_{B_t} |(1 - η)∇F - F∇η|² + E |{F > 0} ∩ B_t|` for all cutoffs `η`
  supported in `B_t`, then
  `∫_{B_ρ} |∇F|² ≤ C (R - ρ)⁻² ∫_{B_R} F² + 128 E |{F > 0} ∩ B_R|`
  (via the iteration lemma).
* `IsDeGiorgiAt`: the (boundary) De Giorgi class `DG⁺` of Giaquinta–Giusti on balls centred at
  a fixed point, for all levels above a threshold.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### From the energy inequality to a gradient inequality -/

/-- If `J_Q(w; B) ≤ J_Q(v; B)`, `Q² ≤ Cq` on `B` and `{v > 0} ⊆ {w > 0} ∪ A`, then
`∫_B |∇w|² ≤ ∫_B |∇v|² + Cq |A|`. -/
theorem integral_norm_sq_le_of_energyJ_le {B A : Set (E d)} (hB : MeasurableSet B)
    (hBf : volume B ≠ ⊤) (hA : volume A ≠ ⊤) {Q w v : E d → ℝ} {Gw Gv : E d → E d} {Cq : ℝ}
    (hCq : 0 ≤ Cq) (hQ : ∀ x ∈ B, Q x ^ 2 ≤ Cq)
    (hw : IntegrableOn (fun x ↦ ‖Gw x‖ ^ 2) B) (hv : IntegrableOn (fun x ↦ ‖Gv x‖ ^ 2) B)
    (hJ : energyJ B Q w Gw ≤ energyJ B Q v Gv) (hpos : posSet v B ⊆ posSet w B ∪ A) :
    ∫ x in B, ‖Gw x‖ ^ 2 ≤ (∫ x in B, ‖Gv x‖ ^ 2) + Cq * (volume A).toReal := by
  set Yw : ℝ≥0∞ := ∫⁻ x in B, ENNReal.ofReal (Q x ^ 2 * (posSet w B).indicator 1 x) with hYw
  set Yv : ℝ≥0∞ := ∫⁻ x in B, ENNReal.ofReal (Q x ^ 2 * (posSet v B).indicator 1 x) with hYv
  set Iw : ℝ≥0∞ := ∫⁻ x in B, ENNReal.ofReal (‖Gw x‖ ^ 2) with hIw
  set Iv : ℝ≥0∞ := ∫⁻ x in B, ENNReal.ofReal (‖Gv x‖ ^ 2) with hIv
  have hind : ∀ (S : Set (E d)) x, 0 ≤ Q x ^ 2 * S.indicator (1 : E d → ℝ) x := fun S x ↦
    mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have eJ : ∀ (f : E d → ℝ) (G : E d → E d), IntegrableOn (fun x ↦ ‖G x‖ ^ 2) B →
      energyJ B Q f G = (∫⁻ x in B, ENNReal.ofReal (‖G x‖ ^ 2)) +
        ∫⁻ x in B, ENNReal.ofReal (Q x ^ 2 * (posSet f B).indicator 1 x) := by
    intro f G hG
    unfold energyJ
    rw [← lintegral_add_left' hG.1.aemeasurable.ennreal_ofReal]
    refine lintegral_congr fun x ↦ ?_
    rw [ENNReal.ofReal_add (sq_nonneg _) (hind _ x)]
  set A' := toMeasurable volume A with hA'
  have hA'm : MeasurableSet A' := measurableSet_toMeasurable _ _
  have hYv : Yv ≤ Yw + ENNReal.ofReal Cq * volume A := by
    calc Yv ≤ ∫⁻ x in B, (ENNReal.ofReal (Q x ^ 2 * (posSet w B).indicator 1 x) +
          A'.indicator (fun _ ↦ ENNReal.ofReal Cq) x) := by
          refine lintegral_mono_ae ((ae_restrict_iff' hB).2 (Eventually.of_forall fun x hx ↦ ?_))
          by_cases hv' : x ∈ posSet v B
          · rcases hpos hv' with hw' | hA''
            · rw [indicator_of_mem hv', indicator_of_mem hw']
              exact le_self_add
            · rw [indicator_of_mem hv', indicator_of_mem (subset_toMeasurable _ _ hA''),
                Pi.one_apply, mul_one]
              exact le_add_left (ENNReal.ofReal_le_ofReal (hQ x hx))
          · rw [indicator_of_notMem hv', mul_zero, ENNReal.ofReal_zero]
            exact bot_le
      _ = Yw + ∫⁻ x in B, A'.indicator (fun _ ↦ ENNReal.ofReal Cq) x := by
          rw [lintegral_add_right' _ (measurable_const.indicator hA'm).aemeasurable]
      _ ≤ Yw + ENNReal.ofReal Cq * volume A := by
          gcongr
          rw [lintegral_indicator_const hA'm, Measure.restrict_apply hA'm]
          exact mul_le_mul' le_rfl ((measure_mono inter_subset_left).trans
            (measure_toMeasurable A).le)
  have hYw_fin : Yw ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in B, ENNReal.ofReal Cq) ?_ ?_
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBf
    · refine lintegral_mono_ae ((ae_restrict_iff' hB).2 (Eventually.of_forall fun x hx ↦ ?_))
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hx' : x ∈ posSet w B
      · rw [indicator_of_mem hx', Pi.one_apply, mul_one]; exact hQ x hx
      · rw [indicator_of_notMem hx', mul_zero]; exact hCq
  have hmain : Iw ≤ Iv + ENNReal.ofReal Cq * volume A := by
    have h1 : Iw + Yw ≤ Iv + ENNReal.ofReal Cq * volume A + Yw := by
      calc Iw + Yw = energyJ B Q w Gw := (eJ w Gw hw).symm
        _ ≤ energyJ B Q v Gv := hJ
        _ = Iv + Yv := eJ v Gv hv
        _ ≤ Iv + (Yw + ENNReal.ofReal Cq * volume A) := by gcongr
        _ = Iv + ENNReal.ofReal Cq * volume A + Yw := by ring
    exact (ENNReal.add_le_add_iff_right hYw_fin).1 h1
  have eIw : Iw = ENNReal.ofReal (∫ x in B, ‖Gw x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall fun x ↦ sq_nonneg _)).symm
  have eIv : Iv = ENNReal.ofReal (∫ x in B, ‖Gv x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hv (Eventually.of_forall fun x ↦ sq_nonneg _)).symm
  have eA : ENNReal.ofReal Cq * volume A = ENNReal.ofReal (Cq * (volume A).toReal) := by
    rw [ENNReal.ofReal_mul hCq, ENNReal.ofReal_toReal hA]
  have hIv0 : 0 ≤ ∫ x in B, ‖Gv x‖ ^ 2 := setIntegral_nonneg hB fun x _ ↦ sq_nonneg _
  have hA0 : 0 ≤ Cq * (volume A).toReal := mul_nonneg hCq ENNReal.toReal_nonneg
  rw [eIw, eIv, eA, ← ENNReal.ofReal_add hIv0 hA0] at hmain
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hIv0 hA0)).1 hmain

/-! ### Hole filling -/

theorem norm_sub_sq_le_two (a b : E d) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_sub_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]

theorem volume_inter_ball_ne_top (S : Set (E d)) (z : E d) (r : ℝ) :
    volume (S ∩ ball z r) ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono inter_subset_right)

/-- **Caccioppoli inequality from the one-step inequality (hole filling).** If `F` satisfies
`∫_{B_t} |∇F|² ≤ ∫_{B_t} |(1 - η)∇F - F∇η|² + E |{F > 0} ∩ B_t|` for every smooth `0 ≤ η ≤ 1`
vanishing with its gradient off `B_t`, then for `0 < ρ < R ≤ R₀`
`∫_{B_ρ} |∇F|² ≤ 256 C² (R - ρ)⁻² ∫_{B_R} F² + 128 E |{F > 0} ∩ B_R|`,
`C = cutoffConst`. -/
theorem caccioppoli_of_step {F : E d → ℝ} {GF : E d → E d} {z : E d} {R₀ Er : ℝ} (hEr : 0 ≤ Er)
    (hGF : IntegrableOn (fun x ↦ ‖GF x‖ ^ 2) (ball z R₀))
    (hF : IntegrableOn (fun x ↦ F x ^ 2) (ball z R₀))
    (hstep : ∀ t, 0 < t → t ≤ R₀ → ∀ η : E d → ℝ, ContDiff ℝ ∞ η →
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) → (∀ x ∉ ball z t, η x = 0 ∧ ∇ η x = 0) →
      ∫ x in ball z t, ‖GF x‖ ^ 2 ≤ (∫ x in ball z t, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2) +
        Er * (volume ({x | 0 < F x} ∩ ball z t)).toReal)
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (hR : R ≤ R₀) :
    ∫ x in ball z ρ, ‖GF x‖ ^ 2 ≤ 256 * cutoffConst ^ 2 / (R - ρ) ^ 2 *
      (∫ x in ball z R, F x ^ 2) + 128 * Er * (volume ({x | 0 < F x} ∩ ball z R)).toReal := by
  set Φ : ℝ → ℝ := fun σ ↦ ∫ x in ball z σ, ‖GF x‖ ^ 2 with hΦ
  set S := ∫ x in ball z R, F x ^ 2 with hS
  set V := (volume ({x | 0 < F x} ∩ ball z R)).toReal with hV
  set C := cutoffConst with hC
  have hC0 : 0 < C := cutoffConst_pos
  have hGFσ : ∀ σ ≤ R₀, IntegrableOn (fun x ↦ ‖GF x‖ ^ 2) (ball z σ) := fun σ hσ ↦
    hGF.mono_set (ball_subset_ball hσ)
  have hFσ : ∀ σ ≤ R₀, IntegrableOn (fun x ↦ F x ^ 2) (ball z σ) := fun σ hσ ↦
    hF.mono_set (ball_subset_ball hσ)
  have hΦmono : ∀ σ₁ σ₂, σ₁ ≤ σ₂ → σ₂ ≤ R₀ → Φ σ₁ ≤ Φ σ₂ := fun σ₁ σ₂ h h2 ↦
    setIntegral_mono_set (hGFσ σ₂ h2) (ae_of_all _ fun x ↦ sq_nonneg _)
      (ball_subset_ball h).eventuallyLE
  have hS0 : 0 ≤ S := setIntegral_nonneg measurableSet_ball fun x _ ↦ sq_nonneg _
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  have hVt : ∀ t ≤ R, (volume ({x | 0 < F x} ∩ ball z t)).toReal ≤ V := fun t ht ↦
    ENNReal.toReal_mono (volume_inter_ball_ne_top _ z R)
      (measure_mono (inter_subset_inter_right _ (ball_subset_ball ht)))
  have key : ∀ s t, ρ ≤ s → s < t → t < R →
      Φ s ≤ 1 / 2 * Φ t + C ^ 2 * S / (t - s) ^ 2 + Er * V / 2 := by
    intro s t hs hst htR
    have ht0 : 0 < t := by linarith
    have htR₀ : t ≤ R₀ := by linarith
    have hts : 0 < t - s := by linarith
    obtain ⟨η, hη, hη01, hη1, hη0, -, -, hηg⟩ := exists_cutoff z (by linarith : 0 ≤ s) hst
    have h1 := hstep t ht0 htR₀ η hη hη01 hη0
    set g : E d → ℝ := fun x ↦ 2 * ((closedBall z s)ᶜ.indicator (fun x ↦ ‖GF x‖ ^ 2) x) +
      2 * (C / (t - s)) ^ 2 * F x ^ 2 with hg
    have hpt : ∀ x, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2 ≤ g x := by
      intro x
      refine (norm_sub_sq_le_two _ _).trans ?_
      have ha : ‖(1 - η x) • GF x‖ ^ 2 ≤ (closedBall z s)ᶜ.indicator (fun x ↦ ‖GF x‖ ^ 2) x := by
        by_cases hx : x ∈ closedBall z s
        · rw [hη1 x hx, sub_self, zero_smul, norm_zero,
            indicator_of_notMem (show x ∉ (closedBall z s)ᶜ from fun h ↦ h hx)]
          norm_num
        · rw [indicator_of_mem (show x ∈ (closedBall z s)ᶜ from hx), norm_smul, mul_pow]
          have h01 := hη01 x
          have : ‖1 - η x‖ ^ 2 ≤ 1 := by
            rw [Real.norm_eq_abs, sq_abs]
            exact pow_le_one₀ (by linarith [h01.2]) (by linarith [h01.1])
          exact (mul_le_mul_of_nonneg_right this (sq_nonneg _)).trans_eq (one_mul _)
      have hb : ‖F x • ∇ η x‖ ^ 2 ≤ (C / (t - s)) ^ 2 * F x ^ 2 := by
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hηg x) 2)
          (sq_nonneg _)
      simp only [hg]
      linarith
    have hint_ind : IntegrableOn (fun x ↦ (closedBall z s)ᶜ.indicator (fun x ↦ ‖GF x‖ ^ 2) x)
        (ball z t) :=
      (hGFσ t htR₀).indicator measurableSet_closedBall.compl
    have hint_rhs : IntegrableOn g (ball z t) :=
      (hint_ind.const_mul 2).add ((hFσ t htR₀).const_mul _)
    have h2 : ∫ x in ball z t, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2 ≤ ∫ x in ball z t, g x :=
      integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _) hint_rhs (ae_of_all _ hpt)
    have h3 : ∫ x in ball z t, g x = 2 * (∫ x in ball z t ∩ (closedBall z s)ᶜ, ‖GF x‖ ^ 2) +
        2 * (C / (t - s)) ^ 2 * ∫ x in ball z t, F x ^ 2 := by
      simp only [hg]
      rw [integral_add (hint_ind.const_mul 2) ((hFσ t htR₀).const_mul _), integral_const_mul,
        integral_const_mul, setIntegral_indicator measurableSet_closedBall.compl]
    have h4 : ∫ x in ball z t ∩ (closedBall z s)ᶜ, ‖GF x‖ ^ 2 ≤ Φ t - Φ s := by
      have e : ∫ x in ball z t \ ball z s, ‖GF x‖ ^ 2 = Φ t - Φ s :=
        setIntegral_diff measurableSet_ball (hGFσ t htR₀) (ball_subset_ball hst.le)
      rw [← e]
      refine setIntegral_mono_set ((hGFσ t htR₀).mono_set diff_subset)
        (ae_of_all _ fun _ ↦ sq_nonneg _) (Eventually.of_forall fun x hx ↦ ?_)
      exact ⟨hx.1, fun h ↦ hx.2 (ball_subset_closedBall h)⟩
    have h5 : ∫ x in ball z t, F x ^ 2 ≤ S :=
      setIntegral_mono_set (hFσ R hR) (ae_of_all _ fun _ ↦ sq_nonneg _)
        (ball_subset_ball htR.le).eventuallyLE
    have h6 := hVt t htR.le
    have hct : 0 ≤ (C / (t - s)) ^ 2 := sq_nonneg _
    have hmain : Φ t ≤ 2 * (Φ t - Φ s) + 2 * (C / (t - s)) ^ 2 * S + Er * V := by
      have hEV : Er * (volume ({x | 0 < F x} ∩ ball z t)).toReal ≤ Er * V :=
        mul_le_mul_of_nonneg_left h6 hEr
      have hCS : (C / (t - s)) ^ 2 * ∫ x in ball z t, F x ^ 2 ≤ (C / (t - s)) ^ 2 * S :=
        mul_le_mul_of_nonneg_left h5 hct
      calc Φ t ≤ (∫ x in ball z t, ‖(1 - η x) • GF x - F x • ∇ η x‖ ^ 2) +
            Er * (volume ({x | 0 < F x} ∩ ball z t)).toReal := h1
        _ ≤ (2 * (∫ x in ball z t ∩ (closedBall z s)ᶜ, ‖GF x‖ ^ 2) +
            2 * (C / (t - s)) ^ 2 * ∫ x in ball z t, F x ^ 2) + Er * V := by
            rw [← h3]; exact add_le_add h2 hEV
        _ ≤ 2 * (Φ t - Φ s) + 2 * (C / (t - s)) ^ 2 * S + Er * V := by linarith
    have e : (C / (t - s)) ^ 2 * S = C ^ 2 * S / (t - s) ^ 2 := by rw [div_pow]; ring
    linarith
  have hit := iteration_lemma (f := Φ) (M := Φ R) (A := C ^ 2 * S) (B := Er * V / 2) hρR
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) (by positivity) (by positivity)
    (fun t _ htR ↦ hΦmono t R htR.le hR) key
  have e : (16 : ℝ) / (1 - 1 / 2) ^ 4 * (C ^ 2 * S / (R - ρ) ^ 2 + Er * V / 2) =
      256 * C ^ 2 / (R - ρ) ^ 2 * S + 128 * Er * V := by
    have hRρ : 0 < R - ρ := by linarith
    have : (R - ρ) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at hit
  exact hit

end EllipticBernoulli
