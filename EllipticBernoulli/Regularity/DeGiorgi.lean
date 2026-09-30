/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.ObstacleCaccioppoli
public import EllipticBernoulli.Sobolev.SobolevGNS
public import EllipticBernoulli.Regularity.DeGiorgiSeq

/-!
# The De Giorgi `L^∞` lemma

For `f ∈ DG⁺` on balls centred at `z` (`IsDeGiorgiAt`), the Sobolev inequality on the support
and the De Giorgi iteration give (`degiorgi_linfty`): if `k ≥ K`, `H > 0`, `C₁ ρ² ≤ H²` and
`∫_{B_ρ(z)} (f - k)₊² ≤ ε₀ H² ρᵈ`, then `f ≤ k + H` a.e. on `B_{ρ/2}(z)`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Extension by zero and cutoff products -/

/-- A function with a weak gradient in `U` that vanishes (with its gradient) outside a ball
`B_s(z)` with `B̄_t(z) ⊆ U`, `s < t`, has the same weak gradient on the whole space. -/
theorem HasWeakGradient.univ_of_vanish {U : Set (E d)} {g : E d → ℝ} {Gg : E d → E d}
    (hw : HasWeakGradient U g Gg) {z : E d} {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (hzt : closedBall z t ⊆ U) (hg0 : ∀ x ∉ ball z s, g x = 0)
    (hG0 : ∀ x ∉ ball z s, Gg x = 0) : HasWeakGradient univ g Gg := by
  have hc : IsCompact (closedBall z t) := isCompact_closedBall _ _
  have hbt : ball z s ⊆ closedBall z t :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hst.le)
  have hgs : Function.support g ⊆ closedBall z t := fun x hx ↦ by
    by_contra hx'
    exact hx (hg0 x fun h' ↦ hx' (hbt h'))
  have hGs : Function.support Gg ⊆ closedBall z t := fun x hx ↦ by
    by_contra hx'
    exact hx (hG0 x fun h' ↦ hx' (hbt h'))
  have hgi : Integrable g :=
    (integrableOn_iff_integrable_of_support_subset hgs).1
      (hw.1.integrableOn_compact_subset hzt hc)
  have hGi : Integrable Gg :=
    (integrableOn_iff_integrable_of_support_subset hGs).1
      (hw.2.1.integrableOn_compact_subset hzt hc)
  refine HasWeakGradient.of_integral_eq (hgi.locallyIntegrable.locallyIntegrableOn _)
    (hGi.locallyIntegrable.locallyIntegrableOn _) fun φ hφ hφc _ v ↦ ?_
  set m := (s + t) / 2 with hm
  have hsm : s < m := by rw [hm]; linarith
  have hmt : m < t := by rw [hm]; linarith
  obtain ⟨χ, hχ, -, hχ1, -, hχc, hχt, -⟩ := exists_cutoff z (by linarith : 0 ≤ m) hmt
  have hψ : ContDiff ℝ ∞ (fun x ↦ χ x * φ x) := hχ.mul hφ
  have hψc : HasCompactSupport (fun x ↦ χ x * φ x) := hχc.mul_right
  have hψU : tsupport (fun x ↦ χ x * φ x) ⊆ U :=
    (tsupport_mul_subset_left).trans (hχt.trans (ball_subset_closedBall.trans hzt))
  have h := hw.integral_eq hψ hψc hψU v
  have hloc : ∀ x ∈ ball z s, (fun y ↦ χ y * φ y) =ᶠ[𝓝 x] φ := by
    intro x hx
    have : ball z m ∈ 𝓝 x := isOpen_ball.mem_nhds (ball_subset_ball hsm.le hx)
    filter_upwards [this] with y hy
    rw [hχ1 y (ball_subset_closedBall hy), one_mul]
  have e1 : ∫ x, g x * fderiv ℝ (fun y ↦ χ y * φ y) x v = ∫ x, g x * fderiv ℝ φ x v := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ ball z s
    · simp only [(hloc x hx).fderiv_eq]
    · simp only [hg0 x hx, zero_mul]
  have e2 : ∫ x, inner ℝ (Gg x) v * (χ x * φ x) = ∫ x, inner ℝ (Gg x) v * φ x := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ ball z s
    · simp only [hχ1 x (ball_subset_closedBall (ball_subset_ball hsm.le hx)), one_mul]
    · simp only [hG0 x hx, inner_zero_left, zero_mul]
  rw [← e1, ← e2]
  exact h

/-- `MemLp` on the whole space of a function in `L²` of a closed ball vanishing outside. -/
theorem memLp_of_vanish {F : Type*} [NormedAddCommGroup F] {h : E d → F} {z : E d} {t : ℝ}
    (hh : MemLp h 2 (volume.restrict (closedBall z t)))
    (h0 : ∀ x ∉ closedBall z t, h x = 0) : MemLp h 2 volume := by
  have : (closedBall z t).indicator h = h := by
    funext x
    by_cases hx : x ∈ closedBall z t
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, h0 x hx]
  rw [← this, memLp_indicator_iff_restrict measurableSet_closedBall]
  exact hh

theorem gradient_eq_zero_of_eq_zero {η : E d → ℝ} (hη0 : ∀ x, 0 ≤ η x)
    {x : E d} (hx : η x = 0) : ∇ η x = 0 := by
  have hmin : IsLocalMin η x :=
    Eventually.of_forall fun y ↦ by rw [hx]; exact hη0 y
  have : fderiv ℝ η x = 0 := hmin.fderiv_eq_zero
  simp [gradient, this]

theorem norm_add_sq_le_two (a b : E d) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + b), sq_nonneg (‖a‖ - ‖b‖)]

theorem integrableOn_posPart_sq {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d}
    (hf : MemH1Loc U f G) {K : Set (E d)} (hK : K ⊆ U) (hKc : IsCompact K) (k : ℝ) :
    IntegrableOn (fun x ↦ (max (f x - k) 0) ^ 2) K :=
  integrableOn_sq_of_memH1Loc (hf.posPart_sub hU k) hK hKc

/-- **Chebyshev.** `|{f > k''} ∩ B_r| ≤ (k'' - k')⁻² ∫_{B_r} (f - k')₊²`. -/
theorem measure_levelSet_le {f : E d → ℝ} {z : E d} {r k' k'' : ℝ} (hk : k' < k'')
    (hint : IntegrableOn (fun x ↦ (max (f x - k') 0) ^ 2) (ball z r)) :
    (volume ({x | k'' < f x} ∩ ball z r)).toReal ≤
      (∫ x in ball z r, (max (f x - k') 0) ^ 2) / (k'' - k') ^ 2 := by
  have hpos : 0 < (k'' - k') ^ 2 := by have := sub_pos.2 hk; positivity
  rw [le_div_iff₀ hpos, mul_comm]
  have h := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (ball z r))
    (ae_of_all _ fun x ↦ sq_nonneg (max (f x - k') 0)) hint ((k'' - k') ^ 2)
  refine le_trans (mul_le_mul_of_nonneg_left ?_ hpos.le) h
  rw [measureReal_def, Measure.restrict_apply' measurableSet_ball]
  refine ENNReal.toReal_mono (volume_inter_ball_ne_top _ z r) (measure_mono ?_)
  refine inter_subset_inter_left _ fun x hx ↦ ?_
  have hx' : k'' < f x := hx
  simp only [mem_ofPred_eq]
  rw [max_eq_left (by linarith)]
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- **One De Giorgi step.** For `0 < r' < σ < r ≤ ρ` and a level `k ≥ K`, with
`m = |{f > k} ∩ B_r|` and `I = ∫_{B_r} (f - k)₊²`:
`∫_{B_{r'}} (f - k)₊² ≤ C_S² (m^{1/d})² (2 (C₀ (r - σ)⁻² I + C₁ m) + 2 (C/(σ - r'))² I)`. -/
theorem degiorgi_step {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d}
    (hf : MemH1Loc U f G) {z : E d} {ρ K C₀ C₁ : ℝ} (hDG : IsDeGiorgiAt f G z ρ K C₀ C₁)
    (hzρ : closedBall z ρ ⊆ U) {CS : ℝ≥0} (hS : SobolevSupport d CS)
    {r' σ r k : ℝ} (hr' : 0 < r') (h1 : r' < σ) (h2 : σ < r) (h3 : r ≤ ρ) (hk : K ≤ k) :
    ∫ x in ball z r', (max (f x - k) 0) ^ 2 ≤
      (CS : ℝ) ^ 2 * ((volume ({x | k < f x} ∩ ball z r)).toReal ^ (1 / (d : ℝ))) ^ 2 *
        (2 * (C₀ / (r - σ) ^ 2 * (∫ x in ball z r, (max (f x - k) 0) ^ 2) +
          C₁ * (volume ({x | k < f x} ∩ ball z r)).toReal) +
         2 * (cutoffConst / (σ - r')) ^ 2 * ∫ x in ball z r, (max (f x - k) 0) ^ 2) := by
  obtain ⟨η, hη, hη01, hη1, hη0, hηc, -, hηg⟩ := exists_cutoff z hr'.le h1
  set F : E d → ℝ := fun x ↦ max (f x - k) 0 with hFdef
  set GF : E d → E d := {y | k < f y}.indicator G with hGFdef
  have hF : MemH1Loc U F GF := hf.posPart_sub hU k
  have hg := hF.mul_smooth hU hη
  set g : E d → ℝ := fun x ↦ η x * F x with hgdef
  set Gg : E d → E d := fun x ↦ η x • GF x + F x • ∇ η x with hGgdef
  have hg0 : ∀ x ∉ ball z σ, g x = 0 := fun x hx ↦ by simp [hgdef, (hη0 x hx).1]
  have hG0 : ∀ x ∉ ball z σ, Gg x = 0 := fun x hx ↦ by
    simp [hGgdef, (hη0 x hx).1, (hη0 x hx).2]
  have hzr : closedBall z r ⊆ U := (closedBall_subset_closedBall h3).trans hzρ
  have hσr : ball z σ ⊆ closedBall z r :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall h2.le)
  have hw := hg.1.univ_of_vanish (by linarith : 0 ≤ σ) h2 hzr hg0 hG0
  have hc : IsCompact (closedBall z r) := isCompact_closedBall z r
  have hgL : MemLp g 2 := memLp_of_vanish (hg.2 _ hzr hc).1 fun x hx ↦
    hg0 x fun h ↦ hx (hσr h)
  have hGL : MemLp Gg 2 := memLp_of_vanish (hg.2 _ hzr hc).2 fun x hx ↦
    hG0 x fun h ↦ hx (hσr h)
  have hgc : HasCompactSupport g := hηc.mul_right
  have hFk : ∀ x, F x = 0 → ¬ k < f x := fun x hx hlt ↦ by
    have : F x = f x - k := max_eq_left (by linarith)
    rw [this] at hx; linarith
  have hGz : ∀ x, g x = 0 → Gg x = 0 := by
    intro x hx
    rcases mul_eq_zero.1 hx with h | h
    · simp [hGgdef, h, gradient_eq_zero_of_eq_zero (fun y ↦ (hη01 y).1) h]
    · simp [hGgdef, h, hGFdef, indicator_of_notMem (show x ∉ {y | k < f y} from hFk x h)]
  have hSob := integral_sq_le_of_sobolevSupport hS hw hgL hGL hgc hGz
  -- the support of `g`
  have hsub : {x | g x ≠ 0} ⊆ {x | k < f x} ∩ ball z r := by
    intro x hx
    have hηx : η x ≠ 0 := fun h ↦ hx (by simp [hgdef, h])
    have hFx : F x ≠ 0 := fun h ↦ hx (by simp [hgdef, h])
    refine ⟨?_, ?_⟩
    · change k < f x
      by_contra hlt
      exact hFx (max_eq_right (by linarith [not_lt.1 hlt]))
    · by_contra hxr
      exact hηx (hη0 x fun h ↦ hxr (ball_subset_ball h2.le h)).1
  have hm : (volume {x | g x ≠ 0}).toReal ≤ (volume ({x | k < f x} ∩ ball z r)).toReal :=
    ENNReal.toReal_mono (volume_inter_ball_ne_top _ z r) (measure_mono hsub)
  -- the left-hand side
  have hg2 : Integrable (fun x ↦ g x ^ 2) := by
    have := (memLp_two_iff_integrable_sq_norm hgL.aestronglyMeasurable).1 hgL
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hL : ∫ x in ball z r', F x ^ 2 ≤ ∫ x, g x ^ 2 := by
    have e : ∫ x in ball z r', F x ^ 2 = ∫ x in ball z r', g x ^ 2 :=
      setIntegral_congr_fun measurableSet_ball fun x hx ↦ by
        simp [hgdef, hη1 x (ball_subset_closedBall hx)]
    rw [e]
    exact setIntegral_le_integral hg2 (ae_of_all _ fun x ↦ sq_nonneg _)
  -- the gradient
  set c := cutoffConst / (σ - r') with hc'
  have hGFσ : IntegrableOn (fun x ↦ ‖GF x‖ ^ 2) (ball z σ) :=
    (integrableOn_norm_sq_of_memH1Loc hF hzr hc).mono_set hσr
  have hFσ : IntegrableOn (fun x ↦ F x ^ 2) (ball z σ) :=
    (integrableOn_sq_of_memH1Loc hF hzr hc).mono_set hσr
  have hGint : ∫ x, ‖Gg x‖ ^ 2 ≤ 2 * (∫ x in ball z σ, ‖GF x‖ ^ 2) +
      2 * c ^ 2 * ∫ x in ball z σ, F x ^ 2 := by
    have hrhs0 : IntegrableOn (fun x ↦ 2 * ‖GF x‖ ^ 2 + 2 * c ^ 2 * F x ^ 2) (ball z σ) :=
      (hGFσ.const_mul 2).add (hFσ.const_mul _)
    have hrhs : Integrable ((ball z σ).indicator fun x ↦ 2 * ‖GF x‖ ^ 2 + 2 * c ^ 2 * F x ^ 2) :=
      hrhs0.integrable_indicator measurableSet_ball
    calc ∫ x, ‖Gg x‖ ^ 2
        ≤ ∫ x, (ball z σ).indicator (fun x ↦ 2 * ‖GF x‖ ^ 2 + 2 * c ^ 2 * F x ^ 2) x := by
          refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _) hrhs
            (ae_of_all _ fun x ↦ ?_)
          dsimp only
          by_cases hx : x ∈ ball z σ
          · rw [indicator_of_mem hx]
            refine (norm_add_sq_le_two _ _).trans ?_
            have ha : ‖η x • GF x‖ ^ 2 ≤ ‖GF x‖ ^ 2 := by
              rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
              have h01 := hη01 x
              have hη2 : η x ^ 2 ≤ 1 := pow_le_one₀ h01.1 h01.2
              exact (mul_le_mul_of_nonneg_right hη2 (sq_nonneg ‖GF x‖)).trans_eq (one_mul _)
            have hb : ‖F x • ∇ η x‖ ^ 2 ≤ c ^ 2 * F x ^ 2 := by
              rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_comm]
              exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hηg x) 2)
                (sq_nonneg _)
            linarith
          · rw [indicator_of_notMem hx, hG0 x hx, norm_zero]
            norm_num
      _ = 2 * (∫ x in ball z σ, ‖GF x‖ ^ 2) + 2 * c ^ 2 * ∫ x in ball z σ, F x ^ 2 := by
          rw [integral_indicator measurableSet_ball, integral_add (hGFσ.const_mul 2)
            (hFσ.const_mul _), integral_const_mul, integral_const_mul]
  have hDGσ := hDG k hk σ r (by linarith) h2 h3
  have hFσr : ∫ x in ball z σ, F x ^ 2 ≤ ∫ x in ball z r, F x ^ 2 :=
    setIntegral_mono_set ((integrableOn_sq_of_memH1Loc hF hzr hc).mono_set
      ball_subset_closedBall) (ae_of_all _ fun x ↦ sq_nonneg _)
      (ball_subset_ball h2.le).eventuallyLE
  have hm' : ((volume {x | g x ≠ 0}).toReal ^ (1 / (d : ℝ))) ^ 2 ≤
      ((volume ({x | k < f x} ∩ ball z r)).toReal ^ (1 / (d : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow ENNReal.toReal_nonneg hm (by positivity)) 2
  calc ∫ x in ball z r', F x ^ 2 ≤ ∫ x, g x ^ 2 := hL
    _ ≤ (CS : ℝ) ^ 2 * ((volume {x | g x ≠ 0}).toReal ^ (1 / (d : ℝ))) ^ 2 *
          ∫ x, ‖Gg x‖ ^ 2 := hSob
    _ ≤ (CS : ℝ) ^ 2 * ((volume ({x | k < f x} ∩ ball z r)).toReal ^ (1 / (d : ℝ))) ^ 2 *
          (2 * (∫ x in ball z σ, ‖GF x‖ ^ 2) + 2 * c ^ 2 * ∫ x in ball z σ, F x ^ 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm' (sq_nonneg _)) hGint
          (integral_nonneg fun _ ↦ sq_nonneg _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ (CS : ℝ) ^ 2 * ((volume ({x | k < f x} ∩ ball z r)).toReal ^ (1 / (d : ℝ))) ^ 2 *
          (2 * (C₀ / (r - σ) ^ 2 * (∫ x in ball z r, F x ^ 2) +
            C₁ * (volume ({x | k < f x} ∩ ball z r)).toReal) +
           2 * c ^ 2 * ∫ x in ball z r, F x ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hDGσ (by norm_num))
          (mul_le_mul_of_nonneg_left hFσr (by positivity))) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The constant `A` of the De Giorgi iteration. -/
noncomputable def degiorgiA (d : ℕ) (CS : ℝ≥0) (C₀ : ℝ) : ℝ :=
  2 * ((CS : ℝ) ^ 2 + 1) * (C₀ + 1 + cutoffConst ^ 2) * 4 ^ (3 + 2 / (d : ℝ))

/-- The smallness threshold `ε₀` of the De Giorgi `L^∞` lemma. -/
noncomputable def degiorgiEps (d : ℕ) (CS : ℝ≥0) (C₀ : ℝ) : ℝ :=
  degiorgiA d CS C₀ ^ (-1 / (2 / (d : ℝ))) *
    ((4 : ℝ) ^ (1 + 2 / (d : ℝ))) ^ (-1 / (2 / (d : ℝ)) ^ 2)

theorem degiorgiA_pos {CS : ℝ≥0} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) : 0 < degiorgiA d CS C₀ := by
  unfold degiorgiA; positivity

theorem degiorgiEps_pos {CS : ℝ≥0} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) : 0 < degiorgiEps d CS C₀ := by
  unfold degiorgiEps
  exact mul_pos (Real.rpow_pos_of_pos (degiorgiA_pos hC₀) _)
    (Real.rpow_pos_of_pos (by positivity) _)

/-- **De Giorgi's `L^∞` lemma** (first De Giorgi lemma). Let `f ∈ DG⁺` on balls centred at `z` up
to radius `ρ` (levels `≥ K`, constants `C₀, C₁`). If `k ≥ K`, `H > 0`, `C₁ ρ² ≤ H²` and
`∫_{B_ρ(z)} (f - k)₊² ≤ ε₀ H² ρᵈ`, then `f ≤ k + H` a.e. on `B_{ρ/2}(z)`. -/
theorem degiorgi_linfty (hd : 1 ≤ d) {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    {G : E d → E d} (hf : MemH1Loc U f G) {z : E d} {ρ K C₀ C₁ : ℝ} (hρ : 0 < ρ)
    (hDG : IsDeGiorgiAt f G z ρ K C₀ C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hzρ : closedBall z ρ ⊆ U) {CS : ℝ≥0} (hS : SobolevSupport d CS) {k H : ℝ} (hk : K ≤ k)
    (hH : 0 < H) (hH1 : C₁ * ρ ^ 2 ≤ H ^ 2)
    (hsmall : ∫ x in ball z ρ, (max (f x - k) 0) ^ 2 ≤ degiorgiEps d CS C₀ * H ^ 2 * ρ ^ d) :
    ∀ᵐ x ∂(volume.restrict (ball z (ρ / 2))), f x ≤ k + H := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set α : ℝ := 2 / (d : ℝ) with hα
  have hα0 : 0 < α := by positivity
  set rr : ℕ → ℝ := fun j ↦ ρ / 2 + ρ / 2 ^ (j + 1) with hrr
  set σσ : ℕ → ℝ := fun j ↦ ρ / 2 + 3 * ρ / 2 ^ (j + 3) with hσσ
  set kk : ℕ → ℝ := fun j ↦ k + H - H / 2 ^ j with hkk
  set Y : ℕ → ℝ := fun j ↦ ∫ x in ball z (rr j), (max (f x - kk j) 0) ^ 2 with hY
  have hp : ∀ j : ℕ, (0 : ℝ) < 2 ^ j := fun j ↦ by positivity
  have hrr0 : rr 0 = ρ := by norm_num [hrr]
  have hkk0 : kk 0 = k := by simp [hkk]
  have hrr_pos : ∀ j, 0 < rr j := fun j ↦ by simp only [hrr]; have := hp (j + 1); positivity
  have hrr_le : ∀ j, rr j ≤ ρ := fun j ↦ by
    simp only [hrr]
    have : ρ / 2 ^ (j + 1) ≤ ρ / 2 := by
      apply div_le_div_of_nonneg_left hρ.le (by norm_num)
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have e1 : ∀ j : ℕ, (2 : ℝ) ^ (j + 3) = 2 ^ (j + 1) * 4 := fun j ↦ by ring
  have e2 : ∀ j : ℕ, (2 : ℝ) ^ (j + 2) = 2 ^ (j + 1) * 2 := fun j ↦ by ring
  have hrσ : ∀ j, rr j - σσ j = ρ / 2 ^ (j + 3) := fun j ↦ by
    simp only [hrr, hσσ]; rw [e1]; field_simp; ring
  have hσr : ∀ j, σσ j - rr (j + 1) = ρ / 2 ^ (j + 3) := fun j ↦ by
    simp only [hrr, hσσ]; rw [e1, e2]; field_simp; ring
  have h1 : ∀ j, rr (j + 1) < σσ j := fun j ↦ by
    have := hσr j; have : 0 < ρ / 2 ^ (j + 3) := by have := hp (j + 3); positivity
    linarith
  have h2 : ∀ j, σσ j < rr j := fun j ↦ by
    have := hrσ j; have : 0 < ρ / 2 ^ (j + 3) := by have := hp (j + 3); positivity
    linarith
  have hkk_diff : ∀ j, kk (j + 1) - kk j = H / 2 ^ (j + 1) := fun j ↦ by
    simp only [hkk]; rw [pow_succ]; field_simp; ring
  have hkk_lt : ∀ j, kk j < kk (j + 1) := fun j ↦ by
    have := hkk_diff j; have : 0 < H / 2 ^ (j + 1) := by have := hp (j + 1); positivity
    linarith
  have hkK : ∀ j, K ≤ kk j := fun j ↦ by
    have : H / 2 ^ j ≤ H := div_le_self hH.le (one_le_pow₀ (by norm_num))
    simp only [hkk]; linarith
  have hball : ∀ j, closedBall z (rr j) ⊆ U := fun j ↦
    (closedBall_subset_closedBall (hrr_le j)).trans hzρ
  have hint : ∀ j k', IntegrableOn (fun x ↦ (max (f x - k') 0) ^ 2) (ball z (rr j)) :=
    fun j k' ↦ (integrableOn_posPart_sq hU hf (hball j) (isCompact_closedBall _ _) k').mono_set
      ball_subset_closedBall
  have hY0 : ∀ j, 0 ≤ Y j := fun j ↦ setIntegral_nonneg measurableSet_ball fun x _ ↦ sq_nonneg _
  set A := degiorgiA d CS C₀ with hA
  have hA0 : 0 < A := degiorgiA_pos hC₀
  set N := A / ((H ^ 2) ^ α * ρ ^ 2) with hN
  have hN0 : 0 < N := by
    have : 0 < (H ^ 2) ^ α := Real.rpow_pos_of_pos (by positivity) _
    positivity
  set b : ℝ := (4 : ℝ) ^ (1 + α) with hb
  have hb1 : 1 < b := Real.one_lt_rpow (by norm_num) (by linarith)
  -- the recursion
  have hrec : ∀ j, Y (j + 1) ≤ N * b ^ j * Y j ^ (1 + α) := by
    intro j
    have hstep := degiorgi_step hU hf hDG hzρ hS (r' := rr (j + 1)) (σ := σσ j) (r := rr j)
      (k := kk (j + 1)) (hrr_pos _) (h1 j) (h2 j) (hrr_le j) (hkK _)
    set m := (volume ({x | kk (j + 1) < f x} ∩ ball z (rr j))).toReal with hm
    set I := ∫ x in ball z (rr j), (max (f x - kk (j + 1)) 0) ^ 2 with hI
    have hm2 : (m ^ (1 / (d : ℝ))) ^ 2 = m ^ α := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg, hα]
      congr 1; push_cast; ring
    have hIY : I ≤ Y j := by
      refine setIntegral_mono_on (hint j _) (hint j _) measurableSet_ball fun x _ ↦ ?_
      have h0 : 0 ≤ max (f x - kk (j + 1)) 0 := le_max_right _ _
      have hle : max (f x - kk (j + 1)) 0 ≤ max (f x - kk j) 0 :=
        max_le_max (by linarith [hkk_lt j]) le_rfl
      exact pow_le_pow_left₀ h0 hle 2
    have hmY : m ≤ Y j / (H / 2 ^ (j + 1)) ^ 2 := by
      have := measure_levelSet_le (hkk_lt j) (hint j (kk j))
      rwa [hkk_diff] at this
    have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_ball fun x _ ↦ sq_nonneg _
    rw [hrσ, hσr, hm2] at hstep
    refine hstep.trans ?_
    have := degiorgi_numeric (S := (CS : ℝ)) (c := cutoffConst) j (hY0 j) hI0 hIY
      ENNReal.toReal_nonneg hmY hC₀ hC₁ hρ hH hH1 hα0
    convert this using 1
    rfl
  -- the initial condition
  have hinit : Y 0 ≤ N ^ (-1 / α) * b ^ (-1 / α ^ 2) := by
    have hid : N ^ (-1 / α) = A ^ (-1 / α) * H ^ 2 * ρ ^ d := degiorgi_init_identity hd hA0 hH hρ
    rw [hid]
    have hY0' : Y 0 = ∫ x in ball z ρ, (max (f x - k) 0) ^ 2 := by simp only [hY, hrr0, hkk0]
    rw [hY0']
    refine hsmall.trans (le_of_eq ?_)
    rw [degiorgiEps, ← hA]
    ring
  have hlim := degiorgi_seq_tendsto hN0 hb1 hα0 hY0 hrec hinit
  -- conclusion
  set Z := ∫ x in ball z (ρ / 2), (max (f x - (k + H)) 0) ^ 2 with hZ
  have hZle : ∀ j, Z ≤ Y j := by
    intro j
    have hsub : ball z (ρ / 2) ⊆ ball z (rr j) := ball_subset_ball (by
      simp only [hrr]; have := hp (j + 1); have : 0 < ρ / 2 ^ (j + 1) := by positivity
      linarith)
    calc Z ≤ ∫ x in ball z (ρ / 2), (max (f x - kk j) 0) ^ 2 := by
          refine setIntegral_mono_on ((hint j _).mono_set hsub) ((hint j _).mono_set hsub)
            measurableSet_ball fun x _ ↦ ?_
          have h0 : 0 ≤ max (f x - (k + H)) 0 := le_max_right _ _
          have : kk j ≤ k + H := by
            simp only [hkk]; have := hp j; have : 0 ≤ H / 2 ^ j := by positivity
            linarith
          exact pow_le_pow_left₀ h0 (max_le_max (by linarith) le_rfl) 2
      _ ≤ Y j := setIntegral_mono_set (hint j _) (ae_of_all _ fun x ↦ sq_nonneg _)
          hsub.eventuallyLE
  have hZ0 : Z ≤ 0 := ge_of_tendsto' hlim hZle
  have hZ0' : Z = 0 := le_antisymm hZ0 (setIntegral_nonneg measurableSet_ball fun x _ ↦
    sq_nonneg _)
  have hsub0 : ball z (ρ / 2) ⊆ ball z (rr 0) := by rw [hrr0]; exact ball_subset_ball (by linarith)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x ↦ sq_nonneg _)
    ((hint 0 (k + H)).mono_set hsub0)).1 hZ0'
  filter_upwards [hae] with x hx
  have : max (f x - (k + H)) 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx
  have := le_max_left (f x - (k + H)) 0
  linarith

end EllipticBernoulli
