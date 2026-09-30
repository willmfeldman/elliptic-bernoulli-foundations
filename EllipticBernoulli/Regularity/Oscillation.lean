/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.BoundaryPoincare

/-!
# Oscillation decay at a boundary point

Let `B = B_r(x₀)`, `z ∈ ∂B`, and let `f ∈ DG⁺` on balls centred at `z` (`IsDeGiorgiAt`, levels
`≥ K`) with `f ≤ K` on `B_ρ(z) \ B` and `f ≤ M` a.e. on `B_ρ(z)`. Then (`oscillation_decay`)
`f ≤ K + λ (M - K) + Λ ρ` a.e. on `B_{ρ/16}(z)`, with `λ = 1 - 2^{-(n+1)} < 1` and
`Λ = 2ⁿ √C₁`, where `n` depends only on `d`, the Sobolev constant and `C₀`.

Proof: De Giorgi's second lemma, adapted to the boundary. On the levels
`k_j = M - (M - K) 2^{-j}` the boundary Poincaré inequality (`integral_le_boundary_poincare`),
applied to `min((f - k_j)₊, k_{j+1} - k_j)`, together with Caccioppoli, shows that
`|{f > k_n} ∩ B_{ρ/8}|` is small for `n` large (`measure_shrink_step`, summed over `j`); then the
`L^∞` lemma `degiorgi_linfty` on `B_{ρ/8}(z)` concludes.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal NNReal Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

theorem setIntegral_indicator_const₀ {s A : Set (E d)}
    (hA : NullMeasurableSet A (volume.restrict s)) (C : ℝ) :
    ∫ x in s, A.indicator (fun _ ↦ C) x = C * (volume (A ∩ s)).toReal := by
  rw [integral_indicator₀ hA, setIntegral_const, measureReal_restrict_apply₀ hA, smul_eq_mul,
    mul_comm, measureReal_def]

theorem integrableOn_indicator_const₀ {s A : Set (E d)} (hs : volume s ≠ ⊤)
    (hA : NullMeasurableSet A (volume.restrict s)) (C : ℝ) :
    IntegrableOn (A.indicator (fun _ ↦ C)) s :=
  (integrableOn_const hs).indicator₀ hA

theorem aemeasurable_of_memH1Loc {U : Set (E d)} {f : E d → ℝ} {G : E d → E d}
    (hf : MemH1Loc U f G) {z : E d} {ρ : ℝ} (hzU : closedBall z ρ ⊆ U) {s : ℝ} (hs : s ≤ ρ) :
    AEMeasurable f (volume.restrict (ball z s)) :=
  ((hf.2 _ hzU (isCompact_closedBall z ρ)).1.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono (ball_subset_closedBall.trans (closedBall_subset_closedBall hs))
      le_rfl)).aemeasurable

theorem IsDeGiorgiAt.mono {f : E d → ℝ} {G : E d → E d} {z : E d} {R₀ R₁ K C₀ C₁ : ℝ}
    (h : IsDeGiorgiAt f G z R₀ K C₀ C₁) (hR : R₁ ≤ R₀) : IsDeGiorgiAt f G z R₁ K C₀ C₁ :=
  fun k hk ρ R hρ hρR hR' ↦ h k hk ρ R hρ hρR (hR'.trans hR)

/-- `t ≤ λ/2 + t²/(2λ)`. -/
theorem le_amgm {t lam : ℝ} (hlam : 0 < lam) : t ≤ lam / 2 + t ^ 2 / (2 * lam) := by
  have : 0 ≤ (t - lam) ^ 2 / (2 * lam) := by positivity
  have e : lam / 2 + t ^ 2 / (2 * lam) - t = (t - lam) ^ 2 / (2 * lam) := by
    field_simp; ring
  linarith

/-- **One step of measure shrinking at the boundary.** For levels `a < b` with `f ≤ a` on
`B_ρ(z) \ B` and any `λ > 0`:
`(b - a) |{f > b} ∩ B_{ρ/8}| ≤`
`(ρ/4) (λ/2 |{a < f ≤ b} ∩ B_{ρ/2}| + (2λ)⁻¹ ∫_{B_{ρ/2}} |∇(f-a)₊|²)`. -/
theorem measure_shrink_step {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d}
    (hf : MemH1Loc U f G) {x₀ z : E d} {r ρ : ℝ} (hr : 0 < r) (hz : dist z x₀ = r)
    (hρ : 0 < ρ) (hzU : closedBall z ρ ⊆ U) {a b : ℝ} (hab : a < b)
    (hout : ∀ x ∈ ball z ρ, x ∉ ball x₀ r → f x ≤ a) {lam : ℝ} (hlam : 0 < lam) :
    (b - a) * (volume ({x | b < f x} ∩ ball z (ρ / 8))).toReal ≤
      ρ / 4 * (lam / 2 * (volume ({x | a < f x ∧ f x ≤ b} ∩ ball z (ρ / 2))).toReal +
        1 / (2 * lam) * ∫ x in ball z (ρ / 2), ‖{y | a < f y}.indicator G x‖ ^ 2) := by
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
        · have h1 : GF x = 0 := indicator_of_notMem (show x ∉ {y | a < f y} from not_lt.2 hfa) _
          have hF0 : F x = 0 := max_eq_right (by linarith)
          have h2 : x ∉ {y | c < F y} := by simp [hF0, hc.le]
          simp [hGgdef, h1, indicator_of_notMem h2]
        · have hfb : b < f x := by
            by_contra hfb; exact hxD ⟨not_le.1 hfa, not_lt.1 hfb⟩
          have hFx : F x = f x - a := max_eq_left (by linarith)
          have h2 : x ∈ {y | c < F y} := by simp only [mem_ofPred_eq, hFx, hcdef]; linarith
          simp [hGgdef, indicator_of_mem h2]
      rw [this, norm_zero]; positivity
  -- the Poincaré inequality
  have hP := integral_le_boundary_poincare hg.1 hr hz hρ hzU (fun x _ ↦ hg_nn x)
    (fun x hx hxB ↦ hg_zero x (hout x hx hxB))
  have hKc : IsCompact (closedBall z ρ) := isCompact_closedBall _ _
  have hsub8 : ball z (ρ / 8) ⊆ closedBall z ρ :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hsub2 : ball z (ρ / 2) ⊆ closedBall z ρ :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  -- left-hand side: Markov
  have hgi : IntegrableOn g (ball z (ρ / 8)) :=
    (hg.1.1.integrableOn_compact_subset hzU hKc).mono_set hsub8
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (ball z (ρ / 8)))
    (ae_of_all _ hg_nn) hgi c
  have hL : c * (volume ({x | b < f x} ∩ ball z (ρ / 8))).toReal ≤ ∫ x in ball z (ρ / 8), g x := by
    refine le_trans ?_ hMarkov
    gcongr
    rw [measureReal_def, Measure.restrict_apply' measurableSet_ball]
    exact ENNReal.toReal_mono (volume_inter_ball_ne_top _ z _)
      (measure_mono (inter_subset_inter_left _ fun x hx ↦ hg_ge x hx))
  -- right-hand side
  have hDm : NullMeasurableSet D (volume.restrict (ball z (ρ / 2))) :=
    (aemeasurable_of_memH1Loc hf hzU (by linarith : ρ / 2 ≤ ρ)).nullMeasurable measurableSet_Ioc
  have hGgi : IntegrableOn (fun x ↦ ‖Gg x‖) (ball z (ρ / 2)) :=
    ((hg.1.2.1.integrableOn_compact_subset hzU hKc).mono_set hsub2).norm
  have hGFi : IntegrableOn (fun x ↦ ‖GF x‖ ^ 2) (ball z (ρ / 2)) :=
    (integrableOn_norm_sq_of_memH1Loc hF hzU hKc).mono_set hsub2
  have hIi := integrableOn_indicator_const₀ measure_ball_lt_top.ne hDm (lam / 2)
  have hR : ∫ x in ball z (ρ / 2), ‖Gg x‖ ≤ lam / 2 * (volume (D ∩ ball z (ρ / 2))).toReal +
      1 / (2 * lam) * ∫ x in ball z (ρ / 2), ‖GF x‖ ^ 2 := by
    calc ∫ x in ball z (ρ / 2), ‖Gg x‖
        ≤ ∫ x in ball z (ρ / 2), (D.indicator (fun _ ↦ lam / 2) x + ‖GF x‖ ^ 2 / (2 * lam)) :=
          setIntegral_mono hGgi (hIi.add (hGFi.div_const _)) hGg
      _ = _ := by
          rw [integral_add hIi (hGFi.div_const _),
            setIntegral_indicator_const₀ hDm, integral_div]
          ring
  calc c * (volume ({x | b < f x} ∩ ball z (ρ / 8))).toReal
      ≤ ∫ x in ball z (ρ / 8), g x := hL
    _ ≤ ρ / 4 * ∫ x in ball z (ρ / 2), ‖Gg x‖ := hP
    _ ≤ _ := mul_le_mul_of_nonneg_left hR (by positivity)

/-- The measures of the slabs `{k_j < f ≤ k_{j+1}} ∩ s` sum to at most `|s|`. -/
theorem sum_measure_slab_le {f : E d → ℝ} {s : Set (E d)} (hs : MeasurableSet s)
    (hsf : volume s ≠ ⊤) (hf : AEMeasurable f (volume.restrict s)) {k : ℕ → ℝ} (hk : Monotone k)
    (n : ℕ) :
    ∑ j ∈ Finset.range n, (volume ({x | k j < f x ∧ f x ≤ k (j + 1)} ∩ s)).toReal ≤
      (volume s).toReal := by
  set μ := volume.restrict s with hμ
  set D : ℕ → Set (E d) := fun j ↦ {x | k j < f x ∧ f x ≤ k (j + 1)} with hD
  have e : ∀ j, (volume (D j ∩ s)).toReal = μ.real (D j) := fun j ↦ by
    rw [hμ, measureReal_restrict_apply' hs, measureReal_def]
  have hfin : ∀ b ∈ Finset.range n, μ (D b) ≠ ⊤ := fun b _ ↦
    ne_top_of_le_ne_top (by rw [hμ, Measure.restrict_apply_univ]; exact hsf)
      (measure_mono (subset_univ _))
  have hdisj : ∀ i j, i < j → Disjoint (D i) (D j) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hx hx' ↦ ?_
    have := hk (show i + 1 ≤ j by omega)
    linarith [hx.2, hx'.1]
  have hsum : ∑ j ∈ Finset.range n, μ.real (D j) = μ.real (⋃ j ∈ Finset.range n, D j) := by
    refine (measureReal_biUnion_finset₀ (fun i _ j _ hij ↦ ?_) (fun b _ ↦
      hf.nullMeasurable measurableSet_Ioc) hfin).symm
    rcases lt_or_gt_of_ne hij with h | h
    · exact (hdisj i j h).aedisjoint
    · exact (hdisj j i h).symm.aedisjoint
  rw [Finset.sum_congr rfl (fun j _ ↦ e j), hsum]
  calc μ.real (⋃ j ∈ Finset.range n, D j) ≤ μ.real univ :=
        measureReal_mono (subset_univ _) (by rw [hμ, Measure.restrict_apply_univ]; exact hsf)
    _ = (volume s).toReal := by rw [hμ, measureReal_restrict_apply_univ, measureReal_def]

/-- Algebra of one measure-shrinking step with `λ = τ e / ρ`, `e = δ 2^{-j}`. -/
theorem shrink_algebra {e ρ τ A V m X a : ℝ} (he : 0 < e) (hρ : 0 < ρ) (hτ : 0 < τ)
    (hX : X ≤ A * e ^ 2 / ρ ^ 2 * V)
    (h : e / 2 * a ≤ ρ / 4 * ((τ * e / ρ) / 2 * m + 1 / (2 * (τ * e / ρ)) * X)) :
    a ≤ (τ * m + A * V / τ) / 4 := by
  have e1 : ρ / 4 * ((τ * e / ρ) / 2 * m + 1 / (2 * (τ * e / ρ)) * X) =
      e / 8 * (τ * m) + ρ ^ 2 * X / (8 * τ * e) := by
    field_simp; ring
  have e2 : ρ ^ 2 * X / (8 * τ * e) ≤ e / 8 * (A * V / τ) := by
    rw [div_le_iff₀ (by positivity)]
    have : ρ ^ 2 * X ≤ A * e ^ 2 * V := by
      have := mul_le_mul_of_nonneg_left hX (sq_nonneg ρ)
      calc ρ ^ 2 * X ≤ ρ ^ 2 * (A * e ^ 2 / ρ ^ 2 * V) := this
        _ = A * e ^ 2 * V := by field_simp
    calc ρ ^ 2 * X ≤ A * e ^ 2 * V := this
      _ = e / 8 * (A * V / τ) * (8 * τ * e) := by field_simp
  rw [e1] at h
  have : e / 2 * a ≤ e / 2 * ((τ * m + A * V / τ) / 4) := by
    calc e / 2 * a ≤ e / 8 * (τ * m) + e / 8 * (A * V / τ) := by linarith
      _ = e / 2 * ((τ * m + A * V / τ) / 4) := by ring
  exact le_of_mul_le_mul_left this (by positivity)

/-! ### Constants -/

/-- `ω_d = |B_1|`. -/
noncomputable def unitBallVol (d : ℕ) : ℝ := (volume (ball (0 : E d) 1)).toReal

theorem unitBallVol_pos : 0 < unitBallVol d :=
  ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne

theorem volume_ball_toReal (hd : 1 ≤ d) (z : E d) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume (ball z ρ)).toReal = ρ ^ d * unitBallVol d := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [Measure.addHaar_ball volume z hρ, ENNReal.toReal_mul, finrank_E,
    ENNReal.toReal_ofReal (by positivity), unitBallVol]

/-- `A = 4 C₀ + 1`. -/
noncomputable def oscA (C₀ : ℝ) : ℝ := 4 * C₀ + 1

/-- The parameter `τ = 2 A ω 8ᵈ / ε₀` of the measure-shrinking steps. -/
noncomputable def oscTau (d : ℕ) (CS : ℝ≥0) (C₀ : ℝ) : ℝ :=
  2 * oscA C₀ * unitBallVol d * 8 ^ d / degiorgiEps d CS C₀

/-- The number of measure-shrinking steps. -/
noncomputable def oscN (d : ℕ) (CS : ℝ≥0) (C₀ : ℝ) : ℕ :=
  ⌈2 * unitBallVol d * oscTau d CS C₀ * 8 ^ d / degiorgiEps d CS C₀⌉₊ + 1

theorem oscN_pos (CS : ℝ≥0) (C₀ : ℝ) : 0 < oscN d CS C₀ := Nat.succ_pos _

/-- Numerics: after `oscN` steps the level set is small enough for the `L^∞` lemma. -/
theorem oscillation_numeric {CS : ℝ≥0} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) {a V ρ : ℝ} (hρ : 0 ≤ ρ)
    (hV : V = ρ ^ d * unitBallVol d)
    (ha : a ≤ (oscTau d CS C₀ * V / oscN d CS C₀ + oscA C₀ * V / oscTau d CS C₀) / 4) :
    4 * a ≤ degiorgiEps d CS C₀ * (ρ / 8) ^ d := by
  set ε := degiorgiEps d CS C₀ with hε
  set w0 := unitBallVol d with hw0
  set A := oscA C₀ with hA
  set τ := oscTau d CS C₀ with hτ
  set n := oscN d CS C₀ with hn
  have hε0 : 0 < ε := degiorgiEps_pos hC₀
  have hw0' : 0 < w0 := unitBallVol_pos
  have hA0 : 0 < A := by rw [hA, oscA]; linarith
  have h8 : (0 : ℝ) < 8 ^ d := by positivity
  have hτ0 : 0 < τ := by rw [hτ, oscTau]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast oscN_pos CS C₀
  have hnbig : 2 * w0 * τ * 8 ^ d / ε ≤ n := by
    rw [hn, oscN]; push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  have e1 : w0 * A / τ = ε / (2 * 8 ^ d) := by
    rw [hτ, oscTau, ← hA, ← hw0, ← hε]; field_simp
  have e2 : w0 * τ / n ≤ ε / (2 * 8 ^ d) := by
    rw [div_le_div_iff₀ hn0 (by positivity)]
    rw [div_le_iff₀ hε0] at hnbig
    linarith
  have hρd : 0 ≤ ρ ^ d := by positivity
  calc 4 * a ≤ τ * V / n + A * V / τ := by linarith
    _ = ρ ^ d * (w0 * τ / n) + ρ ^ d * (w0 * A / τ) := by rw [hV]; ring
    _ ≤ ρ ^ d * (ε / (2 * 8 ^ d)) + ρ ^ d * (ε / (2 * 8 ^ d)) := by
        rw [e1]; exact add_le_add (mul_le_mul_of_nonneg_left e2 hρd) le_rfl
    _ = ε * (ρ / 8) ^ d := by rw [div_pow]; field_simp; ring

/-! ### Oscillation decay -/

/-- **Oscillation decay, main case.** If `K < M`, `f ≤ M` a.e. on `B_ρ(z)`, `f ≤ K` on
`B_ρ(z) \ B` and `C₁ ρ² ≤ ((M - K) 2^{-n})²` (`n = oscN`), then
`f ≤ M - (M - K) 2^{-(n+1)}` a.e. on `B_{ρ/16}(z)`. -/
theorem oscillation_main (hd : 1 ≤ d) {CS : ℝ≥0} (hS : SobolevSupport d CS) {U : Set (E d)}
    (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d} (hf : MemH1Loc U f G) {x₀ z : E d}
    {r ρ : ℝ} (hr : 0 < r) (hz : dist z x₀ = r) (hρ : 0 < ρ) (hzU : closedBall z ρ ⊆ U)
    {K C₀ C₁ M : ℝ} (hDG : IsDeGiorgiAt f G z ρ K C₀ C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hout : ∀ x ∈ ball z ρ, x ∉ ball x₀ r → f x ≤ K)
    (hM : ∀ᵐ x ∂(volume.restrict (ball z ρ)), f x ≤ M) (hKM : K < M)
    (hC₁ρ : C₁ * ρ ^ 2 ≤ ((M - K) / 2 ^ oscN d CS C₀) ^ 2) :
    ∀ᵐ x ∂(volume.restrict (ball z (ρ / 16))), f x ≤ M - (M - K) / 2 ^ (oscN d CS C₀ + 1) := by
  set n := oscN d CS C₀ with hn
  set δ := M - K with hδ
  have hδ0 : 0 < δ := sub_pos.2 hKM
  set τ := oscTau d CS C₀ with hτ
  set A := oscA C₀ with hA
  have hτ0 : 0 < τ := by
    rw [hτ, oscTau]
    have := degiorgiEps_pos (d := d) (CS := CS) hC₀
    have := unitBallVol_pos (d := d)
    have : 0 < oscA C₀ := by rw [oscA]; linarith
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
  have hKc : IsCompact (closedBall z ρ) := isCompact_closedBall _ _
  set a : ℕ → ℝ := fun j ↦ (volume ({x | kk j < f x} ∩ ball z (ρ / 8))).toReal with ha
  set m : ℕ → ℝ :=
    fun j ↦ (volume ({x | kk j < f x ∧ f x ≤ kk (j + 1)} ∩ ball z (ρ / 2))).toReal with hm
  -- Caccioppoli bound on each level
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
  have hstep : ∀ j, j < n → a (j + 1) ≤ (τ * m j + A * V / τ) / 4 := by
    intro j hj
    have hej : 0 < δ / 2 ^ j := by have := hp j; positivity
    have hlt : kk j < kk (j + 1) := by
      have := hkk_diff j; have : 0 < δ / 2 ^ j / 2 := by positivity
      linarith
    have h := measure_shrink_step hU hf hr hz hρ hzU hlt
      (fun x hx hxB ↦ (hout x hx hxB).trans (hkK j)) (lam := τ * (δ / 2 ^ j) / ρ)
      (by positivity)
    rw [hkk_diff] at h
    exact shrink_algebra hej hρ hτ0 (hX j hj.le) h
  -- summation
  have ha_mono : ∀ j, j < n → a n ≤ a (j + 1) := by
    intro j hj
    refine ENNReal.toReal_mono (volume_inter_ball_ne_top _ z _) (measure_mono ?_)
    exact inter_subset_inter_left _ fun x hx ↦ lt_of_le_of_lt (hkk_mono (by omega : j + 1 ≤ n)) hx
  have hmsum : ∑ j ∈ Finset.range n, m j ≤ V := by
    refine (sum_measure_slab_le measurableSet_ball measure_ball_lt_top.ne
      (aemeasurable_of_memH1Loc hf hzU (by linarith : ρ / 2 ≤ ρ)) hkk_mono n).trans ?_
    exact ENNReal.toReal_mono measure_ball_lt_top.ne (measure_mono (ball_subset_ball (by linarith)))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast oscN_pos CS C₀
  have han : a n ≤ (τ * V / n + A * V / τ) / 4 := by
    have h1 : (n : ℝ) * a n ≤ ∑ j ∈ Finset.range n, (τ * m j + A * V / τ) / 4 := by
      calc (n : ℝ) * a n = ∑ j ∈ Finset.range n, a n := by simp
        _ ≤ ∑ j ∈ Finset.range n, a (j + 1) :=
            Finset.sum_le_sum fun j hj ↦ ha_mono j (Finset.mem_range.1 hj)
        _ ≤ _ := Finset.sum_le_sum fun j hj ↦ hstep j (Finset.mem_range.1 hj)
    have h2 : ∑ j ∈ Finset.range n, (τ * m j + A * V / τ) / 4 =
        (τ * ∑ j ∈ Finset.range n, m j + n * (A * V / τ)) / 4 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]; simp
    rw [h2] at h1
    have h3 : (n : ℝ) * a n ≤ (τ * V + n * (A * V / τ)) / 4 := h1.trans
      (div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left hmsum hτ0.le) le_rfl)
        (by norm_num))
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4)] at h3 ⊢
    have e : (τ * V / n + A * V / τ) = (τ * V + n * (A * V / τ)) / n := by
      rw [add_div, mul_div_cancel_left₀ _ hn0.ne']
    rw [e, le_div_iff₀ hn0]; linarith
  have h4 := oscillation_numeric hC₀ hρ.le hVeq han
  -- the `L²` smallness on `B_{ρ/8}`
  set H := δ / 2 ^ (n + 1) with hH
  have hH0 : 0 < H := by have := hp (n + 1); positivity
  have hsmall : ∫ x in ball z (ρ / 8), (max (f x - kk n) 0) ^ 2 ≤
      degiorgiEps d CS C₀ * H ^ 2 * (ρ / 8) ^ d := by
    have hAm : NullMeasurableSet {x | kk n < f x} (volume.restrict (ball z (ρ / 8))) :=
      (aemeasurable_of_memH1Loc hf hzU (by linarith : ρ / 8 ≤ ρ)).nullMeasurable
        measurableSet_Ioi
    have hint := (integrableOn_posPart_sq hU hf hzU hKc (kk n)).mono_set
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith : ρ / 8 ≤ ρ)))
    have hM8 : ∀ᵐ x ∂(volume.restrict (ball z (ρ / 8))), f x ≤ M :=
      ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hM
    calc ∫ x in ball z (ρ / 8), (max (f x - kk n) 0) ^ 2
        ≤ ∫ x in ball z (ρ / 8), {x | kk n < f x}.indicator (fun _ ↦ (δ / 2 ^ n) ^ 2) x := by
          refine integral_mono_ae hint
            (integrableOn_indicator_const₀ measure_ball_lt_top.ne hAm _) ?_
          filter_upwards [hM8] with x hx
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
      _ ≤ H ^ 2 * (degiorgiEps d CS C₀ * (ρ / 8) ^ d) := mul_le_mul_of_nonneg_left h4 (sq_nonneg H)
      _ = _ := by ring
  have hC₁8 : C₁ * (ρ / 8) ^ 2 ≤ H ^ 2 := by
    have : H = δ / 2 ^ n / 2 := by rw [hH, pow_succ]; field_simp
    rw [this]
    linarith [sq_nonneg (δ / 2 ^ n)]
  have hL := degiorgi_linfty hd hU hf (ρ := ρ / 8) (by positivity) (hDG.mono (by linarith))
    hC₀ hC₁ ((closedBall_subset_closedBall (by linarith)).trans hzU) hS (hkK n) hH0 hC₁8 hsmall
  have e16 : ρ / 8 / 2 = ρ / 16 := by ring
  rw [e16] at hL
  filter_upwards [hL] with x hx
  have : kk n + H = M - δ / 2 ^ (n + 1) := by
    simp only [hkk, hH]; rw [pow_succ]; field_simp; ring
  linarith

/-- **Oscillation decay at a boundary point.** With `n = oscN d CS C₀`,
`f ≤ K + (1 - 2^{-(n+1)}) (M - K) + 2ⁿ √C₁ ρ` a.e. on `B_{ρ/16}(z)`. -/
theorem oscillation_decay (hd : 1 ≤ d) {CS : ℝ≥0} (hS : SobolevSupport d CS) {U : Set (E d)}
    (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d} (hf : MemH1Loc U f G) {x₀ z : E d}
    {r ρ : ℝ} (hr : 0 < r) (hz : dist z x₀ = r) (hρ : 0 < ρ) (hzU : closedBall z ρ ⊆ U)
    {K C₀ C₁ M : ℝ} (hDG : IsDeGiorgiAt f G z ρ K C₀ C₁) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hout : ∀ x ∈ ball z ρ, x ∉ ball x₀ r → f x ≤ K)
    (hM : ∀ᵐ x ∂(volume.restrict (ball z ρ)), f x ≤ M) :
    ∀ᵐ x ∂(volume.restrict (ball z (ρ / 16))), f x ≤
      K + (1 - 1 / 2 ^ (oscN d CS C₀ + 1)) * (M - K) + 2 ^ oscN d CS C₀ * √C₁ * ρ := by
  set n := oscN d CS C₀ with hn
  have hp : ∀ j : ℕ, (0 : ℝ) < 2 ^ j := fun j ↦ by positivity
  have hM16 : ∀ᵐ x ∂(volume.restrict (ball z (ρ / 16))), f x ≤ M :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith)) hM
  have hΛ : 0 ≤ 2 ^ n * √C₁ * ρ := by positivity
  have hlam : 1 / (2 : ℝ) ^ (n + 1) ≤ 1 := by
    rw [div_le_one (hp _)]; exact one_le_pow₀ (by norm_num)
  rcases le_or_gt M K with hMK | hKM
  · filter_upwards [hM16] with x hx
    have := mul_nonneg (show (0 : ℝ) ≤ 1 / 2 ^ (n + 1) by have := hp (n + 1); positivity)
      (sub_nonneg.2 hMK)
    linarith
  by_cases hC : C₁ * ρ ^ 2 ≤ ((M - K) / 2 ^ n) ^ 2
  · filter_upwards [oscillation_main hd hS hU hf hr hz hρ hzU hDG hC₀ hC₁ hout hM hKM hC]
      with x hx
    have : M - (M - K) / 2 ^ (n + 1) = K + (1 - 1 / 2 ^ (n + 1)) * (M - K) := by ring
    linarith
  · -- `M - K < 2ⁿ √C₁ ρ`
    have h1 : (M - K) / 2 ^ n < √C₁ * ρ := by
      have hpos : 0 < (M - K) / 2 ^ n := by have := hp n; have := sub_pos.2 hKM; positivity
      have h2 : ((M - K) / 2 ^ n) ^ 2 < (√C₁ * ρ) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hC₁]; linarith [not_le.1 hC]
      exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
    have h3 : M - K < 2 ^ n * √C₁ * ρ := by
      rw [div_lt_iff₀ (hp n)] at h1; linarith
    filter_upwards [hM16] with x hx
    have h4 : 0 ≤ 1 / (2 : ℝ) ^ (n + 1) * (M - K) := by
      have := hp (n + 1); have := sub_pos.2 hKM; positivity
    linarith [mul_le_mul_of_nonneg_right hlam (sub_pos.2 hKM).le]

end EllipticBernoulli
