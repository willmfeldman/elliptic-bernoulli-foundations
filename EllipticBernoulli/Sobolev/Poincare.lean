/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.RayPoincare
public import EllipticBernoulli.Sobolev.Lattice
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Poincaré inequality on an annulus with zero outer trace

If `w ∈ H¹_loc(U)` has weak gradient `G`, `B̄_R(x) ⊆ U`, `w = 0` a.e. on `U \ B_R(x)` and
`0 < r < R`, then (`lintegral_sq_annulus_le`)
`∫_{B_R \ B_r} w² ≤ ((R - r) R / r)² ∫_{B_R \ B_r} |G|²`,
hence `∫_{B_R \ B_r} w² ≤ 4 (R - r)² ∫_{B_R \ B_r} |G|²` for `R/2 ≤ r < R`
(`poincare_annulus_zero_outer`).

Proof.
1. `G = 0` a.e. on `U \ B̄_R(x)`, where `w = 0` (`ae_inner_eq_zero_of_ae_eq_zero`: the weak
   gradient identity and the fundamental lemma of the calculus of variations).
2. Let `u = 1_{B_R} w` and `Hᵢ = 1_{B_R} ⟨G, eᵢ⟩`, and mollify: `vₙ = u ⋆ ρₙ` with bumps of radius
   `εₙ → 0`. Then `vₙ ∈ C^∞` vanishes on `{|y - x| ≥ R + εₙ}` and `∂ᵢvₙ = Hᵢ ⋆ ρₙ`
   (`fderiv_convolution_indicator_eq`, using step 1).
3. The ray inequality `lintegral_sq_compl_ball_le` (`Sobolev/RayPoincare.lean`) for `vₙ`, with
   `R' = R + εₙ`, and the `L²` convergence of mollifications
   (`tendsto_eLpNorm_convolution_sub`) on the set `{|y - x| ≥ r}`.
-/

open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped ENNReal ContDiff Convolution

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Preliminaries -/

/-- The weak gradient vanishes a.e. on an open set where the function vanishes a.e. -/
theorem ae_inner_eq_zero_of_ae_eq_zero {U O : Set (E d)} {w : E d → ℝ} {G : E d → E d}
    (hw : HasWeakGradient U w G) (hO : IsOpen O) (hOU : O ⊆ U) (h0 : ∀ᵐ y, y ∈ O → w y = 0)
    (v : E d) : ∀ᵐ y, y ∈ O → inner ℝ (G y) v = 0 := by
  refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_inner_apply (hw.2.1.mono_set hOU) v) fun φ hφ hφc hφO ↦ ?_
  have h := hw.integral_eq hφ hφc (hφO.trans hOU) v
  have hl : ∫ y, w y * fderiv ℝ φ y v = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0] with y hy
    change _ = (0 : ℝ)
    by_cases hyt : y ∈ tsupport φ
    · rw [hy (hφO hyt), zero_mul]
    · rw [fderiv_apply_eq_zero_of_notMem_tsupport hyt, mul_zero]
  rw [hl, eq_comm, neg_eq_zero] at h
  simpa only [smul_eq_mul, mul_comm] using h

/-- `‖L‖² = ∑ᵢ L(eᵢ)²` for a linear form on `E d`. -/
theorem norm_sq_eq_sum_apply_single (L : E d →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ i, L (EuclideanSpace.single i 1) ^ 2 := by
  set g := (InnerProductSpace.toDual ℝ (E d)).symm L with hg
  have hL : ‖L‖ = ‖g‖ := ((InnerProductSpace.toDual ℝ (E d)).symm.norm_map L).symm
  have hi : ∀ i, L (EuclideanSpace.single i 1) = g i := fun i ↦ by
    rw [← InnerProductSpace.toDual_symm_apply, EuclideanSpace.inner_single_right]
    simp [hg]
  rw [hL, EuclideanSpace.norm_sq_eq]
  simp [hi, Real.norm_eq_abs, sq_abs]

/-- `|g|² = ∑ᵢ ⟨g, eᵢ⟩²` on `E d`. -/
theorem norm_sq_eq_sum_inner_single (g : E d) :
    ‖g‖ ^ 2 = ∑ i, inner ℝ g (EuclideanSpace.single i (1 : ℝ)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [EuclideanSpace.inner_single_right]
  simp [Real.norm_eq_abs, sq_abs]

/-- `∫⁻ (f²)⁺ = ‖f‖₂²` for a.e.-strongly measurable `f`. -/
theorem lintegral_ofReal_sq_eq {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : AEStronglyMeasurable f μ) :
    ∫⁻ y, ENNReal.ofReal (f y ^ 2) ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero hf
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at h
  rw [← ENNReal.rpow_natCast, Nat.cast_ofNat, h]
  refine lintegral_congr fun y ↦ ?_
  rw [Real.enorm_eq_ofReal_abs]
  rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]

/-- `L²` convergence implies convergence of the `L²` norms. -/
theorem tendsto_eLpNorm_two_of_tendsto_sub {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {fn : ℕ → X → ℝ} (_hf : AEStronglyMeasurable f μ)
    (_hfn : ∀ n, AEStronglyMeasurable (fn n) μ) (hfin : eLpNorm f 2 μ ≠ ⊤)
    (h : Tendsto (fun n ↦ eLpNorm (fn n - f) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (fn n) 2 μ) atTop (𝓝 (eLpNorm f 2 μ)) := by
  have hup : ∀ n, eLpNorm (fn n) 2 μ ≤ eLpNorm (fn n - f) 2 μ + eLpNorm f 2 μ := fun n ↦ by
    have := eLpNorm_add_le (f := fn n - f) (g := f) one_le_two (μ := μ)
    rwa [sub_add_cancel] at this
  have hlo : ∀ n, eLpNorm f 2 μ - eLpNorm (fn n - f) 2 μ ≤ eLpNorm (fn n) 2 μ := fun n ↦ by
    rw [tsub_le_iff_left]
    have := eLpNorm_add_le (f := f - fn n) (g := fn n) one_le_two (μ := μ)
    rwa [sub_add_cancel, eLpNorm_sub_comm] at this
  have h1 : Tendsto (fun n ↦ eLpNorm (fn n - f) 2 μ + eLpNorm f 2 μ) atTop
      (𝓝 (eLpNorm f 2 μ)) := by
    simpa using h.add (tendsto_const_nhds (x := eLpNorm f 2 μ))
  have h2 : Tendsto (fun n ↦ eLpNorm f 2 μ - eLpNorm (fn n - f) 2 μ) atTop
      (𝓝 (eLpNorm f 2 μ)) := by
    simpa using ENNReal.Tendsto.sub tendsto_const_nhds h (Or.inl hfin)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h2 h1 hlo hup

/-- `L²` convergence on the whole space implies convergence of `∫_S f²` for every set `S`. -/
theorem tendsto_setLIntegral_sq {f : E d → ℝ} {fn : ℕ → E d → ℝ} (hf : MemLp f 2 volume)
    (hfn : ∀ n, AEStronglyMeasurable (fn n) volume)
    (h : Tendsto (fun n ↦ eLpNorm (fn n - f) 2 volume) atTop (𝓝 0)) (S : Set (E d)) :
    Tendsto (fun n ↦ ∫⁻ y in S, ENNReal.ofReal (fn n y ^ 2)) atTop
      (𝓝 (∫⁻ y in S, ENNReal.ofReal (f y ^ 2))) := by
  have e : ∀ n, ∫⁻ y in S, ENNReal.ofReal (fn n y ^ 2) = eLpNorm (fn n) 2 (volume.restrict S) ^ 2 :=
    fun n ↦ lintegral_ofReal_sq_eq _ _ (hfn n).restrict
  simp_rw [e, lintegral_ofReal_sq_eq _ _ hf.aestronglyMeasurable.restrict]
  have hS : Tendsto (fun n ↦ eLpNorm (fn n - f) 2 (volume.restrict S)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ ↦ bot_le)
      fun n ↦ eLpNorm_mono_measure _ Measure.restrict_le_self
  have := tendsto_eLpNorm_two_of_tendsto_sub hf.aestronglyMeasurable.restrict
    (fun n ↦ (hfn n).restrict) (hf.restrict S).ne hS
  exact ((ENNReal.continuous_pow 2).tendsto _).comp this

/-- A convolution of a function vanishing off `B_R(x)` with a bump of radius `ε` vanishes on
`{|y - x| ≥ R + ε}`. -/
theorem convolution_eq_zero_of_support {f : E d → ℝ} {x : E d} {R : ℝ}
    (hf : ∀ y ∉ ball x R, f y = 0) (ρ : ContDiffBump (0 : E d)) {y : E d}
    (hy : R + ρ.rOut ≤ ‖y - x‖) : (f ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) y = 0 := by
  rw [convolution_def]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t ↦ ?_)
  simp only [lsmul_apply, smul_eq_mul, Pi.zero_apply]
  by_cases ht : t ∈ ball x R
  · have hρ : ρ.normed volume (y - t) = 0 := by
      refine Function.notMem_support.1 fun hmem ↦ ?_
      rw [ρ.support_normed_eq, mem_ball, dist_zero_right] at hmem
      rw [mem_ball, dist_eq_norm] at ht
      have : ‖y - x‖ ≤ ‖y - t‖ + ‖t - x‖ := by
        calc ‖y - x‖ = ‖(y - t) + (t - x)‖ := by rw [sub_add_sub_cancel]
          _ ≤ _ := norm_add_le _ _
      linarith
    rw [hρ, mul_zero]
  · rw [hf t ht, zero_mul]

/-! ### The annulus inequality -/

/-- **Poincaré inequality on an annulus with zero outer trace**, sharp form:
`∫_{B_R \ B_r} w² ≤ ((R - r) R / r)² ∫_{B_R \ B_r} |G|²`. -/
theorem lintegral_sq_annulus_le {U : Set (E d)} {w : E d → ℝ} {G : E d → E d} {x : E d}
    {R r : ℝ} (hU : IsOpen U) (hw : MemH1Loc U w G) (hr : 0 < r) (hrR : r < R)
    (hRU : closedBall x R ⊆ U) (h0 : ∀ᵐ y ∂(volume.restrict (U \ ball x R)), w y = 0) :
    ∫⁻ y in ball x R \ ball x r, ENNReal.ofReal (w y ^ 2) ≤
      ENNReal.ofReal (((R - r) * R / r) ^ 2) *
        ∫⁻ y in ball x R \ ball x r, ENNReal.ofReal (‖G y‖ ^ 2) := by
  have hR : 0 < R := hr.trans hrR
  -- a larger ball `B = B_{R₁}(x)` with `B̄_{R₁} ⊆ U`
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall x R).exists_cthickening_subset_open hU hRU
  rw [cthickening_closedBall hδ.le hR.le] at hδU
  set R₁ := δ + R with hR₁
  set B := ball x R₁ with hBdef
  have hBU : B ⊆ U := ball_subset_closedBall.trans hδU
  have h0' : ∀ᵐ y, y ∈ U \ ball x R → w y = 0 :=
    (ae_restrict_iff' (hU.measurableSet.diff measurableSet_ball)).1 h0
  set e : Fin d → E d := fun i ↦ EuclideanSpace.single i 1 with hedef
  -- step 1: the weak gradient vanishes off `B̄_R`
  have hG0 : ∀ i, ∀ᵐ y, y ∈ U \ closedBall x R → inner ℝ (G y) (e i) = 0 := fun i ↦
    ae_inner_eq_zero_of_ae_eq_zero hw.1 (hU.sdiff isClosed_closedBall) sdiff_subset
      (h0'.mono fun y hy hyO ↦ hy ⟨hyO.1, fun h ↦ hyO.2 (ball_subset_closedBall h)⟩) (e i)
  have hsph : ∀ᵐ y, y ∉ sphere x R :=
    measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere_of_ne_zero volume x hR.ne')
  -- step 2: the functions `u`, `Hᵢ`
  set u : E d → ℝ := (ball x R).indicator w with hudef
  set H : Fin d → E d → ℝ := fun i ↦ (ball x R).indicator fun y ↦ inner ℝ (G y) (e i)
    with hHdef
  have hRB : ball x R ⊆ B := ball_subset_ball (by linarith)
  have huB : u =ᵐ[volume] B.indicator w := by
    filter_upwards [h0'] with y hy
    by_cases hyR : y ∈ ball x R
    · rw [hudef, indicator_of_mem hyR, indicator_of_mem (hRB hyR)]
    · by_cases hyB : y ∈ B
      · rw [hudef, indicator_of_notMem hyR, indicator_of_mem hyB, hy ⟨hBU hyB, hyR⟩]
      · rw [hudef, indicator_of_notMem hyR, indicator_of_notMem hyB]
  have hHB : ∀ i, H i =ᵐ[volume] B.indicator fun y ↦ inner ℝ (G y) (e i) := fun i ↦ by
    filter_upwards [hG0 i, hsph] with y hy hys
    by_cases hyR : y ∈ ball x R
    · simp only [hHdef]
      rw [indicator_of_mem hyR, indicator_of_mem (hRB hyR)]
    · by_cases hyB : y ∈ B
      · have hyc : y ∉ closedBall x R := fun h ↦ by
          rcases (mem_closedBall.1 h).lt_or_eq with h' | h'
          · exact hyR (mem_ball.2 h')
          · exact hys (mem_sphere.2 h')
        simp only [hHdef]
        rw [indicator_of_notMem hyR, indicator_of_mem hyB, hy ⟨hBU hyB, hyc⟩]
      · simp only [hHdef]
        rw [indicator_of_notMem hyR, indicator_of_notMem hyB]
  -- integrability
  have hwL2 : MemLp w 2 (volume.restrict (closedBall x R₁)) :=
    (hw.2 (closedBall x R₁) hδU (isCompact_closedBall _ _)).1
  have hGL2 : MemLp G 2 (volume.restrict (closedBall x R₁)) :=
    (hw.2 (closedBall x R₁) hδU (isCompact_closedBall _ _)).2
  have : IsFiniteMeasure (volume.restrict (closedBall x R₁)) :=
    isFiniteMeasure_restrict.2 (measure_closedBall_lt_top (x := x) (r := R₁)).ne
  have hRcl : ball x R ⊆ closedBall x R₁ := hRB.trans ball_subset_closedBall
  have hu2 : MemLp u 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).2
      (hwL2.mono_measure (Measure.restrict_mono hRcl le_rfl))
  have hH2 : ∀ i, MemLp (H i) 2 volume := fun i ↦
    (memLp_indicator_iff_restrict measurableSet_ball).2
      ((hGL2.inner_const (e i)).mono_measure (Measure.restrict_mono hRcl le_rfl))
  have hwB : IntegrableOn w B :=
    IntegrableOn.mono_set (hwL2.integrable one_le_two) ball_subset_closedBall
  have hwk : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ B →
      ∀ v : E d, ∫ y, w y * fderiv ℝ φ y v = -∫ y, inner ℝ (G y) v * φ y :=
    fun φ h1 h2 h3 v ↦ hw.1.integral_eq h1 h2 (h3.trans hBU) v
  -- mollifiers of radius `εₙ = δ / (n + 3)`
  set ε : ℕ → ℝ := fun n ↦ δ / ((n : ℝ) + 3) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hεlt : ∀ n, ε n < δ / 2 := fun n ↦ by
    rw [hεdef]
    exact div_lt_div_of_pos_left hδ (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hε : Tendsto ε atTop (𝓝 0) := by
    have h3 : Tendsto (fun n : ℕ ↦ (n : ℝ) + 3) atTop atTop :=
      tendsto_atTop_add_const_right _ 3 tendsto_natCast_atTop_atTop
    simpa [hεdef, div_eq_mul_inv] using h3.inv_tendsto_atTop.const_mul δ
  let ρ : ℕ → ContDiffBump (0 : E d) := fun n ↦
    ⟨ε n / 2, ε n, half_pos (hεpos n), half_lt_self (hεpos n)⟩
  have hρ : ∀ n, (ρ n).rOut = ε n := fun _ ↦ rfl
  have hρt : Tendsto (fun n ↦ (ρ n).rOut) atTop (𝓝 0) := hε
  set v : ℕ → E d → ℝ := fun n ↦ u ⋆[lsmul ℝ ℝ, volume] (ρ n).normed volume with hvdef
  have hvc : ∀ n, ContDiff ℝ 1 (v n) := fun n ↦
    (ρ n).hasCompactSupport_normed.contDiff_convolution_right (lsmul ℝ ℝ)
      (hu2.locallyIntegrable one_le_two) (ρ n).contDiff_normed
  have hu0 : ∀ y ∉ ball x R, u y = 0 := fun y hy ↦ indicator_of_notMem hy _
  have hH0 : ∀ i, ∀ y ∉ ball x R, H i y = 0 := fun i y hy ↦ indicator_of_notMem hy _
  have hv0 : ∀ n y, R + ε n ≤ ‖y - x‖ → v n y = 0 := fun n y hy ↦
    convolution_eq_zero_of_support hu0 (ρ n) hy
  -- `∂ᵢ vₙ = Hᵢ ⋆ ρₙ`
  have hder : ∀ n y i, fderiv ℝ (v n) y (e i) =
      (H i ⋆[lsmul ℝ ℝ, volume] (ρ n).normed volume) y := by
    intro n y i
    by_cases hy : ‖y - x‖ < R₁ - ε n
    · have hsub : closedBall y (ρ n).rOut ⊆ B := fun z hz ↦ by
        rw [mem_closedBall, dist_eq_norm, hρ] at hz
        rw [hBdef, mem_ball, dist_eq_norm]
        calc ‖z - x‖ = ‖(z - y) + (y - x)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖z - y‖ + ‖y - x‖ := norm_add_le _ _
          _ < R₁ := by linarith
      have e1 : v n = B.indicator w ⋆[lsmul ℝ ℝ, volume] (ρ n).normed volume :=
        convolution_congr (lsmul ℝ ℝ) huB (ae_eq_refl _)
      have e2 : H i ⋆[lsmul ℝ ℝ, volume] (ρ n).normed volume =
          B.indicator (fun y ↦ inner ℝ (G y) (e i)) ⋆[lsmul ℝ ℝ, volume] (ρ n).normed volume :=
        convolution_congr (lsmul ℝ ℝ) (hHB i) (ae_eq_refl _)
      rw [e1, e2]
      exact fderiv_convolution_indicator_eq measurableSet_ball hwB hwk (ρ n) (e i) hsub
    · push Not at hy
      have hfar : R + ε n < ‖y - x‖ := by linarith [hεlt n]
      have hloc : v n =ᶠ[𝓝 y] fun _ ↦ 0 := by
        have hopen : IsOpen {z : E d | R + ε n < ‖z - x‖} :=
          isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
        filter_upwards [hopen.mem_nhds hfar] with z hz
        exact hv0 n z hz.le
      rw [hloc.fderiv_eq, fderiv_const_apply, zero_apply,
        convolution_eq_zero_of_support (hH0 i) (ρ n) (by rw [hρ]; exact hfar.le)]
  have hcontH : ∀ n i, Continuous (H i ⋆[lsmul ℝ ℝ, volume] (ρ n).normed volume) := fun n i ↦
    (ρ n).hasCompactSupport_normed.continuous_convolution_right (lsmul ℝ ℝ)
      ((hH2 i).locallyIntegrable one_le_two) (ρ n).continuous_normed
  -- step 3: the ray inequality for `vₙ`
  set C := (ball x r)ᶜ with hCdef
  have hineq : ∀ n, ∫⁻ y in C, ENNReal.ofReal (v n y ^ 2) ≤
      ENNReal.ofReal (((R + ε n - r) * (R + ε n) / r) ^ 2) *
        ∑ i, ∫⁻ y in C, ENNReal.ofReal ((H i ⋆[lsmul ℝ ℝ, volume] (ρ n).normed volume) y ^ 2) := by
    intro n
    have h := lintegral_sq_compl_ball_le (hvc n) hr (by linarith [hεpos n]) (hv0 n)
    refine h.trans (le_of_eq ?_)
    congr 1
    rw [← lintegral_finsetSum _ fun i _ ↦ ((hcontH n i).measurable.pow_const 2).ennreal_ofReal]
    refine lintegral_congr fun y ↦ ?_
    rw [norm_sq_eq_sum_apply_single, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← hder n y i]
  -- limits
  have hL : Tendsto (fun n ↦ ∫⁻ y in C, ENNReal.ofReal (v n y ^ 2)) atTop
      (𝓝 (∫⁻ y in C, ENNReal.ofReal (u y ^ 2))) := by
    have h := tendsto_eLpNorm_convolution_sub (p := 2) one_le_two
      (by rw [ENNReal.ofReal_ofNat]; exact hu2) hρt
    rw [ENNReal.ofReal_ofNat] at h
    exact tendsto_setLIntegral_sq hu2 (fun n ↦ (hvc n).continuous.aestronglyMeasurable) h C
  have hHi : ∀ i, Tendsto (fun n ↦ ∫⁻ y in C,
      ENNReal.ofReal ((H i ⋆[lsmul ℝ ℝ, volume] (ρ n).normed volume) y ^ 2)) atTop
      (𝓝 (∫⁻ y in C, ENNReal.ofReal (H i y ^ 2))) := fun i ↦ by
    have h := tendsto_eLpNorm_convolution_sub (p := 2) one_le_two
      (by rw [ENNReal.ofReal_ofNat]; exact hH2 i) hρt
    rw [ENNReal.ofReal_ofNat] at h
    exact tendsto_setLIntegral_sq (hH2 i) (fun n ↦ (hcontH n i).aestronglyMeasurable) h C
  have hc : Tendsto (fun n ↦ ENNReal.ofReal (((R + ε n - r) * (R + ε n) / r) ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (((R - r) * R / r) ^ 2))) := by
    refine ENNReal.tendsto_ofReal ?_
    have := ((((hε.const_add R).sub_const r).mul (hε.const_add R)).div_const r).pow 2
    simpa using this
  have hc0 : ENNReal.ofReal (((R - r) * R / r) ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < (R - r) * R / r := by
      have : 0 < R - r := by linarith
      positivity
    positivity
  have hlim := le_of_tendsto_of_tendsto' hL
    (ENNReal.Tendsto.mul hc (Or.inl hc0) (tendsto_finsetSum _ fun i _ ↦ hHi i)
      (Or.inr ENNReal.ofReal_ne_top)) hineq
  -- identify the limits
  have hA : ball x R \ ball x r = ball x R ∩ C := by
    rw [hCdef, sdiff_eq]
  have hl : ∫⁻ y in C, ENNReal.ofReal (u y ^ 2) =
      ∫⁻ y in ball x R \ ball x r, ENNReal.ofReal (w y ^ 2) := by
    rw [hA, ← Measure.restrict_restrict measurableSet_ball,
      ← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun y ↦ ?_
    by_cases hy : y ∈ ball x R
    · rw [hudef, indicator_of_mem hy, indicator_of_mem hy]
    · rw [hudef, indicator_of_notMem hy, indicator_of_notMem hy]
      simp
  have hrt : ∑ i, ∫⁻ y in C, ENNReal.ofReal (H i y ^ 2) =
      ∫⁻ y in ball x R \ ball x r, ENNReal.ofReal (‖G y‖ ^ 2) := by
    rw [← lintegral_finsetSum' _ fun i _ ↦
      ((hH2 i).aestronglyMeasurable.restrict.aemeasurable.pow_const 2).ennreal_ofReal, hA,
      ← Measure.restrict_restrict measurableSet_ball,
      ← lintegral_indicator measurableSet_ball]
    refine lintegral_congr fun y ↦ ?_
    by_cases hy : y ∈ ball x R
    · rw [indicator_of_mem hy, norm_sq_eq_sum_inner_single,
        ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
      exact Finset.sum_congr rfl fun i _ ↦ by simp only [hHdef]; rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp only [hHdef]
      rw [indicator_of_notMem hy]
      simp
  rwa [hl, hrt] at hlim

/-- **Poincaré inequality on an annulus with zero outer trace**, with `C = 4`: for
`R / 2 ≤ r < R`, `∫_{B_R \ B_r} w² ≤ 4 (R - r)² ∫_{B_R \ B_r} |G|²`. -/
theorem poincare_annulus_zero_outer (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (E d)) (w : E d → ℝ) (G : E d → E d) (x : E d) (R r : ℝ),
      IsOpen U → MemH1Loc U w G → 0 < R → closedBall x R ⊆ U → R / 2 ≤ r → r < R →
      (∀ᵐ y ∂(volume.restrict (U \ ball x R)), w y = 0) →
      ∫⁻ y in ball x R \ ball x r, ENNReal.ofReal (w y ^ 2) ≤
        ENNReal.ofReal (C * (R - r) ^ 2) *
          ∫⁻ y in ball x R \ ball x r, ENNReal.ofReal (‖G y‖ ^ 2) := by
  refine ⟨4, by norm_num, fun U w G x R r hU hw hR hRU hr hrR h0 ↦ ?_⟩
  have hr0 : 0 < r := by linarith
  refine (lintegral_sq_annulus_le hU hw hr0 hrR hRU h0).trans ?_
  gcongr
  -- `((R - r) R / r)² ≤ 4 (R - r)²` since `R ≤ 2 r`
  have h1 : 0 ≤ (R - r) * R / r := by
    have : 0 ≤ R - r := by linarith
    positivity
  have h2 : (R - r) * R / r ≤ 2 * (R - r) := by
    rw [div_le_iff₀ hr0]
    nlinarith
  nlinarith

end EllipticBernoulli
