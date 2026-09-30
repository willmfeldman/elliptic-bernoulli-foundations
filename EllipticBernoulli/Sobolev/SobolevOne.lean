/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.SobolevGNS

/-!
# The Sobolev inequality on the support in dimension one

`sobolevSupport_one : SobolevSupport 1 1`, i.e. `‖g‖₂ ≤ |{g ≠ 0}| ‖g'‖₂` for compactly supported
`g ∈ H¹(ℝ)` with `g' = 0` on `{g = 0}`; and `exists_sobolevSupport` for every `d ≥ 1`.

Proof: mollify. For the smooth mollifications `gₙ`, the 1-D fundamental theorem of calculus
(`enorm_le_lintegral_fderiv_one`, via `HasCompactSupport.enorm_le_lintegral_Ici_deriv` along the
measure-preserving line `t ↦ t e₀`) gives `|gₙ| ≤ ‖gₙ'‖₁ ≤ ‖G‖₁`, and Young gives
`‖gₙ‖₁ ≤ ‖g‖₁`, so `‖gₙ‖₂² ≤ ‖G‖₁ ‖g‖₁`. In the limit `‖g‖₂² ≤ ‖G‖₁ ‖g‖₁ ≤ |S| ‖G‖₂ ‖g‖₂` by
Hölder on `S = {g ≠ 0}` (where `G` also vanishes).
-/

open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal NNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

/-- **1-D fundamental theorem of calculus.** A compactly supported `C¹` function on `E 1` is
bounded by the `L¹` norm of its derivative. -/
theorem enorm_le_lintegral_fderiv_one {φ : E 1 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hc : HasCompactSupport φ) (x : E 1) : ‖φ x‖ₑ ≤ ∫⁻ y, ‖fderiv ℝ φ y‖ₑ := by
  set e₀ : E 1 := EuclideanSpace.single 0 1 with he₀
  have he₀n : ‖e₀‖ = 1 := by simp [he₀]
  have he₀0 : e₀ ≠ 0 := by intro h; rw [h, norm_zero] at he₀n; exact zero_ne_one he₀n
  set L : ℝ → E 1 := fun t ↦ t • e₀ with hL
  have hLmp : MeasurePreserving L volume volume := by
    have := (PiLp.volume_preserving_toLp (Fin 1)).comp
      (volume_preserving_funUnique (Fin 1) ℝ).symm
    convert this using 1
    funext t
    ext i
    fin_cases i
    simp [hL, he₀]
  have hx : L (x 0) = x := by
    ext i; fin_cases i; simp [hL, he₀]
  set ψ : ℝ → ℝ := fun t ↦ φ (L t) with hψ
  have hLd : ∀ t, HasDerivAt L e₀ t := fun t ↦ by
    simpa using (hasDerivAt_id t).smul_const e₀
  have hψs : ContDiff ℝ 1 ψ := hφ.comp (contDiff_id.smul contDiff_const)
  have hψc : HasCompactSupport ψ := hc.comp_isClosedEmbedding (isClosedEmbedding_smul_left he₀0)
  have h1 := hψc.enorm_le_lintegral_Ici_deriv hψs (x 0)
  simp only [hψ, hx] at h1
  refine h1.trans ?_
  have hderiv : ∀ t, deriv ψ t = fderiv ℝ φ (L t) e₀ := fun t ↦
    (((hφ.differentiable one_ne_zero) (L t)).hasFDerivAt.comp_hasDerivAt t (hLd t)).deriv
  calc ∫⁻ y in Iic (x 0), ‖deriv (fun t ↦ φ (L t)) y‖ₑ
      ≤ ∫⁻ t, ‖deriv ψ t‖ₑ := setLIntegral_le_lintegral _ _
    _ ≤ ∫⁻ t, ‖fderiv ℝ φ (L t)‖ₑ := by
        refine lintegral_mono fun t ↦ ?_
        rw [hderiv]
        refine (ContinuousLinearMap.le_opENorm _ _).trans ?_
        rw [← ofReal_norm e₀, he₀n, ENNReal.ofReal_one, mul_one]
    _ = ∫⁻ y, ‖fderiv ℝ φ y‖ₑ :=
        hLmp.lintegral_comp (hφ.continuous_fderiv one_ne_zero).enorm.measurable

/-- Hölder on the support: `‖h‖₁ ≤ ‖h‖₂ |S|^{1/2}` if `h = 0` off `S`. -/
theorem eLpNorm_one_le_of_support {F : Type*} [NormedAddCommGroup F] {h : E 1 → F}
    {S : Set (E 1)} (hh : MemLp h 2) (h0 : ∀ x, x ∉ S → h x = 0) :
    eLpNorm h 1 volume ≤ eLpNorm h 2 volume * volume S ^ (1 / 2 : ℝ) := by
  set S' := toMeasurable volume S with hS'
  have hexp : 1 / ((1 : ℝ≥0∞)).toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / 2 := by norm_num
  have hsupp : Function.support h ⊆ S' := fun x hx ↦
    subset_toMeasurable _ _ (by by_contra h'; exact hx (h0 x h'))
  rw [← eLpNorm_restrict_eq_of_support_subset hh.aestronglyMeasurable hsupp]
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
    (by norm_num) hh.aestronglyMeasurable.restrict).trans ?_
  rw [Measure.restrict_apply_univ, hS', measure_toMeasurable, hexp]
  gcongr
  exact Measure.restrict_le_self

theorem sobolevSupport_one : SobolevSupport 1 1 := by
  intro g G hw hg hG hgc hGz
  set S := {x | g x ≠ 0} with hSdef
  have hSt : S ⊆ tsupport g := subset_tsupport g
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hgc.isCompact.measure_lt_top.ne
    (measure_mono hSt)
  have hGS : ∀ x, x ∉ S → G x = 0 := fun x hx ↦ hGz x (by simpa [hSdef] using hx)
  have hgS : ∀ x, x ∉ S → g x = 0 := fun x hx ↦ by simpa [hSdef] using hx
  have hG1 : MemLp G 1 := hG.mono_exponent_of_measure_support_ne_top hGS hSfin (by norm_num)
  have hg1 : MemLp g 1 := hg.mono_exponent_of_measure_support_ne_top hgS hSfin (by norm_num)
  have hgloc : LocallyIntegrable g volume := hg.locallyIntegrable (by norm_num)
  have hgint : Integrable g := memLp_one_iff_integrable.1 hg1
  let φb : ℕ → ContDiffBump (0 : E 1) := fun n ↦
    { rIn := 1 / (n + 1 : ℝ) / 2
      rOut := 1 / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφrOut : Tendsto (fun n ↦ (φb n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  set gn : ℕ → E 1 → ℝ := fun n ↦ g ⋆[lsmul ℝ ℝ, volume] (φb n).normed volume with hgn
  have hsmooth : ∀ n, ContDiff ℝ ∞ (gn n) := fun n ↦
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := lsmul ℝ ℝ) hgloc
      (φb n).contDiff_normed
  have hcs : ∀ n, HasCompactSupport (gn n) := fun n ↦
    HasCompactSupport.convolution (L := lsmul ℝ ℝ) hgc (φb n).hasCompactSupport_normed
  set A := eLpNorm G 1 volume with hA
  set Bg := eLpNorm g 1 volume with hBg
  have hAtop : A ≠ ⊤ := hG1.ne
  -- the sup bound
  have hsup : ∀ n x, ‖gn n x‖ₑ ≤ A := by
    intro n x
    refine (enorm_le_lintegral_fderiv_one ((hsmooth n).of_le (by simp)) (hcs n) x).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm
      ((hsmooth n).continuous_fderiv (by simp)).aestronglyMeasurable]
    have := eLpNorm_fderiv_convolution_le hw hgint (p := 1) le_rfl hG1 (φb n)
    simpa using this
  -- Young in `L¹`
  have hYoung : ∀ n, eLpNorm (gn n) 1 volume ≤ Bg := by
    intro n
    have := eLpNorm_convolution_le (p := 1) le_rfl ((φb n).nonneg_normed)
      (φb n).continuous_normed.aestronglyMeasurable (φb n).integral_normed
      (by rw [ENNReal.ofReal_one]; exact hg1)
    simpa [ENNReal.ofReal_one] using this
  -- the `L²` bound of the mollifications
  have hL2 : ∀ n, eLpNorm (gn n) 2 volume ≤ (A * Bg) ^ (1 / 2 : ℝ) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      (hsmooth n).continuous.aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat]
    gcongr
    calc ∫⁻ x, ‖gn n x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, A * ‖gn n x‖ₑ := by
          refine lintegral_mono fun x ↦ ?_
          rw [ENNReal.rpow_two, sq]
          gcongr
          exact hsup n x
      _ = A * ∫⁻ x, ‖gn n x‖ₑ := lintegral_const_mul' _ _ hAtop
      _ ≤ A * Bg := by
          rw [← eLpNorm_one_eq_lintegral_enorm (hsmooth n).continuous.aestronglyMeasurable]
          gcongr
          exact hYoung n
  -- the limit
  have hconv : Tendsto (fun n ↦ eLpNorm (gn n - g) 2 volume) atTop (𝓝 0) := by
    have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
      rw [ENNReal.ofReal_ofNat]; exact hg
    have := tendsto_eLpNorm_convolution_sub (p := 2) (by norm_num) hg' hφrOut
    rw [ENNReal.ofReal_ofNat] at this
    exact this
  have hbound : ∀ n, eLpNorm g 2 volume ≤ eLpNorm (gn n - g) 2 volume + (A * Bg) ^ (1 / 2 : ℝ) := by
    intro n
    have e : g = gn n - (gn n - g) := by abel
    calc eLpNorm g 2 volume = eLpNorm (gn n - (gn n - g)) 2 volume := by rw [← e]
      _ ≤ eLpNorm (gn n) 2 volume + eLpNorm (gn n - g) 2 volume :=
          eLpNorm_sub_le (by norm_num)
      _ ≤ (A * Bg) ^ (1 / 2 : ℝ) + eLpNorm (gn n - g) 2 volume := by gcongr; exact hL2 n
      _ = _ := add_comm _ _
  have hlim : eLpNorm g 2 volume ≤ (A * Bg) ^ (1 / 2 : ℝ) := by
    have ht : Tendsto (fun n ↦ eLpNorm (gn n - g) 2 volume + (A * Bg) ^ (1 / 2 : ℝ)) atTop
        (𝓝 (0 + (A * Bg) ^ (1 / 2 : ℝ))) := hconv.add tendsto_const_nhds
    rw [zero_add] at ht
    exact ge_of_tendsto' ht hbound
  set a := eLpNorm g 2 volume with ha
  have hsq : a ^ 2 ≤ A * Bg := by
    have h2 : ((A * Bg) ^ (1 / 2 : ℝ)) ^ 2 = A * Bg := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    calc a ^ 2 ≤ ((A * Bg) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
      _ = A * Bg := h2
  -- Hölder on `S`
  set s := volume S ^ (1 / 2 : ℝ) with hs
  have hss : s * s = volume S := by
    rw [hs, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
  have hkey : a * a ≤ volume S * eLpNorm G 2 volume * a := by
    calc a * a = a ^ 2 := (sq a).symm
      _ ≤ A * Bg := hsq
      _ ≤ (eLpNorm G 2 volume * s) * (a * s) := by
          gcongr
          · exact eLpNorm_one_le_of_support hG hGS
          · exact eLpNorm_one_le_of_support hg hgS
      _ = s * s * eLpNorm G 2 volume * a := by ring
      _ = _ := by rw [hss]
  simp only [ENNReal.coe_one, one_mul, Nat.cast_one, div_one, ENNReal.rpow_one]
  by_cases ha0 : a = 0
  · rw [ha0]; simp
  · exact (ENNReal.mul_le_mul_iff_left ha0 hg.ne).1 hkey

theorem exists_sobolevSupport {d : ℕ} (hd : 1 ≤ d) : ∃ CS : ℝ≥0, SobolevSupport d CS := by
  rcases Nat.lt_or_ge d 2 with h | h
  · obtain rfl : d = 1 := by omega
    exact ⟨1, sobolevSupport_one⟩
  · exact ⟨_, sobolevSupport_of_two_le h⟩

end EllipticBernoulli
