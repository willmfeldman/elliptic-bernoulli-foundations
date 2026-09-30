/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.Lattice
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A Sobolev inequality for compactly supported `H¹` functions

`eLpNorm_le_sobolev_support` (`d ≥ 2`): if `g ∈ L²(ℝᵈ)` has compact support and an `L²` weak
gradient `G` on `ℝᵈ` vanishing where `g` vanishes, then
`‖g‖_{L²} ≤ C_d |{g ≠ 0}|^{1/d} ‖G‖_{L²}`.

Proof: mollify, apply Mathlib's Gagliardo–Nirenberg–Sobolev inequality
(`eLpNorm_le_eLpNorm_fderiv_of_eq_inner`) with `p = 2d/(d+2)`, `p* = 2`, bound the `Lᵖ` norm
of the mollified gradient by Young's inequality componentwise, pass to the limit in `L²`, and
finish with Hölder's inequality on `{g ≠ 0}`.
-/

open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal NNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The operator norm of a functional on `ℝᵈ` is at most the sum of its values on the standard
basis (in absolute value). -/
theorem norm_le_sum_abs_apply_basisFun (L : E d →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, |L (EuclideanSpace.basisFun (Fin d) ℝ i)| := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) fun v ↦ ?_
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  have hv : v = ∑ i, inner ℝ (b i) v • b i := (b.sum_repr' v).symm
  have hLv : L v = ∑ i, inner ℝ (b i) v * L (b i) := by
    conv_lhs => rw [hv]
    simp [map_sum, map_smul, smul_eq_mul]
  rw [hLv, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [abs_mul, mul_comm]
  gcongr
  calc |inner ℝ (b i) v| ≤ ‖b i‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ = ‖v‖ := by rw [b.orthonormal.1 i, one_mul]

/-- The GNS exponent `p = 2d/(d+2)` whose Sobolev conjugate is `2`. -/
noncomputable def gnsExp (d : ℕ) : ℝ≥0 := ⟨2 * d / (d + 2), by positivity⟩

theorem gnsExp_coe (d : ℕ) : (gnsExp d : ℝ) = 2 * d / (d + 2) := rfl

theorem one_le_gnsExp (hd : 2 ≤ d) : 1 ≤ gnsExp d := by
  rw [← NNReal.coe_le_coe, gnsExp_coe, NNReal.coe_one, one_le_div (by positivity)]
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

theorem gnsExp_le_two : gnsExp d ≤ 2 := by
  rw [← NNReal.coe_le_coe, gnsExp_coe, div_le_iff₀ (by positivity)]
  push_cast
  linarith

/-- The Sobolev constant `C_GNS(d, p) · d`. -/
noncomputable def sobConst (d : ℕ) : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (E d)) (gnsExp d) * d

theorem finrank_E : Module.finrank ℝ (E d) = d := finrank_euclideanSpace_fin

/-- The `Lᵖ` norm of the derivative of a mollification is at most `d ‖G‖_{Lᵖ}`. -/
theorem eLpNorm_fderiv_convolution_le {g : E d → ℝ} {G : E d → E d}
    (hw : HasWeakGradient univ g G) (hgint : Integrable g) {p : ℝ≥0} (hp1 : 1 ≤ p)
    (hGp : MemLp G p) (ρ : ContDiffBump (0 : E d)) :
    eLpNorm (fderiv ℝ (g ⋆[lsmul ℝ ℝ, volume] ρ.normed volume)) p volume ≤
      d * eLpNorm G p volume := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  set Gi : Fin d → E d → ℝ := fun i y ↦ inner ℝ (G y) (b i) with hGi
  set gn := g ⋆[lsmul ℝ ℝ, volume] ρ.normed volume with hgn
  have hGip : ∀ i, MemLp (Gi i) p := fun i ↦ hGp.inner_const (b i)
  have hGiG : ∀ i, eLpNorm (Gi i) p volume ≤ eLpNorm G p volume := fun i ↦
    eLpNorm_mono (hGip i).aestronglyMeasurable fun x ↦ by
      calc ‖Gi i x‖ = |inner ℝ (G x) (b i)| := Real.norm_eq_abs _
        _ ≤ ‖G x‖ * ‖b i‖ := abs_real_inner_le_norm _ _
        _ = ‖G x‖ := by rw [b.orthonormal.1 i, mul_one]
  have hwhole : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ univ →
      ∀ v : E d, ∫ x, g x * fderiv ℝ φ x v = -∫ x, inner ℝ (G x) v * φ x :=
    fun φ h1 h2 h3 v ↦ hw.integral_eq h1 h2 h3 v
  have hder : ∀ x i, fderiv ℝ gn x (b i) = (Gi i ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) x := by
    intro x i
    have := fderiv_convolution_indicator_eq MeasurableSet.univ hgint.integrableOn hwhole ρ
      (b i) (subset_univ (closedBall x ρ.rOut))
    rw [indicator_univ, indicator_univ] at this
    exact this
  have hρnn : (0 : E d → ℝ) ≤ ρ.normed volume := fun x ↦ ρ.nonneg_normed x
  have hρm : AEStronglyMeasurable (ρ.normed volume) volume :=
    (ρ.contDiff_normed (n := 1)).continuous.aestronglyMeasurable
  have hY : ∀ i, eLpNorm (fun x ↦ |(Gi i ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) x|) p volume ≤
      eLpNorm G p volume := by
    intro i
    have hGi' : MemLp (Gi i) (ENNReal.ofReal (p : ℝ)) volume := by
      rw [ENNReal.ofReal_coe_nnreal]; exact hGip i
    have h := eLpNorm_convolution_le (p := p) (by exact_mod_cast hp1) hρnn hρm
      ρ.integral_normed hGi'
    rw [ENNReal.ofReal_coe_nnreal] at h
    have e : eLpNorm (fun x ↦ |(Gi i ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) x|) p volume =
        eLpNorm (Gi i ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) p volume := by
      conv_rhs => rw [← eLpNorm_norm _ ((hGip i).aestronglyMeasurable.convolution _ hρm)]
      simp only [Real.norm_eq_abs]
    rw [e]
    exact h.trans (hGiG i)
  calc eLpNorm (fderiv ℝ gn) p volume
      ≤ eLpNorm (∑ i, fun x ↦ |(Gi i ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) x|) p volume := by
        refine eLpNorm_mono (measurable_fderiv ℝ gn).aestronglyMeasurable fun x ↦ ?_
        rw [Finset.sum_apply, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)]
        refine (norm_le_sum_abs_apply_basisFun _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ ↦ by rw [hder]
    _ ≤ ∑ i, eLpNorm (fun x ↦ |(Gi i ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) x|) p volume :=
        eLpNorm_sum_le (by exact_mod_cast hp1)
    _ ≤ ∑ _i : Fin d, eLpNorm G p volume := Finset.sum_le_sum fun i _ ↦ hY i
    _ = d * eLpNorm G p volume := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem gns_exponent_relation (hd : 2 ≤ d) :
    ((2 : ℝ≥0) : ℝ)⁻¹ = (gnsExp d : ℝ)⁻¹ - (Module.finrank ℝ (E d) : ℝ)⁻¹ := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [finrank_E, gnsExp_coe, NNReal.coe_ofNat]
  field_simp
  ring

/-- **Sobolev inequality on the support** (`d ≥ 2`). If `g ∈ L²(ℝᵈ)` has compact support and
an `L²` weak gradient `G` on `ℝᵈ` with `G = 0` where `g = 0`, then
`‖g‖_{L²} ≤ C_d |{g ≠ 0}|^{1/d} ‖G‖_{L²}`. -/
theorem eLpNorm_le_sobolev_support (hd : 2 ≤ d) {g : E d → ℝ} {G : E d → E d}
    (hw : HasWeakGradient univ g G) (hg : MemLp g 2) (hG : MemLp G 2)
    (hgc : HasCompactSupport g) (hGz : ∀ x, g x = 0 → G x = 0) :
    eLpNorm g 2 volume ≤
      sobConst d * volume {x | g x ≠ 0} ^ (1 / (d : ℝ)) * eLpNorm G 2 volume := by
  set p := gnsExp d with hpdef
  have hp1 : 1 ≤ p := one_le_gnsExp hd
  have hp2 : p ≤ 2 := gnsExp_le_two
  set S := {x | g x ≠ 0} with hSdef
  have hSt : S ⊆ tsupport g := subset_tsupport g
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hgc.isCompact.measure_lt_top.ne
    (measure_mono hSt)
  have hGS : ∀ x, x ∉ S → G x = 0 := fun x hx ↦ hGz x (by simpa [hSdef] using hx)
  have hGp : MemLp G p :=
    hG.mono_exponent_of_measure_support_ne_top hGS hSfin (by exact_mod_cast hp2)
  have hgloc : LocallyIntegrable g volume := hg.locallyIntegrable (by norm_num)
  have hgint : Integrable g :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport g)).1
      (hgloc.integrableOn_isCompact hgc.isCompact)
  let φb : ℕ → ContDiffBump (0 : E d) := fun n ↦
    { rIn := 1 / (n + 1 : ℝ) / 2
      rOut := 1 / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφrOut : Tendsto (fun n ↦ (φb n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  set gn : ℕ → E d → ℝ := fun n ↦ g ⋆[lsmul ℝ ℝ, volume] (φb n).normed volume with hgn
  have hsmooth : ∀ n, ContDiff ℝ ∞ (gn n) := fun n ↦
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := lsmul ℝ ℝ) hgloc
      (φb n).contDiff_normed
  have hcs : ∀ n, HasCompactSupport (gn n) := fun n ↦
    HasCompactSupport.convolution (L := lsmul ℝ ℝ) hgc (φb n).hasCompactSupport_normed
  set K := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (E d)) p with hK
  have hGNS : ∀ n, eLpNorm (gn n) 2 volume ≤ (K : ℝ≥0∞) * (d * eLpNorm G p volume) := by
    intro n
    have h := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (μ := volume) (p' := 2)
      ((hsmooth n).of_le (by simp)) (hcs n) hp1 (by rw [finrank_E]; omega)
      (gns_exponent_relation hd)
    have h2 := eLpNorm_fderiv_convolution_le hw hgint hp1 hGp (φb n)
    calc eLpNorm (gn n) 2 volume = eLpNorm (gn n) ((2 : ℝ≥0) : ℝ≥0∞) volume := rfl
      _ ≤ (K : ℝ≥0∞) * eLpNorm (fderiv ℝ (gn n)) p volume := h
      _ ≤ (K : ℝ≥0∞) * (d * eLpNorm G p volume) := by gcongr
  have hconv : Tendsto (fun n ↦ eLpNorm (gn n - g) 2 volume) atTop (𝓝 0) := by
    have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) volume := by
      rw [ENNReal.ofReal_ofNat]; exact hg
    have := tendsto_eLpNorm_convolution_sub (p := 2) (by norm_num) hg' hφrOut
    rw [ENNReal.ofReal_ofNat] at this
    exact this
  have hbound : ∀ n, eLpNorm g 2 volume ≤ eLpNorm (gn n - g) 2 volume +
      (K : ℝ≥0∞) * (d * eLpNorm G p volume) := by
    intro n
    have e : g = gn n - (gn n - g) := by abel
    calc eLpNorm g 2 volume = eLpNorm (gn n - (gn n - g)) 2 volume := by rw [← e]
      _ ≤ eLpNorm (gn n) 2 volume + eLpNorm (gn n - g) 2 volume :=
          eLpNorm_sub_le (by norm_num)
      _ ≤ (K : ℝ≥0∞) * (d * eLpNorm G p volume) + eLpNorm (gn n - g) 2 volume := by
          gcongr
          exact hGNS n
      _ = _ := add_comm _ _
  have hlim : eLpNorm g 2 volume ≤ (K : ℝ≥0∞) * (d * eLpNorm G p volume) := by
    have ht : Tendsto (fun n ↦ eLpNorm (gn n - g) 2 volume +
        (K : ℝ≥0∞) * (d * eLpNorm G p volume)) atTop
        (𝓝 (0 + (K : ℝ≥0∞) * (d * eLpNorm G p volume))) := hconv.add tendsto_const_nhds
    rw [zero_add] at ht
    exact ge_of_tendsto' ht hbound
  set S' := toMeasurable volume S with hS'
  have hGsupp : Function.support G ⊆ S' := fun x hx ↦
    subset_toMeasurable _ _ (by by_contra h; exact hx (hGS x h))
  have hexp : 1 / ((p : ℝ≥0∞)).toReal - 1 / (2 : ℝ≥0∞).toReal = 1 / (d : ℝ) := by
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    rw [ENNReal.coe_toReal, hpdef, gnsExp_coe, ENNReal.toReal_ofNat]
    field_simp
    ring
  have hHolder : eLpNorm G p volume ≤ eLpNorm G 2 volume * volume S ^ (1 / (d : ℝ)) := by
    rw [← eLpNorm_restrict_eq_of_support_subset hG.aestronglyMeasurable hGsupp]
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := (p : ℝ≥0∞)) (q := 2)
      (by exact_mod_cast hp2) hG.aestronglyMeasurable.restrict).trans ?_
    rw [Measure.restrict_apply_univ, hS', measure_toMeasurable, hexp]
    gcongr
    exact Measure.restrict_le_self
  calc eLpNorm g 2 volume ≤ (K : ℝ≥0∞) * (d * eLpNorm G p volume) := hlim
    _ ≤ (K : ℝ≥0∞) * (d * (eLpNorm G 2 volume * volume S ^ (1 / (d : ℝ)))) := by
        gcongr
    _ = sobConst d * volume {x | g x ≠ 0} ^ (1 / (d : ℝ)) * eLpNorm G 2 volume := by
        rw [sobConst, ENNReal.coe_mul, ENNReal.coe_natCast, ← hK]
        ring

end EllipticBernoulli

namespace EllipticBernoulli

variable {d : ℕ}

/-- The Sobolev inequality on the support, with constant `C`, as a property of the dimension. -/
def SobolevSupport (d : ℕ) (C : ℝ≥0) : Prop :=
  ∀ (g : E d → ℝ) (G : E d → E d), HasWeakGradient univ g G → MemLp g 2 → MemLp G 2 →
    HasCompactSupport g → (∀ x, g x = 0 → G x = 0) →
    eLpNorm g 2 volume ≤ C * volume {x | g x ≠ 0} ^ (1 / (d : ℝ)) * eLpNorm G 2 volume

theorem sobolevSupport_of_two_le (hd : 2 ≤ d) : SobolevSupport d (sobConst d) :=
  fun _ _ hw hg hG hgc hGz ↦ eLpNorm_le_sobolev_support hd hw hg hG hgc hGz

/-- `‖f‖²_{L²} = ∫ ‖f‖²`. -/
theorem toReal_eLpNorm_two_sq {F : Type*} [NormedAddCommGroup F] {f : E d → F}
    (hf : MemLp f 2) : (eLpNorm f 2 volume).toReal ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h0 : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ≥0∞).toReal := integral_nonneg fun x ↦ by positivity
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h0 _), ← Real.rpow_natCast,
    ← Real.rpow_mul h0]
  simp only [ENNReal.toReal_ofNat, Nat.cast_ofNat]
  rw [inv_mul_cancel₀ (by norm_num), Real.rpow_one]
  congr 1
  funext x
  exact Real.rpow_two _

/-- **Sobolev inequality on the support, integral form.** -/
theorem integral_sq_le_of_sobolevSupport {C : ℝ≥0} (hS : SobolevSupport d C) {g : E d → ℝ}
    {G : E d → E d} (hw : HasWeakGradient univ g G) (hg : MemLp g 2) (hG : MemLp G 2)
    (hgc : HasCompactSupport g) (hGz : ∀ x, g x = 0 → G x = 0) :
    ∫ x, g x ^ 2 ≤ (C : ℝ) ^ 2 * ((volume {x | g x ≠ 0}).toReal ^ (1 / (d : ℝ))) ^ 2 *
      ∫ x, ‖G x‖ ^ 2 := by
  have h := hS g G hw hg hG hgc hGz
  have hfin : volume {x | g x ≠ 0} ≠ ⊤ :=
    ne_top_of_le_ne_top hgc.isCompact.measure_lt_top.ne (measure_mono (subset_tsupport g))
  have hRHS : (C : ℝ≥0∞) * volume {x | g x ≠ 0} ^ (1 / (d : ℝ)) * eLpNorm G 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hfin)) hG.ne
  have h2 := ENNReal.toReal_mono hRHS h
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.coe_toReal,
    ← ENNReal.toReal_rpow] at h2
  have h3 := pow_le_pow_left₀ ENNReal.toReal_nonneg h2 2
  rw [toReal_eLpNorm_two_sq hg, mul_pow, mul_pow, toReal_eLpNorm_two_sq hG] at h3
  simpa [Real.norm_eq_abs, sq_abs] using h3

end EllipticBernoulli
