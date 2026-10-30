/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.TwoPhase
import EllipticBernoulli.TwoPhase.Regularity
import EllipticBernoulli.TwoPhase.Defs
import EllipticBernoulli.Sobolev.Lipschitz
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The free boundary condition for two-plane minimizers

If the two-plane function `u(x) = a (x·e + c)⁺ - b (x·e + c)⁻`, with `‖e‖ = 1`
and `a, b > 0`, is a local minimizer of `J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ`, then
`a² - b² = 1`.

* `sq_sub_sq_eq_one_of_isLocalEnergyMinimizer_twoPlane`: the statement.

## Proof

Write `s = x·e + c` and let `y` be the remaining coordinates of `x` after a reflection taking
`e` to the first coordinate vector (`coord`). Let `ζ` be a bump on `ℝ` with `ζ = 1` on
`[-1, 1]`, `θ` a bump on `ℝ^{d-1}`, `η = ζ(s) θ(y)`, and for `|t| < 1/2` compare `u` with the
competitor `v_t = prof(s - t η)`, `prof(σ) = a σ⁺ - b σ⁻`, which equals `u` outside a ball.
Away from the null set `{s = 0} ∪ {s = t θ(y)}`,
`∇v_t = κ_t (e - t ∇η)` with `κ_t ∈ {a, b}` the slope at `σ = s - t η`, and `e·∇η = ζ'(s) θ(y)`.
The energy difference `J(v_t) - J(u)` is therefore `∫ F_t(y, s) + t² ∫ κ_t² |∇η|²`, where the
slab integrand `F_t` (`slabF`) is computed by Fubini in `(y, s)`:
* the change of slope and of phase is supported in the thin region between `s = 0` and
  `s = t θ(y)`, of signed volume `t Θ`, `Θ = ∫ θ`, and contributes `t Θ (b² - a² - 1)`;
* the term `-2t κ_t² ζ'(s) θ(y)` lives where `|s| ≥ 1`, where `κ_t = κ_0`, and contributes
  `-2t Θ (b² - a²)` because `∫_0^∞ ζ' = -1` and `∫_{-∞}^0 ζ' = 1`.
So `0 ≤ J(v_t) - J(u) ≤ t Θ (a² - b² - 1) + C t²` for both signs of `t`, whence `a² = b² + 1`.
The minimality hypothesis is applied to `u` itself; the coordinates enter only inside the
integrals, through the measure-preserving map `coord`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped NNReal Gradient ContDiff

namespace EllipticBernoulli

/-! ### The one-dimensional profile -/

/-- The profile `σ ↦ a σ⁺ - b σ⁻` of a two-plane function. -/
private noncomputable def prof (a b σ : ℝ) : ℝ := a * max σ 0 - b * max (-σ) 0

/-- The slope of the profile: `a` for `σ > 0`, `b` for `σ ≤ 0`. -/
private noncomputable def slope (a b σ : ℝ) : ℝ := if 0 < σ then a else b

/-- The indicator of `σ > 0`. -/
private noncomputable def ind (σ : ℝ) : ℝ := if 0 < σ then 1 else 0

private theorem slope_of_pos {a b σ : ℝ} (h : 0 < σ) : slope a b σ = a := by
  simp [slope, h]

private theorem slope_of_nonpos {a b σ : ℝ} (h : σ ≤ 0) : slope a b σ = b := by
  simp [slope, not_lt.2 h]

private theorem ind_of_pos {σ : ℝ} (h : 0 < σ) : ind σ = 1 := by
  simp [ind, h]

private theorem ind_of_nonpos {σ : ℝ} (h : σ ≤ 0) : ind σ = 0 := by
  simp [ind, not_lt.2 h]

private theorem measurable_slope (a b : ℝ) : Measurable (slope a b) :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

private theorem measurable_ind : Measurable ind :=
  Measurable.ite measurableSet_Ioi measurable_const measurable_const

private theorem slope_sq_le (a b σ : ℝ) : slope a b σ ^ 2 ≤ a ^ 2 + b ^ 2 := by
  unfold slope; split_ifs <;> nlinarith [sq_nonneg a, sq_nonneg b]

private theorem abs_ind_le (σ : ℝ) : |ind σ| ≤ 1 := by
  unfold ind; split_ifs <;> simp

private theorem prof_pos_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (σ : ℝ) :
    0 < prof a b σ ↔ 0 < σ := by
  unfold prof
  rcases le_or_gt σ 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    constructor
    · intro h'; nlinarith
    · intro h'; linarith
  · rw [max_eq_left h.le, max_eq_right (neg_nonpos.2 h.le)]
    simp only [mul_zero, sub_zero]
    exact ⟨fun _ ↦ h, fun _ ↦ mul_pos ha h⟩

/-- Away from `0` the profile is linear with slope `slope a b σ`. -/
private theorem prof_eventuallyEq {a b σ : ℝ} (hσ : σ ≠ 0) :
    prof a b =ᶠ[𝓝 σ] fun τ ↦ slope a b σ * τ := by
  rcases lt_or_gt_of_ne hσ with h | h
  · filter_upwards [eventually_lt_nhds h] with τ hτ
    rw [slope_of_nonpos h.le, prof, max_eq_right hτ.le, max_eq_left (neg_nonneg.2 hτ.le)]
    ring
  · filter_upwards [eventually_gt_nhds h] with τ hτ
    rw [slope_of_pos h, prof, max_eq_left hτ.le, max_eq_right (neg_nonpos.2 hτ.le)]
    ring

private theorem lipschitzWith_prof (a b : ℝ) : LipschitzWith (‖a‖₊ + ‖b‖₊) (prof a b) := by
  refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
  simp only [Real.dist_eq, NNReal.coe_add, coe_nnnorm, Real.norm_eq_abs, prof]
  have h1 : |max s 0 - max t 0| ≤ |s - t| := abs_max_sub_max_le_abs s t 0
  have h2 : |max (-s) 0 - max (-t) 0| ≤ |s - t| := by
    have := abs_max_sub_max_le_abs (-s) (-t) 0
    rwa [neg_sub_neg, abs_sub_comm t s] at this
  calc |a * max s 0 - b * max (-s) 0 - (a * max t 0 - b * max (-t) 0)|
      = |a * (max s 0 - max t 0) - b * (max (-s) 0 - max (-t) 0)| := by ring_nf
    _ ≤ |a * (max s 0 - max t 0)| + |b * (max (-s) 0 - max (-t) 0)| := abs_sub _ _
    _ = |a| * |max s 0 - max t 0| + |b| * |max (-s) 0 - max (-t) 0| := by
        rw [abs_mul, abs_mul]
    _ ≤ |a| * |s - t| + |b| * |s - t| := by gcongr
    _ = (|a| + |b|) * |s - t| := by ring

/-! ### The computation in the slab -/

section Slab

variable {n : ℕ}

/-- Graphs over `ℝⁿ` are null in `ℝⁿ × ℝ`. -/
private theorem volume_graph_eq_zero {g : (Fin n → ℝ) → ℝ} (hg : Measurable g) :
    volume {q : (Fin n → ℝ) × ℝ | q.2 = g q.1} = 0 := by
  rw [Measure.volume_eq_prod]
  refine (Measure.measure_prod_null
    (measurableSet_eq_fun measurable_snd (hg.comp measurable_fst))).2
    (Eventually.of_forall fun y ↦ ?_)
  have : Prod.mk y ⁻¹' {q : (Fin n → ℝ) × ℝ | q.2 = g q.1} = {g y} := by ext; simp
  simp [this]

/-- The integrand of the energy difference, in coordinates `q = (y, s)` with `s` the signed
distance to the interface: `κ_t² - κ_0² + 1_{σ > 0} - 1_{s > 0} - 2t κ_t² ζ'(s) θ(y)`, where
`σ = s - t ζ(s) θ(y)` and `κ_t = slope a b σ`. -/
private noncomputable def slabF (a b t : ℝ) (ζ : ℝ → ℝ) (θ : (Fin n → ℝ) → ℝ)
    (q : (Fin n → ℝ) × ℝ) : ℝ :=
  slope a b (q.2 - t * (ζ q.2 * θ q.1)) ^ 2 - slope a b q.2 ^ 2 +
    ind (q.2 - t * (ζ q.2 * θ q.1)) - ind q.2 -
    2 * t * slope a b (q.2 - t * (ζ q.2 * θ q.1)) ^ 2 * (deriv ζ q.2 * θ q.1)

private theorem deriv_eq_zero_of_abs_lt {ζ : ℝ → ℝ} (hζ1 : ∀ s, |s| < 1 → ζ s = 1) {s : ℝ}
    (hs : |s| < 1) : deriv ζ s = 0 := by
  have hev : ζ =ᶠ[𝓝 s] fun _ ↦ 1 := by
    have hopen : IsOpen {s : ℝ | |s| < 1} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds hs] with r hr using hζ1 r hr
  rw [hev.deriv_eq, deriv_const]

/-- `∫ κ(s)² ζ'(s) ds = b² - a²`. -/
private theorem integral_slope_sq_mul_deriv (a b : ℝ) {ζ : ℝ → ℝ} (hζc : ContDiff ℝ 1 ζ)
    (hζs : HasCompactSupport ζ) (hζ0 : ζ 0 = 1) :
    ∫ s, slope a b s ^ 2 * deriv ζ s = b ^ 2 - a ^ 2 := by
  have hint : Integrable (deriv ζ) :=
    (hζc.continuous_deriv le_rfl).integrable_of_hasCompactSupport hζs.deriv
  have hbd : ∀ s, ‖slope a b s ^ 2‖ ≤ a ^ 2 + b ^ 2 := fun s ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact slope_sq_le a b s
  have hint' : Integrable fun s ↦ slope a b s ^ 2 * deriv ζ s :=
    hint.bdd_mul ((measurable_slope a b).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall hbd)
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint'.integrableOn hint'.integrableOn]
  have h1 : ∫ s in Iic (0 : ℝ), slope a b s ^ 2 * deriv ζ s = b ^ 2 * ∫ s in Iic (0 : ℝ),
      deriv ζ s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Iic fun s hs ↦ ?_
    rw [slope_of_nonpos hs]
  have h2 : ∫ s in Ioi (0 : ℝ), slope a b s ^ 2 * deriv ζ s = a ^ 2 * ∫ s in Ioi (0 : ℝ),
      deriv ζ s := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ ?_
    rw [slope_of_pos hs]
  rw [h1, h2, hζs.integral_Iic_deriv_eq hζc 0, hζs.integral_Ioi_deriv_eq hζc 0, hζ0]
  ring

/-- Pointwise form of the slab integrand off the null set `{s = 0} ∪ {s = t θ(y)}`. -/
private theorem slabF_eq {a b : ℝ} {ζ : ℝ → ℝ} {θ : (Fin n → ℝ) → ℝ}
    (hζ1 : ∀ s, |s| < 1 → ζ s = 1) (hζ0 : ∀ s, 0 ≤ ζ s) (hζle : ∀ s, ζ s ≤ 1)
    (hθ0 : ∀ y, 0 ≤ θ y) (hθle : ∀ y, θ y ≤ 1) {t : ℝ} (ht : |t| < 1 / 2)
    {q : (Fin n → ℝ) × ℝ} (hs0 : q.2 ≠ 0) (hst : q.2 ≠ t * θ q.1) :
    slabF a b t ζ θ q =
      (b ^ 2 - a ^ 2 - 1) *
        ((regionBetween (fun _ ↦ (0 : ℝ)) (fun y ↦ t * θ y) univ).indicator 1 q -
          (regionBetween (fun y ↦ t * θ y) (fun _ ↦ (0 : ℝ)) univ).indicator 1 q) +
      -2 * t * (θ q.1 * (slope a b q.2 ^ 2 * deriv ζ q.2)) := by
  obtain ⟨y, s⟩ := q
  simp only at hs0 hst ⊢
  have hmp : ((y, s) ∈ regionBetween (fun _ ↦ (0 : ℝ)) (fun y ↦ t * θ y) univ) ↔
      0 < s ∧ s < t * θ y := by simp [regionBetween]
  have hmm : ((y, s) ∈ regionBetween (fun y ↦ t * θ y) (fun _ ↦ (0 : ℝ)) univ) ↔
      t * θ y < s ∧ s < 0 := by simp [regionBetween]
  have hζθ0 : 0 ≤ ζ s * θ y := mul_nonneg (hζ0 s) (hθ0 y)
  have hζθ1 : ζ s * θ y ≤ 1 :=
    (mul_le_mul (hζle s) (hθle y) (hθ0 y) zero_le_one).trans_eq (one_mul 1)
  have hb : |t * (ζ s * θ y)| < 1 / 2 := by
    rw [abs_mul, abs_of_nonneg hζθ0]
    nlinarith [abs_nonneg t]
  have hb' : |t * θ y| < 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (hθ0 y)]
    nlinarith [abs_nonneg t, hθle y]
  have hb1 := abs_lt.1 hb
  have hb1' := abs_lt.1 hb'
  unfold slabF
  simp only
  rcases lt_or_ge |s| 1 with hs1 | hs1
  · have hz := hζ1 s hs1
    rw [deriv_eq_zero_of_abs_lt hζ1 hs1, hz, one_mul]
    rcases lt_or_gt_of_ne hs0 with hneg | hpos <;> rcases lt_or_gt_of_ne hst with h2 | h2
    · rw [slope_of_nonpos (by linarith), slope_of_nonpos hneg.le, ind_of_nonpos (by linarith),
        ind_of_nonpos hneg.le, indicator_of_notMem (fun h ↦ by linarith [(hmp.1 h).1]),
        indicator_of_notMem (fun h ↦ by linarith [(hmm.1 h).1])]
      ring
    · rw [slope_of_pos (by linarith), slope_of_nonpos hneg.le, ind_of_pos (by linarith),
        ind_of_nonpos hneg.le, indicator_of_notMem (fun h ↦ by linarith [(hmp.1 h).1]),
        indicator_of_mem (hmm.2 ⟨h2, hneg⟩)]
      simp only [Pi.one_apply]
      ring
    · rw [slope_of_nonpos (by linarith), slope_of_pos hpos, ind_of_nonpos (by linarith),
        ind_of_pos hpos, indicator_of_mem (hmp.2 ⟨hpos, h2⟩),
        indicator_of_notMem (fun h ↦ by linarith [(hmm.1 h).2])]
      simp only [Pi.one_apply]
      ring
    · rw [slope_of_pos (by linarith), slope_of_pos hpos, ind_of_pos (by linarith),
        ind_of_pos hpos, indicator_of_notMem (fun h ↦ by linarith [(hmp.1 h).2]),
        indicator_of_notMem (fun h ↦ by linarith [(hmm.1 h).2])]
      ring
  · rcases le_abs'.1 hs1 with h | h
    · rw [slope_of_nonpos (by linarith), slope_of_nonpos (by linarith),
        ind_of_nonpos (by linarith), ind_of_nonpos (by linarith),
        indicator_of_notMem (fun h' ↦ by linarith [(hmp.1 h').1]),
        indicator_of_notMem (fun h' ↦ by linarith [(hmm.1 h').1])]
      ring
    · rw [slope_of_pos (by linarith), slope_of_pos (by linarith),
        ind_of_pos (by linarith), ind_of_pos (by linarith),
        indicator_of_notMem (fun h' ↦ by linarith [(hmp.1 h').2]),
        indicator_of_notMem (fun h' ↦ by linarith [(hmm.1 h').2])]
      ring

/-- **The slab computation.** For `|t| < 1/2`, the slab integrand is integrable on `ℝⁿ × ℝ` and
`∫ F_t = t Θ (a² - b² - 1)` with `Θ = ∫ θ`. -/
private theorem integrable_and_integral_slabF (a b : ℝ) {ζ : ℝ → ℝ} {θ : (Fin n → ℝ) → ℝ}
    (hζc : ContDiff ℝ 1 ζ) (hζs : HasCompactSupport ζ) (hζ1 : ∀ s, |s| < 1 → ζ s = 1)
    (hζ0 : ∀ s, 0 ≤ ζ s) (hζle : ∀ s, ζ s ≤ 1) (hθc : Continuous θ) (hθi : Integrable θ)
    (hθ0 : ∀ y, 0 ≤ θ y) (hθle : ∀ y, θ y ≤ 1) {t : ℝ} (ht : |t| < 1 / 2) :
    Integrable (slabF a b t ζ θ) ∧
      ∫ q, slabF a b t ζ θ q = t * (∫ y, θ y) * (a ^ 2 - b ^ 2 - 1) := by
  set Θ := ∫ y, θ y with hΘ
  have hΘ0 : 0 ≤ Θ := integral_nonneg hθ0
  have hθm : Measurable θ := hθc.measurable
  set Rp := regionBetween (fun _ ↦ (0 : ℝ)) (fun y ↦ t * θ y) univ with hRp
  set Rm := regionBetween (fun y ↦ t * θ y) (fun _ ↦ (0 : ℝ)) univ with hRm
  have hRpm : MeasurableSet Rp :=
    measurableSet_regionBetween measurable_const (hθm.const_mul t) MeasurableSet.univ
  have hRmm : MeasurableSet Rm :=
    measurableSet_regionBetween (hθm.const_mul t) measurable_const MeasurableSet.univ
  have htθi : IntegrableOn (fun y ↦ t * θ y) univ := (hθi.const_mul t).integrableOn
  have h0i : IntegrableOn (fun _ : Fin n → ℝ ↦ (0 : ℝ)) univ := integrableOn_zero
  -- the volumes of the two thin regions
  have hvol : volume Rp ≠ ⊤ ∧ volume Rm ≠ ⊤ ∧ volume.real Rp - volume.real Rm = t * Θ := by
    simp only [Measure.real, Measure.volume_eq_prod]
    rcases le_total 0 t with h | h
    · have hRm0 : Rm = ∅ := by
        refine eq_empty_of_forall_notMem fun q hq ↦ ?_
        simp only [hRm, regionBetween, mem_ofPred_eq, mem_univ, mem_Ioo, true_and] at hq
        nlinarith [hθ0 q.1]
      have hp := volume_regionBetween_eq_integral h0i htθi MeasurableSet.univ
        fun y _ ↦ mul_nonneg h (hθ0 y)
      simp only [Measure.restrict_univ, Pi.sub_apply, sub_zero, integral_const_mul] at hp
      rw [← hRp, ← hΘ] at hp
      rw [hRm0, hp]
      refine ⟨ENNReal.ofReal_ne_top, by simp, ?_⟩
      simp [ENNReal.toReal_ofReal (mul_nonneg h hΘ0)]
    · have hRp0 : Rp = ∅ := by
        refine eq_empty_of_forall_notMem fun q hq ↦ ?_
        simp only [hRp, regionBetween, mem_ofPred_eq, mem_univ, mem_Ioo, true_and] at hq
        nlinarith [hθ0 q.1]
      have hm := volume_regionBetween_eq_integral htθi h0i MeasurableSet.univ
        fun y _ ↦ mul_nonpos_of_nonpos_of_nonneg h (hθ0 y)
      simp only [Measure.restrict_univ, Pi.sub_apply, zero_sub, integral_neg,
        integral_const_mul] at hm
      rw [← hRm, ← hΘ] at hm
      rw [hRp0, hm]
      refine ⟨by simp, ENNReal.ofReal_ne_top, ?_⟩
      simp [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ -(t * Θ))]
  obtain ⟨hRpf, hRmf, hvol⟩ := hvol
  -- the null set
  have hN : volume ({q : (Fin n → ℝ) × ℝ | q.2 = (fun _ ↦ (0 : ℝ)) q.1} ∪
      {q | q.2 = (fun y ↦ t * θ y) q.1}) = 0 :=
    measure_union_null (volume_graph_eq_zero measurable_const)
      (volume_graph_eq_zero (hθm.const_mul t))
  have hF : slabF a b t ζ θ =ᵐ[volume] fun q ↦
      (b ^ 2 - a ^ 2 - 1) * (Rp.indicator 1 q - Rm.indicator 1 q) +
        -2 * t * (θ q.1 * (slope a b q.2 ^ 2 * deriv ζ q.2)) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with q hq
    simp only [mem_union, mem_ofPred_eq, not_or] at hq
    exact slabF_eq hζ1 hζ0 hζle hθ0 hθle ht hq.1 hq.2
  -- integrability of the pieces
  have hderi : Integrable (deriv ζ) :=
    (hζc.continuous_deriv le_rfl).integrable_of_hasCompactSupport hζs.deriv
  have hgi : Integrable fun s ↦ slope a b s ^ 2 * deriv ζ s :=
    hderi.bdd_mul ((measurable_slope a b).pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact slope_sq_le a b s)
  have hprod : Integrable (fun q : (Fin n → ℝ) × ℝ ↦ θ q.1 * (slope a b q.2 ^ 2 * deriv ζ q.2))
      (volume : Measure ((Fin n → ℝ) × ℝ)) := by
    rw [Measure.volume_eq_prod]; exact hθi.mul_prod hgi
  have hip : Integrable (Rp.indicator (1 : (Fin n → ℝ) × ℝ → ℝ)) :=
    (integrable_indicator_iff hRpm).2 (integrableOn_const hRpf)
  have him : Integrable (Rm.indicator (1 : (Fin n → ℝ) × ℝ → ℝ)) :=
    (integrable_indicator_iff hRmm).2 (integrableOn_const hRmf)
  have hrhs : Integrable fun q : (Fin n → ℝ) × ℝ ↦
      (b ^ 2 - a ^ 2 - 1) * (Rp.indicator 1 q - Rm.indicator 1 q) +
        -2 * t * (θ q.1 * (slope a b q.2 ^ 2 * deriv ζ q.2)) :=
    ((hip.sub him).const_mul _).add (hprod.const_mul _)
  have h1 : Integrable fun q : (Fin n → ℝ) × ℝ ↦
      (b ^ 2 - a ^ 2 - 1) * (Rp.indicator 1 q - Rm.indicator 1 q) := (hip.sub him).const_mul _
  have h2 : Integrable fun q : (Fin n → ℝ) × ℝ ↦
      -2 * t * (θ q.1 * (slope a b q.2 ^ 2 * deriv ζ q.2)) := hprod.const_mul _
  refine ⟨hrhs.congr hF.symm, ?_⟩
  rw [integral_congr_ae hF, integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_sub hip him, integral_indicator_one hRpm,
    integral_indicator_one hRmm, hvol]
  have hpm : ∫ q : (Fin n → ℝ) × ℝ, θ q.1 * (slope a b q.2 ^ 2 * deriv ζ q.2) =
      Θ * (b ^ 2 - a ^ 2) := by
    rw [Measure.volume_eq_prod, integral_prod_mul (fun y ↦ θ y)
      (fun s ↦ slope a b s ^ 2 * deriv ζ s),
      integral_slope_sq_mul_deriv a b hζc hζs (hζ1 0 (by simp))]
  rw [hpm]
  ring

end Slab

/-! ### Minimality in real form -/

section Energy

variable {d : ℕ}

private theorem posSet_indicator_eq {f : E d → ℝ} {V : Set (E d)} {x : E d} (hx : x ∈ V) :
    (posSet f V).indicator 1 x = ind (f x) := by
  by_cases h : 0 < f x
  · rw [indicator_of_mem (show x ∈ posSet f V from ⟨hx, h⟩), ind_of_pos h, Pi.one_apply]
  · rw [indicator_of_notMem (fun h' ↦ h h'.2), ind_of_nonpos (not_lt.1 h)]

private theorem integrableOn_energy_density {f : E d → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (R : ℝ) : IntegrableOn (fun x ↦ ‖∇ f x‖ ^ 2 + ind (f x)) (ball (0 : E d) R) :=
  (integrableOn_norm_sq_gradient_ball hf 0 R).add
    (IntegrableOn.of_bound measure_ball_lt_top
      (measurable_ind.comp hf.continuous.measurable).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact abs_ind_le _))

private theorem energyJ_eq_ofReal {f : E d → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (R : ℝ) :
    energyJ (ball (0 : E d) R) (fun _ ↦ 1) f (∇ f) =
      ENNReal.ofReal (∫ x in ball (0 : E d) R, (‖∇ f x‖ ^ 2 + ind (f x))) := by
  unfold energyJ
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_energy_density hf R)
    (Eventually.of_forall fun x ↦ add_nonneg (sq_nonneg _) (by unfold ind; split_ifs <;> simp))]
  refine setLIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
  simp only [one_pow, one_mul, posSet_indicator_eq hx]

/-- Minimality of `u` against a Lipschitz competitor `v` equal to `u` off `B_R(0)`, as an
inequality of real integrals. -/
private theorem setIntegral_energy_sub_nonneg {u v : E d → ℝ} {L K : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u)
    (hv : LipschitzWith K v) (R : ℝ) (hvu : ∀ x ∉ ball (0 : E d) R, v x = u x) :
    0 ≤ ∫ x in ball (0 : E d) R, (‖∇ v x‖ ^ 2 + ind (v x) - (‖∇ u x‖ ^ 2 + ind (u x))) := by
  have hle := hmin.energyJ_gradient_le hu 0 R
    (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ hv.locallyLipschitz.locallyLipschitzOn)
    (ae_restrict_of_forall_mem measurableSet_ball.compl fun x hx ↦ hvu x hx)
  rw [energyJ_eq_ofReal hu, energyJ_eq_ofReal hv] at hle
  have hv0 : 0 ≤ ∫ x in ball (0 : E d) R, (‖∇ v x‖ ^ 2 + ind (v x)) :=
    setIntegral_nonneg measurableSet_ball fun x _ ↦
      add_nonneg (sq_nonneg _) (by unfold ind; split_ifs <;> simp)
  rw [ENNReal.ofReal_le_ofReal_iff hv0] at hle
  rw [integral_sub (integrableOn_energy_density hv R) (integrableOn_energy_density hu R)]
  linarith

end Energy

/-! ### Coordinates adapted to the interface -/

section Coordinates

variable {n : ℕ}

/-- The first coordinate vector of `ℝⁿ⁺¹`. -/
private noncomputable def e₀ (n : ℕ) : E (n + 1) := EuclideanSpace.single 0 1

private theorem norm_e₀ : ‖e₀ n‖ = 1 := by simp [e₀]

/-- A reflection of `ℝⁿ⁺¹` taking the unit vector `e` to `e₀`. -/
private noncomputable def rot (e : E (n + 1)) : E (n + 1) ≃ₗᵢ[ℝ] E (n + 1) :=
  Submodule.reflection (ℝ ∙ (e - e₀ n))ᗮ

private theorem rot_apply_self {e : E (n + 1)} (he : ‖e‖ = 1) : rot e e = e₀ n :=
  Submodule.reflection_sub (by rw [he, norm_e₀])

private theorem rot_apply_zero {e : E (n + 1)} (he : ‖e‖ = 1) (x : E (n + 1)) :
    rot e x 0 = inner ℝ x e := by
  have h1 : rot e x 0 = inner ℝ (rot e x) (e₀ n) := by
    simp [e₀, EuclideanSpace.inner_single_right]
  rw [h1, ← rot_apply_self he, LinearIsometryEquiv.inner_map_map]

/-- Coordinates `(y, s)` adapted to `e` and `c`: `s = x·e + c` and `y` collects the remaining
coordinates of `rot e x`. -/
private noncomputable def coord (e : E (n + 1)) (c : ℝ) (x : E (n + 1)) : (Fin n → ℝ) × ℝ :=
  (fun i ↦ rot e x i.succ, inner ℝ x e + c)

private theorem coord_add_smul {e : E (n + 1)} (he : ‖e‖ = 1) (c : ℝ) (x : E (n + 1))
    (h : ℝ) : coord e c (x + h • e) = ((coord e c x).1, (coord e c x).2 + h) := by
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  ext i
  · simp [coord, rot_apply_self he, e₀, Fin.succ_ne_zero]
  · simp only [coord, inner_add_left, inner_smul_left, hee, RCLike.conj_to_real]
    ring

private theorem coord_eq_comp {e : E (n + 1)} (he : ‖e‖ = 1) (c : ℝ) :
    coord e c = Prod.swap ∘ MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0 ∘ WithLp.ofLp ∘
      rot e ∘ fun x ↦ x + c • e := by
  funext x
  ext i
  · simp [coord, MeasurableEquiv.piFinSuccAbove_apply, rot_apply_self he, e₀, Fin.tail,
      Fin.succ_ne_zero]
  · simp [coord, MeasurableEquiv.piFinSuccAbove_apply, rot_apply_zero he, he]

private theorem measurePreserving_coord {e : E (n + 1)} (he : ‖e‖ = 1) (c : ℝ) :
    MeasurePreserving (coord e c) := by
  rw [coord_eq_comp he]
  exact Measure.measurePreserving_swap.comp
    ((volume_preserving_piFinSuccAbove (fun _ ↦ ℝ) 0).comp
      ((PiLp.volume_preserving_ofLp (Fin (n + 1))).comp
        ((rot e).measurePreserving.comp (measurePreserving_add_right volume (c • e)))))

private theorem measurableEmbedding_coord {e : E (n + 1)} (he : ‖e‖ = 1) (c : ℝ) :
    MeasurableEmbedding (coord e c) := by
  rw [coord_eq_comp he]
  exact MeasurableEquiv.prodComm.measurableEmbedding.comp
    ((MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0).measurableEmbedding.comp
      ((MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.measurableEmbedding.comp
        ((rot e).toHomeomorph.measurableEmbedding.comp
          (MeasurableEquiv.addRight (c • e)).measurableEmbedding)))

private theorem norm_add_smul_sq {e : E (n + 1)} (he : ‖e‖ = 1) (c : ℝ) (x : E (n + 1)) :
    ‖x + c • e‖ ^ 2 = (coord e c x).2 ^ 2 + ∑ i, (coord e c x).1 i ^ 2 := by
  rw [← (rot e).norm_map, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp [coord, rot_apply_zero he, rot_apply_self he, e₀, Fin.succ_ne_zero]

end Coordinates

/-! ### Gradients of the competitors -/

section Gradient

variable {d : ℕ}

private theorem toDual_symm_innerSL (e : E d) :
    (InnerProductSpace.toDual ℝ (E d)).symm (innerSL ℝ e) = e :=
  (InnerProductSpace.toDual ℝ (E d)).symm_apply_eq.2 (by ext v; simp)

/-- Where `g x ≠ 0`, the gradient of `prof a b ∘ g` is `slope a b (g x) ∇g(x)`. -/
private theorem gradient_prof_comp {a b : ℝ} {g : E d → ℝ} {g' : E d →L[ℝ] ℝ} {x : E d}
    (hg : HasFDerivAt g g' x) (hσ : g x ≠ 0) :
    ∇ (fun y ↦ prof a b (g y)) x =
      slope a b (g x) • (InnerProductSpace.toDual ℝ (E d)).symm g' := by
  have heq : (fun y ↦ prof a b (g y)) =ᶠ[𝓝 x] fun y ↦ slope a b (g x) * g y :=
    hg.continuousAt.tendsto.eventually (prof_eventuallyEq hσ)
  rw [heq.gradient_eq]
  rw [← map_smul]
  exact (hasFDerivAt_iff_hasGradientAt.1 (hg.const_mul _)).gradient

end Gradient

/-! ### The competitor and the energy expansion -/

section Main

variable {n : ℕ}

/-- The normal cutoff `ζ`: `ζ = 1` on `[-1, 1]`, supported in `(-2, 2)`. -/
private noncomputable def ζb : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The tangential cutoff `θ`: `θ = 1` on the unit ball, supported in the ball of radius `2`. -/
private noncomputable def θb (n : ℕ) : ContDiffBump (0 : Fin n → ℝ) :=
  ⟨1, 2, one_pos, one_lt_two⟩

private theorem ζb_eq_one {s : ℝ} (hs : |s| < 1) : ζb s = 1 :=
  ζb.one_of_mem_closedBall (by simpa [ζb, Real.dist_eq] using hs.le)

private theorem ζb_eq_zero {s : ℝ} (hs : 2 ≤ |s|) : ζb s = 0 := by
  have : s ∉ Function.support ζb := by
    rw [ζb.support_eq]; simpa [ζb, Real.dist_eq] using hs
  exact Function.notMem_support.1 this

private theorem θb_eq_zero {y : Fin n → ℝ} (hy : 2 ≤ ‖y‖) : θb n y = 0 := by
  have : y ∉ Function.support (θb n) := by
    rw [(θb n).support_eq]; simpa [θb] using hy
  exact Function.notMem_support.1 this

private theorem contDiff_coord (e : E (n + 1)) (c : ℝ) : ContDiff ℝ ∞ (coord e c) := by
  have h1 : ContDiff ℝ ∞ fun x : E (n + 1) ↦ fun i : Fin n ↦ rot e x i.succ :=
    contDiff_pi.2 fun i ↦ ((PiLp.proj 2 (fun _ : Fin (n + 1) ↦ ℝ) i.succ).contDiff).comp
      (rot e).contDiff
  have h2 : ContDiff ℝ ∞ fun x : E (n + 1) ↦ inner ℝ x e + c :=
    (contDiff_id.inner ℝ contDiff_const).add contDiff_const
  exact h1.prodMk h2

/-- If `|s| ≤ 2` and `‖y‖ ≤ 2` in the coordinates of `x`, then `‖x‖ ≤ 2 + 2n + |c|`. -/
private theorem norm_le_of_coord {e : E (n + 1)} (he : ‖e‖ = 1) (c : ℝ) {x : E (n + 1)}
    (hs : |(coord e c x).2| ≤ 2) (hy : ‖(coord e c x).1‖ ≤ 2) :
    ‖x‖ ≤ 2 + 2 * n + |c| := by
  have hsq := norm_add_smul_sq he c x
  have hsum : ∑ i, (coord e c x).1 i ^ 2 ≤ n * 4 := by
    calc ∑ i, (coord e c x).1 i ^ 2 ≤ ∑ _i : Fin n, (4 : ℝ) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have := (norm_le_pi_norm (coord e c x).1 i).trans hy
          rw [Real.norm_eq_abs] at this
          nlinarith [abs_nonneg ((coord e c x).1 i), sq_abs ((coord e c x).1 i)]
      _ = n * 4 := by simp
  have hs2 : (coord e c x).2 ^ 2 ≤ 4 := by
    nlinarith [sq_abs (coord e c x).2, abs_nonneg (coord e c x).2]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : ‖x + c • e‖ ≤ 2 + 2 * n := by
    have h0 : 0 ≤ 2 + 2 * (n : ℝ) := by positivity
    nlinarith [norm_nonneg (x + c • e)]
  have h2 : ‖x‖ ≤ ‖x + c • e‖ + ‖c • e‖ := by
    simpa using norm_sub_le (x + c • e) (c • e)
  rw [norm_smul, he, mul_one, Real.norm_eq_abs] at h2
  linarith

private theorem contDiff_bump (e : E (n + 1)) (c : ℝ) :
    ContDiff ℝ ∞ fun x ↦ ζb (coord e c x).2 * θb n (coord e c x).1 :=
  (ζb.contDiff.comp (contDiff_coord e c).snd).mul ((θb n).contDiff.comp (contDiff_coord e c).fst)

/-- The derivative of `η = ζ(s) θ(y)` along `e` is `ζ'(s) θ(y)`. -/
private theorem inner_gradient_bump {e : E (n + 1)} (he : ‖e‖ = 1) (c : ℝ) (x : E (n + 1)) :
    inner ℝ e (∇ (fun x ↦ ζb (coord e c x).2 * θb n (coord e c x).1) x) =
      deriv ζb (coord e c x).2 * θb n (coord e c x).1 := by
  set η : E (n + 1) → ℝ := fun x ↦ ζb (coord e c x).2 * θb n (coord e c x).1 with hη
  have hd : DifferentiableAt ℝ η x := (contDiff_bump e c).differentiable (by simp) x
  have hline : HasDerivAt (fun h : ℝ ↦ x + h • e) e 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    simp only [id, one_smul] at this
    exact this
  have h1 : HasDerivAt (fun h : ℝ ↦ η (x + h • e)) (fderiv ℝ η x e) 0 :=
    hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hfun : (fun h : ℝ ↦ η (x + h • e)) =
      fun h ↦ ζb ((coord e c x).2 + h) * θb n (coord e c x).1 := by
    funext h; simp only [hη, coord_add_smul he]
  have h2 : HasDerivAt (fun h : ℝ ↦ ζb ((coord e c x).2 + h) * θb n (coord e c x).1)
      (deriv ζb (coord e c x).2 * θb n (coord e c x).1) 0 := by
    have hζd : HasDerivAt ζb (deriv ζb (coord e c x).2) ((coord e c x).2 + 0) := by
      rw [add_zero]
      exact ((ζb.contDiff (n := 1)).differentiable one_ne_zero _).hasDerivAt
    exact (hζd.comp_const_add _ 0 |>.mul_const _)
  rw [hfun] at h1
  rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
  exact h1.unique h2

private theorem slabF_eq_zero {a b t : ℝ} {ζ : ℝ → ℝ} {θ : (Fin n → ℝ) → ℝ}
    {q : (Fin n → ℝ) × ℝ} (h : ζ q.2 * θ q.1 = 0) (h' : deriv ζ q.2 * θ q.1 = 0) :
    slabF a b t ζ θ q = 0 := by
  simp [slabF, h, h']

private theorem ind_prof {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (σ : ℝ) :
    ind (prof a b σ) = ind σ := by
  unfold ind; simp only [prof_pos_iff ha hb]

/-- **The free boundary condition for two-plane minimizers in `ℝⁿ⁺¹`.** -/
private theorem sq_sub_sq_eq_one_aux {e : E (n + 1)} (he : ‖e‖ = 1) {a b c : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) (twoPlane a b e c)) :
    a ^ 2 - b ^ 2 = 1 := by
  set ζ : ℝ → ℝ := ⇑ζb with hζdef
  set θ : (Fin n → ℝ) → ℝ := ⇑(θb n) with hθdef
  set η : E (n + 1) → ℝ := fun x ↦ ζ (coord e c x).2 * θ (coord e c x).1 with hηdef
  have hζ1 : ∀ s, |s| < 1 → ζ s = 1 := fun s hs ↦ ζb_eq_one hs
  have hζ0 : ∀ s, 0 ≤ ζ s := fun s ↦ ζb.nonneg
  have hζle : ∀ s, ζ s ≤ 1 := fun s ↦ ζb.le_one
  have hθ0 : ∀ y, 0 ≤ θ y := fun y ↦ (θb n).nonneg
  have hθle : ∀ y, θ y ≤ 1 := fun y ↦ (θb n).le_one
  have hζc : ContDiff ℝ 1 ζ := ζb.contDiff
  have hζs : HasCompactSupport ζ := ζb.hasCompactSupport
  have hθc : Continuous θ := (θb n).continuous
  have hθi : Integrable θ := (θb n).integrable
  set Θ := ∫ y, θ y with hΘdef
  have hΘ : 0 < Θ := (θb n).integral_pos
  have hηc : ContDiff ℝ ∞ η := contDiff_bump e c
  set R₀ : ℝ := 2 + 2 * n + |c| with hR₀
  have hηz : ∀ x, R₀ < ‖x‖ → η x = 0 := by
    intro x hx
    by_contra h
    have h' := mul_ne_zero_iff.1 h
    have hs : |(coord e c x).2| ≤ 2 := by
      by_contra h2; exact h'.1 (ζb_eq_zero (not_le.1 h2).le)
    have hy : ‖(coord e c x).1‖ ≤ 2 := by
      by_contra h2; exact h'.2 (θb_eq_zero (not_le.1 h2).le)
    exact absurd (norm_le_of_coord he c hs hy) (not_le.2 hx)
  have hηcs : HasCompactSupport η :=
    HasCompactSupport.intro (isCompact_closedBall 0 R₀) fun x hx ↦
      hηz x (by simpa using hx)
  obtain ⟨Kη, hKη⟩ := hηc.lipschitzWith_of_hasCompactSupport hηcs (by simp)
  have hgη : ∀ x, ‖∇ η x‖ ≤ Kη := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hKη
  set R : ℝ := R₀ + 1 with hR
  set C : ℝ := (a ^ 2 + b ^ 2) * (Kη : ℝ) ^ 2 * volume.real (ball (0 : E (n + 1)) R) with hCdef
  have hC : 0 ≤ C := by positivity
  have hu_eq : twoPlane a b e c = fun x ↦ prof a b (inner ℝ x e + c) := rfl
  have hu := twoPlane_lipschitzWith a b e c
  have hmp := measurePreserving_coord he c
  have hemb := measurableEmbedding_coord he c
  have hdlin : ∀ x : E (n + 1), HasFDerivAt (fun x ↦ inner ℝ x e + c) (innerSL ℝ e) x := by
    intro x
    have := ((innerSL ℝ e).hasFDerivAt (x := x)).add_const c
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
    simp [real_inner_comm]
  have key : ∀ t : ℝ, |t| < 1 / 2 → 0 ≤ t * Θ * (a ^ 2 - b ^ 2 - 1) + t ^ 2 * C := by
    intro t ht
    obtain ⟨hFi, hFint⟩ :=
      integrable_and_integral_slabF a b hζc hζs hζ1 hζ0 hζle hθc hθi hθ0 hθle ht
    set σ : E (n + 1) → ℝ := fun x ↦ inner ℝ x e + c - t * η x with hσdef
    set v : E (n + 1) → ℝ := fun x ↦ prof a b (σ x) with hvdef
    have hσL : LipschitzWith (1 + ‖t‖₊ * Kη) σ := by
      refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
      have h1 : |inner ℝ x e - inner ℝ y e| ≤ ‖x - y‖ := by
        rw [← inner_sub_left]
        exact (abs_real_inner_le_norm _ _).trans (by rw [he, mul_one])
      have h2 : |η x - η y| ≤ Kη * ‖x - y‖ := by
        have := hKη.dist_le_mul x y
        rwa [Real.dist_eq, dist_eq_norm] at this
      simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_one, coe_nnnorm,
        Real.norm_eq_abs, dist_eq_norm, hσdef]
      calc |inner ℝ x e + c - t * η x - (inner ℝ y e + c - t * η y)|
          = |(inner ℝ x e - inner ℝ y e) - t * (η x - η y)| := by ring_nf
        _ ≤ |inner ℝ x e - inner ℝ y e| + |t| * |η x - η y| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ ‖x - y‖ + |t| * (Kη * ‖x - y‖) := by gcongr
        _ = (1 + |t| * Kη) * ‖x - y‖ := by ring
    have hv : LipschitzWith _ v := (lipschitzWith_prof a b).comp hσL
    have hvu : ∀ x ∉ ball (0 : E (n + 1)) R, v x = twoPlane a b e c x := by
      intro x hx
      have : R₀ < ‖x‖ := by rw [mem_ball_zero_iff, not_lt] at hx; linarith
      simp only [hvdef, hσdef, hηz x this, mul_zero, sub_zero, hu_eq]
    have h0 := setIntegral_energy_sub_nonneg hmin hu hv R hvu
    set G : E (n + 1) → ℝ := fun x ↦ t ^ 2 * (slope a b (σ x) ^ 2 * ‖∇ η x‖ ^ 2) with hGdef
    -- the exceptional null set
    set N : Set ((Fin n → ℝ) × ℝ) := {q | q.2 = (fun _ ↦ (0 : ℝ)) q.1} ∪
      {q | q.2 = (fun y ↦ t * θ y) q.1} with hNdef
    have hNm : MeasurableSet N :=
      (measurableSet_eq_fun measurable_snd measurable_const).union
        (measurableSet_eq_fun measurable_snd ((hθc.measurable.const_mul t).comp measurable_fst))
    have hN : volume (coord e c ⁻¹' N) = 0 := by
      rw [hmp.measure_preimage hNm.nullMeasurableSet]
      exact measure_union_null (volume_graph_eq_zero measurable_const)
        (volume_graph_eq_zero (hθc.measurable.const_mul t))
    have hae : ∀ᵐ x, ‖∇ v x‖ ^ 2 + ind (v x) -
        (‖∇ (twoPlane a b e c) x‖ ^ 2 + ind (twoPlane a b e c x)) =
          slabF a b t ζ θ (coord e c x) + G x := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN] with x hx
      simp only [hNdef, mem_preimage, mem_union, mem_ofPred_eq, not_or] at hx
      obtain ⟨hs0, hst⟩ := hx
      set s := (coord e c x).2 with hs
      set y := (coord e c x).1 with hy
      have hsx : inner ℝ x e + c = s := rfl
      have hσx : σ x = s - t * (ζ s * θ y) := rfl
      have hσ0 : σ x ≠ 0 := by
        intro h0'
        rw [hσx] at h0'
        have hζθ0 : 0 ≤ ζ s * θ y := mul_nonneg (hζ0 s) (hθ0 y)
        have hζθ1 : ζ s * θ y ≤ 1 :=
          (mul_le_mul (hζle s) (hθle y) (hθ0 y) zero_le_one).trans_eq (one_mul 1)
        have h2 : |s| < 1 := by
          rw [show s = t * (ζ s * θ y) by linarith, abs_mul, abs_of_nonneg hζθ0]
          nlinarith [abs_nonneg t]
        rw [hζ1 s h2, one_mul] at h0'
        exact hst (by linarith)
      have hdη : HasFDerivAt η (fderiv ℝ η x) x :=
        (hηc.differentiable (by simp) x).hasFDerivAt
      have hgv : ∇ v x = slope a b (σ x) • (e - t • ∇ η x) := by
        rw [hvdef, gradient_prof_comp (g := σ) (by exact (hdlin x).sub (hdη.const_mul t)) hσ0,
          map_sub, map_smul,
          toDual_symm_innerSL]
        rfl
      have hgu : ∇ (twoPlane a b e c) x = slope a b s • e := by
        rw [hu_eq, gradient_prof_comp (hdlin x) (by rwa [hsx]), toDual_symm_innerSL]
        rfl
      have hinner : inner ℝ e (∇ η x) = deriv ζ s * θ y := inner_gradient_bump he c x
      rw [hgv, hgu, hvdef, ind_prof ha hb, hu_eq, ind_prof ha hb, hsx]
      rw [norm_smul, norm_smul, mul_pow, mul_pow, he, norm_sub_sq_real, he, inner_smul_right,
        norm_smul, hinner]
      simp only [Real.norm_eq_abs, hGdef, slabF, hσx, ← hs, ← hy, mul_pow, sq_abs]
      ring
    -- integrability and the two integrals
    have hGm : Measurable G :=
      (((measurable_slope a b).comp (by fun_prop : Continuous σ).measurable).pow_const 2 |>.mul
        ((measurable_gradient η).norm.pow_const 2)).const_mul _
    have hGb : ∀ x, ‖G x‖ ≤ t ^ 2 * ((a ^ 2 + b ^ 2) * (Kη : ℝ) ^ 2) := fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := slope_sq_le a b (σ x)
      have h2 : ‖∇ η x‖ ^ 2 ≤ (Kη : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hgη x) 2
      have h3 : slope a b (σ x) ^ 2 * ‖∇ η x‖ ^ 2 ≤ (a ^ 2 + b ^ 2) * (Kη : ℝ) ^ 2 :=
        mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_left h3 (sq_nonneg t)
    have hGi : IntegrableOn G (ball (0 : E (n + 1)) R) :=
      IntegrableOn.of_bound measure_ball_lt_top hGm.aestronglyMeasurable _
        (Eventually.of_forall hGb)
    have hFi' : Integrable fun x ↦ slabF a b t ζ θ (coord e c x) :=
      (hmp.integrable_comp_emb hemb).2 hFi
    have hFzero : ∀ x ∉ ball (0 : E (n + 1)) R, slabF a b t ζ θ (coord e c x) = 0 := by
      intro x hx
      have hxR : R₀ < ‖x‖ := by rw [mem_ball_zero_iff, not_lt] at hx; linarith
      by_cases hy : ‖(coord e c x).1‖ ≤ 2
      · have hs : 2 < |(coord e c x).2| := by
          by_contra hs; exact absurd (norm_le_of_coord he c (not_lt.1 hs) hy) (not_le.2 hxR)
        have hev : ζ =ᶠ[𝓝 (coord e c x).2] fun _ ↦ 0 := by
          have hopen : IsOpen {s : ℝ | 2 < |s|} := isOpen_lt continuous_const continuous_abs
          filter_upwards [hopen.mem_nhds hs] with r hr using ζb_eq_zero hr.le
        have hz : ζ (coord e c x).2 = 0 := ζb_eq_zero hs.le
        refine slabF_eq_zero ?_ ?_
        · rw [hz, zero_mul]
        · rw [hev.deriv_eq, deriv_const, zero_mul]
      · have hθz : θ (coord e c x).1 = 0 := θb_eq_zero (not_le.1 hy).le
        exact slabF_eq_zero (by rw [hθz, mul_zero]) (by rw [hθz, mul_zero])
    have hI1 : ∫ x in ball (0 : E (n + 1)) R, slabF a b t ζ θ (coord e c x) =
        t * Θ * (a ^ 2 - b ^ 2 - 1) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hFzero,
        hmp.integral_comp hemb (slabF a b t ζ θ), hFint]
    have hI2 : ∫ x in ball (0 : E (n + 1)) R, G x ≤ t ^ 2 * C := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (measure_ball_lt_top (x := (0 : E (n + 1))) (r := R)) (fun x _ ↦ hGb x)
      rw [Real.norm_eq_abs] at this
      calc ∫ x in ball (0 : E (n + 1)) R, G x ≤ |∫ x in ball (0 : E (n + 1)) R, G x| :=
            le_abs_self _
        _ ≤ _ := this
        _ = t ^ 2 * C := by rw [hCdef]; ring
    rw [setIntegral_congr_ae measurableSet_ball (hae.mono fun x hx _ ↦ hx),
      integral_add hFi'.integrableOn hGi, hI1] at h0
    linarith
  -- conclusion: the first variation vanishes
  by_contra hne
  set δ := a ^ 2 - b ^ 2 - 1 with hδ
  have hδ0 : δ ≠ 0 := fun h ↦ hne (by linarith)
  have hδa : 0 < |δ| := abs_pos.2 hδ0
  set τ : ℝ := min (1 / 4) (Θ * |δ| / (2 * (C + 1))) with hτ
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 / 4 := min_le_left _ _
  have hτ2 : τ * (2 * (C + 1)) ≤ Θ * |δ| :=
    (le_div_iff₀ (by positivity)).1 (min_le_right _ _)
  have hτC : τ * C ≤ Θ * |δ| / 2 := by nlinarith
  rcases lt_or_gt_of_ne hδ0 with hneg | hpos
  · have h := key τ (by rw [abs_of_pos hτ0]; linarith)
    rw [abs_of_neg hneg] at hτC
    have : 0 ≤ τ * (Θ * δ + τ * C) := by nlinarith
    have h' : 0 ≤ Θ * δ + τ * C := nonneg_of_mul_nonneg_right (by linarith) hτ0
    nlinarith
  · have h := key (-τ) (by rw [abs_neg, abs_of_pos hτ0]; linarith)
    rw [abs_of_pos hpos] at hτC
    have : 0 ≤ τ * (-(Θ * δ) + τ * C) := by nlinarith
    have h' : 0 ≤ -(Θ * δ) + τ * C := nonneg_of_mul_nonneg_right (by linarith) hτ0
    nlinarith

end Main

/-- **The free boundary condition for two-plane minimizers.** If
`‖e‖ = 1`, `a, b > 0` and the two-plane function `x ↦ a (x·e + c)⁺ - b (x·e + c)⁻` is a local
minimizer of `J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ`, then `a² - b² = 1`. -/
public theorem sq_sub_sq_eq_one_of_isLocalEnergyMinimizer_twoPlane {d : ℕ} {e : E d}
    (he : ‖e‖ = 1) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) (twoPlane a b e c)) :
    a ^ 2 - b ^ 2 = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero fun hd ↦ by
    subst hd
    have : e = 0 := Subsingleton.elim _ _
    simp [this] at he
  exact sq_sub_sq_eq_one_aux he ha hb hmin

end EllipticBernoulli
