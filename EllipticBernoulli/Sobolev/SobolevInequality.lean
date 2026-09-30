/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.SobolevOne
public import EllipticBernoulli.Sobolev.ZeroExtension

/-!
# The Poincaré inequality on balls for `H¹_loc` functions vanishing off the ball

`integral_sq_le_of_ae_eq_zero_off_ball`: for `d ≥ 1` there is `C = C(d)` such that
if `v ∈ H¹_loc(U)` with weak gradient `G`, `closedBall x₀ r ⊆ U` and `v = 0` a.e. on
`U \ ball x₀ r`, then
`∫_{B_r(x₀)} v² ≤ C r² ∫_{B_r(x₀)} |G|²`.
One can take `C = C_S(d)² |B_1|^{2/d}` with `C_S(d)` the constant of `exists_sobolevSupport`.

Proof: extend `v` by zero (`HasWeakGradient.univ_of_ae_eq_zero`) to `g = 1_{B̄_r} v`, modify the
gradient on the null set where Stampacchia's lemma (`HasWeakGradient.ae_eq_zero_of_eq_zero`)
allows it so that it vanishes pointwise on `{g = 0}`, and apply the Sobolev inequality on the
support (`integral_sq_le_of_sobolevSupport`, `exists_sobolevSupport`) with
`|{g ≠ 0}| ≤ |B̄_r| = |B_1| r^d`.

This file re-exports the Sobolev-on-the-support inequality (`SobolevSupport`,
`sobolevSupport_of_two_le`, `exists_sobolevSupport`, `integral_sq_le_of_sobolevSupport`) from
`Sobolev/SobolevGNS.lean` and `Sobolev/SobolevOne.lean`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- Open and closed balls of positive radius agree up to a null set. -/
theorem ball_ae_eq_closedBall (x : E d) {r : ℝ} (hr : 0 < r) :
    (ball x r : Set (E d)) =ᵐ[volume] closedBall x r := by
  refine ae_eq_of_subset_of_measure_ge ball_subset_closedBall ?_
    measurableSet_ball.nullMeasurableSet measure_closedBall_lt_top.ne
  calc volume (closedBall x r) = volume (ball x r ∪ sphere x r) := by rw [ball_union_sphere]
    _ ≤ volume (ball x r) + volume (sphere x r) := measure_union_le _ _
    _ = volume (ball x r) := by rw [Measure.addHaar_sphere_of_ne_zero _ _ hr.ne', add_zero]

/-- **Poincaré inequality on balls.** For `d ≥ 1` there is `C ≥ 0` such that every
`v ∈ H¹_loc(U)` with weak gradient `G` that vanishes a.e. on `U \ B_r(x₀)`, where
`closedBall x₀ r ⊆ U`, satisfies `∫_{B_r(x₀)} v² ≤ C r² ∫_{B_r(x₀)} |G|²`. -/
theorem integral_sq_le_of_ae_eq_zero_off_ball (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (E d)) (v : E d → ℝ) (G : E d → E d) (x₀ : E d) (r : ℝ),
      IsOpen U → MemH1Loc U v G → 0 < r → closedBall x₀ r ⊆ U →
      (∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v y = 0) →
      ∫ y in ball x₀ r, v y ^ 2 ≤ C * r ^ 2 * ∫ y in ball x₀ r, ‖G y‖ ^ 2 := by
  obtain ⟨CS, hS⟩ := exists_sobolevSupport hd
  set b : ℝ := (volume (ball (0 : E d) 1)).toReal with hb
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  refine ⟨(CS : ℝ) ^ 2 * (b ^ (1 / (d : ℝ))) ^ 2, by positivity, ?_⟩
  intro U v G x₀ r hU hv hr hKU h0
  set K := closedBall x₀ r with hKdef
  have hKc : IsCompact K := isCompact_closedBall x₀ r
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hUK : MeasurableSet (U \ K) := hU.measurableSet.diff hKm
  have h0K : ∀ᵐ y ∂(volume.restrict (U \ K)), v y = 0 :=
    ae_restrict_of_ae_restrict_of_subset (sdiff_subset_sdiff_right ball_subset_closedBall) h0
  have hG0 : ∀ᵐ y ∂(volume.restrict (U \ K)), G y = 0 :=
    hv.1.ae_eq_zero_of_ae_eq_zero_on (hU.sdiff hKc.isClosed) sdiff_subset h0K
  have hext := hv.1.univ_of_ae_eq_zero hU hKc hKU h0K
  rw [ae_restrict_iff' hUK] at h0K hG0
  set g : E d → ℝ := K.indicator v with hg
  have hgU : U.indicator v =ᵐ[volume] g := by
    filter_upwards [h0K] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem (hKU hxK), hg, indicator_of_mem hxK]
    · by_cases hxU : x ∈ U
      · rw [indicator_of_mem hxU, hg, indicator_of_notMem hxK, hx ⟨hxU, hxK⟩]
      · rw [indicator_of_notMem hxU, hg, indicator_of_notMem hxK]
  have hGU : U.indicator G =ᵐ[volume] K.indicator G := by
    filter_upwards [hG0] with x hx
    by_cases hxK : x ∈ K
    · rw [indicator_of_mem (hKU hxK), indicator_of_mem hxK]
    · by_cases hxU : x ∈ U
      · rw [indicator_of_mem hxU, indicator_of_notMem hxK, hx ⟨hxU, hxK⟩]
      · rw [indicator_of_notMem hxU, indicator_of_notMem hxK]
  have hwg : HasWeakGradient univ g (U.indicator G) :=
    hext.congr_fun_ae (by rw [Measure.restrict_univ]; exact hgU)
  have hst := hwg.ae_eq_zero_of_eq_zero isOpen_univ
  rw [Measure.restrict_univ] at hst
  set Γ : E d → E d := fun x ↦ if g x = 0 then 0 else U.indicator G x with hΓ
  have hΓU : Γ =ᵐ[volume] U.indicator G := by
    filter_upwards [hst] with x hx
    by_cases hgx : g x = 0
    · simp only [hΓ, ite_eq_left hgx]; exact (hx hgx).symm
    · simp only [hΓ, ite_eq_right hgx]
  have hwΓ : HasWeakGradient univ g Γ :=
    hwg.congr_ae (by rw [Measure.restrict_univ]; exact hΓU.symm)
  have hgL : MemLp g 2 volume := (memLp_indicator_iff_restrict hKm).2 (hv.2 K hKU hKc).1
  have hΓL : MemLp Γ 2 volume :=
    ((memLp_indicator_iff_restrict hKm).2 (hv.2 K hKU hKc).2).ae_eq (hΓU.trans hGU).symm
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro hKc fun x hx ↦ by rw [hg, indicator_of_notMem hx]
  have hGz : ∀ x, g x = 0 → Γ x = 0 := fun x hx ↦ by simp only [hΓ, ite_eq_left hx]
  have key := integral_sq_le_of_sobolevSupport hS hwΓ hgL hΓL hgc hGz
  have hsph := ball_ae_eq_closedBall x₀ hr
  have e1 : ∫ x, g x ^ 2 = ∫ y in ball x₀ r, v y ^ 2 := by
    have : (fun x ↦ g x ^ 2) = K.indicator (fun x ↦ v x ^ 2) := by
      funext x; by_cases hx : x ∈ K <;> simp [hg, hx]
    rw [this, integral_indicator hKm, setIntegral_congr_set hsph]
  have e2 : ∫ x, ‖Γ x‖ ^ 2 = ∫ y in ball x₀ r, ‖G y‖ ^ 2 := by
    have h1 : ∫ x, ‖Γ x‖ ^ 2 = ∫ x, ‖K.indicator G x‖ ^ 2 :=
      integral_congr_ae ((hΓU.trans hGU).fun_comp fun z ↦ ‖z‖ ^ 2)
    have : (fun x ↦ ‖K.indicator G x‖ ^ 2) = K.indicator (fun x ↦ ‖G x‖ ^ 2) := by
      funext x; by_cases hx : x ∈ K <;> simp [hx]
    rw [h1, this, integral_indicator hKm, setIntegral_congr_set hsph]
  have hvolK : volume K = ENNReal.ofReal (r ^ d) * volume (ball (0 : E d) 1) := by
    rw [hKdef, Measure.addHaar_closedBall volume x₀ hr.le, finrank_euclideanSpace_fin]
  have hmeas : (volume {x | g x ≠ 0}).toReal ≤ r ^ d * b := by
    have hsub : {x | g x ≠ 0} ⊆ K := fun x hx ↦ by
      by_contra h; exact hx (by rw [hg, indicator_of_notMem h])
    calc (volume {x | g x ≠ 0}).toReal ≤ (volume K).toReal :=
          ENNReal.toReal_mono hKc.measure_lt_top.ne (measure_mono hsub)
      _ = r ^ d * b := by
          rw [hvolK, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hpow : (volume {x | g x ≠ 0}).toReal ^ (1 / (d : ℝ)) ≤ r * b ^ (1 / (d : ℝ)) := by
    calc (volume {x | g x ≠ 0}).toReal ^ (1 / (d : ℝ)) ≤ (r ^ d * b) ^ (1 / (d : ℝ)) :=
          Real.rpow_le_rpow ENNReal.toReal_nonneg hmeas (by positivity)
      _ = r * b ^ (1 / (d : ℝ)) := by
          rw [Real.mul_rpow (by positivity) hb0, one_div,
            Real.pow_rpow_inv_natCast hr.le (by omega)]
  have hI : 0 ≤ ∫ x, ‖Γ x‖ ^ 2 := integral_nonneg fun _ ↦ by positivity
  rw [← e1, ← e2]
  calc ∫ x, g x ^ 2
      ≤ (CS : ℝ) ^ 2 * ((volume {x | g x ≠ 0}).toReal ^ (1 / (d : ℝ))) ^ 2 *
          ∫ x, ‖Γ x‖ ^ 2 := key
    _ ≤ (CS : ℝ) ^ 2 * (r * b ^ (1 / (d : ℝ))) ^ 2 * ∫ x, ‖Γ x‖ ^ 2 := by
        gcongr
    _ = (CS : ℝ) ^ 2 * (b ^ (1 / (d : ℝ))) ^ 2 * r ^ 2 * ∫ x, ‖Γ x‖ ^ 2 := by ring

end EllipticBernoulli
