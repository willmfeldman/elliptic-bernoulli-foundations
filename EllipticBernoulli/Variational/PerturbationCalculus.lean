/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.IBP
public import EllipticBernoulli.Sobolev.Energy
public import EllipticBernoulli.Sobolev.Lattice

/-!
# Energy comparison for local perturbations

The calculus behind the energy-decreasing perturbations of `Variational/Perturbation.lean`.

* `integral_pos_of_continuousOn`: a continuous function that is `≥ 0` on an open set `U`, vanishes
  off a compact `K ⊆ U` and is positive at one point of `U` has positive integral over `U`.
* `energyJ_lt_of_le_add_inner`: **energy comparison**. Let `w, w' ∈ H¹_loc(U)` agree off a compact
  `K ⊆ B`, where `B ⋐ U`. Suppose that a.e. on `K`
  `|∇w'|² + Q² 1_{w'>0} ≤ |∇w|² + Q² 1_{w>0} + 2 ⟪∇w' - ∇w, ∇φ⟫`
  for a smooth `φ`, and that `∫_U (w' - w) Δφ > 0`. Then `J_Q(w'; B) < J_Q(w; B)`.

The proof integrates the pointwise inequality over `K` and uses integration by parts against the
compactly supported `H¹` function `w' - w` (`HasWeakGradient.integral_inner_gradient_eq_neg`):
`∫ ⟪∇(w' - w), ∇φ⟫ = -∫ (w' - w) Δφ < 0`. Off `K` the energies agree because the weak gradients
agree a.e. there (`HasWeakGradient.ae_eq_of_eqOn`). No harmonicity of `w` is used.

The pointwise inequality is the only place where the perturbation enters. For `w' = max(w, φ + δ)`
it is `0 ≤ |∇w - ∇φ|² - Q² 1_{w=0}` on `{w' > w}` (with `∇w = 0` a.e. on `{w = 0}`); for
`w' = min(w, (φ - δ)₊)` it is `0 ≤ |∇w - ∇φ|²` on `{w' = φ - δ > 0}` and
`0 ≤ |∇w|² - 2⟪∇w, ∇φ⟫ + Q²` on `{w' = 0}`.

The energy computation follows Feldman–Kim–Požár, proof of Lemma 3.3, but is arranged so that
only the sign of `Δφ` near the touching point is used, never harmonicity of `w`.

## References

* W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian ENNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- A function continuous on the open set `U`, nonnegative on `U`, vanishing on `U \ K` for a
compact `K ⊆ U` and positive at some point of `U` has positive integral over `U`. -/
theorem integral_pos_of_continuousOn {U K : Set (E d)} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {g : E d → ℝ} (hg : ContinuousOn g U) (hg0 : ∀ x ∈ U, 0 ≤ g x)
    (hgK : ∀ x ∈ U \ K, g x = 0) {y : E d} (hy : y ∈ U) (hgy : 0 < g y) :
    0 < ∫ x in U, g x := by
  have hint : IntegrableOn g U :=
    ((hg.mono hKU).integrableOn_compact hK).of_forall_diff_eq_zero hU.measurableSet hgK
  have hnn : 0 ≤ᵐ[volume.restrict U] g := by
    rw [EventuallyLE, ae_restrict_iff' hU.measurableSet]
    exact Eventually.of_forall fun x hx ↦ hg0 x hx
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hO : IsOpen (U ∩ g ⁻¹' Ioi 0) := hg.isOpen_inter_preimage hU isOpen_Ioi
  refine (hO.measure_pos volume ⟨y, hy, hgy⟩).trans_le (measure_mono fun x hx ↦ ?_)
  exact ⟨fun h ↦ (ne_of_gt (show 0 < g x from hx.2)) h, hx.1⟩

/-- The positivity term `Q² 1_{v>0}` is integrable on a compact set on which `Q` is continuous and
bounded, for a.e.-strongly-measurable `v`. -/
theorem integrableOn_posTerm {K : Set (E d)} (hK : IsCompact K) {Q v : E d → ℝ}
    (hQ : ContinuousOn Q K) {C : ℝ} (hC : ∀ x ∈ K, |Q x| ≤ C)
    (hv : AEStronglyMeasurable v (volume.restrict K)) :
    IntegrableOn (fun x ↦ Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (v x)) K := by
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hind : Measurable ((Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ)) :=
    measurable_const.indicator measurableSet_Ioi
  have hm : AEStronglyMeasurable (fun x ↦ Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (v x))
      (volume.restrict K) :=
    ((hQ.aestronglyMeasurable hKm).pow 2).mul
      (hind.comp_aemeasurable hv.aemeasurable).aestronglyMeasurable
  refine Integrable.mono' (integrable_const (C ^ 2)) hm ?_
  rw [ae_restrict_iff' hKm]
  refine Eventually.of_forall fun x hx ↦ ?_
  have h1 : (Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ) (v x) ∈ Icc (0 : ℝ) 1 := by
    by_cases h : v x ∈ Ioi (0 : ℝ) <;> simp [h]
  have hQ2 : Q x ^ 2 ≤ C ^ 2 := by
    have := hC x hx
    nlinarith [abs_nonneg (Q x), sq_abs (Q x)]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h1.1)]
  nlinarith [sq_nonneg (Q x), h1.1, h1.2]

/-- `⟪G, ∇φ⟫` is integrable on a compact `K` when `G ∈ L²(K)` and `φ` is `C¹`. -/
theorem integrableOn_inner_gradient {K : Set (E d)} (hK : IsCompact K) {G : E d → E d}
    (hG : MemLp G 2 (volume.restrict K)) {φ : E d → ℝ} (hφ : ContDiff ℝ 1 φ) :
    IntegrableOn (fun x ↦ inner ℝ (G x) (∇ φ x)) K := by
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hc : Continuous (∇ φ) := continuous_gradient hφ
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hG1 : Integrable G (volume.restrict K) := hG.integrable one_le_two
  refine Integrable.mono' (hG1.norm.const_mul M)
    (hG1.aestronglyMeasurable.inner hc.aestronglyMeasurable) ?_
  rw [ae_restrict_iff' hKm]
  refine Eventually.of_forall fun x hx ↦ ?_
  calc ‖inner ℝ (G x) (∇ φ x)‖ ≤ ‖G x‖ * ‖∇ φ x‖ := norm_inner_le_norm _ _
    _ ≤ ‖G x‖ * M := mul_le_mul_of_nonneg_left (hM x hx) (norm_nonneg _)
    _ = M * ‖G x‖ := mul_comm _ _

/-- **Energy comparison for a local perturbation.** Let `B ⋐ U`, `K ⊆ B` compact, and
`w, w' ∈ H¹_loc(U)` with `w' = w` on `U \ K`. If a.e. on `K`
`|∇w'|² + Q² 1_{w'>0} ≤ |∇w|² + Q² 1_{w>0} + 2 ⟪∇w' - ∇w, ∇φ⟫`
for a smooth `φ`, and `∫_U (w' - w) Δφ > 0`, then `J_Q(w'; B) < J_Q(w; B)`. `Q` is continuous on
`U` and bounded on `B`. No harmonicity of `w` is assumed. -/
theorem energyJ_lt_of_le_add_inner {U B K : Set (E d)} {Q w w' φ : E d → ℝ}
    {Gw Gw' : E d → E d} (hU : IsOpen U) (hB : MeasurableSet B) (hBc : IsCompact (closure B))
    (hBU : closure B ⊆ U) (hK : IsCompact K) (hKB : K ⊆ B) (hQc : ContinuousOn Q U) {C : ℝ}
    (hQ : ∀ x ∈ B, |Q x| ≤ C) (hw : MemH1Loc U w Gw) (hw' : MemH1Loc U w' Gw')
    (hφ : ContDiff ℝ ∞ φ) (heq : ∀ x ∈ U \ K, w' x = w x)
    (hpt : ∀ᵐ x ∂(volume.restrict K),
      ‖Gw' x‖ ^ 2 + Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (w' x) ≤
        ‖Gw x‖ ^ 2 + Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (w x) +
          2 * inner ℝ (Gw' x - Gw x) (∇ φ x))
    (hpos : 0 < ∫ x in U, (w' x - w x) * Δ φ x) :
    energyJ B Q w' Gw' < energyJ B Q w Gw := by
  have hBU' : B ⊆ U := subset_closure.trans hBU
  have hKU : K ⊆ U := hKB.trans hBU'
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hfinB : energyJ B Q w Gw < ⊤ := energyJ_lt_top hw hBc hBU hQ
  rw [energyJ_split hKm hB hKB Q w', energyJ_split hKm hB hKB Q w] at *
  -- off `K` the energies agree
  have hGae : ∀ᵐ x ∂(volume.restrict (U \ K)), Gw' x = Gw x :=
    hw'.1.ae_eq_of_eqOn hU (hU.sdiff hK.isClosed) diff_subset hw.1 fun x hx ↦ heq x hx
  have hout : energyJ (B \ K) Q w' Gw' = energyJ (B \ K) Q w Gw :=
    energyJ_congr (fun x hx ↦ heq x ⟨hBU' hx.1, hx.2⟩)
      (ae_restrict_of_ae_restrict_of_subset (diff_subset_diff_left hBU') hGae)
  rw [hout]
  have hfin : energyJ (B \ K) Q w Gw ≠ ⊤ :=
    (lt_of_le_of_lt le_add_self hfinB).ne
  refine ENNReal.add_lt_add_right hfin ?_
  -- on `K`: reduce to real integrals
  have hQK : ∀ x ∈ K, |Q x| ≤ C := fun x hx ↦ hQ x (hKB hx)
  have hL2 := hw.2 K hKU hK
  have hL2' := hw'.2 K hKU hK
  set F : E d → ℝ := fun x ↦ ‖Gw x‖ ^ 2 + Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (w x) with hF
  set F' : E d → ℝ := fun x ↦ ‖Gw' x‖ ^ 2 + Q x ^ 2 * (Ioi (0 : ℝ)).indicator 1 (w' x)
    with hF'
  have hind0 : ∀ t : ℝ, 0 ≤ (Ioi (0 : ℝ)).indicator (1 : ℝ → ℝ) t :=
    fun t ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) t
  have hFnn : ∀ x, 0 ≤ F x := fun x ↦ add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hind0 _))
  have hF'nn : ∀ x, 0 ≤ F' x :=
    fun x ↦ add_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (hind0 _))
  have hFi : IntegrableOn F K :=
    hL2.2.norm.integrable_sq.add (integrableOn_posTerm hK (hQc.mono hKU) hQK hL2.1.1)
  have hF'i : IntegrableOn F' K :=
    hL2'.2.norm.integrable_sq.add (integrableOn_posTerm hK (hQc.mono hKU) hQK hL2'.1.1)
  have hIi : IntegrableOn (fun x ↦ inner ℝ (Gw' x - Gw x) (∇ φ x)) K :=
    integrableOn_inner_gradient hK (hL2'.2.sub hL2.2) (hφ.of_le (by simp))
  -- integration by parts
  have h0 : ∀ᵐ x ∂(volume.restrict (U \ K)), w' x - w x = 0 := by
    rw [ae_restrict_iff' (hU.measurableSet.diff hKm)]
    exact Eventually.of_forall fun x hx ↦ by rw [heq x hx, sub_self]
  have hIBP := (hw'.1.sub hw.1).integral_inner_gradient_eq_neg hU hK hKU h0 hφ
  have hKtoU : ∫ x in U, inner ℝ (Gw' x - Gw x) (∇ φ x) =
      ∫ x in K, inner ℝ (Gw' x - Gw x) (∇ φ x) := by
    refine setIntegral_eq_of_subset_of_ae_diff_eq_zero hU.measurableSet.nullMeasurableSet hKU ?_
    rw [ae_restrict_iff' (hU.measurableSet.diff hKm)] at hGae
    filter_upwards [hGae] with x hx hxUK
    rw [hx hxUK, sub_self, inner_zero_left]
  have hle : ∫ x in K, F' x ≤ ∫ x in K, (F x + 2 * inner ℝ (Gw' x - Gw x) (∇ φ x)) :=
    integral_mono_ae hF'i (hFi.add (hIi.const_mul 2)) hpt
  rw [integral_add hFi (hIi.const_mul 2), integral_const_mul, ← hKtoU, hIBP] at hle
  have hlt : ∫ x in K, F' x < ∫ x in K, F x := by linarith
  have hF'0 : 0 ≤ ∫ x in K, F' x := integral_nonneg hF'nn
  rw [energyJ_eq_lintegral_indicator_Ioi hKm, energyJ_eq_lintegral_indicator_Ioi hKm,
    ← ofReal_integral_eq_lintegral_ofReal hF'i (Eventually.of_forall hF'nn),
    ← ofReal_integral_eq_lintegral_ofReal hFi (Eventually.of_forall hFnn)]
  exact (ENNReal.ofReal_lt_ofReal_iff (hF'0.trans_lt hlt)).2 hlt

end EllipticBernoulli
