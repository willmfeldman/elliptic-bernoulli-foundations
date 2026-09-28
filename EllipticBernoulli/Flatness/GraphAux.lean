/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Generic Hölder and differentiability lemmas for the free-boundary graph

PDE-free helpers for `Flatness/Graph.lean`, filling a gap in Mathlib: a compactly supported
function with a Hölder derivative on its support is globally `HolderWith`.

* `holderWith_of_dist_le`: the `dist` form of `HolderWith`.
* `exists_holderWith_of_local`: a bounded map that is `r`-Hölder at distances `≤ δ` is globally
  `r`-Hölder.
* `hasFDerivAt_of_norm_le_rpow`: a first-order Taylor bound `‖f (x + k) - f x - L k‖ ≤ K ‖k‖^{1+α}`
  for `‖k‖ ≤ δ` gives `HasFDerivAt f L x`.
* `exists_contDiff_holderWith_fderiv_mul`: the cutoff product `χ · h`, with `χ` a `C²` function of
  compact support and `h` differentiable, bounded, locally Lipschitz with locally Hölder
  derivative on a `δ`-neighbourhood of `tsupport χ`, is `C¹` with globally Hölder `fderiv`.
-/

open Set Filter Topology Metric Asymptotics
open scoped NNReal ENNReal

public section

namespace EllipticBernoulli

section Holder

variable {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]

/-- The `dist` form of `HolderWith`. -/
theorem holderWith_of_dist_le {C r : ℝ≥0} {F : X → Y}
    (h : ∀ x y, dist (F x) (F y) ≤ C * dist x y ^ (r : ℝ)) : HolderWith C r F := by
  intro x y
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (NNReal.coe_nonneg r),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg C)]
  exact ENNReal.ofReal_le_ofReal (h x y)

/-- **Local Hölder plus bounded gives global Hölder.** If `‖F‖ ≤ M` and
`dist (F x) (F y) ≤ K dist x y ^ r` whenever `dist x y ≤ δ` (`δ > 0`), then `F` is `r`-Hölder. -/
theorem exists_holderWith_of_local {r : ℝ≥0} {F : X → Y} {δ K M : ℝ} (hδ : 0 < δ)
    (hM : ∀ x, ‖F x‖ ≤ M)
    (hK : ∀ x y, dist x y ≤ δ → dist (F x) (F y) ≤ K * dist x y ^ (r : ℝ)) :
    ∃ C : ℝ≥0, HolderWith C r F := by
  set M' := max M 0
  set K' := max K 0
  have hδr : 0 < δ ^ (r : ℝ) := Real.rpow_pos_of_pos hδ _
  refine ⟨⟨K' + 2 * M' / δ ^ (r : ℝ), by positivity⟩, holderWith_of_dist_le fun x y ↦ ?_⟩
  change dist (F x) (F y) ≤ (K' + 2 * M' / δ ^ (r : ℝ)) * dist x y ^ (r : ℝ)
  have hd : 0 ≤ dist x y ^ (r : ℝ) := Real.rpow_nonneg dist_nonneg _
  have hA : 0 ≤ 2 * M' / δ ^ (r : ℝ) * dist x y ^ (r : ℝ) := by positivity
  rcases le_or_gt (dist x y) δ with hxy | hxy
  · calc dist (F x) (F y) ≤ K * dist x y ^ (r : ℝ) := hK x y hxy
      _ ≤ K' * dist x y ^ (r : ℝ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hd
      _ ≤ (K' + 2 * M' / δ ^ (r : ℝ)) * dist x y ^ (r : ℝ) := by rw [add_mul]; linarith
  · have h1 : dist (F x) (F y) ≤ 2 * M' := by
      rw [dist_eq_norm]
      calc ‖F x - F y‖ ≤ ‖F x‖ + ‖F y‖ := norm_sub_le _ _
        _ ≤ M' + M' := add_le_add ((hM x).trans (le_max_left _ _))
            ((hM y).trans (le_max_left _ _))
        _ = 2 * M' := by ring
    have h2 : 2 * M' ≤ 2 * M' / δ ^ (r : ℝ) * dist x y ^ (r : ℝ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδr]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ.le hxy.le (NNReal.coe_nonneg r))
        (mul_nonneg zero_le_two (le_max_right _ _))
    have hK0 : 0 ≤ K' * dist x y ^ (r : ℝ) := mul_nonneg (le_max_right _ _) hd
    rw [add_mul]
    linarith

end Holder

section Deriv

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- **Differentiability from a first-order Taylor bound.** If
`‖f (x + k) - f x - L k‖ ≤ K ‖k‖^{1+α}` for `‖k‖ ≤ δ`, with `δ, α > 0`, then `f` has derivative
`L` at `x`. -/
theorem hasFDerivAt_of_norm_le_rpow {f : E → F} {L : E →L[ℝ] F} {x : E} {δ K α : ℝ}
    (hδ : 0 < δ) (hα : 0 < α)
    (h : ∀ k, ‖k‖ ≤ δ → ‖f (x + k) - f x - L k‖ ≤ K * ‖k‖ ^ (1 + α)) : HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro c hc
  have ht : Tendsto (fun k : E ↦ K * ‖k‖ ^ α) (𝓝 0) (𝓝 (K * ‖(0 : E)‖ ^ α)) :=
    tendsto_const_nhds.mul ((continuous_norm.tendsto 0).rpow_const (Or.inr hα.le))
  rw [norm_zero, Real.zero_rpow hα.ne', mul_zero] at ht
  have h1 : ∀ᶠ k in 𝓝 (0 : E), K * ‖k‖ ^ α < c := ht.eventually (gt_mem_nhds hc)
  have h2 : ∀ᶠ k in 𝓝 (0 : E), ‖k‖ ≤ δ := by
    filter_upwards [closedBall_mem_nhds (0 : E) hδ] with k hk
    simpa using hk
  filter_upwards [h1, h2] with k hk1 hk2
  calc ‖f (x + k) - f x - L k‖ ≤ K * ‖k‖ ^ (1 + α) := h k hk2
    _ = (K * ‖k‖ ^ α) * ‖k‖ := by
      rw [Real.rpow_add' (norm_nonneg _) (by positivity), Real.rpow_one]; ring
    _ ≤ c * ‖k‖ := mul_le_mul_of_nonneg_right hk1.le (norm_nonneg _)

/-- **The cutoff product.** Let `χ` be `C²` with compact support, and let `h` be differentiable
with derivative `h'` on a set `D` containing the `δ`-neighbourhood of `tsupport χ` (`0 < δ ≤ 1`),
with `|h|, ‖h'‖ ≤ B` on `D` and, for `z, w ∈ D` with `dist z w ≤ δ`, `|h z - h w| ≤ K dist z w`
and `‖h' z - h' w‖ ≤ K dist z w ^ r` (`0 < r ≤ 1`). Then `χ · h` is `C¹` and its `fderiv` is
globally `r`-Hölder. -/
theorem exists_contDiff_holderWith_fderiv_mul {χ h : E → ℝ} {h' : E → E →L[ℝ] ℝ} {D : Set E}
    {r : ℝ≥0} {δ B K : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hB0 : 0 ≤ B) (hK0 : 0 ≤ K) (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hD : ∀ z w, z ∈ tsupport χ → dist z w ≤ δ → w ∈ D)
    (hh : ∀ z ∈ D, HasFDerivAt h (h' z) z)
    (hB : ∀ z ∈ D, |h z| ≤ B ∧ ‖h' z‖ ≤ B)
    (hK : ∀ z ∈ D, ∀ w ∈ D, dist z w ≤ δ →
      |h z - h w| ≤ K * dist z w ∧ ‖h' z - h' w‖ ≤ K * dist z w ^ (r : ℝ)) :
    ContDiff ℝ 1 (fun z ↦ χ z * h z) ∧
      ∃ C : ℝ≥0, HolderWith C r (fderiv ℝ (fun z ↦ χ z * h z)) := by
  set dχ := fderiv ℝ χ with hdχ_def
  set F : E → E →L[ℝ] ℝ := fun z ↦ χ z • h' z + h z • dχ z with hF_def
  have hmemD : ∀ z ∈ tsupport χ, z ∈ D := fun z hz ↦ hD z z hz (by simp [hδ.le])
  -- `F` is the derivative everywhere
  have hderiv : ∀ z, HasFDerivAt (fun z ↦ χ z * h z) (F z) z := by
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact ((hχ.differentiable (by norm_num)).differentiableAt.hasFDerivAt).fun_mul
        (hh z (hmemD z hz))
    · have h0 : χ z = 0 := image_eq_zero_of_notMem_tsupport hz
      have h1 : dχ z = 0 := fderiv_of_notMem_tsupport ℝ hz
      have hFz : F z = 0 := by simp [hF_def, h0, h1]
      rw [hFz]
      exact HasFDerivAt.of_notMem_tsupport ℝ fun hz' ↦ hz (tsupport_mul_subset_left hz')
  have hfd : fderiv ℝ (fun z ↦ χ z * h z) = F := funext fun z ↦ (hderiv z).fderiv
  -- constants for `χ` and `dχ`
  obtain ⟨Lχ, hLχ⟩ := hχ.lipschitzWith_of_hasCompactSupport hχc (by norm_num)
  have hdχ1 : ContDiff ℝ 1 dχ := ContDiff.fderiv_right (m := 1) hχ (by norm_num)
  obtain ⟨Ldχ, hLdχ⟩ := hdχ1.lipschitzWith_of_hasCompactSupport (hχc.fderiv ℝ) (by norm_num)
  obtain ⟨Mχ, hMχ⟩ := hχ.continuous.bounded_above_of_compact_support hχc
  obtain ⟨Mdχ, hMdχ⟩ := hdχ1.continuous.bounded_above_of_compact_support (hχc.fderiv ℝ)
  -- `F` vanishes off `tsupport χ`
  have hF0 : ∀ z, z ∉ tsupport χ → F z = 0 := fun z hz ↦ by
    simp [hF_def, image_eq_zero_of_notMem_tsupport hz, fderiv_of_notMem_tsupport ℝ hz, dχ]
  have hbound : ∀ z, ‖F z‖ ≤ Mχ * B + B * Mdχ := by
    intro z
    by_cases hz : z ∈ tsupport χ
    · obtain ⟨hb1, hb2⟩ := hB z (hmemD z hz)
      calc ‖F z‖ ≤ ‖χ z • h' z‖ + ‖h z • dχ z‖ := norm_add_le _ _
        _ = ‖χ z‖ * ‖h' z‖ + |h z| * ‖dχ z‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs (h z)]
        _ ≤ Mχ * B + B * Mdχ :=
          add_le_add (mul_le_mul (hMχ z) hb2 (norm_nonneg _) ((norm_nonneg _).trans (hMχ z)))
            (mul_le_mul hb1 (hMdχ z) (norm_nonneg _) hB0)
    · rw [hF0 z hz, norm_zero]
      have := (norm_nonneg _).trans (hMχ z)
      have := (norm_nonneg _).trans (hMdχ z)
      positivity
  have hloc : ∀ z w, dist z w ≤ δ →
      dist (F z) (F w) ≤ (Lχ * B + Mχ * K + K * Mdχ + B * Ldχ) * dist z w ^ (r : ℝ) := by
    intro z w hzw
    have hMχ0 : 0 ≤ Mχ := (norm_nonneg _).trans (hMχ z)
    have hMdχ0 : 0 ≤ Mdχ := (norm_nonneg _).trans (hMdχ z)
    have hdr : dist z w ≤ dist z w ^ (r : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge' dist_nonneg (hzw.trans hδ1)
        (NNReal.coe_nonneg r) (show (r : ℝ) ≤ 1 by exact_mod_cast hr1)
      rwa [Real.rpow_one] at this
    have hdr0 : 0 ≤ dist z w ^ (r : ℝ) := Real.rpow_nonneg dist_nonneg _
    by_cases hzw' : z ∈ tsupport χ ∨ w ∈ tsupport χ
    · have hzD : z ∈ D ∧ w ∈ D := by
        rcases hzw' with hz | hw
        · exact ⟨hmemD z hz, hD z w hz hzw⟩
        · exact ⟨hD w z hw (by rwa [dist_comm]), hmemD w hw⟩
      obtain ⟨hhz, hh'z⟩ := hB z hzD.1
      obtain ⟨hhw, hh'w⟩ := hB w hzD.2
      obtain ⟨hK1, hK2⟩ := hK z hzD.1 w hzD.2 hzw
      have hsplit : F z - F w = (χ z - χ w) • h' z + χ w • (h' z - h' w) +
          ((h z - h w) • dχ z + h w • (dχ z - dχ w)) := by
        simp only [hF_def]; module
      have e1 : |χ z - χ w| ≤ Lχ * dist z w := by
        simpa [Real.dist_eq] using hLχ.dist_le_mul z w
      have e2 : ‖dχ z - dχ w‖ ≤ Ldχ * dist z w := by
        simpa [dist_eq_norm] using hLdχ.dist_le_mul z w
      rw [dist_eq_norm, hsplit]
      calc ‖(χ z - χ w) • h' z + χ w • (h' z - h' w) +
            ((h z - h w) • dχ z + h w • (dχ z - dχ w))‖
          ≤ ‖(χ z - χ w) • h' z‖ + ‖χ w • (h' z - h' w)‖ +
            (‖(h z - h w) • dχ z‖ + ‖h w • (dχ z - dχ w)‖) :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
        _ = |χ z - χ w| * ‖h' z‖ + ‖χ w‖ * ‖h' z - h' w‖ +
            (|h z - h w| * ‖dχ z‖ + |h w| * ‖dχ z - dχ w‖) := by
            simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ (Lχ * dist z w) * B + Mχ * (K * dist z w ^ (r : ℝ)) +
            ((K * dist z w) * Mdχ + B * (Ldχ * dist z w)) :=
            add_le_add
              (add_le_add (mul_le_mul e1 hh'z (norm_nonneg _) (mul_nonneg Lχ.2 dist_nonneg))
                (mul_le_mul (hMχ w) hK2 (norm_nonneg _) hMχ0))
              (add_le_add (mul_le_mul hK1 (hMdχ z) (norm_nonneg _) (mul_nonneg hK0 dist_nonneg))
                (mul_le_mul hhw e2 (norm_nonneg _) hB0))
        _ ≤ (Lχ * dist z w ^ (r : ℝ)) * B + Mχ * (K * dist z w ^ (r : ℝ)) +
            ((K * dist z w ^ (r : ℝ)) * Mdχ + B * (Ldχ * dist z w ^ (r : ℝ))) :=
            add_le_add
              (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdr Lχ.2) hB0)
                le_rfl)
              (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdr hK0) hMdχ0)
                (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdr Ldχ.2) hB0))
        _ = (Lχ * B + Mχ * K + K * Mdχ + B * Ldχ) * dist z w ^ (r : ℝ) := by ring
    · push Not at hzw'
      rw [hF0 z hzw'.1, hF0 w hzw'.2, dist_self]
      positivity
  obtain ⟨C, hC⟩ := exists_holderWith_of_local hδ hbound hloc
  refine ⟨contDiff_one_iff_hasFDerivAt.2 ⟨F, ?_, hderiv⟩, C, hfd ▸ hC⟩
  exact hC.continuous hr0

end Deriv

end EllipticBernoulli
