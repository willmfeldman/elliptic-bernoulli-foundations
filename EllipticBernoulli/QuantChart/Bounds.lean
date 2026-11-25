/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Uniform bounds on partial derivatives over a compact set

`exists_bound_iteratedFDeriv_slice`: if `H : E × F → G` is smooth on an open `O` and `K ⊆ O` is
compact, then the iterated derivatives of the slices `b ↦ H (a, b)` of order `≤ n` are bounded
uniformly for `(a, b) ∈ K`. This gives bounds on families such as `q ↦ gradVec e q` that are
uniform in the parameter `e` on the unit sphere, without explicit formulas.

The proof is Faà di Bruno (`norm_iteratedFDerivWithin_comp_le`) for `H ∘ (b ↦ (a, b))`: the inner
map is affine with linear part `inr` of norm `≤ 1`. Then `‖D^i H‖` is bounded on `K` by
continuity and compactness.
-/

open Set Filter Topology
open scoped ContDiff Nat

public section

namespace EllipticBernoulli

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The slice map `b ↦ (a, b)` has `‖D^i‖ ≤ 1` for `i ≥ 1`. -/
private theorem norm_iteratedFDeriv_slice_le (a : E) {i : ℕ} (hi : 1 ≤ i) (b : F) :
    ‖iteratedFDeriv ℝ i (fun b : F ↦ (a, b)) b‖ ≤ 1 := by
  have hfd : fderiv ℝ (fun b : F ↦ (a, b)) = fun _ ↦ ContinuousLinearMap.inr ℝ E F := by
    funext b'
    exact ((hasFDerivAt_const a b').prodMk (hasFDerivAt_id b')).fderiv
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    exact ContinuousLinearMap.norm_inr_le_one ℝ E F
  · rw [iteratedFDeriv_const_of_ne hj.ne', Pi.zero_apply, norm_zero]; exact zero_le_one

/-- **Uniform bounds on partial derivatives over a compact set.** -/
theorem exists_bound_iteratedFDeriv_slice {H : E × F → G} {O : Set (E × F)} (hO : IsOpen O)
    (hH : ContDiffOn ℝ ∞ H O) {K : Set (E × F)} (hK : IsCompact K) (hKO : K ⊆ O) (n : ℕ) :
    ∃ M, ∀ p ∈ K, ∀ i ≤ n, ‖iteratedFDeriv ℝ i (fun b ↦ H (p.1, b)) p.2‖ ≤ M := by
  -- bounds on `‖D^j H‖` over `K`
  have hj : ∀ j : ℕ, ∃ Mj, ∀ p ∈ K, ‖iteratedFDeriv ℝ j H p‖ ≤ Mj := by
    intro j
    have hc : ContinuousOn (fun p ↦ ‖iteratedFDeriv ℝ j H p‖) O := by
      have := hH.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast le_top)
        hO.uniqueDiffOn
      exact (this.congr fun p hp ↦ (iteratedFDerivWithin_of_isOpen j hO hp).symm).norm
    obtain ⟨Mj, hMj⟩ := hK.exists_bound_of_continuousOn (hc.mono hKO)
    exact ⟨Mj, fun p hp ↦ (le_abs_self _).trans (by simpa using hMj p hp)⟩
  choose Mj hMj using hj
  set C := ∑ j ∈ Finset.range (n + 1), |Mj j| with hC
  have hCj : ∀ j ≤ n, ∀ p ∈ K, ‖iteratedFDeriv ℝ j H p‖ ≤ C := fun j hjn p hp ↦
    (hMj j p hp).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j ↦ |Mj j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hjn))))
  refine ⟨n ! * C, fun p hp i hi ↦ ?_⟩
  set s : Set F := {b | (p.1, b) ∈ O} with hs
  have hso : IsOpen s := hO.preimage (by fun_prop)
  have hps : p.2 ∈ s := by simpa [hs] using hKO hp
  have hslice : ContDiffOn ℝ ∞ (fun b : F ↦ (p.1, b)) s := by fun_prop
  have hmaps : MapsTo (fun b : F ↦ (p.1, b)) s O := fun b hb ↦ hb
  have := norm_iteratedFDerivWithin_comp_le (n := i) hH hslice (by exact_mod_cast le_top)
    hO.uniqueDiffOn hso.uniqueDiffOn hmaps hps (C := C) (D := 1)
    (fun j hj ↦ by
      rw [iteratedFDerivWithin_of_isOpen j hO (hKO hp)]
      exact hCj j (hj.trans hi) p hp)
    (fun j hj1 _ ↦ by
      rw [iteratedFDerivWithin_of_isOpen j hso hps, one_pow]
      exact norm_iteratedFDeriv_slice_le p.1 hj1 p.2)
  rw [iteratedFDerivWithin_of_isOpen i hso hps] at this
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  calc ‖iteratedFDeriv ℝ i (fun b ↦ H (p.1, b)) p.2‖ ≤ i ! * C * 1 ^ i := this
    _ = i ! * C := by ring
    _ ≤ n ! * C := by gcongr

end EllipticBernoulli
