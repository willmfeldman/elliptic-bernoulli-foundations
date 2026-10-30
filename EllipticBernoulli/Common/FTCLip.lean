/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Fundamental theorem of calculus for Lipschitz functions

A Lipschitz function on a compact interval is absolutely continuous
(`LipschitzOnWith.absolutelyContinuousOnInterval`), so the fundamental theorem of calculus for
absolutely continuous functions (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) applies.
This file records the consequences used for radial calculus.

* `LipschitzOnWith.integral_deriv_eq_sub`: `∫_a^b f' = f b - f a`.
* `LipschitzOnWith.integral_eq_sub_of_ae_hasDerivAt`: the same with any a.e. derivative `f'`
  (`AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt` for absolutely continuous
  `f`).
* `LipschitzOnWith.integral_le_sub_of_ae_le`: if `g ≤ f'` a.e., then `∫_a^b g ≤ f b - f a`.
* `LipschitzOnWith.monotoneOn_of_ae_nonneg`, `LocallyLipschitzOn.monotoneOn_of_ae_nonneg`:
  a nonnegative a.e. derivative makes `f` nondecreasing.
-/

open MeasureTheory Set Filter
open scoped NNReal

public section

namespace AbsolutelyContinuousOnInterval

variable {f : ℝ → ℝ} {a b : ℝ}

/-- **FTC for absolutely continuous functions, with a given a.e. derivative.** If `f` is
absolutely continuous on `[a, b]` and has derivative `f' x` at a.e. `x` in `[a, b]`, then
`∫_a^b f' = f b - f a`. -/
theorem integral_eq_sub_of_ae_hasDerivAt {f' : ℝ → ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hf' : ∀ᵐ x, x ∈ uIoo a b → HasDerivAt f (f' x) x) :
    ∫ x in a..b, f' x = f b - f a := by
  rw [← hf.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  have hb : ∀ᵐ x : ℝ, x ≠ max a b := volume.ae_ne (max a b)
  filter_upwards [hf', hb] with x hx hxb hmem
  have hmem' : x ∈ uIoo a b := by
    rw [uIoc, mem_Ioc] at hmem
    exact ⟨hmem.1, lt_of_le_of_ne hmem.2 hxb⟩
  exact (hx hmem').deriv.symm

end AbsolutelyContinuousOnInterval

namespace LipschitzOnWith

variable {f : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}

/-- **FTC for Lipschitz functions.** If `f` is Lipschitz on `[a, b]`, then
`∫_a^b f' = f b - f a`. -/
theorem integral_deriv_eq_sub (hf : LipschitzOnWith K f (uIcc a b)) :
    ∫ x in a..b, deriv f x = f b - f a :=
  hf.absolutelyContinuousOnInterval.integral_deriv_eq_sub

/-- A Lipschitz function on `[a, b]` has an interval-integrable derivative. -/
theorem intervalIntegrable_deriv (hf : LipschitzOnWith K f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b :=
  hf.absolutelyContinuousOnInterval.intervalIntegrable_deriv

/-- **FTC for Lipschitz functions, with a given a.e. derivative.** If `f` is Lipschitz on
`[a, b]` and `f` has derivative `f' x` at a.e. `x` in `[a, b]`, then `∫_a^b f' = f b - f a`. -/
theorem integral_eq_sub_of_ae_hasDerivAt {f' : ℝ → ℝ} (hf : LipschitzOnWith K f (uIcc a b))
    (hf' : ∀ᵐ x, x ∈ uIoo a b → HasDerivAt f (f' x) x) :
    ∫ x in a..b, f' x = f b - f a :=
  hf.absolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt hf'

/-- If `f` is Lipschitz on `[a, b]` with `a ≤ b`, `g` is integrable on `[a, b]`, and
`g ≤ f'` a.e. on `[a, b]`, then `∫_a^b g ≤ f b - f a`. -/
theorem integral_le_sub_of_ae_le {g : ℝ → ℝ} (hab : a ≤ b) (hf : LipschitzOnWith K f (Icc a b))
    (hg : IntervalIntegrable g volume a b) (hgf : ∀ᵐ x, x ∈ Ioo a b → g x ≤ deriv f x) :
    ∫ x in a..b, g x ≤ f b - f a := by
  have hf' : LipschitzOnWith K f (uIcc a b) := by rwa [uIcc_of_le hab]
  rw [← hf'.integral_deriv_eq_sub]
  refine intervalIntegral.integral_mono_ae_restrict hab hg hf'.intervalIntegrable_deriv ?_
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  have hb : ∀ᵐ x : ℝ, x ≠ b := volume.ae_ne b
  have ha : ∀ᵐ x : ℝ, x ≠ a := volume.ae_ne a
  filter_upwards [hgf, ha, hb] with x hx hxa hxb hmem
  exact hx ⟨lt_of_le_of_ne hmem.1 (Ne.symm hxa), lt_of_le_of_ne hmem.2 hxb⟩

/-- If `f` is Lipschitz on `[a, b]` and `f' ≥ 0` a.e. on `[a, b]`, then `f` is nondecreasing on
`[a, b]`. -/
theorem monotoneOn_of_ae_nonneg (hf : LipschitzOnWith K f (Icc a b))
    (hpos : ∀ᵐ x, x ∈ Ioo a b → 0 ≤ deriv f x) : MonotoneOn f (Icc a b) := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have h := (hf.mono hsub).integral_le_sub_of_ae_le (g := 0) hxy intervalIntegrable_const
    (by
      filter_upwards [hpos] with t ht htm
      exact ht ⟨lt_of_le_of_lt hx.1 htm.1, lt_of_lt_of_le htm.2 hy.2⟩)
  simp only [Pi.zero_apply, intervalIntegral.integral_zero] at h
  linarith

end LipschitzOnWith

namespace LocallyLipschitzOn

variable {f : ℝ → ℝ} {s : Set ℝ}

/-- If `f` is locally Lipschitz on an order-connected set `s` (an interval) and `f' ≥ 0` a.e. on
`s`, then `f` is nondecreasing on `s`. -/
theorem monotoneOn_of_ae_nonneg (hs : s.OrdConnected) (hf : LocallyLipschitzOn s f)
    (hpos : ∀ᵐ x, x ∈ s → 0 ≤ deriv f x) : MonotoneOn f s := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ s := hs.out hx hy
  obtain ⟨K, hK⟩ := (hf.mono hsub).exists_lipschitzOnWith_of_compact isCompact_Icc
  refine hK.monotoneOn_of_ae_nonneg ?_ (left_mem_Icc.2 hxy) (right_mem_Icc.2 hxy) hxy
  filter_upwards [hpos] with t ht htm
  exact ht (hsub (Ioo_subset_Icc_self htm))

/-- If `f` is locally Lipschitz on an order-connected set `s` containing `a ≤ b`, `g` is
integrable on `[a, b]`, and `g ≤ f'` a.e. on `s`, then `∫_a^b g ≤ f b - f a`. -/
theorem integral_le_sub_of_ae_le {g : ℝ → ℝ} {a b : ℝ} (hs : s.OrdConnected)
    (hf : LocallyLipschitzOn s f) (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b) (hgf : ∀ᵐ x, x ∈ s → g x ≤ deriv f x) :
    ∫ x in a..b, g x ≤ f b - f a := by
  have hsub : Icc a b ⊆ s := hs.out ha hb
  obtain ⟨K, hK⟩ := (hf.mono hsub).exists_lipschitzOnWith_of_compact isCompact_Icc
  refine hK.integral_le_sub_of_ae_le hab hg ?_
  filter_upwards [hgf] with t ht htm
  exact ht (hsub (Ioo_subset_Icc_self htm))

end LocallyLipschitzOn
