/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Pointwise inner products of `L²` functions

Small shared facts about `∫ ⟪f, g⟫` for `f, g ∈ L²`.

## Main results

* `integral_inner_eq_L2`: `∫ ⟪f, g⟫` is the `L²` inner product of the classes.
* `integrable_inner_of_memLp`: `⟪f, g⟫` is integrable.
* `abs_integral_inner_le`, `abs_integral_mul_le_L2`: Cauchy–Schwarz in `L²`.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure X}

/-- `∫ ⟪f, g⟫` is the `L²` inner product. -/
theorem integral_inner_eq_L2 {f g : X → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, inner ℝ (f x) (g x) ∂μ = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

/-- The pointwise inner product of two `L²` functions is integrable. -/
theorem integrable_inner_of_memLp {f g : X → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x ↦ inner ℝ (f x) (g x)) μ := by
  refine (L2.integrable_inner (𝕜 := ℝ) hf.toLp hg.toLp).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x e₁ e₂
  rw [e₁, e₂]

/-- Cauchy–Schwarz in `L²`. -/
theorem abs_integral_inner_le {f g : X → F} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, inner ℝ (f x) (g x) ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  rw [integral_inner_eq_L2 hf hg]
  refine (abs_real_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [Lp.norm_toLp, Lp.norm_toLp]

/-- Cauchy–Schwarz in `L²` for real functions. -/
theorem abs_integral_mul_le_L2 {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have h := abs_integral_inner_le hf hg
  simpa only [Real.inner_apply] using h

end EllipticBernoulli
