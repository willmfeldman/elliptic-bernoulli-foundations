/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Shared calculus helpers

Calculus facts used in several parts of the library, for any real inner product space. This file
imports only Mathlib.

* `continuous_gradient`: the gradient of a `C¹` function is continuous.
* `norm_gradient_eq_norm_fderiv`: the gradient has the same norm as the Fréchet derivative.
-/

open scoped Gradient ContDiff

@[expose] public section

namespace EllipticBernoulli

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The gradient of a `C¹` function is continuous. -/
theorem continuous_gradient {k : F → ℝ} (hk : ContDiff ℝ 1 k) : Continuous (∇ k) := by
  have : ∇ k = fun y ↦ (InnerProductSpace.toDual ℝ F).symm (fderiv ℝ k y) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ F).symm.continuous.comp (hk.continuous_fderiv one_ne_zero)

/-- The gradient has the same norm as the Fréchet derivative. -/
theorem norm_gradient_eq_norm_fderiv (f : F → ℝ) (x : F) : ‖∇ f x‖ = ‖fderiv ℝ f x‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]

end EllipticBernoulli
