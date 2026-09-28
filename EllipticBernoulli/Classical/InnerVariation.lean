/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Classical
import EllipticBernoulli.Classical.Gradient
import EllipticBernoulli.Classical.InnerVariationCore

/-!
# The inner-variation identity for classical solutions

`IsClassicalSolution.integral_innerVarIntegrand_eq_zero : ClassicalInnerVarStatement`: for a
classical solution `u` in `U`, with `Q` Lipschitz and `Q ≥ c > 0` on `U`, and every Lipschitz test
field `ξ` with compact support in `U`, `∫_U innerVarIntegrand Q u 1_{{u > 0} ∩ U} ξ = 0`, with the
integrand of Abedin–Feldman–Stinson, Definition 2.8(iv). This is the remark after
Kriventsov–Weiss, Definition 9.1: a classical solution is a variational solution, by integration by
parts. Points with `{u > 0}` on both sides of the free boundary are allowed, and no dimension
hypothesis is needed. Both hypotheses on `Q` are used; `Q ≡ 1` qualifies.

The integration by parts needs `|∇u| → Q` uniformly up to the free boundary on compact sets, while
the classical definition gives only a one-sided normal difference quotient at each point. The proof
combines
* the gradient limit `IsClassicalSolution.tendsto_norm_gradient` (`Classical/Gradient.lean`):
  `‖∇u(x)‖ → Q(x₀)` as `x → x₀ ∈ F(u)` inside `{u > 0}`, side by side; and
* the cut-off computation `IsClassicalSolution.integral_innerVarIntegrand_eq_zero_of_tendsto`
  (`Classical/InnerVariationCore.lean`), which uses only that limit.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
  in the Bernoulli one-phase problem*, arXiv:2609.14981.
* D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131. Result numbers are those of arXiv:2306.10131v2.
-/

public section

namespace EllipticBernoulli

/-- **The inner-variation identity for classical solutions** (`ClassicalInnerVarStatement`;
Kriventsov–Weiss, remark after Definition 9.1). -/
theorem IsClassicalSolution.integral_innerVarIntegrand_eq_zero : ClassicalInnerVarStatement := by
  intro d U Q u ξ hu hQ hQpos hξ hξc hξU
  exact hu.integral_innerVarIntegrand_eq_zero_of_tendsto hQ hQpos hξ hξc hξU
    fun x₀ hx₀ ↦ hu.tendsto_norm_gradient hQ hQpos hx₀

end EllipticBernoulli
