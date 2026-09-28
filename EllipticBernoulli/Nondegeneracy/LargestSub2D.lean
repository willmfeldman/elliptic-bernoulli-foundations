/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Nondegeneracy
import EllipticBernoulli.Nondegeneracy.Planar.LargestSub

/-!
# Non-degeneracy of largest subsolutions in the plane (Orcan-Ekmekci)

* `isNondegenerateAt_of_isLocalLargestSub` (`LargestSubNondeg2DStatement`;
  Abedin–Feldman–Stinson, Theorem B.1):
  a local largest subsolution in `B_R(x₀) ⊆ ℝ²` with `Q ≥ q₀ > 0`, Lipschitz, `C²` and harmonic
  in `{u > 0}`, is non-degenerate at the free boundary point `x₀`, with constant
  `c = massConst q₀ (K + 1) / 480 / (4π)` (depending only on `q₀` and the Lipschitz constant `K`)
  and radius `ρ = R/2`.
* `exists_pos_le_of_isLocalLargestSub` (`LargestSubNondeg2DQuantStatement`): the same bound with
  the constant chosen before `u`, depending only on `q₀` and `K`.

Abedin–Feldman–Stinson assume only that `u` is a largest subsolution in `B_1` with
`0 ∈ ∂{u > 0}`, and conclude `sup_{∂B_r} u ≥ c r` for all `0 < r ≤ 1` by scaling. Here `u` is
also assumed Lipschitz, `C²` and harmonic in `{u > 0}`, with `Q ≥ q₀ > 0`; the conclusion is for
the supremum over the closed ball `B̄_r(x₀)`, `r ≤ R/2`, and the proof works at all small scales
directly, without a scaling reduction. `IsNondegenerateAt` only asserts some `c > 0` for the
given `u`; the quantitative form records that `c` depends only on `q₀` and `K`.

The proof (Riesz measure, Abedin–Feldman–Stinson, Lemma B.4, Vitali covering) is in
`Nondegeneracy/Planar/*`; see `exists_le_of_isLocalLargestSub` (`Planar/LargestSub.lean`).

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
  in the Bernoulli one-phase problem*, arXiv:2609.14981.
* B. Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary
  problem in ℝ²: elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3–4,
  937–962.
-/

public section

namespace EllipticBernoulli

/-- **Non-degeneracy of local largest subsolutions** in `d = 2` (`LargestSubNondeg2DStatement`;
Abedin–Feldman–Stinson, Theorem B.1, after Orcan-Ekmekci), for `u` that is
`K`-Lipschitz, `C²` and harmonic in `{u > 0}` (hypotheses not stated in the source). -/
theorem isNondegenerateAt_of_isLocalLargestSub : LargestSubNondeg2DStatement := by
  intro Q u x₀ R q₀ K hR hq₀ hQ hll hLip hC2 hΔ hx₀
  exact ⟨_, div_pos (div_pos (massConst_pos hq₀ (by positivity)) (by norm_num)) (by positivity),
    R / 2, by positivity, exists_le_of_isLocalLargestSub hq₀ hQ hll hLip hC2 hΔ hx₀⟩

/-- **Quantitative non-degeneracy of local largest subsolutions in `d = 2`**
(`LargestSubNondeg2DQuantStatement`; Abedin–Feldman–Stinson, Theorem B.1, after
Orcan-Ekmekci).
The constant `c = massConst q₀ (K + 1) / 480 / (4π)` depends only on `q₀` and the Lipschitz
constant `K`. The source assumes only that `u` is a largest subsolution; here `u` is also assumed
`K`-Lipschitz, `C²` and harmonic in `{u > 0}`. -/
theorem exists_pos_le_of_isLocalLargestSub : LargestSubNondeg2DQuantStatement :=
  fun q₀ K hq₀ ↦ ⟨_, div_pos (div_pos (massConst_pos hq₀ (by positivity)) (by norm_num))
    (by positivity), fun _ hQ hll hLip hC2 hΔ hx₀ ↦
      exists_le_of_isLocalLargestSub hq₀ hQ hll hLip hC2 hΔ hx₀⟩

end EllipticBernoulli
