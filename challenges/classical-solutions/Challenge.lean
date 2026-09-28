import Challenge.Setting
import Challenge.Sobolev
import Challenge.Touching
import Challenge.Viscosity
import Challenge.Regularity
import Challenge.Variational

/-!
# Challenge: classical solutions

Trusted statement surface for classical solutions of the one-phase problem (`IsClassicalSolution`:
the classical solutions of Kriventsov–Weiss, Definition 9.1, with a variable coefficient `Q`; `u`
Lipschitz, harmonic in `{u > 0}`, the free boundary locally the zero set of a smooth `F` with
`∇F ≠ 0`, and the normal difference quotient into `{u > 0}` tending to `Q`). Classical solutions are
viscosity solutions (Abedin–Feldman–Stinson, Definition 2.1); for Lipschitz `Q ≥ c > 0` they satisfy
the inner-variation identity (Abedin–Feldman–Stinson, (2.5), with `χ = 1_{{u>0} ∩ U}`, for Lipschitz
test fields compactly supported in `U`); and, for `Q ≡ 1`, they satisfy the Alt–Caffarelli gradient
bound `sup_{B_r} |∇u| ≤ 1 + ω(r)` with a modulus `ω` depending on the Lipschitz bound `L`
(Alt–Caffarelli, Thm 6.3, as cited in Kriventsov–Weiss, Proposition 9.1; Kriventsov–Weiss numbers
are those of arXiv:2306.10131v2). Kriventsov–Weiss state the modulus as depending only on the
dimension.

The project vocabulary is restated in `Challenge/*.lean`, one file per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`, `Basic/Touching.lean`,
`Defs/Viscosity.lean`, `Defs/Regularity.lean`, `Defs/Variational.lean`), with the library's
names, definitions and order. Every file imports Mathlib modules only (the same ones as the
library file it restates).

## References

* D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: classical solutions are viscosity solutions. -/
theorem challenge_isClassicalSolution_isViscSolution {U : Set (E d)} {Q u : E d → ℝ}
    (hu : IsClassicalSolution U Q u) (hQ : ContinuousOn Q U) : IsViscSolution U Q u := by
  sorry

/-- Challenge: classical solutions satisfy the inner-variation identity with
`χ = 1_{{u>0} ∩ U}`. -/
theorem challenge_isClassicalSolution_integral_innerVarIntegrand_eq_zero {U : Set (E d)}
    {Q u : E d → ℝ} {ξ : E d → E d}
    (hu : IsClassicalSolution U Q u) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ y ∈ U, c ≤ Q y) (hξ : ∃ K, LipschitzWith K ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ U) :
    ∫ x in U, innerVarIntegrand Q u ((posSet u U).indicator 1) ξ x = 0 := by
  sorry

/-- Challenge: the Alt–Caffarelli gradient bound for `L`-Lipschitz classical solutions with `Q ≡ 1`
and `u(0) = 0` on `B_1`, encoded as a Lipschitz bound `1 + ω(r)` on `B_r`. -/
theorem challenge_classical_lipschitz_bound (L : ℝ≥0) :
    ∃ w : ℝ → ℝ, ContinuousOn w (Ico 0 1) ∧ MonotoneOn w (Ico 0 1) ∧
      Tendsto w (𝓝[>] 0) (𝓝 0) ∧
      ∀ u : E d → ℝ, IsClassicalSolution (ball 0 1) (fun _ ↦ 1) u →
        LipschitzOnWith L u (ball 0 1) →
        u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r) := by
  sorry

end EllipticBernoulli
