import Challenge.Setting
import Challenge.Sobolev

/-!
# Challenge: energy-decreasing perturbations (the proof of Feldman–Kim–Požár, Lemma 3.3)

Trusted statement surface for the perturbation step in the proof of Feldman–Kim–Požár, Lemma 3.3,
together with their Lemma A.1; Abedin–Feldman–Stinson use it in the proof of their Lemma 6.3. The
statements are the key step of that proof, not the lemma itself (minimizers are viscosity
solutions), which is certified in `challenges/viscosity-minimizers`.

Let `w ≥ 0` be continuous on the open set `U`, with weak gradient `Gw`, and let a smooth `φ`
touch `w` strictly from below, or `φ₊` touch `w` strictly from above relative to
`\overline{{w > 0}}`, at a point `x₀` of an open `B ⊂⊂ U`, where the supersolution (resp.
subsolution) test of the one-phase problem `|∇u| = Q` fails. Let `Q` be Lipschitz with
`0 < c ≤ Q ≤ C` on `U`. Then for every `ρ, η > 0` a local perturbation of `w` inside
`B_ρ(x₀) ⊆ B`, trapped between `w` and `max(w, φ + η)` (resp. `min(w, (φ − η)₊)` and `w`), has
strictly smaller Alt–Caffarelli energy `J_Q(·; B) = ∫_B |∇·|² + Q² 1_{·>0}`.

The project vocabulary is restated in `Challenge/*.lean`, one file per library file
(`Basic/Setting.lean`, `Basic/Sobolev.lean`), with the library's names, definitions and order.
Every file imports Mathlib modules only (the same ones as the library file it restates).

## References

* W. M. Feldman, I. C. Kim, N. Požár, *On the geometry of rate-independent droplet evolution*,
  Calc. Var. Partial Differential Equations 65 (2026), no. 10, Paper No. 265; arXiv:2310.03656.
  Result numbers are those of arXiv:2310.03656v2.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

namespace EllipticBernoulli

variable {d : ℕ}

/-- Challenge: energy decrease when the supersolution test fails at a strict touching point
from below (proof of Feldman–Kim–Požár, Lemma 3.3). -/
theorem challenge_energy_decrease_of_not_super {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (htouch : φ x₀ = w x₀ ∧ ∀ᶠ y in 𝓝[≠] x₀, φ y < w y)
    (hfail : 0 < Δ φ x₀ ∧ (φ x₀ = 0 → Q x₀ < ‖∇ φ x₀‖)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, w y ≤ w' y ∧ w' y ≤ max (w y) (φ y + η)) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  sorry

/-- Challenge: energy decrease when the subsolution test fails at a strict touching point
from above (proof of Feldman–Kim–Požár, Lemma 3.3). -/
theorem challenge_energy_decrease_of_not_sub {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (hx₀pos : x₀ ∈ closure (posSet w U))
    (htouch : max (φ x₀) 0 = w x₀ ∧
      ∀ᶠ y in 𝓝[(closure (posSet w U) ∩ U) \ {x₀}] x₀, w y < max (φ y) 0)
    (hfail : Δ φ x₀ < 0 ∧ (φ x₀ = 0 → ‖∇ φ x₀‖ < Q x₀)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, min (w y) (max (φ y - η) 0) ≤ w' y ∧ w' y ≤ w y) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw := by
  sorry

end EllipticBernoulli
