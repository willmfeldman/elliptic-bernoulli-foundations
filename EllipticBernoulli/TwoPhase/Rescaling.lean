/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Regularity
public import EllipticBernoulli.Defs.TwoPhase
public import EllipticBernoulli.TwoPhase.Rescaling.Compact
public import EllipticBernoulli.TwoPhase.Rescaling.Euler
public import EllipticBernoulli.TwoPhase.Rescaling.Homogeneity
public import EllipticBernoulli.TwoPhase.Rescaling.Limits
public import EllipticBernoulli.TwoPhase.Rescaling.Strong
public import EllipticBernoulli.TwoPhase.Rescaling.TwoPlane
import EllipticBernoulli.Harmonic.Affine

/-!
# Rescalings and limits

Throughout, `u : ℝᵈ → ℝ` is `L`-Lipschitz with `u(x₀) = 0`,
and `u_k = u_{x₀,r_k}` (`blowup u x₀ (r k)`, `y ↦ u(x₀ + r_k y)/r_k`) with `r_k → 0⁺` or
`r_k → ∞`. The results are stated for an abstract sequence `f k` of `L`-Lipschitz functions with
`f k 0 = 0`, harmonic on `{f k > 0}` and on `{f k < 0}`; `harmonicOnNhd_blowup_posSet` and
`harmonicOnNhd_blowup_negSet` provide the harmonicity of the rescalings. The limit is never shown
to be a minimizer.

* `TwoPhase/Rescaling/Compact.lean`: compactness and harmonicity of the limit.
* `TwoPhase/Rescaling/Strong.lean`: strong convergence of the gradients of each phase.
* `TwoPhase/Rescaling/Euler.lean`: Euler's relation integrated.
* `TwoPhase/Rescaling/Homogeneity.lean`: the Weiss defect passes to the limit, so the limit is
  homogeneous; the defects of blow-ups and blow-downs of a minimizer tend to `0`.
* `TwoPhase/Rescaling/Limits.lean`: convergence of `W` and of `Φ`.
* `TwoPhase/Rescaling/TwoPlane.lean`: `W = |B₁|/2` for two-plane functions.

This file collects the harmonicity of rescalings and the combined statement
`exists_subseq_tendsto_homogeneous` used by the classification of global minimizers.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Harmonicity of rescalings, positive phase.** If `u` is harmonic
on `{u > 0}` and `r > 0`, then `u_{x₀,r}` is harmonic on `{u_{x₀,r} > 0}`. -/
theorem harmonicOnNhd_blowup_posSet {u : E d → ℝ} (hH : HarmonicOnNhd u {x | 0 < u x})
    (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    HarmonicOnNhd (blowup u x₀ r) {x | 0 < blowup u x₀ r x} := by
  have h := HarmonicOnNhd.rescale hH x₀ r
  have hset : {x | 0 < blowup u x₀ r x} = (fun x ↦ x₀ + r • x) ⁻¹' {x | 0 < u x} := by
    ext x
    simp only [blowup, mem_ofPred_eq, mem_preimage]
    exact div_pos_iff_of_pos_right hr
  rw [hset]
  exact h

/-- **Harmonicity of rescalings, negative phase.** If `u` is harmonic
on `{u < 0}` and `r > 0`, then `u_{x₀,r}` is harmonic on `{u_{x₀,r} < 0}`. -/
theorem harmonicOnNhd_blowup_negSet {u : E d → ℝ} (hH : HarmonicOnNhd u {x | u x < 0})
    (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    HarmonicOnNhd (blowup u x₀ r) {x | blowup u x₀ r x < 0} := by
  have h := HarmonicOnNhd.rescale hH x₀ r
  have hset : {x | blowup u x₀ r x < 0} = (fun x ↦ x₀ + r • x) ⁻¹' {x | u x < 0} := by
    ext x
    simp only [blowup, mem_ofPred_eq, mem_preimage]
    rw [div_lt_iff₀ hr, zero_mul]
  rw [hset]
  exact h

/-- The positive part of a rescaling is the rescaling of the positive part, for `r > 0`. -/
theorem posPart_blowup (u : E d → ℝ) (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    (fun y ↦ max (blowup u x₀ r y) 0) = blowup (fun y ↦ max (u y) 0) x₀ r := by
  funext y
  simp only [blowup]
  rw [← max_div_div_right hr.le, zero_div]

/-- The negative part of a rescaling is the rescaling of the negative part, for `r > 0`. -/
theorem negPart_blowup (u : E d → ℝ) (x₀ : E d) {r : ℝ} (hr : 0 < r) :
    (fun y ↦ max (-blowup u x₀ r y) 0) = blowup (fun y ↦ max (-u y) 0) x₀ r := by
  funext y
  simp only [blowup]
  rw [← max_div_div_right hr.le, zero_div, neg_div]

/-- **Limits of rescalings.** Let `f k` be `L`-Lipschitz with `f k 0 = 0`,
harmonic on `{f k > 0}` and on `{f k < 0}`, and suppose `D(f_k, 0; ρ, ρ') → 0` for all
`0 < ρ < ρ'`. Then along a subsequence `f k → f₀` locally uniformly, where `f₀` is `L`-Lipschitz,
positively `1`-homogeneous, and harmonic on `{f₀ > 0}` and on `{f₀ < 0}`; moreover
`Φ(f_k⁺, f_k⁻, 0, ρ) → Φ(f₀⁺, f₀⁻, 0, ρ)` for every `ρ`, and if `{f₀ = 0}` is null then
`W(f_k, 0, ρ) → W(f₀, 0, ρ)` for every `ρ > 0`. Minimality of `f₀` is not asserted. -/
theorem exists_subseq_tendsto_homogeneous (hd : 1 ≤ d) {f : ℕ → E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hf0 : ∀ k, f k 0 = 0)
    (hpos : ∀ k, HarmonicOnNhd (f k) {x | 0 < f k x})
    (hneg : ∀ k, HarmonicOnNhd (f k) {x | f k x < 0})
    (hD : ∀ ρ ρ' : ℝ, 0 < ρ → ρ < ρ' →
      Tendsto (fun k ↦ weissDefect (f k) 0 ρ ρ') atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : E d → ℝ, LipschitzWith L f₀ ∧
      TendstoLocallyUniformly (fun k ↦ f (φ k)) f₀ atTop ∧
      (∀ t : ℝ, 0 < t → ∀ x, f₀ (t • x) = t * f₀ x) ∧
      HarmonicOnNhd f₀ {x | 0 < f₀ x} ∧ HarmonicOnNhd f₀ {x | f₀ x < 0} ∧
      (∀ ρ : ℝ, Tendsto (fun k ↦ acfPhi (fun y ↦ max (f (φ k) y) 0)
        (fun y ↦ max (-f (φ k) y) 0) 0 ρ) atTop
          (𝓝 (acfPhi (fun y ↦ max (f₀ y) 0) (fun y ↦ max (-f₀ y) 0) 0 ρ))) ∧
      (volume {x | f₀ x = 0} = 0 → ∀ ρ : ℝ, 0 < ρ →
        Tendsto (fun k ↦ weissW (f (φ k)) 0 ρ) atTop (𝓝 (weissW f₀ 0 ρ))) := by
  obtain ⟨φ, hφ, f₀, hf₀, -, hconv⟩ := exists_subseq_tendstoLocallyUniformly_of_apply_zero hf hf0
  have hf' : ∀ k, LipschitzWith L (f (φ k)) := fun k ↦ hf _
  have hf0' : ∀ k, f (φ k) 0 = 0 := fun k ↦ hf0 _
  have hpos' : ∀ k, HarmonicOnNhd (f (φ k)) {x | 0 < f (φ k) x} := fun k ↦ hpos _
  have hneg' : ∀ k, HarmonicOnNhd (f (φ k)) {x | f (φ k) x < 0} := fun k ↦ hneg _
  refine ⟨φ, hφ, f₀, hf₀, hconv,
    homogeneous_of_tendsto_weissDefect hf' hf0' hpos' hneg' hconv
      (fun ρ ρ' hρ hρρ' ↦ (hD ρ ρ' hρ hρρ').comp hφ.tendsto_atTop),
    harmonicOnNhd_posSet_of_tendstoLocallyUniformly hpos' hf₀.continuous hconv,
    harmonicOnNhd_negSet_of_tendstoLocallyUniformly hneg' hf₀.continuous hconv,
    fun ρ ↦ tendsto_acfPhi_of_tendstoLocallyUniformly hd hf' hpos' hneg' hconv ρ,
    fun hnull ρ hρ ↦ tendsto_weissW_of_tendstoLocallyUniformly hf' hf0' hpos' hneg' hconv hnull hρ⟩

end EllipticBernoulli
