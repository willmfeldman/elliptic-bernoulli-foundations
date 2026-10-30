/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.TwoPhase
public import EllipticBernoulli.Sphere.Colatitude
import EllipticBernoulli.Sphere.CapODE
import EllipticBernoulli.Sphere.FaberKrahn

/-!
# The Friedland–Hayman inequality from the cap inequality

The proof of the Friedland–Hayman inequality `α_d(Γ₁) + α_d(Γ₂) ≥ 2` from Faber–Krahn on the
sphere and the cap inequality `ᾱ_d(θ) + ᾱ_d(π - θ) ≥ 2`, as in Salato (arXiv:2506.13473),
Proposition 3.3 and §5, Step 4:

1. disjointness gives `σ(Γ₂) ≤ σ(𝕊) - σ(Γ₁)`;
2. if `σ(C(θᵢ)) = σ(Γᵢ)`, then `θ₂ ≤ π - θ₁` (`toReal_toSphere_sphCap_pi_sub`: the cap of
   colatitude `π - θ` has measure `σ(𝕊) - σ(C(θ))`);
3. Faber–Krahn and the monotonicity of `κ_d` and of `ᾱ_d` give
   `α_d(Γ₁) + α_d(Γ₂) ≥ ᾱ_d(θ₁) + ᾱ_d(θ₂) ≥ ᾱ_d(θ₁) + ᾱ_d(π - θ₁)`.

Step 2 does not compare `C(π - θ₁)` with the complement of the closed cap `C̄(θ₁)` (an open cap
about `-N`); it uses the formula `σ(C(θ)) = c_d ∫_0^θ sin^{d-2}` and the symmetry
`sin (π - φ) = sin φ`.

## Main results

* `exists_capExponent_add_le_sphExponent_add`: for disjoint nonempty open `Γ₁, Γ₂ ⊆ 𝕊^{d-1}` there
  is `θ ∈ (0, π)` with `ᾱ_d(θ) + ᾱ_d(π - θ) ≤ α_d(Γ₁) + α_d(Γ₂)`.
* `friedlandHaymanIn_of_capInequality`: the cap inequality in dimension `d ≥ 2` implies
  `FriedlandHaymanIn d`.
* `friedlandHaymanIn_two`, `friedlandHaymanIn_four`.

## References

* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and
  the growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473 (v2).
-/

open Set MeasureTheory Metric Real
open scoped ENNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **The cap of colatitude `π - θ`** has measure `σ(𝕊) - σ(C(θ))`. -/
theorem toReal_toSphere_sphCap_pi_sub (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {θ : ℝ}
    (hθ : θ ∈ Icc 0 π) :
    ((volume : Measure (E d)).toSphere (sphCap N (π - θ))).toReal =
      ((volume : Measure (E d)).toSphere univ).toReal -
        ((volume : Measure (E d)).toSphere (sphCap N θ)).toReal := by
  have hθ' : π - θ ∈ Icc 0 π := ⟨sub_nonneg.2 hθ.2, sub_le_self _ hθ.1⟩
  rw [← toSphere_sphCap_pi hd hN, toReal_toSphere_sphCap hd hN hθ',
    toReal_toSphere_sphCap hd hN ⟨pi_pos.le, le_rfl⟩, toReal_toSphere_sphCap hd hN hθ, ← mul_sub]
  congr 1
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun φ ↦ sin φ ^ (d - 2)) volume a b :=
    fun a b ↦ (continuous_sin.pow _).intervalIntegrable a b
  rw [intervalIntegral.integral_interval_sub_left (hi 0 π) (hi 0 θ)]
  have h := intervalIntegral.integral_comp_sub_left (fun φ ↦ sin φ ^ (d - 2)) π (a := θ) (b := π)
  simp only [sin_pi_sub, sub_self] at h
  exact h.symm

/-- **Reduction to caps** (by Faber–Krahn on the sphere). For `d ≥ 2`
and disjoint nonempty open `Γ₁, Γ₂ ⊆ 𝕊^{d-1}`, there is `θ ∈ (0, π)` with
`ᾱ_d(θ) + ᾱ_d(π - θ) ≤ α_d(Γ₁) + α_d(Γ₂)`. -/
theorem exists_capExponent_add_le_sphExponent_add (hd : 2 ≤ d)
    {Γ₁ Γ₂ : Set (sphere (0 : E d) 1)} (hΓ₁ : IsOpen Γ₁) (hΓ₂ : IsOpen Γ₂)
    (hne₁ : Γ₁.Nonempty) (hne₂ : Γ₂.Nonempty) (hdisj : Disjoint Γ₁ Γ₂) :
    ∃ θ ∈ Ioo 0 π, capExponent d θ + capExponent d (π - θ) ≤ sphExponent Γ₁ + sphExponent Γ₂ := by
  set σ := (volume : Measure (E d)).toSphere
  obtain ⟨N, hN⟩ : ∃ N : E d, ‖N‖ = 1 := ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp⟩
  obtain ⟨θ₁, hθ₁, hσ₁⟩ := exists_toSphere_sphCap_eq hd hN (measure_mono (μ := σ) (subset_univ Γ₁))
  obtain ⟨θ₂, hθ₂, hσ₂⟩ := exists_toSphere_sphCap_eq hd hN (measure_mono (μ := σ) (subset_univ Γ₂))
  have hpos₁ : 0 < σ Γ₁ := toSphere_pos_of_isOpen hΓ₁ hne₁
  have hpos₂ : 0 < σ Γ₂ := toSphere_pos_of_isOpen hΓ₂ hne₂
  have hsum : (σ Γ₁).toReal + (σ Γ₂).toReal ≤ (σ univ).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← measure_union hdisj hΓ₂.measurableSet]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  have hr₂ : 0 < (σ Γ₂).toReal := ENNReal.toReal_pos hpos₂.ne' (measure_ne_top _ _)
  have hθpos : ∀ θ ∈ Icc 0 π, 0 < σ (sphCap N θ) → 0 < θ := fun θ hθ h ↦ by
    rcases hθ.1.eq_or_lt with h0 | h0
    · rw [← h0, sphCap_zero, measure_empty] at h
      exact absurd h (lt_irrefl 0)
    · exact h0
  have hθ₁0 : 0 < θ₁ := hθpos θ₁ hθ₁ (hσ₁ ▸ hpos₁)
  have hθ₂0 : 0 < θ₂ := hθpos θ₂ hθ₂ (hσ₂ ▸ hpos₂)
  -- `θ₂ ≤ π - θ₁`
  have hθ₁₂ : θ₂ ≤ π - θ₁ := by
    by_contra h
    push Not at h
    have h' := (toReal_toSphere_sphCap_lt_iff hd hN
      ⟨sub_nonneg.2 hθ₁.2, sub_le_self _ hθ₁.1⟩ hθ₂).2 h
    rw [← ENNReal.toReal_lt_toReal (measure_ne_top _ _) (measure_ne_top _ _),
      toReal_toSphere_sphCap_pi_sub hd hN hθ₁, hσ₁, hσ₂] at h'
    linarith
  have hθ₁π : θ₁ < π := by linarith
  have hθ₂π : θ₂ < π := by linarith
  -- Faber–Krahn and monotonicity
  have h₁ : capExponent d θ₁ ≤ sphExponent Γ₁ :=
    charExponent_mono (capEigenvalue_le_sphEigenvalue hd hN hΓ₁ hne₁ hθ₁π hσ₁)
  have h₂ : capExponent d θ₂ ≤ sphExponent Γ₂ :=
    charExponent_mono (capEigenvalue_le_sphEigenvalue hd hN hΓ₂ hne₂ hθ₂π hσ₂)
  have h₃ : capExponent d (π - θ₁) ≤ capExponent d θ₂ :=
    capExponent_le_of_le hθ₂0 hθ₁₂ (sub_le_self _ hθ₁0.le)
  exact ⟨θ₁, ⟨hθ₁0, hθ₁π⟩, by linarith⟩

/-- **Friedland–Hayman from the cap inequality.** If `d ≥ 2` and
`ᾱ_d(θ) + ᾱ_d(π - θ) ≥ 2` for every `θ ∈ (0, π)`, then `FriedlandHaymanIn d`. -/
theorem friedlandHaymanIn_of_capInequality (hd : 2 ≤ d)
    (hCI : ∀ θ ∈ Ioo 0 π, 2 ≤ capExponent d θ + capExponent d (π - θ)) :
    FriedlandHaymanIn d := by
  intro Γ₁ Γ₂ hΓ₁ hΓ₂ hne₁ hne₂ hdisj
  obtain ⟨θ, hθ, hle⟩ := exists_capExponent_add_le_sphExponent_add hd hΓ₁ hΓ₂ hne₁ hne₂ hdisj
  exact (hCI θ hθ).trans hle

/-- **Friedland–Hayman in dimension two.** -/
theorem friedlandHaymanIn_two : FriedlandHaymanIn 2 :=
  friedlandHaymanIn_of_capInequality le_rfl capInequality_two

/-- **Friedland–Hayman in dimension four.** -/
theorem friedlandHaymanIn_four : FriedlandHaymanIn 4 :=
  friedlandHaymanIn_of_capInequality (by norm_num) capInequality_four

end EllipticBernoulli

end
