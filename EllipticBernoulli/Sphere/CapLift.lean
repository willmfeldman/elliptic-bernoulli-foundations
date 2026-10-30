/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.TwoPhase
public import EllipticBernoulli.Sphere.Lift
public import EllipticBernoulli.Sphere.Colatitude
import EllipticBernoulli.Sphere.FriedlandHayman
import EllipticBernoulli.Sphere.CapODE

/-!
# Dimension monotonicity of the cap inequality; Friedland–Hayman for `d = 3`

Lifting the two complementary caps `C(θ)` and
`C_{-N}(π - θ)` of `𝕊^{n-1}` to `𝕊ⁿ` (`Lift.lean`) gives disjoint open sets whose exponents are at
most `ᾱ_n(θ)` and `ᾱ_n(π - θ)`. So the Friedland–Hayman inequality in dimension `n + 1` implies the
cap inequality in dimension `n` (`capInequality_of_friedlandHaymanIn_succ`), and, with the
reduction to caps (`FriedlandHayman.lean`), the Friedland–Hayman inequality in dimension `n`
(`friedlandHaymanIn_of_succ`).

The Friedland–Hayman inequality in dimension `n + 1` is applied directly to the lifted sets; by
`friedlandHaymanIn_of_capInequality` this is equivalent to an argument by contradiction with
Faber–Krahn and the cap inequality in dimension `n + 1`. Combined with the cap inequality in
dimension four (`capInequality_four`), this gives the cap inequality and the Friedland–Hayman
inequality in dimension three.

## Main results

* `charExponent_sphEigenvalue_liftSet_sphCap_le`: `α_{n+1}(C(θ)↑) ≤ ᾱ_n(θ)`.
* `capInequality_of_friedlandHaymanIn_succ`, `friedlandHaymanIn_of_succ`.
* `capInequality_three`, `friedlandHaymanIn_three`.

## References

* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and
  the growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
-/

open Set Filter Topology MeasureTheory Metric Real InnerProductGeometry

public section

namespace EllipticBernoulli

variable {n : ℕ}

theorem continuous_charExponent (d : ℕ) : Continuous (charExponent d) := by
  unfold charExponent
  fun_prop

/-- The cap of colatitude `θ < π` is not the whole sphere: it misses `-N`. -/
theorem sphCap_ne_univ {N : E n} (hN : ‖N‖ = 1) {θ : ℝ} (hθ : θ < π) : sphCap N θ ≠ univ := by
  intro h
  have hN0 : N ≠ 0 := by rw [← norm_ne_zero_iff, hN]; exact one_ne_zero
  have hmem : -N ∈ sphere (0 : E n) 1 := by rw [mem_sphere_zero_iff_norm, norm_neg, hN]
  have : (⟨-N, hmem⟩ : sphere (0 : E n) 1) ∈ sphCap N θ := h ▸ mem_univ _
  simp only [sphCap, mem_ofPred_eq, colatitude, angle_neg_self_of_nonzero hN0] at this
  exact lt_irrefl _ (this.trans hθ)

theorem isOpen_sphCap {N : E n} (hN : ‖N‖ = 1) (θ : ℝ) : IsOpen (sphCap N θ) :=
  isOpen_lt (continuous_colatitude hN) continuous_const

theorem sphCap_nonempty {N : E n} (hN : ‖N‖ = 1) {θ : ℝ} (hθ : 0 < θ) :
    (sphCap N θ).Nonempty := by
  have hN0 : N ≠ 0 := by rw [← norm_ne_zero_iff, hN]; exact one_ne_zero
  refine ⟨⟨N, by rw [mem_sphere_zero_iff_norm, hN]⟩, ?_⟩
  simp only [sphCap, mem_ofPred_eq, colatitude, angle_self hN0]
  exact hθ

/-- The caps `C_N(θ)` and `C_{-N}(π - θ)` are disjoint. -/
theorem disjoint_sphCap_neg (N : E n) (θ : ℝ) : Disjoint (sphCap N θ) (sphCap (-N) (π - θ)) := by
  rw [Set.disjoint_left]
  intro ω h₁ h₂
  simp only [sphCap, mem_ofPred_eq, colatitude, angle_neg_right] at h₁ h₂
  linarith

/-- **Lifted caps.** For `n ≥ 2`, a unit vector `P` and
`θ ∈ (0, π)`, `α_{n+1}(C_P(θ)↑) ≤ ᾱ_n(θ)`. -/
theorem charExponent_sphEigenvalue_liftSet_sphCap_le (hn : 2 ≤ n) {P : E n} (hP : ‖P‖ = 1)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < π) :
    charExponent (n + 1) (sphEigenvalue (liftSet (sphCap P θ))) ≤ capExponent n θ := by
  set S := capRayleigh n θ '' {F | IsCapAdmissible θ F}
  have hne : S.Nonempty := nonempty_capRayleigh hθ
  have hbdd : BddBelow S := bddBelow_capRayleigh hθ.le hθπ.le
  rw [capExponent, capEigenvalue, Monotone.map_csInf_of_continuousAt
    (continuous_charExponent n).continuousAt charExponent_mono hne hbdd]
  refine le_csInf (hne.image _) ?_
  rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
  obtain ⟨f, hf, hfR⟩ := exists_isSphAdmissible_sphRayleigh_eq (by omega) hP hθ hθπ.le hF
  have hR : 0 < sphRayleigh f := hf.sphRayleigh_pos (by omega) (sphCap_ne_univ hP hθπ)
  rw [← hfR]
  exact charExponent_sphEigenvalue_liftSet_le hn hf hR

/-- **Dimension monotonicity of the cap inequality** (from dimension `n + 1` to dimension `n`).
For `n ≥ 2`, the Friedland–Hayman inequality in dimension `n + 1` implies
`ᾱ_n(θ) + ᾱ_n(π - θ) ≥ 2` for every `θ ∈ (0, π)`. -/
theorem capInequality_of_friedlandHaymanIn_succ (hn : 2 ≤ n) (hFH : FriedlandHaymanIn (n + 1)) :
    ∀ θ ∈ Ioo 0 π, 2 ≤ capExponent n θ + capExponent n (π - θ) := by
  rintro θ ⟨hθ, hθπ⟩
  obtain ⟨N, hN⟩ : ∃ N : E n, ‖N‖ = 1 := ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp⟩
  have hN' : ‖-N‖ = 1 := by rw [norm_neg, hN]
  have hθ' : 0 < π - θ := sub_pos.2 hθπ
  have hθπ' : π - θ < π := sub_lt_self π hθ
  have h := hFH (liftSet (sphCap N θ)) (liftSet (sphCap (-N) (π - θ)))
    (isOpen_liftSet (isOpen_sphCap hN θ)) (isOpen_liftSet (isOpen_sphCap hN' (π - θ)))
    (liftSet_nonempty (sphCap_nonempty hN hθ)) (liftSet_nonempty (sphCap_nonempty hN' hθ'))
    (liftSet_disjoint (disjoint_sphCap_neg N θ))
  have h₁ := charExponent_sphEigenvalue_liftSet_sphCap_le hn hN hθ hθπ
  have h₂ := charExponent_sphEigenvalue_liftSet_sphCap_le hn hN' hθ' hθπ'
  exact h.trans (add_le_add h₁ h₂)

/-- For `n ≥ 2`, the Friedland–Hayman inequality in dimension `n + 1` implies it in dimension
`n`. -/
theorem friedlandHaymanIn_of_succ (hn : 2 ≤ n) (hFH : FriedlandHaymanIn (n + 1)) :
    FriedlandHaymanIn n :=
  friedlandHaymanIn_of_capInequality hn (capInequality_of_friedlandHaymanIn_succ hn hFH)

/-- **The cap inequality in dimension three.** -/
theorem capInequality_three : ∀ θ ∈ Ioo 0 π, 2 ≤ capExponent 3 θ + capExponent 3 (π - θ) :=
  capInequality_of_friedlandHaymanIn_succ (n := 3) (by norm_num) friedlandHaymanIn_four

/-- **Friedland–Hayman in dimension three.** -/
theorem friedlandHaymanIn_three : FriedlandHaymanIn 3 :=
  friedlandHaymanIn_of_capInequality (by norm_num) capInequality_three

end EllipticBernoulli

end
