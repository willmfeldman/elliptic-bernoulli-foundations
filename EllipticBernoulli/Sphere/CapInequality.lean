/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.TwoPhase
import EllipticBernoulli.TwoPhase.Defs
import EllipticBernoulli.Sphere.CapLift
import EllipticBernoulli.Sphere.CapODE
import EllipticBernoulli.Sphere.FriedlandHayman
import EllipticBernoulli.Sphere.CapKoch

/-!
# The cap inequality in every dimension, from Koch convexity

The cap inequality `ᾱ_n(θ) + ᾱ_n(π - θ) ≥ 2` in every dimension `n ≥ 2`, and with it the
Friedland–Hayman inequality. The cap inequality in a high dimension `N` comes from Koch convexity
and an elementary lower bound for the characteristic exponent `κ_N`; dimension monotonicity
(lifting) brings it down to dimension `n`. This is the route of Salato (arXiv:2506.13473), §5,
Steps 3–4, with Step 3 replaced by the lifting argument of `Sphere/Lift.lean` and
`Sphere/CapLift.lean`: Salato's Step 3 compares the exponents of caps of a fixed colatitude in
dimensions `n` and `n + 1`; here the lifted set is compared with the caps of dimension `n`, and
Faber–Krahn in dimension `n + 1` gives the monotonicity of `min_θ (ᾱ_n(θ) + ᾱ_n(π - θ))` in `n`,
which is what Step 4 uses.

* `exists_capExponent_add_le_of_le`: a value of `ᾱ_n(θ) + ᾱ_n(π - θ)` is attained or undercut in
  every dimension `N ≥ n` (lifting, iterated).
* `le_charExponent`: `κ_N(λ) ≥ λ/m - λ²/m³` for `m = N - 2 > 0` and `0 ≤ λ ≤ 2m²`, from
  `√(1 + 4x) ≥ 1 + 2x - 2x²` on `[0, 2]`.
* `capInequality_of_forall_exists`: if for infinitely many `N` the radial cap eigenvalues satisfy
  `Λ_N(θ) + Λ_N(π - θ) ≥ 2 (N - 1)` on `(0, π)`, then the cap inequality
  `ᾱ_n(θ) + ᾱ_n(π - θ) ≥ 2` holds in every dimension `n ≥ 2`.
* `friedlandHayman_of_forall_exists`: the same hypothesis gives `FriedlandHaymanStatement`.
* `capInequality`: **the cap inequality** in every dimension `n ≥ 2`.
* `friedlandHayman`: **the Friedland–Hayman inequality** in every dimension `d ≥ 2`
  (`FriedlandHaymanStatement`).

The hypothesis on `Λ_N` is Koch's convexity consequence, proved for every
`N ≥ 5` in `CapKoch.lean` (`two_mul_sub_one_le_capEigenvalue_add`).

## References

* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and
  the growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473 (v2).
* H. Koch, *Convexity and concavity of the ground state energy*, New York J. Math. 21 (2015),
  1003–1005; arXiv:1502.07290.
-/

open Set Real

public section

namespace EllipticBernoulli

/-! ### Iterated lifting -/

/-- **Dimension monotonicity of the cap inequality, iterated.** For
`2 ≤ n ≤ N` and `θ ∈ (0, π)` there is `θ' ∈ (0, π)` with
`ᾱ_N(θ') + ᾱ_N(π - θ') ≤ ᾱ_n(θ) + ᾱ_n(π - θ)`. -/
theorem exists_capExponent_add_le_of_le {n N : ℕ} (hn : 2 ≤ n) (hnN : n ≤ N) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 π) :
    ∃ θ' ∈ Ioo 0 π, capExponent N θ' + capExponent N (π - θ') ≤
      capExponent n θ + capExponent n (π - θ) := by
  induction N, hnN using Nat.le_induction with
  | base => exact ⟨θ, hθ, le_rfl⟩
  | succ N hnN ih =>
    obtain ⟨θ', ⟨hθ', hθ'π⟩, hle⟩ := ih
    have hN : 2 ≤ N := hn.trans hnN
    obtain ⟨P, hP⟩ : ∃ P : E N, ‖P‖ = 1 := ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp⟩
    have hP' : ‖-P‖ = 1 := by rw [norm_neg, hP]
    have h0 : 0 < π - θ' := sub_pos.2 hθ'π
    have h1 : π - θ' < π := sub_lt_self π hθ'
    obtain ⟨θ'', hθ'', hle'⟩ := exists_capExponent_add_le_sphExponent_add (d := N + 1)
      (by omega) (isOpen_liftSet (isOpen_sphCap hP θ'))
      (isOpen_liftSet (isOpen_sphCap hP' (π - θ')))
      (liftSet_nonempty (sphCap_nonempty hP hθ')) (liftSet_nonempty (sphCap_nonempty hP' h0))
      (liftSet_disjoint (disjoint_sphCap_neg P θ'))
    have h₁ := charExponent_sphEigenvalue_liftSet_sphCap_le hN hP hθ' hθ'π
    have h₂ := charExponent_sphEigenvalue_liftSet_sphCap_le hN hP' h0 h1
    refine ⟨θ'', hθ'', hle'.trans ?_⟩
    exact (add_le_add h₁ h₂).trans hle

/-! ### Elementary bounds for `κ_N` -/

/-- `√(1 + 4x) ≥ 1 + 2x - 2x²` for `0 ≤ x ≤ 2`. -/
theorem one_add_two_mul_sub_le_sqrt {x : ℝ} (hx : 0 ≤ x) (hx2 : x ≤ 2) :
    1 + 2 * x - 2 * x ^ 2 ≤ √(1 + 4 * x) := by
  rcases le_or_gt (1 + 2 * x - 2 * x ^ 2) 0 with h | h
  · exact h.trans (sqrt_nonneg _)
  · refine Real.le_sqrt_of_sq_le ?_
    nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hx 3) (sub_nonneg.2 hx2)) zero_le_four]

/-- **Lower bound for `κ_N`.** With `m = N - 2 > 0`
and `0 ≤ λ ≤ 2m²`, `κ_N(λ) ≥ λ/m - λ²/m³`. -/
theorem le_charExponent {N : ℕ} {lam : ℝ} (hm : 0 < (N : ℝ) - 2) (hlam : 0 ≤ lam)
    (hlam2 : lam ≤ 2 * ((N : ℝ) - 2) ^ 2) :
    lam / ((N : ℝ) - 2) - lam ^ 2 / ((N : ℝ) - 2) ^ 3 ≤ charExponent N lam := by
  set m : ℝ := (N : ℝ) - 2 with hm_def
  set x : ℝ := lam / m ^ 2 with hx_def
  have hm2 : 0 < m ^ 2 := by positivity
  have hlamx : lam = x * m ^ 2 := by rw [hx_def]; field_simp
  have hx : 0 ≤ x := div_nonneg hlam hm2.le
  have hx2 : x ≤ 2 := by rw [hx_def, div_le_iff₀ hm2]; linarith
  have hsq : √(m ^ 2 + 4 * lam) = m * √(1 + 4 * x) := by
    rw [hlamx, show m ^ 2 + 4 * (x * m ^ 2) = m ^ 2 * (1 + 4 * x) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hm.le]
  have h := one_add_two_mul_sub_le_sqrt hx hx2
  unfold charExponent
  rw [← hm_def, hsq]
  have e : lam / m - lam ^ 2 / m ^ 3 = m * (x - x ^ 2) := by
    rw [hlamx]; field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left h hm.le]

/-! ### The closure -/

/-- **The contradiction step.** Let `N ≥ 4`,
`m = N - 2`, `θ ∈ (0, π)` with `Λ_N(θ) + Λ_N(π - θ) ≥ 2 (N - 1)`. If
`ᾱ_N(θ) + ᾱ_N(π - θ) ≤ 2 - δ` with `δ > 0`, then `δ m ≤ 30`. -/
theorem mul_le_thirty_of_capExponent_add_le {N : ℕ} (hN : 4 ≤ N) {θ δ : ℝ} (hθ : θ ∈ Ioo 0 π)
    (hδ : 0 < δ) (hK : 2 * ((N : ℝ) - 1) ≤ capEigenvalue N θ + capEigenvalue N (π - θ))
    (hle : capExponent N θ + capExponent N (π - θ) ≤ 2 - δ) : δ * ((N : ℝ) - 2) ≤ 30 := by
  set m : ℝ := (N : ℝ) - 2 with hm_def
  have hN' : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hm : 2 ≤ m := by rw [hm_def]; linarith
  have hm0 : 0 < m := by linarith
  set l₁ := capEigenvalue N θ
  set l₂ := capEigenvalue N (π - θ)
  have hl₁ : 0 ≤ l₁ := capEigenvalue_nonneg hθ.1.le hθ.2.le
  have hl₂ : 0 ≤ l₂ := capEigenvalue_nonneg (sub_nonneg.2 hθ.2.le) (sub_le_self π hθ.1.le)
  have ha₁ := charExponent_nonneg (d := N) hl₁
  have ha₂ := charExponent_nonneg (d := N) hl₂
  have hs₁ := charExponent_sq_add (d := N) hl₁
  have hs₂ := charExponent_sq_add (d := N) hl₂
  rw [← hm_def] at hs₁ hs₂
  have hc₁ : capExponent N θ = charExponent N l₁ := rfl
  have hc₂ : capExponent N (π - θ) = charExponent N l₂ := rfl
  rw [hc₁, hc₂] at hle
  set a₁ := charExponent N l₁
  set a₂ := charExponent N l₂
  -- (i) `λᵢ < 2 (m + 2) ≤ 2 m²`
  have ha₁2 : a₁ ≤ 2 := by linarith
  have ha₂2 : a₂ ≤ 2 := by linarith
  have hb₁ : l₁ ≤ 2 * (m + 2) := by rw [← hs₁]; nlinarith
  have hb₂ : l₂ ≤ 2 * (m + 2) := by rw [← hs₂]; nlinarith
  have hmm : 2 * (m + 2) ≤ 2 * m ^ 2 := by nlinarith
  -- (ii)
  have hk₁ := le_charExponent (N := N) hm0 hl₁ (hb₁.trans hmm)
  have hk₂ := le_charExponent (N := N) hm0 hl₂ (hb₂.trans hmm)
  rw [← hm_def] at hk₁ hk₂
  -- (iii)
  have hsum : 2 * (m + 1) ≤ l₁ + l₂ := by
    have : (N : ℝ) - 1 = m + 1 := by rw [hm_def]; ring
    rw [this] at hK; exact hK
  have hq₁ : l₁ ^ 2 ≤ 4 * (m + 2) ^ 2 := by nlinarith
  have hq₂ : l₂ ^ 2 ≤ 4 * (m + 2) ^ 2 := by nlinarith
  have hm3 : 0 < m ^ 3 := by positivity
  have key : 2 - δ ≥ 2 * (m + 1) / m - 8 * (m + 2) ^ 2 / m ^ 3 := by
    have e₁ : l₁ / m + l₂ / m = (l₁ + l₂) / m := by ring
    have e₂ : l₁ ^ 2 / m ^ 3 + l₂ ^ 2 / m ^ 3 = (l₁ ^ 2 + l₂ ^ 2) / m ^ 3 := by ring
    have h₁ : 2 * (m + 1) / m ≤ (l₁ + l₂) / m := div_le_div_of_nonneg_right hsum hm0.le
    have h₂ : (l₁ ^ 2 + l₂ ^ 2) / m ^ 3 ≤ 8 * (m + 2) ^ 2 / m ^ 3 :=
      div_le_div_of_nonneg_right (by linarith) hm3.le
    linarith
  have hsq : (m + 2) ^ 2 ≤ 4 * m ^ 2 := by nlinarith
  have key2 : 2 * (m + 1) / m - 8 * (m + 2) ^ 2 / m ^ 3 ≥ 2 - 30 / m := by
    have e : 2 * (m + 1) / m = 2 + 2 / m := by field_simp
    have h : 8 * (m + 2) ^ 2 / m ^ 3 ≤ 32 / m := by
      rw [div_le_div_iff₀ hm3 hm0]
      nlinarith
    rw [e]
    have : 2 / m - 32 / m = -(30 / m) := by ring
    linarith
  have h30 : δ ≤ 30 / m := by linarith
  rwa [le_div_iff₀ hm0] at h30

/-- **The cap inequality in every dimension, from the Koch bound.** Suppose that for every `M` there
is `N ≥ M` with `Λ_N(θ) + Λ_N(π - θ) ≥ 2 (N - 1)` for all `θ ∈ (0, π)`. Then for every `n ≥ 2` and
`θ ∈ (0, π)`, `ᾱ_n(θ) + ᾱ_n(π - θ) ≥ 2`. -/
theorem capInequality_of_forall_exists
    (hK : ∀ M : ℕ, ∃ N ≥ M, ∀ θ ∈ Ioo 0 π,
      2 * ((N : ℝ) - 1) ≤ capEigenvalue N θ + capEigenvalue N (π - θ))
    {n : ℕ} (hn : 2 ≤ n) : ∀ θ ∈ Ioo 0 π, 2 ≤ capExponent n θ + capExponent n (π - θ) := by
  intro θ hθ
  by_contra hlt
  push Not at hlt
  set δ := 2 - (capExponent n θ + capExponent n (π - θ)) with hδ_def
  have hδ : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨M, hM⟩ := exists_nat_gt (30 / δ)
  obtain ⟨N, hNM, hN⟩ := hK (max (max (M + 2) n) 4)
  have hnN : n ≤ N := (le_max_right _ n).trans ((le_max_left _ 4).trans hNM)
  have h4N : 4 ≤ N := (le_max_right _ 4).trans hNM
  have hMN : ((M + 2 : ℕ) : ℝ) ≤ N := by
    exact_mod_cast (le_max_left _ n).trans ((le_max_left _ 4).trans hNM)
  obtain ⟨θ', hθ', hle⟩ := exists_capExponent_add_le_of_le hn hnN hθ
  have h := mul_le_thirty_of_capExponent_add_le h4N hθ' hδ (hN θ' hθ') (by linarith)
  push_cast at hMN
  have h1 : 30 / δ < (N : ℝ) - 2 := by linarith
  rw [div_lt_iff₀ hδ] at h1
  linarith

/-- **Friedland–Hayman in every dimension, from the Koch bound.** Under the hypothesis of
`capInequality_of_forall_exists`, `FriedlandHaymanStatement` holds. -/
theorem friedlandHayman_of_forall_exists
    (hK : ∀ M : ℕ, ∃ N ≥ M, ∀ θ ∈ Ioo 0 π,
      2 * ((N : ℝ) - 1) ≤ capEigenvalue N θ + capEigenvalue N (π - θ)) :
    FriedlandHaymanStatement := fun _ hd ↦
  friedlandHaymanIn_of_capInequality hd (capInequality_of_forall_exists hK hd)

/-- **The cap inequality.** For every `n ≥ 2` and `θ ∈ (0, π)`,
`ᾱ_n(θ) + ᾱ_n(π - θ) ≥ 2`. -/
theorem capInequality {n : ℕ} (hn : 2 ≤ n) :
    ∀ θ ∈ Ioo 0 π, 2 ≤ capExponent n θ + capExponent n (π - θ) :=
  capInequality_of_forall_exists (fun M ↦ ⟨max M 5, le_max_left _ _, fun _ hθ ↦
    two_mul_sub_one_le_capEigenvalue_add (le_max_right _ _) hθ⟩) hn

/-- **The Friedland–Hayman inequality** (Friedland–Hayman 1976). For every
`d ≥ 2` and disjoint, nonempty, relatively open `Γ₁, Γ₂ ⊆ 𝕊^{d-1}`,
`α_d(Γ₁) + α_d(Γ₂) ≥ 2`. -/
theorem friedlandHayman : FriedlandHaymanStatement := fun _ hd ↦
  friedlandHaymanIn_of_capInequality hd (capInequality hd)

end EllipticBernoulli

end
