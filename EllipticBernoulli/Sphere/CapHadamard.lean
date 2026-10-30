/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.CapEigenfunction
import EllipticBernoulli.Sphere.CapODE
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The Wronskian identity and the Hadamard formula for `Λ_d`

* `capShoot_wronskian`: for any `λ, μ`, the Wronskian identity (in
  finite-difference form)
  `y_λ (sin^m y_μ') - (sin^m y_λ') y_μ = (λ - μ) ∫_0^x sin^m y_λ y_μ` on `[0, π)`.
* `exists_slope_capEigenvalue_eq`: for `0 < a < b < π`, with `y_a = y(·, Λ_d(a))`,
  `y_b = y(·, Λ_d(b))`, there is `ξ ∈ (a, b)` with
  `(Λ_d(b) - Λ_d(a)) / (b - a) = -(sin^m y_a')(a) y_b'(ξ) / ∫_0^a sin^m y_a y_b`.
* `hasDerivAt_capEigenvalue`: **Hadamard formula.**
  `Λ_d'(θ) = -(sin^m y')(θ) y'(θ) / ∫_0^θ sin^m y²`, with `y = y(·, Λ_d(θ))`.

No implicit function theorem for `(θ, λ) ↦ y(θ, λ)` is used, and hence no derivative `∂_λ y`.
Instead, the Wronskian identity at two eigenvalues, the mean value theorem, the continuity of `Λ_d`
(`continuousOn_capEigenvalue`) and the joint continuity of `y'` in `(x, λ)` give the derivative
directly as a limit of difference quotients.
-/

open Set Filter Topology MeasureTheory Real

public section

namespace EllipticBernoulli

variable {m d : ℕ}

/-- **Wronskian identity.** For `λ, μ ∈ ℝ` and `x ∈ [0, π)`,
`y_λ(x) H_μ(x) - H_λ(x) y_μ(x) = (λ - μ) ∫_0^x sin^m y_λ y_μ`, with `H = sin^m y'` the flux. -/
theorem capShoot_wronskian (m : ℕ) (lam mu : ℝ) {x : ℝ} (hx : x ∈ Ico 0 π) :
    capShoot m lam x * capShootFlux m mu x - capShootFlux m lam x * capShoot m mu x =
      (lam - mu) * ∫ t in 0..x, sin t ^ m * (capShoot m lam t * capShoot m mu t) := by
  have hsub : Icc 0 x ⊆ Ico 0 π := fun t ht ↦ ⟨ht.1, ht.2.trans_lt hx.2⟩
  have hsol₁ := isCapSolution_capShoot m lam hx.2
  have hsol₂ := isCapSolution_capShoot m mu hx.2
  have hcont : ContinuousOn (fun t ↦ sin t ^ m * (capShoot m lam t * capShoot m mu t))
      (Icc 0 x) :=
    (continuous_sin.pow m).continuousOn.mul (hsol₁.continuousOn.mul hsol₂.continuousOn)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
    ((hsol₁.continuousOn.mul hsol₂.continuousOn_flux).sub
      (hsol₁.continuousOn_flux.mul hsol₂.continuousOn))
    (f' := fun t ↦ (lam - mu) * (sin t ^ m * (capShoot m lam t * capShoot m mu t)))
    (fun t ht ↦ by
      have h1 := ((hsol₁.hasDerivAt t ht).mul (hsol₂.hasDerivAt_flux t ht)).sub
        ((hsol₁.hasDerivAt_flux t ht).mul (hsol₂.hasDerivAt t ht))
      convert h1 using 1
      have hs : sin t ^ m ≠ 0 :=
        (pow_pos (sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans hx.2)) m).ne'
      field_simp
      ring)
    ((hcont.const_smul (lam - mu)).intervalIntegrable_of_Icc hx.1)
  rw [intervalIntegral.integral_const_mul] at h
  simp only [Pi.sub_apply, Pi.mul_apply, capShoot_zero_right, capShootFlux_zero_right, mul_zero,
    zero_mul, sub_zero] at h
  exact h.symm

/-- The integral `∫_0^a sin^m y_a y_b` is positive when `y_a` and `y_b` are positive on `[0, a)`. -/
theorem integral_sin_pow_mul_capShoot_pos {a lam mu : ℝ} (ha : 0 < a) (haπ : a < π)
    (h₁ : ∀ x ∈ Ico 0 a, 0 < capShoot m lam x) (h₂ : ∀ x ∈ Ico 0 a, 0 < capShoot m mu x) :
    0 < ∫ t in 0..a, sin t ^ m * (capShoot m lam t * capShoot m mu t) := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun x hx ↦ ?_) ha
  · exact ((continuous_sin.pow m).continuousOn.mul
      ((isCapSolution_capShoot m lam haπ).continuousOn.mul
        (isCapSolution_capShoot m mu haπ).continuousOn)).intervalIntegrable_of_Icc ha.le
  · exact mul_pos (pow_pos (sin_pos_of_pos_of_lt_pi hx.1 (hx.2.trans haπ)) m)
      (mul_pos (h₁ x ⟨hx.1.le, hx.2⟩) (h₂ x ⟨hx.1.le, hx.2⟩))

/-- **Two-point identity.** For `0 < a < b < π` there is `ξ ∈ (a, b)` with
`(Λ_d(b) - Λ_d(a)) / (b - a) = -(H_a(a) y_b'(ξ)) / ∫_0^a sin^m y_a y_b`, where
`y_a = y(·, Λ_d(a))`, `y_b = y(·, Λ_d(b))` and `H_a = sin^m y_a'`. -/
theorem exists_slope_capEigenvalue_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbπ : b < π) :
    ∃ ξ ∈ Ioo a b, (capEigenvalue d b - capEigenvalue d a) / (b - a) =
      -(capShootFlux (d - 2) (capEigenvalue d a) a *
        capShootDeriv (d - 2) (capEigenvalue d b) ξ) /
        ∫ t in 0..a, sin t ^ (d - 2) *
          (capShoot (d - 2) (capEigenvalue d a) t * capShoot (d - 2) (capEigenvalue d b) t) := by
  set m := d - 2
  have haπ : a < π := hab.trans hbπ
  obtain ⟨-, hpa, hya⟩ := capShoot_capEigenvalue (d := d) ha haπ
  obtain ⟨-, hpb, hyb⟩ := capShoot_capEigenvalue (d := d) (ha.trans hab) hbπ
  set la := capEigenvalue d a
  set lb := capEigenvalue d b
  have hW := capShoot_wronskian m la lb ⟨ha.le, haπ⟩
  rw [hya, zero_mul, zero_sub] at hW
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (capShoot m lb) (capShootDeriv m lb) hab
    ((isCapSolution_capShoot m lb hbπ).continuousOn.mono (Icc_subset_Icc ha.le le_rfl))
    fun x hx ↦ hasDerivAt_capShoot m lb ⟨ha.trans hx.1, hx.2.trans hbπ⟩
  rw [hyb, zero_sub] at hslope
  have hD := integral_sin_pow_mul_capShoot_pos (m := m) ha haπ hpa
    fun x hx ↦ hpb x ⟨hx.1, hx.2.trans hab⟩
  refine ⟨ξ, hξ, ?_⟩
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  generalize (∫ t in 0..a, sin t ^ m * (capShoot m la t * capShoot m lb t)) = D at hW hD ⊢
  rw [eq_div_iff hD.ne', hslope]
  field_simp
  linear_combination hW

/-- **Hadamard formula.** For `θ ∈ (0, π)`, with `y = y(·, Λ_d(θ))`
and `H = sin^m y'`, `Λ_d'(θ) = -H(θ) y'(θ) / ∫_0^θ sin^m y²`. -/
theorem hasDerivAt_capEigenvalue {θ : ℝ} (hθ : θ ∈ Ioo 0 π) :
    HasDerivAt (capEigenvalue d)
      (-(capShootFlux (d - 2) (capEigenvalue d θ) θ *
          capShootDeriv (d - 2) (capEigenvalue d θ) θ) /
        ∫ t in 0..θ, sin t ^ (d - 2) *
          (capShoot (d - 2) (capEigenvalue d θ) t * capShoot (d - 2) (capEigenvalue d θ) t))
      θ := by
  set m := d - 2
  set Λ := capEigenvalue d
  set G : ℝ × ℝ × ℝ → ℝ := fun q ↦
    ∫ t in 0..q.1, sin t ^ m * (capShoot m q.2.1 t * capShoot m q.2.2 t)
  have hG : ContinuousAt G (θ, Λ θ, Λ θ) := continuousAt_integral_capShoot_mul m hθ _ _
  have hG0 : G (θ, Λ θ, Λ θ) ≠ 0 := by
    have hp := (capShoot_capEigenvalue (d := d) hθ.1 hθ.2).2.1
    exact (integral_sin_pow_mul_capShoot_pos (m := m) hθ.1 hθ.2 hp hp).ne'
  have hΛ : Tendsto Λ (𝓝 θ) (𝓝 (Λ θ)) :=
    (continuousOn_capEigenvalue d).continuousAt (Ioo_mem_nhds hθ.1 hθ.2)
  have hD : ContinuousAt (fun p : ℝ × ℝ ↦ capShootDeriv m p.2 p.1) (θ, Λ θ) :=
    (continuousOn_capShootDeriv m).continuousAt
      (prod_mem_nhds (Ioo_mem_nhds hθ.1 hθ.2) univ_mem)
  have hH : ContinuousAt (fun p : ℝ × ℝ ↦ capShootFlux m p.2 p.1) (θ, Λ θ) :=
    (continuousOn_capShootFlux m).continuousAt
      (prod_mem_nhds (Ico_mem_nhds hθ.1 hθ.2) univ_mem)
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · -- from the left: `a = θ' < b = θ`
    have hex : ∀ θ', ∃ ξ, θ' ∈ Ioo 0 θ → ξ ∈ Ioo θ' θ ∧
        slope Λ θ θ' = -(capShootFlux m (Λ θ') θ' * capShootDeriv m (Λ θ) ξ) /
          G (θ', Λ θ', Λ θ) := by
      intro θ'
      by_cases h : θ' ∈ Ioo 0 θ
      · obtain ⟨ξ, hξ, hs⟩ := exists_slope_capEigenvalue_eq (d := d) h.1 h.2 hθ.2
        refine ⟨ξ, fun _ ↦ ⟨hξ, ?_⟩⟩
        rw [slope_def_field, ← neg_div_neg_eq, neg_sub, neg_sub]
        exact hs
      · exact ⟨0, fun h' ↦ absurd h' h⟩
    choose ξ hξ using hex
    have hev : ∀ᶠ θ' in 𝓝[<] θ, θ' ∈ Ioo 0 θ := Ioo_mem_nhdsLT hθ.1
    have hξt : Tendsto ξ (𝓝[<] θ) (𝓝 θ) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_nhdsWithin_of_tendsto_nhds
        tendsto_id) tendsto_const_nhds ?_ ?_
      · filter_upwards [hev] with θ' h using (hξ θ' h).1.1.le
      · filter_upwards [hev] with θ' h using (hξ θ' h).1.2.le
    have hΛ' := hΛ.mono_left (nhdsWithin_le_nhds (s := Iio θ))
    have hid : Tendsto (fun θ' : ℝ ↦ θ') (𝓝[<] θ) (𝓝 θ) := tendsto_nhdsWithin_of_tendsto_nhds
      tendsto_id
    have h1 : Tendsto (fun θ' ↦ capShootFlux m (Λ θ') θ') (𝓝[<] θ)
        (𝓝 (capShootFlux m (Λ θ) θ)) := hH.tendsto.comp (hid.prodMk_nhds hΛ')
    have h2 : Tendsto (fun θ' ↦ capShootDeriv m (Λ θ) (ξ θ')) (𝓝[<] θ)
        (𝓝 (capShootDeriv m (Λ θ) θ)) :=
      hD.tendsto.comp (hξt.prodMk_nhds tendsto_const_nhds)
    have h3 : Tendsto (fun θ' ↦ G (θ', Λ θ', Λ θ)) (𝓝[<] θ) (𝓝 (G (θ, Λ θ, Λ θ))) :=
      hG.tendsto.comp (hid.prodMk_nhds (hΛ'.prodMk_nhds tendsto_const_nhds))
    refine ((h1.mul h2).neg.div h3 hG0).congr' ?_
    filter_upwards [hev] with θ' h
    exact ((hξ θ' h).2).symm
  · -- from the right: `a = θ < b = θ'`
    have hex : ∀ θ', ∃ ξ, θ' ∈ Ioo θ π → ξ ∈ Ioo θ θ' ∧
        slope Λ θ θ' = -(capShootFlux m (Λ θ) θ * capShootDeriv m (Λ θ') ξ) /
          G (θ, Λ θ, Λ θ') := by
      intro θ'
      by_cases h : θ' ∈ Ioo θ π
      · obtain ⟨ξ, hξ, hs⟩ := exists_slope_capEigenvalue_eq (d := d) hθ.1 h.1 h.2
        refine ⟨ξ, fun _ ↦ ⟨hξ, ?_⟩⟩
        rw [slope_def_field]
        exact hs
      · exact ⟨0, fun h' ↦ absurd h' h⟩
    choose ξ hξ using hex
    have hev : ∀ᶠ θ' in 𝓝[>] θ, θ' ∈ Ioo θ π := Ioo_mem_nhdsGT hθ.2
    have hξt : Tendsto ξ (𝓝[>] θ) (𝓝 θ) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id) ?_ ?_
      · filter_upwards [hev] with θ' h using (hξ θ' h).1.1.le
      · filter_upwards [hev] with θ' h using (hξ θ' h).1.2.le
    have hΛ' := hΛ.mono_left (nhdsWithin_le_nhds (s := Ioi θ))
    have h2 : Tendsto (fun θ' ↦ capShootDeriv m (Λ θ') (ξ θ')) (𝓝[>] θ)
        (𝓝 (capShootDeriv m (Λ θ) θ)) :=
      hD.tendsto.comp (hξt.prodMk_nhds hΛ')
    have h3 : Tendsto (fun θ' ↦ G (θ, Λ θ, Λ θ')) (𝓝[>] θ) (𝓝 (G (θ, Λ θ, Λ θ))) :=
      hG.tendsto.comp (tendsto_const_nhds.prodMk_nhds
        (tendsto_const_nhds.prodMk_nhds hΛ'))
    refine (((tendsto_const_nhds (x := capShootFlux m (Λ θ) θ)).mul h2).neg.div h3
      hG0).congr' ?_
    filter_upwards [hev] with θ' h
    exact ((hξ θ' h).2).symm

end EllipticBernoulli

end
