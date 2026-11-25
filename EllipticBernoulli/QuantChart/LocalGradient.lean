/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.QuantChart.LocalChart
import EllipticBernoulli.QuantChart.Gradient
import EllipticBernoulli.Flatness.Classical
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Affine
import EllipticBernoulli.Viscosity.Harmonic

/-!
# Flatness and the gradient near free-boundary points of a flat minimizer

Let `u` be a continuous, non-negative local minimizer of `J` in `B_1` with
`|u - (x · e)₊| ≤ ε` on `B_1`, and write `c = c_d` for the non-degeneracy constant.

* `eq_zero_of_flat_of_inner_le`: `u = 0` at every `x ∈ B_{7/8}` with `x · e ≤ -(2/c) ε`.
* `flat_about_freeBoundary`: about a free-boundary point `y` with `‖y‖ ≤ 3/8`, `u` is
  `(4/c + 1) ε`-flat in max form on `B_{1/2}(y)`, in direction `e`.
* `exists_norm_gradient_sub_le_of_flat`: for `ε` small, `‖∇u - e‖ ≤ C ε` on
  `{u > 0} ∩ B_{1/4}(y)` for each such `y` (by rescaling and
  `norm_gradient_sub_le_of_flat_uniform`).
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **The zero side.** An `ε`-flat minimizer vanishes on `{x · e ≤ -(2/c) ε} ∩ B_{7/8}`. -/
theorem eq_zero_of_flat_of_inner_le (hd : 2 ≤ d) {u : E d → ℝ} {e : E d} {ε : ℝ} (hε : 0 < ε)
    (hεc : 2 * ε / ndConst d ≤ 1 / 8) (hc : ContinuousOn u (ball 0 1))
    (hnn : ∀ x ∈ ball (0 : E d) 1, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u) (he : ‖e‖ = 1)
    (hflat : ∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) {x : E d} (hx : ‖x‖ < 7 / 8)
    (hxe : ⟪x, e⟫ ≤ -(2 * ε / ndConst d)) : u x = 0 := by
  have hc0 := ndConst_pos hd
  have hxU : x ∈ ball (0 : E d) 1 := by rw [mem_ball, dist_zero_right]; linarith
  by_contra hne
  have hpos : 0 < u x := lt_of_le_of_ne (hnn x hxU) (Ne.symm hne)
  set σ := 2 * ε / ndConst d with hσ
  have hσ0 : 0 < σ := by positivity
  have hsub : closedBall x σ ⊆ ball (0 : E d) 1 := fun z hz ↦ by
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z x
    linarith
  obtain ⟨z, hz, hcz⟩ := nondegenerate_of_isLocalEnergyMinimizer hd isOpen_ball hc hnn hmin x
    (subset_closure ⟨hxU, hpos⟩) σ hσ0 hsub
  have hcσ : ndConst d * σ = 2 * ε := by rw [hσ]; field_simp
  have hze : ⟪z, e⟫ ≤ 0 := by
    have h2 : ⟪z - x, e⟫ ≤ ‖z - x‖ := by
      have := real_inner_le_norm (z - x) e; rwa [he, mul_one] at this
    rw [inner_sub_left] at h2
    rw [mem_closedBall, dist_eq_norm] at hz
    linarith
  have h1 := (abs_le.1 (hflat z (hsub hz))).2
  rw [max_eq_right hze] at h1
  linarith

/-- **Flatness about a free-boundary point.** -/
theorem flat_about_freeBoundary (hd : 2 ≤ d) {u : E d → ℝ} {e : E d} {ε : ℝ} (hε : 0 < ε)
    (hεc : 2 * ε / ndConst d ≤ 1 / 8) (hc : ContinuousOn u (ball 0 1))
    (hnn : ∀ x ∈ ball (0 : E d) 1, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u) (he : ‖e‖ = 1)
    (hflat : ∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) {y : E d}
    (hy : y ∈ freeBoundary u (ball 0 1)) (hy3 : ‖y‖ ≤ 3 / 8) :
    ∀ z ∈ ball y (1 / 2), max (⟪z - y, e⟫ - (4 / ndConst d + 1) * ε) 0 ≤ u z ∧
      u z ≤ max (⟪z - y, e⟫ + (4 / ndConst d + 1) * ε) 0 := by
  have hc0 := ndConst_pos hd
  have hrc : 2 * ε / ndConst d < 1 / 2 := by linarith
  obtain ⟨-, hye⟩ := abs_inner_le_of_mem_freeBoundary_of_flat hd hε hrc hc hnn hmin he hflat hy
    (by linarith)
  set a := 2 * ε / ndConst d with ha
  have hK : (4 / ndConst d + 1) * ε = 2 * a + ε := by rw [ha]; ring
  intro z hz
  have hzn : ‖z‖ < 7 / 8 := by
    rw [mem_ball, dist_eq_norm] at hz
    have := norm_le_norm_add_norm_sub' z y
    linarith
  have hzU : z ∈ ball (0 : E d) 1 := by rw [mem_ball, dist_zero_right]; linarith
  have hzy : ⟪z - y, e⟫ = ⟪z, e⟫ - ⟪y, e⟫ := inner_sub_left _ _ _
  obtain ⟨hy1, hy2⟩ := abs_le.1 hye
  have h := abs_le.1 (hflat z hzU)
  rw [hK, hzy]
  constructor
  · refine max_le ?_ (hnn z hzU)
    have := le_max_left ⟪z, e⟫ 0
    linarith
  · by_cases hs : ⟪z, e⟫ ≤ -a
    · rw [eq_zero_of_flat_of_inner_le hd hε hεc hc hnn hmin he hflat hzn hs]
      exact le_max_right _ _
    · push Not at hs
      refine le_trans ?_ (le_max_left _ _)
      rcases le_total 0 ⟪z, e⟫ with h0 | h0
      · rw [max_eq_left h0] at h; linarith
      · rw [max_eq_right h0] at h; linarith

/-- **The gradient near free-boundary points.** For `d ≥ 2` there are `ε₂, C > 0` such that,
if `u` is an `ε`-flat minimizer in `B_1` (`0 < ε ≤ ε₂`) and `y` a free-boundary point with
`‖y‖ ≤ 3/8`, then `‖∇u - e‖ ≤ C ε` on `{u > 0} ∩ B_{1/4}(y)`. -/
theorem exists_norm_gradient_sub_le_of_flat (hd : 2 ≤ d) : ∃ ε₂ > 0, ∃ C > 0,
    ∀ {u : E d → ℝ} {e : E d} {ε : ℝ}, 0 < ε → ε ≤ ε₂ →
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ y ∈ freeBoundary u (ball 0 1), ‖y‖ ≤ 3 / 8 →
    ∀ z ∈ posSet u (ball 0 1) ∩ ball y (1 / 4), ‖∇ u z - e‖ ≤ C * ε := by
  obtain ⟨ε₁, hε₁, C₁, hC₁, H⟩ := norm_gradient_sub_le_of_flat_uniform (d := d) hd
  set c := ndConst d with hcdef
  have hc0 : 0 < c := ndConst_pos hd
  set K := 4 / c + 1 with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min (ε₁ / (2 * K)) (c / 16), lt_min (by positivity) (by positivity), C₁ * (2 * K),
    by positivity, fun {u e ε} hε hεle hc hnn hmin he hflat y hy hy3 z hz ↦ ?_⟩
  have hεc : 2 * ε / c ≤ 1 / 8 := by
    rw [div_le_iff₀ hc0]
    have := hεle.trans (min_le_right _ _)
    linarith
  have hεK : 2 * K * ε ≤ ε₁ := by
    have := hεle.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hfl := flat_about_freeBoundary hd hε hεc hc hnn hmin he hflat hy hy3
  have hB2 : ball y (1 / 2) ⊆ ball (0 : E d) 1 := fun z hz ↦ by
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z y
    linarith
  -- rescale by `1/2` about `y`
  obtain ⟨hU', hB', hvisc, -, -, hvflat, -⟩ := flat_rescale (L := 0) (qmin := 1)
    (εbar := 2 * K * ε) (r := 1 / 2) (x₀ := y) (e := e) isOpen_ball
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith (fun _ _ ↦ le_rfl) one_pos
    (IsLocalEnergyMinimizer.isViscSolution isOpen_ball continuousOn_const
      (fun _ _ ↦ zero_le_one) hc hnn hmin) (by norm_num) hB2 (fun z hz ↦ by
        have := hfl z hz
        simp only [one_mul]
        rw [show 2 * K * ε * (1 / 2) = K * ε by ring]
        exact this)
  set v : E d → ℝ := fun x ↦ u (y + (1 / 2 : ℝ) • x) / (1 / 2 * (fun _ ↦ (1 : ℝ)) y) with hv
  set U' := (fun x ↦ y + (1 / 2 : ℝ) • x) ⁻¹' ball (0 : E d) 1 with hU'def
  have hvisc' : IsViscSolution U' (fun _ ↦ 1) v := by
    convert hvisc using 1
    funext x; simp
  -- the point `x = 2 (z - y)`
  set x : E d := (2 : ℝ) • (z - y) with hx
  have hxz : y + (1 / 2 : ℝ) • x = z := by
    rw [hx, smul_smul]; norm_num
  have hxP : x ∈ posSet v U' ∩ ball 0 (1 / 2) := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change y + (1 / 2 : ℝ) • x ∈ ball (0 : E d) 1
      rw [hxz]; exact hz.1.1
    · change 0 < u (y + (1 / 2 : ℝ) • x) / (1 / 2 * 1)
      rw [hxz]; have := hz.1.2; positivity
    · have hzy : ‖z - y‖ < 1 / 4 := by simpa [dist_eq_norm] using hz.2
      rw [mem_ball, dist_zero_right, hx, norm_smul, Real.norm_two]
      linarith
  have hb := H U' v e (2 * K * ε) hU' hB' hvisc' he (by positivity) hεK hvflat x hxP
  -- `∇v(x) = ∇u(z)`
  have hud : DifferentiableAt ℝ u (y + (1 / 2 : ℝ) • x) := by
    rw [hxz]
    have hvH : HarmonicOnNhd u (posSet u (ball 0 1)) := IsViscSolution.harmonicOnNhd_posSet
      isOpen_ball (IsLocalEnergyMinimizer.isViscSolution isOpen_ball continuousOn_const
        (fun _ _ ↦ zero_le_one) hc hnn hmin)
    exact (hvH z hz.1).1.differentiableAt (by norm_num)
  have hg := gradient_rescale (c := (fun _ ↦ (1 : ℝ)) y) (by norm_num : (1 / 2 : ℝ) ≠ 0) hud
  rw [hxz] at hg
  have hg' : ∇ v x = ∇ u z := by
    rw [hv, hg]; simp
  rw [hg'] at hb
  calc ‖∇ u z - e‖ ≤ C₁ * (2 * K * ε) := hb
    _ = C₁ * (2 * K) * ε := by ring

end EllipticBernoulli
