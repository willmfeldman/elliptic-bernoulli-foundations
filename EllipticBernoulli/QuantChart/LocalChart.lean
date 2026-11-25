/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Flatness.Iteration
public import EllipticBernoulli.Statements.Hodograph
import EllipticBernoulli.Hodograph.Chart
import EllipticBernoulli.Flatness.Classical
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Affine
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Lipschitz.Estimate
import EllipticBernoulli.Nondegeneracy.Minimizer
import EllipticBernoulli.Hodograph.Flat

/-!
# Local charts at the free boundary of a flat minimizer

Let `u` be a continuous, non-negative local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` in `B_1`
with `|u(x) - (x · e)₊| ≤ ε` on `B_1`.

* `abs_inner_le_of_mem_freeBoundary_of_flat`: free-boundary points `y` satisfy `|y · e| ≤ ε`.
* `IsFlatC1AlphaAt.isBlowupLimit`: a pointwise `C^{1,α}` expansion at `y` with normal `ν`
  makes `(x · ν)₊` a blow-up limit at `y`.
* `exists_chart_of_flat`: for `ε` small (depending on `d` only), every free-boundary point
  `y ∈ B̄_{1/2}` has a smooth one-sided chart (`FlatChartStatement`).

## Proof

At a free-boundary point `y` with `‖y‖ ≤ 1/2`, `u` is `2ε`-flat about `y` on `B_{1/2}(y) ⊆ B_1`
in direction `e`. Rescaling by `1/2` about `y` (`flat_rescale`) gives a `4ε`-flat viscosity solution
with `0` on its free boundary, so De Silva's iteration (`flat_pointwise_C1alpha`) gives a pointwise
`C^{1,α}` expansion at `0`. Hence the half-plane solution is a blow-up limit at `0`, and so at `y`,
and `flat_chart` applies.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- `|max (a + δ) 0 - max a 0| ≤ |δ|`. -/
private theorem abs_max_add_sub_max_le (a δ : ℝ) : |max (a + δ) 0 - max a 0| ≤ |δ| := by
  rcases le_total 0 (a + δ) with h1 | h1 <;> rcases le_total 0 a with h2 | h2 <;>
    simp only [max_eq_left, max_eq_right, h1, h2] <;> rw [abs_le] <;>
    constructor <;> linarith [le_abs_self δ, neg_abs_le δ]

/-- **Blow-up from a pointwise `C^{1,α}` expansion.** If `IsFlatC1AlphaAt u 1 y ν C α R` with
`α, R > 0`, then `(x · ν)₊` is a blow-up limit of `u` at `y`. -/
theorem IsFlatC1AlphaAt.isBlowupLimit {u : E d → ℝ} {y ν : E d} {C α R : ℝ}
    (h : IsFlatC1AlphaAt u (fun _ ↦ 1) y ν C α R) (hα : 0 < α) (hR : 0 < R) :
    IsBlowupLimit u y (fun z ↦ max ⟪z, ν⟫ 0) := by
  set r : ℕ → ℝ := fun n ↦ R / (n + 1) with hr
  have hr0 : ∀ n, 0 < r n := fun n ↦ by positivity
  have hrt : Tendsto r atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat R |>.comp (tendsto_add_atTop_nat 1) |>.congr
      fun n ↦ by simp [hr]
  refine ⟨r, hr0, hrt, Metric.tendstoLocallyUniformly_iff.2 fun δ hδ x ↦ ?_⟩
  set K := ‖x‖ + 1 with hK
  have hK0 : 0 < K := by positivity
  set M := |C| * K ^ (1 + α) with hM
  have hpow : Tendsto (fun n ↦ r n ^ α) atTop (𝓝 0) := by
    have := ((Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto).comp hrt
    rwa [Real.zero_rpow hα.ne'] at this
  have hev : ∀ᶠ n in atTop, M * r n ^ α < δ ∧ r n * K ≤ R := by
    have h1 : Tendsto (fun n ↦ M * r n ^ α) atTop (𝓝 0) := by
      simpa using hpow.const_mul M
    have h2 : Tendsto (fun n ↦ r n * K) atTop (𝓝 0) := by simpa using hrt.mul_const K
    exact (h1.eventually (gt_mem_nhds hδ)).and (h2.eventually (ge_mem_nhds hR))
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩
  filter_upwards [hev] with n ⟨hn1, hn2⟩ z hz
  have hzK : ‖z‖ < K := by
    have := norm_le_norm_add_norm_sub' z x
    rw [mem_ball, dist_eq_norm] at hz
    linarith
  set ρ := r n with hρ
  have hρ0 : 0 < ρ := hr0 n
  set s := ρ * K with hs
  have hs0 : 0 < s := by positivity
  have hmem : y + ρ • z ∈ ball y s := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hρ0.le]
    exact mul_lt_mul_of_pos_left hzK hρ0
  obtain ⟨hlo, hhi⟩ := h.2 s ⟨hs0, hn2⟩ _ hmem
  simp only [one_mul, add_sub_cancel_left, inner_smul_left, RCLike.conj_to_real] at hlo hhi
  set a := ρ * ⟪z, ν⟫ with ha
  set c := C * s ^ (1 + α) with hc
  have hb : |u (y + ρ • z) - max a 0| ≤ |c| := by
    have e1 := abs_max_add_sub_max_le a c
    have e2 := abs_max_add_sub_max_le a (-c)
    rw [abs_neg, ← sub_eq_add_neg] at e2
    rw [abs_le] at e1 e2 ⊢
    constructor <;> linarith [le_max_right (a - c) 0, le_max_right (a + c) 0]
  have hcs : |c| = |C| * K ^ (1 + α) * ρ ^ (1 + α) := by
    rw [hc, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _), hs,
      Real.mul_rpow hρ0.le hK0.le]
    ring
  have hρpow : ρ ^ (1 + α) = ρ * ρ ^ α := by
    rw [Real.rpow_add hρ0, Real.rpow_one]
  rw [dist_eq_norm, Real.norm_eq_abs, blowup]
  have hmax : max ⟪z, ν⟫ 0 = max a 0 / ρ := by
    rw [ha, ← max_div_div_right hρ0.le, mul_div_cancel_left₀ _ hρ0.ne', zero_div]
  rw [hmax, ← sub_div, abs_div, abs_sub_comm, abs_of_pos hρ0, div_lt_iff₀ hρ0]
  calc |u (y + ρ • z) - max a 0| ≤ |c| := hb
    _ = M * ρ ^ α * ρ := by rw [hcs, hρpow, hM]; ring
    _ < δ * ρ := mul_lt_mul_of_pos_right hn1 hρ0

/-! ### Non-degeneracy and the location of the free boundary -/

/-- The non-degeneracy constant used below, `c_d = 1/(8 d e^{d/2})`. -/
noncomputable def ndConst (d : ℕ) : ℝ := 1 / (8 * d * Real.exp ((d : ℝ) / 2))

theorem ndConst_pos (hd : 2 ≤ d) : 0 < ndConst d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold ndConst; positivity

theorem ndConst_le_one (hd : 2 ≤ d) : ndConst d ≤ 1 := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have he : 1 ≤ Real.exp ((d : ℝ) / 2) := Real.one_le_exp (by positivity)
  unfold ndConst
  rw [div_le_one (by positivity)]
  nlinarith

/-- **Uniform non-degeneracy** of a continuous non-negative local minimizer in an open `U`. -/
theorem nondegenerate_of_isLocalEnergyMinimizer (hd : 2 ≤ d) {U : Set (E d)} {u : E d → ℝ}
    (hU : IsOpen U) (hc : ContinuousOn u U) (hnn : ∀ x ∈ U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) :
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, ndConst d * r ≤ u y := by
  have hvisc : IsViscSolution U (fun _ ↦ 1) u :=
    IsLocalEnergyMinimizer.isViscSolution hU continuousOn_const (fun _ _ ↦ zero_le_one) hc hnn
      hmin
  have hH : HarmonicOnNhd u (posSet u U) := IsViscSolution.harmonicOnNhd_posSet hU hvisc
  have hlip : LocallyLipschitzOn U u :=
    locallyLipschitzOn_of_isViscSuper hU hvisc.1 hH continuousOn_const
  have hdm := hmin.isDownwardMinimizer hU hc hH
  intro z hz r hr hsub
  exact IsDownwardMinimizer.exists_le_of_closedBall_subset (by omega) hU hdm hlip hnn one_pos
    (fun _ _ ↦ le_rfl) ⟨1, fun _ _ ↦ le_rfl⟩ measurable_const z hz r hr hsub

/-- Free-boundary points `y` of a flat minimizer with `‖y‖ + (2/c_d) ε < 1` lie in the slab
`|y · e| ≤ (2/c_d) ε`. -/
theorem abs_inner_le_of_mem_freeBoundary_of_flat_of_lt (hd : 2 ≤ d) {u : E d → ℝ} {e : E d}
    {ε : ℝ} (hε : 0 < ε)
    (hc : ContinuousOn u (ball 0 1)) (hnn : ∀ x ∈ ball (0 : E d) 1, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u) (he : ‖e‖ = 1)
    (hflat : ∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε)
    {y : E d} (hy : y ∈ freeBoundary u (ball 0 1)) (hyr : ‖y‖ + 2 * ε / ndConst d < 1) :
    u y = 0 ∧ |⟪y, e⟫| ≤ 2 * ε / ndConst d := by
  have hc0 := ndConst_pos hd
  have hc1 := ndConst_le_one hd
  have hyU : y ∈ ball (0 : E d) 1 := hy.2
  have hP : IsOpen (posSet u (ball 0 1)) := isOpen_posSet isOpen_ball hc
  have hyP : y ∉ posSet u (ball 0 1) := fun h ↦ hy.1.2 (hP.interior_eq.symm ▸ h)
  have huy : u y = 0 := by
    by_contra hne
    exact hyP ⟨hyU, lt_of_le_of_ne (hnn y hyU) (Ne.symm hne)⟩
  refine ⟨huy, abs_le.2 ⟨?_, ?_⟩⟩
  · -- lower bound, from non-degeneracy at scale `r = 2ε/c`
    set r := 2 * ε / ndConst d with hr
    have hr0 : 0 < r := by positivity
    have hsub : closedBall y r ⊆ ball (0 : E d) 1 := fun z hz ↦ by
      rw [mem_closedBall, dist_eq_norm] at hz
      rw [mem_ball, dist_zero_right]
      have := norm_le_norm_add_norm_sub' z y
      linarith
    obtain ⟨z, hz, hcz⟩ := nondegenerate_of_isLocalEnergyMinimizer hd isOpen_ball hc hnn hmin y
      hy.1.1 r hr0 hsub
    have hzU := hsub hz
    have h1 := (abs_le.1 (hflat z hzU)).2
    have hcr : ndConst d * r = 2 * ε := by rw [hr]; field_simp
    have hze : ⟪z, e⟫ ≤ ⟪y, e⟫ + r := by
      have h2 : ⟪z - y, e⟫ ≤ ‖z - y‖ := by
        have := real_inner_le_norm (z - y) e; rwa [he, mul_one] at this
      rw [inner_sub_left] at h2
      rw [mem_closedBall, dist_eq_norm] at hz
      linarith
    by_contra hneg
    push Not at hneg
    have : max ⟪z, e⟫ 0 < ε := by
      rcases le_total ⟪z, e⟫ 0 with h | h
      · rw [max_eq_right h]; exact hε
      · rw [max_eq_left h]; linarith
    linarith
  · -- upper bound: `u(y) = 0 ≥ (y · e) - ε`
    have h1 := (abs_le.1 (hflat y hyU)).1
    rw [huy] at h1
    have h2 : 2 * ε ≤ 2 * ε / ndConst d := by
      rw [le_div_iff₀ hc0]; nlinarith
    linarith [le_max_left ⟪y, e⟫ 0]

/-- Free-boundary points of a flat minimizer in `B̄_{1/2}` lie in the slab `|y · e| ≤ (2/c_d) ε`. -/
theorem abs_inner_le_of_mem_freeBoundary_of_flat (hd : 2 ≤ d) {u : E d → ℝ} {e : E d}
    {ε : ℝ} (hε : 0 < ε) (hεc : 2 * ε / ndConst d < 1 / 2)
    (hc : ContinuousOn u (ball 0 1)) (hnn : ∀ x ∈ ball (0 : E d) 1, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u) (he : ‖e‖ = 1)
    (hflat : ∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε)
    {y : E d} (hy : y ∈ freeBoundary u (ball 0 1)) (hy2 : ‖y‖ ≤ 1 / 2) :
    u y = 0 ∧ |⟪y, e⟫| ≤ 2 * ε / ndConst d :=
  abs_inner_le_of_mem_freeBoundary_of_flat_of_lt hd hε hc hnn hmin he hflat hy (by linarith)

/-! ### Charts at the free boundary of a flat minimizer -/

/-- **A smooth one-sided chart at every free-boundary point of a flat minimizer.** For `d ≥ 2`
there is `ε₁ > 0` such that, if `u` is a continuous, non-negative local minimizer of `J` in `B_1`
with `|u - (x · e)₊| ≤ ε ≤ ε₁` on `B_1`, then every free-boundary point `y` with `‖y‖ ≤ 1/2` has a
smooth chart `F` on some `B_ρ(y) ⊆ B_1`: `u = max(F, 0)`, `∇F ≠ 0`, `|∇F| = 1` on `{F = 0}` and
`ΔF = 0` on `{F > 0}`. -/
theorem exists_chart_of_flat (hd : 2 ≤ d) : ∃ ε₁ > 0, ∀ {u : E d → ℝ} {e : E d} {ε : ℝ},
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 → ε ≤ ε₁ →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ y ∈ freeBoundary u (ball 0 1), ‖y‖ ≤ 1 / 2 →
    ∃ ρ > 0, ball y ρ ⊆ ball 0 1 ∧ ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball y ρ) ∧
      (∀ x ∈ ball y ρ, u x = max (F x) 0) ∧ (∀ x ∈ ball y ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball y ρ, F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ ball y ρ, 0 < F x → Δ F x = 0) := by
  obtain ⟨εbar, hεbar, α, hα, C, hC, H⟩ := flat_pointwise_C1alpha hd
  set c := ndConst d with hcdef
  have hc0 : 0 < c := ndConst_pos hd
  have hc1 : c ≤ 1 := ndConst_le_one hd
  set K := 4 / c + 1 with hK
  have hK0 : 0 < K := by positivity
  set A := 1 + 2 / c with hA
  have hA0 : 0 < A := by positivity
  set ε₁ := min (εbar / (8 * K * A)) (c ^ 2 / 48) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by positivity) (by positivity)
  refine ⟨ε₁, hε₁0, fun {u e ε} hc hnn hmin he hεle hflat y hy hy2 ↦ ?_⟩
  -- a positive flatness parameter
  set ε' := max ε (ε₁ / 2) with hε'
  have hε'0 : 0 < ε' := lt_max_of_lt_right (by positivity)
  have hε'1 : ε' ≤ ε₁ := max_le hεle (by linarith)
  have hflat' : ∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε' :=
    fun x hx ↦ (hflat x hx).trans (le_max_left _ _)
  have hε'b : ε' ≤ εbar / (8 * K * A) := hε'1.trans (min_le_left _ _)
  have hε'c : ε' ≤ c ^ 2 / 48 := hε'1.trans (min_le_right _ _)
  have hrc : 2 * ε' / c < 1 / 2 := by
    rw [div_lt_iff₀ hc0]; nlinarith
  obtain ⟨huy, hye⟩ := abs_inner_le_of_mem_freeBoundary_of_flat hd hε'0 hrc hc hnn hmin he
    hflat' hy hy2
  set ε₂ := A * ε' with hε₂
  have hε₂0 : 0 < ε₂ := by positivity
  have hye' : |⟪y, e⟫| ≤ ε₂ - ε' := by
    have : ε₂ - ε' = 2 * ε' / c := by rw [hε₂, hA]; ring
    rw [this]; exact hye
  have hyU : y ∈ ball (0 : E d) 1 := hy.2
  have hB2 : ball y (1 / 2) ⊆ ball (0 : E d) 1 := fun z hz ↦ by
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z y
    linarith
  -- approximation about `y`
  have happ : ∀ z ∈ ball y (1 / 2), |u z - max ⟪z - y, e⟫ 0| ≤ 2 * ε₂ * (1 / 2) := by
    intro z hz
    have h1 := hflat' z (hB2 hz)
    have h2 := abs_max_add_sub_max_le ⟪z - y, e⟫ ⟪y, e⟫
    rw [inner_sub_left, sub_add_cancel] at h2
    rw [inner_sub_left]
    calc |u z - max (⟪z, e⟫ - ⟪y, e⟫) 0|
        ≤ |u z - max ⟪z, e⟫ 0| + |max ⟪z, e⟫ 0 - max (⟪z, e⟫ - ⟪y, e⟫) 0| := abs_sub_le _ _ _
      _ ≤ ε' + (ε₂ - ε') := add_le_add h1 (h2.trans hye')
      _ = 2 * ε₂ * (1 / 2) := by ring
  -- the zero side, by non-degeneracy
  have hnd := nondegenerate_of_isLocalEnergyMinimizer hd isOpen_ball hc hnn hmin
  have hAc : A * c = c + 2 := by rw [hA]; field_simp
  have hσ : 2 * ε₂ / c ≤ 1 / 2 / 4 := by
    rw [div_le_iff₀ hc0, hε₂]
    nlinarith
  have hzero : ∀ z ∈ ball y (1 / 4), ⟪z - y, e⟫ ≤ -(2 * (2 * ε₂ / c)) → u z = 0 := by
    intro z hz hze
    refine eq_zero_of_approx he hnn hnd hB2 happ
      (by rw [show (1 : ℝ) / 2 / 2 = 1 / 4 by norm_num]; exact hz) (by positivity) hσ hze ?_
    rw [mul_div_cancel₀ _ hc0.ne']; linarith
  -- two-sided flatness about `y` on `B_{1/4}(y)`
  set η := 4 * K * ε₂ with hη
  have hη0 : 0 < η := by positivity
  have hηb : η ≤ εbar := by
    have : η = 4 * K * A * ε' := by rw [hη, hε₂]; ring
    rw [this]
    have h8 : 8 * K * A * ε' ≤ εbar := by
      rw [le_div_iff₀ (by positivity)] at hε'b; linarith
    linarith [mul_pos (mul_pos hK0 hA0) hε'0]
  have hB4 : ball y (1 / 4) ⊆ ball (0 : E d) 1 :=
    (ball_subset_ball (by norm_num)).trans hB2
  have hflat4 : ∀ z ∈ ball y (1 / 4),
      (fun _ ↦ (1 : ℝ)) y * max (⟪z - y, e⟫ - η * (1 / 4)) 0 ≤ u z ∧
        u z ≤ (fun _ ↦ (1 : ℝ)) y * max (⟪z - y, e⟫ + η * (1 / 4)) 0 := by
    intro z hz
    have hzU := hB4 hz
    have hη4 : η * (1 / 4) = K * ε₂ := by rw [hη]; ring
    have hKε : ε₂ ≤ K * ε₂ := by
      have : 1 ≤ K := by rw [hK]; have : 0 < 4 / c := by positivity
                         linarith
      nlinarith
    have ha := abs_le.1 (happ z (ball_subset_ball (by norm_num) hz))
    simp only [one_mul, hη4]
    constructor
    · refine max_le ?_ (hnn z hzU)
      linarith [le_max_left ⟪z - y, e⟫ 0]
    · by_cases hs : ⟪z - y, e⟫ ≤ -(2 * (2 * ε₂ / c))
      · rw [hzero z hz hs]; exact le_max_right _ _
      · push Not at hs
        refine le_trans ?_ (le_max_left _ _)
        have h4 : -(2 * (2 * ε₂ / c)) = -(4 / c * ε₂) := by ring
        rw [h4] at hs
        rcases le_total 0 ⟪z - y, e⟫ with h0 | h0
        · rw [max_eq_left h0] at ha; linarith
        · rw [max_eq_right h0] at ha
          have : K * ε₂ = 4 / c * ε₂ + ε₂ := by rw [hK]; ring
          linarith
  -- rescale and run De Silva's iteration
  obtain ⟨hU', hB', hvisc, -, -, hvflat, hFB⟩ := flat_rescale (L := 0) (qmin := 1) (εbar := η)
    (r := 1 / 4) (x₀ := y) (e := e) isOpen_ball (LipschitzWith.const (1 : ℝ)).lipschitzOnWith
    (fun _ _ ↦ le_rfl) one_pos (IsLocalEnergyMinimizer.isViscSolution isOpen_ball continuousOn_const
      (fun _ _ ↦ zero_le_one) hc hnn hmin) (by norm_num) hB4 hflat4
  set v : E d → ℝ := fun z ↦ u (y + (1 / 4 : ℝ) • z) / (1 / 4 * (fun _ ↦ (1 : ℝ)) y) with hv
  set U' := (fun z ↦ y + (1 / 4 : ℝ) • z) ⁻¹' ball (0 : E d) 1 with hU'def
  have hvisc' : IsViscSolution U' (fun _ ↦ 1) v := by
    convert hvisc using 1
    funext z; simp
  have h0FB : (0 : E d) ∈ freeBoundary v U' ∩ ball 0 (1 / 2) := by
    refine ⟨?_, mem_ball_self (by norm_num)⟩
    rw [hFB]
    simpa using hy
  obtain ⟨ν, hν⟩ := H U' (fun _ ↦ 1) v e η hU' hB' hvisc' he hη0 hηb
    (fun _ _ ↦ by rw [sub_self, abs_zero]; positivity)
    ((LipschitzWith.const (1 : ℝ)).weaken bot_le).lipschitzOnWith hvflat
  obtain ⟨-, hfC⟩ := hν 0 h0FB
  have hblow : IsBlowupLimit u y (fun z ↦ max ⟪z, ν 0⟫ 0) := by
    obtain ⟨r, hr0, hrt, hconv⟩ := hfC.isBlowupLimit hα.1 (by norm_num : (0 : ℝ) < 1 / 4)
    refine ⟨fun n ↦ r n / 4, fun n ↦ by have := hr0 n; positivity, by
      simpa using hrt.div_const 4, ?_⟩
    have heq : (fun n ↦ blowup u y (r n / 4)) = fun n ↦ blowup v 0 (r n) := by
      funext n z
      have h1 : (1 / 4 : ℝ) • (r n • z) = (r n / 4) • z := by
        rw [smul_smul]; congr 1; ring
      have hrn := (hr0 n).ne'
      simp only [blowup, hv, zero_add, h1]
      field_simp
    rw [heq]; exact hconv
  obtain ⟨ρ, hρ, hρU, F, hF1, hF2, hF3, hF4, hF5, -⟩ :=
    flat_chart hd isOpen_ball hc hnn hmin hy hfC.1 hblow
  exact ⟨ρ, hρ, hρU, F, hF1, hF2, hF3, hF4, hF5⟩

end EllipticBernoulli
