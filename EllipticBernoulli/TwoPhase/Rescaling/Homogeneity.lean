/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Regularity
public import EllipticBernoulli.Defs.TwoPhase
import EllipticBernoulli.TwoPhase.Rescaling.Compact
import EllipticBernoulli.TwoPhase.Rescaling.Euler
import EllipticBernoulli.TwoPhase.Rescaling.Strong
import EllipticBernoulli.TwoPhase.Weiss
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sphere.Radial

/-!
# Homogeneity of limits of rescalings

Let `f k : ℝᵈ → ℝ` be `L`-Lipschitz with `f k 0 = 0`, harmonic on `{f k > 0}` and on `{f k < 0}`,
with `f k → f₀` locally uniformly.

* `tendsto_weissDefect_of_tendsto`: if
  `∫_K |∇f_k - ∇f₀|² → 0` on compact sets, then `D(f_k, 0; ρ, ρ') → D(f₀, 0; ρ, ρ')` for
  `0 < ρ`. Only strong convergence is used, no lower semicontinuity.
* `ae_inner_gradient_eq_of_weissDefect_eq_zero`: if `D(v, 0; ρ, ρ') = 0` for all `0 < ρ < ρ'`, then
  `x · ∇v(x) = v(x)` a.e.
* `homogeneous_of_tendsto_weissDefect`: if
  `D(f_k, 0; ρ, ρ') → 0` for all `0 < ρ < ρ'`, then `f₀` is positively `1`-homogeneous (with
  `homogeneous_of_ae_inner_gradient_eq`, Euler's relation integrated).
* `tendsto_weissDefect_blowup_nhdsGT`, `tendsto_weissDefect_blowup_atTop`: for a Lipschitz local
  minimizer `u` with `u(x₀) = 0` and rescalings `u_{x₀,r_k}` (`blowup`) with `r_k → 0⁺` (blow-up)
  or `r_k → ∞` (blow-down), `D(u_{x₀,r_k}, 0; ρ, ρ') = D(u, x₀; r_k ρ, r_k ρ') → 0`, since
  `0 ≤ D(u, x₀; r_k ρ, r_k ρ') ≤ W(u, x₀, r_k ρ') - W(u, x₀, r_k ρ)` and `W(u, x₀, ·)` has a
  limit at `0⁺` and at `∞` (`exists_tendsto_weissW`).

## Proof of the defect limit

On the annulus `A = B_{ρ'} \ B_ρ` the weight `|x|^{-d-2}` is bounded and
`|x · ∇f_k - f_k| ≤ 2 L ρ'`. Every subsequence has a further subsequence with `∇f_k → ∇f₀` a.e. on
`B̄_{ρ'}` (`exists_subseq_ae_tendsto_gradient`), and `f_k → f₀` pointwise; dominated convergence
along subsequences (`tendsto_integral_of_forall_subseq_ae`) concludes.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The defect integrand -/

/-- The integrand of `D(v, 0; ρ, ρ')` is bounded by `ρ^{-d-2} (2 L ρ')²` on `B_{ρ'} \ B_ρ`, for
`L`-Lipschitz `v` with `v 0 = 0`. -/
theorem norm_weissDefect_integrand_le {v : E d → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v)
    (hv0 : v 0 = 0) {ρ ρ' : ℝ} (hρ : 0 < ρ) {x : E d} (hx : x ∈ ball (0 : E d) ρ' \ ball 0 ρ) :
    ‖‖x - 0‖ ^ (-(d : ℝ) - 2) * (inner ℝ (x - 0) (∇ v x) - v x) ^ 2‖ ≤
      ρ ^ (-(d : ℝ) - 2) * (2 * L * ρ') ^ 2 := by
  rw [sub_zero]
  have hxρ : ρ ≤ ‖x‖ := by simpa using hx.2
  have hxρ' : ‖x‖ < ρ' := by simpa using hx.1
  have hvx : |v x| ≤ L * ‖x‖ := by
    have := hv.dist_le_mul x 0
    rwa [dist_zero_right, Real.dist_eq, hv0, sub_zero] at this
  have hin : |inner ℝ x (∇ v x)| ≤ ‖x‖ * L :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (norm_gradient_le_of_lipschitzWith hv x) (norm_nonneg _))
  have h1 : |inner ℝ x (∇ v x) - v x| ≤ 2 * L * ρ' := by
    have := abs_sub (inner ℝ x (∇ v x)) (v x)
    nlinarith [NNReal.coe_nonneg L]
  have hw : ‖x‖ ^ (-(d : ℝ) - 2) ≤ ρ ^ (-(d : ℝ) - 2) :=
    Real.rpow_le_rpow_of_nonpos hρ hxρ (by linarith [(d.cast_nonneg : (0 : ℝ) ≤ d)])
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), norm_pow,
    Real.norm_eq_abs]
  exact mul_le_mul hw (pow_le_pow_left₀ (abs_nonneg _) h1 2) (by positivity)
    (Real.rpow_nonneg hρ.le _)

/-- The integrand of `D(v, 0; ρ, ρ')` is measurable for continuous `v`. -/
theorem measurable_weissDefect_integrand {v : E d → ℝ} (hv : Continuous v) :
    Measurable fun x : E d ↦ ‖x - 0‖ ^ (-(d : ℝ) - 2) * (inner ℝ (x - 0) (∇ v x) - v x) ^ 2 :=
  ((measurable_id.sub_const 0).norm.pow_const _).mul
    ((((measurable_id.sub_const 0).inner (measurable_gradient v)).sub hv.measurable).pow_const 2)

/-- The integrand of `D(v, 0; ρ, ρ')` is integrable on `B_{ρ'} \ B_ρ`. -/
theorem integrableOn_weissDefect_integrand {v : E d → ℝ} {L : ℝ≥0} (hv : LipschitzWith L v)
    (hv0 : v 0 = 0) {ρ ρ' : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun x : E d ↦ ‖x - 0‖ ^ (-(d : ℝ) - 2) * (inner ℝ (x - 0) (∇ v x) - v x) ^ 2)
      (ball 0 ρ' \ ball 0 ρ) :=
  Measure.integrableOn_of_bounded (M := ρ ^ (-(d : ℝ) - 2) * (2 * L * ρ') ^ 2)
    ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
    (measurable_weissDefect_integrand hv.continuous).aestronglyMeasurable
    ((ae_restrict_mem (measurableSet_ball.diff measurableSet_ball)).mono fun _ hx ↦
      norm_weissDefect_integrand_le hv hv0 hρ hx)

/-! ### The defect passes to the limit -/

/-- **The Weiss defect passes to the limit.** Let
`f k` be `L`-Lipschitz with `f k 0 = 0`, `f k → f₀` locally uniformly, and
`∫_K |∇f_k - ∇f₀|² → 0` for every compact `K`. Then `D(f_k, 0; ρ, ρ') → D(f₀, 0; ρ, ρ')` for every
`0 < ρ` and `ρ'`. -/
theorem tendsto_weissDefect_of_tendsto {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hf0 : ∀ k, f k 0 = 0)
    (hconv : TendstoLocallyUniformly f f₀ atTop)
    (hstrong : ∀ K, IsCompact K →
      Tendsto (fun k ↦ ∫ x in K, ‖∇ (f k) x - ∇ f₀ x‖ ^ 2) atTop (𝓝 0))
    {ρ ρ' : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun k ↦ weissDefect (f k) 0 ρ ρ') atTop (𝓝 (weissDefect f₀ 0 ρ ρ')) := by
  have hf₀ := lipschitzWith_of_tendstoLocallyUniformly hf hconv
  have hpt : ∀ x, Tendsto (fun k ↦ f k x) atTop (𝓝 (f₀ x)) := fun x ↦
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ x)
  set A : Set (E d) := ball 0 ρ' \ ball 0 ρ
  have hAm : MeasurableSet A := measurableSet_ball.diff measurableSet_ball
  have : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.2 ((measure_mono sdiff_subset).trans_lt measure_ball_lt_top).ne
  have hAK : A ⊆ closedBall 0 ρ' := sdiff_subset.trans ball_subset_closedBall
  refine tendsto_integral_of_forall_subseq_ae
    (fun k ↦ (measurable_weissDefect_integrand (hf k).continuous).aestronglyMeasurable)
    (integrable_const (ρ ^ (-(d : ℝ) - 2) * (2 * L * ρ') ^ 2))
    (fun k ↦ (ae_restrict_mem hAm).mono fun _ hx ↦ norm_weissDefect_integrand_le (hf k) (hf0 k)
      hρ hx) fun ns hns ↦ ?_
  obtain ⟨ms, hms, hae⟩ := exists_subseq_ae_tendsto_gradient hf hf₀ (isCompact_closedBall 0 ρ')
    (hstrong _ (isCompact_closedBall 0 ρ')) hns
  refine ⟨ms, (ae_restrict_of_ae_restrict_of_subset hAK hae).mono fun x hx ↦ ?_⟩
  have hfx := (hpt x).comp (hns.comp hms.tendsto_atTop)
  exact tendsto_const_nhds.mul (((tendsto_const_nhds.inner hx).sub hfx).pow 2)

/-! ### Vanishing defect and homogeneity -/

/-- If `D(v, 0; ρ, ρ') = 0` for all `0 < ρ < ρ'`, then `x · ∇v(x) = v(x)` for a.e. `x`. -/
theorem ae_inner_gradient_eq_of_weissDefect_eq_zero {v : E d → ℝ} {L : ℝ≥0}
    (hv : LipschitzWith L v) (hv0 : v 0 = 0)
    (hD : ∀ ρ ρ' : ℝ, 0 < ρ → ρ < ρ' → weissDefect v 0 ρ ρ' = 0) :
    ∀ᵐ x, inner ℝ x (∇ v x) = v x := by
  set A : ℕ → Set (E d) := fun n ↦ ball 0 ((n : ℝ) + 2) \ ball 0 (1 / ((n : ℝ) + 1))
  have hA : ∀ n, ∀ᵐ x, x ∈ A n → inner ℝ x (∇ v x) = v x := by
    intro n
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    have hρ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hρρ' : 1 / ((n : ℝ) + 1) < (n : ℝ) + 2 :=
      calc 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        _ < _ := by linarith
    have hAm : MeasurableSet (A n) := measurableSet_ball.diff measurableSet_ball
    have h0 := hD _ _ hρ hρρ'
    rw [weissDefect] at h0
    have hz := (setIntegral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x ↦ mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (sq_nonneg _))
      (integrableOn_weissDefect_integrand hv hv0 hρ (ρ' := (n : ℝ) + 2))).1 h0
    rw [← ae_restrict_iff' hAm]
    filter_upwards [hz, ae_restrict_mem hAm] with x hx hxA
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hρ (by simpa using hxA.2)
    rw [Pi.zero_apply, sub_zero, mul_eq_zero] at hx
    rcases hx with h | h
    · exact absurd h (Real.rpow_pos_of_pos hxpos _).ne'
    · have := pow_eq_zero_iff two_ne_zero |>.1 h
      linarith
  filter_upwards [ae_all_iff.2 hA] with x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [hv0]
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖x‖ ‖x‖⁻¹)
    have h1 : ‖x‖ < n := (le_max_left _ _).trans_lt hn
    have h2 : ‖x‖⁻¹ < n := (le_max_right _ _).trans_lt hn
    refine hx n ⟨by rw [mem_ball_zero_iff]; linarith, fun hb ↦ ?_⟩
    rw [mem_ball_zero_iff] at hb
    have h3 : 1 / ((n : ℝ) + 1) < 1 / ‖x‖⁻¹ :=
      one_div_lt_one_div_of_lt (inv_pos.2 hxpos) (by linarith)
    rw [show 1 / ‖x‖⁻¹ = ‖x‖ by rw [one_div, inv_inv]] at h3
    linarith

/-- **Homogeneity of the limit.** Let `f k` be `L`-Lipschitz with
`f k 0 = 0`, harmonic on `{f k > 0}` and on `{f k < 0}`, with `f k → f₀` locally uniformly. If
`D(f_k, 0; ρ, ρ') → 0` for all `0 < ρ < ρ'`, then `f₀(t x) = t f₀(x)` for every `t > 0` and `x`. -/
theorem homogeneous_of_tendsto_weissDefect {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hf0 : ∀ k, f k 0 = 0)
    (hpos : ∀ k, HarmonicOnNhd (f k) {x | 0 < f k x})
    (hneg : ∀ k, HarmonicOnNhd (f k) {x | f k x < 0})
    (hconv : TendstoLocallyUniformly f f₀ atTop)
    (hD : ∀ ρ ρ' : ℝ, 0 < ρ → ρ < ρ' →
      Tendsto (fun k ↦ weissDefect (f k) 0 ρ ρ') atTop (𝓝 0)) :
    ∀ t : ℝ, 0 < t → ∀ x, f₀ (t • x) = t * f₀ x := by
  have hf₀ := lipschitzWith_of_tendstoLocallyUniformly hf hconv
  have hf₀0 : f₀ 0 = 0 := by
    have h := (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ (0 : E d))
    simp only [hf0] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  refine homogeneous_of_ae_inner_gradient_eq hf₀
    (ae_inner_gradient_eq_of_weissDefect_eq_zero hf₀ hf₀0 fun ρ ρ' hρ hρρ' ↦ ?_)
  exact tendsto_nhds_unique (tendsto_weissDefect_of_tendsto hf hf0 hconv
    (fun K hK ↦ (tendsto_setIntegral_norm_sq_gradient_sub hf hpos hneg hconv hK).1) hρ)
    (hD ρ ρ' hρ hρρ')

/-! ### The defect of blow-ups and blow-downs -/

/-- For a Lipschitz local minimizer with `u(x₀) = 0` and radii `r k > 0` such that
`W(u, x₀, r_k ρ)` and `W(u, x₀, r_k ρ')` have the same limit, `D(u_{x₀,r_k}, 0; ρ, ρ') → 0`. -/
private theorem tendsto_weissDefect_blowup_of_tendsto {u : E d → ℝ} {L : ℝ≥0} {x₀ : E d}
    (hd : 1 ≤ d) (hu : LipschitzWith L u) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hx₀ : u x₀ = 0) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ')
    {W : ℝ} (h1 : Tendsto (fun k ↦ weissW u x₀ (r k * ρ)) atTop (𝓝 W))
    (h2 : Tendsto (fun k ↦ weissW u x₀ (r k * ρ')) atTop (𝓝 W)) :
    Tendsto (fun k ↦ weissDefect (blowup u x₀ (r k)) 0 ρ ρ') atTop (𝓝 0) := by
  have hlim := h2.sub h1
  rw [sub_self] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun k ↦ weissDefect_nonneg _ _ _ _) fun k ↦ ?_
  rw [weissDefect_blowup u x₀ (hr k)]
  exact weissDefect_le_weissW_sub hd hu hmin hx₀ (mul_pos (hr k) hρ)
    (mul_le_mul_of_nonneg_left hρρ'.le (hr k).le)

/-- **The defect of blow-ups tends to `0`.** Let `u` be an
`L`-Lipschitz local minimizer of `J` with `u(x₀) = 0`, and `r k → 0⁺`. Then for `0 < ρ < ρ'`,
`D(u_{x₀,r_k}, 0; ρ, ρ') = D(u, x₀; r_k ρ, r_k ρ') ≤ W(u, x₀, r_k ρ') - W(u, x₀, r_k ρ) → 0`. -/
theorem tendsto_weissDefect_blowup_nhdsGT {u : E d → ℝ} {L : ℝ≥0} {x₀ : E d} (hd : 1 ≤ d)
    (hu : LipschitzWith L u) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hx₀ : u x₀ = 0) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') :
    Tendsto (fun k ↦ weissDefect (blowup u x₀ (r k)) 0 ρ ρ') atTop (𝓝 0) := by
  obtain ⟨W₀, -, hW₀, -⟩ := exists_tendsto_weissW hd hu hmin hx₀
  have hs : ∀ s : ℝ, 0 < s → Tendsto (fun k ↦ r k * s) atTop (𝓝[>] 0) := fun s hs ↦
    tendsto_nhdsWithin_iff.2 ⟨by simpa using hr0.mul_const s,
      Eventually.of_forall fun k ↦ mul_pos (hr k) hs⟩
  exact tendsto_weissDefect_blowup_of_tendsto hd hu hmin hx₀ hr hρ hρρ'
    (hW₀.comp (hs ρ hρ)) (hW₀.comp (hs ρ' (hρ.trans hρρ')))

/-- **The defect of blow-downs tends to `0`.** Let `u` be an
`L`-Lipschitz local minimizer of `J` with `u(x₀) = 0`, and `r k → ∞`. Then for `0 < ρ < ρ'`,
`D(u_{x₀,r_k}, 0; ρ, ρ') → 0`. -/
theorem tendsto_weissDefect_blowup_atTop {u : E d → ℝ} {L : ℝ≥0} {x₀ : E d} (hd : 1 ≤ d)
    (hu : LipschitzWith L u) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hx₀ : u x₀ = 0) {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop atTop)
    {ρ ρ' : ℝ} (hρ : 0 < ρ) (hρρ' : ρ < ρ') :
    Tendsto (fun k ↦ weissDefect (blowup u x₀ (r k)) 0 ρ ρ') atTop (𝓝 0) := by
  obtain ⟨-, W₁, -, hW₁, -⟩ := exists_tendsto_weissW hd hu hmin hx₀
  exact tendsto_weissDefect_blowup_of_tendsto hd hu hmin hx₀ hr hρ hρρ'
    (hW₁.comp (hr0.atTop_mul_const hρ)) (hW₁.comp (hr0.atTop_mul_const (hρ.trans hρρ')))

end EllipticBernoulli
