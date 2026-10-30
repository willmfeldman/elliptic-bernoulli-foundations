/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.Radial
public import EllipticBernoulli.Basic.Sobolev
public import EllipticBernoulli.Defs.Variational
import EllipticBernoulli.Sphere.Tangential
import EllipticBernoulli.Sphere.HomogeneousExt
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sobolev.Energy
import EllipticBernoulli.TwoPhase.Regularity
import EllipticBernoulli.TwoPhase.ACFCore

/-!
# The homogeneous competitor for Weiss monotonicity

Let `u : ℝᵈ → ℝ` be `L`-Lipschitz with `u(x₀) = 0`. Write
`e_u(x) = |∇u(x)|² + 1_{u > 0}(x)` (`weissDensity`) for the energy density of
`J(u, B) = ∫_B |∇u|² + 1_{u > 0}` (`energyJ` with `Q ≡ 1` and the pointwise gradient), and
`j(t) = ∫_𝕊 e_u(x₀ + tω) dσ(ω)` (`radialJ`).

* `energyJ_ball_gradient_eq`: for Lipschitz `f`,
  `energyJ (B_r(c)) 1 f ∇f = ENNReal.ofReal (∫_{B_r(c)} e_f)`.
* `homogCompetitor u x₀ t`: the `1`-homogeneous extension of `u|_{∂B_t(x₀)}` into `B_t(x₀)`,
  glued to `u` outside: `x ↦ (|x - x₀|/t) u(x₀ + t (x - x₀)/|x - x₀|)` on `B̄_t(x₀)` and `u`
  elsewhere. It is `3L`-Lipschitz (`lipschitzWith_homogCompetitor`).
* `ae_setIntegral_weissDensity_le`: if `u` is moreover a local
  minimizer of `J` on `ℝᵈ`, then for a.e. `t > 0`,
  `J(u, B_t(x₀)) ≤ (t^d/d) (j(t) - a(t) + t^{-2} m(t))`.

## Proof

For a.e. `t > 0`, `u` is differentiable at `x₀ + tω` for `σ`-a.e. `ω`. At such `ω` and
`0 < τ < t`, the chain rule and the tangential identity (`norm_sq_gradient_homogExt0_of_eq`) give
`|∇v_t(x₀ + τω)|² = u²/t² + |∇u|² - (∂ᵣu)²`, evaluated at `x₀ + tω`, and
`1_{v_t > 0}(x₀ + τω) = 1_{u > 0}(x₀ + tω)`. The polar formula
(`setIntegral_ball_mul_rpow_eq` with `β = 0`) then computes `J(v_t, B_t(x₀))`, and minimality
(`IsLocalEnergyMinimizer.energyJ_gradient_le`) concludes.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped Gradient NNReal

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public noncomputable section

/-- The energy density of `J(u, B) = ∫_B |∇u|² + 1_{u > 0}`:
`e_u(x) = |∇u(x)|² + 1_{u > 0}(x)`. -/
def weissDensity (u : E d → ℝ) (x : E d) : ℝ :=
  ‖∇ u x‖ ^ 2 + {y | 0 < u y}.indicator 1 x

/-- `j(t) = ∫_𝕊 e_u(x₀ + tω) dσ(ω)`, the sphere integral of the energy density. -/
def radialJ (u : E d → ℝ) (x₀ : E d) (t : ℝ) : ℝ :=
  ∫ ω : sphere (0 : E d) 1, weissDensity u (x₀ + t • (ω : E d)) ∂(volume : Measure (E d)).toSphere

/-- The `1`-homogeneous competitor: on `B̄_t(x₀)`,
`x ↦ (|x - x₀|/t) u(x₀ + t (x - x₀)/|x - x₀|)` (written with the `0`-homogeneous extension of
`ω ↦ u(x₀ + tω)`), and `u` off `B̄_t(x₀)`. -/
def homogCompetitor (u : E d → ℝ) (x₀ : E d) (t : ℝ) (x : E d) : ℝ :=
  if ‖x - x₀‖ ≤ t then
    ‖x - x₀‖ / t * homogExt0 (fun ω : sphere (0 : E d) 1 ↦ u (x₀ + t • (ω : E d))) (x - x₀)
  else u x

end

public section

/-! ### The energy density -/

theorem weissDensity_nonneg (u : E d → ℝ) (x : E d) : 0 ≤ weissDensity u x :=
  add_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)

theorem measurable_weissDensity {u : E d → ℝ} (hu : Continuous u) :
    Measurable (weissDensity u) :=
  ((measurable_gradient u).norm.pow_const 2).add
    (measurable_const.indicator (measurableSet_lt measurable_const hu.measurable))

theorem abs_weissDensity_le {u : E d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) (x : E d) :
    |weissDensity u x| ≤ (L : ℝ) ^ 2 + 1 := by
  rw [abs_of_nonneg (weissDensity_nonneg u x), weissDensity]
  have h1 : ‖∇ u x‖ ^ 2 ≤ (L : ℝ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hu x) 2
  have h2 : {y | 0 < u y}.indicator (1 : E d → ℝ) x ≤ 1 :=
    indicator_le_self' (fun _ _ ↦ zero_le_one) x
  linarith

theorem integrableOn_weissDensity_ball {u : E d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (c : E d) (r : ℝ) : IntegrableOn (weissDensity u) (ball c r) :=
  Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2 + 1) measure_ball_lt_top.ne
    (measurable_weissDensity hu.continuous).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ by rw [Real.norm_eq_abs]; exact abs_weissDensity_le hu x)

/-- For Lipschitz `f`, `J(f, B_r(c)) = ∫_{B_r(c)} (|∇f|² + 1_{f > 0})`. -/
theorem energyJ_ball_gradient_eq {f : E d → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (c : E d)
    (r : ℝ) :
    energyJ (ball c r) (fun _ ↦ 1) f (∇ f) =
      ENNReal.ofReal (∫ x in ball c r, weissDensity f x) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_weissDensity_ball hf c r)
    (ae_of_all _ (weissDensity_nonneg f)), energyJ]
  refine setLIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
  rw [weissDensity, one_pow, one_mul]
  congr 2
  by_cases h : 0 < f x
  · rw [indicator_of_mem (show x ∈ posSet f (ball c r) from ⟨hx, h⟩),
      indicator_of_mem (show x ∈ {y | 0 < f y} from h)]
  · rw [indicator_of_notMem (show x ∉ posSet f (ball c r) from fun h' ↦ h h'.2),
      indicator_of_notMem (show x ∉ {y | 0 < f y} from h)]

theorem toReal_energyJ_ball_gradient_eq {f : E d → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (c : E d) (r : ℝ) :
    (energyJ (ball c r) (fun _ ↦ 1) f (∇ f)).toReal = ∫ x in ball c r, weissDensity f x := by
  rw [energyJ_ball_gradient_eq hf c r, ENNReal.toReal_ofReal
    (setIntegral_nonneg measurableSet_ball fun x _ ↦ weissDensity_nonneg f x)]

/-! ### The competitor is Lipschitz -/

private theorem norm_smul_normalize (x : E d) : ‖x‖ • (‖x‖⁻¹ • x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

private theorem norm_normalize_le (x : E d) : ‖‖x‖⁻¹ • x‖ ≤ 1 := by
  rw [norm_smul, norm_inv, norm_norm]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

/-- `|y| |x/|x| - y/|y|| ≤ 2 |x - y|`, with the convention `0/|0| = 0`. -/
private theorem norm_mul_norm_normalize_sub_le (x y : E d) :
    ‖y‖ * ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ := by
  have hsplit : ‖y‖ • (‖x‖⁻¹ • x - ‖y‖⁻¹ • y) = (‖y‖ - ‖x‖) • (‖x‖⁻¹ • x) + (x - y) := by
    rw [smul_sub, norm_smul_normalize, sub_smul, norm_smul_normalize]; abel
  have h1 : ‖(‖y‖ - ‖x‖) • (‖x‖⁻¹ • x)‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |‖y‖ - ‖x‖| * ‖‖x‖⁻¹ • x‖ ≤ |‖y‖ - ‖x‖| * 1 :=
          mul_le_mul_of_nonneg_left (norm_normalize_le x) (abs_nonneg _)
      _ ≤ ‖x - y‖ := by rw [mul_one, abs_sub_comm]; exact abs_norm_sub_norm_le x y
  calc ‖y‖ * ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ = ‖‖y‖ • (‖x‖⁻¹ • x - ‖y‖⁻¹ • y)‖ := by
        rw [norm_smul, norm_norm]
    _ ≤ ‖(‖y‖ - ‖x‖) • (‖x‖⁻¹ • x)‖ + ‖x - y‖ := by rw [hsplit]; exact norm_add_le _ _
    _ ≤ 2 * ‖x - y‖ := by linarith

variable {u : E d → ℝ} {L : ℝ≥0} {x₀ : E d}

/-- The cone function `x ↦ (|x - x₀|/t) u(x₀ + t (x - x₀)/|x - x₀|)` is `3L`-Lipschitz on all of
`ℝᵈ` when `u` is `L`-Lipschitz with `u(x₀) = 0`. -/
private theorem lipschitzWith_cone (hu : LipschitzWith L u) (hx₀ : u x₀ = 0) {t : ℝ}
    (ht : 0 < t) :
    LipschitzWith (3 * L)
      (fun x ↦ ‖x - x₀‖ / t * u (x₀ + t • (‖x - x₀‖⁻¹ • (x - x₀)))) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  set ξ := x - x₀
  set η := y - x₀
  have hxy : dist x y = ‖ξ - η‖ := by rw [dist_eq_norm]; congr 1; simp [ξ, η]
  set a := u (x₀ + t • (‖ξ‖⁻¹ • ξ))
  set b := u (x₀ + t • (‖η‖⁻¹ • η))
  have ha : |a| ≤ L * t := by
    have h := hu.dist_le_mul (x₀ + t • (‖ξ‖⁻¹ • ξ)) x₀
    rw [Real.dist_eq, hx₀, sub_zero, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg ht.le] at h
    calc |a| ≤ L * (t * ‖‖ξ‖⁻¹ • ξ‖) := h
      _ ≤ L * (t * 1) := by gcongr; exact norm_normalize_le ξ
      _ = L * t := by ring
  have hab : |a - b| ≤ L * t * ‖‖ξ‖⁻¹ • ξ - ‖η‖⁻¹ • η‖ := by
    have h := hu.dist_le_mul (x₀ + t • (‖ξ‖⁻¹ • ξ)) (x₀ + t • (‖η‖⁻¹ • η))
    rw [Real.dist_eq, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
      Real.norm_of_nonneg ht.le] at h
    linarith
  have hsplit : ‖ξ‖ / t * a - ‖η‖ / t * b = (‖ξ‖ - ‖η‖) / t * a + ‖η‖ / t * (a - b) := by ring
  rw [Real.dist_eq, hxy, hsplit]
  have hN := norm_mul_norm_normalize_sub_le ξ η
  have hd : |‖ξ‖ - ‖η‖| ≤ ‖ξ - η‖ := abs_norm_sub_norm_le ξ η
  calc |(‖ξ‖ - ‖η‖) / t * a + ‖η‖ / t * (a - b)|
      ≤ |(‖ξ‖ - ‖η‖) / t * a| + |‖η‖ / t * (a - b)| := abs_add_le _ _
    _ = |‖ξ‖ - ‖η‖| / t * |a| + ‖η‖ / t * |a - b| := by
        rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos ht, abs_norm]
    _ ≤ ‖ξ - η‖ / t * (L * t) + ‖η‖ / t * (L * t * ‖‖ξ‖⁻¹ • ξ - ‖η‖⁻¹ • η‖) := by
        gcongr
    _ = L * ‖ξ - η‖ + L * (‖η‖ * ‖‖ξ‖⁻¹ • ξ - ‖η‖⁻¹ • η‖) := by field_simp
    _ ≤ L * ‖ξ - η‖ + L * (2 * ‖ξ - η‖) := by gcongr
    _ = ((3 * L : ℝ≥0) : ℝ) * ‖ξ - η‖ := by push_cast; ring

/-- Gluing two `K`-Lipschitz functions along a sphere: the mixed case. -/
private theorem abs_sub_le_of_mem_closedBall_of_not {f g : E d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) {c : E d} {t : ℝ}
    (hfg : ∀ z, ‖z - c‖ = t → f z = g z) {x y : E d} (hx : ‖x - c‖ ≤ t) (hy : t < ‖y - c‖) :
    |f x - g y| ≤ K * dist x y := by
  set φ : ℝ → ℝ := fun s ↦ ‖x + s • (y - x) - c‖
  have hφc : ContinuousOn φ (Icc 0 1) := by fun_prop
  have hmem : t ∈ Icc (φ 0) (φ 1) := ⟨by simpa [φ] using hx, by simpa [φ] using hy.le⟩
  obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc zero_le_one hφc hmem
  set z := x + s • (y - x)
  have hfz : f z = g z := hfg z hφs
  have hxz : dist x z = s * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, show x - z = -(s • (y - x)) by simp [z], norm_neg, norm_smul,
      Real.norm_of_nonneg hs.1, norm_sub_rev]
  have hzy : dist z y = (1 - s) * dist x y := by
    rw [dist_eq_norm, dist_eq_norm, show z - y = (1 - s) • (x - y) by
      simp only [z, sub_smul, one_smul, smul_sub]; abel, norm_smul,
      Real.norm_of_nonneg (by linarith [hs.2])]
  have h1 := hf.dist_le_mul x z
  have h2 := hg.dist_le_mul z y
  rw [Real.dist_eq] at h1 h2
  calc |f x - g y| = |(f x - f z) + (g z - g y)| := by rw [hfz]; ring_nf
    _ ≤ |f x - f z| + |g z - g y| := abs_add_le _ _
    _ ≤ K * dist x z + K * dist z y := add_le_add h1 h2
    _ = K * dist x y := by rw [hxz, hzy]; ring

/-- Gluing two `K`-Lipschitz functions that agree on the sphere `∂B_t(c)`. -/
private theorem lipschitzWith_piecewise_closedBall {f g : E d → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) (c : E d) (t : ℝ)
    (hfg : ∀ z, ‖z - c‖ = t → f z = g z) :
    LipschitzWith K (fun x ↦ if ‖x - c‖ ≤ t then f x else g x) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq]
  by_cases hx : ‖x - c‖ ≤ t <;> by_cases hy : ‖y - c‖ ≤ t <;>
    simp only [hx, hy, ite_true, ite_false]
  · rw [← Real.dist_eq]; exact hf.dist_le_mul x y
  · exact abs_sub_le_of_mem_closedBall_of_not hf hg hfg hx (not_le.mp hy)
  · rw [abs_sub_comm, dist_comm]
    exact abs_sub_le_of_mem_closedBall_of_not hf hg hfg hy (not_le.mp hx)
  · rw [← Real.dist_eq]; exact hg.dist_le_mul x y

/-- With `u(x₀) = 0`, the competitor is the cone function on `B̄_t(x₀)` (also at `x₀`). -/
private theorem homogCompetitor_eq (hx₀ : u x₀ = 0) (t : ℝ) (x : E d) :
    homogCompetitor u x₀ t x = if ‖x - x₀‖ ≤ t then
      ‖x - x₀‖ / t * u (x₀ + t • (‖x - x₀‖⁻¹ • (x - x₀))) else u x := by
  unfold homogCompetitor
  split_ifs
  · congr 1
    rcases eq_or_ne (x - x₀) 0 with h | h
    · simp [h, hx₀]
    · rw [homogExt0_of_ne_zero _ h]
  · rfl

/-- The homogeneous competitor is `3L`-Lipschitz. -/
theorem lipschitzWith_homogCompetitor (hu : LipschitzWith L u) (hx₀ : u x₀ = 0) {t : ℝ}
    (ht : 0 < t) : LipschitzWith (3 * L) (homogCompetitor u x₀ t) := by
  have heq : homogCompetitor u x₀ t = fun x ↦ if ‖x - x₀‖ ≤ t then
      ‖x - x₀‖ / t * u (x₀ + t • (‖x - x₀‖⁻¹ • (x - x₀))) else u x :=
    funext (homogCompetitor_eq hx₀ t)
  rw [heq]
  have hu3 : LipschitzWith (3 * L) u := hu.weaken (le_mul_of_one_le_left zero_le (by norm_num))
  refine lipschitzWith_piecewise_closedBall (lipschitzWith_cone hu hx₀ ht) hu3 x₀ t fun z hz ↦ ?_
  simp only [hz, div_self ht.ne', one_mul, smul_smul, mul_inv_cancel₀ ht.ne', one_smul,
    add_sub_cancel]

/-- The competitor agrees with `u` off `B_t(x₀)`. -/
theorem homogCompetitor_eq_of_not_mem_ball (hx₀ : u x₀ = 0) {t : ℝ} (ht : 0 < t) {x : E d}
    (hx : x ∉ ball x₀ t) : homogCompetitor u x₀ t x = u x := by
  rw [homogCompetitor_eq hx₀]
  rw [mem_ball, dist_eq_norm, not_lt] at hx
  split_ifs with h
  · have hn : ‖x - x₀‖ = t := le_antisymm h hx
    simp only [hn, div_self ht.ne', one_mul, smul_smul, mul_inv_cancel₀ ht.ne', one_smul,
      add_sub_cancel]
  · rfl

/-! ### The gradient of the competitor -/

/-- The derivative of `x ↦ ‖x - x₀‖` at `x ≠ x₀`. -/
private theorem hasFDerivAt_norm_sub' {x : E d} (hx : x ≠ x₀) :
    HasFDerivAt (fun y : E d ↦ ‖y - x₀‖) (innerSL ℝ (‖x - x₀‖⁻¹ • (x - x₀))) x := by
  have hne : ‖x - x₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have h1 := ((hasFDerivAt_id x).sub_const x₀).norm_sq
  have h2 := h1.sqrt (by simp only [id]; positivity)
  simp only [id, Real.sqrt_sq (norm_nonneg _)] at h2
  refine h2.congr_fderiv ?_
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.coe_id', id, RCLike.conj_to_real]
  rw [smul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

/-- The `0`-homogeneous extension of `ω ↦ u(x₀ + tω)` is differentiable at `ω ∈ 𝕊` when `u` is
differentiable at `x₀ + tω`. -/
private theorem differentiableAt_homogExt0_restrict {t : ℝ} (ω : sphere (0 : E d) 1)
    (hdiff : DifferentiableAt ℝ u (x₀ + t • (ω : E d))) :
    DifferentiableAt ℝ (homogExt0 fun ω' : sphere (0 : E d) 1 ↦ u (x₀ + t • (ω' : E d)))
      (ω : E d) := by
  have hω : ‖(ω : E d)‖ = 1 := norm_eq_of_mem_sphere ω
  have hω0 : (ω : E d) ≠ 0 := norm_ne_zero_iff.mp (by rw [hω]; exact one_ne_zero)
  have heq : (homogExt0 fun ω' : sphere (0 : E d) 1 ↦ u (x₀ + t • (ω' : E d))) =ᶠ[𝓝 (ω : E d)]
      fun y ↦ u (x₀ + t • (‖y‖⁻¹ • y)) := by
    filter_upwards [isOpen_ne.mem_nhds hω0] with y hy
    rw [homogExt0_of_ne_zero _ hy]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
  have hg : DifferentiableAt ℝ (fun y : E d ↦ x₀ + t • (‖y‖⁻¹ • y)) (ω : E d) :=
    (((differentiableAt_id.norm ℝ hω0).inv (by rw [id, hω]; exact one_ne_zero)).smul
      differentiableAt_id).const_smul t |>.const_add x₀
  have hdiff' : DifferentiableAt ℝ u (x₀ + t • (‖(ω : E d)‖⁻¹ • (ω : E d))) := by
    rwa [hω, inv_one, one_smul]
  exact hdiff'.comp (ω : E d) hg

/-- **The gradient of the competitor.** For `0 < τ < t`, if
`u` is differentiable at `x₀ + tω`, then
`|∇v_t(x₀ + τω)|² = u(x₀ + tω)²/t² + |∇u(x₀ + tω)|² - (∂ᵣu(x₀ + tω))²`. -/
theorem norm_sq_gradient_homogCompetitor {t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) (hτt : τ < t)
    (ω : sphere (0 : E d) 1) (hdiff : DifferentiableAt ℝ u (x₀ + t • (ω : E d))) :
    ‖∇ (homogCompetitor u x₀ t) (x₀ + τ • (ω : E d))‖ ^ 2 =
      (u (x₀ + t • (ω : E d)) / t) ^ 2 + ‖∇ u (x₀ + t • (ω : E d))‖ ^ 2 -
        radialDeriv u x₀ (x₀ + t • (ω : E d)) ^ 2 := by
  set f : sphere (0 : E d) 1 → ℝ := fun ω' ↦ u (x₀ + t • (ω' : E d)) with hf
  set F := homogExt0 f with hF
  set x := x₀ + τ • (ω : E d) with hx
  have hω : ‖(ω : E d)‖ = 1 := norm_eq_of_mem_sphere ω
  have hξ : x - x₀ = τ • (ω : E d) := by rw [hx, add_sub_cancel_left]
  have hξn : ‖x - x₀‖ = τ := by rw [hξ, norm_smul, hω, mul_one, Real.norm_of_nonneg hτ.le]
  have hxne : x ≠ x₀ := fun h ↦ by rw [h, sub_self, norm_zero] at hξn; exact hτ.ne' hξn.symm
  -- the competitor is the cone function near `x`
  have hev : homogCompetitor u x₀ t =ᶠ[𝓝 x] fun y ↦ ‖y - x₀‖ * t⁻¹ * F (y - x₀) := by
    have hopen : IsOpen {y : E d | ‖y - x₀‖ < t} :=
      isOpen_lt (continuous_id.sub continuous_const).norm continuous_const
    filter_upwards [hopen.mem_nhds (show ‖x - x₀‖ < t by rw [hξn]; exact hτt)] with y hy
    have hy' : ‖y - x₀‖ ≤ t := le_of_lt hy
    simp only [homogCompetitor, hy', ite_true, hF, div_eq_mul_inv]
    rfl
  -- differentiability of `F` at `x - x₀ = τ ω`
  have hFd : DifferentiableAt ℝ F (x - x₀) := by
    rw [hξ, hF, differentiableAt_homogExt0_smul_iff f hτ]
    exact differentiableAt_homogExt0_restrict ω hdiff
  have hN := hasFDerivAt_norm_sub' (x₀ := x₀) hxne
  have hFc : HasFDerivAt (fun y ↦ F (y - x₀)) (fderiv ℝ F (x - x₀)) x := by
    have := hFd.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)
    simpa [Function.comp_def] using this
  have hprod := (hN.mul_const t⁻¹).mul hFc
  set G := (‖x - x₀‖ / t) • ∇ F (x - x₀) + (F (x - x₀) / t) • (‖x - x₀‖⁻¹ • (x - x₀)) with hG
  have hgrad : HasGradientAt (fun y ↦ ‖y - x₀‖ * t⁻¹ * F (y - x₀)) G x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine hprod.congr_fderiv ?_
    ext v
    simp only [hG, add_apply, smul_apply,
      InnerProductSpace.toDual_apply_apply, inner_add_left, inner_smul_left, RCLike.conj_to_real,
      smul_eq_mul, innerSL_apply_apply, inner_gradient_left]
    ring
  have hFω : F (ω : E d) = u (x₀ + t • (ω : E d)) := by
    rw [hF, homogExt0_of_ne_zero f (norm_ne_zero_iff.mp (by rw [hω]; exact one_ne_zero))]
    simp only [hf, hω, inv_one, one_smul]
  have horth : inner ℝ (∇ F (ω : E d)) (ω : E d) = 0 := inner_gradient_homogExt0_self f _
  have htan := norm_sq_gradient_homogExt0_of_eq x₀ ht (f := f) (fun _ ↦ rfl) ω hdiff
  rw [← hF] at htan
  have hvec : (τ / t) • ∇ F (τ • (ω : E d)) + (F (τ • (ω : E d)) / t) • τ⁻¹ •
      (τ • (ω : E d)) = t⁻¹ • (∇ F (ω : E d) + F (ω : E d) • (ω : E d)) := by
    rw [hF, gradient_homogExt0_smul f hτ, homogExt0_smul f hτ, ← hF, smul_smul, smul_smul,
      smul_smul, smul_add, smul_smul]
    congr 2 <;> field_simp
  rw [hev.gradient_eq, hgrad.gradient, hG, hξn, hξ, hvec, norm_smul, mul_pow, norm_add_sq_real,
    norm_smul, inner_smul_right, horth, hω, htan, hFω, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, mul_pow, sq_abs]
  field_simp
  ring

/-! ### The energy of the competitor -/

/-- On the ray through `ω`, inside `B̄_t(x₀)`: `v_t(x₀ + τω) = (τ/t) u(x₀ + tω)`. -/
theorem homogCompetitor_add_smul (hx₀ : u x₀ = 0) {t τ : ℝ} (hτ : 0 < τ) (hτt : τ ≤ t)
    (ω : sphere (0 : E d) 1) :
    homogCompetitor u x₀ t (x₀ + τ • (ω : E d)) = τ / t * u (x₀ + t • (ω : E d)) := by
  have hω : ‖(ω : E d)‖ = 1 := norm_eq_of_mem_sphere ω
  have hn : ‖x₀ + τ • (ω : E d) - x₀‖ = τ := by
    rw [add_sub_cancel_left, norm_smul, hω, mul_one, Real.norm_of_nonneg hτ.le]
  rw [homogCompetitor_eq hx₀, hn]
  simp only [hτt, ite_true]
  rw [add_sub_cancel_left, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one]

/-- The radial integral `∫_0^t τ^{d-1} c dτ = c t^d/d`. -/
private theorem integral_rpow_mul_const (hd : 1 ≤ d) (t c : ℝ) :
    ∫ τ in (0 : ℝ)..t, τ ^ ((d : ℝ) - 1) * c = t ^ d / d * c := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  rw [intervalIntegral.integral_mul_const, integral_rpow (Or.inl (by linarith)), sub_add_cancel,
    Real.zero_rpow hd0, sub_zero, Real.rpow_natCast]

/-- **The energy of the competitor.** If `u` is
differentiable at `x₀ + tω` for `σ`-a.e. `ω`, then
`J(v_t, B_t(x₀)) = (t^d/d) (j(t) - a(t) + t^{-2} m(t))`. -/
theorem setIntegral_weissDensity_homogCompetitor (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (hx₀ : u x₀ = 0) {t : ℝ} (ht : 0 < t)
    (hdiff : ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
      DifferentiableAt ℝ u (x₀ + t • (ω : E d))) :
    ∫ x in ball x₀ t, weissDensity (homogCompetitor u x₀ t) x =
      t ^ d / d * (radialJ u x₀ t - radialA u x₀ t + radialM u x₀ t / t ^ 2) := by
  set σ := (volume : Measure (E d)).toSphere
  set v := homogCompetitor u x₀ t with hv_def
  have hv := lipschitzWith_homogCompetitor hu hx₀ ht
  have hwm : Measurable u := hu.continuous.measurable
  have h1 := setIntegral_ball_mul_rpow_eq hd (measurable_weissDensity hv.continuous)
    (abs_weissDensity_le hv) x₀ (β := 0) (by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      linarith) ht.le
  simp only [Real.rpow_zero, mul_one, add_zero] at h1
  rw [h1]
  set c := radialJ u x₀ t - radialA u x₀ t + radialM u x₀ t / t ^ 2
  -- integrability of the sphere integrands at radius `t`
  have hint_J : Integrable (fun ω : sphere (0 : E d) 1 ↦ weissDensity u (x₀ + t • (ω : E d))) σ :=
    integrable_toSphere_of_bound (measurable_weissDensity hu.continuous) x₀ t
      fun ω ↦ abs_weissDensity_le hu _
  have hint_a : Integrable (fun ω : sphere (0 : E d) 1 ↦
      radialDeriv u x₀ (x₀ + t • (ω : E d)) ^ 2) σ :=
    integrable_toSphere_of_bound ((measurable_radialDeriv u x₀).pow_const 2) x₀ t
      (B := (L : ℝ) ^ 2) fun ω ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_radialDeriv_le hu _ _) 2
  have hint_m : Integrable (fun ω : sphere (0 : E d) 1 ↦ u (x₀ + t • (ω : E d)) ^ 2) σ :=
    integrable_toSphere_of_bound (hwm.pow_const 2) x₀ t (B := (L * t) ^ 2) fun ω ↦ by
      have h := abs_apply_add_smul_le hu x₀ ht.le ω
      rw [hx₀, abs_zero, zero_add] at h
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  -- the sphere integral at each radius `0 < τ < t`
  have hin : ∀ τ, 0 < τ → τ < t →
      ∫ ω : sphere (0 : E d) 1, weissDensity v (x₀ + τ • (ω : E d)) ∂σ = c := by
    intro τ hτ hτt
    rw [integral_congr_ae (g := fun ω : sphere (0 : E d) 1 ↦
        weissDensity u (x₀ + t • (ω : E d)) - radialDeriv u x₀ (x₀ + t • (ω : E d)) ^ 2 +
          u (x₀ + t • (ω : E d)) ^ 2 / t ^ 2)]
    · rw [integral_add (f := fun ω : sphere (0 : E d) 1 ↦ weissDensity u (x₀ + t • (ω : E d)) -
          radialDeriv u x₀ (x₀ + t • (ω : E d)) ^ 2) (hint_J.sub hint_a) (hint_m.div_const _),
        integral_sub hint_J hint_a,
        integral_div]
      rfl
    · filter_upwards [hdiff] with ω hω
      have hpos : (0 < v (x₀ + τ • (ω : E d))) ↔ 0 < u (x₀ + t • (ω : E d)) := by
        rw [hv_def, homogCompetitor_add_smul hx₀ hτ hτt.le]
        exact mul_pos_iff_of_pos_left (div_pos hτ ht)
      have hind : {y | 0 < v y}.indicator (1 : E d → ℝ) (x₀ + τ • (ω : E d)) =
          {y | 0 < u y}.indicator 1 (x₀ + t • (ω : E d)) := by
        by_cases h : 0 < u (x₀ + t • (ω : E d))
        · rw [indicator_of_mem (show x₀ + τ • (ω : E d) ∈ {y | 0 < v y} from hpos.2 h),
            indicator_of_mem (show x₀ + t • (ω : E d) ∈ {y | 0 < u y} from h)]
          rfl
        · rw [indicator_of_notMem (show x₀ + τ • (ω : E d) ∉ {y | 0 < v y} from
              fun h' ↦ h (hpos.1 h')),
            indicator_of_notMem (show x₀ + t • (ω : E d) ∉ {y | 0 < u y} from h)]
      simp only [weissDensity]
      rw [hv_def, norm_sq_gradient_homogCompetitor ht hτ hτt ω hω, ← hv_def, hind, div_pow]
      ring
  rw [intervalIntegral.integral_congr_ae (g := fun τ ↦ τ ^ ((d : ℝ) - 1) * c),
    integral_rpow_mul_const hd t c]
  filter_upwards [(volume : Measure ℝ).ae_ne t] with τ hτne hτ
  rw [uIoc_of_le ht.le] at hτ
  rw [hin τ hτ.1 (lt_of_le_of_ne hτ.2 hτne)]

/-- **The homogeneous competitor.** Let `u` be `L`-Lipschitz, a local
minimizer of `J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ` (no sign condition), with `u(x₀) = 0`.
Then for a.e. `t > 0`, `J(u, B_t(x₀)) ≤ (t^d/d) (j(t) - a(t) + t^{-2} m(t))`. -/
theorem ae_setIntegral_weissDensity_le (hd : 1 ≤ d) (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hx₀ : u x₀ = 0) :
    ∀ᵐ t, 0 < t → ∫ x in ball x₀ t, weissDensity u x ≤
      t ^ d / d * (radialJ u x₀ t - radialA u x₀ t + radialM u x₀ t / t ^ 2) := by
  filter_upwards [ae_ae_differentiableAt_add_smul hd hu x₀] with t hdiff ht
  have hv := lipschitzWith_homogCompetitor hu hx₀ ht
  have hle := hmin.energyJ_gradient_le hu x₀ t
    (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ hv.locallyLipschitz.locallyLipschitzOn)
    (ae_restrict_of_forall_mem measurableSet_ball.compl fun x hx ↦
      homogCompetitor_eq_of_not_mem_ball hx₀ ht hx)
  rw [energyJ_ball_gradient_eq hu, energyJ_ball_gradient_eq hv, ENNReal.ofReal_le_ofReal_iff
    (setIntegral_nonneg measurableSet_ball fun x _ ↦ weissDensity_nonneg _ x)] at hle
  rw [← setIntegral_weissDensity_homogCompetitor hd hu hx₀ ht (hdiff ht)]
  exact hle

end

end EllipticBernoulli
