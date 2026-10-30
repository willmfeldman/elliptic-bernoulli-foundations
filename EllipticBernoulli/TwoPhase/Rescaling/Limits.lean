/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.TwoPhase
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import EllipticBernoulli.TwoPhase.Rescaling.Compact
import EllipticBernoulli.TwoPhase.Rescaling.Strong
import EllipticBernoulli.TwoPhase.Weiss
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sphere.Radial

/-!
# Convergence of the Weiss and ACF functionals along rescalings

Let `f k : ℝᵈ → ℝ` be `L`-Lipschitz, harmonic on `{f k > 0}` and on `{f k < 0}`, with
`f k → f₀` locally uniformly.

* `tendsto_weissW_of_tendstoLocallyUniformly`: if moreover `f k 0 = 0`
  and `{f₀ = 0}` is Lebesgue-null, then `W(f_k, 0, ρ) → W(f₀, 0, ρ)` for `ρ > 0`. The null-set
  hypothesis is the only place where convergence of the indicators `1_{f_k > 0}` is used.
* `tendsto_acfIntegral_of_tendsto`, `tendsto_acfPhi_of_tendstoLocallyUniformly`:
  `Φ(f_k⁺, f_k⁻, 0, ρ) → Φ(f₀⁺, f₀⁻, 0, ρ)`, with
  `f⁺ = max(f, 0)` and `f⁻ = max(-f, 0)`. No indicator convergence is used.

## Proof

Dominated convergence along subsequences (`tendsto_integral_of_forall_subseq_ae`), using that
every subsequence has a further subsequence with `∇f_k → ∇f₀` a.e. on compact sets
(`exists_subseq_ae_tendsto_gradient`, from the strong convergence of
`tendsto_setIntegral_norm_sq_gradient_sub`). For `Φ` the dominating function is
`L² |x|^{2-d}`, integrable on balls, so no splitting `B₁ = B_ε ∪ (B₁ \ B_ε)` is needed. For `W`, if
`f₀(x) > 0` then `f_k(x) > 0` for large `k`, and if `f₀(x) < 0` then `f_k(x) < 0` for large `k`, so
`1_{f_k > 0} → 1_{f₀ > 0}` off `{f₀ = 0}`; the sphere term converges by pointwise convergence and
the bound `|f_k| ≤ L ρ` on `∂B_ρ`.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The Weiss functional -/

/-- **Convergence of `W`** (the only use of indicator convergence). Let
`f k` be `L`-Lipschitz with `f k 0 = 0`, harmonic on `{f k > 0}` and on `{f k < 0}`, with
`f k → f₀` locally uniformly, and suppose `{f₀ = 0}` is Lebesgue-null (true for two-plane
functions, `volume_setOf_twoPlane_eq_zero`). Then `W(f_k, 0, ρ) → W(f₀, 0, ρ)` for `ρ > 0`. -/
theorem tendsto_weissW_of_tendstoLocallyUniformly {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hf0 : ∀ k, f k 0 = 0)
    (hpos : ∀ k, HarmonicOnNhd (f k) {x | 0 < f k x})
    (hneg : ∀ k, HarmonicOnNhd (f k) {x | f k x < 0})
    (hconv : TendstoLocallyUniformly f f₀ atTop) (hnull : volume {x | f₀ x = 0} = 0)
    {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun k ↦ weissW (f k) 0 ρ) atTop (𝓝 (weissW f₀ 0 ρ)) := by
  have hf₀ := lipschitzWith_of_tendstoLocallyUniformly hf hconv
  have hpt : ∀ x, Tendsto (fun k ↦ f k x) atTop (𝓝 (f₀ x)) := fun x ↦
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ x)
  simp_rw [weissW_eq (hf _), weissW_eq hf₀]
  refine Tendsto.sub (Tendsto.div_const ?_ _) (Tendsto.div_const ?_ _)
  · -- the energy term
    have : IsFiniteMeasure (volume.restrict (ball (0 : E d) ρ)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    refine tendsto_integral_of_forall_subseq_ae
      (fun k ↦ (measurable_weissDensity (hf k).continuous).aestronglyMeasurable)
      (integrable_const ((L : ℝ) ^ 2 + 1))
      (fun k ↦ Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs]; exact abs_weissDensity_le (hf k) x) fun ns hns ↦ ?_
    obtain ⟨ms, hms, hae⟩ := exists_subseq_ae_tendsto_gradient hf hf₀
      (isCompact_closedBall 0 ρ)
      ((tendsto_setIntegral_norm_sq_gradient_sub hf hpos hneg hconv
        (isCompact_closedBall 0 ρ)).1) hns
    have hnz : ∀ᵐ x ∂volume.restrict (ball (0 : E d) ρ), f₀ x ≠ 0 :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hnull)
    refine ⟨ms, ?_⟩
    filter_upwards [ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hae, hnz]
      with x hx hx0
    have hfx := (hpt x).comp (hns.comp hms.tendsto_atTop)
    refine (hx.norm.pow 2).add ?_
    rcases hx0.lt_or_gt with hlt | hgt
    · have hev : ∀ᶠ k in atTop, f (ns (ms k)) x < 0 := hfx.eventually (gt_mem_nhds hlt)
      rw [indicator_of_notMem (show x ∉ {y | 0 < f₀ y} from fun h ↦ absurd h hlt.not_gt)]
      exact tendsto_const_nhds.congr' (hev.mono fun k hk ↦ (indicator_of_notMem
        (show x ∉ {y | 0 < f (ns (ms k)) y} from fun h ↦ absurd h hk.not_gt) _).symm)
    · have hev : ∀ᶠ k in atTop, 0 < f (ns (ms k)) x := hfx.eventually (lt_mem_nhds hgt)
      rw [indicator_of_mem (show x ∈ {y | 0 < f₀ y} from hgt)]
      exact tendsto_const_nhds.congr' (hev.mono fun k hk ↦
        (indicator_of_mem (show x ∈ {y | 0 < f (ns (ms k)) y} from hk) _).symm)
  · -- the sphere term
    set σ := (volume : Measure (E d)).toSphere
    have hb : ∀ k (ω : sphere (0 : E d) 1), ‖f k (0 + ρ • (ω : E d)) ^ 2‖ ≤ ((L : ℝ) * ρ) ^ 2 := by
      intro k ω
      have h1 := (hf k).dist_le_mul (0 + ρ • (ω : E d)) 0
      rw [Real.dist_eq, hf0, sub_zero, dist_zero_right, zero_add, norm_smul,
        Real.norm_of_nonneg hρ.le, norm_eq_of_mem_sphere ω, mul_one] at h1
      rw [norm_pow, Real.norm_eq_abs, zero_add]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hm : ∀ k, AEStronglyMeasurable (fun ω : sphere (0 : E d) 1 ↦
        f k (0 + ρ • (ω : E d)) ^ 2) σ := fun k ↦ by
      have := (hf k).continuous
      have hc : Continuous fun ω : sphere (0 : E d) 1 ↦ f k (0 + ρ • (ω : E d)) ^ 2 := by
        fun_prop
      exact hc.aestronglyMeasurable
    exact tendsto_integral_of_dominated_convergence
      (F := fun k (ω : sphere (0 : E d) 1) ↦ f k (0 + ρ • (ω : E d)) ^ 2)
      (fun _ ↦ ((L : ℝ) * ρ) ^ 2) hm (integrable_const _)
      (fun k ↦ Eventually.of_forall (hb k)) (Eventually.of_forall fun ω ↦ (hpt _).pow 2)

/-! ### The ACF functional -/

/-- **Convergence of the ACF integral.** If `L`-Lipschitz `w k`, `w₀` satisfy
`∫_K |∇w_k - ∇w₀|² → 0` for every compact `K`, then `I(w_k, 0, ρ) → I(w₀, 0, ρ)`: the weight
`|x|^{2-d}` is integrable on `B_ρ`. -/
theorem tendsto_acfIntegral_of_tendsto (hd : 1 ≤ d) {w : ℕ → E d → ℝ} {w₀ : E d → ℝ} {L : ℝ≥0}
    (hw : ∀ k, LipschitzWith L (w k)) (hw₀ : LipschitzWith L w₀)
    (hstrong : ∀ K, IsCompact K →
      Tendsto (fun k ↦ ∫ x in K, ‖∇ (w k) x - ∇ w₀ x‖ ^ 2) atTop (𝓝 0)) (ρ : ℝ) :
    Tendsto (fun k ↦ acfIntegral (w k) 0 ρ) atTop (𝓝 (acfIntegral w₀ 0 ρ)) := by
  have hwt : IntegrableOn (fun x : E d ↦ ‖x - 0‖ ^ (2 - (d : ℝ))) (ball 0 ρ) :=
    integrableOn_ball_norm_sub_rpow hd 0 (by linarith) ρ
  refine tendsto_integral_of_forall_subseq_ae
    (fun k ↦ (((measurable_gradient _).norm.pow_const 2).mul
      ((measurable_id.sub_const 0).norm.pow_const _)).aestronglyMeasurable)
    (hwt.const_mul ((L : ℝ) ^ 2)) (fun k ↦ Eventually.of_forall fun x ↦ ?_) fun ns hns ↦ ?_
  · rw [norm_mul, norm_pow, norm_norm, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith (hw k) x) 2)
      (Real.rpow_nonneg (norm_nonneg _) _)
  · obtain ⟨ms, -, hae⟩ := exists_subseq_ae_tendsto_gradient hw hw₀
      (isCompact_closedBall 0 ρ) (hstrong _ (isCompact_closedBall 0 ρ)) hns
    exact ⟨ms, (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hae).mono
      fun x hx ↦ (hx.norm.pow 2).mul_const _⟩

/-- **Convergence of `Φ`.** Let `f k` be `L`-Lipschitz, harmonic on
`{f k > 0}` and on `{f k < 0}`, with `f k → f₀` locally uniformly. Then
`Φ(f_k⁺, f_k⁻, 0, ρ) → Φ(f₀⁺, f₀⁻, 0, ρ)` for every `ρ`, where `f⁺ = max(f, 0)` and
`f⁻ = max(-f, 0)`. No indicator convergence is used. -/
theorem tendsto_acfPhi_of_tendstoLocallyUniformly (hd : 1 ≤ d) {f : ℕ → E d → ℝ}
    {f₀ : E d → ℝ} {L : ℝ≥0} (hf : ∀ k, LipschitzWith L (f k))
    (hpos : ∀ k, HarmonicOnNhd (f k) {x | 0 < f k x})
    (hneg : ∀ k, HarmonicOnNhd (f k) {x | f k x < 0})
    (hconv : TendstoLocallyUniformly f f₀ atTop) (ρ : ℝ) :
    Tendsto (fun k ↦ acfPhi (fun y ↦ max (f k y) 0) (fun y ↦ max (-f k y) 0) 0 ρ) atTop
      (𝓝 (acfPhi (fun y ↦ max (f₀ y) 0) (fun y ↦ max (-f₀ y) 0) 0 ρ)) := by
  have hf₀ := lipschitzWith_of_tendstoLocallyUniformly hf hconv
  have h1 := tendsto_acfIntegral_of_tendsto hd (w := fun k y ↦ max (f k y) 0)
    (fun k ↦ (hf k).max_const 0) (hf₀.max_const 0)
    (fun K hK ↦ (tendsto_setIntegral_norm_sq_gradient_sub hf hpos hneg hconv hK).2.1) ρ
  have h2 := tendsto_acfIntegral_of_tendsto hd (w := fun k y ↦ max (-f k y) 0)
    (fun k ↦ (hf k).neg.max_const 0) (hf₀.neg.max_const 0)
    (fun K hK ↦ (tendsto_setIntegral_norm_sq_gradient_sub hf hpos hneg hconv hK).2.2) ρ
  simp only [acfPhi]
  exact (h1.mul h2).div_const _

end EllipticBernoulli
