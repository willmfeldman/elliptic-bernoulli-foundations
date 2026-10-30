/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import EllipticBernoulli.Classical.BlowupExtraction
import EllipticBernoulli.Harmonic.Limit
import EllipticBernoulli.Sobolev.Closure
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sphere.Radial
import EllipticBernoulli.TwoPhase.Regularity

/-!
# Compactness of rescalings and harmonicity of the limit

Throughout, `f k : ℝᵈ → ℝ` is a sequence of `L`-Lipschitz functions (in the application, the
rescalings `u_{x₀,r_k}` of a Lipschitz function `u` with `u(x₀) = 0`, `blowup`).

* `exists_subseq_tendstoLocallyUniformly_of_apply_zero`: if
  `f k 0 = 0` for all `k`, a subsequence converges locally uniformly to an `L`-Lipschitz `f₀` with
  `f₀ 0 = 0`.
* `exists_subseq_tendstoWeakL2_gradient`: if `f k → f₀`
  locally uniformly, a further subsequence has `∇f_k ⇀ ∇f₀` weakly in `L²(K)` for every compact
  `K`.
* `harmonicOnNhd_posSet_of_tendstoLocallyUniformly`,
  `harmonicOnNhd_negSet_of_tendstoLocallyUniformly`: if each `f k` is
  harmonic on `{f k > 0}` (resp. `{f k < 0}`), so is `f₀` on `{f₀ > 0}` (resp. `{f₀ < 0}`).

Also: `lipschitzWith_of_tendstoLocallyUniformly` (a locally uniform limit of `L`-Lipschitz functions
is `L`-Lipschitz), `TendstoLocallyUniformly.comp_tendsto` (passing to a subsequence) and
`tendsto_eLpNorm_sub_of_tendstoLocallyUniformly` (locally uniform convergence implies `L²_loc`
convergence).

## Proof of harmonicity

If `f₀(x) > 0`, then `f₀ > η > 0` on a ball `B_δ(x)`, and for `k ≥ k₀` also `f k > 0` on `B_δ(x)`.
The shifted sequence `(f (k + k₀))_k` is harmonic on `B_δ(x)` and converges locally uniformly to
`f₀` there, so `harmonicOnNhd_of_tendstoLocallyUniformlyOn` applies.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient NNReal ENNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Locally uniform convergence -/

/-- Locally uniform convergence is preserved under composition with a map of index filters, for
example a subsequence. -/
theorem TendstoLocallyUniformly.comp_tendsto {α β ι ι' : Type*} [TopologicalSpace α]
    [UniformSpace β] {F : ι → α → β} {f : α → β} {p : Filter ι} {p' : Filter ι'} {ns : ι' → ι}
    (h : TendstoLocallyUniformly F f p) (hns : Tendsto ns p' p) :
    TendstoLocallyUniformly (fun k ↦ F (ns k)) f p' := fun u hu x ↦ by
  obtain ⟨t, ht, h'⟩ := h u hu x
  exact ⟨t, ht, hns.eventually h'⟩

/-- A locally uniform limit of `L`-Lipschitz functions is `L`-Lipschitz. -/
theorem lipschitzWith_of_tendstoLocallyUniformly {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hconv : TendstoLocallyUniformly f f₀ atTop) :
    LipschitzWith L f₀ := by
  have h := tendstoLocallyUniformlyOn_univ.2 hconv
  exact LipschitzWith.of_dist_le_mul fun y z ↦ le_of_tendsto'
    ((h.tendsto_at (mem_univ y)).dist (h.tendsto_at (mem_univ z)))
    fun k ↦ (hf k).dist_le_mul y z

/-- Locally uniform convergence of continuous functions implies `L²(K)` convergence on every
compact `K`. -/
theorem tendsto_eLpNorm_sub_of_tendstoLocallyUniformly {f : ℕ → E d → ℝ} {f₀ : E d → ℝ}
    (hf : ∀ k, Continuous (f k)) (hf₀ : Continuous f₀)
    (hconv : TendstoLocallyUniformly f f₀ atTop) {K : Set (E d)} (hK : IsCompact K) :
    Tendsto (fun k ↦ eLpNorm (f k - f₀) 2 (volume.restrict K)) atTop (𝓝 0) := by
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) K hK
  set c : ℝ≥0∞ := volume.restrict K univ ^ (2 : ℝ≥0∞).toReal⁻¹ with hc
  have hcfin : c ≠ ∞ := by
    rw [hc, Measure.restrict_apply_univ]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hK.measure_lt_top.ne
  have hbd : ∀ δ : ℝ, 0 < δ → ∀ᶠ k in atTop,
      eLpNorm (f k - f₀) 2 (volume.restrict K) ≤ c * ENNReal.ofReal δ := by
    intro δ hδ
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hunif δ hδ] with k hk
    refine eLpNorm_le_of_ae_bound ((hf k).sub hf₀).aestronglyMeasurable
      ((ae_restrict_mem hK.measurableSet).mono fun y hy ↦ ?_)
    rw [Pi.sub_apply, Real.norm_eq_abs, ← Real.dist_eq, dist_comm]
    exact (hk y hy).le
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hlim : Tendsto (fun δ : ℝ ↦ c * ENNReal.ofReal δ) (𝓝 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal (tendsto_id (x := 𝓝 (0 : ℝ))))
      (Or.inr hcfin)
    simpa using this
  obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.1 (hlim.eventually (ge_mem_nhds hε))
  have hδ : (0 : ℝ) < r / 2 := half_pos hr
  filter_upwards [hbd (r / 2) hδ] with k hk
  exact hk.trans (hr' (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ]; linarith))

/-! ### Compactness -/

/-- **Compactness of rescalings** (Arzelà–Ascoli,
`exists_blowup_subseq` with `ρ_k = k + 1` and `M = 0`). A sequence of `L`-Lipschitz functions with
`f k 0 = 0` has a subsequence converging locally uniformly to an `L`-Lipschitz `f₀` with
`f₀ 0 = 0`. -/
theorem exists_subseq_tendstoLocallyUniformly_of_apply_zero {f : ℕ → E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hf0 : ∀ k, f k 0 = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : E d → ℝ, LipschitzWith L f₀ ∧ f₀ 0 = 0 ∧
      TendstoLocallyUniformly (fun k ↦ f (φ k)) f₀ atTop := by
  obtain ⟨φ, hφ, f₀, hf₀, hconv⟩ := exists_blowup_subseq (ρ := fun k ↦ (k : ℝ) + 1)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop) (fun k ↦ by positivity)
    (fun k ↦ (hf k).lipschitzOnWith) (M := 0) (fun k ↦ by rw [hf0 k, abs_zero])
  refine ⟨φ, hφ, f₀, hf₀, ?_, hconv⟩
  have h := (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ (0 : E d))
  simp only [hf0] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **Weak convergence of the gradients.** If `L`-Lipschitz
functions `f k` converge locally uniformly to `f₀`, then along a subsequence `∇f_k ⇀ ∇f₀` weakly in
`L²(K)` for every compact `K`. The weak limit `G` given by `exists_tendstoWeakL2Loc_subseq` is a
weak gradient of `f₀` (`HasWeakGradient.of_tendsto`), hence equals `∇f₀` a.e.
(`HasWeakGradient.ae_eq_gradient_of_lipschitzWith`). -/
theorem exists_subseq_tendstoWeakL2_gradient {f : ℕ → E d → ℝ} {f₀ : E d → ℝ} {L : ℝ≥0}
    (hf : ∀ k, LipschitzWith L (f k)) (hconv : TendstoLocallyUniformly f f₀ atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ K, IsCompact K →
      TendstoWeakL2 volume K (fun k ↦ ∇ (f (φ k))) (∇ f₀) atTop := by
  have hf₀ := lipschitzWith_of_tendstoLocallyUniformly hf hconv
  have hH1 : ∀ {g : E d → ℝ} {K : ℝ≥0}, LipschitzWith K g → MemH1Loc univ g (∇ g) := fun hg ↦
    memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ hg.locallyLipschitz.locallyLipschitzOn
  have hbdd : ∀ K ⊆ univ, IsCompact K → ∃ C : ℝ, ∀ n,
      eLpNorm (∇ (f n)) 2 (volume.restrict K) ≤ ENNReal.ofReal C := by
    intro K _ hK
    refine ⟨(volume K).toReal ^ (2 : ℝ≥0∞).toReal⁻¹ * L, fun n ↦ ?_⟩
    refine (eLpNorm_le_of_ae_bound (measurable_gradient _).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ norm_gradient_le_of_lipschitzWith (hf n) x)).trans
      (le_of_eq ?_)
    rw [Measure.restrict_apply_univ, ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hK.measure_lt_top.ne]
  obtain ⟨φ, hφ, G₀, hG₀⟩ := exists_tendstoWeakL2Loc_subseq isOpen_univ (fun n ↦ ∇ (f n))
    (fun n K _ hK ↦ ((hH1 (hf n)).2 K (subset_univ _) hK).2) hbdd
  have hW : HasWeakGradient univ f₀ G₀ :=
    HasWeakGradient.of_tendsto isOpen_univ (fun k ↦ (hH1 (hf (φ k))).1)
      hf₀.continuous.aestronglyMeasurable
      (fun K _ hK ↦ tendsto_eLpNorm_sub_of_tendstoLocallyUniformly
        (fun k ↦ (hf (φ k)).continuous) hf₀.continuous
        (TendstoLocallyUniformly.comp_tendsto hconv hφ.tendsto_atTop) hK)
      (fun K _ hK ↦ hG₀ K (subset_univ _) hK)
  have hae := HasWeakGradient.ae_eq_gradient_of_lipschitzWith hf₀ hW
  exact ⟨φ, hφ, fun K hK ↦ (hG₀ K (subset_univ _) hK).congr_ae (ae_restrict_of_ae hae)⟩

/-! ### Harmonicity of the limit -/

/-- **Harmonicity of the limit, positive phase.** If each `f k` is
harmonic on `{f k > 0}` and `f k → f₀` locally uniformly with `f₀` continuous, then `f₀` is
harmonic on `{f₀ > 0}`. -/
theorem harmonicOnNhd_posSet_of_tendstoLocallyUniformly {f : ℕ → E d → ℝ} {f₀ : E d → ℝ}
    (hH : ∀ k, HarmonicOnNhd (f k) {x | 0 < f k x}) (hf₀ : Continuous f₀)
    (hconv : TendstoLocallyUniformly f f₀ atTop) : HarmonicOnNhd f₀ {x | 0 < f₀ x} := by
  intro x hx
  have hx' : 0 < f₀ x := hx
  -- a closed ball on which `f₀ > f₀ x / 2`
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ y ∈ closedBall x δ, f₀ x / 2 < f₀ y := by
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1
      (hf₀.continuousAt.eventually (lt_mem_nhds (half_lt_self hx')))
    exact ⟨ε / 2, half_pos hε, fun y hy ↦
      h (lt_of_le_of_lt (mem_closedBall.1 hy) (half_lt_self hε))⟩
  have hunif := (tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) _
    (isCompact_closedBall x δ)
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1
    (Metric.tendstoUniformlyOn_iff.1 hunif (f₀ x / 2) (half_pos hx'))
  -- for `k ≥ k₀`, `f k > 0` on `B_δ(x)`
  have hpos : ∀ k ≥ k₀, ∀ y ∈ ball x δ, 0 < f k y := fun k hk y hy ↦ by
    have h1 := hk₀ k hk y (ball_subset_closedBall hy)
    have h2 := hball y (ball_subset_closedBall hy)
    rw [Real.dist_eq] at h1
    linarith [(abs_lt.1 h1).2]
  have hHk : ∀ k, HarmonicOnNhd (f (k + k₀)) (ball x δ) := fun k y hy ↦
    hH (k + k₀) y (hpos _ (by omega) y hy)
  have hconv' : TendstoLocallyUniformlyOn (fun k ↦ f (k + k₀)) f₀ atTop (ball x δ) :=
    (TendstoLocallyUniformly.comp_tendsto hconv
      (tendsto_add_atTop_nat k₀)).tendstoLocallyUniformlyOn
  exact (harmonicOnNhd_of_tendstoLocallyUniformlyOn' isOpen_ball hHk hconv').1 x
    (mem_ball_self hδ)

/-- **Harmonicity of the limit, negative phase.** If each `f k` is
harmonic on `{f k < 0}` and `f k → f₀` locally uniformly with `f₀` continuous, then `f₀` is
harmonic on `{f₀ < 0}`. -/
theorem harmonicOnNhd_negSet_of_tendstoLocallyUniformly {f : ℕ → E d → ℝ} {f₀ : E d → ℝ}
    (hH : ∀ k, HarmonicOnNhd (f k) {x | f k x < 0}) (hf₀ : Continuous f₀)
    (hconv : TendstoLocallyUniformly f f₀ atTop) : HarmonicOnNhd f₀ {x | f₀ x < 0} := by
  have h := harmonicOnNhd_posSet_of_tendstoLocallyUniformly (f := fun k ↦ -f k) (f₀ := -f₀)
    (fun k x hx ↦ (hH k x (show f k x < 0 by simpa using hx)).neg) hf₀.neg hconv.neg
  intro x hx
  simpa using (h x (show 0 < -f₀ x by simpa using hx)).neg

end EllipticBernoulli
