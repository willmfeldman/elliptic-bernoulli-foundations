/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Bases

/-!
# Moving-domain Arzelà–Ascoli

The compactness step of De Silva (2011), Lemma 4.1, Step 1, used by `linearized_limit`.

* `exists_subseq_tendsto_of_holder_upTo`: the moving-domain Arzelà–Ascoli lemma, in the
  **pointwise-convergence formulation**: functions `f k` on sets `D k`, uniformly
  bounded and Hölder up to an error `η k → 0`, whose domains approximate `K` from inside, have a
  subsequence and a Hölder limit `g` on `K` with `f (φ k) (y k) → g x` whenever `y k ∈ D (φ k)`
  and `y k → x ∈ K`. No Hausdorff distance is used.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric

public section

namespace EllipticBernoulli

/-! ### Moving-domain compactness -/

/-- Hölder errors are small at small scales: `C t^γ < δ` for `0 ≤ t < ρ`. -/
theorem exists_pos_mul_rpow_lt {C γ δ : ℝ} (hγ : 0 < γ) (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ t : ℝ, 0 ≤ t → t < ρ → C * t ^ γ < δ := by
  have hc : Continuous fun t : ℝ ↦ C * t ^ γ :=
    continuous_const.mul (Real.continuous_rpow_const hγ.le)
  have h0 : C * (0 : ℝ) ^ γ = 0 := by rw [Real.zero_rpow hγ.ne', mul_zero]
  obtain ⟨ρ, hρ, h⟩ := Metric.continuousAt_iff.1 hc.continuousAt δ hδ
  refine ⟨ρ, hρ, fun t ht htρ ↦ ?_⟩
  have := h (x := t) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg ht])
  rw [h0, Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans_lt this

/-- **Moving-domain Arzelà–Ascoli, pointwise form** (De Silva (2011), Lemma 4.1, Step 1). Let
`f k : X → ℝ` be bounded by `M` on `D k`, and Hölder with constant `C` and exponent `γ` on `D k` up
to an additive error `η k → 0` (for all large `k`). Suppose every point of `K` is a limit of points
`a k ∈ D k`. Then along a subsequence `φ` there is a limit `g`, bounded by `M` and
`(C, γ)`-Hölder on `K`, such that `f (φ (ψ k)) (y k) → g x` whenever `ψ k → ∞`,
`y k ∈ D (φ (ψ k))` eventually, and `y k → x ∈ K`. -/
theorem exists_subseq_tendsto_of_holder_upTo {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] {D : ℕ → Set X} {K : Set X} {f : ℕ → X → ℝ}
    {M C γ : ℝ} {η : ℕ → ℝ} (hγ : 0 < γ)
    (hbd : ∀ k, ∀ x ∈ D k, |f k x| ≤ M)
    (happrox : ∀ x ∈ K, ∃ a : ℕ → X, (∀ᶠ k in atTop, a k ∈ D k) ∧ Tendsto a atTop (𝓝 x))
    (hη : Tendsto η atTop (𝓝 0))
    (hmod : ∀ᶠ k in atTop, ∀ x ∈ D k, ∀ y ∈ D k, |f k x - f k y| ≤ C * dist x y ^ γ + η k) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : X → ℝ,
      (∀ x ∈ K, |g x| ≤ M) ∧ (∀ x ∈ K, ∀ y ∈ K, |g x - g y| ≤ C * dist x y ^ γ) ∧
      ∀ x ∈ K, ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∀ y : ℕ → X,
        (∀ᶠ k in atTop, y k ∈ D (φ (ψ k))) → Tendsto y atTop (𝓝 x) →
          Tendsto (fun k ↦ f (φ (ψ k)) (y k)) atTop (𝓝 (g x)) := by
  classical
  rcases K.eq_empty_or_nonempty with hK | ⟨x₀, hx₀⟩
  · exact ⟨id, strictMono_id, fun _ ↦ 0, by simp [hK], by simp [hK], by simp [hK]⟩
  have hM : 0 ≤ M := by
    obtain ⟨a, ha, -⟩ := happrox x₀ hx₀
    obtain ⟨k, hk⟩ := ha.exists
    exact (abs_nonneg _).trans (hbd k _ hk)
  choose! A hAD hAt using happrox
  -- a countable dense subset `S` of `K`
  obtain ⟨S, hSK, hSc, hKS⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace K).exists_countable_dense_subset
  haveI : Countable S := hSc.to_subtype
  -- the diagonal extraction, via sequential compactness of `[-M, M]^S`
  let v : ℕ → S → ℝ := fun k s ↦ max (-M) (min M (f k (A s k)))
  have hv : ∀ k, v k ∈ Set.pi univ (fun _ : S ↦ Icc (-M) M) := fun k s _ ↦
    ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  obtain ⟨Lim, -, φ, hφ, hlim⟩ := (isCompact_univ_pi fun _ ↦ isCompact_Icc).tendsto_subseq hv
  have hlim' : ∀ s : S, Tendsto (fun k ↦ v (φ k) s) atTop (𝓝 (Lim s)) := fun s ↦
    ((continuous_apply s).tendsto Lim).comp hlim
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hvf : ∀ s : S, ∀ᶠ k in atTop, v k s = f k (A s k) := fun s ↦
    (hAD s (hSK s.2)).mono fun k hk ↦ by
      have := abs_le.1 (hbd k _ hk)
      simp only [v]
      rw [min_eq_right this.2, max_eq_right this.1]
  have hrpow : Continuous fun t : ℝ ↦ C * t ^ γ :=
    continuous_const.mul (Real.continuous_rpow_const hγ.le)
  -- the canonical sequences
  set c : X → ℕ → ℝ := fun x j ↦ f (φ j) (A x (φ j)) with hc
  -- the key estimate against the diagonal limits
  have key : ∀ x ∈ K, ∀ s : S, ∀ δ > 0, ∀ᶠ j in atTop,
      |c x j - Lim s| < C * dist x s ^ γ + δ := by
    intro x hx s δ hδ
    set G : ℕ → ℝ := fun j ↦ C * dist (A x (φ j)) (A s (φ j)) ^ γ + η (φ j) +
      |v (φ j) s - Lim s| with hG
    have hGt : Tendsto G atTop (𝓝 (C * dist x s ^ γ + 0 + |Lim s - Lim s|)) := by
      refine ((hrpow.tendsto _).comp (((hAt x hx).comp hφt).dist
        ((hAt s (hSK s.2)).comp hφt))).add (hη.comp hφt) |>.add ?_
      exact ((hlim' s).sub_const _).abs
    rw [sub_self, abs_zero, add_zero, add_zero] at hGt
    filter_upwards [(tendsto_order.1 hGt).2 _ (lt_add_of_pos_right _ hδ),
      hφt.eventually (hAD x hx), hφt.eventually (hAD s (hSK s.2)), hφt.eventually hmod,
      hφt.eventually (hvf s)] with j hj h1 h2 h3 h4
    refine lt_of_le_of_lt ?_ hj
    have h5 := h3 _ h1 _ h2
    simp only [hG, hc]
    rw [h4] at *
    calc |f (φ j) (A x (φ j)) - Lim s|
        ≤ |f (φ j) (A x (φ j)) - f (φ j) (A s (φ j))| + |f (φ j) (A s (φ j)) - Lim s| :=
          abs_sub_le _ _ _
      _ ≤ _ := by linarith
  -- small Hölder errors
  have hsmall : ∀ δ > 0, ∃ ρ > 0, ∀ t : ℝ, 0 ≤ t → t < ρ → C * t ^ γ < δ := by
    intro δ hδ
    have h0 : C * (0 : ℝ) ^ γ = 0 := by rw [Real.zero_rpow hγ.ne', mul_zero]
    obtain ⟨ρ, hρ, h⟩ := Metric.continuousAt_iff.1 hrpow.continuousAt δ hδ
    refine ⟨ρ, hρ, fun t ht htρ ↦ ?_⟩
    have := h (x := t) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg ht])
    rw [h0, Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  have hdense : ∀ x ∈ K, ∀ δ > 0, ∃ s : S, C * dist x s ^ γ < δ := by
    intro x hx δ hδ
    obtain ⟨ρ, hρ, h⟩ := hsmall δ hδ
    obtain ⟨s, hs, hxs⟩ := Metric.mem_closure_iff.1 (hKS hx) ρ hρ
    exact ⟨⟨s, hs⟩, h _ dist_nonneg hxs⟩
  -- Cauchy
  have hcauchy : ∀ x ∈ K, CauchySeq (c x) := by
    intro x hx
    rw [Metric.cauchySeq_iff']
    intro δ hδ
    obtain ⟨s, hs⟩ := hdense x hx (δ / 4) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.1 (key x hx s (δ / 4) (by positivity))
    refine ⟨N, fun n hn ↦ ?_⟩
    have h1 := abs_lt.1 (hN n hn)
    have h2 := abs_lt.1 (hN N le_rfl)
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  set g : X → ℝ := fun x ↦ limUnder atTop (c x) with hg
  have hgt : ∀ x ∈ K, Tendsto (c x) atTop (𝓝 (g x)) := fun x hx ↦ (hcauchy x hx).tendsto_limUnder
  refine ⟨φ, hφ, g, ?_, ?_, ?_⟩
  · -- bound
    intro x hx
    refine le_of_tendsto (hgt x hx).abs ?_
    filter_upwards [hφt.eventually (hAD x hx)] with j hj
    exact hbd _ _ hj
  · -- Hölder
    intro x hx x' hx'
    refine le_of_tendsto_of_tendsto (((hgt x hx).sub (hgt x' hx')).abs)
      ((hrpow.tendsto _).comp (((hAt x hx).comp hφt).dist ((hAt x' hx').comp hφt)) |>.add
        (hη.comp hφt)) ?_ |>.trans_eq (by rw [add_zero])
    filter_upwards [hφt.eventually (hAD x hx), hφt.eventually (hAD x' hx'),
      hφt.eventually hmod] with j h1 h2 h3
    exact h3 _ h1 _ h2
  · -- convergence along admissible sequences
    intro x hx ψ hψ y hy hyx
    have hφψ : Tendsto (fun k ↦ φ (ψ k)) atTop atTop := hφt.comp hψ
    refine ((hgt x hx).comp hψ).congr_dist ?_
    have hGt : Tendsto (fun k ↦ C * dist (A x (φ (ψ k))) (y k) ^ γ + η (φ (ψ k))) atTop
        (𝓝 (C * dist x x ^ γ + 0)) :=
      ((hrpow.tendsto _).comp (((hAt x hx).comp hφψ).dist hyx)).add (hη.comp hφψ)
    rw [dist_self, Real.zero_rpow hγ.ne', mul_zero, add_zero] at hGt
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hGt
    filter_upwards [hφψ.eventually (hAD x hx), hy, hφψ.eventually hmod] with k h1 h2 h3
    rw [Real.dist_eq]
    exact h3 _ h1 _ h2

end EllipticBernoulli
