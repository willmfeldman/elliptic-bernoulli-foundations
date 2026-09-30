/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import EllipticBernoulli.Sobolev.WeakCompactness
public import EllipticBernoulli.Sobolev.L2Inner
public import Mathlib.Order.LiminfLimsup

/-!
# Weak `L²` convergence: compactness and weighted lower semicontinuity

* `exists_tendstoWeakL2_subseq`: an `L²(Ω)`-bounded sequence has a weakly convergent
  subsequence, in the sense of `TendstoWeakL2`. Glue around
  `exists_weakly_convergent_subseq` (`Sobolev/WeakCompactness.lean`).
* `lintegral_weighted_sq_le_liminf`: if `f_i ⇀ f₀` weakly in `L²(Ω)` and `0 ≤ η ≤ C` is
  measurable, then `∫_Ω η |f₀|² ≤ liminf ∫_Ω η |f_i|²`. Proof: the pointwise inequality
  `η |f_i|² ≥ 2 ⟨f_i, η f₀⟩ - η |f₀|²` (i.e. `η |f_i - f₀|² ≥ 0`), integrated, and weak
  convergence tested against `η f₀ ∈ L²(Ω)`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- `ofReal (∫ g) ≤ ∫⁻ ofReal g` for integrable real `g`. -/
theorem ofReal_integral_le_lintegral_ofReal {μ : Measure X} {g : X → ℝ} (hg : Integrable g μ) :
    ENNReal.ofReal (∫ x, g x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]
  exact (ENNReal.ofReal_le_ofReal (sub_le_self _ ENNReal.toReal_nonneg)).trans
    ENNReal.ofReal_toReal_le

/-- `∫ ‖f‖² ≤ (max C 0)²` from `‖f‖_{L²} ≤ C`. -/
theorem integral_norm_sq_le_of_eLpNorm_le [FiniteDimensional ℝ F] {μ : Measure X} {f : X → F}
    (hf : MemLp f 2 μ) {C : ℝ} (hC : eLpNorm f 2 μ ≤ ENNReal.ofReal C) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ max C 0 ^ 2 := by
  have e : ∫ x, ‖f x‖ ^ 2 ∂μ = ‖hf.toLp f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp] with x e₁
    rw [e₁, real_inner_self_eq_norm_sq]
  have hn : ‖hf.toLp f‖ ≤ max C 0 := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (le_max_right _ _)
      (hC.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  rw [e]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- **Weak sequential compactness in `L²(Ω)`**, in the form of `TendstoWeakL2`. -/
theorem exists_tendstoWeakL2_subseq [FiniteDimensional ℝ F] (μ : Measure X) (Ω : Set X)
    (f : ℕ → X → F) (C : ℝ) (hf : ∀ n, MemLp (f n) 2 (μ.restrict Ω))
    (hC : ∀ n, eLpNorm (f n) 2 (μ.restrict Ω) ≤ ENNReal.ofReal C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : X → F, TendstoWeakL2 μ Ω (fun n ↦ f (φ n)) f₀ atTop := by
  obtain ⟨φ, hφ, G, hG, hconv⟩ := exists_weakly_convergent_subseq f (max C 0 ^ 2) hf
    fun n ↦ integral_norm_sq_le_of_eLpNorm_le (hf n) (hC n)
  exact ⟨φ, hφ, G, fun n ↦ hf (φ n), hG, hconv⟩

/-- **Weighted weak lower semicontinuity of `∫ |f|²`.** -/
theorem lintegral_weighted_sq_le_liminf {ι : Type*} {l : Filter ι} (μ : Measure X) (Ω : Set X)
    (f : ι → X → F) (f₀ : X → F) (hf : TendstoWeakL2 μ Ω f f₀ l) (η : X → ℝ)
    (hη : Measurable η) (hη0 : ∀ x, 0 ≤ η x) (C : ℝ) (hηC : ∀ x, η x ≤ C) :
    ∫⁻ x in Ω, ENNReal.ofReal (η x * ‖f₀ x‖ ^ 2) ∂μ ≤
      liminf (fun i ↦ ∫⁻ x in Ω, ENNReal.ofReal (η x * ‖f i x‖ ^ 2) ∂μ) l := by
  obtain ⟨hfi, hf₀, hconv⟩ := hf
  rcases l.eq_or_neBot with rfl | hl
  · simp
  have hηb : ∀ x, ‖η x‖ ≤ C := fun x ↦ by rw [Real.norm_of_nonneg (hη0 x)]; exact hηC x
  -- the test function `η f₀ ∈ L²(Ω)`
  have hh : MemLp (fun x ↦ η x • f₀ x) 2 (μ.restrict Ω) :=
    hf₀.of_le_mul (c := C) (hη.aestronglyMeasurable.smul hf₀.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ by rw [norm_smul]; gcongr; exact hηb x)
  set A : ℝ := ∫ x in Ω, η x * ‖f₀ x‖ ^ 2 ∂μ
  have hA : ∫ x in Ω, inner ℝ (f₀ x) (η x • f₀ x) ∂μ = A := by
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [inner_smul_right, real_inner_self_eq_norm_sq]
  have hAint : Integrable (fun x ↦ η x * ‖f₀ x‖ ^ 2) (μ.restrict Ω) := by
    refine (integrable_inner_of_memLp hf₀ hh).congr (Eventually.of_forall fun x ↦ ?_)
    simp only [inner_smul_right, real_inner_self_eq_norm_sq]
  have hlim := hconv _ hh
  rw [hA] at hlim
  -- `c i := 2 ∫ ⟨f_i, η f₀⟩ - A → A`
  have hc : Tendsto (fun i ↦ ENNReal.ofReal
      (2 * ∫ x in Ω, inner ℝ (f i x) (η x • f₀ x) ∂μ - A)) l (𝓝 (ENNReal.ofReal A)) := by
    refine ENNReal.tendsto_ofReal ?_
    have := (hlim.const_mul 2).sub_const A
    rwa [show 2 * A - A = A by ring] at this
  rw [← ofReal_integral_eq_lintegral_ofReal hAint
    (Eventually.of_forall fun x ↦ mul_nonneg (hη0 x) (sq_nonneg _)), ← hc.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun i ↦ ?_)
  have hint : Integrable (fun x ↦ 2 * inner ℝ (f i x) (η x • f₀ x) - η x * ‖f₀ x‖ ^ 2)
      (μ.restrict Ω) := ((integrable_inner_of_memLp (hfi i) hh).const_mul 2).sub hAint
  refine le_of_eq_of_le ?_ ((ofReal_integral_le_lintegral_ofReal hint).trans
    (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_))
  · rw [integral_sub ((integrable_inner_of_memLp (hfi i) hh).const_mul 2) hAint, integral_const_mul]
  · have h := mul_nonneg (hη0 x) (sq_nonneg ‖f i x - f₀ x‖)
    rw [norm_sub_sq_real] at h
    rw [inner_smul_right]
    linarith [h]

end EllipticBernoulli
