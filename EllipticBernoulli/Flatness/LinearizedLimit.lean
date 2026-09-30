/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Flatness.Linearized
public import EllipticBernoulli.Flatness.MovingCompactness
public import EllipticBernoulli.Flatness.TestCalculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Bases
import EllipticBernoulli.Common.Calculus
import EllipticBernoulli.Flatness.Barriers
import EllipticBernoulli.Flatness.Harnack
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Calculus
import EllipticBernoulli.Viscosity.Jet
import EllipticBernoulli.Viscosity.Stability

/-!
# Compactness: the linearized limit of flat solutions

De Silva (2011), Lemma 4.1, Steps 1–2.

The moving-domain Arzelà–Ascoli lemma `exists_subseq_tendsto_of_holder_upTo` is in
`EllipticBernoulli.Flatness.MovingCompactness`, and the test-function calculus in
`EllipticBernoulli.Flatness.TestCalculus`.

* `le_of_le_on_closure_posSet`: extension of a lower bound `φ ≤ u` from `closure {u > 0}` to a
  full ball, for test functions nondecreasing along the flatness direction. This fills a gap in
  De Silva (2011), Lemma 4.1, Step 2(ii): De Silva's test `Q_k⁺ ≤ u_k` is only known on
  `Ω(u_k)`, and the viscosity definition needs it on a full neighbourhood; De Silva never
  justifies the extension. It is also used in Step 3 to pass from `Ω_r(u_k)` to `B_r`.
* `linearized_limit`: Steps 1–2 of Lemma 4.1. For flat solutions `u k` with flatness `ε k → 0`
  in directions `e k → e₀`, the normalized functions `ũ_k = (u k - ⟪·, e k⟫)/ε k` on
  `closure {u k > 0} ∩ B_{1/2}` converge (along a subsequence, pointwise along convergent
  sequences) to a solution `w` of the linearized problem in direction `e₀`, with `|w| ≤ 1` and
  `w 0 = 0`. The directions are allowed to move so that no rotation invariance of the viscosity
  notion is needed in the contradiction argument of Lemma 4.1.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The zero phase -/

/-- **Lower bounds extend from `closure {u > 0}` across the zero phase** (a step missing from
De Silva (2011), Lemma 4.1, Step 2(ii)). Let `u ≥ 0` be continuous on `U ⊇ B_δ(x)`
and positive on `B_δ(x) ∩ {⟪·, e⟫ > a}` (flatness). Let `φ` be nondecreasing along `e` inside
`B_δ(x)`, and positive only above `{⟪·, e⟫ > -b}` on `B_{δ'}(x)`, where `δ' + a + b < δ`. If
`φ ≤ u` on `closure {u > 0} ∩ B_δ(x)`, then `φ ≤ u` on all of `B_{δ'}(x)`.

Proof: at a zero-phase point `y` with `φ y > 0`, move up along `e` to the first point `z` of
`closure {u > 0}`; it lies in `B_δ(x)` and has `u z = 0 < φ y ≤ φ z ≤ u z`. -/
theorem le_of_le_on_closure_posSet {U : Set (E d)} {u φ : E d → ℝ} {e x : E d} {δ δ' a b : ℝ}
    (he : ‖e‖ = 1) (hBU : ball x δ ⊆ U) (hcu : ContinuousOn u U) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : δ' + (a + b) < δ)
    (hpos : ∀ y ∈ ball x δ, a < ⟪y, e⟫ → 0 < u y)
    (hφb : ∀ y ∈ ball x δ', 0 < φ y → -b < ⟪y, e⟫)
    (hmono : ∀ y ∈ ball x δ, ∀ t : ℝ, 0 ≤ t → y + t • e ∈ ball x δ → φ y ≤ φ (y + t • e))
    (hle : ∀ y ∈ closure (posSet u U) ∩ ball x δ, φ y ≤ u y) :
    ∀ y ∈ ball x δ', φ y ≤ u y := by
  intro y hy
  have hdy : dist y x < δ' := hy
  have hyδ : y ∈ ball x δ := ball_subset_ball (by linarith) hy
  by_cases hcl : y ∈ closure (posSet u U)
  · exact hle y ⟨hcl, hyδ⟩
  by_contra hlt
  push Not at hlt
  have hφpos : 0 < φ y := lt_of_le_of_lt (hu0 y (hBU hyδ)) hlt
  have hyb : -b < ⟪y, e⟫ := hφb y hy hφpos
  have hball : ∀ t : ℝ, 0 ≤ t → t < δ - dist y x → y + t • e ∈ ball x δ := by
    intro t ht htδ
    rw [mem_ball]
    calc dist (y + t • e) x ≤ dist (y + t • e) y + dist y x := dist_triangle _ _ _
      _ = t + dist y x := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
          abs_of_nonneg ht]
      _ < δ := by linarith
  have hinner : ∀ t : ℝ, ⟪y + t • e, e⟫ = ⟪y, e⟫ + t := fun t ↦ by
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, he]; simp
  -- the first point of `closure {u > 0}` above `y`
  set t₁ := (a - ⟪y, e⟫ + (δ - dist y x)) / 2 with ht₁
  have ht₁a : a - ⟪y, e⟫ < t₁ := by rw [ht₁]; linarith
  have ht₁δ : t₁ < δ - dist y x := by rw [ht₁]; linarith
  have ht₁0 : 0 ≤ t₁ := by
    by_contra h
    push Not at h
    have hya : a < ⟪y, e⟫ := by linarith
    exact hcl (subset_closure ⟨hBU hyδ, hpos y hyδ hya⟩)
  set S := {t : ℝ | t ∈ Icc 0 t₁ ∧ y + t • e ∈ closure (posSet u U)} with hS
  have hSc : IsClosed S :=
    isClosed_Icc.inter (isClosed_closure.preimage (by fun_prop))
  have ht₁S : t₁ ∈ S := by
    refine ⟨⟨ht₁0, le_rfl⟩, subset_closure ⟨hBU (hball t₁ ht₁0 ht₁δ), ?_⟩⟩
    exact hpos _ (hball t₁ ht₁0 ht₁δ) (by rw [hinner]; linarith)
  have hSb : BddBelow S := ⟨0, fun t ht ↦ ht.1.1⟩
  set s := sInf S with hs
  have hsS : s ∈ S := hSc.csInf_mem ⟨t₁, ht₁S⟩ hSb
  have hs0 : 0 < s := by
    rcases hsS.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hcl; have := hsS.2; rwa [← h, zero_smul, add_zero] at this
  have hsδ : s < δ - dist y x := hsS.1.2.trans_lt ht₁δ
  set z := y + s • e with hz
  have hzδ : z ∈ ball x δ := hball s hs0.le hsδ
  -- `u = 0` on the open segment below `z`, hence `u z = 0`
  have hzero : ∀ t ∈ Ioo 0 s, u (y + t • e) ≤ 0 := by
    intro t ht
    by_contra h
    push Not at h
    have hmem : y + t • e ∈ closure (posSet u U) :=
      subset_closure ⟨hBU (hball t ht.1.le (ht.2.trans hsδ)), h⟩
    have : s ≤ t := csInf_le hSb ⟨⟨ht.1.le, ht.2.le.trans hsS.1.2⟩, hmem⟩
    linarith [ht.2]
  have hcz : ContinuousAt u z := hcu.continuousAt (mem_of_superset (isOpen_ball.mem_nhds hzδ) hBU)
  have htend : Tendsto (fun t : ℝ ↦ u (y + t • e)) (𝓝[<] s) (𝓝 (u z)) := by
    have hline : Continuous fun t : ℝ ↦ y + t • e := by fun_prop
    exact (hcz.tendsto.comp (hline.tendsto s)).mono_left nhdsWithin_le_nhds
  have huz : u z ≤ 0 := by
    refine le_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT hs0] with t ht using hzero t ht
  have hφz : φ y ≤ φ z := hmono y hyδ s hs0.le hzδ
  have := hle z ⟨hsS.2, hzδ⟩
  linarith

/-! ### Step 1: the normalized functions -/

/-- On `closure {u > 0} ∩ B_1`, an `ε`-flat `u` has `|u - ⟪·, e⟫| ≤ ε` and `⟪·, e⟫ ≥ -ε`
(De Silva's (4.4)). -/
theorem abs_normalized_le_one {U : Set (E d)} {u : E d → ℝ} {e y : E d} {ε : ℝ} (hε : 0 < ε)
    (hcu : ContinuousOn u U) (hB : ball (0 : E d) 1 ⊆ U)
    (hflat : ∀ z ∈ ball (0 : E d) 1, max (⟪z, e⟫ - ε) 0 ≤ u z ∧ u z ≤ max (⟪z, e⟫ + ε) 0)
    (hy : y ∈ closure (posSet u U) ∩ ball 0 1) :
    |(u y - ⟪y, e⟫) / ε| ≤ 1 ∧ -ε ≤ ⟪y, e⟫ := by
  have htrap : ∀ z ∈ ball (0 : E d) 1, max (⟪z, e⟫ + -ε) 0 ≤ u z ∧
      u z ≤ max (⟪z, e⟫ + ε) 0 := fun z hz ↦ by simpa [sub_eq_add_neg] using hflat z hz
  have h := trap_of_mem_closure_posSet hcu hB htrap hy
  have h0 : 0 ≤ u y := (le_max_right _ _).trans (hflat y hy.2).1
  refine ⟨?_, by linarith [h.2]⟩
  rw [abs_div, abs_of_pos hε, div_le_one hε, abs_le]
  constructor <;> linarith [h.1, h.2]

/-- **Hölder modulus of the normalized functions down to scale `ε`** (De Silva's (4.5), from
Corollary 3.2, here `flat_harnack_oscillation`). For an `ε`-flat solution on `B_1` with
`|Q - 1| ≤ ε²`, `ũ = (u - ⟪·, e⟫)/ε` satisfies
`|ũ x - ũ y| ≤ C |x - y|^γ + C (ε/ε̄)^γ` on `closure {u > 0} ∩ B_{1/2}`. Points closer than the
scale `δ = 2ε/ε̄` are compared through a third point `x + 3δ e` of `{u > 0}`. -/
theorem holder_upTo_of_flat (hd : 2 ≤ d) : ∃ εbar > 0, ∃ C > 0, ∃ γ ∈ Ioo (0 : ℝ) 1,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
    IsViscSolution U Q u → ‖e‖ = 1 → 0 < ε → (∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2) →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + ε) 0) →
    ε / εbar < 1 / 16 →
    ∀ x ∈ closure (posSet u U) ∩ ball 0 (1 / 2), ∀ y ∈ closure (posSet u U) ∩ ball 0 (1 / 2),
      |(u x - ⟪x, e⟫) / ε - (u y - ⟪y, e⟫) / ε| ≤ C * dist x y ^ γ + C * (ε / εbar) ^ γ := by
  obtain ⟨εH, hεH, CH, hCH, γ, hγ, H⟩ := flat_harnack_oscillation hd
  set εb := min εH (1 / 2) with hεb
  have hεb0 : 0 < εb := lt_min hεH (by norm_num)
  have hεbH : εb ≤ εH := min_le_left _ _
  have hεb2 : εb ≤ 1 / 2 := min_le_right _ _
  refine ⟨εb, hεb0, 16 * (4 * CH) + 4, by positivity, γ, hγ, ?_⟩
  intro U Q u e ε hU hB hu he hε hQ hflat hsmall x hx y hy
  set ũ : E d → ℝ := fun z ↦ (u z - ⟪z, e⟫) / ε with hũ
  change |ũ x - ũ y| ≤ _
  set δ := 2 * ε / εb with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ8 : δ < 1 / 8 := by
    have : δ = 2 * (ε / εb) := by rw [hδ]; ring
    rw [this]; linarith
  have hδε : 4 * ε ≤ δ := by
    rw [hδ, le_div_iff₀ hεb0]; linarith [mul_le_mul_of_nonneg_left hεb2 hε.le]
  have hsub : ∀ z ∈ ball (0 : E d) (1 / 2), ball z (1 / 2) ⊆ ball (0 : E d) 1 := by
    intro z hz w hw
    rw [mem_ball, dist_zero_right] at hz ⊢
    rw [mem_ball, dist_eq_norm] at hw
    calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
      _ < 1 := by linarith
  have htrap : ∀ z ∈ ball (0 : E d) 1, max (⟪z, e⟫ + -ε) 0 ≤ u z ∧
      u z ≤ max (⟪z, e⟫ + ε) 0 := fun z hz ↦ by simpa [sub_eq_add_neg] using hflat z hz
  have hbd : ∀ z ∈ closure (posSet u U) ∩ ball (0 : E d) 1, |ũ z| ≤ 1 ∧ -ε ≤ ⟪z, e⟫ :=
    fun z hz ↦ abs_normalized_le_one hε hu.1.1 hB hflat hz
  have hx1 : x ∈ closure (posSet u U) ∩ ball (0 : E d) 1 :=
    ⟨hx.1, ball_subset_ball (by norm_num) hx.2⟩
  have hy1 : y ∈ closure (posSet u U) ∩ ball (0 : E d) 1 :=
    ⟨hy.1, ball_subset_ball (by norm_num) hy.2⟩
  have h2γ : (2 : ℝ) ^ γ ≤ 2 := by
    calc (2 : ℝ) ^ γ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ.2.le
      _ = 2 := Real.rpow_one 2
  -- Corollary 3.2 at scales `≥ δ`
  have hosc : ∀ x₀ ∈ closure (posSet u U) ∩ ball (0 : E d) (1 / 2), ∀ z ∈ closure (posSet u U),
      δ ≤ ‖z - x₀‖ → ‖z - x₀‖ < 1 / 2 → |ũ z - ũ x₀| ≤ 4 * CH * ‖z - x₀‖ ^ γ := by
    intro x₀ hx₀ z hz hδz hz2
    have hB0 : ball x₀ (1 / 2) ⊆ U := (hsub x₀ hx₀.2).trans hB
    have hdist : 4 * ε * (1 / 2) / εH ≤ ‖z - x₀‖ := by
      refine le_trans ?_ hδz
      rw [hδ, div_le_div_iff₀ hεH hεb0]
      linarith [mul_le_mul_of_nonneg_left hεbH hε.le]
    have h := H U Q u e x₀ (1 / 2) (4 * ε) (-ε) ε hU hu he (by norm_num) hB0 (by positivity)
      (fun w hw ↦ (hQ w (hsub x₀ hx₀.2 hw)).trans (by linarith [sq_nonneg ε])) (by linarith)
      (by linarith)
      (fun w hw ↦ htrap w (hsub x₀ hx₀.2 hw)) hx₀.1 z
      ⟨hz, by rw [mem_ball, dist_eq_norm]; exact hz2⟩ hdist
    have ht : (‖z - x₀‖ / (1 / 2)) ^ γ ≤ 2 * ‖z - x₀‖ ^ γ := by
      rw [div_div_eq_mul_div, div_one, mul_comm, Real.mul_rpow (by norm_num) (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right h2γ (by positivity)
    have hdiff : ũ z - ũ x₀ = ((u z - ⟪z, e⟫) - (u x₀ - ⟪x₀, e⟫)) / ε := by
      simp only [hũ]; ring
    rw [hdiff, abs_div, abs_of_pos hε, div_le_iff₀ hε]
    calc _ ≤ CH * (4 * ε) * (1 / 2) * (‖z - x₀‖ / (1 / 2)) ^ γ := h
      _ ≤ CH * (4 * ε) * (1 / 2) * (2 * ‖z - x₀‖ ^ γ) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
      _ = 4 * CH * ‖z - x₀‖ ^ γ * ε := by ring
  set t := ‖x - y‖ with ht
  have hdxy : dist x y = t := dist_eq_norm x y
  rw [hdxy]
  have hC0 : 0 ≤ (16 * (4 * CH) + 4) * t ^ γ := by positivity
  have hC1 : 0 ≤ (16 * (4 * CH) + 4) * (ε / εb) ^ γ := by positivity
  rcases le_or_gt (1 / 2) t with hA | hA
  · -- far points
    have h1 : (1 / 2 : ℝ) ≤ t ^ γ := by
      calc (1 / 2 : ℝ) = (1 / 2) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (1 / 2) ^ γ := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hγ.2.le
        _ ≤ t ^ γ := Real.rpow_le_rpow (by norm_num) hA hγ.1.le
    have h2 : |ũ x - ũ y| ≤ 2 := by
      have := abs_sub (ũ x) (ũ y)
      linarith [(hbd x hx1).1, (hbd y hy1).1]
    have : (4 : ℝ) * t ^ γ ≤ (16 * (4 * CH) + 4) * t ^ γ :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  rcases le_or_gt δ t with hB' | hB'
  · -- intermediate scales
    have h := hosc x hx y hy.1 (by rw [norm_sub_rev]; exact hB') (by rw [norm_sub_rev]; exact hA)
    rw [abs_sub_comm, norm_sub_rev] at h
    have : 4 * CH * t ^ γ ≤ (16 * (4 * CH) + 4) * t ^ γ :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  · -- close points: compare through `z = x + 3δ e`
    set z := x + (3 * δ) • e with hz
    have hze : ‖z - x‖ = 3 * δ := by
      rw [hz, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    have hz1 : z ∈ ball (0 : E d) 1 := by
      rw [mem_ball, dist_zero_right]
      have := hx.2
      rw [mem_ball, dist_zero_right] at this
      calc ‖z‖ ≤ ‖x‖ + ‖z - x‖ := by
            calc ‖z‖ = ‖x + (z - x)‖ := by rw [add_sub_cancel]
              _ ≤ _ := norm_add_le _ _
        _ < 1 := by rw [hze]; linarith
    have hzpos : 0 < u z := by
      have h1 := (hflat z hz1).1
      have h2 : ⟪z, e⟫ = ⟪x, e⟫ + 3 * δ := by
        rw [hz, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, he]; simp
      have h3 := (hbd x hx1).2
      have : ⟪z, e⟫ - ε ≤ u z := (le_max_left _ _).trans h1
      linarith
    have hzcl : z ∈ closure (posSet u U) := subset_closure ⟨hB hz1, hzpos⟩
    have hzy : ‖z - y‖ = ‖(x - y) + (3 * δ) • e‖ := by rw [hz]; congr 1; abel
    have hzy1 : 2 * δ ≤ ‖z - y‖ := by
      have := norm_sub_norm_le ((3 * δ) • e) (-(x - y))
      rw [norm_neg, norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity),
        sub_neg_eq_add, add_comm] at this
      rw [hzy]; linarith
    have hzy2 : ‖z - y‖ ≤ 4 * δ := by
      rw [hzy]
      calc ‖(x - y) + (3 * δ) • e‖ ≤ ‖x - y‖ + ‖(3 * δ) • e‖ := norm_add_le _ _
        _ = t + 3 * δ := by
          rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
        _ ≤ 4 * δ := by linarith
    have h1 := hosc x hx z hzcl (by rw [hze]; linarith) (by rw [hze]; linarith)
    have h2 := hosc y hy z hzcl (by linarith) (by linarith)
    rw [hze] at h1
    have h4δ : (4 * δ) ^ γ ≤ 8 * (ε / εb) ^ γ := by
      have : 4 * δ = 8 * (ε / εb) := by rw [hδ]; ring
      rw [this, Real.mul_rpow (by norm_num) (by positivity)]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc (8 : ℝ) ^ γ ≤ 8 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ.2.le
        _ = 8 := Real.rpow_one 8
    have h3 : (3 * δ) ^ γ ≤ (4 * δ) ^ γ := Real.rpow_le_rpow (by positivity) (by linarith) hγ.1.le
    have h5 : ‖z - y‖ ^ γ ≤ (4 * δ) ^ γ := Real.rpow_le_rpow (norm_nonneg _) hzy2 hγ.1.le
    have hsum : |ũ x - ũ y| ≤ |ũ z - ũ x| + |ũ z - ũ y| := by
      rw [abs_sub_comm (ũ z) (ũ x)]; exact abs_sub_le _ _ _
    have hCH : 0 ≤ 4 * CH := by positivity
    have : |ũ x - ũ y| ≤ 16 * (4 * CH) * (ε / εb) ^ γ := by
      calc |ũ x - ũ y| ≤ 4 * CH * (3 * δ) ^ γ + 4 * CH * ‖z - y‖ ^ γ := by linarith
        _ ≤ 4 * CH * (4 * δ) ^ γ + 4 * CH * (4 * δ) ^ γ :=
          add_le_add (mul_le_mul_of_nonneg_left h3 hCH) (mul_le_mul_of_nonneg_left h5 hCH)
        _ ≤ 4 * CH * (8 * (ε / εb) ^ γ) + 4 * CH * (8 * (ε / εb) ^ γ) :=
          add_le_add (mul_le_mul_of_nonneg_left h4δ hCH) (mul_le_mul_of_nonneg_left h4δ hCH)
        _ = 16 * (4 * CH) * (ε / εb) ^ γ := by ring
    have : 16 * (4 * CH) * (ε / εb) ^ γ ≤ (16 * (4 * CH) + 4) * (ε / εb) ^ γ :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith

/-! ### Step 2: touching points along the sequence -/

/-- **Touching points along the sequence** (De Silva's (4.7)–(4.8)). Let `f k → g` on `K` in the
pointwise sense of `exists_subseq_tendsto_of_holder_upTo`, and let `P` (continuous) touch `g`
strictly from below at `x ∈ K` relative to `K ∩ B̄_r(x)`. If the sets `D k ∩ B̄_r(x)` are compact,
`f k` continuous there, `x` is a limit of points of `D k`, and limits of points of `D k` inside
`B̄_r(x)` lie in `K`, then the minimum points `x_k` of `f k - P` over `D k ∩ B̄_r(x)` converge to
`x`, with `f k (x_k) = P(x_k) + c_k`, `c_k → 0` and `P + c_k ≤ f k` on `D k ∩ B̄_r(x)`. -/
theorem exists_touch_seq {D : ℕ → Set (E d)} {K : Set (E d)} {f : ℕ → E d → ℝ}
    {g P : E d → ℝ} {x : E d} {r : ℝ} (hr : 0 < r)
    (hDc : ∀ k, IsCompact (D k ∩ closedBall x r))
    (hfc : ∀ k, ContinuousOn (f k) (D k ∩ closedBall x r)) (hPc : Continuous P)
    (hconv : ∀ z ∈ K, ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∀ y : ℕ → E d,
      (∀ᶠ k in atTop, y k ∈ D (ψ k)) → Tendsto y atTop (𝓝 z) →
        Tendsto (fun k ↦ f (ψ k) (y k)) atTop (𝓝 (g z)))
    (hK : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ y : ℕ → E d, (∀ᶠ k in atTop, y k ∈ D (ψ k)) →
      ∀ z ∈ closedBall x r, Tendsto y atTop (𝓝 z) → z ∈ K)
    (ha : ∃ a : ℕ → E d, (∀ᶠ k in atTop, a k ∈ D k) ∧ Tendsto a atTop (𝓝 x))
    (hxK : x ∈ K) (hPx : P x = g x) (hstrict : ∀ z ∈ K ∩ closedBall x r, z ≠ x → P z < g z) :
    ∃ xs : ℕ → E d, ∃ c : ℕ → ℝ, Tendsto xs atTop (𝓝 x) ∧ Tendsto c atTop (𝓝 0) ∧
      ∀ᶠ k in atTop, xs k ∈ D k ∧ f k (xs k) = P (xs k) + c k ∧
        ∀ y ∈ D k ∩ closedBall x r, P y + c k ≤ f k y := by
  classical
  obtain ⟨a, haD, hax⟩ := ha
  have haB : ∀ᶠ k in atTop, a k ∈ closedBall x r := hax.eventually (closedBall_mem_nhds x hr)
  have hmin : ∀ k, ∃ z, (D k ∩ closedBall x r).Nonempty → z ∈ D k ∩ closedBall x r ∧
      IsMinOn (fun y ↦ f k y - P y) (D k ∩ closedBall x r) z := by
    intro k
    by_cases h : (D k ∩ closedBall x r).Nonempty
    · obtain ⟨z, hz, hmin⟩ := (hDc k).exists_isMinOn h ((hfc k).sub hPc.continuousOn)
      exact ⟨z, fun _ ↦ ⟨hz, hmin⟩⟩
    · exact ⟨x, fun h' ↦ absurd h' h⟩
  choose xs hxs using hmin
  set c : ℕ → ℝ := fun k ↦ f k (xs k) - P (xs k) with hc
  have hxsD : ∀ᶠ k in atTop, xs k ∈ D k ∩ closedBall x r ∧
      IsMinOn (fun y ↦ f k y - P y) (D k ∩ closedBall x r) (xs k) := by
    filter_upwards [haD, haB] with k h1 h2 using hxs k ⟨a k, h1, h2⟩
  have hcle : ∀ᶠ k in atTop, c k ≤ f k (a k) - P (a k) := by
    filter_upwards [hxsD, haD, haB] with k h1 h2 h3 using h1.2 ⟨h2, h3⟩
  have hfa : Tendsto (fun k ↦ f k (a k) - P (a k)) atTop (𝓝 0) := by
    have := (hconv x hxK id tendsto_id a haD hax).sub ((hPc.tendsto x).comp hax)
    simpa [hPx] using this
  have hxsx : Tendsto xs atTop (𝓝 x) := by
    rw [Metric.tendsto_nhds]
    intro ρ hρ
    by_contra hcon
    rw [Filter.not_eventually] at hcon
    have hfreq : ∃ᶠ k in atTop, xs k ∈ closedBall x r \ ball x ρ :=
      (hcon.and_eventually hxsD).mono fun k ⟨h1, h2⟩ ↦ ⟨h2.1.2, fun h ↦ h1 (mem_ball.1 h)⟩
    obtain ⟨z, hz, ψ, hψ, hψz⟩ :=
      ((isCompact_closedBall x r).diff isOpen_ball).tendsto_subseq' hfreq
    have hψt := hψ.tendsto_atTop
    have hyD : ∀ᶠ k in atTop, (xs ∘ ψ) k ∈ D (ψ k) :=
      hψt.eventually (hxsD.mono fun k h ↦ h.1.1)
    have hzK : z ∈ K := hK ψ hψ (xs ∘ ψ) hyD z hz.1 hψz
    have hzx : z ≠ x := fun h ↦ hz.2 (h ▸ mem_ball_self hρ)
    have h1 : Tendsto (fun k ↦ c (ψ k)) atTop (𝓝 (g z - P z)) :=
      (hconv z hzK ψ hψt (xs ∘ ψ) hyD hψz).sub ((hPc.tendsto z).comp hψz)
    have h2 : g z - P z ≤ 0 :=
      le_of_tendsto_of_tendsto h1 (hfa.comp hψt) (hψt.eventually hcle)
    linarith [hstrict z ⟨hzK, hz.1⟩ hzx]
  have hcx : Tendsto c atTop (𝓝 0) := by
    have := (hconv x hxK id tendsto_id xs (hxsD.mono fun k h ↦ h.1.1) hxsx).sub
      ((hPc.tendsto x).comp hxsx)
    simpa [hPx] using this
  refine ⟨xs, c, hxsx, hcx, hxsD.mono fun k h ↦ ⟨h.1.1, by simp [hc], fun y hy ↦ ?_⟩⟩
  have := h.2 hy
  simp only [mem_ofPred_eq] at this
  simp only [hc]
  linarith

/-! ### Testing a single flat solution -/

/-- **Test from below at a point of `closure {u > 0}`** (De Silva (2011), Lemma 4.1, Step 2, with
the zero-phase extension `le_of_le_on_closure_posSet`). Let `u` be a viscosity solution in `U`,
positive on `B_ρ(z) ∩ {⟪·, e⟫ > ε}`, and let `Φ = ⟪·, e⟫ + ε (P + c)`, `P` smooth, touch `u`
from below at `z` relative to `closure {u > 0} ∩ B_ρ(z)`. If `ε` is small against `ρ`, a bound
`B` of `|P + c|` and a Lipschitz constant `L` of `P` on `B_ρ(z)`, then `ε ΔP(z) ≤ 0`, or
`u z = 0` and `|e + ε ∇P(z)| ≤ Q(z)`. -/
theorem super_touch_test {U : Set (E d)} {Q u P : E d → ℝ} {e z : E d} {ε c ρ B : ℝ}
    {L : NNReal} (hu : IsViscSolution U Q u) (he : ‖e‖ = 1) (hε : 0 < ε) (hρ : 0 < ρ)
    (hBU : ball z ρ ⊆ U) (hpos : ∀ y ∈ ball z ρ, ε < ⟪y, e⟫ → 0 < u y) (hP : ContDiff ℝ ∞ P)
    (hPB : ∀ y ∈ ball z ρ, |P y + c| ≤ B) (hPL : LipschitzOnWith L P (ball z ρ))
    (hεL : ε * L ≤ 1) (hsmall : ε + ε * B < ρ / 2) (hzeq : u z = ⟪z, e⟫ + ε * (P z + c))
    (hle : ∀ y ∈ closure (posSet u U) ∩ ball z ρ, ⟪y, e⟫ + ε * (P y + c) ≤ u y) :
    ε * Δ P z ≤ 0 ∨ (u z = 0 ∧ ‖e + ε • ∇ P z‖ ≤ Q z) := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hPB z (mem_ball_self hρ))
  set Φ : E d → ℝ := fun y ↦ 1 * ⟪y, e⟫ + ε * c + ε * P y with hΦdef
  have hΦ : ∀ y, Φ y = ⟪y, e⟫ + ε * (P y + c) := fun y ↦ by simp only [hΦdef]; ring
  have hinner : ∀ (y : E d) (t : ℝ), ⟪y + t • e, e⟫ = ⟪y, e⟫ + t := fun y t ↦ by
    rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, he]; simp
  have hext := le_of_le_on_closure_posSet (U := U) (u := u) (φ := Φ) (e := e) (x := z) (δ := ρ)
    (δ' := ρ / 2) (a := ε) (b := ε * B) he hBU hu.1.1 hu.1.2.1 hε.le (by positivity)
    (by linarith) hpos
    (fun y hy hy0 ↦ by
      rw [hΦ] at hy0
      have := (abs_le.1 (hPB y (ball_subset_ball (by linarith) hy))).2
      linarith [mul_le_mul_of_nonneg_left this hε.le])
    (fun y hy t ht hyt ↦ by
      rw [hΦ, hΦ, hinner]
      have h1 := hPL.dist_le_mul (y + t • e) hyt y hy
      rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left, norm_smul, he, mul_one,
        Real.norm_eq_abs, abs_of_nonneg ht] at h1
      have h2 := (abs_le.1 h1).1
      have h3 : ε * (↑L * t) ≤ t := by rw [← mul_assoc]; exact mul_le_of_le_one_left ht hεL
      linarith [mul_le_mul_of_nonneg_left h2 hε.le])
    (fun y hy ↦ by rw [hΦ]; exact hle y hy)
  have hzU : z ∈ U := hBU (mem_ball_self hρ)
  have htouch : TouchesBelow Φ u U z := by
    refine ⟨hzU, by rw [hΦ, hzeq], ?_⟩
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (half_pos hρ))] with y hy using hext y hy
  have hΦs : ContDiff ℝ ∞ Φ := ((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).add
    contDiff_const).add (contDiff_const.mul hP)
  have hlap : Δ Φ z = ε * Δ P z := laplacian_mul_inner_add_mul (contDiff_two_of_smooth hP) e 1
    (ε * c) ε z
  have hgrad : ∇ Φ z = e + ε • ∇ P z := by
    have h := hasGradientAt_mul_inner_add_mul
      (((hP.differentiable (by simp)) z).hasGradientAt) 1 (ε * c) ε (e := e)
    rw [h.gradient, one_smul]
  rcases hu.1.2.2 Φ hΦs z hzU htouch with h | ⟨h1, h2⟩
  · exact Or.inl (hlap ▸ h)
  · refine Or.inr ⟨?_, hgrad ▸ h2⟩
    rw [← htouch.2.1]; exact h1

/-- **Test from above at a point of `closure {u > 0}`** (De Silva (2011), Lemma 4.1, Step 2): if
`Φ = ⟪·, e⟫ + ε (P + c)` touches `u` from above at `z ∈ closure {u > 0}` relative to
`closure {u > 0} ∩ B_ρ(z)`, then `0 ≤ ε ΔP(z)`, or `u z = 0` and `Q(z) ≤ |e + ε ∇P(z)|`. No
zero-phase argument is needed: the subsolution test of `IsViscSub` is relative to
`closure {u > 0}`. -/
theorem sub_touch_test {U : Set (E d)} {Q u P : E d → ℝ} {e z : E d} {ε c ρ : ℝ}
    (hu : IsViscSolution U Q u) (hρ : 0 < ρ) (hBU : ball z ρ ⊆ U) (hP : ContDiff ℝ ∞ P)
    (hz : z ∈ closure (posSet u U)) (hzeq : u z = ⟪z, e⟫ + ε * (P z + c))
    (hle : ∀ y ∈ closure (posSet u U) ∩ ball z ρ, u y ≤ ⟪y, e⟫ + ε * (P y + c)) :
    0 ≤ ε * Δ P z ∨ (u z = 0 ∧ Q z ≤ ‖e + ε • ∇ P z‖) := by
  set Φ : E d → ℝ := fun y ↦ 1 * ⟪y, e⟫ + ε * c + ε * P y with hΦdef
  have hΦ : ∀ y, Φ y = ⟪y, e⟫ + ε * (P y + c) := fun y ↦ by simp only [hΦdef]; ring
  have hzU : z ∈ U := hBU (mem_ball_self hρ)
  have hu0 : 0 ≤ u z := hu.1.2.1 z hzU
  have htouch : TouchesAbove (fun y ↦ max (Φ y) 0) u (closure (posSet u U) ∩ U) z := by
    refine ⟨⟨hz, hzU⟩, by change max (Φ z) 0 = u z; rw [hΦ, ← hzeq, max_eq_left hu0], ?_⟩
    filter_upwards [inter_mem_nhdsWithin _ (isOpen_ball.mem_nhds (mem_ball_self hρ)),
      self_mem_nhdsWithin] with y hy hy'
    rw [hΦ]
    exact (hle y ⟨hy'.1, hy.2⟩).trans (le_max_left _ _)
  have hΦs : ContDiff ℝ ∞ Φ := ((contDiff_const.mul (contDiff_id.inner ℝ contDiff_const)).add
    contDiff_const).add (contDiff_const.mul hP)
  have hlap : Δ Φ z = ε * Δ P z := laplacian_mul_inner_add_mul (contDiff_two_of_smooth hP) e 1
    (ε * c) ε z
  have hgrad : ∇ Φ z = e + ε • ∇ P z := by
    have h := hasGradientAt_mul_inner_add_mul
      (((hP.differentiable (by simp)) z).hasGradientAt) 1 (ε * c) ε (e := e)
    rw [h.gradient, one_smul]
  rcases hu.2.2.2 Φ hΦs z htouch with h | ⟨h1, h2⟩
  · exact Or.inl (hlap ▸ h)
  · refine Or.inr ⟨?_, hgrad ▸ h2⟩
    rw [hzeq, ← hΦ]; exact h1

/-! ### Steps 1–2 of Lemma 4.1 -/

/-- **The linearized limit** (De Silva (2011), Lemma 4.1, Steps 1–2). Let `u k` be viscosity
solutions in `U k ⊇ B_1` with coefficients `Q k`, `0 ∈ F(u k)`, `|Q k - 1| ≤ (ε k)²` on `B_1`, and
`(⟪y, e k⟫ - ε k)₊ ≤ u k ≤ (⟪y, e k⟫ + ε k)₊` on `B_1`, where `ε k → 0`, `ε k > 0`, and the unit
directions `e k → e₀`. Then along a subsequence `φ` the functions
`ũ_k = (u k - ⟪·, e k⟫)/ε k` on `closure {u k > 0} ∩ B_{1/2}` converge, pointwise along
convergent sequences (also along further subsequences `ψ`), to a solution `w` of the linearized
problem in direction `e₀` on `B_{1/2}` with `|w| ≤ 1` on `halfBall e₀ (1/2)` and `w 0 = 0`. -/
theorem linearized_limit (hd : 2 ≤ d) {U : ℕ → Set (E d)} {Q u : ℕ → E d → ℝ} {e : ℕ → E d}
    {ε : ℕ → ℝ} {e₀ : E d} (hU : ∀ k, IsOpen (U k)) (hB : ∀ k, ball (0 : E d) 1 ⊆ U k)
    (hu : ∀ k, IsViscSolution (U k) (Q k) (u k)) (h0 : ∀ k, (0 : E d) ∈ freeBoundary (u k) (U k))
    (he : ∀ k, ‖e k‖ = 1) (he₀ : Tendsto e atTop (𝓝 e₀)) (hε : ∀ k, 0 < ε k)
    (hε₀ : Tendsto ε atTop (𝓝 0)) (hQ : ∀ k, ∀ y ∈ ball (0 : E d) 1, |Q k y - 1| ≤ ε k ^ 2)
    (hflat : ∀ k, ∀ y ∈ ball (0 : E d) 1,
      max (⟪y, e k⟫ - ε k) 0 ≤ u k y ∧ u k y ≤ max (⟪y, e k⟫ + ε k) 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : E d → ℝ, IsLinearizedSolution w e₀ (1 / 2) ∧
      (∀ x ∈ halfBall e₀ (1 / 2), |w x| ≤ 1) ∧ w 0 = 0 ∧
      ∀ x ∈ halfBall e₀ (1 / 2), ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∀ y : ℕ → E d,
        (∀ᶠ k in atTop, y k ∈ closure (posSet (u (φ (ψ k))) (U (φ (ψ k)))) ∩ ball 0 (1 / 2)) →
        Tendsto y atTop (𝓝 x) →
          Tendsto (fun k ↦ (u (φ (ψ k)) (y k) - ⟪y k, e (φ (ψ k))⟫) / ε (φ (ψ k))) atTop
            (𝓝 (w x)) := by
  obtain ⟨εb, hεb, CO, hCO, γ, hγ, HO⟩ := holder_upTo_of_flat hd
  have he₀1 : ‖e₀‖ = 1 := by
    have h := he₀.norm
    have hc : (fun k ↦ ‖e k‖) = fun _ ↦ (1 : ℝ) := funext he
    rw [hc] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hB2 : ∀ k, ball (0 : E d) (1 / 2) ⊆ U k := fun k ↦
    (ball_subset_ball (by norm_num)).trans (hB k)
  set D : ℕ → Set (E d) := fun k ↦ closure (posSet (u k) (U k)) ∩ ball 0 (1 / 2) with hD
  set f : ℕ → E d → ℝ := fun k y ↦ (u k y - ⟪y, e k⟫) / ε k with hf
  set K := halfBall e₀ (1 / 2) with hK
  have hD1 : ∀ k, ∀ y ∈ D k, y ∈ closure (posSet (u k) (U k)) ∩ ball (0 : E d) 1 :=
    fun k y hy ↦ ⟨hy.1, ball_subset_ball (by norm_num) hy.2⟩
  have hbd : ∀ k, ∀ y ∈ D k, |f k y| ≤ 1 := fun k y hy ↦
    (abs_normalized_le_one (hε k) (hu k).1.1 (hB k) (hflat k) (hD1 k y hy)).1
  have hlow : ∀ k, ∀ y ∈ D k, -ε k ≤ ⟪y, e k⟫ := fun k y hy ↦
    (abs_normalized_le_one (hε k) (hu k).1.1 (hB k) (hflat k) (hD1 k y hy)).2
  -- approximants of points of the half-ball
  have happrox : ∀ x ∈ K, ∃ a : ℕ → E d, (∀ᶠ k in atTop, a k ∈ D k) ∧
      Tendsto a atTop (𝓝 x) := by
    intro x hx
    have hconv : Tendsto (fun k ↦ x + (2 * ε k + ‖e k - e₀‖) • e k) atTop (𝓝 x) := by
      have := tendsto_const_nhds (x := x) |>.add
        (((hε₀.const_mul 2).add (he₀.sub_const e₀).norm).smul he₀)
      simpa using this
    refine ⟨_, ?_, hconv⟩
    filter_upwards [hconv.eventually (isOpen_ball.mem_nhds hx.2)] with k hk
    have hk1 : x + (2 * ε k + ‖e k - e₀‖) • e k ∈ ball (0 : E d) 1 :=
      ball_subset_ball (by norm_num) hk
    refine ⟨subset_closure ⟨hB k hk1, ?_⟩, hk⟩
    have h1 := (hflat k _ hk1).1
    have hx1 : ‖x‖ ≤ 1 := by
      have := hx.2; rw [mem_ball, dist_zero_right] at this; linarith
    have h2 : -‖e k - e₀‖ ≤ ⟪x, e k⟫ := by
      have h3 : ⟪x, e k⟫ = ⟪x, e₀⟫ + ⟪x, e k - e₀⟫ := by rw [inner_sub_right]; ring
      have h4 := abs_real_inner_le_norm x (e k - e₀)
      have h5 : ‖x‖ * ‖e k - e₀‖ ≤ ‖e k - e₀‖ := by
        exact mul_le_of_le_one_left (norm_nonneg _) hx1
      have h7 : 0 ≤ ⟪x, e₀⟫ := hx.1
      rw [h3]; linarith [(abs_le.1 h4).1]
    have h6 : ⟪x + (2 * ε k + ‖e k - e₀‖) • e k, e k⟫ = ⟪x, e k⟫ + (2 * ε k + ‖e k - e₀‖) := by
      rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, he k]; simp
    have h7 := hε k
    have : 0 < ⟪x + (2 * ε k + ‖e k - e₀‖) • e k, e k⟫ - ε k := by rw [h6]; linarith
    exact this.trans_le ((le_max_left _ _).trans h1)
  -- the modulus
  set η : ℕ → ℝ := fun k ↦ CO * (ε k / εb) ^ γ with hη
  have hηt : Tendsto η atTop (𝓝 0) := by
    have := ((hε₀.div_const εb).rpow_const (Or.inr hγ.1.le)).const_mul CO
    simpa [Real.zero_rpow hγ.1.ne'] using this
  have hmod : ∀ᶠ k in atTop, ∀ x ∈ D k, ∀ y ∈ D k, |f k x - f k y| ≤ CO * dist x y ^ γ + η k := by
    have : ∀ᶠ k in atTop, ε k / εb < 1 / 16 := by
      have := (hε₀.div_const εb)
      rw [zero_div] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [this] with k hk
    exact HO (U k) (Q k) (u k) (e k) (ε k) (hU k) (hB k) (hu k) (he k) (hε k) (hQ k) (hflat k) hk
  obtain ⟨φ, hφ, w, hwb, hwH, hconv⟩ := exists_subseq_tendsto_of_holder_upTo (X := E d) (D := D)
    (K := K) (f := f) (M := 1) hγ.1 hbd happrox hηt hmod
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- `u k 0 = 0`
  have hu00 : ∀ k, u k 0 = 0 := by
    intro k
    have hopen : IsOpen (posSet (u k) (U k)) := (hu k).1.1.isOpen_inter_preimage (hU k) isOpen_Ioi
    have hnot : ¬ 0 < u k 0 := fun h ↦ by
      have := (h0 k).1
      rw [hopen.frontier_eq] at this
      exact this.2 ⟨(h0 k).2, h⟩
    exact le_antisymm (not_lt.1 hnot) ((hu k).1.2.1 0 (h0 k).2)
  have h0K : (0 : E d) ∈ K := ⟨by simp, mem_ball_self (by norm_num)⟩
  have h0D : ∀ k, (0 : E d) ∈ D k := fun k ↦
    ⟨frontier_subset_closure (h0 k).1, mem_ball_self (by norm_num)⟩
  have hw0 : w 0 = 0 := by
    have h := hconv 0 h0K id tendsto_id (fun _ ↦ 0) (Eventually.of_forall fun k ↦ h0D _)
      tendsto_const_nhds
    have hc : (fun k ↦ f (φ (id k)) ((fun _ : ℕ ↦ (0 : E d)) k)) = fun _ ↦ 0 := by
      funext k; simp [hf, hu00]
    rw [hc] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  -- continuity of `w`
  have hwc : ContinuousOn w K := by
    rw [Metric.continuousOn_iff]
    intro b hb δ hδ
    obtain ⟨ρ, hρ, h⟩ := exists_pos_mul_rpow_lt (C := CO) hγ.1 hδ
    refine ⟨ρ, hρ, fun a ha hab ↦ ?_⟩
    rw [Real.dist_eq]
    exact (hwH a ha b hb).trans_lt (h _ dist_nonneg hab)
  -- common facts for the touching argument
  have hK_lim : ∀ x : E d, ∀ r : ℝ, closedBall x r ⊆ ball (0 : E d) (1 / 2) →
      ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ y : ℕ → E d, (∀ᶠ k in atTop, y k ∈ D (φ (ψ k))) →
        ∀ z ∈ closedBall x r, Tendsto y atTop (𝓝 z) → z ∈ K := by
    intro x r hrB ψ hψ y hy z hz hyz
    refine ⟨?_, hrB hz⟩
    have hφψ : Tendsto (fun k ↦ φ (ψ k)) atTop atTop := hφt.comp hψ.tendsto_atTop
    have h1 : Tendsto (fun k ↦ ⟪y k, e (φ (ψ k))⟫) atTop (𝓝 ⟪z, e₀⟫) :=
      hyz.inner (he₀.comp hφψ)
    have h2 : Tendsto (fun k ↦ -ε (φ (ψ k))) atTop (𝓝 0) := by
      simpa using (hε₀.comp hφψ).neg
    exact le_of_tendsto_of_tendsto h2 h1 (hy.mono fun k hk ↦ hlow _ _ hk)
  have hDc : ∀ x : E d, ∀ r : ℝ, closedBall x r ⊆ ball (0 : E d) (1 / 2) → ∀ k,
      IsCompact (D k ∩ closedBall x r) := by
    intro x r hrB k
    have : D k ∩ closedBall x r = closure (posSet (u k) (U k)) ∩ closedBall x r := by
      ext y; exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hrB h.2⟩, h.2⟩⟩
    rw [this]
    exact (isCompact_closedBall x r).inter_left isClosed_closure
  have hfc : ∀ x : E d, ∀ r : ℝ, closedBall x r ⊆ ball (0 : E d) (1 / 2) → ∀ k,
      ContinuousOn (f k) (D k ∩ closedBall x r) := by
    intro x r hrB k
    have hc : ContinuousOn (u k) (D k ∩ closedBall x r) :=
      (hu k).1.1.mono fun y hy ↦ hB2 k hy.1.2
    exact (hc.sub (continuous_id.inner continuous_const).continuousOn).div_const _
  have happroxφ : ∀ x ∈ K, ∃ a : ℕ → E d, (∀ᶠ k in atTop, a k ∈ D (φ k)) ∧
      Tendsto a atTop (𝓝 x) := by
    intro x hx
    obtain ⟨a, haD, hax⟩ := happrox x hx
    exact ⟨a ∘ φ, hφt.eventually haD, hax.comp hφt⟩
  have hball_sub : ∀ x : E d, ∀ r : ℝ, ∀ z ∈ ball x (r / 2), ball z (r / 2) ⊆ closedBall x r := by
    intro x r z hz y hy
    rw [mem_closedBall]; rw [mem_ball] at hy hz
    linarith [dist_triangle y z x]
  have hin_ball1 : ∀ x : E d, ∀ r : ℝ, closedBall x r ⊆ ball (0 : E d) (1 / 2) →
      ∀ z ∈ closedBall x r, z ∈ ball (0 : E d) 1 :=
    fun x r hrB z hz ↦ ball_subset_ball (by norm_num) (hrB hz)
  have hposk : ∀ k, ∀ y ∈ ball (0 : E d) 1, ε k < ⟪y, e k⟫ → 0 < u k y := by
    intro k y hy h
    have := (hflat k y hy).1
    have : ⟪y, e k⟫ - ε k ≤ u k y := (le_max_left _ _).trans this
    linarith
  have hinner_lim : ∀ (xs : ℕ → E d) (x : E d), Tendsto xs atTop (𝓝 x) → 0 < ⟪x, e₀⟫ →
      ∀ᶠ k in atTop, ε (φ k) < ⟪xs k, e (φ k)⟫ := by
    intro xs x hxs hx0
    have h1 : Tendsto (fun k ↦ ⟪xs k, e (φ k)⟫ - ε (φ k)) atTop (𝓝 (⟪x, e₀⟫ - 0)) :=
      (hxs.inner (he₀.comp hφt)).sub (hε₀.comp hφt)
    rw [sub_zero] at h1
    filter_upwards [h1.eventually (lt_mem_nhds hx0)] with k hk
    linarith
  have hεφ : Tendsto (fun k ↦ ε (φ k)) atTop (𝓝 0) := hε₀.comp hφt
  -- Step 2, from below
  have core_below : ∀ P : E d → ℝ, ContDiff ℝ ∞ P → ∀ x ∈ K, ∀ r > 0,
      closedBall x r ⊆ ball (0 : E d) (1 / 2) → P x = w x →
      (∀ z ∈ K ∩ closedBall x r, z ≠ x → P z < w z) →
      (0 < ⟪x, e₀⟫ → Δ P x ≤ 0) ∧ (⟪x, e₀⟫ = 0 → 0 < Δ P x → ⟪∇ P x, e₀⟫ ≤ 0) := by
    intro P hP x hx r hr hrB hPx hstrict
    obtain ⟨xs, c, hxs, hc, hev⟩ := exists_touch_seq (D := fun k ↦ D (φ k)) (K := K)
      (f := fun k ↦ f (φ k)) (g := w) (P := P) hr (fun k ↦ hDc x r hrB (φ k))
      (fun k ↦ hfc x r hrB (φ k)) hP.continuous hconv (hK_lim x r hrB) (happroxφ x hx) hx hPx
      hstrict
    have hP1 : ContDiff ℝ 1 P := (contDiff_two_of_smooth hP).of_le one_le_two
    obtain ⟨Bnd, hBnd⟩ :=
      (isCompact_closedBall x r).exists_bound_of_continuousOn hP.continuous.continuousOn
    obtain ⟨L, hL⟩ := hP1.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall x r)
    have hBnd0 : 0 ≤ Bnd := (norm_nonneg _).trans (hBnd x (mem_closedBall_self hr.le))
    have hL1 : ∀ᶠ k in atTop, ε (φ k) * L < 1 := by
      have := hεφ.mul_const (L : ℝ)
      rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds one_pos)
    have hsm : ∀ᶠ k in atTop, ε (φ k) * (Bnd + 2) < r / 4 := by
      have := hεφ.mul_const (Bnd + 2)
      rw [zero_mul] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    have hxs2 : ∀ᶠ k in atTop, xs k ∈ ball x (r / 2) :=
      hxs.eventually (ball_mem_nhds x (half_pos hr))
    have hc1 : ∀ᶠ k in atTop, |c k| ≤ 1 := by
      filter_upwards [hc.eventually (Metric.ball_mem_nhds 0 one_pos)] with k hk
      rw [Real.dist_eq, sub_zero] at hk
      exact hk.le
    have htest : ∀ᶠ k in atTop, ε (φ k) * Δ P (xs k) ≤ 0 ∨
        (u (φ k) (xs k) = 0 ∧ ‖e (φ k) + ε (φ k) • ∇ P (xs k)‖ ≤ Q (φ k) (xs k)) := by
      filter_upwards [hev, hL1, hsm, hxs2, hc1] with k hk hkL hks hkx hkc
      obtain ⟨hkD, hkeq, hkle⟩ := hk
      have hball := hball_sub x r (xs k) hkx
      have hεk := hε (φ k)
      refine super_touch_test (B := Bnd + 1) (c := c k) (hu (φ k)) (he (φ k)) hεk (half_pos hr)
        (fun y hy ↦ hB2 _ (hrB (hball hy)))
        (fun y hy hy' ↦ hposk _ y (hin_ball1 x r hrB y (hball hy)) hy') hP
        (fun y hy ↦ ?_) (hL.mono hball) hkL.le (by linarith) ?_ (fun y hy ↦ ?_)
      · have h1 := hBnd y (hball hy)
        rw [Real.norm_eq_abs] at h1
        exact (abs_add_le _ _).trans (by linarith)
      · have h := hkeq
        simp only [hf] at h
        rw [div_eq_iff hεk.ne'] at h
        linarith
      · have h := hkle y ⟨⟨hy.1, hrB (hball hy.2)⟩, hball hy.2⟩
        simp only [hf] at h
        rw [le_div_iff₀ hεk] at h
        linarith
    have hxs1 : ∀ᶠ k in atTop, xs k ∈ ball (0 : E d) 1 := by
      filter_upwards [hxs2] with k hk using hin_ball1 x r hrB _ (hball_sub x r (xs k) hk
        (mem_ball_self (half_pos hr)))
    refine ⟨fun hx0 ↦ ?_, fun hx0 hΔ ↦ ?_⟩
    · have hΔk : ∀ᶠ k in atTop, Δ P (xs k) ≤ 0 := by
        filter_upwards [htest, hinner_lim xs x hxs hx0, hxs1] with k hk hk' hk1
        rcases hk with h | ⟨h, -⟩
        · exact le_of_mul_le_mul_left (by linarith) (hε (φ k))
        · exact absurd h (hposk _ _ hk1 hk').ne'
      exact le_of_tendsto (((continuous_laplacian (contDiff_two_of_smooth hP)).tendsto x).comp
        hxs) hΔk
    · have hpos : ∀ᶠ k in atTop, 0 < Δ P (xs k) :=
        (((continuous_laplacian (contDiff_two_of_smooth hP)).tendsto x).comp hxs).eventually
          (lt_mem_nhds hΔ)
      have hk2 : ∀ᶠ k in atTop, ⟪∇ P (xs k), e (φ k)⟫ ≤ ε (φ k) + ε (φ k) ^ 3 / 2 := by
        filter_upwards [htest, hpos, hxs1] with k hk hkp hk1
        rcases hk with h | ⟨-, h⟩
        · exact absurd h (not_le.2 (mul_pos (hε (φ k)) hkp))
        · refine inner_le_of_norm_add_smul_le (he _) (hε _) (h.trans ?_)
          have := hQ (φ k) (xs k) hk1
          linarith [(abs_le.1 this).2]
      have hlim1 : Tendsto (fun k ↦ ⟪∇ P (xs k), e (φ k)⟫) atTop (𝓝 ⟪∇ P x, e₀⟫) :=
        (((continuous_gradient hP1).tendsto x).comp hxs).inner (he₀.comp hφt)
      have hlim2 : Tendsto (fun k ↦ ε (φ k) + ε (φ k) ^ 3 / 2) atTop (𝓝 0) := by
        simpa using hεφ.add ((hεφ.pow 3).div_const 2)
      exact le_of_tendsto_of_tendsto hlim1 hlim2 hk2
  -- Step 2, from above
  have core_above : ∀ P : E d → ℝ, ContDiff ℝ ∞ P → ∀ x ∈ K, ∀ r > 0,
      closedBall x r ⊆ ball (0 : E d) (1 / 2) → P x = w x →
      (∀ z ∈ K ∩ closedBall x r, z ≠ x → w z < P z) →
      (0 < ⟪x, e₀⟫ → 0 ≤ Δ P x) ∧ (⟪x, e₀⟫ = 0 → Δ P x < 0 → 0 ≤ ⟪∇ P x, e₀⟫) := by
    intro P hP x hx r hr hrB hPx hstrict
    obtain ⟨xs, c, hxs, hc, hev⟩ := exists_touch_seq (D := fun k ↦ D (φ k)) (K := K)
      (f := fun k y ↦ -f (φ k) y) (g := fun z ↦ -w z) (P := fun z ↦ -P z) hr
      (fun k ↦ hDc x r hrB (φ k)) (fun k ↦ (hfc x r hrB (φ k)).neg) hP.continuous.neg
      (fun z hz ψ hψ y hy hyz ↦ (hconv z hz ψ hψ y hy hyz).neg) (hK_lim x r hrB)
      (happroxφ x hx) hx (by simp [hPx]) (fun z hz hzx ↦ by linarith [hstrict z hz hzx])
    have hP1 : ContDiff ℝ 1 P := (contDiff_two_of_smooth hP).of_le one_le_two
    have hxs2 : ∀ᶠ k in atTop, xs k ∈ ball x (r / 2) :=
      hxs.eventually (ball_mem_nhds x (half_pos hr))
    have hε1 : ∀ᶠ k in atTop, ε (φ k) ≤ 1 :=
      (hεφ.eventually (gt_mem_nhds one_pos)).mono fun k hk ↦ hk.le
    have htest : ∀ᶠ k in atTop, 0 ≤ ε (φ k) * Δ P (xs k) ∨
        (u (φ k) (xs k) = 0 ∧ Q (φ k) (xs k) ≤ ‖e (φ k) + ε (φ k) • ∇ P (xs k)‖) := by
      filter_upwards [hev, hxs2] with k hk hkx
      obtain ⟨hkD, hkeq, hkle⟩ := hk
      have hball := hball_sub x r (xs k) hkx
      have hεk := hε (φ k)
      refine sub_touch_test (c := -c k) (hu (φ k)) (half_pos hr)
        (fun y hy ↦ hB2 _ (hrB (hball hy))) hP hkD.1 ?_ (fun y hy ↦ ?_)
      · have h := hkeq
        simp only [hf] at h
        have h' : (u (φ k) (xs k) - ⟪xs k, e (φ k)⟫) / ε (φ k) = P (xs k) - c k := by linarith
        rw [div_eq_iff hεk.ne'] at h'
        linarith
      · have h := hkle y ⟨⟨hy.1, hrB (hball hy.2)⟩, hball hy.2⟩
        simp only [hf] at h
        have h' : (u (φ k) y - ⟪y, e (φ k)⟫) / ε (φ k) ≤ P y - c k := by linarith
        rw [div_le_iff₀ hεk] at h'
        linarith
    have hxs1 : ∀ᶠ k in atTop, xs k ∈ ball (0 : E d) 1 := by
      filter_upwards [hxs2] with k hk using hin_ball1 x r hrB _ (hball_sub x r (xs k) hk
        (mem_ball_self (half_pos hr)))
    refine ⟨fun hx0 ↦ ?_, fun hx0 hΔ ↦ ?_⟩
    · have hΔk : ∀ᶠ k in atTop, 0 ≤ Δ P (xs k) := by
        filter_upwards [htest, hinner_lim xs x hxs hx0, hxs1] with k hk hk' hk1
        rcases hk with h | ⟨h, -⟩
        · exact le_of_mul_le_mul_left (by linarith) (hε (φ k))
        · exact absurd h (hposk _ _ hk1 hk').ne'
      exact ge_of_tendsto (((continuous_laplacian (contDiff_two_of_smooth hP)).tendsto x).comp
        hxs) hΔk
    · have hneg : ∀ᶠ k in atTop, Δ P (xs k) < 0 :=
        (((continuous_laplacian (contDiff_two_of_smooth hP)).tendsto x).comp hxs).eventually
          (gt_mem_nhds hΔ)
      have hk2 : ∀ᶠ k in atTop,
          -(ε (φ k) * (2 + ‖∇ P (xs k)‖ ^ 2) / 2) ≤ ⟪∇ P (xs k), e (φ k)⟫ := by
        filter_upwards [htest, hneg, hxs1, hε1] with k hk hkn hk1 hkε
        rcases hk with h | ⟨-, h⟩
        · exact absurd h (not_le.2 (mul_neg_of_pos_of_neg (hε (φ k)) hkn))
        · refine le_inner_of_le_norm_add_smul (he _) (hε _) hkε (le_trans ?_ h)
          have := hQ (φ k) (xs k) hk1
          linarith [(abs_le.1 this).1]
      have hlim1 : Tendsto (fun k ↦ ⟪∇ P (xs k), e (φ k)⟫) atTop (𝓝 ⟪∇ P x, e₀⟫) :=
        (((continuous_gradient hP1).tendsto x).comp hxs).inner (he₀.comp hφt)
      have hlim2 : Tendsto (fun k ↦ -(ε (φ k) * (2 + ‖∇ P (xs k)‖ ^ 2) / 2)) atTop (𝓝 0) := by
        have := ((hεφ.mul ((tendsto_const_nhds (x := (2 : ℝ))).add
          ((((continuous_gradient hP1).tendsto x).comp hxs).norm.pow 2))).div_const 2).neg
        simpa using this
      exact le_of_tendsto_of_tendsto hlim2 hlim1 hk2
  -- strictification (De Silva, the Remark after Definition 2.5, first part)
  have hsmallBall : ∀ x ∈ K, ∀ ρ > 0, ∃ r > 0, r < ρ ∧ closedBall x r ⊆ ball (0 : E d) (1 / 2) := by
    intro x hx ρ hρ
    have hx2 : ‖x‖ < 1 / 2 := by have := hx.2; rwa [mem_ball, dist_zero_right] at this
    refine ⟨min (ρ / 2) ((1 / 2 - ‖x‖) / 2), lt_min (half_pos hρ) (by linarith),
      (min_le_left _ _).trans_lt (half_lt_self hρ), fun y hy ↦ ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hy
    rw [mem_ball, dist_zero_right]
    have h1 : min (ρ / 2) ((1 / 2 - ‖x‖) / 2) ≤ (1 / 2 - ‖x‖) / 2 := min_le_right _ _
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ < 1 / 2 := by linarith
  have strict_below : ∀ P : E d → ℝ, ContDiff ℝ ∞ P → ∀ x, TouchesBelow P w K x →
      (0 < ⟪x, e₀⟫ → Δ P x ≤ 0) ∧ (⟪x, e₀⟫ = 0 → 0 < Δ P x → ⟪∇ P x, e₀⟫ ≤ 0) := by
    intro P hP x htouch
    obtain ⟨h1, h2, h3, h4, h5⟩ := touchesBelow_strict_perturb hP htouch
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhdsWithin_iff.1 h5
    obtain ⟨r, hr, hrρ, hrB⟩ := hsmallBall x htouch.1 ρ hρ
    have hcore := core_below _ h1 x htouch.1 r hr hrB h4.2.1 (fun z hz hzx ↦ by
      have hzρ : z ∈ ball x ρ := by
        have := hz.2; rw [mem_closedBall] at this; rw [mem_ball]; linarith
      have h := hρsub ⟨hzρ, hz.1⟩
      have hq : 0 < (‖z - x‖ ^ 2) ^ 2 := by
        have : z - x ≠ 0 := sub_ne_zero.2 hzx
        positivity
      simp only [mem_ofPred_eq] at h
      linarith)
    rw [h2, h3] at hcore
    exact hcore
  have strict_above : ∀ P : E d → ℝ, ContDiff ℝ ∞ P → ∀ x, TouchesAbove P w K x →
      (0 < ⟪x, e₀⟫ → 0 ≤ Δ P x) ∧ (⟪x, e₀⟫ = 0 → Δ P x < 0 → 0 ≤ ⟪∇ P x, e₀⟫) := by
    intro P hP x htouch
    obtain ⟨h1, h2, h3, h4, h5⟩ := touchesAbove_strict_perturb hP htouch
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhdsWithin_iff.1 h5
    obtain ⟨r, hr, hrρ, hrB⟩ := hsmallBall x htouch.1 ρ hρ
    have hcore := core_above _ h1 x htouch.1 r hr hrB h4.2.1 (fun z hz hzx ↦ by
      have hzρ : z ∈ ball x ρ := by
        have := hz.2; rw [mem_closedBall] at this; rw [mem_ball]; linarith
      have h := hρsub ⟨hzρ, hz.1⟩
      have hq : 0 < (‖z - x‖ ^ 2) ^ 2 := by
        have : z - x ≠ 0 := sub_ne_zero.2 hzx
        positivity
      simp only [mem_ofPred_eq] at h
      linarith [htouch.2.2])
    rw [h2, h3] at hcore
    exact hcore
  refine ⟨φ, hφ, w, ⟨hwc, ?_, ?_⟩, hwb, hw0, hconv⟩
  · -- from below; the Remark's reduction to `ΔP > 0` at boundary points
    intro ψ hψ x htouch
    refine ⟨fun hx0 ↦ (strict_below ψ hψ x htouch).1 hx0, fun hx0 ↦ ?_⟩
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    set κ := |Δ ψ x| + 1 with hκ
    have hκ0 : 0 < κ := by positivity
    obtain ⟨j1, j2, j3⟩ := jet_add_inner_sq hψ e₀ (-η) κ hx0
    have htouch' : TouchesBelow (fun y ↦ ψ y + -η * ⟪y, e₀⟫ + κ * ⟪y, e₀⟫ ^ 2) w K x := by
      refine ⟨htouch.1, by simp [hx0, htouch.2.1], ?_⟩
      filter_upwards [htouch.2.2, self_mem_nhdsWithin,
        nhdsWithin_le_nhds (ball_mem_nhds x (div_pos hη hκ0))] with y hy hyK hyb
      have ht0 : 0 ≤ ⟪y, e₀⟫ := hyK.1
      have ht1 : ⟪y, e₀⟫ ≤ η / κ := by
        have : ⟪y, e₀⟫ = ⟪y - x, e₀⟫ := by rw [inner_sub_left, hx0, sub_zero]
        rw [this]
        calc ⟪y - x, e₀⟫ ≤ ‖y - x‖ * ‖e₀‖ := real_inner_le_norm _ _
          _ = dist y x := by rw [he₀1, mul_one, dist_eq_norm]
          _ ≤ η / κ := (mem_ball.1 hyb).le
      have : κ * ⟪y, e₀⟫ ^ 2 ≤ η * ⟪y, e₀⟫ := by
        rw [le_div_iff₀ hκ0] at ht1
        linarith [mul_le_mul_of_nonneg_left ht1 ht0]
      linarith
    have hΔ : 0 < Δ (fun y ↦ ψ y + -η * ⟪y, e₀⟫ + κ * ⟪y, e₀⟫ ^ 2) x := by
      rw [j2, he₀1]
      have := neg_abs_le (Δ ψ x)
      linarith
    have h := (strict_below _ j1 x htouch').2 hx0 hΔ
    rw [j3, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he₀1] at h
    linarith
  · -- from above
    intro ψ hψ x htouch
    refine ⟨fun hx0 ↦ (strict_above ψ hψ x htouch).1 hx0, fun hx0 ↦ ?_⟩
    refine le_of_forall_pos_le_add fun η hη ↦ ?_
    rw [← sub_le_iff_le_add', zero_sub]
    set κ := |Δ ψ x| + 1 with hκ
    have hκ0 : 0 < κ := by positivity
    obtain ⟨j1, j2, j3⟩ := jet_add_inner_sq hψ e₀ η (-κ) hx0
    have htouch' : TouchesAbove (fun y ↦ ψ y + η * ⟪y, e₀⟫ + -κ * ⟪y, e₀⟫ ^ 2) w K x := by
      refine ⟨htouch.1, by simp [hx0, htouch.2.1], ?_⟩
      filter_upwards [htouch.2.2, self_mem_nhdsWithin,
        nhdsWithin_le_nhds (ball_mem_nhds x (div_pos hη hκ0))] with y hy hyK hyb
      have ht0 : 0 ≤ ⟪y, e₀⟫ := hyK.1
      have ht1 : ⟪y, e₀⟫ ≤ η / κ := by
        have : ⟪y, e₀⟫ = ⟪y - x, e₀⟫ := by rw [inner_sub_left, hx0, sub_zero]
        rw [this]
        calc ⟪y - x, e₀⟫ ≤ ‖y - x‖ * ‖e₀‖ := real_inner_le_norm _ _
          _ = dist y x := by rw [he₀1, mul_one, dist_eq_norm]
          _ ≤ η / κ := (mem_ball.1 hyb).le
      have : κ * ⟪y, e₀⟫ ^ 2 ≤ η * ⟪y, e₀⟫ := by
        rw [le_div_iff₀ hκ0] at ht1
        linarith [mul_le_mul_of_nonneg_left ht1 ht0]
      linarith
    have hΔ : Δ (fun y ↦ ψ y + η * ⟪y, e₀⟫ + -κ * ⟪y, e₀⟫ ^ 2) x < 0 := by
      rw [j2, he₀1]
      have := le_abs_self (Δ ψ x)
      linarith
    have h := (strict_above _ j1 x htouch').2 hx0 hΔ
    rw [j3, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he₀1] at h
    linarith

end EllipticBernoulli
