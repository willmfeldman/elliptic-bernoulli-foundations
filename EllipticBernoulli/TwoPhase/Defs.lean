/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.TwoPhase

/-!
# Basic API for the two-phase definitions

* Evaluation of the `0`-homogeneous extension `homogExt0`.
* The characteristic exponent: `charExponent_sq_add` (`κ² + (d - 2) κ = λ`),
  `charExponent_nonneg`, `charExponent_sub_one` (`κ_d(d - 1) = 1`).
* Two-plane functions: `twoPlane_lipschitzWith`, and `exists_twoPlane_sign_change`, which shows that
  the conclusion of `TwoPhaseClassificationStatement` is satisfiable by a sign-changing function.
-/

open Set Metric

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The `0`-homogeneous extension -/

@[simp]
theorem homogExt0_zero (f : sphere (0 : E d) 1 → ℝ) : homogExt0 f 0 = 0 := by
  simp [homogExt0]

theorem homogExt0_of_ne_zero (f : sphere (0 : E d) 1 → ℝ) {x : E d} (hx : x ≠ 0) :
    homogExt0 f x = f ⟨‖x‖⁻¹ • x, by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩ := by
  simp [homogExt0, hx]

/-- The `0`-homogeneous extension agrees with `f` on the sphere. -/
@[simp]
theorem homogExt0_coe (f : sphere (0 : E d) 1 → ℝ) (ω : sphere (0 : E d) 1) :
    homogExt0 f ω = f ω := by
  have hω : ‖(ω : E d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  have hne : (ω : E d) ≠ 0 := norm_ne_zero_iff.mp (by rw [hω]; exact one_ne_zero)
  rw [homogExt0_of_ne_zero f hne]
  congr 1
  ext1
  simp [hω]

/-- The `0`-homogeneous extension is `f ∘ (x ↦ x / ‖x‖)`, written with Mathlib's polar
homeomorphism `homeomorphUnitSphereProd`. -/
theorem homogExt0_eq_homeomorphUnitSphereProd (f : sphere (0 : E d) 1 → ℝ) {x : E d}
    (hx : x ≠ 0) : homogExt0 f x = f (homeomorphUnitSphereProd (E d) ⟨x, hx⟩).1 := by
  rw [homogExt0_of_ne_zero f hx]
  congr 1
  ext1
  simp

/-! ### Global local minimizers -/

/-- Unfolding of `IsLocalEnergyMinimizer univ (fun _ ↦ 1) u`: for some weak gradient `G`,
`u ∈ H¹_loc(ℝᵈ)` and, for every ball `B = ball x r` and every `v ∈ H¹_loc(ℝᵈ)` with `v = u` a.e.
off `B`, `J(u, B) ≤ J(v, B)`. -/
theorem isLocalEnergyMinimizer_univ_iff {u : E d → ℝ} :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) u ↔
      ∃ G, MemH1Loc univ u G ∧ ∀ (x : E d) (r : ℝ) (v : E d → ℝ) (Gv : E d → E d),
        MemH1Loc univ v Gv → (∀ᵐ y ∂(MeasureTheory.volume.restrict (ball x r)ᶜ), v y = u y) →
        energyJ (ball x r) (fun _ ↦ 1) u G ≤ energyJ (ball x r) (fun _ ↦ 1) v Gv := by
  constructor
  · rintro ⟨G, hG, hmin⟩
    refine ⟨G, hG, fun x r v Gv hv hvu ↦ ?_⟩
    rcases le_or_gt r 0 with hr | hr
    · simp [energyJ, ball_eq_empty.mpr hr]
    · exact (hmin x r hr (subset_univ _)).2.2.2 v Gv hv (by rwa [← compl_eq_univ_sdiff])
        (Filter.Eventually.of_forall fun _ ↦ trivial)
  · rintro ⟨G, hG, hmin⟩
    refine ⟨G, hG, fun x r _ _ ↦ ⟨hG, fun _ _ ↦ rfl, fun _ _ ↦ trivial, fun v Gv hv hvu _ ↦ ?_⟩⟩
    exact hmin x r v Gv hv (by rwa [compl_eq_univ_sdiff])

/-! ### The characteristic exponent -/

/-- `κ = κ_d(λ)` solves `κ² + (d - 2) κ = λ` for `λ ≥ 0`. -/
theorem charExponent_sq_add {lam : ℝ} (hlam : 0 ≤ lam) :
    charExponent d lam ^ 2 + ((d : ℝ) - 2) * charExponent d lam = lam := by
  have h : 0 ≤ ((d : ℝ) - 2) ^ 2 + 4 * lam := by positivity
  have hs := Real.sq_sqrt h
  unfold charExponent
  linear_combination hs / 4

theorem charExponent_nonneg {lam : ℝ} (hlam : 0 ≤ lam) : 0 ≤ charExponent d lam := by
  unfold charExponent
  have h : |(d : ℝ) - 2| ≤ √(((d : ℝ) - 2) ^ 2 + 4 * lam) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have := le_abs_self ((d : ℝ) - 2)
  linarith

/-- `κ_d(d - 1) = 1`. -/
theorem charExponent_sub_one : charExponent d ((d : ℝ) - 1) = 1 := by
  unfold charExponent
  have h : ((d : ℝ) - 2) ^ 2 + 4 * ((d : ℝ) - 1) = (d : ℝ) ^ 2 := by ring
  rw [h, Real.sqrt_sq (Nat.cast_nonneg d)]
  ring

/-! ### Two-plane functions -/

private theorem lipschitzWith_twoPlaneProfile (a b : ℝ) :
    LipschitzWith (‖a‖₊ + ‖b‖₊) fun t : ℝ ↦ a * max t 0 - b * max (-t) 0 := by
  refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
  simp only [Real.dist_eq, NNReal.coe_add, coe_nnnorm, Real.norm_eq_abs]
  have h1 : |max s 0 - max t 0| ≤ |s - t| := abs_max_sub_max_le_abs s t 0
  have h2 : |max (-s) 0 - max (-t) 0| ≤ |s - t| := by
    have := abs_max_sub_max_le_abs (-s) (-t) 0
    rwa [neg_sub_neg, abs_sub_comm t s] at this
  calc |a * max s 0 - b * max (-s) 0 - (a * max t 0 - b * max (-t) 0)|
      = |a * (max s 0 - max t 0) - b * (max (-s) 0 - max (-t) 0)| := by ring_nf
    _ ≤ |a * (max s 0 - max t 0)| + |b * (max (-s) 0 - max (-t) 0)| := abs_sub _ _
    _ = |a| * |max s 0 - max t 0| + |b| * |max (-s) 0 - max (-t) 0| := by
        rw [abs_mul, abs_mul]
    _ ≤ |a| * |s - t| + |b| * |s - t| := by gcongr
    _ = (|a| + |b|) * |s - t| := by ring

/-- A two-plane function is Lipschitz, with constant `(|a| + |b|) ‖e‖`. -/
theorem twoPlane_lipschitzWith (a b : ℝ) (e : E d) (c : ℝ) :
    LipschitzWith ((‖a‖₊ + ‖b‖₊) * ‖e‖₊) (twoPlane a b e c) := by
  have hl : LipschitzWith ‖e‖₊ fun x : E d ↦ inner ℝ x e + c := by
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    rw [Real.dist_eq, add_sub_add_right_eq_sub, ← inner_sub_left, coe_nnnorm, dist_eq_norm,
      mul_comm]
    exact abs_real_inner_le_norm _ _
  exact (lipschitzWith_twoPlaneProfile a b).comp hl

/-- For a unit vector `e` and `a, b > 0`, the two-plane function takes the value `a > 0` and the
value `-b < 0`. -/
theorem twoPlane_pos_and_neg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {e : E d} (he : ‖e‖ = 1)
    (c : ℝ) : (∃ x, 0 < twoPlane a b e c x) ∧ ∃ x, twoPlane a b e c x < 0 := by
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  refine ⟨⟨(1 - c) • e, ?_⟩, ⟨(-1 - c) • e, ?_⟩⟩
  · simp only [twoPlane, inner_smul_left, hee, RCLike.conj_to_real, mul_one, sub_add_cancel]
    norm_num
    exact ha
  · simp only [twoPlane, inner_smul_left, hee, RCLike.conj_to_real, mul_one, sub_add_cancel]
    norm_num
    exact hb

/-- The conclusion of `TwoPhaseClassificationStatement` can hold for a sign-changing function: in
every dimension `d ≥ 1` there are a unit vector `e` and `a, b > 0` with `a² - b² = 1`, and the
two-plane function `a (x·e)⁺ - b (x·e)⁻` takes a positive and a negative value. -/
theorem exists_twoPlane_sign_change (hd : 1 ≤ d) :
    ∃ (e : E d) (a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = 1 ∧
      (∃ x, 0 < twoPlane a b e 0 x) ∧ ∃ x, twoPlane a b e 0 x < 0 := by
  let e : E d := EuclideanSpace.single ⟨0, hd⟩ 1
  have he : ‖e‖ = 1 := by simp [e]
  refine ⟨e, √2, 1, he, by positivity, one_pos, ?_,
    twoPlane_pos_and_neg (by positivity) one_pos he 0⟩
  rw [Real.sq_sqrt (by norm_num)]
  norm_num

end EllipticBernoulli
