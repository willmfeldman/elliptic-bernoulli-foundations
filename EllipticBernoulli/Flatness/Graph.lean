/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Flatness.Iteration
public import EllipticBernoulli.Defs.Regularity
import EllipticBernoulli.Flatness.GraphAux
import EllipticBernoulli.Viscosity.Affine
import EllipticBernoulli.Viscosity.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Pointwise `C^{1,α}` flatness gives a `C^{1,α}` free-boundary graph

De Silva (2011), end of §5 (proof of Theorem 1.1); Caffarelli–Salsa, Ch. 4 (flatness at every
scale gives a `C^{1,α}` graph).

The argument is purely geometric. It uses only the **cone condition** `IsFlatConeAt` at every
free-boundary point: in `B_s(z)`, `u > 0` above the slab `|⟪x - z, ν⟫| ≤ M s^{1+α}` and `u ≤ 0`
below it. This follows from `IsFlatC1AlphaAt` (`IsFlatC1AlphaAt.isFlatConeAt`).

* `FlatGraphData U v e ν ε η M α ρ`: the hypotheses of the graph construction (`ε`-flatness on
  `B_1` in direction `e`, and at every free-boundary point `z ∈ B_{3/4}` a normal `ν z` with
  `‖ν z - e‖ ≤ η` and the cone condition with constant `M`, exponent `α`, up to radius `ρ`).
* `FlatGraphData.abs_inner_le`, `FlatGraphData.abs_inner_sub_le` (the cone condition at pairs of
  free-boundary points).
* `FlatGraphData.holder_normal`: `‖ν z - ν z'‖ ≤ 32 M ‖z - z'‖^α` for
  `‖z - z'‖ ≤ ρ/2`. The proof is geometric (two cones), not by comparing slopes.
* `FlatGraphData.abs_inner_le_norm_perpProj`: free-boundary points are `1`-Lipschitz over `e^⊥`
  at distances `≤ ρ/2` (uniqueness on vertical lines, in quantitative form).
* `fbHeight`, `FlatGraphData.fb_graph`: every vertical line over `‖x'‖ < 5/8` meets
  `F(v) ∩ B_{3/4}` exactly once, at height `fbHeight`.
* `FlatGraphData.fb_graph_C1alpha`: `fbHeight` is differentiable with gradient
  `-(⟪e, ν⟫)⁻¹ P ν` and this gradient is `α`-Hölder at distances `≤ ρ/4`.
* `FlatGraphData.isC1GammaHypersurfaceNear`: the cutoff `χ · fbHeight` is a global
  `C^{1,α}` function and `F(v) ∩ B_{1/2}` is its graph.
* `exists_flatGraphData`: `flat_pointwise_C1alpha`, applied after rescaling by `4` at each
  free-boundary point of `B_{3/4}`, produces `FlatGraphData` (and `IsFlatC1AlphaAt` at every
  such point, used in `Flatness/Classical.lean`).
* `isC1GammaHypersurfaceNear_of_flat_normalized`: the normalized graph theorem on `B_{1/2}`.

`flat_pointwise_C1alpha` is applied at *every* free-boundary point of `B_{3/4}` (after
rescaling), so the graph is obtained on `B_{1/2}` at once, as `FlatGraphStatement` (radius `r/2`)
requires, and no separate covering argument is needed.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace NNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The projection `z ↦ z - ⟪z, e⟫ e` onto `e^⊥` (the convention of
`IsC1GammaHypersurfaceNear`). -/
def perpProj (e z : E d) : E d := z - ⟪z, e⟫ • e

/-- **The cone condition** at `z` with unit normal `ν`, constant `M`, exponent `α`, up to radius
`ρ`: for `0 < s ≤ ρ` and `x ∈ B_s(z)`, `v x > 0` if `⟪x - z, ν⟫ > M s^{1+α}` and `v x ≤ 0` if
`⟪x - z, ν⟫ < -M s^{1+α}`. -/
def IsFlatConeAt (v : E d → ℝ) (z ν : E d) (M α ρ : ℝ) : Prop :=
  ‖ν‖ = 1 ∧ ∀ s ∈ Ioc (0 : ℝ) ρ, ∀ x ∈ ball z s,
    (M * s ^ (1 + α) < ⟪x - z, ν⟫ → 0 < v x) ∧ (⟪x - z, ν⟫ < -(M * s ^ (1 + α)) → v x ≤ 0)

/-- The height of the free boundary of `v` over `perpProj e z`: the first `t ∈ [-2ε, 2ε]` with
`v (perpProj e z + t e) > 0`. -/
def fbHeight (v : E d → ℝ) (e : E d) (ε : ℝ) (z : E d) : ℝ :=
  sInf {t ∈ Icc (-2 * ε) (2 * ε) | 0 < v (perpProj e z + t • e)}

/-- The gradient of `fbHeight` at `z`: `-(⟪e, ν y⟫)⁻¹ perpProj e (ν y)`, where
`y = perpProj e z + fbHeight v e ε z • e` is the free-boundary point over `z`. -/
def fbGrad (v : E d → ℝ) (e : E d) (ν : E d → E d) (ε : ℝ) (z : E d) : E d :=
  -(⟪e, ν (perpProj e z + fbHeight v e ε z • e)⟫)⁻¹ •
    perpProj e (ν (perpProj e z + fbHeight v e ε z • e))

/-- Hypotheses of the graph construction. `v` is `ε`-flat on `B_1 ⊆ U` in
direction `e`, and every free-boundary point `z ∈ B_{3/4}` has a normal `ν z` with
`‖ν z - e‖ ≤ η` satisfying the cone condition with constants `M, α, ρ`. The smallness conditions
are those used in the proofs. -/
structure FlatGraphData (U : Set (E d)) (v : E d → ℝ) (e : E d) (ν : E d → E d)
    (ε η M α ρ : ℝ) : Prop where
  isOpen : IsOpen U
  ball_subset : ball (0 : E d) 1 ⊆ U
  continuousOn : ContinuousOn v U
  norm_e : ‖e‖ = 1
  flat : ∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ v y ∧ v y ≤ max (⟪y, e⟫ + ε) 0
  ε_pos : 0 < ε
  ε_le : 8 * ε ≤ ρ
  ρ_le : ρ ≤ 1 / 2
  α_pos : 0 < α
  α_le : α ≤ 1
  η_le : η ≤ 1 / 8
  M_nonneg : 0 ≤ M
  M_le : M ≤ 1 / 8
  normal : ∀ z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4),
    ‖ν z - e‖ ≤ η ∧ IsFlatConeAt v z (ν z) M α ρ

end EllipticBernoulli

end

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The projection onto `e^⊥` -/

section perpProj

variable {e : E d}

theorem inner_perpProj (he : ‖e‖ = 1) (z : E d) : ⟪perpProj e z, e⟫ = 0 := by
  simp [perpProj, inner_sub_left, real_inner_smul_left, he]

theorem perpProj_add_inner_smul (z : E d) : perpProj e z + ⟪z, e⟫ • e = z := by
  simp [perpProj]

theorem perpProj_sub (z w : E d) : perpProj e (z - w) = perpProj e z - perpProj e w := by
  simp only [perpProj, inner_sub_left, sub_smul]; abel

theorem perpProj_add (z w : E d) : perpProj e (z + w) = perpProj e z + perpProj e w := by
  simp only [perpProj, inner_add_left, add_smul]; abel

theorem perpProj_add_smul (he : ‖e‖ = 1) (z : E d) (t : ℝ) :
    perpProj e (z + t • e) = perpProj e z := by
  have : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  simp only [perpProj, inner_add_left, real_inner_smul_left, this, mul_one, add_smul]; abel

theorem perpProj_perpProj (he : ‖e‖ = 1) (z : E d) : perpProj e (perpProj e z) = perpProj e z := by
  have h := perpProj_add_smul he (perpProj e z) (⟪z, e⟫)
  rw [perpProj_add_inner_smul] at h
  exact h.symm

theorem norm_perpProj_sq (he : ‖e‖ = 1) (z : E d) :
    ‖perpProj e z‖ ^ 2 = ‖z‖ ^ 2 - ⟪z, e⟫ ^ 2 := by
  rw [perpProj, norm_sub_sq_real, norm_smul, he, real_inner_smul_right, Real.norm_eq_abs, mul_one,
    sq_abs]
  ring

theorem norm_perpProj_le (he : ‖e‖ = 1) (z : E d) : ‖perpProj e z‖ ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_perpProj_sq he]
  nlinarith [sq_nonneg ⟪z, e⟫]

theorem inner_perpProj_eq (z w : E d) :
    ⟪perpProj e z, w⟫ = ⟪z, perpProj e w⟫ := by
  simp only [perpProj, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_comm e z, real_inner_comm e w]
  ring

end perpProj

/-! ### Consequences of `IsFlatC1AlphaAt` -/

/-- Pointwise `C^{1,α}` flatness gives the cone condition (when `Q z > 0`). -/
theorem IsFlatC1AlphaAt.isFlatConeAt {u Q : E d → ℝ} {z ν : E d} {C α R : ℝ}
    (h : IsFlatC1AlphaAt u Q z ν C α R) (hQ : 0 < Q z) : IsFlatConeAt u z ν C α R := by
  refine ⟨h.1, fun s hs x hx ↦ ⟨fun hlt ↦ ?_, fun hlt ↦ ?_⟩⟩
  · have := (h.2 s hs x hx).1
    have hpos : 0 < max (⟪x - z, ν⟫ - C * s ^ (1 + α)) 0 := lt_max_of_lt_left (by linarith)
    exact lt_of_lt_of_le (mul_pos hQ hpos) this
  · have := (h.2 s hs x hx).2
    rwa [max_eq_right (by linarith), mul_zero] at this

/-! ### Free-boundary points under the cone condition -/

namespace FlatGraphData

variable {U : Set (E d)} {v : E d → ℝ} {e : E d} {ν : E d → E d} {ε η M α ρ : ℝ}

theorem isOpen_posSet (H : FlatGraphData U v e ν ε η M α ρ) : IsOpen (posSet v U) :=
  EllipticBernoulli.isOpen_posSet H.isOpen H.continuousOn

/-- Free-boundary points are not in the positivity set. -/
theorem not_pos_of_mem (H : FlatGraphData U v e ν ε η M α ρ) {y : E d}
    (hy : y ∈ freeBoundary v U) : ¬ 0 < v y := fun h ↦ by
  have hfr := hy.1
  rw [H.isOpen_posSet.frontier_eq] at hfr
  exact hfr.2 ⟨hy.2, h⟩

/-- A free-boundary point has no neighbourhood on which `v ≤ 0`. -/
theorem _root_.EllipticBernoulli.not_nonpos_nhd_of_mem_freeBoundary {y : E d}
    (hy : y ∈ freeBoundary v U) {O : Set (E d)} (hO : IsOpen O) (hyO : y ∈ O)
    (hle : ∀ x ∈ O, v x ≤ 0) : False := by
  have hcl : y ∈ closure (posSet v U) := frontier_subset_closure hy.1
  obtain ⟨x, hxO, hxpos⟩ := mem_closure_iff.1 hcl O hO hyO
  exact absurd (hle x hxO) (not_le.2 hxpos.2)

end FlatGraphData

/-- Free-boundary points of an `ε`-flat function on `B_1` lie in the slab `|⟪y, e⟫| ≤ ε`. -/
theorem abs_inner_le_of_flat {U : Set (E d)} {v : E d → ℝ} {e : E d} {ε : ℝ} (hU : IsOpen U)
    (hcont : ContinuousOn v U)
    (hflat : ∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ v y ∧ v y ≤ max (⟪y, e⟫ + ε) 0)
    {y : E d} (hy : y ∈ freeBoundary v U) (hy1 : y ∈ ball (0 : E d) 1) : |⟪y, e⟫| ≤ ε := by
  refine abs_le.2 ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    refine not_nonpos_nhd_of_mem_freeBoundary hy
      ((isOpen_lt (by fun_prop) continuous_const).inter isOpen_ball)
      (show y ∈ {x | ⟪x, e⟫ < -ε} ∩ ball 0 1 from ⟨hlt, hy1⟩) fun x hx ↦ ?_
    have := (hflat x hx.2).2
    rwa [max_eq_right (by linarith [show ⟪x, e⟫ < -ε from hx.1])] at this
  · have h1 := (hflat y hy1).1
    have hopen := EllipticBernoulli.isOpen_posSet hU hcont
    have h2 : ¬ 0 < v y := fun h ↦ by
      have hfr := hy.1
      rw [hopen.frontier_eq] at hfr
      exact hfr.2 ⟨hy.2, h⟩
    linarith [le_max_left (⟪y, e⟫ - ε) 0, not_lt.1 h2]

namespace FlatGraphData

variable {U : Set (E d)} {v : E d → ℝ} {e : E d} {ν : E d → E d} {ε η M α ρ : ℝ}

theorem ρ_pos (H : FlatGraphData U v e ν ε η M α ρ) : 0 < ρ := by
  linarith [H.ε_pos, H.ε_le]

/-- Free-boundary points of `B_1` lie in the slab `|⟪y, e⟫| ≤ ε`. -/
theorem abs_inner_le (H : FlatGraphData U v e ν ε η M α ρ) {y : E d}
    (hy : y ∈ freeBoundary v U) (hy1 : y ∈ ball (0 : E d) 1) : |⟪y, e⟫| ≤ ε :=
  abs_inner_le_of_flat H.isOpen H.continuousOn H.flat hy hy1

/-- **The cone condition at pairs of free-boundary points**: if `z ∈ F(v) ∩ B_{3/4}`,
`x ∈ F(v)` and `‖x - z‖ < s ≤ ρ`, then `|⟪x - z, ν z⟫| ≤ M s^{1+α}`. -/
theorem abs_inner_sub_le (H : FlatGraphData U v e ν ε η M α ρ) {z x : E d}
    (hz : z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4)) (hx : x ∈ freeBoundary v U) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) ρ) (hxz : x ∈ ball z s) :
    |⟪x - z, ν z⟫| ≤ M * s ^ (1 + α) := by
  obtain ⟨-, hcone⟩ := (H.normal z hz).2
  refine abs_le.2 ⟨?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    refine not_nonpos_nhd_of_mem_freeBoundary hx
      ((isOpen_lt (by fun_prop) continuous_const).inter isOpen_ball)
      (show x ∈ {w | ⟪w - z, ν z⟫ < -(M * s ^ (1 + α))} ∩ ball z s from ⟨hlt, hxz⟩)
      fun w hw ↦ (hcone s hs w hw.2).2 hw.1
  · by_contra hlt
    push Not at hlt
    exact H.not_pos_of_mem hx ((hcone s hs x hxz).1 hlt)

theorem inner_e_normal_ge (H : FlatGraphData U v e ν ε η M α ρ) {z : E d}
    (hz : z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4)) : 1 - η ≤ ⟪e, ν z⟫ := by
  have h1 : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, H.norm_e, one_pow]
  have h2 : ⟪e, ν z⟫ = 1 + ⟪e, ν z - e⟫ := by rw [inner_sub_right, h1]; ring
  have h3 : |⟪e, ν z - e⟫| ≤ η := by
    calc |⟪e, ν z - e⟫| ≤ ‖e‖ * ‖ν z - e‖ := abs_real_inner_le_norm _ _
      _ ≤ η := by rw [H.norm_e, one_mul]; exact (H.normal z hz).1
  linarith [neg_abs_le ⟪e, ν z - e⟫]

/-- **Hölder continuity of the normal.** For free-boundary points
`z, z' ∈ B_{3/4}` with `‖z - z'‖ ≤ ρ/2`, `‖ν z - ν z'‖ ≤ 32 M ‖z - z'‖^α`.

Proof: with `s = ‖z' - z‖`, `a = ‖ν z' - ν z‖` and `x = z' + (s / 2a)(ν z' - ν z)`, the cone
at `z'` (scale `s`) forces `v x > 0` if `a > 4 M s^α`, while the cone at `z` (scale `2s`, which
contains `z'` in its slab) forces `v x ≤ 0` if `a > 32 M s^α`. -/
theorem holder_normal (H : FlatGraphData U v e ν ε η M α ρ) {z z' : E d}
    (hz : z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4))
    (hz' : z' ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4)) (hzz' : ‖z' - z‖ ≤ ρ / 2) :
    ‖ν z' - ν z‖ ≤ 32 * M * ‖z' - z‖ ^ α := by
  set s := ‖z' - z‖ with hs_def
  set a := ‖ν z' - ν z‖ with ha_def
  have hM := H.M_nonneg
  by_contra hlt
  push Not at hlt
  have hsα0 : 0 ≤ s ^ α := Real.rpow_nonneg (norm_nonneg _) _
  have ha0 : 0 < a := lt_of_le_of_lt (mul_nonneg (mul_nonneg (by norm_num) hM) hsα0) hlt
  have hs0 : 0 < s := by
    rcases (norm_nonneg (z' - z)).lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← hs_def] at h
      rw [← h, Real.zero_rpow H.α_pos.ne', mul_zero] at hlt
      have : z' = z := sub_eq_zero.1 (norm_eq_zero.1 h.symm)
      rw [this, sub_self, norm_zero] at ha_def
      linarith
  obtain ⟨hν, hcone⟩ := (H.normal z hz).2
  obtain ⟨hν', hcone'⟩ := (H.normal z' hz').2
  -- the inner products of `ν z' - ν z` with the two normals
  have hsq : a ^ 2 = 2 - 2 * ⟪ν z', ν z⟫ := by
    rw [ha_def, norm_sub_sq_real, hν, hν']; ring
  have hi' : ⟪ν z' - ν z, ν z'⟫ = a ^ 2 / 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hν', real_inner_comm, hsq]; ring
  have hi : ⟪ν z' - ν z, ν z⟫ = -(a ^ 2 / 2) := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, hν, hsq]; ring
  set x := z' + (s / (2 * a)) • (ν z' - ν z) with hx_def
  have hxz' : ‖x - z'‖ = s / 2 := by
    rw [hx_def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hs0 (mul_pos two_pos ha0)), ← ha_def]
    field_simp
  have hρ1 : ρ ≤ 1 := H.ρ_le.trans (by norm_num)
  have hkey : s / (2 * a) * (a ^ 2 / 2) = s * a / 4 := by field_simp; ring
  -- positivity from the cone at `z'`
  have hpos : 0 < v x := by
    refine (hcone' s ⟨hs0, by linarith⟩ x ?_).1 ?_
    · rw [mem_ball, dist_eq_norm, hxz']; linarith
    · rw [hx_def, add_sub_cancel_left, real_inner_smul_left, hi', Real.rpow_add hs0,
        Real.rpow_one]
      have : 4 * M * s ^ α < a := by linarith [mul_nonneg hM hsα0]
      rw [hkey]
      linarith [mul_lt_mul_of_pos_left this hs0]
  -- nonpositivity from the cone at `z`
  have h2s : 2 * s ∈ Ioc (0 : ℝ) ρ := ⟨mul_pos two_pos hs0, by linarith⟩
  have hz'z : z' ∈ ball z (2 * s) := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hslab := H.abs_inner_sub_le hz hz'.1 h2s hz'z
  have h2α : (2 : ℝ) ^ (1 + α) ≤ 4 := by
    calc (2 : ℝ) ^ (1 + α) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [H.α_le])
      _ = 4 := by norm_num
  have hpow : (2 * s) ^ (1 + α) = 2 ^ (1 + α) * (s * s ^ α) := by
    rw [Real.mul_rpow (by norm_num) hs0.le, Real.rpow_add hs0, Real.rpow_one]
  have hnonpos : v x ≤ 0 := by
    refine (hcone (2 * s) h2s x ?_).2 ?_
    · rw [mem_ball, dist_eq_norm]
      calc ‖x - z‖ = ‖(x - z') + (z' - z)‖ := by abel_nf
        _ ≤ ‖x - z'‖ + ‖z' - z‖ := norm_add_le _ _
        _ < 2 * s := by rw [hxz']; linarith
    · have hxz : x - z = (z' - z) + (s / (2 * a)) • (ν z' - ν z) := by
        rw [hx_def]; abel
      rw [hxz, inner_add_left, real_inner_smul_left, hi]
      have hle : ⟪z' - z, ν z⟫ ≤ M * (2 * s) ^ (1 + α) := (abs_le.1 hslab).2
      have hMs : M * (2 * s) ^ (1 + α) ≤ 4 * M * (s * s ^ α) := by
        have hS : 0 ≤ M * (s * s ^ α) := mul_nonneg hM (mul_nonneg hs0.le hsα0)
        calc M * (2 * s) ^ (1 + α) = (M * (s * s ^ α)) * 2 ^ (1 + α) := by rw [hpow]; ring
          _ ≤ (M * (s * s ^ α)) * 4 := mul_le_mul_of_nonneg_left h2α hS
          _ = 4 * M * (s * s ^ α) := by ring
      have : 32 * M * (s * s ^ α) < s * a := by linarith [mul_lt_mul_of_pos_left hlt hs0]
      linarith
  linarith

theorem ball_three_quarters_subset {y : E d} (hy : y ∈ ball (0 : E d) (3 / 4)) :
    y ∈ ball (0 : E d) 1 :=
  ball_subset_ball (by norm_num) hy

/-- **Free-boundary points are `1`-Lipschitz over `e^⊥`** (uniqueness, in quantitative form):
for `y₁, y₂ ∈ F(v) ∩ B_{3/4}` with `‖y₂ - y₁‖ ≤ ρ/2`,
`|⟪y₂ - y₁, e⟫| ≤ ‖perpProj e (y₂ - y₁)‖`. -/
theorem abs_inner_le_norm_perpProj (H : FlatGraphData U v e ν ε η M α ρ) {y₁ y₂ : E d}
    (hy₁ : y₁ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4))
    (hy₂ : y₂ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4)) (h : ‖y₂ - y₁‖ ≤ ρ / 2) :
    |⟪y₂ - y₁, e⟫| ≤ ‖perpProj e (y₂ - y₁)‖ := by
  set w := y₂ - y₁ with hw_def
  set p := perpProj e w with hp_def
  set t := ⟪w, e⟫ with ht_def
  rcases eq_or_ne w 0 with hw | hw
  · simp [ht_def, hw]
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hρ1 : ρ ≤ 1 := H.ρ_le.trans (by norm_num)
  have hs : 2 * ‖w‖ ∈ Ioc (0 : ℝ) ρ := ⟨by positivity, by linarith⟩
  have hy₂b : y₂ ∈ ball y₁ (2 * ‖w‖) := by
    rw [mem_ball, dist_eq_norm, ← hw_def]; linarith
  have hslab := H.abs_inner_sub_le hy₁ hy₂.1 hs hy₂b
  rw [← hw_def] at hslab
  have hpow : (2 * ‖w‖) ^ (1 + α) ≤ 2 * ‖w‖ := by
    have := Real.rpow_le_rpow_of_exponent_ge' (by positivity : (0 : ℝ) ≤ 2 * ‖w‖)
      (by linarith : 2 * ‖w‖ ≤ 1) zero_le_one (by linarith [H.α_pos] : (1 : ℝ) ≤ 1 + α)
    rwa [Real.rpow_one] at this
  have hM := H.M_nonneg
  have hwν : |⟪w, ν y₁⟫| ≤ 2 * M * ‖w‖ :=
    hslab.trans (by linarith [mul_le_mul_of_nonneg_left hpow hM])
  -- decompose `w = p + t e`
  have hdec : w = p + t • e := (perpProj_add_inner_smul w).symm
  have hpe : ⟪p, e⟫ = 0 := inner_perpProj H.norm_e w
  have hnw : ‖w‖ ≤ ‖p‖ + |t| := by
    calc ‖w‖ = ‖p + t • e‖ := by rw [← hdec]
      _ ≤ ‖p‖ + ‖t • e‖ := norm_add_le _ _
      _ = ‖p‖ + |t| := by rw [norm_smul, H.norm_e, mul_one, Real.norm_eq_abs]
  have hc := H.inner_e_normal_ge hy₁
  have hpν : |⟪p, ν y₁⟫| ≤ η * ‖p‖ := by
    have : ⟪p, ν y₁⟫ = ⟪p, ν y₁ - e⟫ := by rw [inner_sub_right, hpe, sub_zero]
    rw [this]
    calc |⟪p, ν y₁ - e⟫| ≤ ‖p‖ * ‖ν y₁ - e‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖p‖ * η := mul_le_mul_of_nonneg_left (H.normal y₁ hy₁).1 (norm_nonneg _)
      _ = η * ‖p‖ := mul_comm _ _
  have hsplit : ⟪w, ν y₁⟫ = ⟪p, ν y₁⟫ + t * ⟪e, ν y₁⟫ := by
    conv_lhs => rw [hdec]
    rw [inner_add_left, real_inner_smul_left]
  have hη := H.η_le
  have hM8 := H.M_le
  have hct : |t| * ⟪e, ν y₁⟫ ≤ 2 * M * (‖p‖ + |t|) + η * ‖p‖ := by
    have h1 : |t * ⟪e, ν y₁⟫| = |t| * ⟪e, ν y₁⟫ := by
      rw [abs_mul, abs_of_pos (a := ⟪e, ν y₁⟫) (by linarith)]
    have h2 : |t * ⟪e, ν y₁⟫| ≤ |⟪w, ν y₁⟫| + |⟪p, ν y₁⟫| := by
      rw [show t * ⟪e, ν y₁⟫ = ⟪w, ν y₁⟫ - ⟪p, ν y₁⟫ by rw [hsplit]; ring]
      exact abs_sub _ _
    have h3 : 2 * M * ‖w‖ ≤ 2 * M * (‖p‖ + |t|) :=
      mul_le_mul_of_nonneg_left hnw (mul_nonneg zero_le_two hM)
    linarith
  have ht0 := abs_nonneg t
  have hp0 := norm_nonneg p
  linarith [mul_le_mul_of_nonneg_left hc ht0, mul_le_mul_of_nonneg_left hη ht0,
    mul_le_mul_of_nonneg_left hM8 ht0, mul_le_mul_of_nonneg_left hM8 hp0,
    mul_le_mul_of_nonneg_left hη hp0]

/-- Existence on vertical lines: the vertical line over `perpProj e z`, `‖perpProj e z‖ < 5/8`,
meets the free boundary at height `fbHeight v e ε z`, inside `B_{3/4}` (the first point of
positivity along the line). -/
theorem fb_graph (H : FlatGraphData U v e ν ε η M α ρ) {z : E d}
    (hz : ‖perpProj e z‖ < 5 / 8) :
    perpProj e z + fbHeight v e ε z • e ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) := by
  set p := perpProj e z with hp_def
  set S := {t ∈ Icc (-2 * ε) (2 * ε) | 0 < v (p + t • e)} with hS_def
  have hh : fbHeight v e ε z = sInf S := rfl
  set h := sInf S with hh_def
  have hε := H.ε_pos
  have h2ε : 2 * ε ≤ 1 / 8 := by linarith [H.ε_le, H.ρ_le]
  have hpe : ⟪p, e⟫ = 0 := inner_perpProj H.norm_e z
  have hin : ∀ t : ℝ, ⟪p + t • e, e⟫ = t := fun t ↦ by
    rw [inner_add_left, hpe, real_inner_smul_left, real_inner_self_eq_norm_sq, H.norm_e]; ring
  have hball : ∀ t : ℝ, |t| ≤ 2 * ε → p + t • e ∈ ball (0 : E d) (3 / 4) := fun t ht ↦ by
    rw [mem_ball, dist_zero_right]
    calc ‖p + t • e‖ ≤ ‖p‖ + ‖t • e‖ := norm_add_le _ _
      _ = ‖p‖ + |t| := by rw [norm_smul, H.norm_e, mul_one, Real.norm_eq_abs]
      _ < 3 / 4 := by linarith
  have hball1 : ∀ t : ℝ, |t| ≤ 2 * ε → p + t • e ∈ ball (0 : E d) 1 := fun t ht ↦
    ball_three_quarters_subset (hball t ht)
  have hmemS : 2 * ε ∈ S := by
    refine ⟨⟨by linarith, le_rfl⟩, ?_⟩
    have := (H.flat _ (hball1 (2 * ε) (by rw [abs_of_pos (by linarith)]))).1
    rw [hin] at this
    exact lt_of_lt_of_le (lt_max_of_lt_left (by linarith)) this
  have hSlow : ∀ t ∈ S, -ε ≤ t := fun t ht ↦ by
    by_contra hlt
    push Not at hlt
    have hta : |t| ≤ 2 * ε := abs_le.2 ⟨by linarith [ht.1.1], ht.1.2⟩
    have := (H.flat _ (hball1 t hta)).2
    rw [hin, max_eq_right (by linarith)] at this
    exact absurd ht.2 (not_lt.2 this)
  have hne : S.Nonempty := ⟨_, hmemS⟩
  have hbdd : BddBelow S := ⟨-2 * ε, fun t ht ↦ ht.1.1⟩
  have hh_ge : -ε ≤ h := le_csInf hne hSlow
  have hh_le : h ≤ 2 * ε := csInf_le hbdd hmemS
  have hha : |h| ≤ 2 * ε := abs_le.2 ⟨by linarith, hh_le⟩
  rw [hh]
  refine ⟨⟨?_, H.ball_subset (hball1 h hha)⟩, hball h hha⟩
  have hφ : Continuous fun t : ℝ ↦ p + t • e := by fun_prop
  -- `p + h e` is in the closure of the positivity set
  have hcl : p + h • e ∈ closure (posSet v U) := by
    have h1 : h ∈ closure S := csInf_mem_closure hne hbdd
    have h2 := image_closure_subset_closure_image hφ ⟨h, h1, rfl⟩
    refine closure_mono ?_ h2
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨H.ball_subset (hball1 t (abs_le.2 ⟨by linarith [ht.1.1], ht.1.2⟩)), ht.2⟩
  -- and not in the positivity set
  have hnot : ¬ 0 < v (p + h • e) := by
    intro hpos
    have hyU : p + h • e ∈ U := H.ball_subset (hball1 h hha)
    have hcont : ContinuousAt (fun t : ℝ ↦ v (p + t • e)) h :=
      ContinuousAt.comp (g := v) (H.continuousOn.continuousAt (H.isOpen.mem_nhds hyU))
        hφ.continuousAt
    obtain ⟨δ, hδ, hδv⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (lt_mem_nhds hpos))
    set t := h - min (δ / 2) (ε / 2) with ht_def
    have hm0 : 0 < min (δ / 2) (ε / 2) := lt_min (by linarith) (by linarith)
    have hm1 : min (δ / 2) (ε / 2) ≤ δ / 2 := min_le_left _ _
    have hm2 : min (δ / 2) (ε / 2) ≤ ε / 2 := min_le_right _ _
    have htS : t ∈ S := by
      refine ⟨⟨by linarith, by linarith⟩, hδv ?_⟩
      rw [Real.dist_eq, ht_def, show h - min (δ / 2) (ε / 2) - h = -min (δ / 2) (ε / 2) by ring,
        abs_neg, abs_of_pos hm0]
      linarith
    have := csInf_le hbdd htS
    linarith
  exact ⟨hcl, fun hint ↦ hnot (interior_subset hint).2⟩

theorem abs_fbHeight_le (H : FlatGraphData U v e ν ε η M α ρ) {z : E d}
    (hz : ‖perpProj e z‖ < 5 / 8) : |fbHeight v e ε z| ≤ ε := by
  have hy := H.fb_graph hz
  have := H.abs_inner_le hy.1 (ball_three_quarters_subset hy.2)
  rwa [inner_add_left, inner_perpProj H.norm_e, real_inner_smul_left,
    real_inner_self_eq_norm_sq, H.norm_e, one_pow, mul_one, zero_add] at this

theorem fbHeight_perpProj (H : FlatGraphData U v e ν ε η M α ρ) (z : E d) :
    fbHeight v e ε (perpProj e z) = fbHeight v e ε z := by
  simp only [fbHeight, perpProj_perpProj H.norm_e]

/-- Uniqueness on vertical lines: two free-boundary points of `B_{3/4}` with
the same projection onto `e^⊥` coincide. -/
theorem eq_of_perpProj_eq (H : FlatGraphData U v e ν ε η M α ρ) {y₁ y₂ : E d}
    (hy₁ : y₁ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4))
    (hy₂ : y₂ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4))
    (hP : perpProj e y₁ = perpProj e y₂) : y₁ = y₂ := by
  have hPw : perpProj e (y₂ - y₁) = 0 := by rw [perpProj_sub, hP, sub_self]
  have hdec : y₂ - y₁ = ⟪y₂ - y₁, e⟫ • e := by
    conv_lhs => rw [← perpProj_add_inner_smul (e := e) (y₂ - y₁)]
    rw [hPw, zero_add]
  have h1 := H.abs_inner_le hy₁.1 (ball_three_quarters_subset hy₁.2)
  have h2 := H.abs_inner_le hy₂.1 (ball_three_quarters_subset hy₂.2)
  have hnorm : ‖y₂ - y₁‖ ≤ ρ / 2 := by
    rw [hdec, norm_smul, H.norm_e, mul_one, Real.norm_eq_abs, inner_sub_left]
    calc |⟪y₂, e⟫ - ⟪y₁, e⟫| ≤ |⟪y₂, e⟫| + |⟪y₁, e⟫| := abs_sub _ _
      _ ≤ ρ / 2 := by linarith [H.ε_le, H.ε_pos]
  have := H.abs_inner_le_norm_perpProj hy₁ hy₂ hnorm
  rw [hPw, norm_zero] at this
  have ht : ⟪y₂ - y₁, e⟫ = 0 := abs_nonpos_iff.1 this
  rw [ht, zero_smul, sub_eq_zero] at hdec
  exact hdec.symm

/-- **The graph identity** on `B_{1/2}`: `y ∈ F(v)` iff `⟪y, e⟫ = fbHeight v e ε y`. -/
theorem mem_freeBoundary_iff (H : FlatGraphData U v e ν ε η M α ρ) {y : E d}
    (hy : y ∈ ball (0 : E d) (1 / 2)) :
    y ∈ freeBoundary v U ↔ ⟪y, e⟫ = fbHeight v e ε y := by
  have hy' : ‖y‖ < 1 / 2 := by rwa [mem_ball, dist_zero_right] at hy
  have hPy : ‖perpProj e y‖ < 5 / 8 := (norm_perpProj_le H.norm_e y).trans_lt (by linarith)
  have hG := H.fb_graph hPy
  have hin : ⟪perpProj e y + fbHeight v e ε y • e, e⟫ = fbHeight v e ε y := by
    rw [inner_add_left, inner_perpProj H.norm_e, real_inner_smul_left,
      real_inner_self_eq_norm_sq, H.norm_e, one_pow, mul_one, zero_add]
  constructor
  · intro hfb
    have hy34 : y ∈ ball (0 : E d) (3 / 4) := ball_subset_ball (by norm_num) hy
    have := H.eq_of_perpProj_eq ⟨hfb, hy34⟩ hG
      (by rw [perpProj_add_smul H.norm_e, perpProj_perpProj H.norm_e])
    have h2 : ⟪y, e⟫ = ⟪perpProj e y + fbHeight v e ε y • e, e⟫ :=
      congrArg (fun x ↦ ⟪x, e⟫) this
    rw [h2, hin]
  · intro heq
    have : y = perpProj e y + fbHeight v e ε y • e := by
      rw [← heq, perpProj_add_inner_smul]
    rw [this]
    exact hG.1

/-- `fbHeight` is `1`-Lipschitz at distances `≤ ρ/4` over `‖perpProj e ·‖ < 5/8`. -/
theorem abs_fbHeight_sub_le (H : FlatGraphData U v e ν ε η M α ρ) {z₁ z₂ : E d}
    (hz₁ : ‖perpProj e z₁‖ < 5 / 8) (hz₂ : ‖perpProj e z₂‖ < 5 / 8)
    (h : ‖z₂ - z₁‖ ≤ ρ / 4) :
    |fbHeight v e ε z₂ - fbHeight v e ε z₁| ≤ ‖perpProj e (z₂ - z₁)‖ := by
  set h₁ := fbHeight v e ε z₁
  set h₂ := fbHeight v e ε z₂
  have hy₁ := H.fb_graph hz₁
  have hy₂ := H.fb_graph hz₂
  have hdiff : (perpProj e z₂ + h₂ • e) - (perpProj e z₁ + h₁ • e) =
      perpProj e (z₂ - z₁) + (h₂ - h₁) • e := by
    rw [perpProj_sub, sub_smul]; abel
  have hP : perpProj e (perpProj e (z₂ - z₁) + (h₂ - h₁) • e) = perpProj e (z₂ - z₁) := by
    rw [perpProj_add_smul H.norm_e, perpProj_perpProj H.norm_e]
  have hin : ⟪perpProj e (z₂ - z₁) + (h₂ - h₁) • e, e⟫ = h₂ - h₁ := by
    rw [inner_add_left, inner_perpProj H.norm_e, real_inner_smul_left,
      real_inner_self_eq_norm_sq, H.norm_e, one_pow, mul_one, zero_add]
  have hb₁ := H.abs_fbHeight_le hz₁
  have hb₂ := H.abs_fbHeight_le hz₂
  have hnorm : ‖perpProj e (z₂ - z₁) + (h₂ - h₁) • e‖ ≤ ρ / 2 := by
    calc ‖perpProj e (z₂ - z₁) + (h₂ - h₁) • e‖
        ≤ ‖perpProj e (z₂ - z₁)‖ + ‖(h₂ - h₁) • e‖ := norm_add_le _ _
      _ = ‖perpProj e (z₂ - z₁)‖ + |h₂ - h₁| := by
        rw [norm_smul, H.norm_e, mul_one, Real.norm_eq_abs]
      _ ≤ ‖z₂ - z₁‖ + (|h₂| + |h₁|) := add_le_add (norm_perpProj_le H.norm_e _) (abs_sub _ _)
      _ ≤ ρ / 2 := by linarith [H.ε_le]
  have := H.abs_inner_le_norm_perpProj hy₁ hy₂ (by rwa [hdiff])
  rwa [hdiff, hP, hin] at this

theorem inv_inner_e_normal_le (H : FlatGraphData U v e ν ε η M α ρ) {z : E d}
    (hz : z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4)) : (⟪e, ν z⟫)⁻¹ ≤ 2 := by
  have := H.inner_e_normal_ge hz
  exact inv_le_of_inv_le₀ (by norm_num) (by linarith [H.η_le])

/-- **Differentiability of the height**: at `z` with `‖perpProj e z‖ < 5/8`,
`fbHeight` has gradient `fbGrad`, with the first-order Taylor bound
`|fbHeight (z + k) - fbHeight z - ⟪fbGrad z, k⟫| ≤ 32 M ‖k‖^{1+α}` (from the cone condition at
the free-boundary point over `z`, at scale `≈ ‖k‖`). -/
theorem hasFDerivAt_fbHeight (H : FlatGraphData U v e ν ε η M α ρ) {z : E d}
    (hz : ‖perpProj e z‖ < 5 / 8) :
    HasFDerivAt (fbHeight v e ε) (innerSL ℝ (fbGrad v e ν ε z)) z := by
  have hρ := H.ρ_pos
  have hM := H.M_nonneg
  refine hasFDerivAt_of_norm_le_rpow (δ := min (ρ / 4) ((5 / 8 - ‖perpProj e z‖) / 2))
    (K := 32 * M) (lt_min (by linarith) (by linarith)) H.α_pos fun k hk ↦ ?_
  have hk1 : ‖k‖ ≤ ρ / 4 := hk.trans (min_le_left _ _)
  have hk2 : ‖k‖ ≤ (5 / 8 - ‖perpProj e z‖) / 2 := hk.trans (min_le_right _ _)
  have hzk : ‖perpProj e (z + k)‖ < 5 / 8 := by
    rw [perpProj_add]
    calc ‖perpProj e z + perpProj e k‖ ≤ ‖perpProj e z‖ + ‖perpProj e k‖ := norm_add_le _ _
      _ ≤ ‖perpProj e z‖ + ‖k‖ := (add_le_add_iff_left _).2 (norm_perpProj_le H.norm_e k)
      _ < 5 / 8 := by linarith
  set y₀ := perpProj e z + fbHeight v e ε z • e with hy₀_def
  set y₁ := perpProj e (z + k) + fbHeight v e ε (z + k) • e with hy₁_def
  set τ := fbHeight v e ε (z + k) - fbHeight v e ε z with hτ_def
  set c := ⟪e, ν y₀⟫ with hc_def
  have hy₀ : y₀ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) := H.fb_graph hz
  have hy₁ : y₁ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) := H.fb_graph hzk
  have hτ : |τ| ≤ ‖perpProj e k‖ := by
    have := H.abs_fbHeight_sub_le hz hzk (by rwa [add_sub_cancel_left])
    rwa [add_sub_cancel_left] at this
  have hPk : ‖perpProj e k‖ ≤ ‖k‖ := norm_perpProj_le H.norm_e k
  have hdiff : y₁ - y₀ = perpProj e k + τ • e := by
    rw [hy₁_def, hy₀_def, hτ_def, perpProj_add, sub_smul]; abel
  have hnorm : ‖y₁ - y₀‖ ≤ 2 * ‖k‖ := by
    rw [hdiff]
    calc ‖perpProj e k + τ • e‖ ≤ ‖perpProj e k‖ + ‖τ • e‖ := norm_add_le _ _
      _ = ‖perpProj e k‖ + |τ| := by rw [norm_smul, H.norm_e, mul_one, Real.norm_eq_abs]
      _ ≤ 2 * ‖k‖ := by linarith
  -- the cone condition at `y₀`
  have hslab : |⟪y₁ - y₀, ν y₀⟫| ≤ 16 * M * ‖k‖ ^ (1 + α) := by
    have hk0 : 0 ≤ ‖k‖ ^ (1 + α) := Real.rpow_nonneg (norm_nonneg _) _
    rcases eq_or_ne y₁ y₀ with heq | hne
    · rw [heq, sub_self, inner_zero_left, abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hM) hk0
    have hs0 : 0 < ‖y₁ - y₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have hs : 2 * ‖y₁ - y₀‖ ∈ Ioc (0 : ℝ) ρ := ⟨mul_pos two_pos hs0, by linarith⟩
    have hmem : y₁ ∈ ball y₀ (2 * ‖y₁ - y₀‖) := by rw [mem_ball, dist_eq_norm]; linarith
    have h1 := H.abs_inner_sub_le hy₀ hy₁.1 hs hmem
    have h2 : (2 * ‖y₁ - y₀‖) ^ (1 + α) ≤ (4 * ‖k‖) ^ (1 + α) :=
      Real.rpow_le_rpow (mul_pos two_pos hs0).le (by linarith) (by linarith [H.α_pos])
    have h3 : (4 * ‖k‖) ^ (1 + α) ≤ 16 * ‖k‖ ^ (1 + α) := by
      rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
      have : (4 : ℝ) ^ (1 + α) ≤ 16 := by
        calc (4 : ℝ) ^ (1 + α) ≤ 4 ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [H.α_le])
          _ = 16 := by norm_num
      exact mul_le_mul_of_nonneg_right this hk0
    calc |⟪y₁ - y₀, ν y₀⟫| ≤ M * (2 * ‖y₁ - y₀‖) ^ (1 + α) := h1
      _ ≤ M * (16 * ‖k‖ ^ (1 + α)) := mul_le_mul_of_nonneg_left (h2.trans h3) hM
      _ = 16 * M * ‖k‖ ^ (1 + α) := by ring
  -- the Taylor remainder is `c⁻¹ ⟪y₁ - y₀, ν y₀⟫`
  have hc : 1 - η ≤ c := H.inner_e_normal_ge hy₀
  have hc0 : c ≠ 0 := by linarith [H.η_le]
  have hg : ⟪fbGrad v e ν ε z, k⟫ = -c⁻¹ * ⟪perpProj e k, ν y₀⟫ := by
    rw [fbGrad, ← hy₀_def, ← hc_def, real_inner_smul_left, inner_perpProj_eq,
      real_inner_comm (perpProj e k) (ν y₀)]
  have hrem : fbHeight v e ε (z + k) - fbHeight v e ε z - innerSL ℝ (fbGrad v e ν ε z) k =
      c⁻¹ * ⟪y₁ - y₀, ν y₀⟫ := by
    rw [innerSL_apply_apply, hg, ← hτ_def, hdiff, inner_add_left, real_inner_smul_left,
      ← hc_def]
    field_simp
    ring
  rw [hrem, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 (by linarith [H.η_le]))]
  calc c⁻¹ * |⟪y₁ - y₀, ν y₀⟫| ≤ 2 * (16 * M * ‖k‖ ^ (1 + α)) :=
        mul_le_mul (H.inv_inner_e_normal_le hy₀) hslab (abs_nonneg _) (by norm_num)
    _ = 32 * M * ‖k‖ ^ (1 + α) := by ring

theorem norm_fbGrad_le (H : FlatGraphData U v e ν ε η M α ρ) {z : E d}
    (hz : ‖perpProj e z‖ < 5 / 8) : ‖fbGrad v e ν ε z‖ ≤ 2 := by
  have hy := H.fb_graph hz
  rw [fbGrad, norm_smul, norm_neg, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (by linarith [H.inner_e_normal_ge hy, H.η_le]))]
  calc _ ≤ 2 * 1 := mul_le_mul (H.inv_inner_e_normal_le hy)
        ((norm_perpProj_le H.norm_e _).trans (H.normal _ hy).2.1.le) (norm_nonneg _)
        (by norm_num)
    _ = 2 := by ring

/-- **Hölder continuity of the gradient of the height** (from `holder_normal`):
`‖fbGrad z₂ - fbGrad z₁‖ ≤ 384 M ‖z₂ - z₁‖^α` for `‖z₂ - z₁‖ ≤ ρ/4`. -/
theorem norm_fbGrad_sub_le (H : FlatGraphData U v e ν ε η M α ρ) {z₁ z₂ : E d}
    (hz₁ : ‖perpProj e z₁‖ < 5 / 8) (hz₂ : ‖perpProj e z₂‖ < 5 / 8)
    (h : ‖z₂ - z₁‖ ≤ ρ / 4) :
    ‖fbGrad v e ν ε z₂ - fbGrad v e ν ε z₁‖ ≤ 384 * M * ‖z₂ - z₁‖ ^ α := by
  set y₁ := perpProj e z₁ + fbHeight v e ε z₁ • e with hy₁_def
  set y₂ := perpProj e z₂ + fbHeight v e ε z₂ • e with hy₂_def
  have hy₁ : y₁ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) := H.fb_graph hz₁
  have hy₂ : y₂ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) := H.fb_graph hz₂
  have hM := H.M_nonneg
  have hα := H.α_pos
  -- `‖y₂ - y₁‖ ≤ 2 ‖z₂ - z₁‖`
  have hτ := H.abs_fbHeight_sub_le hz₁ hz₂ h
  have hP := norm_perpProj_le H.norm_e (z₂ - z₁)
  have hdiff : y₂ - y₁ = perpProj e (z₂ - z₁) +
      (fbHeight v e ε z₂ - fbHeight v e ε z₁) • e := by
    rw [hy₁_def, hy₂_def, perpProj_sub, sub_smul]; abel
  have hnorm : ‖y₂ - y₁‖ ≤ 2 * ‖z₂ - z₁‖ := by
    rw [hdiff]
    calc _ ≤ ‖perpProj e (z₂ - z₁)‖ + ‖(fbHeight v e ε z₂ - fbHeight v e ε z₁) • e‖ :=
          norm_add_le _ _
      _ = ‖perpProj e (z₂ - z₁)‖ + |fbHeight v e ε z₂ - fbHeight v e ε z₁| := by
          rw [norm_smul, H.norm_e, mul_one, Real.norm_eq_abs]
      _ ≤ 2 * ‖z₂ - z₁‖ := by linarith
  have hν : ‖ν y₂ - ν y₁‖ ≤ 64 * M * ‖z₂ - z₁‖ ^ α := by
    have h1 := H.holder_normal hy₁ hy₂ (by linarith)
    have h2 : ‖y₂ - y₁‖ ^ α ≤ (2 * ‖z₂ - z₁‖) ^ α :=
      Real.rpow_le_rpow (norm_nonneg _) hnorm hα.le
    have h3 : (2 * ‖z₂ - z₁‖) ^ α ≤ 2 * ‖z₂ - z₁‖ ^ α := by
      rw [Real.mul_rpow (by norm_num) (norm_nonneg _)]
      have : (2 : ℝ) ^ α ≤ 2 := by
        calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) H.α_le
          _ = 2 := Real.rpow_one 2
      exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (norm_nonneg _) _)
    calc ‖ν y₂ - ν y₁‖ ≤ 32 * M * ‖y₂ - y₁‖ ^ α := h1
      _ ≤ 32 * M * (2 * ‖z₂ - z₁‖ ^ α) :=
          mul_le_mul_of_nonneg_left (h2.trans h3) (mul_nonneg (by norm_num) hM)
      _ = 64 * M * ‖z₂ - z₁‖ ^ α := by ring
  -- the gradient formula
  set c₁ := ⟪e, ν y₁⟫ with hc₁
  set c₂ := ⟪e, ν y₂⟫ with hc₂
  have hc₁0 : 1 - η ≤ c₁ := H.inner_e_normal_ge hy₁
  have hc₂0 : 1 - η ≤ c₂ := H.inner_e_normal_ge hy₂
  have hη := H.η_le
  have hc₁p : 0 < c₁ := by linarith
  have hc₂p : 0 < c₂ := by linarith
  have hsplit : fbGrad v e ν ε z₂ - fbGrad v e ν ε z₁ =
      c₁⁻¹ • perpProj e (ν y₁ - ν y₂) + (c₁⁻¹ - c₂⁻¹) • perpProj e (ν y₂) := by
    simp only [fbGrad, ← hy₁_def, ← hy₂_def, ← hc₁, ← hc₂, perpProj_sub, smul_sub, sub_smul,
      neg_smul]
    abel
  have hcc : |c₁⁻¹ - c₂⁻¹| ≤ 4 * ‖ν y₂ - ν y₁‖ := by
    rw [inv_sub_inv hc₁p.ne' hc₂p.ne', abs_div, abs_of_pos (mul_pos hc₁p hc₂p),
      div_le_iff₀ (mul_pos hc₁p hc₂p)]
    have h1 : |c₂ - c₁| ≤ ‖ν y₂ - ν y₁‖ := by
      rw [hc₁, hc₂, ← inner_sub_right]
      calc _ ≤ ‖e‖ * ‖ν y₂ - ν y₁‖ := abs_real_inner_le_norm _ _
        _ = ‖ν y₂ - ν y₁‖ := by rw [H.norm_e, one_mul]
    have h2 : 1 / 4 ≤ c₁ * c₂ :=
      calc (1 : ℝ) / 4 = 1 / 2 * (1 / 2) := by norm_num
        _ ≤ c₁ * c₂ := mul_le_mul (by linarith) (by linarith) (by norm_num) hc₁p.le
    linarith [mul_le_mul_of_nonneg_left h2 (norm_nonneg (ν y₂ - ν y₁))]
  have hn2 : ‖perpProj e (ν y₂)‖ ≤ 1 :=
    (norm_perpProj_le H.norm_e _).trans (H.normal _ hy₂).2.1.le
  have hn12 : ‖perpProj e (ν y₁ - ν y₂)‖ ≤ ‖ν y₂ - ν y₁‖ := by
    rw [← norm_neg (ν y₂ - ν y₁), neg_sub]; exact norm_perpProj_le H.norm_e _
  rw [hsplit]
  calc _ ≤ ‖c₁⁻¹ • perpProj e (ν y₁ - ν y₂)‖ + ‖(c₁⁻¹ - c₂⁻¹) • perpProj e (ν y₂)‖ :=
        norm_add_le _ _
    _ = c₁⁻¹ * ‖perpProj e (ν y₁ - ν y₂)‖ + |c₁⁻¹ - c₂⁻¹| * ‖perpProj e (ν y₂)‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.2 hc₁p)]
    _ ≤ 2 * ‖ν y₂ - ν y₁‖ + 4 * ‖ν y₂ - ν y₁‖ * 1 :=
        add_le_add (mul_le_mul (H.inv_inner_e_normal_le hy₁) hn12 (norm_nonneg _) zero_le_two)
          (mul_le_mul hcc hn2 (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg _)))
    _ = 6 * ‖ν y₂ - ν y₁‖ := by ring
    _ ≤ 6 * (64 * M * ‖z₂ - z₁‖ ^ α) := mul_le_mul_of_nonneg_left hν (by norm_num)
    _ = 384 * M * ‖z₂ - z₁‖ ^ α := by ring

/-- **Globalization.** Under `FlatGraphData`, `F(v) ∩ B_{1/2}` is the graph over
`e^⊥` of the global `C^{1,α}` function `χ · fbHeight`, where `χ` is a smooth bump equal to `1` on
`B̄_{1/2}` and supported in `B̄_{9/16}`. -/
theorem isC1GammaHypersurfaceNear (H : FlatGraphData U v e ν ε η M α ρ) :
    IsC1GammaHypersurfaceNear (freeBoundary v U) 0 (1 / 2) := by
  let χ : ContDiffBump (0 : E d) := ⟨1 / 2, 9 / 16, by norm_num, by norm_num⟩
  set r : ℝ≥0 := ⟨α, H.α_pos.le⟩ with hr_def
  have hρ := H.ρ_pos
  have hM := H.M_nonneg
  set δ := min (ρ / 4) (1 / 32) with hδ_def
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ ρ / 4 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 32 := min_le_right _ _
  set D : Set (E d) := {z | ‖perpProj e z‖ < 5 / 8} with hD_def
  -- the `δ`-neighbourhood of `tsupport χ` lies in `D`
  have hD : ∀ z w, z ∈ tsupport χ → dist z w ≤ δ → w ∈ D := by
    intro z w hz hzw
    rw [χ.tsupport_eq, mem_closedBall, dist_zero_right] at hz
    change ‖perpProj e w‖ < 5 / 8
    have h1 : perpProj e w = perpProj e z + perpProj e (w - z) := by
      rw [perpProj_sub]; abel
    rw [h1]
    calc ‖perpProj e z + perpProj e (w - z)‖ ≤ ‖perpProj e z‖ + ‖perpProj e (w - z)‖ :=
          norm_add_le _ _
      _ ≤ ‖z‖ + ‖w - z‖ := add_le_add (norm_perpProj_le H.norm_e _) (norm_perpProj_le H.norm_e _)
      _ < 5 / 8 := by
          rw [dist_comm, dist_eq_norm] at hzw
          change ‖z‖ ≤ 9 / 16 at hz
          linarith
  have hB : ∀ z ∈ D, |fbHeight v e ε z| ≤ 2 ∧ ‖innerSL ℝ (fbGrad v e ν ε z)‖ ≤ 2 := by
    intro z hz
    refine ⟨(H.abs_fbHeight_le hz).trans (by linarith [H.ε_le, H.ρ_le]), ?_⟩
    rw [innerSL_apply_norm]
    exact H.norm_fbGrad_le hz
  have hK : ∀ z ∈ D, ∀ w ∈ D, dist z w ≤ δ →
      |fbHeight v e ε z - fbHeight v e ε w| ≤ (1 + 384 * M) * dist z w ∧
      ‖innerSL ℝ (fbGrad v e ν ε z) - innerSL ℝ (fbGrad v e ν ε w)‖ ≤
        (1 + 384 * M) * dist z w ^ (r : ℝ) := by
    intro z hz w hw hzw
    rw [dist_eq_norm] at hzw ⊢
    refine ⟨?_, ?_⟩
    · have := H.abs_fbHeight_sub_le hw hz (hzw.trans hδ1)
      calc _ ≤ ‖perpProj e (z - w)‖ := this
        _ ≤ ‖z - w‖ := norm_perpProj_le H.norm_e _
        _ ≤ (1 + 384 * M) * ‖z - w‖ := le_mul_of_one_le_left (norm_nonneg _) (by linarith)
    · rw [← map_sub, innerSL_apply_norm]
      have := H.norm_fbGrad_sub_le hw hz (hzw.trans hδ1)
      calc _ ≤ 384 * M * ‖z - w‖ ^ α := this
        _ ≤ (1 + 384 * M) * ‖z - w‖ ^ (r : ℝ) := by
          change 384 * M * ‖z - w‖ ^ α ≤ (1 + 384 * M) * ‖z - w‖ ^ α
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  obtain ⟨hcd, C, hC⟩ := exists_contDiff_holderWith_fderiv_mul (χ := χ) (h := fbHeight v e ε)
    (h' := fun z ↦ innerSL ℝ (fbGrad v e ν ε z)) (D := D) (r := r) (δ := δ) (B := 2)
    (K := 1 + 384 * M) (show (0 : ℝ≥0) < r from H.α_pos)
    (show r ≤ 1 by rw [← NNReal.coe_le_coe]; exact H.α_le) hδ0 (by linarith) (by norm_num)
    (by positivity) χ.contDiff χ.hasCompactSupport hD
    (fun z hz ↦ H.hasFDerivAt_fbHeight hz) hB hK
  refine ⟨r, H.α_pos, (show r ≤ 1 by rw [← NNReal.coe_le_coe]; exact H.α_le), e, H.norm_e,
    fun z ↦ χ z * fbHeight v e ε z, C, hcd, hC, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_ofPred_eq, sub_zero]
  constructor
  · rintro ⟨hfb, hy⟩
    refine ⟨hy, ?_⟩
    have hPy : ‖perpProj e y‖ ≤ 1 / 2 := by
      have := norm_perpProj_le H.norm_e y
      rw [mem_ball, dist_zero_right] at hy
      linarith
    have h1 : χ (y - ⟪y, e⟫ • e) = 1 :=
      χ.one_of_mem_closedBall (by rwa [mem_closedBall, dist_zero_right])
    rw [h1, one_mul, show y - ⟪y, e⟫ • e = perpProj e y from rfl, H.fbHeight_perpProj]
    exact (H.mem_freeBoundary_iff hy).1 hfb
  · rintro ⟨hy, heq⟩
    refine ⟨?_, hy⟩
    have hPy : ‖perpProj e y‖ ≤ 1 / 2 := by
      have := norm_perpProj_le H.norm_e y
      rw [mem_ball, dist_zero_right] at hy
      linarith
    have h1 : χ (y - ⟪y, e⟫ • e) = 1 :=
      χ.one_of_mem_closedBall (by rwa [mem_closedBall, dist_zero_right])
    rw [h1, one_mul, show y - ⟪y, e⟫ • e = perpProj e y from rfl, H.fbHeight_perpProj] at heq
    exact (H.mem_freeBoundary_iff hy).2 heq

end FlatGraphData

/-! ### From pointwise flatness to `FlatGraphData` -/

/-- Rescaling `flat_pointwise_C1alpha` at a free-boundary point `z ∈ B_{3/4}` by the factor `4`:
`w y = 4 v (z + y/4)` is `8ε`-flat on `B_1`, so `flat_pointwise_C1alpha` (applied with
`8ε`) gives pointwise flatness of `w` at `0`, which is `IsFlatC1AlphaAt v q z n (32 C₀ ε) α (1/16)`
for `v`. -/
private theorem exists_normal_at {εbar α C₀ : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) (hC₀ : 0 < C₀)
    (H0 : ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
      IsViscSolution U Q u → ‖e‖ = 1 → 0 < ε → ε ≤ εbar →
      (∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2) →
      LipschitzOnWith (ε ^ 2).toNNReal Q (ball 0 1) →
      (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + ε) 0) →
      ∃ ν : E d → E d, ∀ y ∈ freeBoundary u U ∩ ball 0 (1 / 2),
        ‖ν y - e‖ ≤ C₀ * ε ∧ IsFlatC1AlphaAt u Q y (ν y) (C₀ * ε) α (1 / 4))
    {U : Set (E d)} {q v : E d → ℝ} {e : E d} {ε : ℝ} (hU : IsOpen U)
    (hB : ball (0 : E d) 1 ⊆ U) (hv : IsViscSolution U q v) (he : ‖e‖ = 1) (hε : 0 < ε)
    (hεbar : 8 * ε ≤ εbar) (hε1 : ε < 1) (hq : ∀ y ∈ ball (0 : E d) 1, |q y - 1| ≤ ε ^ 2)
    (hLip : LipschitzOnWith (ε ^ 2).toNNReal q (ball 0 1))
    (hflat : ∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ v y ∧ v y ≤ max (⟪y, e⟫ + ε) 0)
    {z : E d} (hz : z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4)) :
    ∃ n : E d, ‖n - e‖ ≤ 32 * C₀ * ε ∧ IsFlatC1AlphaAt v q z n (32 * C₀ * ε) α (1 / 16) := by
  have hz1 : z ∈ ball (0 : E d) 1 := ball_subset_ball (by norm_num) hz.2
  have hz34 : ‖z‖ < 3 / 4 := by simpa using hz.2
  have hze : |⟪z, e⟫| ≤ ε := abs_inner_le_of_flat hU hv.1.1 hflat hz.1 hz1
  -- the affine map `y ↦ z + y/4` maps `B_1` into `B_1`
  have hA : ∀ y ∈ ball (0 : E d) 1, z + (1 / 4 : ℝ) • y ∈ ball (0 : E d) 1 := fun y hy ↦ by
    rw [mem_ball, dist_zero_right] at hy ⊢
    calc ‖z + (1 / 4 : ℝ) • y‖ ≤ ‖z‖ + ‖(1 / 4 : ℝ) • y‖ := norm_add_le _ _
      _ = ‖z‖ + ‖y‖ / 4 := by rw [norm_smul]; norm_num; ring
      _ < 1 := by linarith
  have hvis := hv.rescale z (r := 1 / 4) (s := 1) (by norm_num) one_pos
  have hBz : ball (0 : E d) 1 ⊆ (fun y ↦ z + (1 / 4 : ℝ) • y) ⁻¹' U := fun y hy ↦ hB (hA y hy)
  have hε8 : 0 < 8 * ε := by linarith
  -- the rescaled coefficient
  have hq' : ∀ y ∈ ball (0 : E d) 1, |q (z + (1 / 4 : ℝ) • y) / 1 - 1| ≤ (8 * ε) ^ 2 :=
    fun y hy ↦ by rw [div_one]; exact (hq _ (hA y hy)).trans (by linarith [sq_nonneg ε])
  have hLip' : LipschitzOnWith ((8 * ε) ^ 2).toNNReal (fun y ↦ q (z + (1 / 4 : ℝ) • y) / 1)
      (ball 0 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun y₁ hy₁ y₂ hy₂ ↦ ?_
    have h := hLip.dist_le_mul _ (hA y₁ hy₁) _ (hA y₂ hy₂)
    rw [Real.coe_toNNReal _ (by positivity)] at h ⊢
    simp only [div_one]
    have hd : dist (z + (1 / 4 : ℝ) • y₁) (z + (1 / 4 : ℝ) • y₂) = dist y₁ y₂ / 4 := by
      rw [dist_add_left, dist_smul₀]; norm_num; ring
    rw [hd] at h
    linarith [mul_nonneg (sq_nonneg ε) (dist_nonneg (x := y₁) (y := y₂))]
  -- the rescaled flatness
  have hflat' : ∀ y ∈ ball (0 : E d) 1,
      max (⟪y, e⟫ - 8 * ε) 0 ≤ v (z + (1 / 4 : ℝ) • y) / (1 / 4 * 1) ∧
        v (z + (1 / 4 : ℝ) • y) / (1 / 4 * 1) ≤ max (⟪y, e⟫ + 8 * ε) 0 := by
    intro y hy
    obtain ⟨h1, h2⟩ := hflat _ (hA y hy)
    have hin : ⟪z + (1 / 4 : ℝ) • y, e⟫ = ⟪z, e⟫ + ⟪y, e⟫ / 4 := by
      rw [inner_add_left, real_inner_smul_left]; ring
    rw [hin] at h1 h2
    have hze' := abs_le.1 hze
    rw [show v (z + (1 / 4 : ℝ) • y) / (1 / 4 * 1) = 4 * v (z + (1 / 4 : ℝ) • y) by ring]
    constructor
    · rcases le_total (⟪y, e⟫ - 8 * ε) 0 with h | h
      · rw [max_eq_right h]; linarith [le_max_right (⟪z, e⟫ + ⟪y, e⟫ / 4 - ε) 0]
      · rw [max_eq_left h]; linarith [le_max_left (⟪z, e⟫ + ⟪y, e⟫ / 4 - ε) 0]
    · rcases le_total (⟪z, e⟫ + ⟪y, e⟫ / 4 + ε) 0 with h | h
      · rw [max_eq_right h] at h2; linarith [le_max_right (⟪y, e⟫ + 8 * ε) 0]
      · rw [max_eq_left h] at h2; linarith [le_max_left (⟪y, e⟫ + 8 * ε) 0]
  -- `0` is a free-boundary point of the rescaled function
  have h0 : (0 : E d) ∈ freeBoundary (fun y ↦ v (z + (1 / 4 : ℝ) • y) / (1 / 4 * 1))
      ((fun y ↦ z + (1 / 4 : ℝ) • y) ⁻¹' U) ∩ ball 0 (1 / 2) := by
    refine ⟨?_, by simp⟩
    rw [freeBoundary_rescale z (by norm_num) one_pos]
    simpa using hz.1
  obtain ⟨ν', hν'⟩ := H0 _ _ _ e (8 * ε) (hU.preimage (by fun_prop)) hBz hvis he hε8 hεbar hq'
    hLip' hflat'
  obtain ⟨hne, hn1, hflatn⟩ := hν' 0 h0
  refine ⟨ν' 0, by linarith [mul_pos hC₀ hε], hn1, fun t ht x hx ↦ ?_⟩
  -- transport the flatness at `0` back to `z`
  have hqz : 0 < q z := by
    have := abs_le.1 (hq z hz1)
    have hε1 : ε ^ 2 < 1 := pow_lt_one₀ hε.le hε1 two_ne_zero
    linarith
  set y := (4 : ℝ) • (x - z) with hy_def
  have ht4 : 4 * t ∈ Ioc (0 : ℝ) (1 / 4) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hy : y ∈ ball (0 : E d) (4 * t) := by
    rw [mem_ball, dist_zero_right, hy_def, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    rw [mem_ball, dist_eq_norm] at hx
    linarith
  obtain ⟨hlo, hhi⟩ := hflatn (4 * t) ht4 y hy
  have hzy : z + (1 / 4 : ℝ) • y = x := by
    rw [hy_def, smul_smul]; norm_num
  simp only [hzy, smul_zero, add_zero, div_one, sub_zero] at hlo hhi
  have hiny : ⟪y, ν' 0⟫ = 4 * ⟪x - z, ν' 0⟫ := by rw [hy_def, real_inner_smul_left]
  rw [hiny] at hlo hhi
  have ht0 : 0 < t := ht.1
  have hpow : (4 * t) ^ (1 + α) ≤ 16 * t ^ (1 + α) := by
    rw [Real.mul_rpow (by norm_num) ht0.le]
    have : (4 : ℝ) ^ (1 + α) ≤ 16 := by
      calc (4 : ℝ) ^ (1 + α) ≤ 4 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hα.2])
        _ = 16 := by norm_num
    exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg ht0.le _)
  have hC8 : 0 ≤ C₀ * (8 * ε) := mul_nonneg hC₀.le hε8.le
  have hkey : C₀ * (8 * ε) * (4 * t) ^ (1 + α) ≤ 4 * (32 * C₀ * ε * t ^ (1 + α)) := by
    calc C₀ * (8 * ε) * (4 * t) ^ (1 + α) ≤ C₀ * (8 * ε) * (16 * t ^ (1 + α)) :=
          mul_le_mul_of_nonneg_left hpow hC8
      _ = 4 * (32 * C₀ * ε * t ^ (1 + α)) := by ring
  have h4 : ∀ a : ℝ, 4 * max a 0 = max (4 * a) 0 := fun a ↦ by
    rcases le_total a 0 with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
  constructor
  · have : q z * max (4 * (⟪x - z, ν' 0⟫ - 32 * C₀ * ε * t ^ (1 + α))) 0 ≤ 4 * v x := by
      refine le_trans ?_ (hlo.trans_eq (by ring))
      exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hqz.le
    rw [← h4] at this
    linarith
  · have : 4 * v x ≤ q z * max (4 * (⟪x - z, ν' 0⟫ + 32 * C₀ * ε * t ^ (1 + α))) 0 := by
      refine le_trans (hhi.trans_eq' (by ring)) ?_
      exact mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hqz.le
    rw [← h4] at this
    linarith

/-- **`FlatGraphData` from `flat_pointwise_C1alpha`.** There are `ε₁ > 0`, `α ∈ (0, 1)`
and `C > 0` such that, for `0 < ε ≤ ε₁`, every viscosity solution `v` in `U ⊇ B_1` with
coefficient `q`, `|q - 1| ≤ ε²` and `Lip(q; B_1) ≤ ε²`, which is `ε`-flat on `B_1` in direction
`e`, has normals `ν` with `FlatGraphData U v e ν ε (C ε) (C ε) α (1/16)`, and
`IsFlatC1AlphaAt v q z (ν z) (C ε) α (1/16)` at every free-boundary point `z ∈ B_{3/4}`. -/
theorem exists_flatGraphData (hd : 2 ≤ d) : ∃ ε₁ > 0, ∃ α ∈ Ioo (0 : ℝ) 1, ∃ C > 0,
    ∀ (U : Set (E d)) (q v : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
    IsViscSolution U q v → ‖e‖ = 1 → 0 < ε → ε ≤ ε₁ →
    (∀ y ∈ ball (0 : E d) 1, |q y - 1| ≤ ε ^ 2) → LipschitzOnWith (ε ^ 2).toNNReal q (ball 0 1) →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ v y ∧ v y ≤ max (⟪y, e⟫ + ε) 0) →
    ∃ ν : E d → E d, FlatGraphData U v e ν ε (C * ε) (C * ε) α (1 / 16) ∧
      ∀ z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4),
        IsFlatC1AlphaAt v q z (ν z) (C * ε) α (1 / 16) := by
  obtain ⟨εbar, hεbar, α, hα, C₀, hC₀, H0⟩ := flat_pointwise_C1alpha (d := d) hd
  set C := 32 * C₀ with hC_def
  have hC : 0 < C := by positivity
  refine ⟨min (εbar / 8) (min (1 / 128) (1 / (8 * C))), lt_min (by positivity)
    (lt_min (by norm_num) (by positivity)), α, hα, C, hC,
    fun U q v e ε hU hB hv he hε hε₁ hq hLip hflat ↦ ?_⟩
  have hε1 : ε ≤ εbar / 8 := hε₁.trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / 128 := hε₁.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε3 : ε ≤ 1 / (8 * C) := hε₁.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCε : C * ε ≤ 1 / 8 := by
    rw [le_div_iff₀ (by positivity)] at hε3
    linarith
  have hkey : ∀ z, ∃ n : E d, z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) →
      ‖n - e‖ ≤ C * ε ∧ IsFlatC1AlphaAt v q z n (C * ε) α (1 / 16) := by
    intro z
    by_cases hz : z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4)
    · obtain ⟨n, hn⟩ := exists_normal_at hα hC₀ H0 hU hB hv he hε (by linarith) (by linarith) hq
        hLip hflat hz
      exact ⟨n, fun _ ↦ by rwa [hC_def]⟩
    · exact ⟨0, fun h ↦ absurd h hz⟩
  choose ν hν using hkey
  have hqpos : ∀ z ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4), 0 < q z := fun z hz ↦ by
    have := abs_le.1 (hq z (ball_subset_ball (by norm_num) hz.2))
    have : ε ^ 2 < 1 := pow_lt_one₀ hε.le (by linarith) two_ne_zero
    linarith
  refine ⟨ν, ⟨hU, hB, hv.1.1, he, hflat, hε, by linarith, by norm_num, hα.1, hα.2.le, hCε,
    by positivity, hCε, fun z hz ↦ ⟨(hν z hz).1, (hν z hz).2.isFlatConeAt (hqpos z hz)⟩⟩,
    fun z hz ↦ (hν z hz).2⟩

/-- **The normalized graph theorem** (on `B_{1/2}`). There is `ε₁ > 0` such that
for `0 < ε ≤ ε₁`, every viscosity solution `v` in `U ⊇ B_1` with coefficient `q`,
`|q - 1| ≤ ε²` and `Lip(q; B_1) ≤ ε²`, which is `ε`-flat on `B_1` in direction `e`, has a
`C^{1,γ}` free boundary in `B_{1/2}` (for `2 ≤ d`, which enters through
`flat_pointwise_C1alpha`). -/
theorem isC1GammaHypersurfaceNear_of_flat_normalized (hd : 2 ≤ d) : ∃ ε₁ > 0,
    ∀ (U : Set (E d)) (q v : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
    IsViscSolution U q v → ‖e‖ = 1 → 0 < ε → ε ≤ ε₁ →
    (∀ y ∈ ball (0 : E d) 1, |q y - 1| ≤ ε ^ 2) → LipschitzOnWith (ε ^ 2).toNNReal q (ball 0 1) →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ v y ∧ v y ≤ max (⟪y, e⟫ + ε) 0) →
    IsC1GammaHypersurfaceNear (freeBoundary v U) 0 (1 / 2) := by
  obtain ⟨ε₁, hε₁, α, hα, C, hC, H⟩ := exists_flatGraphData (d := d) hd
  refine ⟨ε₁, hε₁, fun U q v e ε hU hB hv he hε hεle hq hLip hflat ↦ ?_⟩
  obtain ⟨ν, hG, -⟩ := H U q v e ε hU hB hv he hε hεle hq hLip hflat
  exact hG.isC1GammaHypersurfaceNear

end EllipticBernoulli
