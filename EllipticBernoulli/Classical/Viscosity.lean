/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Classical
import EllipticBernoulli.Viscosity.Calculus
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Classical solutions are viscosity solutions

`IsClassicalSolution U Q u` is the classical solution of Kriventsov–Weiss, Definition 9.1, with
variable `Q`: `u` is
Lipschitz and nonnegative, harmonic in `{u > 0}`, and near each free boundary point `x` the free
boundary is the zero set of a smooth `F` with `∇F(x) ≠ 0`, with the one-sided normal difference
quotient `→ Q(x)` along each unit normal `±∇F(x)/‖∇F(x)‖` that points into `{u > 0}`.

## Main results

* `IsClassicalSolution.ray_dichotomy` (**ray lemma**): at a free boundary point `x`, along each of
  the two unit normals the function `u` is either eventually positive or eventually zero, and at
  least one of the two normals is a positive side.
* `IsClassicalSolution.isViscSuper`, `IsClassicalSolution.isViscSub`.
* `IsClassicalSolution.isViscSolution` (`ClassicalViscStatement`).

## Proof

*Ray lemma.* The implicit function theorem (Mathlib's `implicitToOpenPartialHomeomorph`) straightens
`F` near `x`: in the chart, `{F > 0}` and `{F < 0}` are the two halves of a convex ball, so near `x`
each side `{±F > 0}` is preconnected. Each side misses `frontier {u > 0}` (the free boundary is
`{F = 0}` near `x`), so it lies in `{u > 0}` or outside its closure. The normal rays enter the
sides. Since `x ∈ closure {u > 0}`, some side is positive.

*Supersolution at a free boundary point.* If `φ ≤ u` near `x` with `φ(x) = 0`, then `φ ≤ 0 = φ(x)`
on `{F = 0}` near `x`, so Lagrange multipliers give `∇φ(x) = μ ∇F(x)`. Write `λ = μ ‖∇F(x)‖`, so
`‖∇φ(x)‖ = |λ|`. Along a positive side `s` the difference quotients give `sλ ≤ Q(x)`; along a zero
side, `sλ ≤ 0`. At least one side is positive, so `|λ| ≤ Q(x)`.

*Subsolution at a free boundary point.* No multiplier is needed: along a positive side `ν`,
`u ≤ φ₊` forces `φ(x) = 0` and `Q(x) ≤ max(⟪∇φ(x), ν⟫, 0) ≤ ‖∇φ(x)‖`.

*Interior points* use the touching comparison of Laplacians (`laplacian_le_of_eventually_le`).

Only the one-sided normal difference quotient is used, never `∇u` up to the free boundary; points
with `{u > 0}` on both sides of the free boundary are handled side by side. The hypothesis
`ContinuousOn Q U` of `ClassicalViscStatement` is not used, and no sign condition on `Q` is needed:
`Q(x) ≥ 0` at every free boundary point follows from the positive side.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
  in the Bernoulli one-phase problem*, arXiv:2609.14981.
* D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131. Result numbers are those of arXiv:2306.10131v2.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Calculus along rays -/

public theorem hasDerivAt_ray {φ : E d → ℝ} {x : E d} (hφ : DifferentiableAt ℝ φ x) (v : E d) :
    HasDerivAt (fun t : ℝ ↦ φ (x + t • v)) ⟪∇ φ x, v⟫ 0 := by
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hx0 : x + (0 : ℝ) • v = x := by simp
  have := (hx0 ▸ hφ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  rw [fderiv_apply_eq_inner_gradient, hx0] at this
  exact this

public theorem tendsto_slope_ray {φ : E d → ℝ} {x : E d} (hφ : DifferentiableAt ℝ φ x)
    (v : E d) :
    Tendsto (fun t : ℝ ↦ (φ (x + t • v) - φ x) / t) (𝓝[>] 0) (𝓝 ⟪∇ φ x, v⟫) := by
  refine (hasDerivAt_ray hφ v).tendsto_slope_zero_right.congr' (Eventually.of_forall fun t ↦ ?_)
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  ring

public theorem tendsto_ray (x v : E d) :
    Tendsto (fun t : ℝ ↦ x + t • v) (𝓝[>] 0) (𝓝 x) := by
  have hc : Continuous fun t : ℝ ↦ x + t • v := continuous_const.add (continuous_id.smul
    continuous_const)
  exact (hc.tendsto' 0 x (by simp)).mono_left nhdsWithin_le_nhds

/-- A one-sided comparison of difference quotients: if `φ` touches `u` from below at `x` and the
difference quotient of `u` along `v` tends to `q`, then `⟪∇φ(x), v⟫ ≤ q`. -/
private theorem inner_gradient_le_of_touch {φ u : E d → ℝ} {x v : E d} {q : ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hφx : φ x = u x) (hle : ∀ᶠ y in 𝓝 x, φ y ≤ u y)
    (hq : Tendsto (fun t : ℝ ↦ (u (x + t • v) - u x) / t) (𝓝[>] 0) (𝓝 q)) :
    ⟪∇ φ x, v⟫ ≤ q := by
  refine le_of_tendsto_of_tendsto (tendsto_slope_ray hφ v) hq ?_
  filter_upwards [(tendsto_ray x v).eventually hle, self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  rw [hφx]
  exact div_le_div_of_nonneg_right (by linarith) htpos'.le

/-- The normal rays enter the two sides `{±F > 0}`. -/
public theorem eventually_pos_mul_ray {F : E d → ℝ} {x : E d} (hF : DifferentiableAt ℝ F x)
    (hFx : F x = 0) (hn : ∇ F x ≠ 0) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < s * F (x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x) := by
  have hnorm : 0 < ‖∇ F x‖ := norm_pos_iff.2 hn
  have hval : ⟪∇ F x, (s * ‖∇ F x‖⁻¹) • ∇ F x⟫ = s * ‖∇ F x‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hlim := (tendsto_slope_ray hF ((s * ‖∇ F x‖⁻¹) • ∇ F x)).const_mul s
  rw [hval, hFx] at hlim
  have hpos : 0 < s * (s * ‖∇ F x‖) := by
    rcases hs with rfl | rfl <;> simp [hnorm]
  filter_upwards [hlim.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with t ht htpos
  have htpos' : (0 : ℝ) < t := htpos
  rw [sub_zero, ← mul_div_assoc] at ht
  exact (div_pos_iff_of_pos_right htpos').1 ht

/-! ### The two sides of a smooth hypersurface are locally preconnected -/

/-- **Local sides of a regular level set.** If `F` is smooth with `∇F(x) ≠ 0`, then every
neighbourhood of `x` contains a neighbourhood `N` of `x` on which both sides `{s F > 0}` are
preconnected. Proof: straighten `F` with the implicit function theorem. -/
public theorem exists_nhds_isPreconnected_sides {F : E d → ℝ} {x : E d} (hF : ContDiff ℝ ∞ F)
    (hn : ∇ F x ≠ 0) {V : Set (E d)} (hV : IsOpen V) (hxV : x ∈ V) :
    ∃ N, IsOpen N ∧ x ∈ N ∧ N ⊆ V ∧ ∀ s : ℝ, IsPreconnected (N ∩ {y | 0 < s * F y}) := by
  have hf : HasStrictFDerivAt F (fderiv ℝ F x) x :=
    hF.contDiffAt.hasStrictFDerivAt (by simp)
  have hf'n : fderiv ℝ F x (∇ F x) = ‖∇ F x‖ ^ 2 := by
    rw [fderiv_apply_eq_inner_gradient, real_inner_self_eq_norm_sq]
  have hnorm : ‖∇ F x‖ ≠ 0 := norm_ne_zero_iff.2 hn
  have hsurj : (fderiv ℝ F x).range = ⊤ := by
    refine LinearMap.range_eq_top.2 fun c ↦ ⟨(c / ‖∇ F x‖ ^ 2) • ∇ F x, ?_⟩
    simp only [ContinuousLinearMap.coe_coe, map_smul, hf'n, smul_eq_mul]
    field_simp
  set Φ := hf.implicitToOpenPartialHomeomorph F (fderiv ℝ F x) hsurj with hΦ
  have hxs : x ∈ Φ.source := hf.mem_implicitToOpenPartialHomeomorph_source hsurj
  have hT : IsOpen (Φ.target ∩ Φ.symm ⁻¹' V) :=
    Φ.continuousOn_symm.isOpen_inter_preimage Φ.open_target hV
  have hΦxT : Φ x ∈ Φ.target ∩ Φ.symm ⁻¹' V :=
    ⟨Φ.map_source hxs, by rw [mem_preimage, Φ.left_inv hxs]; exact hxV⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hT _ hΦxT
  have hWt : ball (Φ x) ε ⊆ Φ.target := fun p hp ↦ (hball hp).1
  have hFsymm : ∀ p ∈ Φ.target, F (Φ.symm p) = p.1 := fun p hp ↦ by
    have h := hf.implicitToOpenPartialHomeomorph_fst hsurj (Φ.symm p)
    rw [← hΦ, Φ.right_inv hp] at h
    exact h.symm
  refine ⟨Φ.symm '' ball (Φ x) ε, ?_, ?_, ?_, fun s ↦ ?_⟩
  · rw [Φ.symm_image_eq_source_inter_preimage hWt]
    exact Φ.continuousOn.isOpen_inter_preimage Φ.open_source isOpen_ball
  · rw [Φ.symm_image_eq_source_inter_preimage hWt]
    exact ⟨hxs, mem_ball_self hε⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (hball hp).2
  · have heq : Φ.symm '' ball (Φ x) ε ∩ {y | 0 < s * F y} =
        Φ.symm '' (ball (Φ x) ε ∩ {p | 0 < s * p.1}) := by
      ext y
      constructor
      · rintro ⟨⟨p, hp, rfl⟩, hy⟩
        refine ⟨p, ⟨hp, ?_⟩, rfl⟩
        simpa only [mem_setOf_eq, hFsymm p (hWt hp)] using hy
      · rintro ⟨p, ⟨hp, hps⟩, rfl⟩
        refine ⟨⟨p, hp, rfl⟩, ?_⟩
        simpa only [mem_setOf_eq, hFsymm p (hWt hp)] using hps
    rw [heq]
    have hlin : IsLinearMap ℝ fun p : ℝ × (fderiv ℝ F x).ker ↦ s * p.1 :=
      ⟨fun a b ↦ by simp [mul_add], fun c a ↦ by simp; ring⟩
    have hconv : Convex ℝ (ball (Φ x) ε ∩ {p | 0 < s * p.1}) :=
      (convex_ball _ _).inter (convex_halfSpace_gt hlin 0)
    exact hconv.isPreconnected.image _
      (Φ.continuousOn_symm.mono (inter_subset_left.trans hWt))

/-! ### Elementary facts about classical solutions -/

section Basic

variable {U : Set (E d)} {Q u : E d → ℝ}

public theorem IsClassicalSolution.continuousOn' (hu : IsClassicalSolution U Q u) :
    ContinuousOn u U :=
  let ⟨_, hL⟩ := hu.lipschitzOnWith
  hL.continuousOn

public theorem IsClassicalSolution.isOpen_posSet (hu : IsClassicalSolution U Q u) :
    IsOpen (posSet u U) :=
  hu.continuousOn'.isOpen_inter_preimage hu.isOpen isOpen_Ioi

/-- Off `posSet`, a classical solution vanishes. -/
public theorem IsClassicalSolution.eq_zero_of_notMem (hu : IsClassicalSolution U Q u) {y : E d}
    (hyU : y ∈ U) (hy : y ∉ posSet u U) : u y = 0 :=
  le_antisymm (not_lt.1 fun h ↦ hy ⟨hyU, h⟩) (hu.nonneg y hyU)

public theorem IsClassicalSolution.notMem_posSet_of_mem_freeBoundary
    (hu : IsClassicalSolution U Q u) {y : E d} (hy : y ∈ freeBoundary u U) : y ∉ posSet u U :=
  fun h ↦ hy.1.2 (hu.isOpen_posSet.interior_eq.symm ▸ h)

end Basic

/-! ### The ray lemma -/

public section

variable {U : Set (E d)} {Q u : E d → ℝ}

/-- **Ray lemma.** Let `x` be a free boundary point of a classical solution, and let
`F` be smooth with `∇F(x) ≠ 0` and `{F = 0} = ∂{u > 0}` in `B_r(x)`. Along each unit normal
`ν = s ∇F(x)/‖∇F(x)‖`, `s = ±1`, the function `u` is either eventually positive or eventually zero
(for `t → 0+`), and at least one of the two normals is a positive side. The proof needs no
connected-component argument beyond the local preconnectedness of the two sides `{±F > 0}`,
obtained from the implicit function theorem. -/
theorem IsClassicalSolution.ray_dichotomy (hu : IsClassicalSolution U Q u) {x : E d}
    (hx : x ∈ freeBoundary u U) {r : ℝ} (hr : 0 < r) {F : E d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hn : ∇ F x ≠ 0) (hFB : ball x r ∩ freeBoundary u U = ball x r ∩ {y | F y = 0}) :
    (∀ s : ℝ, (s = 1 ∨ s = -1) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x)) ∨
        ∀ᶠ t in 𝓝[>] (0 : ℝ), u (x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x) = 0) ∧
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x) := by
  have hU := hu.isOpen
  have hP := hu.isOpen_posSet
  have hxU : x ∈ U := hx.2
  have hFx : F x = 0 := by
    have h : x ∈ ball x r ∩ freeBoundary u U := ⟨mem_ball_self hr, hx⟩
    rw [hFB] at h
    exact h.2
  -- off `{F = 0}`, points of `B_r(x) ∩ U` are in `posSet` or outside its closure
  have hsplit : ∀ y ∈ ball x r ∩ U, F y ≠ 0 → y ∈ posSet u U ∪ (closure (posSet u U))ᶜ := by
    rintro y ⟨hyb, hyU⟩ hFy
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    have hfr : y ∈ frontier (posSet u U) := ⟨hcon.2, by rw [hP.interior_eq]; exact hcon.1⟩
    have h : y ∈ ball x r ∩ freeBoundary u U := ⟨hyb, hfr, hyU⟩
    rw [hFB] at h
    exact hFy h.2
  obtain ⟨N, hNo, hxN, hNV, hconn⟩ :=
    exists_nhds_isPreconnected_sides hF hn (isOpen_ball.inter hU) ⟨mem_ball_self hr, hxU⟩
  have hN : N ∈ 𝓝 x := hNo.mem_nhds hxN
  -- each side lies in `posSet` or outside its closure
  have hside : ∀ s : ℝ, N ∩ {y | 0 < s * F y} ⊆ posSet u U ∨
      N ∩ {y | 0 < s * F y} ⊆ (closure (posSet u U))ᶜ := by
    intro s
    refine (hconn s).subset_or_subset hP isClosed_closure.isOpen_compl
      (disjoint_compl_right_iff_subset.2 subset_closure) ?_
    rintro y ⟨hyN, hy⟩
    refine hsplit y (hNV hyN) fun h ↦ ?_
    rw [mem_setOf_eq, h, mul_zero] at hy
    exact lt_irrefl _ hy
  -- the normal rays enter the sides
  have hray : ∀ s : ℝ, (s = 1 ∨ s = -1) → ∀ᶠ t in 𝓝[>] (0 : ℝ),
      x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x ∈ N ∩ {y | 0 < s * F y} := fun s hs ↦
    ((tendsto_ray x _).eventually hN).and
      (eventually_pos_mul_ray (hF.differentiable (by simp) x) hFx hn hs)
  -- sides contained in `posSet` give positive rays
  have hposray : ∀ s : ℝ, (s = 1 ∨ s = -1) → N ∩ {y | 0 < s * F y} ⊆ posSet u U →
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x) := fun s hs hsub ↦
    (hray s hs).mono fun _ ht ↦ (hsub ht).2
  refine ⟨fun s hs ↦ ?_, ?_⟩
  · rcases hside s with hsub | hsub
    · exact Or.inl (hposray s hs hsub)
    · refine Or.inr ((hray s hs).mono fun t ht ↦ ?_)
      exact hu.eq_zero_of_notMem (hNV ht.1).2 fun h ↦ hsub ht (subset_closure h)
  · -- `x ∈ closure (posSet)`, so some side meets `posSet`
    obtain ⟨y, hyN, hyP⟩ := mem_closure_iff_nhds.1 (frontier_subset_closure hx.1) N hN
    have hFy : F y ≠ 0 := by
      intro h
      have hy : y ∈ ball x r ∩ {y | F y = 0} := ⟨(hNV hyN).1, h⟩
      rw [← hFB] at hy
      exact hu.notMem_posSet_of_mem_freeBoundary hy.2 hyP
    have key : ∀ s : ℝ, (s = 1 ∨ s = -1) → 0 < s * F y → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < u (x + t • (s * ‖∇ F x‖⁻¹) • ∇ F x) := by
      intro s hs hsy
      refine ⟨s, hs, hposray s hs ?_⟩
      refine (hside s).resolve_right fun hsub ↦ ?_
      exact hsub ⟨hyN, hsy⟩ (subset_closure hyP)
    rcases hFy.lt_or_gt with h | h
    · exact key (-1) (Or.inr rfl) (by linarith)
    · exact key 1 (Or.inl rfl) (by linarith)

/-- **Local sides of the free boundary.** Near a free boundary point `x`, with `F` as in
`ray_dichotomy`, there is an open neighbourhood `N ⊆ B_r(x) ∩ U` of `x` on which each side
`N ∩ {s F > 0}` is preconnected and lies in `{u > 0}` or outside its closure. -/
theorem IsClassicalSolution.exists_sides (hu : IsClassicalSolution U Q u) {x : E d}
    (hx : x ∈ freeBoundary u U) {r : ℝ} (hr : 0 < r) {F : E d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hn : ∇ F x ≠ 0) (hFB : ball x r ∩ freeBoundary u U = ball x r ∩ {y | F y = 0}) :
    ∃ N, IsOpen N ∧ x ∈ N ∧ N ⊆ ball x r ∩ U ∧ ∀ s : ℝ,
      IsPreconnected (N ∩ {y | 0 < s * F y}) ∧
      (N ∩ {y | 0 < s * F y} ⊆ posSet u U ∨
        N ∩ {y | 0 < s * F y} ⊆ (closure (posSet u U))ᶜ) := by
  have hU := hu.isOpen
  have hP := hu.isOpen_posSet
  have hxU : x ∈ U := hx.2
  have hsplit : ∀ y ∈ ball x r ∩ U, F y ≠ 0 → y ∈ posSet u U ∪ (closure (posSet u U))ᶜ := by
    rintro y ⟨hyb, hyU⟩ hFy
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    have hfr : y ∈ frontier (posSet u U) := ⟨hcon.2, by rw [hP.interior_eq]; exact hcon.1⟩
    have h : y ∈ ball x r ∩ freeBoundary u U := ⟨hyb, hfr, hyU⟩
    rw [hFB] at h
    exact hFy h.2
  obtain ⟨N, hNo, hxN, hNV, hconn⟩ :=
    exists_nhds_isPreconnected_sides hF hn (isOpen_ball.inter hU) ⟨mem_ball_self hr, hxU⟩
  refine ⟨N, hNo, hxN, hNV, fun s ↦ ⟨hconn s, ?_⟩⟩
  refine (hconn s).subset_or_subset hP isClosed_closure.isOpen_compl
    (disjoint_compl_right_iff_subset.2 subset_closure) ?_
  rintro y ⟨hyN, hy⟩
  refine hsplit y (hNV hyN) fun h ↦ ?_
  rw [mem_setOf_eq, h, mul_zero] at hy
  exact lt_irrefl _ hy

/-! ### Classical ⇒ viscosity -/

/-- **Classical solutions are viscosity supersolutions** (Abedin–Feldman–Stinson,
Definition 2.1(i)). -/
theorem IsClassicalSolution.isViscSuper (hu : IsClassicalSolution U Q u) : IsViscSuper U Q u := by
  have hU := hu.isOpen
  have hP := hu.isOpen_posSet
  refine ⟨hu.continuousOn', hu.nonneg, fun φ hφ x hxU htouch ↦ ?_⟩
  obtain ⟨-, hφx, hle⟩ := htouch
  rw [nhdsWithin_eq_nhds.2 (hU.mem_nhds hxU)] at hle
  have hφ2 : ContDiffAt ℝ 2 φ x := hφ.contDiffAt.of_le (by norm_cast)
  by_cases hpos : 0 < u x
  · -- interior point of `{u > 0}`: `u` is harmonic
    left
    have hh := hu.harmonicAt x hxU hpos
    have h := laplacian_le_of_eventually_le hφ2 hh.1 hφx hle
    rwa [hh.2.eq_of_nhds, Pi.zero_apply] at h
  have hux : u x = 0 := le_antisymm (not_lt.1 hpos) (hu.nonneg x hxU)
  by_cases hcl : x ∈ closure (posSet u U)
  swap
  · -- interior point of `{u = 0}`: `φ` has a local maximum
    left
    have hmin : IsLocalMin (-φ) x := by
      filter_upwards [hle, isClosed_closure.isOpen_compl.mem_nhds hcl, hU.mem_nhds hxU]
        with y h1 h2 h3
      have := hu.eq_zero_of_notMem h3 fun h ↦ h2 (subset_closure h)
      simp only [Pi.neg_apply, neg_le_neg_iff, hφx, hux]
      linarith
    have h := laplacian_nonneg_of_isLocalMin hmin hφ2.neg
    rw [laplacian_neg, Pi.neg_apply] at h
    linarith
  -- free boundary point
  right
  have hfb : x ∈ freeBoundary u U :=
    ⟨⟨hcl, fun h ↦ hpos (hP.interior_eq ▸ h).2⟩, hxU⟩
  refine ⟨hφx.trans hux, ?_⟩
  obtain ⟨r, hr, F, hF, hn, hFB, hQ⟩ := hu.free_boundary x hfb
  obtain ⟨hdich, s₀, hs₀, hpos₀⟩ := hu.ray_dichotomy hfb hr hF hn hFB
  have hFx : F x = 0 := by
    have h : x ∈ ball x r ∩ freeBoundary u U := ⟨mem_ball_self hr, hfb⟩
    rw [hFB] at h
    exact h.2
  -- `φ ≤ 0 = φ(x)` on `{F = 0}` near `x`: Lagrange multipliers
  have hmax : IsLocalMaxOn φ {y | F y = F x} x := by
    filter_upwards [nhdsWithin_le_nhds hle, nhdsWithin_le_nhds (ball_mem_nhds x hr),
      nhdsWithin_le_nhds (hU.mem_nhds hxU), self_mem_nhdsWithin] with y h1 h2 h3 h4
    have hy : y ∈ ball x r ∩ {y | F y = 0} := ⟨h2, (show F y = F x from h4).trans hFx⟩
    rw [← hFB] at hy
    have := hu.eq_zero_of_notMem h3 (hu.notMem_posSet_of_mem_freeBoundary hy.2)
    rw [hφx, hux]
    linarith
  have hextr : IsLocalExtrOn φ {y | F y = F x} x := Or.inr hmax
  obtain ⟨a, b, hab, hlag⟩ := hextr.exists_multipliers_of_hasStrictFDerivAt_1d
    (hF.contDiffAt.hasStrictFDerivAt (by simp)) (hφ.contDiffAt.hasStrictFDerivAt (by simp))
  have hlagv : ∀ v, a * ⟪∇ F x, v⟫ + b * ⟪∇ φ x, v⟫ = 0 := fun v ↦ by
    have := congrArg (fun L : StrongDual ℝ (E d) ↦ L v) hlag
    simpa [fderiv_apply_eq_inner_gradient] using this
  have hnorm : 0 < ‖∇ F x‖ := norm_pos_iff.2 hn
  have hb : b ≠ 0 := by
    rintro rfl
    have ha : a ≠ 0 := fun ha ↦ hab (by simp [ha])
    have := hlagv (∇ F x)
    rw [real_inner_self_eq_norm_sq, zero_mul, add_zero] at this
    exact ha (by
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (pow_ne_zero 2 hnorm.ne'))
  -- `∇φ(x) = μ ∇F(x)`
  set μ := -a / b with hμ
  have hgrad : ∇ φ x = μ • ∇ F x := by
    refine ext_inner_right ℝ fun v ↦ ?_
    rw [real_inner_smul_left, hμ]
    have := hlagv v
    field_simp
    linarith
  set lam := μ * ‖∇ F x‖ with hlam
  have hnormφ : ‖∇ φ x‖ = |lam| := by
    rw [hgrad, norm_smul, Real.norm_eq_abs, hlam, abs_mul, abs_of_pos hnorm]
  have hinner : ∀ s : ℝ, ⟪∇ φ x, (s * ‖∇ F x‖⁻¹) • ∇ F x⟫ = s * lam := fun s ↦ by
    rw [hgrad, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hlam]
    field_simp
  have hdiff := hφ.differentiable (by simp) x
  -- side bounds
  have hside : ∀ s : ℝ, (s = 1 ∨ s = -1) → s * lam ≤ Q x ∨ s * lam ≤ 0 := by
    intro s hs
    rcases hdich s hs with hsp | hsz
    · left
      rw [← hinner s]
      exact inner_gradient_le_of_touch hdiff hφx hle (hQ s hs hsp)
    · right
      rw [← hinner s]
      refine inner_gradient_le_of_touch hdiff hφx hle (tendsto_const_nhds.congr' ?_)
      filter_upwards [hsz] with t ht
      rw [ht, hux, sub_zero, zero_div]
  have hs₀Q : s₀ * lam ≤ Q x := by
    rw [← hinner s₀]
    exact inner_gradient_le_of_touch hdiff hφx hle (hQ s₀ hs₀ hpos₀)
  rw [hnormφ]
  rcases hs₀ with rfl | rfl
  · rcases hside (-1) (Or.inr rfl) with h | h
    · exact abs_le.2 ⟨by linarith, by linarith⟩
    · rw [abs_of_nonneg (by linarith)]; linarith
  · rcases hside 1 (Or.inl rfl) with h | h
    · exact abs_le.2 ⟨by linarith, by linarith⟩
    · rw [abs_of_nonpos (by linarith)]; linarith

/-- **Classical solutions are viscosity subsolutions** (Abedin–Feldman–Stinson,
Definition 2.1(ii)). -/
theorem IsClassicalSolution.isViscSub (hu : IsClassicalSolution U Q u) : IsViscSub U Q u := by
  have hU := hu.isOpen
  have hP := hu.isOpen_posSet
  refine ⟨hu.continuousOn', hu.nonneg, fun φ hφ x htouch ↦ ?_⟩
  obtain ⟨⟨hxcl, hxU⟩, hφx, hle⟩ := htouch
  simp only at hφx
  have hφ2 : ContDiffAt ℝ 2 φ x := hφ.contDiffAt.of_le (by norm_cast)
  by_cases hpos : 0 < u x
  · -- interior point of `{u > 0}`
    left
    have hnhds : closure (posSet u U) ∩ U ∈ 𝓝 x :=
      mem_of_superset (hP.mem_nhds ⟨hxU, hpos⟩) fun y hy ↦ ⟨subset_closure hy, hy.1⟩
    rw [nhdsWithin_eq_nhds.2 hnhds] at hle
    have hφpos : 0 < φ x := by
      by_contra h
      rw [max_eq_right (not_lt.1 h)] at hφx
      linarith
    have hφxu : u x = φ x := by rw [← hφx, max_eq_left hφpos.le]
    have hle' : ∀ᶠ y in 𝓝 x, u y ≤ φ y := by
      filter_upwards [hle, hφ.continuous.continuousAt.eventually (lt_mem_nhds hφpos)]
        with y h1 h2
      rwa [max_eq_left h2.le] at h1
    have hh := hu.harmonicAt x hxU hpos
    have h := laplacian_le_of_eventually_le hh.1 hφ2 hφxu hle'
    rwa [hh.2.eq_of_nhds, Pi.zero_apply] at h
  -- free boundary point
  right
  have hux : u x = 0 := le_antisymm (not_lt.1 hpos) (hu.nonneg x hxU)
  have hfb : x ∈ freeBoundary u U :=
    ⟨⟨hxcl, fun h ↦ hpos (hP.interior_eq ▸ h).2⟩, hxU⟩
  obtain ⟨r, hr, F, hF, hn, hFB, hQ⟩ := hu.free_boundary x hfb
  obtain ⟨-, s₀, hs₀, hpos₀⟩ := hu.ray_dichotomy hfb hr hF hn hFB
  set ν := (s₀ * ‖∇ F x‖⁻¹) • ∇ F x with hν
  have hnorm : 0 < ‖∇ F x‖ := norm_pos_iff.2 hn
  have hνnorm : ‖ν‖ = 1 := by
    rw [hν, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_norm]
    rcases hs₀ with rfl | rfl <;> field_simp <;> simp
  -- along the positive side, `u ≤ φ₊`
  have hray : Tendsto (fun t : ℝ ↦ x + t • ν) (𝓝[>] 0) (𝓝[closure (posSet u U) ∩ U] x) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_ray x ν, ?_⟩
    filter_upwards [hpos₀, (tendsto_ray x ν).eventually (hU.mem_nhds hxU)] with t h1 h2
    exact ⟨subset_closure ⟨h2, h1⟩, h2⟩
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), u (x + t • ν) ≤ max (φ (x + t • ν)) 0 := hray.eventually hle
  have hdiff := hφ.differentiable (by simp) x
  -- `φ(x) = 0`
  have hφ0 : φ x = 0 := by
    have hle0 : φ x ≤ 0 := by
      by_contra h
      rw [max_eq_left (not_le.1 h).le] at hφx
      linarith [not_le.1 h]
    refine le_antisymm hle0 (not_lt.1 fun hlt ↦ ?_)
    have hc : Tendsto (fun t : ℝ ↦ φ (x + t • ν)) (𝓝[>] 0) (𝓝 (φ x)) :=
      (hφ.continuous.tendsto x).comp (tendsto_ray x ν)
    obtain ⟨t, h1, h2, h3⟩ := (hev.and (hpos₀.and (hc.eventually (gt_mem_nhds hlt)))).exists
    rw [max_eq_right h3.le] at h1
    linarith
  refine ⟨hφ0, ?_⟩
  -- difference quotients: `Q(x) ≤ max(⟪∇φ(x), ν⟫, 0)`
  have hlimφ : Tendsto (fun t : ℝ ↦ max ((φ (x + t • ν) - φ x) / t) 0) (𝓝[>] 0)
      (𝓝 (max ⟪∇ φ x, ν⟫ 0)) :=
    (tendsto_slope_ray hdiff ν).max tendsto_const_nhds
  have hQle : Q x ≤ max ⟪∇ φ x, ν⟫ 0 := by
    refine le_of_tendsto_of_tendsto (hQ s₀ hs₀ hpos₀) hlimφ ?_
    filter_upwards [hev, self_mem_nhdsWithin] with t h1 htpos
    have htpos' : (0 : ℝ) < t := htpos
    rw [hux, hφ0, sub_zero, sub_zero, div_le_iff₀ htpos', max_mul_of_nonneg _ _ htpos'.le,
      div_mul_cancel₀ _ htpos'.ne', zero_mul]
    exact h1
  refine hQle.trans (max_le ?_ (norm_nonneg _))
  calc ⟪∇ φ x, ν⟫ ≤ ‖∇ φ x‖ * ‖ν‖ := real_inner_le_norm _ _
    _ = ‖∇ φ x‖ := by rw [hνnorm, mul_one]

/-- **Classical solutions are viscosity solutions** (`ClassicalViscStatement`).
The hypothesis `ContinuousOn Q U` is not needed. -/
theorem IsClassicalSolution.isViscSolution : ClassicalViscStatement :=
  fun hu _ ↦ ⟨hu.isViscSuper, hu.isViscSub⟩

end

end EllipticBernoulli
