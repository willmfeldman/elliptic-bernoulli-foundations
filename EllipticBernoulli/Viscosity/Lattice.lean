/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Viscosity

/-!
# Minima of supersolutions and maxima of subsolutions

* `IsViscSuper.min` (`ViscMinStatement`): the minimum of two viscosity supersolutions is a
  viscosity supersolution.
* `IsViscSub.max` (`ViscMaxStatement`): the maximum of two viscosity subsolutions is a viscosity
  subsolution.

Neither needs `W` open.

## Proof of `IsViscSub.max`

Write `m = max u w` and `S_f = closure (posSet f W) ∩ W`. Since
`posSet m W = posSet u W ∪ posSet w W`, both `S_u` and `S_w` lie in `S_m`. Let `φ₊` touch `m`
from above in `S_m` at `x`, and say `m x = w x` (the other case is symmetric).
* If `x ∈ S_w`, then `φ₊` touches `w` from above in the smaller set `S_w` at `x` (because
  `w ≤ m`), and the subsolution property of `w` applies.
* Otherwise `x ∈ S_u`. As `x ∈ W \ closure (posSet w W)`, `w x ≤ 0`, so `w x = 0`; then
  `0 ≤ u x ≤ m x = w x = 0`, so `m x = u x`, and `φ₊` touches `u` from above in `S_u` at `x`.
-/

open Set Filter Topology
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The minimum of two supersolutions is a supersolution (`ViscMinStatement`). -/
theorem IsViscSuper.min : ViscMinStatement := by
  intro d W Q u w hu hw
  refine ⟨ContinuousOn.inf hu.1 hw.1, fun x hx ↦ le_min (hu.2.1 x hx) (hw.2.1 x hx), ?_⟩
  intro φ hφ x hx htouch
  rcases le_total (u x) (w x) with h | h
  · exact hu.2.2 φ hφ x hx ⟨hx, by rw [htouch.2.1]; exact min_eq_left h,
      htouch.2.2.mono fun y hy ↦ hy.trans (min_le_left _ _)⟩
  · exact hw.2.2 φ hφ x hx ⟨hx, by rw [htouch.2.1]; exact min_eq_right h,
      htouch.2.2.mono fun y hy ↦ hy.trans (min_le_right _ _)⟩

/-- Touching from above passes to a smaller function on a smaller set, provided the two
functions agree at the touching point. -/
private theorem TouchesAbove.of_le_of_subset {ψ m v : E d → ℝ} {S S' : Set (E d)} {x : E d}
    (h : TouchesAbove ψ m S x) (hS : S' ⊆ S) (hx : x ∈ S') (hvx : v x = m x)
    (hvm : ∀ y, v y ≤ m y) : TouchesAbove ψ v S' x :=
  ⟨hx, h.2.1.trans hvx.symm,
    (h.2.2.filter_mono (nhdsWithin_mono x hS)).mono fun y hy ↦ (hvm y).trans hy⟩

/-- `S_f ⊆ S_{max f g}`: the touching set of a subsolution grows under `max`. -/
private theorem closure_posSet_inter_subset_max {W : Set (E d)} (f g : E d → ℝ) :
    closure (posSet f W) ∩ W ⊆ closure (posSet (fun y ↦ max (f y) (g y)) W) ∩ W :=
  inter_subset_inter_left _ (closure_mono fun _ hy ↦ ⟨hy.1, lt_max_of_lt_left hy.2⟩)

/-- `S_g ⊆ S_{max f g}`. -/
private theorem closure_posSet_inter_subset_max' {W : Set (E d)} (f g : E d → ℝ) :
    closure (posSet g W) ∩ W ⊆ closure (posSet (fun y ↦ max (f y) (g y)) W) ∩ W :=
  inter_subset_inter_left _ (closure_mono fun _ hy ↦ ⟨hy.1, lt_max_of_lt_right hy.2⟩)

/-- A point of `S_{max f g}` lies in `S_f` or in `S_g`. -/
private theorem mem_or_mem_of_mem_closure_posSet_max {W : Set (E d)} {f g : E d → ℝ} {x : E d}
    (hx : x ∈ closure (posSet (fun y ↦ max (f y) (g y)) W) ∩ W) :
    x ∈ closure (posSet f W) ∩ W ∨ x ∈ closure (posSet g W) ∩ W := by
  have hunion : posSet (fun y ↦ max (f y) (g y)) W = posSet f W ∪ posSet g W := by
    ext y
    simp only [posSet, mem_ofPred_eq, mem_union, lt_max_iff]
    tauto
  rw [hunion, closure_union] at hx
  rcases hx.1 with h | h
  · exact Or.inl ⟨h, hx.2⟩
  · exact Or.inr ⟨h, hx.2⟩

/-- A nonnegative function vanishes at points of `W` outside the closure of its positivity set. -/
private theorem eq_zero_of_notMem_closure_posSet {W : Set (E d)} {f : E d → ℝ}
    (hf : ∀ y ∈ W, 0 ≤ f y) {x : E d} (hxW : x ∈ W) (hx : x ∉ closure (posSet f W) ∩ W) :
    f x = 0 := by
  refine le_antisymm (not_lt.1 fun hpos ↦ hx ⟨subset_closure ⟨hxW, hpos⟩, hxW⟩) (hf x hxW)

/-- One half of `IsViscSub.max`: the touching point is handled by the subsolution `w` with
`m x = w x` (or, failing `x ∈ S_w`, by `u`). -/
private theorem isViscSub_max_aux {W : Set (E d)} {Q u w : E d → ℝ} (hu : IsViscSub W Q u)
    (hw : IsViscSub W Q w) {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : E d}
    (htouch : TouchesAbove (fun y ↦ max (φ y) 0) (fun y ↦ max (u y) (w y))
      (closure (posSet (fun y ↦ max (u y) (w y)) W) ∩ W) x)
    (hle : u x ≤ w x) :
    0 ≤ Δ φ x ∨ (φ x = 0 ∧ Q x ≤ ‖∇ φ x‖) := by
  have hxW : x ∈ W := htouch.1.2
  by_cases hxw : x ∈ closure (posSet w W) ∩ W
  · exact hw.2.2 φ hφ x (htouch.of_le_of_subset (closure_posSet_inter_subset_max' u w) hxw
      (max_eq_right hle).symm fun y ↦ le_max_right _ _)
  · have hw0 : w x = 0 := eq_zero_of_notMem_closure_posSet hw.2.1 hxW hxw
    have hu0 : u x = 0 := le_antisymm (hle.trans hw0.le) (hu.2.1 x hxW)
    have hxu : x ∈ closure (posSet u W) ∩ W :=
      (mem_or_mem_of_mem_closure_posSet_max htouch.1).resolve_right hxw
    exact hu.2.2 φ hφ x (htouch.of_le_of_subset (closure_posSet_inter_subset_max u w) hxu
      (by simp [hu0, hw0]) fun y ↦ le_max_left _ _)

/-- The maximum of two subsolutions is a subsolution (`ViscMaxStatement`). -/
theorem IsViscSub.max : ViscMaxStatement := by
  intro d W Q u w hu hw
  refine ⟨ContinuousOn.sup hu.1 hw.1, fun x hx ↦ le_max_of_le_left (hu.2.1 x hx), ?_⟩
  intro φ hφ x htouch
  rcases le_total (u x) (w x) with h | h
  · exact isViscSub_max_aux hu hw hφ htouch h
  · have hcomm : (fun y ↦ Max.max (u y) (w y)) = fun y ↦ Max.max (w y) (u y) := by
      funext y; exact max_comm _ _
    rw [hcomm] at htouch
    exact isViscSub_max_aux hw hu hφ htouch h

end EllipticBernoulli

end
