/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Harmonic
public import EllipticBernoulli.Harmonic.MaxPrinciple
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Comparison of viscosity sub/superharmonic functions with harmonic functions

Viscosity sub/superharmonicity is `IsViscSubharmonicOn` / `IsViscSuperharmonicOn`:
globally `C^∞` test functions, non-strict touching relative to `Ω`.

* `IsViscSubharmonicOn.laplacian_nonneg_of_eventually_le`: a viscosity subharmonic function may
  be tested by functions that are `C^∞` only on a neighbourhood of the touching point (cut off
  with a smooth bump).
* `IsViscSubharmonicOn.neg`, `IsViscSuperharmonicOn.neg`: the two notions are exchanged by
  `w ↦ -w`.
* `isViscSubharmonicOn_of_laplacian_nonneg`, `isViscSuperharmonicOn_of_laplacian_nonpos`,
  `HarmonicOnNhd.isViscSubharmonicOn`, `HarmonicOnNhd.isViscSuperharmonicOn`: `C²`
  functions with `Δ ≥ 0` (resp. `≤ 0`) are viscosity sub- (resp. super-)harmonic.
* `le_of_frontier_le_of_laplacian_nonpos` (barrier form): on a bounded open set, a
  continuous viscosity subharmonic `w` lies below a `C^∞(Ω) ∩ C(closure Ω)` function `H` with
  `Δ H ≤ 0` in `Ω` if it does so on the frontier. `le_of_le_frontier_of_laplacian_nonneg` is
  the superharmonic dual.
* `le_of_sphere_le_of_laplacian_nonpos_annulus`, `le_of_le_sphere_of_laplacian_nonneg_annulus`:
  the barrier comparison on the annulus `ball z ρ₂ \ closedBall z ρ₁`, with boundary data on the
  two spheres (for the barriers of `Harmonic/Radial.lean`).
* `IsViscSubharmonicOn.le_of_frontier_le` (`ViscSubComparisonStatement`) and
  `IsViscSuperharmonicOn.le_of_le_frontier` (`ViscSuperComparisonStatement`): comparison with
  harmonic functions (Caffarelli–Salsa, Ch. 2).

The barrier form requires `H ∈ C^∞(Ω)` rather than `C²(Ω)` because the test functions of the
viscosity definitions are `C^∞`. Harmonic functions are `C^∞` by Weyl.

## Proof of the comparison

If `w - H > 0` somewhere, `w - H + ε ‖· - c‖²` has an interior maximum at some `x₀ ∈ Ω`
(`exists_isMaxOn_add_sq_of_frontier_nonpos`). Then `P = H - ε ‖· - c‖² + const` touches `w`
from above at `x₀`, is `C^∞` on `Ω`, and `Δ P (x₀) = Δ H (x₀) - 2 d ε < 0`, which contradicts
viscosity subharmonicity (after cutting `P` off with a bump).

## References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
-/

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Testing with locally smooth functions -/

/-- **Local test functions.** If `w` is viscosity subharmonic on the open set `Ω`, `P` is `C^∞`
on an open neighbourhood `V` of `x₀ ∈ Ω`, `P x₀ = w x₀` and `w ≤ P` near `x₀`, then
`0 ≤ Δ P x₀`. -/
theorem IsViscSubharmonicOn.laplacian_nonneg_of_eventually_le {w : E d → ℝ} {Ω : Set (E d)}
    (hΩ : IsOpen Ω) (hw : IsViscSubharmonicOn w Ω) {P : E d → ℝ} {V : Set (E d)}
    (hV : IsOpen V) (hP : ContDiffOn ℝ ∞ P V) {x₀ : E d} (hx₀Ω : x₀ ∈ Ω) (hx₀V : x₀ ∈ V)
    (heq : P x₀ = w x₀) (hle : ∀ᶠ y in 𝓝 x₀, w y ≤ P y) : 0 ≤ Δ P x₀ := by
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem (hV.mem_nhds hx₀V) (hΩ.mem_nhds hx₀Ω)) hle)
  let χ : ContDiffBump x₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  set φ : E d → ℝ := fun y ↦ χ y * P y with hφ_def
  have hts : tsupport χ ⊆ V := by
    rw [χ.tsupport_eq]
    exact fun y hy ↦ (hδsub (closedBall_subset_ball (by simp [χ]; linarith) hy)).1.1
  have hφ : ContDiff ℝ ∞ φ := by
    refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
    by_cases hy : y ∈ V
    · exact χ.contDiff.contDiffAt.mul (hP.contDiffAt (hV.mem_nhds hy))
    · have hy' : y ∉ tsupport χ := fun h ↦ hy (hts h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy'] with z hz
      simp [hφ_def, image_eq_zero_of_notMem_tsupport hz]
  have hφP : φ =ᶠ[𝓝 x₀] P := by
    filter_upwards [ball_mem_nhds x₀ (by positivity : (0 : ℝ) < δ / 4)] with y hy
    simp [hφ_def, χ.one_of_mem_closedBall (ball_subset_closedBall hy)]
  have htouch : TouchesAbove φ w Ω x₀ := by
    refine ⟨hx₀Ω, by rw [hφP.eq_of_nhds, heq], mem_nhdsWithin_of_mem_nhds ?_⟩
    filter_upwards [hφP, ball_mem_nhds x₀ hδ] with y hy1 hy2
    rw [hy1]
    exact (hδsub hy2).2
  have := hw φ hφ x₀ hx₀Ω htouch
  rwa [(laplacian_congr_nhds hφP).eq_of_nhds] at this

/-- Viscosity superharmonic functions are the negatives of viscosity subharmonic ones. -/
theorem IsViscSuperharmonicOn.neg {w : E d → ℝ} {Ω : Set (E d)}
    (hw : IsViscSuperharmonicOn w Ω) : IsViscSubharmonicOn (-w) Ω := by
  intro φ hφ x hx ⟨hxΩ, heq, hle⟩
  have h := hw (-φ) hφ.neg x hx ⟨hxΩ, by simp [heq], by
    filter_upwards [hle] with y hy
    simp only [Pi.neg_apply] at hy ⊢
    linarith⟩
  rw [laplacian_neg, Pi.neg_apply] at h
  linarith

/-- Viscosity subharmonic functions are the negatives of viscosity superharmonic ones. -/
theorem IsViscSubharmonicOn.neg {w : E d → ℝ} {Ω : Set (E d)}
    (hw : IsViscSubharmonicOn w Ω) : IsViscSuperharmonicOn (-w) Ω := by
  intro φ hφ x hx ⟨hxΩ, heq, hle⟩
  have h := hw (-φ) hφ.neg x hx ⟨hxΩ, by simp [heq], by
    filter_upwards [hle] with y hy
    simp only [Pi.neg_apply] at hy ⊢
    linarith⟩
  rw [laplacian_neg, Pi.neg_apply] at h
  linarith

/-! ### Classical sub/superharmonic functions are viscosity sub/superharmonic -/

/-- A `C²` function with `Δ w ≥ 0` on an open set is viscosity subharmonic there. -/
theorem isViscSubharmonicOn_of_laplacian_nonneg {W : Set (E d)} (hW : IsOpen W)
    {w : E d → ℝ} (hw : ContDiffOn ℝ 2 w W) (hΔ : ∀ x ∈ W, 0 ≤ Δ w x) :
    IsViscSubharmonicOn w W := by
  intro φ hφ x hx ⟨_, heq, hle⟩
  rw [hW.nhdsWithin_eq hx] at hle
  have hw₀ : ContDiffAt ℝ 2 w x := hw.contDiffAt (hW.mem_nhds hx)
  have hφ₀ : ContDiffAt ℝ 2 φ x := hφ.contDiffAt.of_le (by norm_cast)
  have hmin : IsLocalMin (φ - w) x := by
    filter_upwards [hle] with y hy
    simp only [Pi.sub_apply, heq, sub_self]
    linarith
  have h := laplacian_nonneg_of_isLocalMin_of_contDiffAt hmin (hφ₀.sub hw₀)
  rw [hφ₀.laplacian_sub hw₀] at h
  linarith [hΔ x hx]

/-- A `C²` function with `Δ w ≤ 0` on an open set is viscosity superharmonic there. -/
theorem isViscSuperharmonicOn_of_laplacian_nonpos {W : Set (E d)} (hW : IsOpen W)
    {w : E d → ℝ} (hw : ContDiffOn ℝ 2 w W) (hΔ : ∀ x ∈ W, Δ w x ≤ 0) :
    IsViscSuperharmonicOn w W := by
  have hw' : ContDiffOn ℝ 2 (-w) W := hw.neg
  have h := (isViscSubharmonicOn_of_laplacian_nonneg hW hw' (fun x hx ↦ by
    rw [laplacian_neg, Pi.neg_apply]; linarith [hΔ x hx])).neg
  simpa using h

/-- A harmonic function on an open set is viscosity subharmonic there. -/
theorem HarmonicOnNhd.isViscSubharmonicOn {W : Set (E d)} (hW : IsOpen W) {h : E d → ℝ}
    (hh : HarmonicOnNhd h W) : IsViscSubharmonicOn h W :=
  isViscSubharmonicOn_of_laplacian_nonneg hW hh.contDiffOn fun x hx ↦
    (hh x hx).2.eq_of_nhds.ge

/-- A harmonic function on an open set is viscosity superharmonic there. -/
theorem HarmonicOnNhd.isViscSuperharmonicOn {W : Set (E d)} (hW : IsOpen W) {h : E d → ℝ}
    (hh : HarmonicOnNhd h W) : IsViscSuperharmonicOn h W :=
  isViscSuperharmonicOn_of_laplacian_nonpos hW hh.contDiffOn fun x hx ↦
    (hh x hx).2.eq_of_nhds.le

/-! ### Comparison with smooth barriers -/

/-- **Comparison with a smooth superharmonic barrier.** On a bounded open set `Ω`
in `E d`, `1 ≤ d`, a continuous viscosity subharmonic `w` lies below a function
`H ∈ C^∞(Ω) ∩ C(closure Ω)` with `Δ H ≤ 0` in `Ω` if `w ≤ H` on `frontier Ω`. -/
theorem le_of_frontier_le_of_laplacian_nonpos (hd : 1 ≤ d) {Ω : Set (E d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {w H : E d → ℝ} (hw : IsViscSubharmonicOn w Ω)
    (hwc : ContinuousOn w (closure Ω)) (hH : ContDiffOn ℝ ∞ H Ω) (hΔ : ∀ x ∈ Ω, Δ H x ≤ 0)
    (hHc : ContinuousOn H (closure Ω)) (hfr : ∀ x ∈ frontier Ω, w x ≤ H x) :
    ∀ x ∈ closure Ω, w x ≤ H x := by
  haveI := nontrivial_E_of_one_le hd
  intro x₁ hx₁
  by_contra hlt
  obtain ⟨c, ε, hε, x₀, hx₀, hmax⟩ := exists_isMaxOn_add_sq_of_frontier_nonpos hΩ hΩb
    (f := w - H) (hwc.sub hHc) (fun x hx ↦ by simpa using hfr x hx) hx₁
    (by simpa using not_le.1 hlt)
  set K : ℝ := (w - H) x₀ + ε * ‖x₀ - c‖ ^ 2 with hK
  set P : E d → ℝ := fun y ↦ H y - ε * ‖y - c‖ ^ 2 + K with hP
  have hq : ContDiff ℝ ∞ (fun y : E d ↦ ε * ‖y - c‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sub_sq c)
  have hPs : ContDiffOn ℝ ∞ P Ω := (hH.sub hq.contDiffOn).add contDiffOn_const
  have hPx : P x₀ = w x₀ := by simp only [hP, hK, Pi.sub_apply]; ring
  have hPle : ∀ᶠ y in 𝓝 x₀, w y ≤ P y := by
    filter_upwards [hΩ.mem_nhds hx₀] with y hy
    have := hmax y (subset_closure hy)
    simp only [Pi.sub_apply] at this
    simp only [hP, hK, Pi.sub_apply]
    linarith
  have hΔP := hw.laplacian_nonneg_of_eventually_le hΩ hΩ hPs hx₀ hx₀ hPx hPle
  have hH₀ : ContDiffAt ℝ 2 H x₀ := (hH.contDiffAt (hΩ.mem_nhds hx₀)).of_le (by norm_cast)
  have hq₀ : ContDiffAt ℝ 2 (fun y : E d ↦ ε * ‖y - c‖ ^ 2) x₀ :=
    hq.contDiffAt.of_le (by norm_cast)
  have hPΔ : Δ P x₀ = Δ H x₀ - ε * (2 * d) := by
    have e1 : P = (H - fun y ↦ ε * ‖y - c‖ ^ 2) + fun _ ↦ K := rfl
    have hHq : ContDiffAt ℝ 2 (H - fun y ↦ ε * ‖y - c‖ ^ 2) x₀ := hH₀.sub hq₀
    rw [e1, hHq.laplacian_add contDiffAt_const, hH₀.laplacian_sub hq₀]
    have e2 : (fun y ↦ ε * ‖y - c‖ ^ 2) = ε • fun y : E d ↦ ‖y - c‖ ^ 2 := rfl
    rw [e2, laplacian_smul ε ((contDiff_norm_sub_sq c).contDiffAt.of_le (by norm_cast)),
      laplacian_norm_sub_sq, finrank_euclideanSpace_fin, smul_eq_mul]
    simp
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have := hΔ x₀ hx₀
  nlinarith

/-- **Comparison with a smooth subharmonic barrier** (dual of
`le_of_frontier_le_of_laplacian_nonpos`). On a bounded open set, a continuous viscosity
superharmonic `w` lies above `H ∈ C^∞(Ω) ∩ C(closure Ω)` with `Δ H ≥ 0` in `Ω` if `H ≤ w` on
`frontier Ω`. -/
theorem le_of_le_frontier_of_laplacian_nonneg (hd : 1 ≤ d) {Ω : Set (E d)} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {w H : E d → ℝ} (hw : IsViscSuperharmonicOn w Ω)
    (hwc : ContinuousOn w (closure Ω)) (hH : ContDiffOn ℝ ∞ H Ω) (hΔ : ∀ x ∈ Ω, 0 ≤ Δ H x)
    (hHc : ContinuousOn H (closure Ω)) (hfr : ∀ x ∈ frontier Ω, H x ≤ w x) :
    ∀ x ∈ closure Ω, H x ≤ w x := by
  intro x hx
  have hH' : ContDiffOn ℝ ∞ (-H) Ω := hH.neg
  have hwc' : ContinuousOn (-w) (closure Ω) := hwc.neg
  have hHc' : ContinuousOn (-H) (closure Ω) := hHc.neg
  have := le_of_frontier_le_of_laplacian_nonpos hd hΩ hΩb hw.neg hwc' hH'
    (fun y hy ↦ by rw [laplacian_neg, Pi.neg_apply]; linarith [hΔ y hy]) hHc'
    (fun y hy ↦ by simp only [Pi.neg_apply]; linarith [hfr y hy]) x hx
  simp only [Pi.neg_apply] at this
  linarith

/-! ### Annuli -/

/-- **Barrier comparison on an annulus, subharmonic side.** On the annulus
`A = ball z ρ₂ \ closedBall z ρ₁`, a continuous viscosity subharmonic `w` lies below
`H ∈ C^∞(A)` with `Δ H ≤ 0` in `A` if `w ≤ H` on both spheres. -/
theorem le_of_sphere_le_of_laplacian_nonpos_annulus (hd : 1 ≤ d) {z : E d} {ρ₁ ρ₂ : ℝ}
    {w H : E d → ℝ} (hw : IsViscSubharmonicOn w (ball z ρ₂ \ closedBall z ρ₁))
    (hwc : ContinuousOn w (closedBall z ρ₂ \ ball z ρ₁))
    (hH : ContDiffOn ℝ ∞ H (ball z ρ₂ \ closedBall z ρ₁))
    (hΔ : ∀ x ∈ ball z ρ₂ \ closedBall z ρ₁, Δ H x ≤ 0)
    (hHc : ContinuousOn H (closedBall z ρ₂ \ ball z ρ₁))
    (h₁ : ∀ x ∈ sphere z ρ₁, w x ≤ H x) (h₂ : ∀ x ∈ sphere z ρ₂, w x ≤ H x) :
    ∀ x ∈ closedBall z ρ₂ \ ball z ρ₁, w x ≤ H x := by
  intro x hx
  have hopen : IsOpen (ball z ρ₂ \ closedBall z ρ₁) := isOpen_ball.sdiff isClosed_closedBall
  by_cases hA : x ∈ ball z ρ₂ \ closedBall z ρ₁
  · refine le_of_frontier_le_of_laplacian_nonpos hd hopen (isBounded_ball.subset diff_subset) hw
      (hwc.mono (closure_annulus_subset z ρ₁ ρ₂)) hH hΔ (hHc.mono (closure_annulus_subset z ρ₁ ρ₂))
      (fun y hy ↦ ?_) x (subset_closure hA)
    rcases frontier_annulus_subset z ρ₁ ρ₂ hy with hy | hy
    exacts [h₁ y hy, h₂ y hy]
  · simp only [mem_diff, mem_closedBall, mem_ball, not_lt, not_and, not_le] at hx hA
    by_cases hlt : dist x z < ρ₂
    · exact h₁ x (le_antisymm (hA hlt) hx.2)
    · exact h₂ x (le_antisymm hx.1 (not_lt.1 hlt))

/-- **Barrier comparison on an annulus, superharmonic side.** On the annulus
`A = ball z ρ₂ \ closedBall z ρ₁`, a continuous viscosity superharmonic `w` lies above
`H ∈ C^∞(A)` with `Δ H ≥ 0` in `A` if `H ≤ w` on both spheres. -/
theorem le_of_le_sphere_of_laplacian_nonneg_annulus (hd : 1 ≤ d) {z : E d} {ρ₁ ρ₂ : ℝ}
    {w H : E d → ℝ} (hw : IsViscSuperharmonicOn w (ball z ρ₂ \ closedBall z ρ₁))
    (hwc : ContinuousOn w (closedBall z ρ₂ \ ball z ρ₁))
    (hH : ContDiffOn ℝ ∞ H (ball z ρ₂ \ closedBall z ρ₁))
    (hΔ : ∀ x ∈ ball z ρ₂ \ closedBall z ρ₁, 0 ≤ Δ H x)
    (hHc : ContinuousOn H (closedBall z ρ₂ \ ball z ρ₁))
    (h₁ : ∀ x ∈ sphere z ρ₁, H x ≤ w x) (h₂ : ∀ x ∈ sphere z ρ₂, H x ≤ w x) :
    ∀ x ∈ closedBall z ρ₂ \ ball z ρ₁, H x ≤ w x := by
  intro x hx
  have hH' : ContDiffOn ℝ ∞ (-H) (ball z ρ₂ \ closedBall z ρ₁) := hH.neg
  have hwc' : ContinuousOn (-w) (closedBall z ρ₂ \ ball z ρ₁) := hwc.neg
  have hHc' : ContinuousOn (-H) (closedBall z ρ₂ \ ball z ρ₁) := hHc.neg
  have := le_of_sphere_le_of_laplacian_nonpos_annulus hd hw.neg hwc' hH'
    (fun y hy ↦ by rw [laplacian_neg, Pi.neg_apply]; linarith [hΔ y hy]) hHc'
    (fun y hy ↦ by simp only [Pi.neg_apply]; linarith [h₁ y hy])
    (fun y hy ↦ by simp only [Pi.neg_apply]; linarith [h₂ y hy]) x hx
  simp only [Pi.neg_apply] at this
  linarith

/-! ### Comparison with harmonic functions -/

/-- Comparison, subharmonic side (`ViscSubComparisonStatement`). -/
theorem IsViscSubharmonicOn.le_of_frontier_le : ViscSubComparisonStatement :=
  fun hd hΩ hΩb hwc hw hhc hh hfr ↦
    le_of_frontier_le_of_laplacian_nonpos hd hΩ hΩb hw hwc (HarmonicOnNhd.contDiffOn_top hΩ hh)
      (fun x hx ↦ (hh x hx).2.eq_of_nhds.le) hhc hfr

/-- Comparison, superharmonic side (`ViscSuperComparisonStatement`). -/
theorem IsViscSuperharmonicOn.le_of_le_frontier : ViscSuperComparisonStatement :=
  fun hd hΩ hΩb hwc hw hhc hh hfr ↦
    le_of_le_frontier_of_laplacian_nonneg hd hΩ hΩb hw hwc (HarmonicOnNhd.contDiffOn_top hΩ hh)
      (fun x hx ↦ (hh x hx).2.eq_of_nhds.ge) hhc hfr

/-- Both comparison statements (`ViscComparisonStatement`). -/
theorem viscComparison : ViscComparisonStatement :=
  ⟨IsViscSubharmonicOn.le_of_frontier_le, IsViscSuperharmonicOn.le_of_le_frontier⟩

end EllipticBernoulli
