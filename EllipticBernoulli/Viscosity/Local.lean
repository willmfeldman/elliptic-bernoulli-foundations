/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Viscosity.Basic
public import EllipticBernoulli.Viscosity.Calculus
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Locality of viscosity solutions, zeros above strict subsolutions, barrier comparison

* Locality: the viscosity super/subsolution properties are local (`IsViscSuper.mono`,
  `isViscSuper_of_locally`, `IsViscSub.mono`, `isViscSub_of_locally`), and supersolutions can be
  glued along a closed set (`isViscSuper_piecewise`, `isViscSub_piecewise`).
* `eq_zero_of_mem_freeBoundary`: a continuous nonnegative function vanishes on its free boundary.
* At a zero of a viscosity supersolution lying above a smooth strict subsolution `g`, one has
  `g < 0` (`IsViscSuper.strictSub_lt_zero`), proved with an explicit polynomial test function
  (`IsViscSuper.false_of_touch_strictSub`).
* Comparison of subsolutions with strict `C²` barriers (`IsViscSub.le_max_of_barrier`,
  `IsViscSub.le_max_of_isStrictSuperWith`).

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology Metric Asymptotics
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### A second-order Taylor bound -/

/-- A `C²` function agrees with its first-order Taylor polynomial up to `O(|y - x|²)`. -/
theorem exists_taylor_two_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : F → ℝ} (hg : ContDiff ℝ 2 g) (x : F) :
    ∃ C, ∀ᶠ y in 𝓝 x, |g y - g x - fderiv ℝ g x (y - x)| ≤ C * ‖y - x‖ ^ 2 := by
  have hd : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt
  obtain ⟨C, hC0, hC⟩ := hd.isBigO_sub.exists_pos
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.1 hC.bound
  refine ⟨C, Metric.eventually_nhds_iff.2 ⟨ρ, hρ, fun y hy ↦ ?_⟩⟩
  set r := ‖y - x‖ with hr
  have hs : closedBall x r ⊆ ball x ρ := closedBall_subset_ball (by rwa [hr, ← dist_eq_norm])
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (f := g)
    (f' := fderiv ℝ g) (φ := fderiv ℝ g x) (s := closedBall x r) (C := C * r)
    (x := x) (y := y) (fun z _ ↦ (hg1 z).hasFDerivAt.hasFDerivWithinAt)
    (fun z hz ↦ (hρ' (hs hz)).trans (mul_le_mul_of_nonneg_left
      (by rw [← dist_eq_norm]; exact mem_closedBall.1 hz) hC0.le))
    (convex_closedBall x r) (mem_closedBall_self (norm_nonneg _))
    (by simp [hr, dist_eq_norm])
  rw [Real.norm_eq_abs] at key
  calc _ ≤ C * r * ‖y - x‖ := key
    _ = C * ‖y - x‖ ^ 2 := by rw [hr]; ring

/-! ### Locality -/

section Locality

variable {U W : Set (E d)} {Q u v : E d → ℝ}

/-- Restriction of a viscosity supersolution to an open subset. -/
theorem IsViscSuper.mono (hu : IsViscSuper U Q u) (hW : IsOpen W) (hWU : W ⊆ U) :
    IsViscSuper W Q u := by
  refine ⟨hu.1.mono hWU, fun x hx ↦ hu.2.1 x (hWU hx), fun φ hφ x hx h ↦ ?_⟩
  refine hu.2.2 φ hφ x (hWU hx) ⟨hWU hx, h.2.1, ?_⟩
  have := h.2.2
  rw [hW.nhdsWithin_eq hx] at this
  exact nhdsWithin_le_nhds this

/-- The viscosity supersolution property is local. -/
theorem isViscSuper_of_locally (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ v, IsViscSuper W Q v ∧ EqOn u v W) :
    IsViscSuper U Q u := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun φ hφ x hx htouch ↦ ?_⟩
  · obtain ⟨W, hW, hxW, -, v, hv, heq⟩ := h x hx
    have hc : ContinuousAt v x := hv.1.continuousAt (hW.mem_nhds hxW)
    exact (hc.congr (Filter.mem_of_superset (hW.mem_nhds hxW)
      fun y hy ↦ (heq hy).symm)).continuousWithinAt
  · obtain ⟨W, -, hxW, -, v, hv, heq⟩ := h x hx
    rw [heq hxW]; exact hv.2.1 x hxW
  · obtain ⟨W, hW, hxW, -, v, hv, heq⟩ := h x hx
    have h2 := htouch.2.2
    rw [hU.nhdsWithin_eq hx] at h2
    refine hv.2.2 φ hφ x hxW ⟨hxW, by rw [htouch.2.1, heq hxW], ?_⟩
    rw [hW.nhdsWithin_eq hxW]
    filter_upwards [h2, hW.mem_nhds hxW] with y hy hyW
    rw [← heq hyW]; exact hy

theorem posSet_inter_eq (hWU : W ⊆ U) (heq : EqOn u v W) :
    posSet u U ∩ W = posSet v W := by
  ext y
  simp only [posSet, mem_inter_iff, mem_setOf_eq]
  constructor
  · rintro ⟨⟨-, hy⟩, hyW⟩; exact ⟨hyW, by rwa [← heq hyW]⟩
  · rintro ⟨hyW, hy⟩; exact ⟨⟨hWU hyW, by rwa [heq hyW]⟩, hyW⟩

/-- Near a point of an open `W ⊆ U` on which `u = v`, the touching sets
`\overline{{u > 0}} ∩ U` and `\overline{{v > 0}} ∩ W` agree. -/
theorem closure_posSet_inter_eq (hW : IsOpen W) (hWU : W ⊆ U) (heq : EqOn u v W) :
    closure (posSet u U) ∩ U ∩ W = closure (posSet v W) ∩ W := by
  apply Subset.antisymm
  · rintro y ⟨⟨hy, -⟩, hyW⟩
    refine ⟨?_, hyW⟩
    have := hW.inter_closure ⟨hyW, hy⟩
    rwa [inter_comm, posSet_inter_eq hWU heq] at this
  · rintro y ⟨hy, hyW⟩
    refine ⟨⟨closure_mono ?_ hy, hWU hyW⟩, hyW⟩
    rw [← posSet_inter_eq hWU heq]; exact inter_subset_left

/-- Restriction of a viscosity subsolution to an open subset. -/
theorem IsViscSub.mono (hu : IsViscSub U Q u) (hW : IsOpen W) (hWU : W ⊆ U) :
    IsViscSub W Q u := by
  refine ⟨hu.1.mono hWU, fun x hx ↦ hu.2.1 x (hWU hx), fun φ hφ x h ↦ ?_⟩
  have hxW : x ∈ W := h.1.2
  have hS := closure_posSet_inter_eq (u := u) (v := u) hW hWU (fun _ _ ↦ rfl)
  refine hu.2.2 φ hφ x ⟨⟨closure_mono (posSet_inter_eq (u := u) hWU (fun _ _ ↦ rfl) ▸
    inter_subset_left) h.1.1, hWU hxW⟩, h.2.1, ?_⟩
  rw [nhdsWithin_restrict _ hxW hW, hS]
  exact h.2.2

/-- The viscosity subsolution property is local. -/
theorem isViscSub_of_locally
    (h : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ ∃ v, IsViscSub W Q v ∧ EqOn u v W) :
    IsViscSub U Q u := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_, fun φ hφ x htouch ↦ ?_⟩
  · obtain ⟨W, hW, hxW, -, v, hv, heq⟩ := h x hx
    have hc : ContinuousAt v x := hv.1.continuousAt (hW.mem_nhds hxW)
    exact (hc.congr (Filter.mem_of_superset (hW.mem_nhds hxW)
      fun y hy ↦ (heq hy).symm)).continuousWithinAt
  · obtain ⟨W, -, hxW, -, v, hv, heq⟩ := h x hx
    rw [heq hxW]; exact hv.2.1 x hxW
  · obtain ⟨W, hW, hxW, hWU, v, hv, heq⟩ := h x htouch.1.2
    have hS := closure_posSet_inter_eq hW hWU heq
    have hxS : x ∈ closure (posSet v W) ∩ W := by rw [← hS]; exact ⟨htouch.1, hxW⟩
    refine hv.2.2 φ hφ x ⟨hxS, by rw [htouch.2.1, heq hxW], ?_⟩
    have h2 := htouch.2.2
    rw [nhdsWithin_restrict _ hxW hW, hS] at h2
    filter_upwards [h2, self_mem_nhdsWithin] with y hy hyS
    rw [← heq hyS.2]; exact hy

open Classical in
/-- **Gluing.** If `u` is a viscosity supersolution in `U`, `v` one in an open `W ⊆ U`, and
`v = u` on `W \ K` for a closed `K ⊆ W`, then the function equal to `v` on `W` and to `u`
elsewhere is a viscosity supersolution in `U`. -/
theorem isViscSuper_piecewise (hU : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) {K : Set (E d)}
    (hK : IsClosed K) (hKW : K ⊆ W) (hu : IsViscSuper U Q u) (hv : IsViscSuper W Q v)
    (heq : ∀ y ∈ W \ K, v y = u y) : IsViscSuper U Q (W.piecewise v u) := by
  refine isViscSuper_of_locally hU fun x hx ↦ ?_
  by_cases hxW : x ∈ W
  · exact ⟨W, hW, hxW, hWU, v, hv, fun y hy ↦ piecewise_eq_of_mem _ _ _ hy⟩
  · refine ⟨U \ K, hU.sdiff hK, ⟨hx, fun h ↦ hxW (hKW h)⟩, diff_subset, u,
      hu.mono (hU.sdiff hK) diff_subset, fun y hy ↦ ?_⟩
    by_cases hyW : y ∈ W
    · rw [piecewise_eq_of_mem _ _ _ hyW]; exact heq y ⟨hyW, hy.2⟩
    · exact piecewise_eq_of_notMem _ _ _ hyW

open Classical in
/-- **Gluing** for viscosity subsolutions (same hypotheses as `isViscSuper_piecewise`). -/
theorem isViscSub_piecewise (hU : IsOpen U) (hW : IsOpen W) (hWU : W ⊆ U) {K : Set (E d)}
    (hK : IsClosed K) (hKW : K ⊆ W) (hu : IsViscSub U Q u) (hv : IsViscSub W Q v)
    (heq : ∀ y ∈ W \ K, v y = u y) : IsViscSub U Q (W.piecewise v u) := by
  refine isViscSub_of_locally fun x hx ↦ ?_
  by_cases hxW : x ∈ W
  · exact ⟨W, hW, hxW, hWU, v, hv, fun y hy ↦ piecewise_eq_of_mem _ _ _ hy⟩
  · refine ⟨U \ K, hU.sdiff hK, ⟨hx, fun h ↦ hxW (hKW h)⟩, diff_subset, u,
      hu.mono (hU.sdiff hK) diff_subset, fun y hy ↦ ?_⟩
    by_cases hyW : y ∈ W
    · rw [piecewise_eq_of_mem _ _ _ hyW]; exact heq y ⟨hyW, hy.2⟩
    · exact piecewise_eq_of_notMem _ _ _ hyW

end Locality

/-! ### Supersolutions above a strict subsolution -/

/-- At a free boundary point, a continuous nonnegative function vanishes. -/
theorem eq_zero_of_mem_freeBoundary {U : Set (E d)} {u : E d → ℝ} (hU : IsOpen U)
    (hc : ContinuousOn u U) (hnn : ∀ y ∈ U, 0 ≤ u y) {x : E d} (hx : x ∈ freeBoundary u U) :
    u x = 0 := by
  refine le_antisymm (not_lt.1 fun hpos ↦ ?_) (hnn x hx.2)
  apply hx.1.2
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [hU.mem_nhds hx.2,
    (hc.continuousAt (hU.mem_nhds hx.2)).eventually (lt_mem_nhds hpos)] with y hyU hy
  exact ⟨hyU, hy⟩

/-- **Supersolutions above a strict subsolution, test-function step.** Let `u` be a viscosity
supersolution in `U`, `x ∈ U` with `u(x) = 0`, and `g ∈ C²` with `g ≤ u` in `U`, `g(x) = 0` and
`|∇g(x)| > Q(x) > 0`. This is impossible: with `ν = ∇g(x)/|∇g(x)|`, `s = (y - x)·ν` and
`Q(x) < λ < |∇g(x)|`, the polynomial `φ(y) = λ s + B s² - K |y - x|²` (with `K` a second-order
Taylor constant of `g` and `B = dK + 1`) touches `u` from below at `x` and has `Δφ = 2 > 0`,
`|∇φ(x)| = λ > Q(x)`. -/
theorem IsViscSuper.false_of_touch_strictSub {U : Set (E d)} {Q u g : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) {x : E d} (hx : x ∈ U) (hux : u x = 0)
    (hgu : ∀ y ∈ U, g y ≤ u y) (hg : ContDiff ℝ 2 g) (hgx : g x = 0) (hQ : 0 < Q x)
    (hgrad : Q x < ‖∇ g x‖) : False := by
  set a := ‖∇ g x‖ with ha_def
  have ha : 0 < a := hQ.trans hgrad
  set ν : E d := a⁻¹ • ∇ g x with hν_def
  have hν : ‖ν‖ = 1 := by
    rw [hν_def, norm_smul, norm_inv, norm_norm, ← ha_def, inv_mul_cancel₀ ha.ne']
  have hgν : ∇ g x = a • ν := by rw [hν_def, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hfd : ∀ w, fderiv ℝ g x w = a * ⟪w, ν⟫ := by
    intro w
    have : fderiv ℝ g x w = ⟪∇ g x, w⟫ := (InnerProductSpace.toDual_symm_apply).symm
    rw [this, hgν, real_inner_smul_left, real_inner_comm]
  set lam := (Q x + a) / 2 with hlam
  have hlam1 : Q x < lam := by rw [hlam]; linarith
  have hlam2 : lam < a := by rw [hlam]; linarith
  have hlam0 : 0 < lam := hQ.trans hlam1
  obtain ⟨C, hC⟩ := exists_taylor_two_bound hg x
  set K := max C 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hCK : C ≤ K := le_max_left _ _
  set B : ℝ := (d : ℝ) * K + 1 with hB
  have hB0 : 0 < B := by positivity
  set φ : E d → ℝ := fun y ↦ lam * ⟪y - x, ν⟫ + B * ⟪y - x, ν⟫ ^ 2 - K * ‖y - x‖ ^ 2
    with hφ_def
  have hφ : ContDiff ℝ ∞ φ := by
    have h1 : ContDiff ℝ ∞ fun y : E d ↦ ⟪y - x, ν⟫ :=
      (contDiff_id.sub contDiff_const).inner ℝ contDiff_const
    have h2 : ContDiff ℝ ∞ fun y : E d ↦ ‖y - x‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    exact ((contDiff_const.mul h1).add (contDiff_const.mul (h1.pow 2))).sub
      (contDiff_const.mul h2)
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth hφ
  -- the 2-jet of `φ` at `x`
  have hjet : ∀ w : E d, φ x = 0 ∧ fderiv ℝ φ x w = lam * ⟪w, ν⟫ ∧
      iteratedFDeriv ℝ 2 φ x ![w, w] = 2 * (B * ⟪w, ν⟫ ^ 2 - K * ‖w‖ ^ 2) := by
    intro w
    refine iteratedFDeriv_two_eq_of_isLittleO hφ2 ((isLittleO_zero _ _).congr_left fun t ↦ ?_)
    simp only [hφ_def, add_sub_cancel_left, real_inner_smul_left, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hφx : φ x = 0 := (hjet 0).1
  have hlap : Δ φ x = 2 := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp_rw [fun i ↦ (hjet ((EuclideanSpace.basisFun (Fin d) ℝ) i)).2.2]
    have hn : ∀ i, ‖(EuclideanSpace.basisFun (Fin d) ℝ) i‖ = 1 :=
      fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.1 i
    have hs : ∑ i, ⟪(EuclideanSpace.basisFun (Fin d) ℝ) i, ν⟫ ^ 2 = 1 := by
      have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner ν ν
      rw [real_inner_self_eq_norm_sq, hν, one_pow] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [real_inner_comm ν, sq]
    simp_rw [hn, one_pow, mul_one, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hs, hB]
    ring
  have hgradφ : lam ≤ ‖∇ φ x‖ := by
    have h1 : ⟪∇ φ x, ν⟫ = lam := by
      have : ⟪∇ φ x, ν⟫ = fderiv ℝ φ x ν := InnerProductSpace.toDual_symm_apply
      rw [this, (hjet ν).2.1, real_inner_self_eq_norm_sq, hν]; ring
    have h2 := real_inner_le_norm (∇ φ x) ν
    rw [hν, mul_one, h1] at h2
    exact h2
  -- `φ` touches `u` from below at `x`
  set ρ := min ((a - lam) / B) (lam / B) with hρ
  have hρ0 : 0 < ρ := lt_min (div_pos (by linarith) hB0) (div_pos hlam0 hB0)
  have htouch : TouchesBelow φ u U x := by
    refine ⟨hx, by rw [hφx, hux], mem_nhdsWithin_of_mem_nhds ?_⟩
    filter_upwards [hU.mem_nhds hx, hC, ball_mem_nhds x hρ0] with y hyU hyC hyρ
    have hu0 := hu.2.1 y hyU
    have hgy := hgu y hyU
    rw [hgx, sub_zero, hfd] at hyC
    set s := ⟪y - x, ν⟫ with hs
    set r := ‖y - x‖ with hr
    have hsr : |s| ≤ r := by
      have := abs_real_inner_le_norm (y - x) ν
      rwa [hν, mul_one] at this
    have hrρ : r < ρ := by rw [hr, ← dist_eq_norm]; exact hyρ
    have hBr1 : B * r < a - lam := by
      have := (lt_of_lt_of_le hrρ (min_le_left _ _))
      rwa [lt_div_iff₀ hB0, mul_comm] at this
    have hBr2 : B * r < lam := by
      have := (lt_of_lt_of_le hrρ (min_le_right _ _))
      rwa [lt_div_iff₀ hB0, mul_comm] at this
    have hBs : B * |s| ≤ B * r := mul_le_mul_of_nonneg_left hsr hB0.le
    have hr0 : 0 ≤ r ^ 2 := sq_nonneg _
    have hKC : C * r ^ 2 ≤ K * r ^ 2 := mul_le_mul_of_nonneg_right hCK hr0
    have hKr : 0 ≤ K * r ^ 2 := mul_nonneg hK0 hr0
    change lam * s + B * s ^ 2 - K * r ^ 2 ≤ u y
    rcases le_or_gt s 0 with hs0 | hs0
    · rw [abs_of_nonpos hs0] at hBs
      have : 0 ≤ lam + B * s := by linarith
      have : s * (lam + B * s) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs0 this
      linarith
    · rw [abs_of_pos hs0] at hBs
      have hgl := (abs_le.1 hyC).1
      have : 0 ≤ s * (a - lam - B * s) := mul_nonneg hs0.le (by linarith)
      linarith
  rcases hu.2.2 φ hφ x hx htouch with h | ⟨-, h⟩
  · rw [hlap] at h; norm_num at h
  · linarith

/-- **Supersolutions above a strict subsolution.** If `u` is a viscosity supersolution in `U` with
`u ≥ g` in `U`, where `g` is a smooth strict subsolution and `Q > 0`, then `g(x) < 0` at every
zero `x ∈ U` of `u`. The proof of Abedin–Feldman–Stinson, Lemma 2.7, claims `u > g` in `U`
because `u` cannot touch `g` from above; this does not follow directly, since `Δg ≥ 0` is not
strict. The weaker fact here is what the argument needs. -/
theorem IsViscSuper.strictSub_lt_zero {U : Set (E d)} {Q u g : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) (hg : IsStrictSub U Q g) (hgu : ∀ y ∈ U, g y ≤ u y) {x : E d}
    (hx : x ∈ U) (hux : u x = 0) (hQ : 0 < Q x) : g x < 0 := by
  obtain ⟨hg2, a₀, ha₀, δ₀, hδ₀, -, h2⟩ := hg
  refine lt_of_le_of_ne (hux ▸ hgu x hx) fun hgx ↦ ?_
  have hq := h2 x (subset_closure hx) (by rw [hgx, abs_zero]; exact ha₀.le)
  have hlt : Q x ^ 2 < ‖∇ g x‖ ^ 2 := by
    have : 0 < δ₀ * Q x ^ 2 := by positivity
    linarith
  exact hu.false_of_touch_strictSub hU hx hux hgu hg2 hgx hQ
    (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt)

/-! ### Comparison with strict `C²` barriers -/

/-- **Comparison with a strict barrier.** Let `v` be a viscosity subsolution in an open `W`,
`K ⊆ W` compact and `H ∈ C²` with `ΔH < 0` on `K` and `|∇H| < Q` at the points of `K` where
`H < 0`. If `v ≤ H₊` on `W \ K`, then `v ≤ H₊` on `K`.

Proof: otherwise let `t > 0` be the maximum of `v - H` over `\overline{{v > 0} ∩ K}`, attained at
`z`; then `v ≤ (H + t)₊` on `W` with equality at `z`, and a smooth quadratic majorant of `H + t`
at `z` (`exists_smooth_ge_of_contDiff_two`) contradicts the subsolution property at `z`. -/
theorem IsViscSub.le_max_of_barrier {W K : Set (E d)} {Q v H : E d → ℝ} (hd : 0 < d)
    (hW : IsOpen W) (hv : IsViscSub W Q v) (hK : IsCompact K) (hKW : K ⊆ W)
    (hH : ContDiff ℝ 2 H) (hlap : ∀ z ∈ K, Δ H z < 0)
    (hgrad : ∀ z ∈ K, H z < 0 → ‖∇ H z‖ < Q z)
    (hout : ∀ y ∈ W \ K, v y ≤ max (H y) 0) : ∀ y ∈ K, v y ≤ max (H y) 0 := by
  intro y hy
  by_contra hcon
  push Not at hcon
  have hvy : 0 < v y := lt_of_le_of_lt (le_max_right _ _) hcon
  have hHy : H y < v y := lt_of_le_of_lt (le_max_left _ _) hcon
  set A := posSet v W ∩ K with hA
  have hAK : closure A ⊆ K := hK.isClosed.closure_subset_iff.2 inter_subset_right
  have hAc : IsCompact (closure A) := hK.of_isClosed_subset isClosed_closure hAK
  have hF : ContinuousOn (fun w ↦ v w - H w) (closure A) :=
    ((hv.1.mono (hAK.trans hKW)).sub hH.continuous.continuousOn)
  have hyA : y ∈ A := ⟨⟨hKW hy, hvy⟩, hy⟩
  obtain ⟨z, hzA, hzmax⟩ := hAc.exists_isMaxOn ⟨y, subset_closure hyA⟩ hF
  set t := v z - H z with ht
  have hty : v y - H y ≤ t := hzmax (subset_closure hyA)
  have ht0 : 0 < t := by linarith
  have hzK : z ∈ K := hAK hzA
  have hzW : z ∈ W := hKW hzK
  have hle : ∀ w ∈ W, v w ≤ max (H w + t) 0 := by
    intro w hw
    by_cases hwK : w ∈ K
    · by_cases hvw : 0 < v w
      · have := hzmax (subset_closure (⟨⟨hw, hvw⟩, hwK⟩ : w ∈ A))
        simp only [mem_setOf_eq] at this
        exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (not_lt.1 hvw)
    · exact (hout w ⟨hw, hwK⟩).trans (max_le_max (by linarith) le_rfl)
  set η : ℝ := -Δ H z / (4 * d) with hη
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hη0 : 0 < η := div_pos (by linarith [hlap z hzK]) (by positivity)
  obtain ⟨φ, hφs, hφz, hφg, hφl, hφle⟩ := exists_smooth_ge_of_contDiff_two
    (hH.add (contDiff_const (c := t))) z hη0
  rw [laplacian_add_const hH.contDiffAt, finrank_euclideanSpace_fin] at hφl
  rw [gradient_add_const] at hφg
  have hvz : v z = H z + t := by rw [ht]; ring
  have htouch : TouchesAbove (fun w ↦ max (φ w) 0) v (closure (posSet v W) ∩ W) z := by
    refine ⟨⟨closure_mono inter_subset_left hzA, hzW⟩, ?_, ?_⟩
    · have hφv : φ z = v z := by rw [hφz]; exact hvz.symm
      simp only [hφv]; exact max_eq_left (hv.2.1 z hzW)
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hzW),
        mem_nhdsWithin_of_mem_nhds hφle] with w hw hw'
      exact (hle w hw).trans (max_le_max hw' le_rfl)
  rcases hv.2.2 φ hφs z htouch with h | ⟨h1, h2⟩
  · have : Δ φ z = Δ H z / 2 := by
      rw [hφl, hη]; field_simp; ring
    linarith [hlap z hzK]
  · have hHz : H z < 0 := by rw [hφz] at h1; linarith
    have := hgrad z hzK hHz
    rw [hφg] at h2
    linarith

/-- **Barrier step of the dual of Lemma 2.5.** Let `g` be a strict supersolution with constants
`a₀, δ₀`, and `B̄_r(x) ⊆ U` a ball on which `g > -a₀/2` and `Q ≥ q₀ > 0`. If `v` is a viscosity
subsolution in `B_r(x)`, `K ⊆ B_r(x)` is compact and `v ≤ g₊` on `B_r(x) \ K`, then `v ≤ g₊` on
`K`. (Comparison with the barriers `g + ε(r² - |y - x|²)`, `ε → 0`.) -/
theorem IsViscSub.le_max_of_isStrictSuperWith {U : Set (E d)} {Q g v : E d → ℝ} (hd : 0 < d)
    {a₀ δ₀ : ℝ} (hg : IsStrictSuperWith U Q g a₀ δ₀) {x : E d} {r : ℝ}
    (hBU : closedBall x r ⊆ U) (hga : ∀ y ∈ closedBall x r, -a₀ / 2 < g y) {q₀ : ℝ}
    (hq₀ : 0 < q₀) (hQ : ∀ y ∈ closedBall x r, q₀ ≤ Q y) (hv : IsViscSub (ball x r) Q v)
    {K : Set (E d)} (hK : IsCompact K) (hKB : K ⊆ ball x r)
    (hout : ∀ y ∈ ball x r \ K, v y ≤ max (g y) 0) : ∀ y ∈ K, v y ≤ max (g y) 0 := by
  obtain ⟨hg2, ha₀, hδ₀, hg1, hg2'⟩ := hg
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  -- the paraboloid `ψ(y) = r² - |y - x|²`
  set ψ : E d → ℝ := fun y ↦ r ^ 2 - ‖y - x‖ ^ 2 with hψ
  have hψs : ContDiff ℝ 2 ψ :=
    contDiff_const.sub ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))
  have hψjet : ∀ z w : E d, ψ z = r ^ 2 - ‖z - x‖ ^ 2 ∧
      fderiv ℝ ψ z w = -2 * ⟪z - x, w⟫ ∧ iteratedFDeriv ℝ 2 ψ z ![w, w] = 2 * (-‖w‖ ^ 2) := by
    intro z w
    refine iteratedFDeriv_two_eq_of_isLittleO hψs ((isLittleO_zero _ _).congr_left fun t ↦ ?_)
    have : z + t • w - x = (z - x) + t • w := by abel
    simp only [hψ, this, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
    ring
  have hψlap : ∀ z, Δ ψ z = -2 * d := by
    intro z
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis ψ
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    simp_rw [fun i ↦ (hψjet z ((EuclideanSpace.basisFun (Fin d) ℝ) i)).2.2]
    simp
    ring
  have hψgrad : ∀ z, ‖fderiv ℝ ψ z‖ ≤ 2 * ‖z - x‖ := by
    intro z
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
    rw [(hψjet z w).2.1, Real.norm_eq_abs, abs_mul, abs_neg, abs_two, mul_assoc]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
  have hψnn : ∀ y ∈ ball x r, 0 ≤ ψ y := by
    intro y hy
    have h1 : ‖y - x‖ < r := by rw [← dist_eq_norm]; exact hy
    simp only [hψ]
    nlinarith [norm_nonneg (y - x)]
  have hψle : ∀ y ∈ ball x r, ψ y ≤ r ^ 2 := fun y _ ↦ by
    simp only [hψ]; nlinarith [norm_nonneg (y - x)]
  intro y hy
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (hKB hy)
  set ε₀ := min (δ₀ * q₀ / (8 * r)) (q₀ / (2 * r)) with hε₀
  have hε₀pos : 0 < ε₀ := by positivity
  have hmain : ∀ ε, 0 < ε → ε ≤ ε₀ → v y ≤ max (g y + ε * ψ y) 0 := by
    intro ε hε hεle
    have hc1 : 2 * ε * r ≤ δ₀ * q₀ / 4 := by
      have := (hεle.trans (min_le_left _ _))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hc2 : 2 * ε * r ≤ q₀ := by
      have := (hεle.trans (min_le_right _ _))
      rw [le_div_iff₀ (by positivity)] at this
      linarith
    have hψε : ContDiff ℝ 2 (ε • ψ) := hψs.const_smul ε
    have hHs : ContDiff ℝ 2 (g + ε • ψ) := hg2.add hψε
    have hHapp : ∀ w, (g + ε • ψ) w = g w + ε * ψ w := fun w ↦ rfl
    have key := hv.le_max_of_barrier hd isOpen_ball hK hKB hHs ?_ ?_ ?_ y hy
    · simpa [hHapp] using key
    · -- the barrier is strictly superharmonic
      intro z hz
      have hzB : z ∈ closedBall x r := ball_subset_closedBall (hKB hz)
      have hΔg : Δ g z ≤ 0 := hg1 z (subset_closure (hBU hzB)) (by linarith [hga z hzB])
      rw [hg2.contDiffAt.laplacian_add hψε.contDiffAt,
        InnerProductSpace.laplacian_smul ε hψs.contDiffAt, hψlap z, smul_eq_mul]
      linarith [mul_pos hε hdR]
    · -- gradient condition on the zero level set
      intro z hz hHz
      have hzb : z ∈ ball x r := hKB hz
      have hzB : z ∈ closedBall x r := ball_subset_closedBall hzb
      rw [hHapp] at hHz
      have hgz : g z < 0 := by linarith [mul_nonneg hε.le (hψnn z hzb)]
      have hgabs : |g z| ≤ a₀ := by
        rw [abs_le]; constructor <;> linarith [hga z hzB]
      have hG := hg2' z (subset_closure (hBU hzB)) hgabs
      have hq := hQ z hzB
      have hfd : fderiv ℝ (g + ε • ψ) z = fderiv ℝ g z + ε • fderiv ℝ ψ z := by
        rw [fderiv_add (hg2.differentiable (by norm_num) z)
          (hψε.differentiable (by norm_num) z),
          fderiv_const_smul (hψs.differentiable (by norm_num) z)]
      have hbound : ‖∇ (g + ε • ψ) z‖ ≤ ‖∇ g z‖ + 2 * ε * r := by
        rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv, hfd]
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        have h1 := hψgrad z
        have h2 : ‖z - x‖ ≤ r := by rw [← dist_eq_norm]; exact hzB
        have := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 zero_le_two))
          hε.le
        linarith
      set G := ‖∇ g z‖
      have hG0 : 0 ≤ G := norm_nonneg _
      have hQ0 : 0 < Q z := hq₀.trans_le hq
      have hδQ : 0 < δ₀ * Q z ^ 2 := by positivity
      have hG2 : G ^ 2 ≤ Q z ^ 2 := by linarith
      have hGq : G ≤ Q z := (pow_le_pow_iff_left₀ hG0 hQ0.le two_ne_zero).1 hG2
      set c := 2 * ε * r with hc
      have hc0 : 0 ≤ c := by positivity
      have e1 : c * G ≤ c * Q z := mul_le_mul_of_nonneg_left hGq hc0
      have e2 : c * Q z ≤ δ₀ * q₀ / 4 * Q z := mul_le_mul_of_nonneg_right hc1 hQ0.le
      have e3 : δ₀ * q₀ * Q z ≤ δ₀ * (Q z * Q z) := by
        have := mul_le_mul_of_nonneg_left hq (by positivity : (0:ℝ) ≤ δ₀ * Q z)
        linarith
      have e4 : c * c ≤ δ₀ * q₀ / 4 * q₀ := mul_le_mul hc1 hc2 hc0 (by positivity)
      have e5 : δ₀ * q₀ * q₀ ≤ δ₀ * (Q z * Q z) := by
        have h1 := mul_le_mul hq hq hq₀.le hQ0.le
        linarith [mul_le_mul_of_nonneg_left h1 hδ₀.le]
      have hlt : (G + c) ^ 2 < Q z ^ 2 := by linarith
      have : G + c < Q z := lt_of_pow_lt_pow_left₀ 2 hQ0.le hlt
      linarith
    · -- outside `K`
      intro w hw
      exact (hout w hw).trans (max_le_max (by
        rw [hHapp]; linarith [mul_nonneg hε.le (hψnn w hw.1)]) le_rfl)
  -- let `ε → 0`
  by_contra hcon
  push Not at hcon
  set δ := v y - max (g y) 0 with hδ
  have hδ0 : 0 < δ := by linarith
  set ε := min ε₀ (δ / (2 * (r ^ 2 + 1))) with hε
  have hε0 : 0 < ε := lt_min hε₀pos (by positivity)
  have h1 := hmain ε hε0 (min_le_left _ _)
  have hεr : ε * r ^ 2 < δ := by
    have h2 : ε ≤ δ / (2 * (r ^ 2 + 1)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h2
    linarith [mul_nonneg hε0.le (sq_nonneg r)]
  have hψy := hψle y (hKB hy)
  have h3 : max (g y + ε * ψ y) 0 ≤ max (g y) 0 + ε * r ^ 2 := by
    refine max_le ?_ (by linarith [le_max_right (g y) 0, mul_nonneg hε0.le (sq_nonneg r)])
    linarith [le_max_left (g y) 0, mul_le_mul_of_nonneg_left hψy hε0.le]
  linarith

end EllipticBernoulli

end
