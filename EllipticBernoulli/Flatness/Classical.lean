/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Flatness
public import EllipticBernoulli.Defs.Regularity
import EllipticBernoulli.Flatness.Graph
import EllipticBernoulli.Flatness.OneStep
import EllipticBernoulli.Harmonic.GradientEstimate
import EllipticBernoulli.Viscosity.Affine
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic

/-!
# Flatness implies classical regularity

De Silva (2011), Theorem 1.1, with `f = 0` and `g = Q`, plus an interior-estimate route to
`IsClassicalNear` (no boundary Schauder theory).

* Bookkeeping: `closure_posSet_inter` (`closure {u > 0} = {u > 0} ∪ F(u)` inside `U`),
  `frontier_setOf_pos_inter` (`∂{v > 0} = F(v)` inside an open `V ⊆ U`).
* `flat_rescale`: the hypotheses of `FlatClassicalStatement`, rescaled by
  `v z = u(x₀ + r z)/(r Q(x₀))`, `q z = Q(x₀ + r z)/Q(x₀)`, give the normalized hypotheses with
  `|q - 1|, Lip q ≤ L r / qmin`.
* `IsC1GammaHypersurfaceNear.affine`, `IsC1GammaHypersurfaceNear.mono`: transport of the graph
  property under `z ↦ x₀ + r z`, and restriction to smaller balls.
* `isC1GammaHypersurfaceNear_of_flat : FlatGraphStatement` (radius `r/2`), from
  `isC1GammaHypersurfaceNear_of_flat_normalized` (`Flatness/Graph.lean`).
* `deSilva_flat_implies_regular_core` (`Q ≡ 1`): the free boundary is the zero set of the
  defining function `F y = ⟪e', y⟫ - f (y - ⟪y, e'⟫ e')`, with `⟪∇F, e'⟫ = 1`.
* `gradient_extends_to_fb` and `isClassicalNear_of_flat : FlatClassicalStatement`: the gradient
  up to the free boundary, and the classical property near a flat free-boundary point.

`flat_pointwise_C1alpha` enters only through `Flatness/Graph.lean`. The passage from the
unnormalized hypotheses is `flat_rescale` with the normalized flatness parameter fixed at `ε₁` and
`εbar = min(ε₁, ε₁² qmin / (L + 1))`; the normalized theorem accepts every `ε ≤ ε₁`.

**Deviations from De Silva (2011).** De Silva allows a Hölder coefficient (`[g]_{C^{0,β}} ≤ ε̄`);
here `Q` is `L`-Lipschitz with `qmin ≤ Q ≤ qmax`, and after the rescaling with `r ≤ εbar` the
Lipschitz seminorm of `q` is at most `εbar L / qmin`. De Silva's exponent and radius do not depend
on the solution, whereas `IsC1GammaHypersurfaceNear` and `IsClassicalNear` choose the exponent, the
Hölder constant and the radius per solution. The proofs do not use `qmax`.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Frontier and closure bookkeeping -/

/-- Inside `U`, the closure of the positivity set is the positivity set plus the free
boundary. -/
theorem closure_posSet_inter {U S : Set (E d)} {u : E d → ℝ} (hS : S ⊆ U) :
    closure (posSet u U) ∩ S = (posSet u U ∪ freeBoundary u U) ∩ S := by
  rw [closure_eq_self_union_frontier]
  ext y
  simp only [mem_inter_iff, mem_union, freeBoundary]
  constructor
  · rintro ⟨h | h, hy⟩
    · exact ⟨Or.inl h, hy⟩
    · exact ⟨Or.inr ⟨h, hS hy⟩, hy⟩
  · rintro ⟨h | h, hy⟩
    · exact ⟨Or.inl h, hy⟩
    · exact ⟨Or.inr h.1, hy⟩

/-- Inside an open `V ⊆ U` (`U` open), the topological boundary of `{v > 0}` is the free
boundary `freeBoundary v U` (so statements phrased with `frontier {y | 0 < v y}` agree). -/
theorem frontier_setOf_pos_inter {U V : Set (E d)} {v : E d → ℝ} (hU : IsOpen U) (hV : V ⊆ U) :
    frontier {y | 0 < v y} ∩ V = freeBoundary v U ∩ V := by
  have h : frontier ({y | 0 < v y} ∩ U) ∩ U = frontier {y | 0 < v y} ∩ U :=
    frontier_inter_open_inter hU
  have hpos : posSet v U = {y | 0 < v y} ∩ U := by
    ext y; simp [posSet, and_comm]
  rw [freeBoundary, hpos]
  calc frontier {y | 0 < v y} ∩ V = (frontier {y | 0 < v y} ∩ U) ∩ V := by
        rw [inter_assoc, inter_eq_right.2 hV]
    _ = (frontier ({y | 0 < v y} ∩ U) ∩ U) ∩ V := by rw [h]

/-! ### Rescaling the flatness hypotheses -/

/-- **Rescaling lemma.** Under the hypotheses of `FlatClassicalStatement` (`Q`
`L`-Lipschitz with `Q ≥ qmin > 0` on `U`, `B_r(x₀) ⊆ U`, two-sided `εbar r`-flatness with slope
`Q(x₀)`), put `A z = x₀ + r z`, `v z = u(A z)/(r Q(x₀))`, `q z = Q(A z)/Q(x₀)`. Then `v` is a
viscosity solution in `A⁻¹ U ⊇ B_1` with coefficient `q`, `|q - 1| ≤ L r/qmin` and
`Lip(q; B_1) ≤ L r/qmin` on `B_1`, `v` is `εbar`-flat on `B_1`, and `F(v) = A⁻¹ F(u)`. -/
theorem flat_rescale {U : Set (E d)} {Q u : E d → ℝ} {L : ℝ≥0} {qmin εbar r : ℝ} {x₀ e : E d}
    (hU : IsOpen U) (hQ : LipschitzOnWith L Q U) (hQlo : ∀ y ∈ U, qmin ≤ Q y) (hqmin : 0 < qmin)
    (hu : IsViscSolution U Q u) (hr : 0 < r) (hB : ball x₀ r ⊆ U)
    (hflat : ∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
      u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) :
    IsOpen ((fun z ↦ x₀ + r • z) ⁻¹' U) ∧ ball (0 : E d) 1 ⊆ (fun z ↦ x₀ + r • z) ⁻¹' U ∧
    IsViscSolution ((fun z ↦ x₀ + r • z) ⁻¹' U) (fun z ↦ Q (x₀ + r • z) / Q x₀)
      (fun z ↦ u (x₀ + r • z) / (r * Q x₀)) ∧
    (∀ z ∈ ball (0 : E d) 1, |Q (x₀ + r • z) / Q x₀ - 1| ≤ L * r / qmin) ∧
    LipschitzOnWith (L * r / qmin).toNNReal (fun z ↦ Q (x₀ + r • z) / Q x₀) (ball 0 1) ∧
    (∀ z ∈ ball (0 : E d) 1, max (⟪z, e⟫ - εbar) 0 ≤ u (x₀ + r • z) / (r * Q x₀) ∧
      u (x₀ + r • z) / (r * Q x₀) ≤ max (⟪z, e⟫ + εbar) 0) ∧
    freeBoundary (fun z ↦ u (x₀ + r • z) / (r * Q x₀)) ((fun z ↦ x₀ + r • z) ⁻¹' U) =
      (fun z ↦ x₀ + r • z) ⁻¹' freeBoundary u U := by
  have hx₀U : x₀ ∈ U := hB (mem_ball_self hr)
  have hQx₀ : qmin ≤ Q x₀ := hQlo x₀ hx₀U
  have hQ0 : 0 < Q x₀ := hqmin.trans_le hQx₀
  have hA : ∀ z ∈ ball (0 : E d) 1, x₀ + r • z ∈ ball x₀ r := fun z hz ↦ by
    rw [mem_ball, dist_zero_right] at hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact mul_lt_of_lt_one_right hr hz
  have hdist : ∀ z₁ z₂ : E d, dist (x₀ + r • z₁) (x₀ + r • z₂) = r * dist z₁ z₂ := fun z₁ z₂ ↦ by
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hr]
  have hL0 : (0 : ℝ) ≤ L := L.2
  have hLr : 0 ≤ (L : ℝ) * r / qmin := div_nonneg (mul_nonneg hL0 hr.le) hqmin.le
  refine ⟨hU.preimage (by fun_prop), fun z hz ↦ hB (hA z hz), hu.rescale x₀ hr hQ0, ?_, ?_, ?_,
    freeBoundary_rescale x₀ hr hQ0⟩
  · intro z hz
    have h1 := hQ.dist_le_mul _ (hB (hA z hz)) _ hx₀U
    have hd : dist (x₀ + r • z) x₀ = r * ‖z‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    rw [hd, Real.dist_eq] at h1
    rw [mem_ball, dist_zero_right] at hz
    rw [div_sub_one hQ0.ne', abs_div, abs_of_pos hQ0, div_le_div_iff₀ hQ0 hqmin]
    have h2 : (L : ℝ) * (r * ‖z‖) ≤ L * r :=
      mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hr.le hz.le) hL0
    calc |Q (x₀ + r • z) - Q x₀| * qmin ≤ (L * r) * qmin :=
          mul_le_mul_of_nonneg_right (by linarith) hqmin.le
      _ ≤ (L * r) * Q x₀ := mul_le_mul_of_nonneg_left hQx₀ (mul_nonneg hL0 hr.le)
  · refine LipschitzOnWith.of_dist_le_mul fun z₁ hz₁ z₂ hz₂ ↦ ?_
    have h1 := hQ.dist_le_mul _ (hB (hA z₁ hz₁)) _ (hB (hA z₂ hz₂))
    rw [hdist, Real.dist_eq] at h1
    rw [Real.coe_toNNReal _ hLr, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hQ0,
      div_le_iff₀ hQ0]
    calc |Q (x₀ + r • z₁) - Q (x₀ + r • z₂)| ≤ L * (r * dist z₁ z₂) := h1
      _ = (L * r / qmin * dist z₁ z₂) * qmin := by field_simp
      _ ≤ (L * r / qmin * dist z₁ z₂) * Q x₀ :=
          mul_le_mul_of_nonneg_left hQx₀ (mul_nonneg hLr dist_nonneg)
  · intro z hz
    obtain ⟨h1, h2⟩ := hflat _ (hA z hz)
    rw [add_sub_cancel_left, real_inner_smul_left] at h1 h2
    have hrQ : 0 < r * Q x₀ := mul_pos hr hQ0
    have hm : ∀ a : ℝ, Q x₀ * max (r * a) 0 = r * Q x₀ * max a 0 := fun a ↦ by
      rcases le_total a 0 with h | h
      · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hr.le h)]; ring
      · rw [max_eq_left h, max_eq_left (mul_nonneg hr.le h)]; ring
    rw [show r * ⟪z, e⟫ - εbar * r = r * (⟪z, e⟫ - εbar) by ring, hm] at h1
    rw [show r * ⟪z, e⟫ + εbar * r = r * (⟪z, e⟫ + εbar) by ring, hm] at h2
    exact ⟨(le_div_iff₀ hrQ).2 (by linarith), (div_le_iff₀ hrQ).2 (by linarith)⟩

/-! ### Transport of the graph property -/

/-- `IsC1GammaHypersurfaceNear` restricts to smaller balls. -/
theorem IsC1GammaHypersurfaceNear.mono {S : Set (E d)} {x₀ : E d} {r r' : ℝ}
    (h : IsC1GammaHypersurfaceNear S x₀ r) (hr' : r' ≤ r) :
    IsC1GammaHypersurfaceNear S x₀ r' := by
  obtain ⟨γ, hγ0, hγ1, e, he, f, C, hf, hC, hgraph⟩ := h
  refine ⟨γ, hγ0, hγ1, e, he, f, C, hf, hC, ?_⟩
  have hsub : ball x₀ r' ⊆ ball x₀ r := ball_subset_ball hr'
  ext y
  constructor
  · rintro ⟨hyS, hy⟩
    exact ⟨hy, ((Set.ext_iff.1 hgraph y).1 ⟨hyS, hsub hy⟩).2⟩
  · rintro ⟨hy, heq⟩
    exact ⟨((Set.ext_iff.1 hgraph y).2 ⟨hsub hy, heq⟩).1, hy⟩

/-- **Transport under `z ↦ x₀ + r z`.** If `S` is a `C^{1,γ}` graph in `B_ρ(0)`, then
`{y | r⁻¹ (y - x₀) ∈ S}` is a `C^{1,γ}` graph in `B_{rρ}(x₀)`, with `f_u(w) = r f(w/r)` and Hölder
constant `C r^{-γ}`. -/
theorem IsC1GammaHypersurfaceNear.affine {S : Set (E d)} {ρ r : ℝ} (hr : 0 < r) (x₀ : E d)
    (h : IsC1GammaHypersurfaceNear S 0 ρ) :
    IsC1GammaHypersurfaceNear ((fun y ↦ r⁻¹ • (y - x₀)) ⁻¹' S) x₀ (r * ρ) := by
  obtain ⟨γ, hγ0, hγ1, e, he, f, C, hf, hC, hgraph⟩ := h
  have hfd : ∀ w, fderiv ℝ (fun w ↦ r * f (r⁻¹ • w)) w = fderiv ℝ f (r⁻¹ • w) := fun w ↦ by
    have hdiff : DifferentiableAt ℝ (fun w ↦ f (r⁻¹ • w)) w :=
      ((hf.differentiable (by norm_num)) _).comp w (by fun_prop)
    rw [fderiv_const_mul hdiff, show (fun w ↦ f (r⁻¹ • w)) = (f <| r⁻¹ • ·) from rfl,
      fderiv_comp_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hlip : LipschitzWith ‖r⁻¹‖₊ (fun w : E d ↦ r⁻¹ • w) := lipschitzWith_smul r⁻¹
  refine ⟨γ, hγ0, hγ1, e, he, fun w ↦ r * f (r⁻¹ • w), C * ‖r⁻¹‖₊ ^ (γ : ℝ), ?_, ?_, ?_⟩
  · exact contDiff_const.mul (hf.comp (by fun_prop))
  · have := hC.comp (holderWith_one.2 hlip)
    rw [mul_one] at this
    rwa [show fderiv ℝ (fun w ↦ r * f (r⁻¹ • w)) = fderiv ℝ f ∘ (fun w ↦ r⁻¹ • w) from
      funext hfd]
  · ext y
    have hy := Set.ext_iff.1 hgraph (r⁻¹ • (y - x₀))
    simp only [mem_inter_iff, mem_preimage, mem_setOf_eq, sub_zero] at hy ⊢
    have hball : r⁻¹ • (y - x₀) ∈ ball (0 : E d) ρ ↔ y ∈ ball x₀ (r * ρ) := by
      rw [mem_ball, mem_ball, dist_zero_right, dist_eq_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 hr), inv_mul_lt_iff₀ hr]
    have hin : ⟪r⁻¹ • (y - x₀), e⟫ = r⁻¹ * ⟪y - x₀, e⟫ := real_inner_smul_left _ _ _
    have harg : r⁻¹ • (y - x₀) - ⟪r⁻¹ • (y - x₀), e⟫ • e =
        r⁻¹ • (y - x₀ - ⟪y - x₀, e⟫ • e) := by
      rw [hin, mul_smul, ← smul_sub]
    rw [hball, harg, hin] at hy
    rw [hy]
    exact and_congr_right fun _ ↦ inv_mul_eq_iff_eq_mul₀ hr.ne'

/-! ### The headline statements -/

/-- **Flat free boundaries are `C^{1,γ}` graphs** (`FlatGraphStatement`; De Silva (2011),
Theorem 1.1).
Proof: `flat_rescale`, then `isC1GammaHypersurfaceNear_of_flat_normalized` (graph on `B_{1/2}`),
then `IsC1GammaHypersurfaceNear.affine`. With `εbar = min(ε₁, ε₁² qmin/(L + 1))`, the rescaled
coefficient satisfies `|q - 1|, Lip q ≤ L εbar/qmin ≤ ε₁²`. -/
theorem isC1GammaHypersurfaceNear_of_flat : FlatGraphStatement := by
  intro d hd L qmin qmax hqmin
  obtain ⟨ε₁, hε₁, H⟩ := isC1GammaHypersurfaceNear_of_flat_normalized (d := d) hd
  have hL1 : 0 < (L : ℝ) + 1 := by positivity
  refine ⟨min ε₁ (ε₁ ^ 2 * qmin / (L + 1)), lt_min hε₁ (by positivity),
    fun U Q u x₀ e r hU hQ hQb hu hx₀ he hr hrε hB hflat ↦ ?_⟩
  have hrε₂ : r ≤ ε₁ ^ 2 * qmin / (L + 1) := hrε.trans (min_le_right _ _)
  obtain ⟨hU', hB', hv, hq, hLip, hflat', hfb⟩ :=
    flat_rescale hU hQ (fun y hy ↦ (hQb y hy).1) hqmin hu hr hB hflat
  have hLr : (L : ℝ) * r / qmin ≤ ε₁ ^ 2 := by
    rw [div_le_iff₀ hqmin]
    rw [le_div_iff₀ hL1] at hrε₂
    linarith
  have hεbar : min ε₁ (ε₁ ^ 2 * qmin / (L + 1)) ≤ ε₁ := min_le_left _ _
  have hG := H _ _ _ e ε₁ hU' hB' hv he hε₁ le_rfl (fun z hz ↦ (hq z hz).trans hLr)
    (hLip.weaken (Real.toNNReal_le_toNNReal hLr)) (fun z hz ↦ by
      obtain ⟨h1, h2⟩ := hflat' z hz
      exact ⟨le_trans (max_le_max (by linarith) le_rfl) h1,
        h2.trans (max_le_max (by linarith) le_rfl)⟩)
  rw [hfb] at hG
  have := hG.affine hr x₀
  rw [show r * (1 / 2) = r / 2 by ring] at this
  convert this using 1
  ext y
  simp [smul_smul, mul_inv_cancel₀ hr.ne']

/-- **Flat free boundaries are regular level sets** (`Q ≡ 1`; De Silva (2011), Theorem 1.1).
An `ε₀`-flat viscosity solution on `B_1` has, in `B_{1/2}`, a free boundary that is the
zero set of a `C¹` function `F` with nonvanishing gradient: `F y = ⟪e', y⟫ - f (y - ⟪y, e'⟫ e')`,
with `f` and `e'` from the normalized graph theorem, so `⟪∇F, e'⟫ = 1`. The hypothesis
`0 ∈ F(v)` is not used. -/
theorem deSilva_flat_implies_regular_core (hd : 2 ≤ d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (v : E d → ℝ) (e : E d), ‖e‖ = 1 →
      IsViscSolution (ball 0 1) (fun _ ↦ 1) v → (0 : E d) ∈ freeBoundary v (ball 0 1) →
      (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε₀) 0 ≤ v y ∧ v y ≤ max (⟪y, e⟫ + ε₀) 0) →
      ∃ F : E d → ℝ, ContDiff ℝ 1 F ∧ (∀ y ∈ ball (0 : E d) (1 / 2), gradient F y ≠ 0) ∧
        ball (0 : E d) (1 / 2) ∩ freeBoundary v (ball 0 1) = ball 0 (1 / 2) ∩ {y | F y = 0} := by
  obtain ⟨ε₁, hε₁, H⟩ := isC1GammaHypersurfaceNear_of_flat_normalized (d := d) hd
  refine ⟨ε₁, hε₁, fun v e he hv _ hflat ↦ ?_⟩
  have hLip1 : LipschitzOnWith (ε₁ ^ 2).toNNReal (fun _ : E d ↦ (1 : ℝ)) (ball 0 1) :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.weaken zero_le
  obtain ⟨γ, -, -, e', he', f, C, hf, -, hgraph⟩ := H (ball 0 1) (fun _ ↦ 1) v e ε₁ isOpen_ball
    subset_rfl hv he hε₁ le_rfl (fun _ _ ↦ by simp only [sub_self, abs_zero]; positivity) hLip1
    hflat
  set P : E d →L[ℝ] E d := ContinuousLinearMap.id ℝ (E d) - (innerSL ℝ e').smulRight e' with hP
  have hPapp : ∀ y, P y = y - ⟪y, e'⟫ • e' := fun y ↦ by
    simp [hP, real_inner_comm]
  have hee : ⟪e', e'⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he', one_pow]
  have hPe : P e' = 0 := by rw [hPapp, hee, one_smul, sub_self]
  refine ⟨fun y ↦ innerSL ℝ e' y - f (P y), ?_, ?_, ?_⟩
  · exact (innerSL ℝ e').contDiff.sub (hf.comp P.contDiff)
  · intro y _ h0
    have hder : HasFDerivAt (fun y ↦ innerSL ℝ e' y - f (P y))
        (innerSL ℝ e' - (fderiv ℝ f (P y)).comp P) y :=
      (innerSL ℝ e').hasFDerivAt.sub
        (((hf.differentiable (by norm_num)) (P y)).hasFDerivAt.comp y P.hasFDerivAt)
    have h1 : ⟪gradient (fun y ↦ innerSL ℝ e' y - f (P y)) y, e'⟫ = 1 := by
      rw [gradient, toDual_symm_apply, hder.fderiv]
      simp [hPe, he']
    rw [h0, inner_zero_left] at h1
    exact zero_ne_one h1
  · ext y
    have hy := Set.ext_iff.1 hgraph y
    simp only [mem_inter_iff, mem_setOf_eq, sub_zero] at hy ⊢
    rw [innerSL_apply_apply, hPapp, real_inner_comm, sub_eq_zero]
    exact ⟨fun ⟨hb, hfb⟩ ↦ hy.1 ⟨hfb, hb⟩, fun h ↦ (hy.2 h).symm⟩

/-! ### The gradient up to the free boundary -/

/-- The gradient and the derivative differ by the Riesz isometry:
`‖∇v y - a‖ = ‖fderiv v y - toDual a‖`. -/
private theorem norm_gradient_sub_eq (v : E d → ℝ) (y a : E d) :
    ‖∇ v y - a‖ = ‖fderiv ℝ v y - toDual ℝ (E d) a‖ := by
  rw [← (toDual ℝ (E d)).norm_map, LinearIsometryEquiv.map_sub, gradient,
    LinearIsometryEquiv.apply_symm_apply]

/-- **Linear approximation of the gradient.** Let `v` be harmonic on `{v > 0}`,
pointwise flat at `x₁` (`IsFlatC1AlphaAt v q x₁ ν₁ M α ρ`, `0 < q x₁ ≤ 2`), and let
`B_s(y) ⊆ {v > 0}` with `‖y - x₁‖ ≤ s`, `2s ≤ ρ`. Then `‖∇v(y) - q(x₁) ν₁‖ ≤ 16 C_d M s^α`,
where `C_d` is the constant of the interior gradient estimate.

Proof: on `B_s(y) ⊆ B_{2s}(x₁)`, `v > 0` and the flatness give
`|v - q(x₁) ⟪· - x₁, ν₁⟫| ≤ q(x₁) M (2s)^{1+α}`; the difference is harmonic, and the interior
gradient estimate on `B̄_{s/2}(y)` gives the bound. -/
private theorem norm_gradient_sub_le_of_flat {U : Set (E d)} {q v : E d → ℝ} {x₁ ν₁ y : E d}
    {M α ρ s Cd : ℝ} (hCd0 : 0 ≤ Cd)
    (hCd : ∀ (u : E d → ℝ) (x₀ : E d) (r M : ℝ), 0 < r →
      HarmonicOnNhd u (closedBall x₀ r) → (∀ y ∈ closedBall x₀ r, |u y| ≤ M) →
      ‖fderiv ℝ u x₀‖ ≤ Cd * M / r)
    (hvH : HarmonicOnNhd v (posSet v U)) (hflat : IsFlatC1AlphaAt v q x₁ ν₁ M α ρ)
    (hM : 0 ≤ M) (hα1 : α ≤ 1) (hq0 : 0 < q x₁) (hq2 : q x₁ ≤ 2) (hs : 0 < s)
    (hsρ : 2 * s ≤ ρ) (hball : ball y s ⊆ posSet v U) (hyx : ‖y - x₁‖ ≤ s) :
    ‖∇ v y - q x₁ • ν₁‖ ≤ 16 * Cd * M * s ^ α := by
  set σ := -⟪x₁, ν₁⟫ with hσ
  set h : E d → ℝ := fun x ↦ v x - q x₁ * (⟪x, ν₁⟫ + σ) with hh_def
  have hlin : ∀ x, ⟪x, ν₁⟫ + σ = ⟪x - x₁, ν₁⟫ := fun x ↦ by rw [inner_sub_left, hσ]; ring
  -- `h` is harmonic near `closedBall y (s/2)`
  have hcb : closedBall y (s / 2) ⊆ ball y s := closedBall_subset_ball (by linarith)
  have hhH : HarmonicOnNhd h (closedBall y (s / 2)) := fun x hx ↦
    (hvH x (hball (hcb hx))).sub ((harmonicAt_inner_add ν₁ σ x).const_smul (c := q x₁))
  -- the bound on `h`
  have hpow : (2 * s) ^ (1 + α) ≤ 4 * (s * s ^ α) := by
    rw [Real.mul_rpow (by norm_num) hs.le, Real.rpow_add hs, Real.rpow_one]
    have : (2 : ℝ) ^ (1 + α) ≤ 4 := by
      calc (2 : ℝ) ^ (1 + α) ≤ 2 ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 4 := by norm_num
    have hss : 0 ≤ s * s ^ α := mul_nonneg hs.le (Real.rpow_nonneg hs.le _)
    exact mul_le_mul_of_nonneg_right this hss
  have hbound : ∀ x ∈ closedBall y (s / 2), |h x| ≤ q x₁ * M * (2 * s) ^ (1 + α) := by
    intro x hx
    have hxpos : 0 < v x := (hball (hcb hx)).2
    have hx1 : x ∈ ball x₁ (2 * s) := by
      rw [mem_ball, dist_eq_norm]
      rw [mem_closedBall, dist_eq_norm] at hx
      calc ‖x - x₁‖ = ‖(x - y) + (y - x₁)‖ := by abel_nf
        _ ≤ ‖x - y‖ + ‖y - x₁‖ := norm_add_le _ _
        _ < 2 * s := by linarith
    obtain ⟨hlo, hhi⟩ := hflat.2 (2 * s) ⟨by linarith, hsρ⟩ x hx1
    have hup : max (⟪x - x₁, ν₁⟫ + M * (2 * s) ^ (1 + α)) 0 =
        ⟪x - x₁, ν₁⟫ + M * (2 * s) ^ (1 + α) := by
      refine max_eq_left ?_
      by_contra hneg
      push Not at hneg
      rw [max_eq_right hneg.le, mul_zero] at hhi
      linarith
    rw [hup] at hhi
    have hlo' := le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hq0.le) hlo
    simp only [hh_def, hlin]
    rw [abs_le]
    constructor <;> linarith
  have hest := hCd h y (s / 2) _ (by linarith) hhH hbound
  -- the derivative of `h`
  have hvd : DifferentiableAt ℝ v y :=
    ((hvH y (hball (mem_ball_self hs))).1).differentiableAt (by norm_num)
  have hinner : HasFDerivAt (fun x ↦ ⟪x, ν₁⟫ + σ) (toDual ℝ (E d) ν₁) y := by
    have : (fun x : E d ↦ ⟪x, ν₁⟫ + σ) = fun x ↦ toDual ℝ (E d) ν₁ x + σ := by
      funext x; rw [toDual_apply_apply, real_inner_comm]
    rw [this]
    exact (toDual ℝ (E d) ν₁).hasFDerivAt.add_const σ
  have hhd : HasFDerivAt h (fderiv ℝ v y - q x₁ • toDual ℝ (E d) ν₁) y :=
    hvd.hasFDerivAt.sub (hinner.const_mul (q x₁))
  rw [norm_gradient_sub_eq, map_smul, ← hhd.fderiv]
  calc ‖fderiv ℝ h y‖ ≤ Cd * (q x₁ * M * (2 * s) ^ (1 + α)) / (s / 2) := hest
    _ ≤ Cd * (2 * M * (4 * (s * s ^ α))) / (s / 2) := by
        gcongr
    _ = 16 * Cd * M * s ^ α := by field_simp; ring

/-- The nearest point of `{v ≤ 0}`: for `y ∈ {v > 0}` and `y₀ ∉ {v > 0}`, there is `x₁ ∉ {v > 0}`
in `closure {v > 0}` with `s = ‖y - x₁‖ ≤ ‖y - y₀‖`, `s > 0` and `B_s(y) ⊆ {v > 0}`. -/
private theorem exists_nearest_zero {P : Set (E d)} (hP : IsOpen P) {y y₀ : E d} (hy : y ∈ P)
    (hy₀ : y₀ ∉ P) :
    ∃ x₁, x₁ ∉ P ∧ x₁ ∈ closure P ∧ 0 < ‖y - x₁‖ ∧ ‖y - x₁‖ ≤ ‖y - y₀‖ ∧
      ball y ‖y - x₁‖ ⊆ P := by
  have hcl : IsClosed Pᶜ := hP.isClosed_compl
  obtain ⟨x₁, hx₁, hdist⟩ := hcl.exists_infDist_eq_dist ⟨y₀, hy₀⟩ y
  rw [dist_eq_norm] at hdist
  have hball : ball y ‖y - x₁‖ ⊆ P := fun x hx ↦ by
    by_contra hxP
    have := Metric.infDist_le_dist_of_mem (x := y) (show x ∈ Pᶜ from hxP)
    rw [hdist, dist_comm, dist_eq_norm] at this
    rw [mem_ball, dist_eq_norm] at hx
    linarith
  have hpos : 0 < ‖y - x₁‖ := by
    rcases (norm_nonneg (y - x₁)).lt_or_eq with h | h
    · exact h
    · exfalso
      have : y = x₁ := sub_eq_zero.1 (norm_eq_zero.1 h.symm)
      exact hx₁ (this ▸ hy)
  refine ⟨x₁, hx₁, ?_, hpos, ?_, hball⟩
  · have : x₁ ∈ closedBall y ‖y - x₁‖ := by rw [mem_closedBall, dist_comm, dist_eq_norm]
    rw [← closure_ball y hpos.ne'] at this
    exact closure_mono hball this
  · have := Metric.infDist_le_dist_of_mem (x := y) (show y₀ ∈ Pᶜ from hy₀)
    rw [hdist, dist_eq_norm] at this
    exact this

/-- **Gradient up to the free boundary** (normalized form). Under the hypotheses
of `isC1GammaHypersurfaceNear_of_flat_normalized`, `∇v` extends continuously from `{v > 0}` to
`closure {v > 0}` in `B_{1/2}`, with `‖G‖ = q` on the free boundary: `G = ∇v` on `{v > 0}` and
`G = q ν` on `F(v)`. Only the interior gradient estimate is used (no boundary Schauder
theory): `‖∇v(y) - q(x₁) ν(x₁)‖ ≤ C s^α` with `x₁` a nearest free-boundary point and
`s = ‖y - x₁‖`, plus the Hölder continuity of `q ν` along the free boundary. -/
theorem gradient_extends_to_fb (hd : 2 ≤ d) : ∃ ε₁ > 0,
    ∀ (U : Set (E d)) (q v : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
    IsViscSolution U q v → ‖e‖ = 1 → 0 < ε → ε ≤ ε₁ →
    (∀ y ∈ ball (0 : E d) 1, |q y - 1| ≤ ε ^ 2) → LipschitzOnWith (ε ^ 2).toNNReal q (ball 0 1) →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ v y ∧ v y ≤ max (⟪y, e⟫ + ε) 0) →
    ∃ G : E d → E d, ContinuousOn G (closure (posSet v U) ∩ ball 0 (1 / 2)) ∧
      (∀ y ∈ posSet v U ∩ ball 0 (1 / 2), G y = ∇ v y) ∧
      ∀ y ∈ freeBoundary v U ∩ ball 0 (1 / 2), ‖G y‖ = q y := by
  obtain ⟨ε₁, hε₁, α, hα, C, hC, H⟩ := exists_flatGraphData (d := d) hd
  obtain ⟨Cd, hCd0, hCd⟩ := exists_norm_fderiv_le_div_of_harmonic (d := d) (by omega)
  refine ⟨ε₁, hε₁, fun U q v e ε hU hB hv he hε hεle hq hLip hflat ↦ ?_⟩
  obtain ⟨ν, hG, hF⟩ := H U q v e ε hU hB hv he hε hεle hq hLip hflat
  have hvH : HarmonicOnNhd v (posSet v U) := IsViscSolution.harmonicOnNhd_posSet hU hv
  have hPopen : IsOpen (posSet v U) := hG.isOpen_posSet
  have hε1 : ε ≤ 1 / 128 := by linarith [hG.ε_le]
  have hM := hG.M_nonneg
  have hα0 := hα.1
  have hα1 := hα.2.le
  -- bounds on `q`
  have hqb : ∀ y ∈ ball (0 : E d) 1, 1 / 2 ≤ q y ∧ q y ≤ 2 := fun y hy ↦ by
    have := abs_le.1 (hq y hy)
    have : ε ^ 2 ≤ 1 / 2 := (pow_le_pow_left₀ hε.le hε1 2).trans (by norm_num)
    constructor <;> linarith
  have h34 : ∀ y ∈ ball (0 : E d) (3 / 4), y ∈ ball (0 : E d) 1 := fun y hy ↦
    ball_subset_ball (by norm_num) hy
  -- Hölder continuity of `q ν` along the free boundary
  have hE1 : ∀ a ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4),
      ∀ b ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4), ‖a - b‖ ≤ 1 / 32 →
      ‖q a • ν a - q b • ν b‖ ≤ (ε ^ 2 + 64 * (C * ε)) * ‖a - b‖ ^ α := by
    intro a ha b hb hab
    have hνa : ‖ν a‖ = 1 := (hG.normal a ha).2.1
    have hqab : |q a - q b| ≤ ε ^ 2 * ‖a - b‖ := by
      have := hLip.dist_le_mul a (h34 a ha.2) b (h34 b hb.2)
      rwa [Real.coe_toNNReal _ (by positivity), Real.dist_eq, dist_eq_norm] at this
    have hab1 : ‖a - b‖ ≤ ‖a - b‖ ^ α := by
      have := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg (a - b)) (by linarith) hα0.le hα1
      rwa [Real.rpow_one] at this
    have hsplit : q a • ν a - q b • ν b = (q a - q b) • ν a + q b • (ν a - ν b) := by
      rw [sub_smul, smul_sub]; abel
    rw [hsplit]
    calc _ ≤ ‖(q a - q b) • ν a‖ + ‖q b • (ν a - ν b)‖ := norm_add_le _ _
      _ = |q a - q b| + |q b| * ‖ν a - ν b‖ := by
          rw [norm_smul, norm_smul, hνa, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ ε ^ 2 * ‖a - b‖ ^ α + 2 * (32 * (C * ε) * ‖a - b‖ ^ α) := by
          have hqb2 := hqb b (h34 b hb.2)
          rw [abs_of_pos (a := q b) (by linarith)]
          have h1 : |q a - q b| ≤ ε ^ 2 * ‖a - b‖ ^ α :=
            hqab.trans (mul_le_mul_of_nonneg_left hab1 (sq_nonneg ε))
          have h2 : ‖ν a - ν b‖ ≤ 32 * (C * ε) * ‖a - b‖ ^ α :=
            hG.holder_normal hb ha (by linarith)
          have h3 : q b * ‖ν a - ν b‖ ≤ 2 * (32 * (C * ε) * ‖a - b‖ ^ α) :=
            mul_le_mul hqb2.2 h2 (norm_nonneg _) (by norm_num)
          linarith
      _ = (ε ^ 2 + 64 * (C * ε)) * ‖a - b‖ ^ α := by ring
  classical
  set G : E d → E d := fun y ↦ if y ∈ posSet v U then ∇ v y else q y • ν y with hG_def
  have hGP : ∀ y ∈ posSet v U, G y = ∇ v y := fun y hy ↦ if_pos hy
  have hGN : ∀ y ∉ posSet v U, G y = q y • ν y := fun y hy ↦ if_neg hy
  refine ⟨G, ?_, fun y hy ↦ hGP y hy.1, fun y hy ↦ ?_⟩
  swap
  · -- `‖G‖ = q` on the free boundary
    have hy34 : y ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) :=
      ⟨hy.1, ball_subset_ball (by norm_num) hy.2⟩
    have hnot : y ∉ posSet v U := fun h ↦ hG.not_pos_of_mem hy.1 h.2
    rw [hGN y hnot, norm_smul, (hG.normal y hy34).2.1, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith [(hqb y (h34 y hy34.2)).1])]
  -- continuity
  intro y₀ hy₀
  by_cases hy₀P : y₀ ∈ posSet v U
  · -- interior points: `G = ∇v` near `y₀`, and `v` is smooth there
    refine ContinuousAt.continuousWithinAt ?_
    have hGeq : G =ᶠ[𝓝 y₀] ∇ v := by
      filter_upwards [hPopen.mem_nhds hy₀P] with y hy
      exact hGP y hy
    refine ContinuousAt.congr ?_ hGeq.symm
    have hfd : ContinuousAt (fderiv ℝ v) y₀ :=
      ((hvH y₀ hy₀P).1.fderiv_right (m := 1) (by norm_num)).continuousAt
    exact (toDual ℝ (E d)).symm.continuous.continuousAt.comp hfd
  · -- free-boundary points
    have hy₀U : y₀ ∈ U := hB (ball_subset_ball (by norm_num) hy₀.2)
    have hy₀F : y₀ ∈ freeBoundary v U := ⟨⟨hy₀.1, fun hint ↦ hy₀P (interior_subset hint)⟩, hy₀U⟩
    have hy₀B : ‖y₀‖ < 1 / 2 := by simpa using hy₀.2
    have hy₀34 : y₀ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) :=
      ⟨hy₀F, ball_subset_ball (by norm_num) hy₀.2⟩
    set K := 16 * Cd * (C * ε) + 2 * (ε ^ 2 + 64 * (C * ε)) with hK_def
    have hK0 : 0 ≤ K := by positivity
    have hGy₀ : G y₀ = q y₀ • ν y₀ := hGN y₀ hy₀P
    -- the key estimate
    have hkey : ∀ y ∈ closure (posSet v U) ∩ ball (0 : E d) (1 / 2), ‖y - y₀‖ < 1 / 128 →
        ‖G y - G y₀‖ ≤ K * ‖y - y₀‖ ^ α := by
      intro y hy hyy₀
      have hyn : ‖y - y₀‖ ^ α ≥ 0 := Real.rpow_nonneg (norm_nonneg _) _
      have hCε : 0 ≤ C * ε := (mul_pos hC hε).le
      have hCdε : 0 ≤ 16 * Cd * (C * ε) := mul_nonneg (mul_nonneg (by norm_num) hCd0) hCε
      have hεC : 0 ≤ ε ^ 2 + 64 * (C * ε) := add_nonneg (sq_nonneg ε) (mul_nonneg (by norm_num) hCε)
      by_cases hyP : y ∈ posSet v U
      · obtain ⟨x₁, hx₁P, hx₁cl, hs0, hs, hball⟩ := exists_nearest_zero hPopen hyP hy₀P
        set s := ‖y - x₁‖ with hs_def
        have hx₁y₀ : ‖x₁ - y₀‖ ≤ 2 * ‖y - y₀‖ := by
          calc ‖x₁ - y₀‖ = ‖(y - y₀) - (y - x₁)‖ := by abel_nf
            _ ≤ ‖y - y₀‖ + ‖y - x₁‖ := norm_sub_le _ _
            _ ≤ 2 * ‖y - y₀‖ := by linarith
        have hx₁B : x₁ ∈ ball (0 : E d) (3 / 4) := by
          rw [mem_ball, dist_zero_right]
          calc ‖x₁‖ = ‖(x₁ - y₀) + y₀‖ := by abel_nf
            _ ≤ ‖x₁ - y₀‖ + ‖y₀‖ := norm_add_le _ _
            _ < 3 / 4 := by linarith
        have hx₁F : x₁ ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) :=
          ⟨⟨⟨hx₁cl, fun hint ↦ hx₁P (interior_subset hint)⟩, hB (h34 x₁ hx₁B)⟩, hx₁B⟩
        have hq₁ := hqb x₁ (h34 x₁ hx₁B)
        have hgrad := norm_gradient_sub_le_of_flat hCd0 hCd hvH (hF x₁ hx₁F) (by positivity)
          hα1 (by linarith) hq₁.2 hs0 (by linarith) hball le_rfl
        have hfb := hE1 x₁ hx₁F y₀ hy₀34 (by linarith)
        have hsα : s ^ α ≤ ‖y - y₀‖ ^ α := Real.rpow_le_rpow hs0.le hs hα0.le
        have h2α : ‖x₁ - y₀‖ ^ α ≤ 2 * ‖y - y₀‖ ^ α := by
          calc ‖x₁ - y₀‖ ^ α ≤ (2 * ‖y - y₀‖) ^ α :=
                Real.rpow_le_rpow (norm_nonneg _) hx₁y₀ hα0.le
            _ = 2 ^ α * ‖y - y₀‖ ^ α := Real.mul_rpow (by norm_num) (norm_nonneg _)
            _ ≤ 2 * ‖y - y₀‖ ^ α := by
                refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (norm_nonneg _) _)
                calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
                      Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
                  _ = 2 := Real.rpow_one 2
        rw [hGy₀, hGP y hyP]
        calc ‖∇ v y - q y₀ • ν y₀‖ ≤ ‖∇ v y - q x₁ • ν x₁‖ + ‖q x₁ • ν x₁ - q y₀ • ν y₀‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 16 * Cd * (C * ε) * s ^ α + (ε ^ 2 + 64 * (C * ε)) * ‖x₁ - y₀‖ ^ α :=
              add_le_add hgrad hfb
          _ ≤ 16 * Cd * (C * ε) * ‖y - y₀‖ ^ α +
              (ε ^ 2 + 64 * (C * ε)) * (2 * ‖y - y₀‖ ^ α) :=
            add_le_add (mul_le_mul_of_nonneg_left hsα hCdε) (mul_le_mul_of_nonneg_left h2α hεC)
          _ = K * ‖y - y₀‖ ^ α := by ring
      · have hyU : y ∈ U := hB (ball_subset_ball (by norm_num) hy.2)
        have hyF : y ∈ freeBoundary v U ∩ ball (0 : E d) (3 / 4) :=
          ⟨⟨⟨hy.1, fun hint ↦ hyP (interior_subset hint)⟩, hyU⟩,
            ball_subset_ball (by norm_num) hy.2⟩
        rw [hGy₀, hGN y hyP]
        calc ‖q y • ν y - q y₀ • ν y₀‖ ≤ (ε ^ 2 + 64 * (C * ε)) * ‖y - y₀‖ ^ α :=
              hE1 y hyF y₀ hy₀34 (by linarith)
          _ ≤ K * ‖y - y₀‖ ^ α := by
              have h0 : 0 ≤ 16 * Cd * (C * ε) * ‖y - y₀‖ ^ α := mul_nonneg hCdε hyn
              have h1 : 0 ≤ (ε ^ 2 + 64 * (C * ε)) * ‖y - y₀‖ ^ α := mul_nonneg hεC hyn
              rw [hK_def]
              linarith
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun y ↦ K * ‖y - y₀‖ ^ α)
      (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ ?_
    · rw [eventually_nhdsWithin_iff]
      filter_upwards [ball_mem_nhds y₀ (by norm_num : (0 : ℝ) < 1 / 128)] with y hy hyS
      rw [mem_ball, dist_eq_norm] at hy
      exact hkey y hyS hy
    · have hcont : Continuous fun y : E d ↦ K * ‖y - y₀‖ ^ α :=
        continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
          fun _ ↦ Or.inr hα0.le)
      have := hcont.tendsto y₀
      simp only [sub_self, norm_zero, Real.zero_rpow hα0.ne', mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds

/-- The gradient under the rescaling `v z = u (x₀ + r z) / (r c)`:
`∇v(z) = c⁻¹ ∇u(x₀ + r z)`. -/
private theorem gradient_rescale {u : E d → ℝ} {x₀ z : E d} {r c : ℝ} (hr : r ≠ 0)
    (hu : DifferentiableAt ℝ u (x₀ + r • z)) :
    ∇ (fun z ↦ u (x₀ + r • z) / (r * c)) z = c⁻¹ • ∇ u (x₀ + r • z) := by
  have hA : HasFDerivAt (fun z : E d ↦ x₀ + r • z) (r • ContinuousLinearMap.id ℝ (E d)) z :=
    ((hasFDerivAt_id z).const_smul r).const_add x₀
  have h1 := (hu.hasFDerivAt.comp z hA).const_mul (r * c)⁻¹
  have hfun : (fun z ↦ u (x₀ + r • z) / (r * c)) =
      fun z ↦ (r * c)⁻¹ * (u ∘ fun z ↦ x₀ + r • z) z := by
    funext z; simp only [Function.comp_apply]; ring
  have hD : (r * c)⁻¹ • (fderiv ℝ u (x₀ + r • z)).comp (r • ContinuousLinearMap.id ℝ (E d)) =
      c⁻¹ • fderiv ℝ u (x₀ + r • z) := by
    ext w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    field_simp
  rw [gradient, hfun, h1.fderiv, hD, map_smul, gradient]

/-- **Flat viscosity solutions are classical near the free boundary** (`FlatClassicalStatement`;
De Silva (2011), Theorem 1.1, plus `gradient_extends_to_fb`). Radius `r/2`:
* the graph property is `isC1GammaHypersurfaceNear_of_flat` (radius `r/2`);
* `u ∈ C²` and `Δu = 0` in `{u > 0}` by `IsViscSolution.harmonicOnNhd_posSet`;
* `G y = Q(x₀) G_v(r⁻¹(y - x₀))`, with `G_v` from `gradient_extends_to_fb` applied to the
  rescaled `v = u(x₀ + r ·)/(r Q(x₀))`, `q = Q(x₀ + r ·)/Q(x₀)` (`flat_rescale`). -/
theorem isClassicalNear_of_flat : FlatClassicalStatement := by
  intro d hd L qmin qmax hqmin
  obtain ⟨εg, hεg, Hg⟩ := isC1GammaHypersurfaceNear_of_flat hd L qmin qmax hqmin
  obtain ⟨ε₁, hε₁, H⟩ := gradient_extends_to_fb (d := d) hd
  have hL1 : 0 < (L : ℝ) + 1 := by positivity
  set εbar := min εg (min ε₁ (ε₁ ^ 2 * qmin / (L + 1))) with hεbar_def
  have hεbar : 0 < εbar := lt_min hεg (lt_min hε₁ (by positivity))
  refine ⟨εbar, hεbar, fun U Q u x₀ e r hU hQ hQb hu hx₀ he hr hrε hB hflat ↦ ?_⟩
  have hεbar_g : εbar ≤ εg := min_le_left _ _
  have hεbar_1 : εbar ≤ ε₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hrε₂ : r ≤ ε₁ ^ 2 * qmin / (L + 1) :=
    hrε.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hx₀U : x₀ ∈ U := hB (mem_ball_self hr)
  have hQ0 : 0 < Q x₀ := hqmin.trans_le (hQb x₀ hx₀U).1
  -- the graph
  have hgraph : IsC1GammaHypersurfaceNear (freeBoundary u U) x₀ (r / 2) := by
    refine Hg U Q u x₀ e r hU hQ hQb hu hx₀ he hr (hrε.trans hεbar_g) hB fun y hy ↦ ?_
    obtain ⟨h1, h2⟩ := hflat y hy
    have hmul : εbar * r ≤ εg * r := mul_le_mul_of_nonneg_right hεbar_g hr.le
    exact ⟨le_trans (mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hQ0.le) h1,
      h2.trans (mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) hQ0.le)⟩
  -- harmonicity in the positivity set
  have huH : HarmonicOnNhd u (posSet u U) := IsViscSolution.harmonicOnNhd_posSet hU hu
  -- the rescaled problem and its gradient extension
  obtain ⟨hU', hB', hv, hq, hLip, hflat', hfb⟩ :=
    flat_rescale hU hQ (fun y hy ↦ (hQb y hy).1) hqmin hu hr hB hflat
  have hLr : (L : ℝ) * r / qmin ≤ ε₁ ^ 2 := by
    rw [div_le_iff₀ hqmin]
    rw [le_div_iff₀ hL1] at hrε₂
    linarith
  obtain ⟨Gv, hGc, hGpos, hGfb⟩ := H _ _ _ e ε₁ hU' hB' hv he hε₁ le_rfl
    (fun z hz ↦ (hq z hz).trans hLr) (hLip.weaken (Real.toNNReal_le_toNNReal hLr))
    (fun z hz ↦ by
      obtain ⟨h1, h2⟩ := hflat' z hz
      exact ⟨le_trans (max_le_max (by linarith) le_rfl) h1,
        h2.trans (max_le_max (by linarith) le_rfl)⟩)
  -- transport back: `B y = r⁻¹ (y - x₀)`, `A (B y) = y`
  set Bm : E d → E d := fun y ↦ r⁻¹ • (y - x₀) with hBm
  have hAB : ∀ y, x₀ + r • Bm y = y := fun y ↦ by
    simp [hBm, smul_smul, mul_inv_cancel₀ hr.ne']
  have hBball : ∀ y ∈ ball x₀ (r / 2), Bm y ∈ ball (0 : E d) (1 / 2) := fun y hy ↦ by
    rw [mem_ball, dist_eq_norm] at hy
    rw [mem_ball, dist_zero_right, hBm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr),
      inv_mul_lt_iff₀ hr]
    linarith
  have hpos_v : ∀ y, y ∈ posSet u U → Bm y ∈ posSet (fun z ↦ u (x₀ + r • z) / (r * Q x₀))
      ((fun z ↦ x₀ + r • z) ⁻¹' U) := fun y hy ↦ by
    rw [posSet_rescale x₀ hr hQ0, mem_preimage, hAB]; exact hy
  have hcl_v : ∀ y, y ∈ closure (posSet u U) → Bm y ∈
      closure (posSet (fun z ↦ u (x₀ + r • z) / (r * Q x₀)) ((fun z ↦ x₀ + r • z) ⁻¹' U)) :=
    fun y hy ↦ by rw [closure_posSet_rescale x₀ hr hQ0, mem_preimage, hAB]; exact hy
  have hfb_v : ∀ y, y ∈ freeBoundary u U → Bm y ∈
      freeBoundary (fun z ↦ u (x₀ + r • z) / (r * Q x₀)) ((fun z ↦ x₀ + r • z) ⁻¹' U) :=
    fun y hy ↦ by rw [hfb, mem_preimage, hAB]; exact hy
  refine ⟨r / 2, by positivity, (ball_subset_ball (by linarith)).trans hB, hgraph,
    (huH.contDiffOn).mono inter_subset_left, fun y hy ↦ (huH y hy.1).2.self_of_nhds,
    fun y ↦ Q x₀ • Gv (Bm y), ?_, fun y hy ↦ ?_, fun y hy ↦ ?_⟩
  · -- continuity
    have hBc : Continuous Bm := by fun_prop
    refine (continuous_const.continuousOn.smul (hGc.comp hBc.continuousOn ?_))
    exact fun y hy ↦ ⟨hcl_v y hy.1, hBball y hy.2⟩
  · -- `G = ∇u` in the positivity set
    have hyv := hpos_v y hy.1
    change Q x₀ • Gv (Bm y) = ∇ u y
    rw [hGpos _ ⟨hyv, hBball y hy.2⟩]
    have hdiff : DifferentiableAt ℝ u (x₀ + r • Bm y) := by
      rw [hAB]; exact (huH y hy.1).1.differentiableAt (by norm_num)
    rw [gradient_rescale hr.ne' hdiff, smul_smul, mul_inv_cancel₀ hQ0.ne', one_smul, hAB]
  · -- `‖G‖ = Q` on the free boundary
    have hyv := hfb_v y hy.1
    change ‖Q x₀ • Gv (Bm y)‖ = Q y
    rw [norm_smul, hGfb _ ⟨hyv, hBball y hy.2⟩, Real.norm_eq_abs, abs_of_pos hQ0, hAB]
    field_simp

end EllipticBernoulli
