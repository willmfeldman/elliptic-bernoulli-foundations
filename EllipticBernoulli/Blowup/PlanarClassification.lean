/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Blowup
import EllipticBernoulli.Blowup.Constancy
import EllipticBernoulli.Blowup.Flux
import EllipticBernoulli.Blowup.Homogeneous

/-!
# Classification of planar 1-homogeneous inner variational solutions

We prove `PlanarHomogeneousClassificationStatement` (`EllipticBernoulli/Statements/Blowup.lean`),
the classification after Jerison–Kamburov, §5, as used in the proof sketch of
Abedin–Feldman–Stinson, Corollary 1.2. The proof follows the case analysis in the proof of
Jerison–Kamburov, Proposition 5.3; Propositions 5.3 and 5.4 assume in addition that the solution
is Lipschitz, non-degenerate, and both a viscosity and a variational solution. The list in
Abedin–Feldman–Stinson omits the third alternative, `v ≡ 0` with
`χ = 0` a.e., which is also an inner variational solution; and the two-plane family includes
`α = 0` (`v ≡ 0`, `χ = 1` a.e.).

## Proof

* **Step 1** (`eq_halfPlanes_of_homogeneous`, `Blowup/Homogeneous.lean`): `v ≡ 0`, or
  `v = a (y·e)₊ + b (y·e)₋` with `‖e‖ = 1`, `a > 0`, `b ≥ 0`.
* **Step 2** (`IsInnerVarSolution.hasWeakGradient_zero_of_eqOn_zero`, this file): on an open set
  where `v = 0`, the inner variation identity with `ξ = φ w` reads `q² ∫ χ ∂_w φ = 0`, so `χ` has
  zero weak gradient there, hence is a.e. constant on each connected open piece
  (`exists_ae_eq_const_of_hasWeakGradient_zero`, `Blowup/Constancy.lean`). As `χ ∈ {0, 1}`, the
  constant is `0` or `1`. Where `v > 0`, `χ = 1` a.e. by `pos_le`.
* **Step 3** (`IsInnerVarSolution.flux_eq`, `Blowup/Flux.lean`): `q² − a² = q² c − b²`, where `c`
  is the value of `χ` on `{y·e < 0}`.
* **Case analysis.** `b > 0`: then `c = 1` and `a = b` (case 2). `b = 0`: `c = 1` would force
  `a = 0`, so `c = 0` and `a = q` (case 1). `v ≡ 0`: `χ ≡ c` a.e. on `ℝ²`; `c = 1` is case 2 with
  `α = 0`, `c = 0` is case 3.

## References

* D. Jerison, N. Kamburov, *Structure of one-phase free boundaries in the plane*, Int. Math. Res.
  Not. IMRN 2016, no. 19, 5922–5987; arXiv:1412.4106.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient RealInnerProductSpace ContDiff Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- For `ξ = φ w` with `φ` differentiable at `x`: `Dξ(x) = Dφ(x) ⊗ w`. -/
private theorem fderiv_smul_const_apply' {φ : E d → ℝ} {x : E d} (hφ : DifferentiableAt ℝ φ x)
    (w z : E d) : fderiv ℝ (fun y ↦ φ y • w) x z = fderiv ℝ φ x z • w := by
  rw [fderiv_smul_const hφ]
  simp

/-- For `ξ = φ w` with `φ` differentiable at `x`: `div ξ(x) = ∂_w φ(x)`. -/
private theorem divergence_smul_const {φ : E d → ℝ} {x : E d} (hφ : DifferentiableAt ℝ φ x)
    (w : E d) : divergence (fun y ↦ φ y • w) x = fderiv ℝ φ x w := by
  rw [divergence, fderiv_smul_const hφ]
  exact LinearMap.trace_smulRight _ _

/-- A measurable `{0, 1}`-valued function is locally integrable. -/
private theorem locallyIntegrable_of_zero_one {χ : E d → ℝ} (hm : Measurable χ)
    (h01 : ∀ x, χ x = 0 ∨ χ x = 1) : LocallyIntegrable χ := by
  refine (locallyIntegrable_iff (μ := volume)).2 fun K hK ↦ ?_
  refine Measure.integrableOn_of_bounded (M := 1) hK.measure_lt_top.ne
    hm.aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  rcases h01 x with h | h <;> simp [h]

/-- **Step 2.** Where `v` vanishes on an open set `Ω`, the inner variation identity says that
`χ` has zero weak gradient in `Ω` (`q ≠ 0`). -/
theorem IsInnerVarSolution.hasWeakGradient_zero_of_eqOn_zero {q : ℝ} (hq : q ≠ 0)
    {v χ : E d → ℝ} (hv : IsInnerVarSolution univ (fun _ ↦ q) v χ) {Ω : Set (E d)}
    (hΩ : IsOpen Ω) (hv0 : ∀ y ∈ Ω, v y = 0) : HasWeakGradient Ω χ 0 := by
  refine ⟨(locallyIntegrable_of_zero_one hv.meas fun x ↦ hv.zero_one x trivial).locallyIntegrableOn
    Ω, (locallyIntegrable_zero).locallyIntegrableOn Ω, fun φ hφ hφc hφΩ w ↦ ?_⟩
  simp only [Pi.zero_apply, inner_zero_left, zero_mul, integral_zero, neg_zero]
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  set ξ : E d → E d := fun y ↦ φ y • w with hξ
  have hξc : ContDiff ℝ ∞ ξ := hφ.smul contDiff_const
  have hξs : HasCompactSupport ξ := hφc.smul_right
  obtain ⟨K, hK⟩ := hξc.lipschitzWith_of_hasCompactSupport hξs (by simp)
  have hstat := hv.stationary ξ ⟨K, hK⟩ hξs (subset_univ _)
  rw [Measure.restrict_univ] at hstat
  have hpt : ∀ x, innerVarIntegrand (fun _ ↦ q) v χ ξ x =
      q ^ 2 * Ω.indicator (fun x ↦ χ x * fderiv ℝ φ x w) x := by
    intro x
    by_cases hx : x ∈ Ω
    · have hg : ∇ v x = 0 := by
        refine gradient_eq_of_eventuallyEq_inner ?_
        filter_upwards [hΩ.mem_nhds hx] with z hz
        simp [hv0 z hz]
      rw [indicator_of_mem hx]
      simp only [innerVarIntegrand, hg, norm_zero, inner_zero_left, divergence_smul_const (hφd x),
        fderiv_const_apply, zero_apply, hξ]
      ring
    · have h0 : fderiv ℝ φ x = 0 := fderiv_of_notMem_tsupport ℝ fun h ↦ hx (hφΩ h)
      rw [indicator_of_notMem hx]
      simp only [innerVarIntegrand, hξ, divergence_smul_const (hφd x),
        fderiv_smul_const_apply' (hφd x), h0, zero_apply, zero_smul,
        inner_zero_right, fderiv_const_apply]
      ring
  simp_rw [hpt] at hstat
  rw [integral_const_mul, integral_indicator hΩ.measurableSet] at hstat
  exact (mul_eq_zero.1 hstat).resolve_left (pow_ne_zero 2 hq)

/-- On a connected open set `Ω` of positive measure where `v = 0`, `χ` is a.e. equal to `0` or to
`1` on `Ω`. -/
private theorem IsInnerVarSolution.exists_ae_eq_zero_one {q : ℝ} (hq : q ≠ 0)
    {v χ : E d → ℝ} (hv : IsInnerVarSolution univ (fun _ ↦ q) v χ) {Ω : Set (E d)}
    (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω) (hΩne : Ω.Nonempty) (hv0 : ∀ y ∈ Ω, v y = 0) :
    ∃ c : ℝ, (c = 0 ∨ c = 1) ∧ ∀ᵐ y, y ∈ Ω → χ y = c := by
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_hasWeakGradient_zero hΩ hΩc
    (hv.hasWeakGradient_zero_of_eqOn_zero hq hΩ hv0)
  have hpos : volume.restrict Ω ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]
    exact (hΩ.measure_pos volume hΩne).ne'
  have : (ae (volume.restrict Ω)).NeBot := ae_neBot.2 hpos
  obtain ⟨x, hx⟩ := hc.exists
  refine ⟨c, ?_, (ae_restrict_iff' hΩ.measurableSet).1 hc⟩
  rw [← hx]
  exact hv.zero_one x trivial

private theorem max_add_max_neg (a t : ℝ) : a * max t 0 + a * max (-t) 0 = a * |t| := by
  rcases le_total t 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring

/-- Classification of planar 1-homogeneous inner variational solutions
(`PlanarHomogeneousClassificationStatement`). -/
theorem classification_homogeneous_planar : PlanarHomogeneousClassificationStatement := by
  intro q hq v χ hv hhom
  have hpos : posSet v univ = {y | 0 < v y} := by ext; simp [posSet]
  have hcont : Continuous v := continuousOn_univ.1 hv.locLip.continuousOn
  have hposle : ∀ᵐ y, 0 < v y → χ y = 1 := by
    simpa [Measure.restrict_univ] using hv.pos_le
  rcases eq_halfPlanes_of_homogeneous hcont (fun y ↦ hv.nonneg y trivial) (hpos ▸ hv.c2)
      (fun y hy ↦ hv.harmonic y (hpos ▸ hy)) hhom with hzero | ⟨e, he, a, b, ha, hb, hvab⟩
  · -- `v ≡ 0`: `χ` is a.e. constant on `ℝ²`.
    obtain ⟨c, hc01, hc⟩ := hv.exists_ae_eq_zero_one hq.ne' isOpen_univ isPreconnected_univ
      univ_nonempty fun y _ ↦ hzero y
    refine ⟨EuclideanSpace.single 0 1, by simp, ?_⟩
    rcases hc01 with rfl | rfl
    · exact Or.inr (Or.inr ⟨hzero, by filter_upwards [hc] with y hy using hy trivial⟩)
    · exact Or.inr (Or.inl ⟨0, le_rfl, fun y ↦ by simp [hzero y],
        by filter_upwards [hc] with y hy using hy trivial⟩)
  refine ⟨e, he, ?_⟩
  have hcontI : Continuous fun y : E 2 ↦ ⟪y, e⟫ := continuous_id.inner continuous_const
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hline : ∀ᵐ y : E 2, ⟪y, e⟫ ≠ 0 := by
    rw [ae_iff]
    simpa using volume_inner_eq_zero he0
  -- `χ = 1` a.e. on `{y·e > 0}`.
  have hχp : ∀ᵐ y, 0 < ⟪y, e⟫ → χ y = 1 := by
    filter_upwards [hposle] with y hy hye
    refine hy ?_
    rw [hvab, max_eq_left hye.le]
    have : 0 ≤ b * max (-⟪y, e⟫) 0 := mul_nonneg hb (le_max_right _ _)
    nlinarith
  rcases hb.eq_or_lt with rfl | hbpos
  · -- One half-plane: `χ` is a.e. a constant `c ∈ {0, 1}` on `{y·e < 0}`; the flux gives
    -- `q² − a² = q² c`, so `c = 0` and `a = q`.
    have hlin : IsLinearMap ℝ fun y : E 2 ↦ ⟪y, e⟫ :=
      ⟨fun x y ↦ inner_add_left x y e, fun c x ↦ real_inner_smul_left x e c⟩
    have hne : ({y : E 2 | ⟪y, e⟫ < 0}).Nonempty :=
      ⟨-e, by simp [he]⟩
    obtain ⟨c, hc01, hc⟩ := hv.exists_ae_eq_zero_one hq.ne' (isOpen_lt hcontI continuous_const)
      (convex_halfSpace_lt hlin 0).isPreconnected hne fun y hy ↦ by
        rw [hvab, max_eq_right (le_of_lt hy)]; ring
    have hflux := hv.flux_eq he hvab hχp hc
    rcases hc01 with rfl | rfl
    · have haq : a = q := by nlinarith
      subst haq
      refine Or.inl ⟨fun y ↦ by rw [hvab]; ring, ?_⟩
      filter_upwards [hχp, hc, hline] with y h1 h2 h3
      rcases lt_or_gt_of_ne h3 with h | h
      · rw [h2 h, indicator_of_notMem (show y ∉ {z : E 2 | 0 < ⟪z, e⟫} from
          fun hh ↦ by simp only [mem_ofPred_eq] at hh; linarith)]
      · rw [h1 h, indicator_of_mem (show y ∈ {z : E 2 | 0 < ⟪z, e⟫} from h), Pi.one_apply]
    · exfalso
      nlinarith
  · -- Two half-planes: `χ = 1` a.e. and the flux gives `a = b`.
    have hχ1 : ∀ᵐ y, χ y = 1 := by
      filter_upwards [hposle, hline] with y hy hye
      refine hy ?_
      rw [hvab]
      rcases lt_or_gt_of_ne hye with h | h
      · rw [max_eq_right h.le, max_eq_left (by linarith)]
        nlinarith
      · rw [max_eq_left h.le, max_eq_right (by linarith)]
        nlinarith
    have hflux := hv.flux_eq he hvab hχp (c := 1) (by filter_upwards [hχ1] with y hy _ using hy)
    have hab : a = b := by nlinarith
    subst hab
    exact Or.inr (Or.inl ⟨a, ha.le, fun y ↦ by rw [hvab, max_add_max_neg], hχ1⟩)

end EllipticBernoulli
