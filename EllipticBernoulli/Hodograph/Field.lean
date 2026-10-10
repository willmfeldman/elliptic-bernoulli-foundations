/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Flatness.Graph
public import BasicElliptic.Basic.HalfSpace
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Linear algebra of the partial hodograph transform

Fix a unit vector `e` and write `P z = z - (z · e) e` for the projection onto `e^⊥`
(`perpProj`). For `u` with `p = ∇u(y)`, `p · e ≠ 0`, the hodograph map `y ↦ P(y - x₀) + u(y) e` has
derivative `h ↦ P h + (p · h) e` (`hodoCLM e p`), with inverse `hodoInvCLM e p`. If
`w(x', t)` is the height of the level `{u = t}` over `x'`, then `∇w = gradVec e p`, where
`gradVec e p = (p · e)⁻¹ (e - P p)`.

The hodograph equation is `div Φ(∇w) = 0` with `Φ = field e`, the gradient of the potential
`Φ₀(q) = (1 + |P q|²) / (q · e) + q · e` (Kinderlehrer–Nirenberg (1977)). Along the transform,
`Φ(∇w) = fieldOf e p = -2 P p + (1 - |p|²) e` (`field_gradVec`), so the conormal condition
`Φ(∇w) · e = 0` is the free boundary condition `|∇u| = 1` (`inner_fieldOf`).

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
-/

open Set Metric InnerProductSpace
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace EllipticBernoulli.Hodograph

variable {d : ℕ}

/-- The hodograph potential `Φ₀(q) = (1 + |P q|²) / (q · e) + q · e`. -/
def potential (e q : E d) : ℝ := (1 + ‖perpProj e q‖ ^ 2) / ⟪q, e⟫ + ⟪q, e⟫

/-- The hodograph flux `Φ(q) = ∇Φ₀(q) = (2 / (q · e)) P q + (1 - (1 + |P q|²) / (q · e)²) e`. -/
def field (e q : E d) : E d :=
  (2 / ⟪q, e⟫) • perpProj e q + (1 - (1 + ‖perpProj e q‖ ^ 2) / ⟪q, e⟫ ^ 2) • e

/-- The gradient of the hodograph height in terms of `p = ∇u`: `(p · e)⁻¹ (e - P p)`. -/
def gradVec (e p : E d) : E d := ⟪p, e⟫⁻¹ • (e - perpProj e p)

/-- The flux in terms of `p = ∇u`: `-2 P p + (1 - |p|²) e`. -/
def fieldOf (e p : E d) : E d := (-2 : ℝ) • perpProj e p + (1 - ‖p‖ ^ 2) • e

/-- `P` as a continuous linear map. -/
def perpCLM (e : E d) : E d →L[ℝ] E d :=
  ContinuousLinearMap.id ℝ (E d) - (innerSL ℝ e).smulRight e

/-- The derivative of the hodograph map: `h ↦ P h + (p · h) e`. -/
def hodoCLM (e p : E d) : E d →L[ℝ] E d := perpCLM e + (innerSL ℝ p).smulRight e

/-- The inverse of `hodoCLM e p`: `k ↦ P k + (p · e)⁻¹ (e · k - p · P k) e`. -/
def hodoInvCLM (e p : E d) : E d →L[ℝ] E d :=
  perpCLM e + (⟪p, e⟫⁻¹ • (innerSL ℝ e - (innerSL ℝ p).comp (perpCLM e))).smulRight e

end EllipticBernoulli.Hodograph

end

public section

namespace EllipticBernoulli.Hodograph

variable {d : ℕ} {e p : E d}

theorem perpCLM_apply (e h : E d) : perpCLM e h = perpProj e h := by
  simp [perpCLM, perpProj, real_inner_comm]

theorem hodoCLM_apply (e p h : E d) : hodoCLM e p h = perpProj e h + ⟪p, h⟫ • e := by
  simp [hodoCLM, perpCLM_apply]

theorem hodoInvCLM_apply (e p k : E d) :
    hodoInvCLM e p k = perpProj e k + (⟪p, e⟫⁻¹ * (⟪e, k⟫ - ⟪p, perpProj e k⟫)) • e := by
  simp [hodoInvCLM, perpCLM_apply]

theorem perpProj_self (he : ‖e‖ = 1) : perpProj e e = 0 := by
  simp [perpProj, he]

theorem inner_self_of_norm (he : ‖e‖ = 1) : ⟪e, e⟫ = 1 := by
  rw [real_inner_self_eq_norm_sq, he, one_pow]

/-- `⟪p, h⟫ - ⟪p, P h⟫ = ⟪h, e⟫ ⟪p, e⟫`. -/
theorem inner_sub_inner_perpProj (e p h : E d) :
    ⟪p, h⟫ - ⟪p, perpProj e h⟫ = ⟪h, e⟫ * ⟪p, e⟫ := by
  simp only [perpProj, inner_sub_right, real_inner_smul_right]; ring

theorem hodoInvCLM_hodoCLM (he : ‖e‖ = 1) (hp : ⟪p, e⟫ ≠ 0) (h : E d) :
    hodoInvCLM e p (hodoCLM e p h) = h := by
  rw [hodoInvCLM_apply, hodoCLM_apply, perpProj_add_smul he, perpProj_perpProj he]
  have h1 : ⟪e, perpProj e h + ⟪p, h⟫ • e⟫ = ⟪p, h⟫ := by
    rw [inner_add_right, real_inner_comm, inner_perpProj he, real_inner_smul_right,
      inner_self_of_norm he]; ring
  rw [h1, inner_sub_inner_perpProj, mul_comm ⟪h, e⟫, ← mul_assoc, inv_mul_cancel₀ hp, one_mul,
    perpProj_add_inner_smul]

theorem hodoCLM_hodoInvCLM (he : ‖e‖ = 1) (hp : ⟪p, e⟫ ≠ 0) (k : E d) :
    hodoCLM e p (hodoInvCLM e p k) = k := by
  rw [hodoCLM_apply, hodoInvCLM_apply, perpProj_add_smul he, perpProj_perpProj he,
    inner_add_right, real_inner_smul_right]
  have : ⟪p, perpProj e k⟫ + ⟪p, e⟫⁻¹ * (⟪e, k⟫ - ⟪p, perpProj e k⟫) * ⟪p, e⟫ = ⟪k, e⟫ := by
    rw [real_inner_comm e k]; field_simp; ring
  rw [this, perpProj_add_inner_smul]

/-- The derivative of the hodograph map as a continuous linear equivalence. -/
@[expose] noncomputable def hodoEquiv (he : ‖e‖ = 1) (hp : ⟪p, e⟫ ≠ 0) : E d ≃L[ℝ] E d :=
  ContinuousLinearEquiv.equivOfInverse (hodoCLM e p) (hodoInvCLM e p)
    (hodoInvCLM_hodoCLM he hp) (hodoCLM_hodoInvCLM he hp)

@[simp] theorem hodoEquiv_apply (he : ‖e‖ = 1) (hp : ⟪p, e⟫ ≠ 0) (h : E d) :
    hodoEquiv he hp h = hodoCLM e p h := rfl

@[simp] theorem hodoEquiv_symm_apply (he : ‖e‖ = 1) (hp : ⟪p, e⟫ ≠ 0) (k : E d) :
    (hodoEquiv he hp).symm k = hodoInvCLM e p k := rfl

/-- The `e`-component of the inverse is `⟪gradVec e p, ·⟫`. -/
theorem inner_hodoInvCLM (he : ‖e‖ = 1) (k : E d) :
    ⟪e, hodoInvCLM e p k⟫ = ⟪gradVec e p, k⟫ := by
  rw [hodoInvCLM_apply, inner_add_right, real_inner_comm, inner_perpProj he,
    real_inner_smul_right, inner_self_of_norm he, gradVec, real_inner_smul_left, inner_sub_left,
    real_inner_comm k e, inner_perpProj_eq p k]
  ring

theorem inner_gradVec (he : ‖e‖ = 1) : ⟪gradVec e p, e⟫ = ⟪p, e⟫⁻¹ := by
  rw [gradVec, real_inner_smul_left, inner_sub_left, inner_perpProj he, inner_self_of_norm he]
  ring

theorem perpProj_gradVec (he : ‖e‖ = 1) :
    perpProj e (gradVec e p) = -⟪p, e⟫⁻¹ • perpProj e p := by
  rw [gradVec, ← perpCLM_apply, map_smul, map_sub, perpCLM_apply, perpCLM_apply,
    perpProj_self he, perpProj_perpProj he, zero_sub, smul_neg, neg_smul]

/-- Along the transform, the flux is `fieldOf e p`. -/
theorem field_gradVec (he : ‖e‖ = 1) (hp : ⟪p, e⟫ ≠ 0) : field e (gradVec e p) = fieldOf e p := by
  rw [field, fieldOf, perpProj_gradVec he, inner_gradVec he, norm_smul, mul_pow, smul_smul,
    Real.norm_eq_abs, sq_abs, norm_perpProj_sq he]
  congr 2
  · field_simp
  · field_simp; ring

theorem gradVec_self (he : ‖e‖ = 1) : gradVec e e = e := by
  rw [gradVec, perpProj_self he, sub_zero, inner_self_of_norm he, inv_one, one_smul]

theorem inner_fieldOf (he : ‖e‖ = 1) (p : E d) : ⟪fieldOf e p, e⟫ = 1 - ‖p‖ ^ 2 := by
  rw [fieldOf, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_perpProj he,
    inner_self_of_norm he]
  ring

theorem inner_field (he : ‖e‖ = 1) (q : E d) :
    ⟪field e q, e⟫ = 1 - (1 + ‖perpProj e q‖ ^ 2) / ⟪q, e⟫ ^ 2 := by
  rw [field, inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_perpProj he,
    inner_self_of_norm he]
  ring

theorem norm_gradVec_sq (he : ‖e‖ = 1) (q : E d) :
    ‖gradVec e q‖ ^ 2 = (1 + ‖perpProj e q‖ ^ 2) / ⟪q, e⟫ ^ 2 := by
  have h1 : ‖e - perpProj e q‖ ^ 2 = 1 + ‖perpProj e q‖ ^ 2 := by
    rw [norm_sub_sq_real, he, real_inner_comm, inner_perpProj he]; ring
  rw [gradVec, norm_smul, mul_pow, h1, Real.norm_eq_abs, sq_abs, inv_pow, div_eq_inv_mul]

/-- The conormal condition `Φ(q) · e = 0` says `|gradVec e q| = 1`. -/
theorem norm_gradVec_of_inner_field (he : ‖e‖ = 1) {q : E d} (h : ⟪field e q, e⟫ = 0) :
    ‖gradVec e q‖ = 1 := by
  have h2 : ‖gradVec e q‖ ^ 2 = 1 := by
    rw [norm_gradVec_sq he]; rw [inner_field he] at h; linarith
  have := norm_nonneg (gradVec e q)
  nlinarith [sq_nonneg (‖gradVec e q‖ - 1), sq_nonneg (‖gradVec e q‖ + 1)]

theorem gradVec_ne_zero (he : ‖e‖ = 1) {q : E d} (hq : ⟪q, e⟫ ≠ 0) : gradVec e q ≠ 0 := by
  intro h0
  have := inner_gradVec (p := q) he
  rw [h0, inner_zero_left] at this
  exact inv_ne_zero hq this.symm

theorem continuousAt_gradVec {q : E d} (hq : ⟪q, e⟫ ≠ 0) : ContinuousAt (gradVec e) q := by
  have hP : Continuous (perpProj e) := by
    have : perpProj e = fun z ↦ perpCLM e z := funext fun z ↦ (perpCLM_apply e z).symm
    rw [this]; exact (perpCLM e).continuous
  unfold gradVec
  exact ((continuous_id.inner continuous_const).continuousAt.inv₀ hq).smul
    (continuous_const.sub hP).continuousAt

end EllipticBernoulli.Hodograph
