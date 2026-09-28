/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Viscosity.Basic
public import EllipticBernoulli.Lipschitz.Barrier
import EllipticBernoulli.Viscosity.Calculus
import EllipticBernoulli.Viscosity.Jet

/-!
# Exponential radial barriers for non-degeneracy

* `expProfile p σ λ A y = A (1 - exp(-λ (|y - p|² - σ²)))`: a globally smooth radial profile
  vanishing on `∂B_σ(p)`, with
  `|∇H| = |A λ e^{-λ(|y-p|²-σ²)}| · 2|y - p|` (`norm_gradient_expProfile`) and
  `ΔH = A λ e^{-λ(|y-p|²-σ²)} (2d - 4λ|y - p|²)` (`laplacian_expProfile`).
  This is the barrier of the exterior-ball lemma `exists_le_of_exteriorBall`
  (Abedin–Feldman–Stinson, Lemma B.2).
* `nondegProfile z σ A = expProfile z σ (d / (2σ²)) A`, and the
  **supersolution barrier** `nondegBarrier z σ A = max (nondegProfile z σ A) 0`. It vanishes on
  `B̄_σ(z)` (`nondegBarrier_eq_zero`), is `≥ 5A/13` off `B_{3σ/2}(z)` (`le_nondegProfile`), and is
  a viscosity supersolution wherever `Q ≥ A d / σ` (`isViscSuper_nondegBarrier`). This is the
  barrier of the smallest-supersolution non-degeneracy theorem.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
  in the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The exponential profile -/

/-- The radial profile `H(y) = A (1 - exp(-λ (|y - p|² - σ²)))` with a general rate `λ`. -/
def expProfile (p : E d) (σ lam A : ℝ) (y : E d) : ℝ :=
  A - A * Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2)))

/-- `expProfile` as a function of `t = |y - p|²`. -/
def expProfileF (σ lam A : ℝ) (t : ℝ) : ℝ :=
  A - A * Real.exp (-(lam * (t - σ ^ 2)))

/-- The supersolution profile `S(y) = A (1 - exp(-λ (|y - z|² - σ²)))`, `λ = d / (2σ²)`. It
vanishes on `∂B_σ(z)`, is positive outside and negative inside `B_σ(z)`, and superharmonic
outside `B_σ(z)`. -/
def nondegProfile (z : E d) (σ A : ℝ) (y : E d) : ℝ :=
  A - A * Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2)))

/-- `nondegProfile` as a function of `t = |y - z|²`. -/
def nondegProfileF (σ A : ℝ) (d : ℕ) (t : ℝ) : ℝ :=
  A - A * Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (t - σ ^ 2)))

/-- The non-degeneracy barrier `w = max(S, 0)`: a viscosity supersolution vanishing on
`B̄_σ(z)` with free boundary slope `A d / σ`. -/
def nondegBarrier (z : E d) (σ A : ℝ) (y : E d) : ℝ :=
  max (nondegProfile z σ A y) 0

end EllipticBernoulli

end

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Calculus of the supersolution profile -/

section Profile

variable {z : E d} {σ A : ℝ}

theorem contDiff_nondegProfile (z : E d) (σ A : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (nondegProfile z σ A) := by
  have hg : ContDiff ℝ n (fun y : E d ↦ ‖y - z‖ ^ 2) := contDiff_normSq_sub_const z
  unfold nondegProfile
  exact contDiff_const.sub (contDiff_const.mul (Real.contDiff_exp.comp
    ((contDiff_const.mul (hg.sub contDiff_const)).neg)))

theorem nondegProfile_eq (y : E d) :
    nondegProfile z σ A y = nondegProfileF σ A d (‖y - z‖ ^ 2) := rfl

theorem hasDerivAt_nondegProfileF (t : ℝ) :
    HasDerivAt (nondegProfileF σ A d) (A * ((d : ℝ) / (2 * σ ^ 2)) *
      Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (t - σ ^ 2)))) t := by
  set lm := (d : ℝ) / (2 * σ ^ 2)
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lm * (t - σ ^ 2))) (-lm) t := by
    simpa using (((hasDerivAt_id t).sub_const (σ ^ 2)).const_mul lm).neg
  have h2 := (h1.exp.const_mul A).const_sub A
  convert h2 using 1
  ring

theorem deriv_nondegProfileF : deriv (nondegProfileF σ A d) = fun t ↦
    A * ((d : ℝ) / (2 * σ ^ 2)) * Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (t - σ ^ 2))) :=
  funext fun t ↦ (hasDerivAt_nondegProfileF t).deriv

theorem deriv_deriv_nondegProfileF (t : ℝ) : deriv (deriv (nondegProfileF σ A d)) t =
    -(A * ((d : ℝ) / (2 * σ ^ 2)) ^ 2 * Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (t - σ ^ 2)))) := by
  rw [deriv_nondegProfileF]
  set lm := (d : ℝ) / (2 * σ ^ 2)
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lm * (t - σ ^ 2))) (-lm) t := by
    simpa using (((hasDerivAt_id t).sub_const (σ ^ 2)).const_mul lm).neg
  have h2 := h1.exp.const_mul (A * lm)
  rw [h2.deriv]
  ring

theorem norm_gradient_nondegProfile (y : E d) :
    ‖∇ (nondegProfile z σ A) y‖ = |A * ((d : ℝ) / (2 * σ ^ 2)) *
      Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2)))| * (2 * ‖y - z‖) := by
  have hcomp : HasFDerivAt (fun y ↦ nondegProfileF σ A d (‖y - z‖ ^ 2))
      ((A * ((d : ℝ) / (2 * σ ^ 2)) * Real.exp (-((d : ℝ) / (2 * σ ^ 2) *
        (‖y - z‖ ^ 2 - σ ^ 2)))) • ((2 : ℝ) • innerSL ℝ (y - z))) y :=
    (hasDerivAt_nondegProfileF (σ := σ) (A := A) (d := d) (‖y - z‖ ^ 2)).comp_hasFDerivAt
      (f := fun y : E d ↦ ‖y - z‖ ^ 2) y (hasFDerivAt_normSq_sub_const z y)
  have hS : nondegProfile z σ A = fun y ↦ nondegProfileF σ A d (‖y - z‖ ^ 2) := rfl
  rw [hS, norm_gradient_eq_norm_fderiv, hcomp.fderiv, norm_smul, norm_smul, innerSL_apply_norm,
    Real.norm_eq_abs]
  norm_num

theorem laplacian_nondegProfile_nonpos (hA : 0 ≤ A) (hσ : 0 < σ) {y : E d}
    (hy : σ ≤ ‖y - z‖) : Δ (nondegProfile z σ A) y ≤ 0 := by
  have hcomp := laplacian_comp (f := nondegProfileF σ A d) (g := fun y : E d ↦ ‖y - z‖ ^ 2)
    (x := y) (by unfold nondegProfileF; fun_prop) (contDiff_normSq_sub_const z).contDiffAt
  have hS : nondegProfile z σ A = fun y ↦ nondegProfileF σ A d (‖y - z‖ ^ 2) := rfl
  rw [hS, hcomp, deriv_deriv_nondegProfileF, deriv_nondegProfileF, norm_gradient_normSq_sub,
    laplacian_normSq_sub_const, finrank_euclideanSpace_fin]
  simp only
  set E' := Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2)))
  have hE : 0 < E' := Real.exp_pos _
  have hσ2 : 0 < σ ^ 2 := by positivity
  have ht : σ ^ 2 ≤ ‖y - z‖ ^ 2 := pow_le_pow_left₀ hσ.le hy 2
  set t := ‖y - z‖ ^ 2
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- `Δ = A λ E (2d - 4 λ t)` with `λ t ≥ d/2`
  have hlt : (d : ℝ) / 2 ≤ (d : ℝ) / (2 * σ ^ 2) * t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have key : -(A * ((d : ℝ) / (2 * σ ^ 2)) ^ 2 * E') * (2 * ‖y - z‖) ^ 2 +
      A * ((d : ℝ) / (2 * σ ^ 2)) * E' * (2 * (d : ℝ)) =
      A * ((d : ℝ) / (2 * σ ^ 2)) * E' * (2 * d - 4 * ((d : ℝ) / (2 * σ ^ 2) * t)) := by
    rw [mul_pow]; ring
  rw [key]
  have hlm : 0 ≤ (d : ℝ) / (2 * σ ^ 2) := by positivity
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem nondegProfile_pos (hA : 0 < A) (hσ : 0 < σ) (hd : 1 ≤ d) {y : E d}
    (hy : σ < ‖y - z‖) : 0 < nondegProfile z σ A y := by
  unfold nondegProfile
  have hlm : 0 < (d : ℝ) / (2 * σ ^ 2) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have ht : σ ^ 2 < ‖y - z‖ ^ 2 := pow_lt_pow_left₀ hy hσ.le two_ne_zero
  have : Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) < 1 :=
    Real.exp_lt_one_iff.2 (by nlinarith)
  nlinarith

theorem nondegProfile_neg (hA : 0 < A) (hσ : 0 < σ) (hd : 1 ≤ d) {y : E d}
    (hy : ‖y - z‖ < σ) : nondegProfile z σ A y < 0 := by
  unfold nondegProfile
  have hlm : 0 < (d : ℝ) / (2 * σ ^ 2) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have ht : ‖y - z‖ ^ 2 < σ ^ 2 := pow_lt_pow_left₀ hy (norm_nonneg _) two_ne_zero
  have : 1 < Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) :=
    Real.one_lt_exp_iff.2 (by nlinarith)
  nlinarith

theorem nondegProfile_eq_zero {y : E d} (hy : ‖y - z‖ = σ) : nondegProfile z σ A y = 0 := by
  unfold nondegProfile
  rw [hy]; simp

/-- Lower bound of the barrier away from `B_{3σ/2}(z)`: `w ≥ 5A/13`. -/
theorem le_nondegProfile (hA : 0 ≤ A) (hσ : 0 < σ) (hd : 1 ≤ d) {y : E d}
    (hy : 3 * σ / 2 ≤ ‖y - z‖) : 5 * A / 13 ≤ nondegProfile z σ A y := by
  unfold nondegProfile
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hσ2 : 0 < σ ^ 2 := by positivity
  have ht : 9 / 4 * σ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hy 2
    nlinarith
  have harg : 5 / 8 ≤ (d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hexp : Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) ≤ 8 / 13 := by
    have h1 : Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) ≤
        Real.exp (-(5 / 8)) := Real.exp_le_exp.2 (by linarith)
    have h2 : (13 / 8 : ℝ) ≤ Real.exp (5 / 8) := by
      have := Real.add_one_le_exp (5 / 8 : ℝ); linarith
    have h3 : Real.exp (-(5 / 8 : ℝ)) ≤ 8 / 13 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    linarith
  nlinarith

end Profile

/-- **The barrier is a viscosity supersolution** wherever `Q ≥ A d / σ`. -/
theorem isViscSuper_nondegBarrier {W : Set (E d)} (hW : IsOpen W) {Q : E d → ℝ} {z : E d}
    {σ A : ℝ} (hA : 0 < A) (hσ : 0 < σ) (hd : 1 ≤ d) (hQ : ∀ x ∈ W, A * d / σ ≤ Q x) :
    IsViscSuper W Q (nondegBarrier z σ A) := by
  have hSc : ContDiff ℝ ∞ (nondegProfile z σ A) := contDiff_nondegProfile z σ A
  refine ⟨(hSc.continuous.max continuous_const).continuousOn, fun _ _ ↦ le_max_right _ _, ?_⟩
  intro φ hφ x hx htouch
  have hle := htouch.eventually_le_of_isOpen hW
  have hφ2 : ContDiff ℝ 2 φ := contDiff_two_of_smooth hφ
  have hcont : Continuous fun y : E d ↦ ‖y - z‖ := continuous_norm.comp (continuous_sub_right z)
  rcases lt_trichotomy ‖x - z‖ σ with hlt | heq | hgt
  · left
    have hnear : ∀ᶠ y in 𝓝 x, ‖y - z‖ < σ := hcont.continuousAt.eventually (gt_mem_nhds hlt)
    have hφx : φ x = 0 := by
      rw [htouch.2.1, nondegBarrier, max_eq_right (nondegProfile_neg hA hσ hd hlt).le]
    refine IsLocalMax.laplacian_nonpos hφ2 ?_
    filter_upwards [hle, hnear] with y hy hy'
    rw [hφx]
    rwa [nondegBarrier, max_eq_right (nondegProfile_neg hA hσ hd hy').le] at hy
  · right
    have hS0 : nondegProfile z σ A x = 0 := nondegProfile_eq_zero heq
    have hφx : φ x = 0 := by rw [htouch.2.1, nondegBarrier, hS0, max_self]
    refine ⟨hφx, ?_⟩
    have h := norm_gradient_le_of_le_max (hφ.differentiable (by simp)).differentiableAt
      (hSc.differentiable (by simp)).differentiableAt hφx hS0 hle
    rw [norm_gradient_nondegProfile, heq] at h
    refine h.trans (le_of_eq_of_le ?_ (hQ x hx))
    simp only [sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one]
    rw [abs_of_nonneg (by positivity)]
    field_simp
  · left
    have hnear : ∀ᶠ y in 𝓝 x, σ < ‖y - z‖ := hcont.continuousAt.eventually (lt_mem_nhds hgt)
    have hx' : φ x = nondegProfile z σ A x := by
      rw [htouch.2.1, nondegBarrier, max_eq_left (nondegProfile_pos hA hσ hd hgt).le]
    refine (laplacian_le_of_eventually_le hφ2.contDiffAt
      (contDiff_two_of_smooth hSc).contDiffAt hx' ?_).trans
      (laplacian_nondegProfile_nonpos hA.le hσ hgt.le)
    filter_upwards [hle, hnear] with y hy hy'
    rwa [nondegBarrier, max_eq_left (nondegProfile_pos hA hσ hd hy').le] at hy

theorem nondegBarrier_eq_zero {z : E d} {σ A : ℝ} (hA : 0 < A) (hσ : 0 < σ) (hd : 1 ≤ d)
    {y : E d} (hy : ‖y - z‖ ≤ σ) : nondegBarrier z σ A y = 0 := by
  rcases hy.lt_or_eq with h | h
  · exact max_eq_right (nondegProfile_neg hA hσ hd h).le
  · rw [nondegBarrier, nondegProfile_eq_zero h, max_self]

/-! ### Calculus of the exponential profile -/

section Exp

variable {p : E d} {σ lam A : ℝ}

theorem contDiff_expProfile {n : WithTop ℕ∞} : ContDiff ℝ n (expProfile p σ lam A) := by
  have hg : ContDiff ℝ n (fun y : E d ↦ ‖y - p‖ ^ 2) := contDiff_normSq_sub_const p
  unfold expProfile
  exact contDiff_const.sub (contDiff_const.mul (Real.contDiff_exp.comp
    ((contDiff_const.mul (hg.sub contDiff_const)).neg)))

theorem hasDerivAt_expProfileF (t : ℝ) :
    HasDerivAt (expProfileF σ lam A) (A * lam * Real.exp (-(lam * (t - σ ^ 2)))) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lam * (t - σ ^ 2))) (-lam) t := by
    simpa using (((hasDerivAt_id t).sub_const (σ ^ 2)).const_mul lam).neg
  have h2 := (h1.exp.const_mul A).const_sub A
  convert h2 using 1
  ring

theorem deriv_expProfileF :
    deriv (expProfileF σ lam A) = fun t ↦ A * lam * Real.exp (-(lam * (t - σ ^ 2))) :=
  funext fun t ↦ (hasDerivAt_expProfileF t).deriv

theorem deriv_deriv_expProfileF (t : ℝ) :
    deriv (deriv (expProfileF σ lam A)) t = -(A * lam ^ 2 * Real.exp (-(lam * (t - σ ^ 2)))) := by
  rw [deriv_expProfileF]
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lam * (t - σ ^ 2))) (-lam) t := by
    simpa using (((hasDerivAt_id t).sub_const (σ ^ 2)).const_mul lam).neg
  rw [(h1.exp.const_mul (A * lam)).deriv]
  ring

theorem norm_gradient_expProfile (y : E d) :
    ‖∇ (expProfile p σ lam A) y‖ =
      |A * lam * Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2)))| * (2 * ‖y - p‖) := by
  have hcomp : HasFDerivAt (fun y ↦ expProfileF σ lam A (‖y - p‖ ^ 2))
      ((A * lam * Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2)))) • ((2 : ℝ) • innerSL ℝ (y - p))) y :=
    (hasDerivAt_expProfileF (σ := σ) (lam := lam) (A := A) (‖y - p‖ ^ 2)).comp_hasFDerivAt
      (f := fun y : E d ↦ ‖y - p‖ ^ 2) y (hasFDerivAt_normSq_sub_const p y)
  have hS : expProfile p σ lam A = fun y ↦ expProfileF σ lam A (‖y - p‖ ^ 2) := rfl
  rw [hS, norm_gradient_eq_norm_fderiv, hcomp.fderiv, norm_smul, norm_smul, innerSL_apply_norm,
    Real.norm_eq_abs]
  norm_num

/-- `ΔH = A λ E (2d - 4 λ |y - p|²)`, `E = exp(-λ(|y - p|² - σ²))`. -/
theorem laplacian_expProfile (y : E d) :
    Δ (expProfile p σ lam A) y = A * lam * Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2))) *
      (2 * d - 4 * lam * ‖y - p‖ ^ 2) := by
  have hcomp := laplacian_comp (f := expProfileF σ lam A) (g := fun y : E d ↦ ‖y - p‖ ^ 2)
    (x := y) (by unfold expProfileF; fun_prop) (contDiff_normSq_sub_const p).contDiffAt
  have hS : expProfile p σ lam A = fun y ↦ expProfileF σ lam A (‖y - p‖ ^ 2) := rfl
  rw [hS, hcomp, deriv_deriv_expProfileF, deriv_expProfileF, norm_gradient_normSq_sub,
    laplacian_normSq_sub_const, finrank_euclideanSpace_fin]
  simp only
  ring

theorem expProfile_eq_zero {y : E d} (hy : ‖y - p‖ = σ) : expProfile p σ lam A y = 0 := by
  unfold expProfile
  rw [hy]; simp

theorem expProfile_neg (hA : 0 < A) (hlam : 0 < lam) {y : E d}
    (hy : ‖y - p‖ < σ) : expProfile p σ lam A y < 0 := by
  unfold expProfile
  have ht : ‖y - p‖ ^ 2 < σ ^ 2 := pow_lt_pow_left₀ hy (norm_nonneg _) two_ne_zero
  have : 1 < Real.exp (-(lam * (‖y - p‖ ^ 2 - σ ^ 2))) :=
    Real.one_lt_exp_iff.2 (by nlinarith)
  nlinarith

end Exp

end EllipticBernoulli
