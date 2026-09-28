/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Nondegeneracy
import EllipticBernoulli.Nondegeneracy.Barriers
import EllipticBernoulli.Sobolev.Energy
import EllipticBernoulli.Sobolev.IBP
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sobolev.Uniqueness
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Non-degeneracy of downward minimizers and of local energy minimizers

* `isUniformlyNondegenerateNear_of_forall_energyJ_le`: the core statement. Let `u ≥ 0` be locally
  Lipschitz on the open set `U`, with `0 < q ≤ Q ≤ C` and `Q` measurable. Suppose
  `J_Q(u; B_r(z)) ≤ J_Q(v; B_r(z))` for every ball `B̄_r(z) ⊆ U` and every locally Lipschitz
  `v ≤ u` with `v = u` off `B_r(z)` (pointwise gradients). Then `u` is uniformly non-degenerate
  near every point of `U`, with `c = q / (8 d e^{d/2})` and `ρ = R/4` for any `B_R(x₀) ⊆ U`.
* `IsDownwardMinimizer.isUniformlyNondegenerateNear` (`DownwardNondegStatement`; Alt–Caffarelli,
  Lemma 3.4; Velichkov, Lemma 4.4).
* `IsDownwardMinimizer.exists_le_of_closedBall_subset` (`DownwardNondegQuantStatement`): the same
  on every ball `B̄_r(z) ⊆ U` centred in `\overline{{u > 0}}`, with `c = q₀ / (8 d e^{d/2})`.
* `IsLocalEnergyMinimizer.isUniformlyNondegenerateNear`.

## Proof (no trace inequality)

Suppose `z ∈ \overline{{u > 0}}` and `u < κ r` on `B̄_r(z)`, with `κ = q/(8 d e^{d/2})`. Let
`σ = r/2`, `A = 3κr`, `H = nondegProfile z σ A` (smooth; `< 0` in `B_σ`, `> 0` outside
`B̄_σ`, `ΔH ≤ 0` outside `B_σ`), and `w = max(H, 0) = nondegBarrier z σ A`. The competitor is
`v = u − ψ` with `ψ = max(min(u, κr) − w, 0)`. It vanishes off `B̄_{3r/4}(z)`, because
`w ≥ 5A/13 > κ r` there, and `ψ = u` on `B̄_σ`.

Let `g_f = |∇f|² + Q² 1_{f>0}` and `P = B_σ(z) ∩ {u > 0}`. A.e. on `B_r(z)`,
`g_v − g_u ≤ −2 ∇ψ·∇H + 1_P (−|∇u|² − Q² + 2 M₁ |∇u|)`, with `M₁ = A d e^{d/2}/σ ≥ |∇H|` on
`B̄_σ`. The cases are `ψ = 0`, `ψ > 0` with `H > 0`, and `ψ > 0` with `H < 0`; `∂B_σ` is null.
Integrating, and using `∫ ∇ψ·∇H = −∫ ψ ΔH` (integration by parts), minimality gives
`0 ≤ ∫ (2ψΔH + 1_P(…)) ≤ −(q²/16)|P|`. Here we used
`ψ ΔH ≤ 1_P κ r M₂`, with `M₂ = A d² e^{d/2}/σ² ≥ ΔH` on `B̄_σ`, together with
`M₁ = 3q/4` and `κ r M₂ ≤ 3q²/16`. But `|P| > 0` since `z ∈ \overline{{u>0}}` and `u` is
continuous. The trace term of Alt–Caffarelli appears here as the volume integral of `∇H·∇u` over
`B_σ`, where `H` is the smooth interior extension of the barrier.

Alt–Caffarelli use a trace inequality on a sphere; this proof is trace-free and needs one
integration by parts. Harmonicity of `u` in `{u > 0}` is not used. The dimension assumption is
`1 ≤ d`; the headline `DownwardNondegStatement` assumes `2 ≤ d`. The constants depend only on the
data.

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian NNReal RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Helpers -/

private theorem locallyLipschitzOn_max_const {s : Set (E d)} {f : E d → ℝ}
    (hf : LocallyLipschitzOn s f) (a : ℝ) : LocallyLipschitzOn s fun x ↦ max (f x) a :=
  fun _ hx ↦ by
    obtain ⟨K, t, ht, h⟩ := hf hx
    exact ⟨1 * K, t, ht, (LipschitzWith.id.max_const a).comp_lipschitzOnWith h⟩

private theorem locallyLipschitzOn_min_const {s : Set (E d)} {f : E d → ℝ}
    (hf : LocallyLipschitzOn s f) (a : ℝ) : LocallyLipschitzOn s fun x ↦ min (f x) a :=
  fun _ hx ↦ by
    obtain ⟨K, t, ht, h⟩ := hf hx
    exact ⟨1 * K, t, ht, (LipschitzWith.id.min_const a).comp_lipschitzOnWith h⟩

private theorem integrableOn_ball_of_bound {z : E d} {r : ℝ} {f : E d → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (ball z r))) (C : ℝ)
    (hC : ∀ x ∈ ball z r, |f x| ≤ C) : IntegrableOn f (ball z r) :=
  IntegrableOn.of_bound measure_ball_lt_top hf C
    ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ by rw [Real.norm_eq_abs]; exact hC x hx)

private theorem indicator_one_mem_Icc (s : Set (E d)) (x : E d) :
    s.indicator (1 : E d → ℝ) x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : x ∈ s <;> simp [h]

/-- The energy on a ball of a function continuous on the ball, with bounded gradient, as the
`ofReal` of a Bochner integral. -/
private theorem energyJ_ball_eq {z : E d} {r : ℝ} {Q f : E d → ℝ} (hQm : Measurable Q)
    {CQ : ℝ} (hQb : ∀ x ∈ ball z r, Q x ^ 2 ≤ CQ) (hf : ContinuousOn f (ball z r))
    {CG : ℝ} (hG : ∀ x ∈ ball z r, ‖∇ f x‖ ≤ CG) :
    IntegrableOn (fun x ↦ ‖∇ f x‖ ^ 2 + Q x ^ 2 * (posSet f (ball z r)).indicator 1 x)
      (ball z r) ∧
    energyJ (ball z r) Q f (∇ f) = ENNReal.ofReal (∫ x in ball z r,
      (‖∇ f x‖ ^ 2 + Q x ^ 2 * (posSet f (ball z r)).indicator 1 x)) := by
  have hopen : IsOpen (posSet f (ball z r)) := hf.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hint : IntegrableOn
      (fun x ↦ ‖∇ f x‖ ^ 2 + Q x ^ 2 * (posSet f (ball z r)).indicator 1 x) (ball z r) := by
    refine integrableOn_ball_of_bound ?_ (CG ^ 2 + CQ) fun x hx ↦ ?_
    · exact (((measurable_gradient f).norm.pow_const 2).add
        ((hQm.pow_const 2).mul (measurable_one.indicator hopen.measurableSet))).aestronglyMeasurable
    · have h1 : 0 ≤ ‖∇ f x‖ := norm_nonneg _
      have h2 := hG x hx
      have h3 := hQb x hx
      have hi := indicator_one_mem_Icc (posSet f (ball z r)) x
      have hq0 : 0 ≤ Q x ^ 2 := sq_nonneg _
      rw [abs_of_nonneg (by nlinarith [hi.1])]
      nlinarith [hi.1, hi.2]
  refine ⟨hint, ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦ ?_)]
  · rfl
  · have hi := (indicator_one_mem_Icc (posSet f (ball z r)) x).1
    have : 0 ≤ Q x ^ 2 * (posSet f (ball z r)).indicator 1 x := mul_nonneg (sq_nonneg _) hi
    change 0 ≤ ‖∇ f x‖ ^ 2 + Q x ^ 2 * (posSet f (ball z r)).indicator 1 x
    positivity

/-! ### Bounds for the barrier inside its zero set -/

private theorem exp_le_of_norm_le {z y : E d} {σ : ℝ} (hσ : 0 < σ) :
    Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) ≤ Real.exp ((d : ℝ) / 2) := by
  apply Real.exp_le_exp.2
  have hlm : 0 ≤ (d : ℝ) / (2 * σ ^ 2) := by positivity
  have h : (d : ℝ) / (2 * σ ^ 2) * σ ^ 2 = d / 2 := by field_simp
  linarith [mul_nonneg hlm (sq_nonneg ‖y - z‖)]

/-- `|∇H| ≤ A d e^{d/2} / σ` on `B̄_σ(z)`. -/
private theorem norm_gradient_nondegProfile_le {z : E d} {σ A : ℝ} (hA : 0 ≤ A) (hσ : 0 < σ)
    {y : E d} (hy : ‖y - z‖ ≤ σ) :
    ‖∇ (nondegProfile z σ A) y‖ ≤ A * d * Real.exp ((d : ℝ) / 2) / σ := by
  rw [norm_gradient_nondegProfile]
  have hE := exp_le_of_norm_le (d := d) (z := z) (y := y) hσ
  rw [abs_of_nonneg (by positivity)]
  calc A * ((d : ℝ) / (2 * σ ^ 2)) *
        Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) * (2 * ‖y - z‖)
      ≤ A * ((d : ℝ) / (2 * σ ^ 2)) * Real.exp ((d : ℝ) / 2) * (2 * σ) := by gcongr
    _ = A * d * Real.exp ((d : ℝ) / 2) / σ := by field_simp

/-- The Laplacian of the profile, in closed form. -/
private theorem laplacian_nondegProfile_eq (z : E d) (σ A : ℝ) :
    Δ (nondegProfile z σ A) = fun y ↦ A * ((d : ℝ) / (2 * σ ^ 2)) *
      Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) *
      (2 * d - 4 * ((d : ℝ) / (2 * σ ^ 2)) * ‖y - z‖ ^ 2) :=
  funext fun y ↦ laplacian_expProfile (p := z) (σ := σ) (lam := (d : ℝ) / (2 * σ ^ 2)) (A := A) y

/-- `ΔH ≤ A d² e^{d/2} / σ²` on `B̄_σ(z)`. -/
private theorem laplacian_nondegProfile_le {z : E d} {σ A : ℝ} (hA : 0 ≤ A) (hσ : 0 < σ)
    (y : E d) : Δ (nondegProfile z σ A) y ≤ A * d ^ 2 * Real.exp ((d : ℝ) / 2) / σ ^ 2 := by
  rw [laplacian_nondegProfile_eq]
  have hE := exp_le_of_norm_le (d := d) (z := z) (y := y) hσ
  have hlm : 0 ≤ (d : ℝ) / (2 * σ ^ 2) := by positivity
  have h2 : 2 * (d : ℝ) - 4 * ((d : ℝ) / (2 * σ ^ 2)) * ‖y - z‖ ^ 2 ≤ 2 * d := by
    linarith [mul_nonneg hlm (sq_nonneg ‖y - z‖)]
  calc A * ((d : ℝ) / (2 * σ ^ 2)) *
        Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) *
        (2 * d - 4 * ((d : ℝ) / (2 * σ ^ 2)) * ‖y - z‖ ^ 2)
      ≤ A * ((d : ℝ) / (2 * σ ^ 2)) *
        Real.exp (-((d : ℝ) / (2 * σ ^ 2) * (‖y - z‖ ^ 2 - σ ^ 2))) * (2 * d) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ A * ((d : ℝ) / (2 * σ ^ 2)) * Real.exp ((d : ℝ) / 2) * (2 * d) := by gcongr
    _ = A * d ^ 2 * Real.exp ((d : ℝ) / 2) / σ ^ 2 := by field_simp

/-! ### The contradiction argument on one ball -/

private theorem false_of_small {d : ℕ} (hd : 1 ≤ d) {U : Set (E d)} (hU : IsOpen U)
    {Q u : E d → ℝ} (hu : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y) {q C : ℝ}
    (hq : 0 < q) (hQ : ∀ y ∈ U, q ≤ Q y) (hQC : ∀ y ∈ U, Q y ≤ C) (hQm : Measurable Q)
    {z : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall z r ⊆ U)
    (hmin : ∀ v : E d → ℝ, LocallyLipschitzOn U v → (∀ y ∈ U, v y ≤ u y) →
      (∀ y ∈ U \ ball z r, v y = u y) →
      energyJ (ball z r) Q u (∇ u) ≤ energyJ (ball z r) Q v (∇ v))
    (hz : z ∈ closure (posSet u U))
    (hsmall : ∀ y ∈ closedBall z r, u y < q / (8 * d * Real.exp ((d : ℝ) / 2)) * r) :
    False := by
  classical
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  haveI : Nontrivial (E d) :=
    Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)
  set eD := Real.exp ((d : ℝ) / 2) with heD
  have heD1 : 1 ≤ eD := Real.one_le_exp (by positivity)
  set κ := q / (8 * d * eD) with hκ
  have hκ0 : 0 < κ := by positivity
  set σ := r / 2 with hσ_def
  have hσ : 0 < σ := by positivity
  set A := 3 * κ * r with hA_def
  have hA : 0 < A := by positivity
  set H := nondegProfile z σ A with hH_def
  have hHs : ContDiff ℝ ∞ H := contDiff_nondegProfile z σ A
  set w := nondegBarrier z σ A with hw_def
  set B := ball z r with hB_def
  have hBU : B ⊆ U := ball_subset_closedBall.trans hB
  set ψ : E d → ℝ := fun y ↦ max (min (u y) (κ * r) - w y) 0 with hψ_def
  set v : E d → ℝ := fun y ↦ u y - ψ y with hv_def
  -- Lipschitz regularity
  have hHLip : LocallyLipschitzOn U H :=
    ((contDiff_nondegProfile z σ A (n := 1)).locallyLipschitz).locallyLipschitzOn
  have hwLip : LocallyLipschitzOn U w := locallyLipschitzOn_max_const hHLip 0
  have hψLip : LocallyLipschitzOn U ψ :=
    locallyLipschitzOn_max_const ((locallyLipschitzOn_min_const hu (κ * r)).sub hwLip) 0
  have hvLip : LocallyLipschitzOn U v := hu.sub hψLip
  -- pointwise facts
  have hw0 : ∀ y, 0 ≤ w y := fun y ↦ le_max_right _ _
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y ↦ le_max_right _ _
  have hψle : ∀ y ∈ U, ψ y ≤ u y := fun y hy ↦
    max_le (by linarith [min_le_left (u y) (κ * r), hw0 y]) (hu0 y hy)
  have hψκ : ∀ y, ψ y ≤ κ * r := fun y ↦
    max_le (by linarith [min_le_right (u y) (κ * r), hw0 y]) (by positivity)
  have hψout : ∀ y, 3 * r / 4 ≤ ‖y - z‖ → ψ y = 0 := by
    intro y hy
    have h1 := le_nondegProfile (z := z) hA.le hσ hd (y := y) (by rw [hσ_def]; linarith)
    have h2 : H y ≤ w y := le_max_left _ _
    have h3 : κ * r < 5 * A / 13 := by rw [hA_def]; linarith [mul_pos hκ0 hr]
    exact max_eq_right (by linarith [min_le_right (u y) (κ * r)])
  have hψin : ∀ y ∈ closedBall z r, ψ y = max (u y - w y) 0 := fun y hy ↦ by
    simp only [hψ_def, min_eq_left (hsmall y hy).le]
  have hwσ : ∀ y, ‖y - z‖ ≤ σ → w y = 0 := fun y hy ↦ nondegBarrier_eq_zero hA hσ hd hy
  have hψσ : ∀ y ∈ closedBall z r, ‖y - z‖ ≤ σ → ψ y = u y := fun y hy hyσ ↦ by
    rw [hψin y hy, hwσ y hyσ, sub_zero, max_eq_left (hu0 y (hB hy))]
  -- the competitor
  have hJ := hmin v hvLip (fun y _ ↦ by simp only [hv_def]; linarith [hψ0 y]) (fun y hy ↦ by
    have : r ≤ ‖y - z‖ := by rw [← dist_eq_norm]; exact not_lt.1 (mt mem_ball.2 hy.2)
    simp only [hv_def, hψout y (by linarith), sub_zero])
  -- bounds on `B̄_r(z)`
  have hBc : IsCompact (closedBall z r) := isCompact_closedBall z r
  obtain ⟨Cu, hCu⟩ := exists_bound_fderiv_of_locallyLipschitzOn hU hu hBc hB
  obtain ⟨Cv, hCv⟩ := exists_bound_fderiv_of_locallyLipschitzOn hU hvLip hBc hB
  obtain ⟨Cψ, hCψ⟩ := exists_bound_fderiv_of_locallyLipschitzOn hU hψLip hBc hB
  have hgu : ∀ x ∈ B, ‖∇ u x‖ ≤ Cu := fun x hx ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact hCu x (ball_subset_closedBall hx)
  have hgv : ∀ x ∈ B, ‖∇ v x‖ ≤ Cv := fun x hx ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact hCv x (ball_subset_closedBall hx)
  have hgψ : ∀ x ∈ B, ‖∇ ψ x‖ ≤ Cψ := fun x hx ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact hCψ x (ball_subset_closedBall hx)
  obtain ⟨CH, hCH⟩ := hBc.exists_bound_of_continuousOn
    (continuous_gradient (contDiff_nondegProfile z σ A (n := 1))).continuousOn
  have hΔc : Continuous (Δ H) := by rw [hH_def, laplacian_nondegProfile_eq]; fun_prop
  obtain ⟨CΔ, hCΔ⟩ := hBc.exists_bound_of_continuousOn hΔc.continuousOn
  have hQ2 : ∀ x ∈ B, Q x ^ 2 ≤ C ^ 2 := fun x hx ↦ by
    have h1 := hQ x (hBU hx); exact pow_le_pow_left₀ (by linarith) (hQC x (hBU hx)) 2
  -- energies as real integrals
  have huc : ContinuousOn u B := hu.continuousOn.mono hBU
  obtain ⟨hIu, hJu⟩ := energyJ_ball_eq (z := z) (r := r) hQm hQ2 huc hgu
  obtain ⟨hIv, hJv⟩ := energyJ_ball_eq (z := z) (r := r) hQm hQ2
    (hvLip.continuousOn.mono hBU) hgv
  rw [hJu, hJv, ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x ↦ by
    have := (indicator_one_mem_Icc (posSet v B) x).1
    have := mul_nonneg (sq_nonneg (Q x)) this
    positivity)] at hJ
  -- weak gradients on `B`
  have hWu := (memH1Loc_gradient_of_locallyLipschitzOn isOpen_ball (hu.mono hBU)).1
  have hWv := (memH1Loc_gradient_of_locallyLipschitzOn isOpen_ball (hvLip.mono hBU)).1
  have hWψ := (memH1Loc_gradient_of_locallyLipschitzOn isOpen_ball (hψLip.mono hBU)).1
  have hae1 : ∀ᵐ x ∂(volume.restrict B), ∇ ψ x = ∇ u x - ∇ v x :=
    HasWeakGradient.ae_eq_of_eqOn isOpen_ball isOpen_ball subset_rfl hWψ (hWu.sub hWv)
      (fun x _ ↦ by simp only [hv_def]; ring)
  have hae2 : ∀ᵐ x ∂(volume.restrict B), ψ x = 0 → ∇ ψ x = 0 :=
    HasWeakGradient.ae_eq_zero_of_eq_zero isOpen_ball hWψ
  have hae3 : ∀ᵐ x ∂(volume.restrict B), x ∉ sphere z σ :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume z σ))
  -- the set `P = B_σ ∩ {u > 0}` and the constants
  have hposU : IsOpen (posSet u B) := huc.isOpen_inter_preimage isOpen_ball isOpen_Ioi
  set P := ball z σ ∩ posSet u B with hP_def
  have hPo : IsOpen P := isOpen_ball.inter hposU
  have hPB : P ⊆ B := fun x hx ↦ hx.2.1
  set M₁ := A * d * eD / σ with hM₁_def
  set M₂ := A * d ^ 2 * eD / σ ^ 2 with hM₂_def
  have hM₁ : M₁ = 3 * q / 4 := by
    rw [hM₁_def, hA_def, hκ, hσ_def]; field_simp; ring
  have hM₂ : κ * r * M₂ ≤ 3 * q ^ 2 / 16 := by
    have e : κ * r * M₂ = 3 * q ^ 2 / (16 * eD) := by
      rw [hM₂_def, hA_def, hκ, hσ_def]; field_simp; ring
    rw [e]
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have hM₂0 : 0 ≤ M₂ := by positivity
  set T : E d → ℝ := fun x ↦ -‖∇ u x‖ ^ 2 - Q x ^ 2 + 2 * M₁ * ‖∇ u x‖ with hT_def
  -- open set where `ψ > 0`, on which `v = w`
  have hOo : IsOpen (B ∩ ψ ⁻¹' Ioi 0) :=
    (hψLip.continuousOn.mono hBU).isOpen_inter_preimage isOpen_ball isOpen_Ioi
  have hvw : ∀ y ∈ B ∩ ψ ⁻¹' Ioi 0, v y = w y := fun y hy ↦ by
    have e := hψin y (ball_subset_closedBall hy.1)
    have hpos : 0 < ψ y := hy.2
    have hm : 0 < u y - w y := by
      by_contra hc
      push Not at hc
      rw [e, max_eq_right hc] at hpos
      exact lt_irrefl _ hpos
    change u y - ψ y = w y
    rw [e, max_eq_left hm.le]; ring
  -- the pointwise inequality
  have hptw : ∀ᵐ x ∂(volume.restrict B),
      (‖∇ v x‖ ^ 2 + Q x ^ 2 * (posSet v B).indicator 1 x) -
        (‖∇ u x‖ ^ 2 + Q x ^ 2 * (posSet u B).indicator 1 x) ≤
      -2 * ⟪∇ ψ x, ∇ H x⟫_ℝ + P.indicator T x := by
    filter_upwards [hae1, hae2, hae3, ae_restrict_mem measurableSet_ball] with x h1 h2 h3 hxB
    have hxcB : x ∈ closedBall z r := ball_subset_closedBall hxB
    by_cases hψx : ψ x = 0
    · have hg : ∇ ψ x = 0 := h2 hψx
      have hvx : v x = u x := by simp only [hv_def, hψx, sub_zero]
      have hgv : ∇ v x = ∇ u x := by
        rw [hg] at h1; exact (sub_eq_zero.1 h1.symm).symm
      have hxP : x ∉ P := by
        rintro ⟨hxσ, -, hxpos⟩
        have := hψσ x hxcB (by rw [← dist_eq_norm]; exact (mem_ball.1 hxσ).le)
        linarith
      have hposeq : (posSet v B).indicator (1 : E d → ℝ) x =
          (posSet u B).indicator 1 x := by
        have hiff : x ∈ posSet v B ↔ x ∈ posSet u B := by
          change x ∈ B ∧ 0 < v x ↔ x ∈ B ∧ 0 < u x
          rw [hvx]
        by_cases h : x ∈ posSet u B
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hiff.2 h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hiff.1 h)]
      rw [hgv, hposeq, hg, Set.indicator_of_notMem hxP]
      simp
    · have hψpos : 0 < ψ x := lt_of_le_of_ne (hψ0 x) (Ne.symm hψx)
      have hxO : x ∈ B ∩ ψ ⁻¹' Ioi 0 := ⟨hxB, hψpos⟩
      have hvwx := hvw x hxO
      have hux : 0 < u x := by
        have := hψle x (hBU hxB); linarith
      have hupos : (posSet u B).indicator (1 : E d → ℝ) x = 1 := by
        rw [Set.indicator_of_mem (show x ∈ posSet u B from ⟨hxB, hux⟩)]; rfl
      have hcont : Continuous fun y : E d ↦ ‖y - z‖ := continuous_norm.comp (continuous_sub_right z)
      rcases lt_trichotomy ‖x - z‖ σ with hlt | heq | hgt
      · -- inside `B_σ`: `v = 0` near `x`
        have hnb : v =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
          filter_upwards [hOo.mem_nhds hxO, (isOpen_lt hcont continuous_const).mem_nhds hlt]
            with y hy hyσ
          rw [hvw y hy, hwσ y (le_of_lt hyσ)]
        have hgv : ∇ v x = 0 := by rw [hnb.gradient_eq]; simp
        have hvx : v x = 0 := hnb.eq_of_nhds
        have hgψ : ∇ ψ x = ∇ u x := by rw [h1, hgv, sub_zero]
        have hxP : x ∈ P := ⟨by rw [mem_ball, dist_eq_norm]; exact hlt, hxB, hux⟩
        have hvpos : (posSet v B).indicator (1 : E d → ℝ) x = 0 :=
          Set.indicator_of_notMem (fun h ↦ by have := h.2; linarith) _
        rw [hgv, Set.indicator_of_mem hxP, hgψ, hvpos, hupos]
        have hH : ‖∇ H x‖ ≤ M₁ := norm_gradient_nondegProfile_le hA.le hσ hlt.le
        have hin := real_inner_le_norm (∇ u x) (∇ H x)
        have : ‖∇ u x‖ * ‖∇ H x‖ ≤ ‖∇ u x‖ * M₁ := mul_le_mul_of_nonneg_left hH (norm_nonneg _)
        simp only [hT_def, norm_zero]
        linarith
      · exact absurd (by rw [mem_sphere, dist_eq_norm]; exact heq) h3
      · -- outside `B̄_σ`: `v = H` near `x`
        have hnb : v =ᶠ[𝓝 x] H := by
          filter_upwards [hOo.mem_nhds hxO, (isOpen_lt continuous_const hcont).mem_nhds hgt]
            with y hy hyσ
          rw [hvw y hy]; exact max_eq_left (nondegProfile_pos hA hσ hd hyσ).le
        have hgv : ∇ v x = ∇ H x := hnb.gradient_eq
        have hvx : 0 < v x := by rw [hnb.eq_of_nhds]; exact nondegProfile_pos hA hσ hd hgt
        have hxP : x ∉ P := fun h ↦ by
          have := mem_ball.1 h.1; rw [dist_eq_norm] at this; linarith
        have hvpos : (posSet v B).indicator (1 : E d → ℝ) x = 1 := by
          rw [Set.indicator_of_mem (show x ∈ posSet v B from ⟨hxB, hvx⟩)]; rfl
        have hgψ : ∇ ψ x = ∇ u x - ∇ H x := by rw [h1, hgv]
        rw [Set.indicator_of_notMem hxP, hgv, hvpos, hupos, hgψ, inner_sub_left,
          real_inner_self_eq_norm_sq]
        have := norm_sub_sq_real (∇ u x) (∇ H x)
        linarith [sq_nonneg ‖∇ u x - ∇ H x‖]
  -- the pointwise bound after integration by parts
  have hptw2 : ∀ x ∈ B, 2 * (ψ x * Δ H x) + P.indicator T x ≤
      P.indicator (fun _ ↦ -(q ^ 2 / 16)) x := by
    intro x hxB
    by_cases hxP : x ∈ P
    · rw [Set.indicator_of_mem hxP, Set.indicator_of_mem hxP]
      have hlt : ‖x - z‖ < σ := by rw [← dist_eq_norm]; exact mem_ball.1 hxP.1
      have hΔ : Δ H x ≤ M₂ := laplacian_nondegProfile_le hA.le hσ x
      have h1 : ψ x * Δ H x ≤ κ * r * M₂ :=
        calc ψ x * Δ H x ≤ ψ x * M₂ := mul_le_mul_of_nonneg_left hΔ (hψ0 x)
          _ ≤ κ * r * M₂ := mul_le_mul_of_nonneg_right (hψκ x) hM₂0
      have hQx : q ^ 2 ≤ Q x ^ 2 := pow_le_pow_left₀ hq.le (hQ x (hBU hxB)) 2
      have hsq : -‖∇ u x‖ ^ 2 + 2 * M₁ * ‖∇ u x‖ ≤ M₁ ^ 2 := by
        linarith [sq_nonneg (‖∇ u x‖ - M₁)]
      have hM₁sq : M₁ ^ 2 = 9 * q ^ 2 / 16 := by rw [hM₁]; ring
      simp only [hT_def]
      linarith
    · rw [Set.indicator_of_notMem hxP, Set.indicator_of_notMem hxP]
      rcases le_or_gt σ ‖x - z‖ with hge | hlt
      · have := laplacian_nondegProfile_nonpos (z := z) hA.le hσ hge
        linarith [mul_nonpos_of_nonneg_of_nonpos (hψ0 x) this]
      · have hux : u x = 0 := by
          by_contra hne
          exact hxP ⟨by rw [mem_ball, dist_eq_norm]; exact hlt, hxB,
            lt_of_le_of_ne (hu0 x (hBU hxB)) (Ne.symm hne)⟩
        have : ψ x = 0 := le_antisymm (hux ▸ hψle x (hBU hxB)) (hψ0 x)
        rw [this]; simp
  -- integrability
  have hI1 : IntegrableOn (fun x ↦ ⟪∇ ψ x, ∇ H x⟫_ℝ) B := by
    refine integrableOn_ball_of_bound
      ((measurable_gradient ψ).inner (measurable_gradient H)).aestronglyMeasurable
      (Cψ * CH) fun x hx ↦ (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hgψ x hx) (hCH x (ball_subset_closedBall hx)) (norm_nonneg _)
      ((norm_nonneg _).trans (hgψ x hx))
  have hTm : Measurable T := by
    rw [hT_def]
    exact (((measurable_gradient u).norm.pow_const 2).neg.sub (hQm.pow_const 2)).add
      (measurable_const.mul (measurable_gradient u).norm)
  have hI2 : IntegrableOn (fun x ↦ P.indicator T x) B := by
    refine integrableOn_ball_of_bound (hTm.indicator hPo.measurableSet).aestronglyMeasurable
      (Cu ^ 2 + C ^ 2 + 2 * M₁ * Cu) fun x hx ↦ ?_
    have hM₁0 : 0 ≤ M₁ := by rw [hM₁]; positivity
    have h1 := hgu x hx
    have h0 := norm_nonneg (∇ u x)
    have h2 := hQ2 x hx
    have hQ0 : 0 ≤ Q x ^ 2 := sq_nonneg _
    have hCu : 0 ≤ Cu := h0.trans h1
    have hu2 : ‖∇ u x‖ ^ 2 ≤ Cu ^ 2 := pow_le_pow_left₀ h0 h1 2
    have hMu : M₁ * ‖∇ u x‖ ≤ M₁ * Cu := mul_le_mul_of_nonneg_left h1 hM₁0
    have hMu0 : 0 ≤ M₁ * ‖∇ u x‖ := mul_nonneg hM₁0 h0
    have hbd : 0 ≤ Cu ^ 2 + C ^ 2 + 2 * M₁ * Cu := by positivity
    by_cases hxP : x ∈ P
    · rw [Set.indicator_of_mem hxP, abs_le]
      simp only [hT_def]
      constructor <;> linarith [sq_nonneg (‖∇ u x‖)]
    · rw [Set.indicator_of_notMem hxP, abs_zero]
      exact hbd
  have hψc : ContinuousOn ψ B := hψLip.continuousOn.mono hBU
  have hI3 : IntegrableOn (fun x ↦ ψ x * Δ H x) B := by
    refine integrableOn_ball_of_bound
      ((hψc.aestronglyMeasurable measurableSet_ball).mul hΔc.aestronglyMeasurable)
      (κ * r * CΔ) fun x hx ↦ ?_
    rw [abs_mul, abs_of_nonneg (hψ0 x)]
    exact mul_le_mul (hψκ x) (by rw [← Real.norm_eq_abs]; exact hCΔ x (ball_subset_closedBall hx))
      (abs_nonneg _) (by positivity)
  have hI4 : IntegrableOn (fun x ↦ P.indicator (fun _ ↦ -(q ^ 2 / 16)) x) B := by
    refine integrableOn_ball_of_bound
      (measurable_const.indicator hPo.measurableSet).aestronglyMeasurable (q ^ 2 / 16)
      fun x _ ↦ ?_
    by_cases hxP : x ∈ P
    · rw [Set.indicator_of_mem hxP, abs_neg, abs_of_nonneg (by positivity)]
    · rw [Set.indicator_of_notMem hxP, abs_zero]; positivity
  -- integration by parts
  have hIBP : ∫ x in B, ⟪∇ ψ x, ∇ H x⟫_ℝ = -∫ x in B, ψ x * Δ H x :=
    HasWeakGradient.integral_inner_gradient_eq_neg isOpen_ball hWψ
      (isCompact_closedBall z (3 * r / 4)) (closedBall_subset_ball (by linarith))
      (ae_restrict_of_forall_mem (measurableSet_ball.diff measurableSet_closedBall)
        fun y hy ↦ hψout y (by
          have := hy.2; rw [mem_closedBall, not_le, dist_eq_norm] at this; linarith))
      hHs
  -- assembly
  have hL : 0 ≤ ∫ x in B, ((‖∇ v x‖ ^ 2 + Q x ^ 2 * (posSet v B).indicator 1 x) -
      (‖∇ u x‖ ^ 2 + Q x ^ 2 * (posSet u B).indicator 1 x)) := by
    rw [integral_sub hIv hIu]; linarith
  have hmono : ∫ x in B, ((‖∇ v x‖ ^ 2 + Q x ^ 2 * (posSet v B).indicator 1 x) -
      (‖∇ u x‖ ^ 2 + Q x ^ 2 * (posSet u B).indicator 1 x)) ≤
      ∫ x in B, (-2 * ⟪∇ ψ x, ∇ H x⟫_ℝ + P.indicator T x) :=
    integral_mono_ae (hIv.sub hIu) ((hI1.const_mul (-2)).add hI2) hptw
  have hR : ∫ x in B, (-2 * ⟪∇ ψ x, ∇ H x⟫_ℝ + P.indicator T x) =
      ∫ x in B, (2 * (ψ x * Δ H x) + P.indicator T x) := by
    rw [integral_add (hI1.const_mul (-2)) hI2, integral_add (hI3.const_mul 2) hI2,
      integral_const_mul, integral_const_mul, hIBP]
    ring
  have hfin : ∫ x in B, (2 * (ψ x * Δ H x) + P.indicator T x) ≤
      ∫ x in B, P.indicator (fun _ ↦ -(q ^ 2 / 16)) x :=
    setIntegral_mono_on ((hI3.const_mul 2).add hI2) hI4 measurableSet_ball hptw2
  have hval : ∫ x in B, P.indicator (fun _ ↦ -(q ^ 2 / 16)) x =
      volume.real P * -(q ^ 2 / 16) := by
    rw [integral_indicator_const _ hPo.measurableSet, measureReal_restrict_apply hPo.measurableSet,
      inter_eq_left.2 hPB, smul_eq_mul]
  -- `|P| > 0`
  obtain ⟨y, hyσ, hyU, hypos⟩ : ∃ y ∈ ball z σ, y ∈ U ∧ 0 < u y := by
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hz (ball z σ) (ball_mem_nhds z hσ)
    exact ⟨y, hy1, hy2.1, hy2.2⟩
  have hyP : y ∈ P := ⟨hyσ, ball_subset_ball (by linarith) hyσ, hypos⟩
  have hPpos : 0 < volume.real P := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hPo.measure_ne_zero volume ⟨y, hyP⟩)
      ((measure_mono hPB).trans_lt measure_ball_lt_top).ne
  have hq2 : 0 < q ^ 2 := by positivity
  linarith [mul_pos hPpos hq2]

/-! ### Main results -/

/-- **Non-degeneracy from one-sided (downward) energy comparison.** Let `u ≥ 0` be locally
Lipschitz on the open set `U`, `0 < q ≤ Q ≤ C` on `U`, and `Q` measurable. Suppose
`J_Q(u; B) ≤ J_Q(v; B)` on every ball `B = B_r(z)` with `B̄_r(z) ⊆ U`, for every locally
Lipschitz `v ≤ u` on `U` with `v = u` on `U \ B`. Here both energies use pointwise gradients.
Then `u` is uniformly non-degenerate near every `x₀ ∈ U`, with `c = q / (8 d e^{d/2})` and
`ρ = R/4` for any `R > 0` with `B_R(x₀) ⊆ U`. Assumes `1 ≤ d`. -/
theorem isUniformlyNondegenerateNear_of_forall_energyJ_le (hd : 1 ≤ d) {U : Set (E d)}
    (hU : IsOpen U) {Q u : E d → ℝ} (hu : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    {q C : ℝ} (hq : 0 < q) (hQ : ∀ y ∈ U, q ≤ Q y) (hQC : ∀ y ∈ U, Q y ≤ C)
    (hQm : Measurable Q)
    (hmin : ∀ (z : E d) (r : ℝ), 0 < r → closedBall z r ⊆ U → ∀ v : E d → ℝ,
      LocallyLipschitzOn U v → (∀ y ∈ U, v y ≤ u y) → (∀ y ∈ U \ ball z r, v y = u y) →
      energyJ (ball z r) Q u (∇ u) ≤ energyJ (ball z r) Q v (∇ v))
    {x₀ : E d} (hx₀ : x₀ ∈ U) : IsUniformlyNondegenerateNear U u x₀ := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x₀ hx₀
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨q / (8 * d * Real.exp ((d : ℝ) / 2)), by positivity, R / 4, by positivity, ?_⟩
  rintro z ⟨hzcl, hzB⟩ r hr hrρ
  by_contra hcon
  push Not at hcon
  have hball : closedBall z r ⊆ U := fun y hy ↦ hRU (by
    rw [mem_ball]; rw [mem_closedBall] at hy; rw [mem_ball] at hzB
    linarith [dist_triangle y z x₀])
  exact false_of_small hd hU hu hu0 hq hQ hQC hQm hr hball (hmin z r hr hball) hzcl hcon

/-- **Downward minimizers are uniformly non-degenerate** (`DownwardNondegStatement`;
Alt–Caffarelli, Lemma 3.4; Velichkov, Lemma 4.4), with `c = q₀ / (8 d e^{d/2})` and `ρ = R/4`
for any `B_R(x₀) ⊆ U`. The proof uses only the downward energy comparison and the Lipschitz
bound (`isUniformlyNondegenerateNear_of_forall_energyJ_le`): harmonicity in `{u > 0}` and
`2 ≤ d` are not used (`1 ≤ d` suffices). -/
theorem IsDownwardMinimizer.isUniformlyNondegenerateNear : DownwardNondegStatement := by
  intro d U Q u x₀ hd hU hmin hu hu0 hQ hQb hQm hx₀
  obtain ⟨q, hq, hQ⟩ := hQ
  obtain ⟨C, hC⟩ := hQb
  refine isUniformlyNondegenerateNear_of_forall_energyJ_le (by omega) hU hu hu0 hq hQ hC hQm
    ?_ hx₀.2
  intro z r hr hB v hv hvle hveq
  exact hmin.2.2.2.2 z r hr hB (∇ u) v (∇ v) (memH1Loc_gradient_of_locallyLipschitzOn hU hu)
    (memH1Loc_gradient_of_locallyLipschitzOn hU hv)
    (ae_restrict_of_forall_mem hU.measurableSet hvle)
    (ae_restrict_of_forall_mem (hU.measurableSet.diff measurableSet_ball) hveq)

/-- **Downward minimizers are non-degenerate on every ball** (`DownwardNondegQuantStatement`;
Alt–Caffarelli, Lemma 3.4; Velichkov, Lemma 4.4).
For `z ∈ \overline{{u > 0}}` and `B̄_r(z) ⊆ U`,
`sup_{B̄_r(z)} u ≥ q₀ r / (8 d e^{d/2})`. Harmonicity in `{u > 0}` is not used, and `1 ≤ d`
suffices. -/
theorem IsDownwardMinimizer.exists_le_of_closedBall_subset : DownwardNondegQuantStatement := by
  intro d U Q u q₀ hd hU hmin hu hu0 hq₀ hQ hQb hQm z hz r hr hB
  obtain ⟨C, hC⟩ := hQb
  by_contra hcon
  push Not at hcon
  refine false_of_small hd hU hu hu0 hq₀ hQ hC hQm hr hB (fun v hv hvle hveq ↦ ?_) hz hcon
  exact hmin.2.2.2.2 z r hr hB (∇ u) v (∇ v) (memH1Loc_gradient_of_locallyLipschitzOn hU hu)
    (memH1Loc_gradient_of_locallyLipschitzOn hU hv)
    (ae_restrict_of_forall_mem hU.measurableSet hvle)
    (ae_restrict_of_forall_mem (hU.measurableSet.diff measurableSet_ball) hveq)

/-- **Local energy minimizers are uniformly non-degenerate**: a locally Lipschitz,
nonnegative local minimizer of `J_Q` with `0 < q₀ ≤ Q ≤ C` and `Q` measurable is uniformly
non-degenerate near every free boundary point. The constants are `c = q₀ / (8 d e^{d/2})` and
`ρ = R/4` for `B_R(x₀) ⊆ U`. The minimizer's weak gradient agrees a.e. with the pointwise one
(uniqueness of weak gradients), and the unconstrained comparison contains the downward one.
Assumes `1 ≤ d`. -/
theorem IsLocalEnergyMinimizer.isUniformlyNondegenerateNear (hd : 1 ≤ d) {U : Set (E d)}
    (hU : IsOpen U) {Q u : E d → ℝ} (hmin : IsLocalEnergyMinimizer U Q u)
    (hu : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    (hQ : ∃ q₀ > 0, ∀ y ∈ U, q₀ ≤ Q y) (hQb : ∃ C, ∀ y ∈ U, Q y ≤ C) (hQm : Measurable Q)
    {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u U) : IsUniformlyNondegenerateNear U u x₀ := by
  obtain ⟨q, hq, hQ⟩ := hQ
  obtain ⟨C, hC⟩ := hQb
  obtain ⟨Gu, hGu, hmin⟩ := hmin
  have hGae : ∀ᵐ x ∂(volume.restrict U), Gu x = ∇ u x :=
    HasWeakGradient.ae_eq_of_eqOn hU hU subset_rfl hGu.1
      (memH1Loc_gradient_of_locallyLipschitzOn hU hu).1 (fun _ _ ↦ rfl)
  refine isUniformlyNondegenerateNear_of_forall_energyJ_le hd hU hu hu0 hq hQ hC hQm ?_ hx₀.2
  intro z r hr hB v hv _ hveq
  have hBU : ball z r ⊆ U := ball_subset_closedBall.trans hB
  rw [← energyJ_congr_ae (Q := Q) measurableSet_ball (Eventually.of_forall fun _ ↦ rfl)
    (ae_restrict_of_ae_restrict_of_subset hBU hGae)]
  exact (hmin z r hr hB).2.2.2 v (∇ v) (memH1Loc_gradient_of_locallyLipschitzOn hU hv)
    (ae_restrict_of_forall_mem (hU.measurableSet.diff measurableSet_ball) hveq)
    (Eventually.of_forall fun _ ↦ mem_univ _)

end EllipticBernoulli
