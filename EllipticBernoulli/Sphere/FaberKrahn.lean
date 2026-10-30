/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.PolyaSzego
import EllipticBernoulli.Sphere.CapRearrangement
import EllipticBernoulli.Sobolev.Lipschitz

/-!
# The Faber–Krahn inequality on the sphere

Let `d ≥ 2`, `|N| = 1`, let `Γ ⊆ 𝕊` be open and nonempty, and let `θ` satisfy
`σ(C(θ)) = σ(Γ)`. Then `λ₁(Γ) ≥ Λ_d(θ)` (`capEigenvalue_le_sphEigenvalue`).

This is the reduction of Salato (arXiv:2506.13473), Proposition 3.3, to the Pólya–Szegő
inequality. Proof: for an admissible `f`, replace `f` by `|f|` (same Rayleigh quotient,
`sphDirichlet_abs`), apply Pólya–Szegő (`polya_szego`) to get `f* = F ∘ φ` with
`R(f*) ≤ R(f)` and `F = 0` on `[θ_f, π] ⊇ [θ, π]`, and compute `R(F ∘ φ)` by the colatitude
formula (`sphL2Sq_comp_colatitude`, `sphDirichlet_comp_colatitude`): it is the one-dimensional
quotient `capRayleigh d θ F ≥ Λ_d(θ)`.

The Lean statement assumes `θ < π`, i.e. `σ(Γ) < σ(𝕊)`. In the Friedland–Hayman application the
two sets are disjoint and nonempty, so both have measure `< σ(𝕊)`.

## References

* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473 (v2).
-/

open MeasureTheory Metric Set Filter Topology
open scoped Gradient NNReal Real ENNReal

namespace EllipticBernoulli

variable {d : ℕ}

public section

/-! ### The absolute value -/

private theorem homogExt0_abs (f : sphere (0 : E d) 1 → ℝ) :
    homogExt0 (fun ω ↦ |f ω|) = fun x ↦ |homogExt0 f x| := by
  funext x
  by_cases hx : x = 0
  · simp [homogExt0, hx]
  · rw [homogExt0_of_ne_zero _ hx, homogExt0_of_ne_zero _ hx]

/-- `|∇|u|| = |∇u|` at points where `u` and `|u|` are differentiable. -/
private theorem norm_fderiv_abs {u : E d → ℝ} {x : E d} (hu : DifferentiableAt ℝ u x)
    (ha : DifferentiableAt ℝ (fun y ↦ |u y|) x) :
    ‖fderiv ℝ (fun y ↦ |u y|) x‖ = ‖fderiv ℝ u x‖ := by
  have hmax : (fun y ↦ max (u y) (-u y)) = fun y ↦ |u y| := funext fun y ↦ (abs_eq_max_neg).symm
  have hmin : (fun y ↦ min (u y) (-u y)) = fun y ↦ -|u y| := by
    funext y
    rcases le_total 0 (u y) with h | h
    · rw [abs_of_nonneg h, min_eq_right (by linarith)]
    · rw [abs_of_nonpos h, neg_neg, min_eq_left (by linarith)]
  have key := norm_sq_fderiv_max_add_min (v := fun y ↦ -u y) hu
    (hu.neg : DifferentiableAt ℝ (fun y ↦ -u y) x) (by rw [hmax]; exact ha)
    (by rw [hmin]; exact (ha.neg : DifferentiableAt ℝ (fun y ↦ -|u y|) x))
  have hn : ∀ v : E d → ℝ, ‖fderiv ℝ (fun y ↦ -v y) x‖ = ‖fderiv ℝ v x‖ := fun v ↦ by
    rw [show (fun y ↦ -v y) = -v from rfl, fderiv_neg, norm_neg]
  rw [hmax, hmin, hn, hn] at key
  have : ‖fderiv ℝ (fun y ↦ |u y|) x‖ ^ 2 = ‖fderiv ℝ u x‖ ^ 2 := by linarith
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

private theorem lipschitzWith_abs_comp {f : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K fun ω ↦ |f ω| :=
  LipschitzWith.of_dist_le_mul fun a b ↦ by
    rw [Real.dist_eq]
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by rw [← Real.dist_eq]; exact hf.dist_le_mul a b)

/-- `∫_𝕊 |∇|f|^|² = ∫_𝕊 |∇f̂|²` for Lipschitz `f`. -/
theorem sphDirichlet_abs (hd : 1 ≤ d) {f : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : sphDirichlet (fun ω ↦ |f ω|) = sphDirichlet f := by
  have hfa : LipschitzWith K fun ω ↦ |f ω| := lipschitzWith_abs_comp hf
  unfold sphDirichlet
  refine integral_congr_ae ?_
  filter_upwards [ae_differentiableAt_homogExt0 hd hf, ae_differentiableAt_homogExt0 hd hfa]
    with ω hu ha
  rw [homogExt0_abs] at ha ⊢
  simp only [norm_gradient_eq_norm_fderiv]
  rw [norm_fderiv_abs hu ha]

/-! ### Rayleigh quotients of colatitude functions -/

private theorem integral_Ioo_pi_eq' {G : ℝ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ π)
    (hG : ∀ φ, θ < φ → φ < π → G φ = 0) : ∫ φ in Ioo 0 π, G φ = ∫ φ in 0..θ, G φ := by
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
    (Ioo_subset_Ioo_right hθπ), intervalIntegral.integral_of_le hθ, integral_Ioc_eq_integral_Ioo]
  filter_upwards [volume.ae_ne θ] with φ hφ hmem
  exact hG φ (lt_of_le_of_ne (not_lt.1 fun h ↦ hmem.2 ⟨hmem.1.1, h⟩) (Ne.symm hφ)) hmem.1.2

/-- `∫_𝕊 F(φ)² dσ = c_d ∫_0^θ F² sin^{d-2}` when `F = 0` on `[θ, π]`. -/
theorem sphL2Sq_comp_colatitude (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {F : ℝ → ℝ}
    (hF : Continuous F) {θ : ℝ} (hθ : θ ∈ Icc 0 π) (hF0 : ∀ φ ∈ Icc θ π, F φ = 0) :
    sphL2Sq (fun ω ↦ F (colatitude N ω)) =
      ((volume : Measure (E (d - 1))).toSphere univ).toReal *
        ∫ φ in 0..θ, F φ ^ 2 * Real.sin φ ^ (d - 2) := by
  rw [sphL2Sq, integral_toSphere_colatitude hd hN (g := fun φ ↦ F φ ^ 2)
    (hF.measurable.pow_const 2) (fun _ ↦ sq_nonneg _),
    integral_Ioo_pi_eq' hθ.1 hθ.2 fun φ h₁ h₂ ↦ by simp [hF0 φ ⟨h₁.le, h₂.le⟩]]
  congr 1
  exact intervalIntegral.integral_congr fun φ _ ↦ by ring

/-- `∫_𝕊 |∇(F ∘ φ)^|² dσ = c_d ∫_0^θ F'² sin^{d-2}` for Lipschitz `F` with `F = 0` on
`[θ, π]`. -/
theorem sphDirichlet_comp_colatitude (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {F : ℝ → ℝ}
    {K : ℝ≥0} (hF : LipschitzWith K F) {θ : ℝ} (hθ : θ ∈ Icc 0 π)
    (hF0 : ∀ φ ∈ Icc θ π, F φ = 0) :
    sphDirichlet (fun ω ↦ F (colatitude N ω)) =
      ((volume : Measure (E (d - 1))).toSphere univ).toReal *
        ∫ φ in 0..θ, deriv F φ ^ 2 * Real.sin φ ^ (d - 2) := by
  have hZ : volume ({0, π} ∪ {φ | ¬DifferentiableAt ℝ F φ}) = 0 :=
    measure_union_null ((Set.toFinite _).measure_zero _) (ae_iff.1 hF.ae_differentiableAt)
  have hpt : ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
      ‖∇ (homogExt0 fun ω ↦ F (colatitude N ω)) (ω : E d)‖ ^ 2 =
        deriv F (colatitude N ω) ^ 2 := by
    filter_upwards [ae_colatitude_notMem hd hN hZ] with ω hω
    simp only [mem_union, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq, not_or,
      not_not] at hω
    exact norm_sq_gradient_homogExt0_comp_colatitude hN ω
      (lt_of_le_of_ne (colatitude_nonneg N ω) (Ne.symm hω.1.1))
      (lt_of_le_of_ne (colatitude_le_pi N ω) hω.1.2) hω.2
  have hderiv : ∀ φ, θ < φ → φ < π → deriv F φ = 0 := fun φ h₁ h₂ ↦ by
    rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)), deriv_const]
    filter_upwards [Ioo_mem_nhds h₁ h₂] with x hx
    exact hF0 x ⟨hx.1.le, hx.2.le⟩
  rw [sphDirichlet, integral_congr_ae hpt,
    integral_toSphere_colatitude hd hN (g := fun φ ↦ deriv F φ ^ 2)
      ((measurable_deriv F).pow_const 2) (fun _ ↦ sq_nonneg _),
    integral_Ioo_pi_eq' hθ.1 hθ.2 fun φ h₁ h₂ ↦ by simp [hderiv φ h₁ h₂]]
  congr 1
  exact intervalIntegral.integral_congr fun φ _ ↦ by ring

/-! ### Faber–Krahn -/

/-- A nonempty open subset of the sphere carries an admissible function (a Lipschitz bump). -/
private theorem exists_isSphAdmissible {Γ : Set (sphere (0 : E d) 1)} (hΓ : IsOpen Γ)
    (hne : Γ.Nonempty) : ∃ f, IsSphAdmissible Γ f := by
  obtain ⟨ω₀, hω₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hΓ ω₀ hω₀
  set f : sphere (0 : E d) 1 → ℝ := fun ω ↦ max 0 (r - dist ω ω₀)
  have hfL : LipschitzWith 1 f := LipschitzWith.of_dist_le_mul fun ω ω' ↦ by
    rw [Real.dist_eq, NNReal.coe_one, one_mul]
    calc |max 0 (r - dist ω ω₀) - max 0 (r - dist ω' ω₀)|
        ≤ |(r - dist ω ω₀) - (r - dist ω' ω₀)| := by
          rw [max_comm 0 (r - dist ω ω₀), max_comm 0 (r - dist ω' ω₀)]
          exact abs_max_sub_max_le_abs _ _ _
      _ = |dist ω' ω₀ - dist ω ω₀| := by congr 1; ring
      _ ≤ dist ω' ω := abs_dist_sub_le ω' ω ω₀
      _ = dist ω ω' := dist_comm _ _
  refine ⟨f, ⟨1, hfL⟩, fun ω hω ↦ ?_, ?_⟩
  · have : r ≤ dist ω ω₀ := not_lt.1 fun h ↦ hω (hball (mem_ball.2 h))
    exact max_eq_left (by linarith)
  · have hcont : Continuous fun ω ↦ f ω ^ 2 := hfL.continuous.pow 2
    have hint : Integrable (fun ω ↦ f ω ^ 2) (volume : Measure (E d)).toSphere :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [sphL2Sq, integral_pos_iff_support_of_nonneg (fun _ ↦ sq_nonneg _) hint]
    refine lt_of_lt_of_le (toSphere_pos_of_isOpen isOpen_ball ⟨ω₀, mem_ball_self hr⟩)
      (measure_mono fun ω hω ↦ ?_)
    have : 0 < r - dist ω ω₀ := sub_pos.2 (mem_ball.1 hω)
    simp only [Function.mem_support, f]
    exact pow_ne_zero 2 (by rw [max_eq_right this.le]; exact this.ne')

/-- **Faber–Krahn on the sphere.** Let `d ≥ 2`, `|N| = 1`, let `Γ ⊆ 𝕊` be
open and nonempty, and let `θ < π` satisfy `σ(C(θ)) = σ(Γ)`. Then `Λ_d(θ) ≤ λ₁(Γ)`.

The Lean statement assumes `θ < π` (equivalently `σ(Γ) < σ(𝕊)`). -/
theorem capEigenvalue_le_sphEigenvalue (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1)
    {Γ : Set (sphere (0 : E d) 1)} (hΓ : IsOpen Γ) (hΓne : Γ.Nonempty) {θ : ℝ} (hθπ : θ < π)
    (hθΓ : (volume : Measure (E d)).toSphere (sphCap N θ) =
      (volume : Measure (E d)).toSphere Γ) :
    capEigenvalue d θ ≤ sphEigenvalue Γ := by
  set σ := (volume : Measure (E d)).toSphere
  set c := ((volume : Measure (E (d - 1))).toSphere univ).toReal
  have hc : 0 < c := ENNReal.toReal_pos (colatConst_ne_zero hd) (colatConst_ne_top d)
  -- `θ > 0`
  have hθ0 : 0 < θ := by
    have hpos : 0 < σ (sphCap N θ) := by rw [hθΓ]; exact toSphere_pos_of_isOpen hΓ hΓne
    obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hpos.ne'
    exact lt_of_le_of_lt (colatitude_nonneg N ω) hω
  have hθmem : θ ∈ Icc 0 π := ⟨hθ0.le, hθπ.le⟩
  obtain ⟨f₀, hf₀⟩ := exists_isSphAdmissible hΓ hΓne
  refine le_csInf ⟨_, f₀, hf₀, rfl⟩ ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨K, hK⟩ := hf.lipschitz
  set g : sphere (0 : E d) 1 → ℝ := fun ω ↦ |f ω|
  have hgK : LipschitzWith K g := lipschitzWith_abs_comp hK
  have hgL2 : sphL2Sq g = sphL2Sq f := by simp only [sphL2Sq, g, sq_abs]
  have hgR : sphRayleigh g = sphRayleigh f := by
    rw [sphRayleigh, sphRayleigh, hgL2, sphDirichlet_abs (by omega) hK]
  obtain ⟨F, hFL, hanti, hF0, hlev, hL2, hDir, hsupp⟩ :=
    polya_szego hd hN hgK (fun ω ↦ abs_nonneg (f ω))
  -- the support radius `θ_f ≤ θ`
  obtain ⟨θf, hθf, hθfm⟩ := exists_toSphere_sphCap_eq hd hN (N := N)
    (measure_mono (μ := σ) (subset_univ {ω | 0 < g ω}))
  have hθfθ : θf ≤ θ := by
    by_contra hlt
    push Not at hlt
    have h₁ := (toReal_toSphere_sphCap_lt_iff hd hN hθmem hθf).2 hlt
    have h₂ : σ {ω | 0 < g ω} ≤ σ Γ := measure_mono fun ω hω ↦ by
      by_contra hωΓ
      have : g ω = 0 := by simp [g, hf.eq_zero ω hωΓ]
      exact (lt_irrefl _ (this ▸ hω : (0 : ℝ) < 0))
    rw [hθfm] at h₁
    exact lt_irrefl _ (h₁.trans_le (h₂.trans hθΓ.symm.le))
  have hFθ : ∀ φ ∈ Icc θ π, F φ = 0 := fun φ hφ ↦
    hsupp θf hθf.1 (hθfθ.trans_lt hθπ) hθfm φ ⟨hθfθ.trans hφ.1, hφ.2⟩
  -- the colatitude quotient
  have hL2' := sphL2Sq_comp_colatitude hd hN hFL.continuous hθmem hFθ
  have hDir' := sphDirichlet_comp_colatitude hd hN hFL hθmem hFθ
  have hpos : 0 < sphL2Sq (fun ω ↦ F (colatitude N ω)) := by
    rw [hL2, hgL2]; exact hf.sphL2Sq_pos
  have hadm : IsCapAdmissible θ F := by
    refine ⟨⟨K, hFL.lipschitzOnWith⟩, hFθ θ ⟨le_rfl, hθπ.le⟩, ?_⟩
    by_contra hall
    push Not at hall
    have hzero : (fun ω ↦ F (colatitude N ω)) = fun _ ↦ 0 := funext fun ω ↦ by
      rcases le_total (colatitude N ω) θ with h | h
      · exact hall _ ⟨colatitude_nonneg N ω, h⟩
      · exact hFθ _ ⟨h, colatitude_le_pi N ω⟩
    rw [hzero] at hpos
    simp [sphL2Sq] at hpos
  have hbdd : BddBelow (capRayleigh d θ '' {F | IsCapAdmissible θ F}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨G, -, rfl⟩
    refine div_nonneg (intervalIntegral.integral_nonneg hθ0.le fun φ hφ ↦ ?_)
      (intervalIntegral.integral_nonneg hθ0.le fun φ hφ ↦ ?_) <;>
      exact mul_nonneg (sq_nonneg _)
        (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1 (hφ.2.trans hθπ.le)) _)
  calc capEigenvalue d θ ≤ capRayleigh d θ F := csInf_le hbdd ⟨F, hadm, rfl⟩
    _ = sphRayleigh (fun ω ↦ F (colatitude N ω)) := by
      rw [sphRayleigh, hL2', hDir', mul_div_mul_left _ _ hc.ne', capRayleigh]
    _ ≤ sphRayleigh g := by
      rw [sphRayleigh, sphRayleigh, hL2]
      exact div_le_div_of_nonneg_right hDir (by rw [← hL2]; exact hpos.le)
    _ = sphRayleigh f := hgR

end

end EllipticBernoulli
