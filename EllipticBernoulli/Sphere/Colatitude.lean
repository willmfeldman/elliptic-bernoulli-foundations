/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.Tangential
public import EllipticBernoulli.Sphere.Measure
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Colatitude functions on the sphere

Fix a unit vector `N` (the north pole). The colatitude of `ω ∈ 𝕊` is `φ(ω) = ∠(ω, N)`
(`colatitude N ω`, equal to `arccos ⟨ω, N⟩`), and the open cap of colatitude `θ` is
`sphCap N θ = {ω | φ(ω) < θ}`.

Pointwise facts:

* `angle_le_pi_div_two_mul_norm_sub`: for unit vectors, `∠(x, y) ≤ (π/2) |x - y|`;
* `lipschitzWith_comp_colatitude`: if `F` is `K`-Lipschitz on `[0, π]`, then `F ∘ φ` is
  `(π/2) K`-Lipschitz on the sphere (chordal metric);
* `norm_sq_gradient_homogExt0_comp_colatitude`: `|∇(F ∘ φ)^(ω)|² = F'(φ(ω))²` at every `ω` with
  `0 < φ(ω) < π` where `F` is differentiable at `φ(ω)`;

and the integral parts:

* `lintegral_toSphere_colatitude`, `integral_toSphere_colatitude`: for `d ≥ 2`,
  `∫_𝕊 h(φ(ω)) dσ = c_d ∫_0^π h(φ) sin^{d-2}(φ) dφ` with `c_d = σ_{d-1}(𝕊^{d-2}) ∈ (0, ∞)`;
* `ae_colatitude_notMem`: preimages of Lebesgue-null sets under `φ` are `σ`-null;
* `exists_isSphAdmissible_sphRayleigh_eq`: an admissible `F` for `Λ_d(θ)` gives an admissible
  colatitude function for the cap with the same Rayleigh quotient;
* `sphEigenvalue_sphCap_le_capEigenvalue`: `λ₁(C(θ)) ≤ Λ_d(θ)` for `0 < θ ≤ π`.

For the integration formula, compute `∫_{B_1} h(φ(x/|x|)) dx` once in polar
coordinates on `E d`, and once by splitting `E d = ℝ × E (d - 1)`, using polar coordinates in
`E (d - 1)` and then Mathlib's `polarCoord` in the half plane. A general pole is reduced to
`e₀ = single 0 1` by a reflection.
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace InnerProductGeometry
open scoped Gradient NNReal Real ENNReal

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public noncomputable section

/-- The colatitude `φ(ω) = ∠(ω, N) ∈ [0, π]` of `ω ∈ 𝕊` with respect to the pole `N`. -/
def colatitude (N : E d) (ω : sphere (0 : E d) 1) : ℝ :=
  angle (ω : E d) N

/-- The open cap `{ω ∈ 𝕊 | φ(ω) < θ}` of colatitude `θ` about the pole `N`. -/
def sphCap (N : E d) (θ : ℝ) : Set (sphere (0 : E d) 1) :=
  {ω | colatitude N ω < θ}

end

public section

theorem colatitude_nonneg (N : E d) (ω : sphere (0 : E d) 1) : 0 ≤ colatitude N ω :=
  angle_nonneg _ _

theorem colatitude_le_pi (N : E d) (ω : sphere (0 : E d) 1) : colatitude N ω ≤ π :=
  angle_le_pi _ _

theorem colatitude_eq_arccos {N : E d} (hN : ‖N‖ = 1) (ω : sphere (0 : E d) 1) :
    colatitude N ω = Real.arccos (inner ℝ N (ω : E d)) := by
  rw [colatitude, angle, norm_eq_of_mem_sphere ω, hN, mul_one, div_one, real_inner_comm]

theorem continuous_colatitude {N : E d} (hN : ‖N‖ = 1) : Continuous (colatitude N) := by
  rw [show colatitude N = fun ω : sphere (0 : E d) 1 ↦ Real.arccos (inner ℝ N (ω : E d)) from
    funext (colatitude_eq_arccos hN)]
  fun_prop

/-- For unit vectors, the angle is at most `π/2` times the chordal distance. -/
theorem angle_le_pi_div_two_mul_norm_sub {x y : E d} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    angle x y ≤ π / 2 * ‖x - y‖ := by
  set α := angle x y
  have hα0 : 0 ≤ α := angle_nonneg x y
  have hαπ : α ≤ π := angle_le_pi x y
  have hlaw := norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle x y
  rw [hx, hy] at hlaw
  have hcos : Real.cos α = 1 - 2 * Real.sin (α / 2) ^ 2 := by
    have := Real.cos_sq_add_sin_sq (α / 2)
    have h := Real.cos_two_mul (α / 2)
    rw [show 2 * (α / 2) = α by ring] at h
    linarith
  have hs0 : 0 ≤ Real.sin (α / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hnorm : ‖x - y‖ = 2 * Real.sin (α / 2) := by
    have h2 : ‖x - y‖ ^ 2 = (2 * Real.sin (α / 2)) ^ 2 := by
      rw [sq, hlaw, hcos]; ring
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2
  have hj := Real.mul_le_sin (x := α / 2) (by linarith) (by linarith)
  rw [hnorm]
  have hπ : 0 < π := Real.pi_pos
  have : 2 / π * (α / 2) * π = α := by field_simp
  nlinarith

/-- `|φ(ω) - φ(ω')| ≤ (π/2) |ω - ω'|`. -/
theorem abs_colatitude_sub_le (N : E d) (ω ω' : sphere (0 : E d) 1) :
    |colatitude N ω - colatitude N ω'| ≤ π / 2 * dist ω ω' := by
  have h := angle_le_pi_div_two_mul_norm_sub (norm_eq_of_mem_sphere ω) (norm_eq_of_mem_sphere ω')
  rw [Subtype.dist_eq, dist_eq_norm]
  have h1 := angle_le_angle_add_angle (ω : E d) (ω' : E d) N
  have h2 := angle_le_angle_add_angle (ω' : E d) (ω : E d) N
  rw [angle_comm (ω' : E d) (ω : E d)] at h2
  rw [abs_le]
  constructor <;> simp only [colatitude] <;> linarith

/-- If `F` is `K`-Lipschitz on `[0, π]`, then `F ∘ φ` is `(π/2) K`-Lipschitz on the sphere. -/
theorem lipschitzWith_comp_colatitude {F : ℝ → ℝ} {K : ℝ≥0} (hF : LipschitzOnWith K F (Icc 0 π))
    (N : E d) :
    LipschitzWith (K * Real.toNNReal (π / 2)) fun ω ↦ F (colatitude N ω) := by
  refine LipschitzWith.of_dist_le_mul fun ω ω' ↦ ?_
  have hmem : ∀ ω, colatitude N ω ∈ Icc 0 π := fun ω ↦
    ⟨colatitude_nonneg N ω, colatitude_le_pi N ω⟩
  refine (hF.dist_le_mul _ (hmem ω) _ (hmem ω')).trans ?_
  rw [Real.dist_eq, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity), mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_colatitude_sub_le N ω ω') K.2

/-- **The gradient of a colatitude function.** If `0 < φ(ω) < π` and `F`
is differentiable at `φ(ω)`, then `|∇(F ∘ φ)^(ω)|² = F'(φ(ω))²`. -/
theorem norm_sq_gradient_homogExt0_comp_colatitude {N : E d} (hN : ‖N‖ = 1) {F : ℝ → ℝ}
    (ω : sphere (0 : E d) 1) (hφ0 : 0 < colatitude N ω) (hφπ : colatitude N ω < π)
    (hF : DifferentiableAt ℝ F (colatitude N ω)) :
    ‖∇ (homogExt0 fun ω ↦ F (colatitude N ω)) (ω : E d)‖ ^ 2 =
      deriv F (colatitude N ω) ^ 2 := by
  set c := inner ℝ N (ω : E d) with hc
  have hφ : colatitude N ω = Real.arccos c := colatitude_eq_arccos hN ω
  have hc1 : c ≠ 1 := fun h ↦ by rw [hφ, h, Real.arccos_one] at hφ0; exact lt_irrefl _ hφ0
  have hcm1 : c ≠ -1 := fun h ↦ by rw [hφ, h, Real.arccos_neg_one] at hφπ; exact lt_irrefl _ hφπ
  have hcabs : c ^ 2 < 1 := by
    have h1 : |c| ≤ 1 := by
      have := abs_real_inner_le_norm N (ω : E d)
      rwa [hN, norm_eq_of_mem_sphere ω, one_mul] at this
    have h2 : |c| ≠ 1 := by
      intro h
      rcases abs_eq (zero_le_one) |>.1 h with h | h
      · exact hc1 h
      · exact hcm1 h
    have : |c| < 1 := lt_of_le_of_ne h1 h2
    nlinarith [abs_nonneg c, sq_abs c]
  set w : E d → ℝ := fun x ↦ F (Real.arccos (inner ℝ N x)) with hw
  set a : ℝ := deriv F (colatitude N ω) * (-(1 / √(1 - c ^ 2)))
  -- the gradient of `w` at `ω`
  have hin : HasFDerivAt (fun x : E d ↦ inner ℝ N x) (innerSL ℝ N) (ω : E d) :=
    (innerSL ℝ N).hasFDerivAt
  have harc := Real.hasDerivAt_arccos hcm1 hc1
  have hF' : HasDerivAt F (deriv F (colatitude N ω)) (Real.arccos c) := by
    rw [← hφ]; exact hF.hasDerivAt
  have hwd : HasFDerivAt w (a • innerSL ℝ N) (ω : E d) :=
    HasDerivAt.comp_hasFDerivAt (h₂ := F ∘ Real.arccos) (ω : E d) (hF'.comp c harc) hin
  have hgrad : ∇ w (ω : E d) = a • N := by
    refine HasGradientAt.gradient ?_
    rw [hasGradientAt_iff_hasFDerivAt]
    refine hwd.congr_fderiv ?_
    ext v
    simp
  have hfw : ∀ ω' : sphere (0 : E d) 1, F (colatitude N ω') = w (0 + (1 : ℝ) • (ω' : E d)) :=
    fun ω' ↦ by rw [zero_add, one_smul, colatitude_eq_arccos hN]
  have hwdiff : DifferentiableAt ℝ w (0 + (1 : ℝ) • (ω : E d)) := by
    rw [zero_add, one_smul]; exact hwd.differentiableAt
  rw [norm_sq_gradient_homogExt0_of_eq (w := w) 0 one_pos hfw ω hwdiff]
  simp only [zero_add, one_smul, one_pow, one_mul]
  have hrad : radialDeriv w 0 (ω : E d) = a * c := by
    rw [radialDeriv, hgrad, sub_zero, norm_eq_of_mem_sphere ω, inv_one, one_smul,
      inner_smul_left, RCLike.conj_to_real, hc]
  rw [hrad, hgrad, norm_smul, hN, mul_one, Real.norm_eq_abs, sq_abs]
  have hpos : 0 < 1 - c ^ 2 := by linarith
  have hsq : √(1 - c ^ 2) ^ 2 = 1 - c ^ 2 := Real.sq_sqrt hpos.le
  have hne : √(1 - c ^ 2) ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  simp only [a]
  field_simp
  rw [hsq]



/-! ### The colatitude integration formula -/



/-- The last `n` coordinates of `x ∈ E (n + 1)`. -/
private noncomputable def tailE {n : ℕ} (x : E (n + 1)) : E n :=
  WithLp.toLp 2 fun i ↦ x.ofLp i.succ

private theorem norm_sq_eq_head_add_tail {n : ℕ} (x : E (n + 1)) :
    ‖x‖ ^ 2 = x.ofLp 0 ^ 2 + ‖tailE x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  simp [tailE]

/-- Splitting `E (n + 1) = ℝ × E n` (Tonelli). -/
private theorem lintegral_head_tail {n : ℕ} {H : ℝ × E n → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ x : E (n + 1), H (x.ofLp 0, tailE x) = ∫⁻ s : ℝ, ∫⁻ y : E n, H (s, y) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin (n + 1))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin n))
  have hΦ := (h3.comp h2).comp h1
  rw [← Measure.volume_eq_prod] at hΦ
  have := hΦ.lintegral_comp hH
  rw [← lintegral_prod _ hH.aemeasurable, ← Measure.volume_eq_prod, ← this]
  rfl

/-- Radial integrals on `E n`, `n ≥ 1`:
`∫⁻ g(|y|) dy = σ_n(𝕊) ∫⁻_{ρ > 0} ρ^{n-1} g(ρ) dρ`. -/
private theorem lintegral_norm_eq {n : ℕ} (hn : 1 ≤ n) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ y : E n, g ‖y‖ = (volume : Measure (E n)).toSphere univ *
      ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (n - 1)) * g ρ := by
  have := nontrivial_E hn
  rw [lintegral_eq_lintegral_Ioi_lintegral_toSphere (h := fun y : E n ↦ g ‖y‖)
      (hg.comp measurable_norm),
    finrank_euclideanSpace_fin, ← lintegral_const_mul (f := fun ρ : ℝ ↦
      ENNReal.ofReal (ρ ^ (n - 1)) * g ρ) _ ((by fun_prop : Measurable fun ρ : ℝ ↦
      ENNReal.ofReal (ρ ^ (n - 1))).mul hg)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun ρ hρ ↦ ?_
  have hρ : 0 < ρ := hρ
  have hin : ∀ ω : sphere (0 : E n) 1, ‖ρ • (ω : E n)‖ = ρ := fun ω ↦ by
    rw [norm_smul, norm_eq_of_mem_sphere ω, mul_one, Real.norm_of_nonneg hρ.le]
  simp only [hin, lintegral_const]
  ring

/-- Polar coordinates in the upper half plane:
`∫⁻_ℝ ∫⁻_{ρ > 0} K(s, ρ) = ∫⁻_{t > 0} ∫⁻_{0 < φ < π} t K(t cos φ, t sin φ)`. -/
private theorem lintegral_halfPlane {K : ℝ × ℝ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ s : ℝ, ∫⁻ ρ in Ioi (0 : ℝ), K (s, ρ) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ φ in Ioo 0 π,
        ENNReal.ofReal t * K (t * Real.cos φ, t * Real.sin φ) := by
  set f : ℝ × ℝ → ℝ≥0∞ := {p | 0 < p.2}.indicator K with hf
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  have hfm : Measurable f := hK.indicator hS
  have h1 : ∫⁻ s : ℝ, ∫⁻ ρ in Ioi (0 : ℝ), K (s, ρ) = ∫⁻ p : ℝ × ℝ, f p := by
    rw [Measure.volume_eq_prod, lintegral_prod _ hfm.aemeasurable]
    refine lintegral_congr fun s ↦ ?_
    rw [← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun ρ ↦ ?_
    simp [hf, indicator]
  have hT : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioo 0 π) := measurableSet_Ioi.prod measurableSet_Ioo
  have hsub : Ioi (0 : ℝ) ×ˢ Ioo 0 π ⊆ polarCoord.target := by
    rintro ⟨t, φ⟩ ⟨ht, hφ⟩
    exact ⟨ht, by linarith [Real.pi_pos, hφ.1], hφ.2⟩
  have h2 : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) =
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo 0 π, ENNReal.ofReal p.1 * K (polarCoord.symm p) := by
    rw [← lintegral_indicator polarCoord.open_target.measurableSet,
      ← lintegral_indicator hT]
    refine lintegral_congr fun p ↦ ?_
    by_cases hp : p ∈ polarCoord.target
    · rw [indicator_of_mem hp]
      obtain ⟨ht, hφ⟩ := hp
      have ht : 0 < p.1 := ht
      by_cases hφ0 : 0 < p.2
      · have hsin : 0 < p.1 * Real.sin p.2 := mul_pos ht (Real.sin_pos_of_pos_of_lt_pi hφ0 hφ.2)
        rw [indicator_of_mem (show p ∈ Ioi (0 : ℝ) ×ˢ Ioo 0 π from ⟨ht, hφ0, hφ.2⟩)]
        simp [hf, hsin, smul_eq_mul]
      · have hsin : ¬ 0 < p.1 * Real.sin p.2 := by
          have := Real.sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.1 hφ0) hφ.1.le
          nlinarith
        rw [indicator_of_notMem (fun h ↦ hφ0 h.2.1)]
        simp [hf, hsin]
    · rw [indicator_of_notMem hp, indicator_of_notMem (fun h ↦ hp (hsub h))]
  rw [h1, ← lintegral_comp_polarCoord_symm, h2, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1 * K (polarCoord.symm p))
      ((by fun_prop : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal p.1).mul
        (hK.comp (by fun_prop))).aemeasurable]
  simp

/-- `∫⁻_{(0,1)} t^n dt` is positive and finite. -/
private theorem lintegral_Ioo_pow_ne_zero_ne_top (n : ℕ) :
    ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ n) ≠ 0 ∧
      ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ n) ≠ ⊤ := by
  constructor
  · intro h0
    rw [lintegral_eq_zero_iff (by fun_prop)] at h0
    have hpos : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), False := by
      filter_upwards [h0, ae_restrict_mem measurableSet_Ioo] with t ht hmem
      have : 0 < t ^ n := pow_pos hmem.1 n
      simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at ht
      linarith
    rw [ae_iff] at hpos
    simp at hpos
  · refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioo (0 : ℝ) 1, 1) (by simp) ?_
    refine setLIntegral_mono (by fun_prop) fun t ht ↦ ?_
    rw [ENNReal.ofReal_le_one]
    exact pow_le_one₀ ht.1.le ht.2.le

/-- **Colatitude formula, pole `e₀`.** For `n ≥ 1` and measurable `h : ℝ → [0, ∞]`,
`∫⁻_{𝕊^n} h(φ(ω)) dσ = σ_n(𝕊^{n-1}) ∫⁻_0^π h(φ) sin^{n-1}(φ) dφ`. -/
private theorem lintegral_toSphere_colatitude_single {n : ℕ} (hn : 1 ≤ n) {h : ℝ → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ ω : sphere (0 : E (n + 1)) 1, h (colatitude (EuclideanSpace.single 0 1) ω)
        ∂(volume : Measure (E (n + 1))).toSphere =
      (volume : Measure (E n)).toSphere univ *
        ∫⁻ φ in Ioo 0 π, ENNReal.ofReal (Real.sin φ ^ (n - 1)) * h φ := by
  have := nontrivial_E (show 1 ≤ n + 1 by omega)
  set e₀ : E (n + 1) := EuclideanSpace.single 0 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  set S := ∫⁻ ω : sphere (0 : E (n + 1)) 1, h (colatitude e₀ ω)
    ∂(volume : Measure (E (n + 1))).toSphere
  set B := ∫⁻ φ in Ioo 0 π, ENNReal.ofReal (Real.sin φ ^ (n - 1)) * h φ
  set A := ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ n)
  -- the test function on `E (n + 1)`, in the form `G(x₀, |tail x|)`
  set G : ℝ × ℝ → ℝ≥0∞ := fun q ↦
    if √(q.1 ^ 2 + q.2 ^ 2) < 1 then h (Real.arccos (q.1 / √(q.1 ^ 2 + q.2 ^ 2))) else 0
    with hG
  have hGm : Measurable G := by
    refine Measurable.ite (measurableSet_lt (by fun_prop) measurable_const) ?_ measurable_const
    exact hh.comp (Real.continuous_arccos.measurable.comp (by fun_prop))
  set Ψ : E (n + 1) → ℝ≥0∞ := fun x ↦ G (x.ofLp 0, ‖tailE x‖)
  have htail : Continuous (tailE (n := n)) := by unfold tailE; fun_prop
  have hΨm : Measurable Ψ := hGm.comp (by
    refine Measurable.prodMk ?_ ?_
    · exact (measurable_pi_apply 0).comp (PiLp.continuous_ofLp 2 _).measurable
    · exact measurable_norm.comp htail.measurable)
  have hnormx : ∀ x : E (n + 1), √(x.ofLp 0 ^ 2 + ‖tailE x‖ ^ 2) = ‖x‖ := fun x ↦ by
    rw [← norm_sq_eq_head_add_tail, Real.sqrt_sq (norm_nonneg x)]
  -- first computation: polar coordinates in `E (n + 1)`
  have hway1 : ∫⁻ x, Ψ x = A * S := by
    rw [lintegral_eq_lintegral_Ioi_lintegral_toSphere hΨm, finrank_euclideanSpace_fin,
      Nat.add_sub_cancel]
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ n) *
        ∫⁻ ω : sphere (0 : E (n + 1)) 1, Ψ (t • (ω : E (n + 1)))
          ∂(volume : Measure (E (n + 1))).toSphere =
        (Iio (1 : ℝ)).indicator (fun t ↦ ENNReal.ofReal (t ^ n) * S) t := by
      intro t ht
      have ht : 0 < t := ht
      have hval : ∀ ω : sphere (0 : E (n + 1)) 1, Ψ (t • (ω : E (n + 1))) =
          (Iio (1 : ℝ)).indicator (fun _ ↦ h (colatitude e₀ ω)) t := fun ω ↦ by
        have hn1 : ‖t • (ω : E (n + 1))‖ = t := by
          rw [norm_smul, norm_eq_of_mem_sphere ω, mul_one, Real.norm_of_nonneg ht.le]
        simp only [Ψ, hG, hnormx, hn1, indicator, mem_Iio]
        split_ifs
        · rw [colatitude_eq_arccos he₀, EuclideanSpace.inner_single_left]
          congr 2
          simp only [map_one, one_mul, PiLp.smul_apply, smul_eq_mul]
          field_simp
        · rfl
      simp_rw [hval]
      by_cases ht1 : t < 1
      · simp [indicator, ht1, S]
      · simp [indicator, ht1]
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt, setLIntegral_indicator measurableSet_Iio,
      inter_comm, Ioi_inter_Iio, lintegral_mul_const _ (by fun_prop)]
  -- second computation: split off the first coordinate, then polar coordinates in the plane
  have hway2 : ∫⁻ x, Ψ x = (volume : Measure (E n)).toSphere univ * (A * B) := by
    have hsplit := lintegral_head_tail (n := n) (H := fun q : ℝ × E n ↦ G (q.1, ‖q.2‖))
      (hGm.comp (measurable_fst.prodMk measurable_snd.norm))
    simp only at hsplit
    rw [hsplit]
    have hrad : ∀ s : ℝ, ∫⁻ y : E n, G (s, ‖y‖) = (volume : Measure (E n)).toSphere univ *
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (n - 1)) * G (s, ρ) := fun s ↦
      lintegral_norm_eq hn (hGm.comp (measurable_const.prodMk measurable_id))
    simp_rw [hrad]
    have hKm : Measurable fun q : ℝ × ℝ ↦ ENNReal.ofReal (q.2 ^ (n - 1)) * G q :=
      (by fun_prop : Measurable fun q : ℝ × ℝ ↦ ENNReal.ofReal (q.2 ^ (n - 1))).mul hGm
    rw [lintegral_const_mul' _ _ (measure_ne_top _ _), lintegral_halfPlane hKm]
    congr 1
    have hin : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ φ in Ioo 0 π, ENNReal.ofReal t *
        (ENNReal.ofReal ((t * Real.sin φ) ^ (n - 1)) * G (t * Real.cos φ, t * Real.sin φ)) =
        (Iio (1 : ℝ)).indicator (fun t ↦ ENNReal.ofReal (t ^ n)) t * B := by
      intro t ht
      have ht : 0 < t := ht
      rw [← lintegral_const_mul' _ _ (by
        by_cases ht1 : t < 1 <;> simp [indicator, ht1])]
      refine setLIntegral_congr_fun measurableSet_Ioo fun φ hφ ↦ ?_
      have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
      have hsq : √((t * Real.cos φ) ^ 2 + (t * Real.sin φ) ^ 2) = t := by
        rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one,
          Real.sqrt_sq ht.le]
      have harc : Real.arccos (t * Real.cos φ / t) = φ := by
        rw [mul_div_cancel_left₀ _ ht.ne', Real.arccos_cos hφ.1.le hφ.2.le]
      have hpow : ENNReal.ofReal t * ENNReal.ofReal ((t * Real.sin φ) ^ (n - 1)) =
          ENNReal.ofReal (t ^ n) * ENNReal.ofReal (Real.sin φ ^ (n - 1)) := by
        rw [← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul (by positivity), mul_pow,
          ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]
      simp only [hG, hsq, harc]
      by_cases ht1 : t < 1
      · simp only [ht1, ite_true, indicator, mem_Iio]
        rw [← mul_assoc, hpow, mul_assoc]
      · simp [ht1, indicator]
    rw [setLIntegral_congr_fun measurableSet_Ioi hin, lintegral_mul_const _ (by
      exact (by fun_prop : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ n)).indicator
        measurableSet_Iio), setLIntegral_indicator measurableSet_Iio, inter_comm, Ioi_inter_Iio]
  have hA := lintegral_Ioo_pow_ne_zero_ne_top n
  rw [hway1, ← mul_assoc, mul_comm _ A, mul_assoc] at hway2
  exact (ENNReal.mul_right_inj hA.1 hA.2).1 hway2

/-- **Colatitude formula.** Let `d ≥ 2` and `|N| = 1`. For every measurable
`h : ℝ → [0, ∞]`, `∫⁻_𝕊 h(φ(ω)) dσ = c_d ∫⁻_0^π h(φ) sin^{d-2}(φ) dφ`, with
`c_d = σ_{d-1}(𝕊^{d-2})` (finite and positive, `colatConst_ne_zero`, `colatConst_ne_top`). -/
theorem lintegral_toSphere_colatitude (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {h : ℝ → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ ω : sphere (0 : E d) 1, h (colatitude N ω) ∂(volume : Measure (E d)).toSphere =
      (volume : Measure (E (d - 1))).toSphere univ *
        ∫⁻ φ in Ioo 0 π, ENNReal.ofReal (Real.sin φ ^ (d - 2)) * h φ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  set e₀ : E (n + 1) := EuclideanSpace.single 0 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  set R : E (n + 1) ≃ₗᵢ[ℝ] E (n + 1) := Submodule.reflection (ℝ ∙ (e₀ - N))ᗮ
  have hR : R e₀ = N := Submodule.reflection_sub (by rw [he₀, hN])
  have hcol : ∀ ω, colatitude N (sphereMap R ω) = colatitude e₀ ω := fun ω ↦ by
    rw [colatitude, colatitude, coe_sphereMap, ← hR]
    exact R.toLinearIsometry.angle_map _ _
  have hmp := measurePreserving_sphereMap R
  rw [← hmp.lintegral_comp (f := fun ω ↦ h (colatitude N ω))
    (hh.comp (continuous_colatitude hN).measurable)]
  simp_rw [hcol]
  exact lintegral_toSphere_colatitude_single hn hh

theorem colatConst_ne_zero (hd : 2 ≤ d) :
    (volume : Measure (E (d - 1))).toSphere univ ≠ 0 := by
  have := nontrivial_E (show 1 ≤ d - 1 by omega)
  rw [Ne, Measure.measure_univ_eq_zero]
  exact Measure.toSphere_ne_zero _

theorem colatConst_ne_top (d : ℕ) : (volume : Measure (E (d - 1))).toSphere univ ≠ ⊤ :=
  measure_ne_top _ _

/-- **Null sets of colatitudes.** If `Z ⊆ ℝ` is Lebesgue-null, then `φ(ω) ∉ Z` for `σ`-a.e. `ω`. -/
theorem ae_colatitude_notMem (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {Z : Set ℝ}
    (hZ : volume Z = 0) :
    ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere, colatitude N ω ∉ Z := by
  obtain ⟨Z', hZZ', hZ'm, hZ'0⟩ := exists_measurable_superset_of_null hZ
  have hint := lintegral_toSphere_colatitude hd hN (measurable_one.indicator hZ'm)
  have h0 : ∫⁻ φ in Ioo 0 π, ENNReal.ofReal (Real.sin φ ^ (d - 2)) * Z'.indicator 1 φ = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    refine ae_restrict_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ'0] with φ hφ
    simp [hφ]
  rw [h0, mul_zero, lintegral_eq_zero_iff (f := fun ω ↦ Z'.indicator 1 (colatitude N ω))
    ((measurable_one.indicator hZ'm).comp (continuous_colatitude hN).measurable)] at hint
  filter_upwards [hint] with ω hω hmem
  simp [indicator_of_mem (hZZ' hmem)] at hω

/-- **Colatitude formula, Bochner form.** For `d ≥ 2`, `|N| = 1` and a measurable `g ≥ 0`,
`∫_𝕊 g(φ(ω)) dσ = c_d ∫_0^π sin^{d-2}(φ) g(φ) dφ` with `c_d = σ_{d-1}(𝕊^{d-2})`. -/
theorem integral_toSphere_colatitude (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {g : ℝ → ℝ}
    (hg : Measurable g) (hg0 : ∀ φ, 0 ≤ g φ) :
    ∫ ω : sphere (0 : E d) 1, g (colatitude N ω) ∂(volume : Measure (E d)).toSphere =
      ((volume : Measure (E (d - 1))).toSphere univ).toReal *
        ∫ φ in Ioo 0 π, Real.sin φ ^ (d - 2) * g φ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω ↦ hg0 _)
      (hg.comp (continuous_colatitude hN).measurable).aestronglyMeasurable,
    lintegral_toSphere_colatitude hd hN hg.ennreal_ofReal, ENNReal.toReal_mul,
    integral_eq_lintegral_of_nonneg_ae]
  · congr 2
    refine setLIntegral_congr_fun measurableSet_Ioo fun φ hφ ↦ ?_
    rw [ENNReal.ofReal_mul (pow_nonneg (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2).le _)]
  · exact ae_restrict_of_forall_mem measurableSet_Ioo fun φ hφ ↦
      mul_nonneg (pow_nonneg (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2).le _) (hg0 φ)
  · exact ((Real.continuous_sin.pow _).measurable.mul hg).aestronglyMeasurable



/-! ### Radial test functions on caps -/



/-- `F` clamped to `[0, θ]`: `φ ↦ F (max 0 (min φ θ))`. -/
private noncomputable def clampF (F : ℝ → ℝ) (θ : ℝ) (φ : ℝ) : ℝ :=
  F (max 0 (min φ θ))

private theorem clamp_mem {θ : ℝ} (hθ : 0 ≤ θ) (φ : ℝ) : max 0 (min φ θ) ∈ Icc 0 θ :=
  ⟨le_max_left _ _, max_le hθ (min_le_right _ _)⟩

private theorem abs_clamp_sub_le (θ x y : ℝ) :
    |max 0 (min x θ) - max 0 (min y θ)| ≤ |x - y| := by
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  have := abs_min_sub_min_le_max x θ y θ
  simpa using this

private theorem lipschitzWith_clampF {F : ℝ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) {K : ℝ≥0}
    (hF : LipschitzOnWith K F (Icc 0 θ)) : LipschitzWith K (clampF F θ) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  refine (hF.dist_le_mul _ (clamp_mem hθ x) _ (clamp_mem hθ y)).trans ?_
  rw [Real.dist_eq, Real.dist_eq]
  exact mul_le_mul_of_nonneg_left (abs_clamp_sub_le θ x y) K.2

private theorem clampF_of_mem {F : ℝ → ℝ} {θ φ : ℝ} (hφ : φ ∈ Icc 0 θ) : clampF F θ φ = F φ := by
  rw [clampF, min_eq_left hφ.2, max_eq_right hφ.1]

private theorem clampF_of_le {F : ℝ → ℝ} {θ φ : ℝ} (hθ : 0 ≤ θ) (hF : F θ = 0) (hφ : θ ≤ φ) :
    clampF F θ φ = 0 := by
  rw [clampF, min_eq_right hφ, max_eq_right hθ, hF]

private theorem deriv_clampF_of_mem {F : ℝ → ℝ} {θ φ : ℝ} (hφ : φ ∈ Ioo 0 θ) :
    deriv (clampF F θ) φ = deriv F φ := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Ioo_mem_nhds hφ.1 hφ.2] with x hx
  exact clampF_of_mem (Ioo_subset_Icc_self hx)

private theorem deriv_clampF_of_lt {F : ℝ → ℝ} {θ φ : ℝ} (hθ : 0 ≤ θ) (hF : F θ = 0)
    (hφ : θ < φ) : deriv (clampF F θ) φ = 0 := by
  rw [Filter.EventuallyEq.deriv_eq (f := fun _ ↦ (0 : ℝ)), deriv_const]
  filter_upwards [lt_mem_nhds hφ] with x hx
  exact clampF_of_le hθ hF hx.le

/-- An integral over `(0, π)` of a function vanishing a.e. on `(θ, π)` is an integral over
`0..θ`. -/
private theorem integral_Ioo_pi_eq {G : ℝ → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ π)
    (hG : ∀ φ, θ < φ → G φ = 0) : ∫ φ in Ioo 0 π, G φ = ∫ φ in 0..θ, G φ := by
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioo.nullMeasurableSet
    (Ioo_subset_Ioo_right hθπ), intervalIntegral.integral_of_le hθ, integral_Ioc_eq_integral_Ioo]
  filter_upwards [volume.ae_ne θ] with φ hφ hmem
  exact hG φ (lt_of_le_of_ne (not_lt.1 fun h ↦ hmem.2 ⟨hmem.1.1, h⟩) (Ne.symm hφ))

/-- **Radial test functions.** Let `d ≥ 2`, `|N| = 1`, `0 < θ ≤ π`, and
let `F` be admissible for `θ`. Then the colatitude function `ω ↦ F(φ(ω))` (with `F` clamped to
`[0, θ]`) is admissible for the cap `C(θ)`, and its Rayleigh quotient is the one-dimensional
quotient `capRayleigh d θ F`. -/
theorem exists_isSphAdmissible_sphRayleigh_eq (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ ≤ π) {F : ℝ → ℝ} (hF : IsCapAdmissible θ F) :
    ∃ f : sphere (0 : E d) 1 → ℝ, IsSphAdmissible (sphCap N θ) f ∧
      sphRayleigh f = capRayleigh d θ F := by
  obtain ⟨K, hK⟩ := hF.lipschitzOn
  have hFθ := hF.apply_right_eq_zero
  set Fc := clampF F θ
  have hlip := lipschitzWith_clampF hθ.le hK
  set f : sphere (0 : E d) 1 → ℝ := fun ω ↦ Fc (colatitude N ω)
  set c := ((volume : Measure (E (d - 1))).toSphere univ).toReal
  have hc : 0 < c := ENNReal.toReal_pos (colatConst_ne_zero hd) (colatConst_ne_top d)
  set M := ∫ φ in 0..θ, F φ ^ 2 * Real.sin φ ^ (d - 2)
  set D := ∫ φ in 0..θ, deriv F φ ^ 2 * Real.sin φ ^ (d - 2)
  -- the `L²` norm
  have hL2 : sphL2Sq f = c * M := by
    rw [sphL2Sq, integral_toSphere_colatitude hd hN (g := fun φ ↦ Fc φ ^ 2)
      (hlip.continuous.measurable.pow_const 2) (fun _ ↦ sq_nonneg _),
      integral_Ioo_pi_eq hθ.le hθπ (fun φ hφ ↦ by
        simp [Fc, clampF_of_le hθ.le hFθ hφ.le])]
    congr 1
    refine intervalIntegral.integral_congr fun φ hφ ↦ ?_
    rw [uIcc_of_le hθ.le] at hφ
    simp only [Fc, clampF_of_mem hφ]
    ring
  -- the Dirichlet energy
  have hDir : sphDirichlet f = c * D := by
    have hZ : volume ({0, π} ∪ {φ | ¬DifferentiableAt ℝ Fc φ}) = 0 := by
      refine measure_union_null ((Set.toFinite _).measure_zero _) ?_
      exact ae_iff.1 hlip.ae_differentiableAt
    have hae := ae_colatitude_notMem hd hN hZ
    have hpt : ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
        ‖∇ (homogExt0 f) (ω : E d)‖ ^ 2 = deriv Fc (colatitude N ω) ^ 2 := by
      filter_upwards [hae] with ω hω
      simp only [mem_union, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq, not_or,
        not_not] at hω
      exact norm_sq_gradient_homogExt0_comp_colatitude hN ω
        (lt_of_le_of_ne (colatitude_nonneg N ω) (Ne.symm hω.1.1))
        (lt_of_le_of_ne (colatitude_le_pi N ω) hω.1.2) hω.2
    rw [sphDirichlet, integral_congr_ae hpt,
      integral_toSphere_colatitude hd hN (g := fun φ ↦ deriv Fc φ ^ 2)
        ((measurable_deriv Fc).pow_const 2) (fun _ ↦ sq_nonneg _),
      integral_Ioo_pi_eq hθ.le hθπ (fun φ hφ ↦ by
        simp [Fc, deriv_clampF_of_lt hθ.le hFθ hφ])]
    congr 1
    rw [intervalIntegral.integral_of_le hθ.le]
    simp only [D]
    rw [intervalIntegral.integral_of_le hθ.le, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ ↦ ?_
    simp only [Fc, deriv_clampF_of_mem hφ]
    ring
  -- positivity of the `L²` norm
  have hMpos : 0 < M := by
    have hcont : ContinuousOn F (Icc 0 θ) := hK.continuousOn
    set U := Ioo 0 θ ∩ F ⁻¹' {0}ᶜ
    have hUo : IsOpen U :=
      (hcont.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo isOpen_compl_singleton
    have hUne : U.Nonempty := by
      by_contra hU
      rw [not_nonempty_iff_eq_empty] at hU
      have h0 : EqOn F 0 (Ioo 0 θ) := fun φ hφ ↦ by
        by_contra hne
        have : φ ∈ U := ⟨hφ, hne⟩
        rw [hU] at this
        exact this
      have h0' : EqOn F 0 (Icc 0 θ) :=
        h0.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self
          (by rw [closure_Ioo hθ.ne])
      obtain ⟨φ₀, hφ₀, hne⟩ := hF.exists_ne_zero
      exact hne (h0' hφ₀)
    have hint : IntervalIntegrable (fun φ ↦ F φ ^ 2 * Real.sin φ ^ (d - 2)) volume 0 θ := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hθ.le]
      exact (hcont.pow 2).mul (Real.continuous_sin.pow _).continuousOn
    rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' ?_ hint]
    · refine ⟨hθ, lt_of_lt_of_le (hUo.measure_pos volume hUne) (measure_mono ?_)⟩
      rintro φ ⟨hφ, hFφ⟩
      refine ⟨?_, Ioo_subset_Ioc_self hφ⟩
      have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 (hφ.2.trans_le hθπ)
      simp only [Function.mem_support]
      exact mul_ne_zero (pow_ne_zero 2 hFφ) (pow_ne_zero _ hs.ne')
    · rw [uIoc_of_le hθ.le]
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun φ hφ ↦ ?_
      exact mul_nonneg (sq_nonneg _)
        (pow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hφ.1.le (hφ.2.trans hθπ)) _)
  refine ⟨f, ⟨⟨_, lipschitzWith_comp_colatitude (hlip.lipschitzOnWith) N⟩, fun ω hω ↦ ?_, ?_⟩, ?_⟩
  · exact clampF_of_le hθ.le hFθ (not_lt.1 hω)
  · rw [hL2]; exact mul_pos hc hMpos
  · rw [sphRayleigh, hL2, hDir, capRayleigh, mul_div_mul_left _ _ hc.ne']

/-- **Colatitude comparison**: for `d ≥ 2`, `|N| = 1` and `0 < θ ≤ π`,
`λ₁(C(θ)) ≤ Λ_d(θ)`. -/
theorem sphEigenvalue_sphCap_le_capEigenvalue (hd : 2 ≤ d) {N : E d} (hN : ‖N‖ = 1) {θ : ℝ}
    (hθ : 0 < θ) (hθπ : θ ≤ π) : sphEigenvalue (sphCap N θ) ≤ capEigenvalue d θ := by
  have hbdd : BddBelow (sphRayleigh '' {f | IsSphAdmissible (sphCap N θ) f}) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨f, -, rfl⟩
    exact div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)
  have hne : (capRayleigh d θ '' {F | IsCapAdmissible θ F}).Nonempty := by
    refine ⟨_, fun φ ↦ θ - φ, ⟨⟨1, ?_⟩, by simp, ⟨0, ⟨le_rfl, hθ.le⟩, by simp [hθ.ne']⟩⟩, rfl⟩
    refine LipschitzWith.lipschitzOnWith (LipschitzWith.of_dist_le_mul fun x y ↦ ?_)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul,
      show θ - x - (θ - y) = -(x - y) by ring, abs_neg]
  refine le_csInf hne ?_
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨f, hf, hfR⟩ := exists_isSphAdmissible_sphRayleigh_eq hd hN hθ hθπ hF
  rw [← hfR]
  exact csInf_le hbdd ⟨f, hf, rfl⟩

end

end EllipticBernoulli
