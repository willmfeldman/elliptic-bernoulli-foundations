/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.TwoPhase
public import EllipticBernoulli.TwoPhase.Defs
import EllipticBernoulli.Harmonic.Affine
import EllipticBernoulli.Sphere.Radial
import EllipticBernoulli.TwoPhase.ACF
import EllipticBernoulli.TwoPhase.ACFCore
import EllipticBernoulli.TwoPhase.FreeBoundaryCondition
import EllipticBernoulli.TwoPhase.Homogeneous
import EllipticBernoulli.TwoPhase.Hopf
import EllipticBernoulli.TwoPhase.OneDim
import EllipticBernoulli.TwoPhase.Regularity
import EllipticBernoulli.TwoPhase.Rescaling
import EllipticBernoulli.TwoPhase.Weiss

/-!
# Classification of global two-phase minimizers

A Lipschitz local minimizer `u` of
`J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ` that takes a positive and a negative value is a two-plane
function `a (x·e + c)⁺ - b (x·e + c)⁻` with `‖e‖ = 1`, `a, b > 0` and `a² - b² = 1`.

* `TwoPhaseClassificationIn d`: the conclusion of `TwoPhaseClassificationStatement` in a fixed
  dimension `d`.
* `twoPhaseClassification_of_friedlandHayman`: for `d ≥ 2`, the Friedland–Hayman inequality in
  dimension `d` (`FriedlandHaymanIn d`) implies `TwoPhaseClassificationIn d`.
* `twoPhaseClassificationIn_one`: the case `d = 1` (`twoPhaseClassification_one`), which needs no
  Friedland–Hayman inequality.
* `twoPhaseClassification_of_forall_friedlandHayman`: Friedland–Hayman in every dimension `d ≥ 2`
  implies `TwoPhaseClassificationStatement`.

The Friedland–Hayman inequality enters as a hypothesis; it is used only through the
Alt–Caffarelli–Friedman monotonicity formula (`acfMonotoneIn_of_friedlandHayman`).

## Proof (`d ≥ 2`)

1. *Base point.* `IsLocalEnergyMinimizer.exists_hopf_point_blowup` gives `x₀` with `u x₀ = 0`,
   `x₀ ∈ ∂{u < 0} ∩ closure {u > 0}`, an interior ball of `{u < 0}` touching `x₀`, and the
   resulting lower bound for the negative part of blow-ups. The point `x₀` stays general: the
   minimality of `u` is never transported by a translation, and harmonicity moves to rescalings
   through `HarmonicOnNhd.rescale`.
2. *Monotone quantities.* `W(r) = W(u, x₀, r)` has limits `W(0⁺) ≤ W(∞)` (`exists_tendsto_weissW`).
   `(u⁺, u⁻)` is an ACF pair at `x₀`, so `Φ(r) = Φ(u⁺, u⁻, x₀, r)` is nondecreasing, and
   `Φ(1) > 0` because both phases accumulate at `x₀` (`acfPhi_posPart_negPart_pos`).
3. *Blow-up* (`r_k = 1/(k+1)`) and 4. *blow-down* (`R_k = k + 1`): a subsequence of the rescalings
   converges to a `1`-homogeneous `u₀`, harmonic in both phases
   (`exists_subseq_tendsto_homogeneous`).
   Both phases of `u₀` are nonempty: the positive one by nondegeneracy, the negative one by the
   Hopf bound at the blow-up and by `Φ(u₀⁺, u₀⁻, 0, 1) ≥ Φ(1) > 0` at the blow-down. So `u₀` is a
   two-plane function (`homogeneousTwoPhaseIn`) and `W(0⁺) = W(∞) = |B₁|/2` (`weissW_twoPlane`).
5. *Rigidity.* The Weiss defect vanishes, so `x ↦ u(x₀ + x)` is `1`-homogeneous, hence a two-plane
   function, and `u(x) = a (x·e + c)⁺ - b (x·e + c)⁻` with `c = -x₀·e`.
6. *Free boundary condition.* `sq_sub_sq_eq_one_of_isLocalEnergyMinimizer_twoPlane`, applied to
   `u` itself, gives `a² - b² = 1`.

The blow-up classification of De Philippis–Spolaor–Velichkov (arXiv:1911.02165, Lemma 2.2) is
stated for the two-phase functional with both phases penalized and uses the nondegeneracy of both
phases. Here only `{u > 0}` is penalized, so the negative phase of the limits is controlled at a
Hopf point (step 3) and by the Alt–Caffarelli–Friedman functional (step 4); only the
classification of homogeneous functions (`homogeneousTwoPhaseIn`) follows their spectral idea.

## References

* H. W. Alt, L. A. Caffarelli, A. Friedman, *Variational problems with two phases and their free
  boundaries*, Trans. Amer. Math. Soc. 282 (1984), 431–461.
* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999), 317–326.
* G. De Philippis, L. Spolaor, B. Velichkov, *Regularity of the free boundary for the two-phase
  Bernoulli problem*, Invent. Math. 225 (2021), 347–394; arXiv:1911.02165.
* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and
  the growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped NNReal Gradient

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Positivity of the ACF functional at a two-phase point -/

/-- If `w` is Lipschitz and `C¹` on `{w > 0}`, `w x₀ ≤ 0` and `x₀ ∈ closure {w > 0}`, then
`∫_{B_r(x₀)} |∇w⁺|² > 0` for every `r > 0`. -/
private theorem setIntegral_norm_sq_gradient_posPart_pos {w : E d → ℝ} {L : ℝ≥0}
    (hw : LipschitzWith L w) (hsm : ContDiffOn ℝ 1 w {x | 0 < w x}) {x₀ : E d}
    (hx₀ : x₀ ∈ closure {x | 0 < w x}) (hw0 : w x₀ ≤ 0) {r : ℝ} (hr : 0 < r) :
    0 < ∫ x in ball x₀ r, ‖∇ (fun y ↦ max (w y) 0) x‖ ^ 2 := by
  have hopen : IsOpen {x | 0 < w x} := isOpen_lt continuous_const hw.continuous
  obtain ⟨p, hp, hpx⟩ := Metric.mem_closure_iff.1 hx₀ r hr
  have hp : 0 < w p := hp
  -- the segment `γ t = x₀ + t (p - x₀)`
  set γ : ℝ → E d := fun t ↦ x₀ + t • (p - x₀) with hγ
  set g : ℝ → ℝ := fun t ↦ w (γ t) with hg
  have hγc : Continuous γ := by fun_prop
  have hgc : Continuous g := hw.continuous.comp hγc
  set S := {t ∈ Icc (0 : ℝ) 1 | g t ≤ 0} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le hgc continuous_const)
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, zero_le_one⟩, by simpa [hg, hγ] using hw0⟩
  have hSbdd : BddAbove S := ⟨1, fun t ht ↦ ht.1.2⟩
  set s := sSup S with hs
  have hsS : s ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hSbdd
  have hs1 : s < 1 := by
    rcases hsS.1.2.lt_or_eq with h | h
    · exact h
    · exfalso
      have := hsS.2
      rw [h] at this
      simp only [hg, hγ, one_smul, add_sub_cancel] at this
      linarith
  have hgpos : ∀ t ∈ Ioc s 1, 0 < g t := fun t ht ↦ by
    by_contra hneg
    have : t ∈ S := ⟨⟨(hsS.1.1).trans ht.1.le, ht.2⟩, not_lt.1 hneg⟩
    exact absurd (le_csSup hSbdd this) (not_le.2 ht.1)
  -- mean value theorem on `[s, 1]`
  have hderiv : ∀ t ∈ Ioo s 1, HasDerivAt g (fderiv ℝ w (γ t) (p - x₀)) t := fun t ht ↦ by
    have hγt : 0 < w (γ t) := hgpos t ⟨ht.1, ht.2.le⟩
    have hdw : DifferentiableAt ℝ w (γ t) :=
      (hsm.differentiableOn one_ne_zero).differentiableAt (hopen.mem_nhds hγt)
    have hl : HasDerivAt γ (p - x₀) t := by
      have := ((hasDerivAt_id t).smul_const (p - x₀)).const_add x₀
      simp only [id, one_smul] at this
      exact this
    exact hdw.hasFDerivAt.comp_hasDerivAt t hl
  obtain ⟨t, ht, hteq⟩ := exists_hasDerivAt_eq_slope g (fun t ↦ fderiv ℝ w (γ t) (p - x₀)) hs1
    hgc.continuousOn hderiv
  have hslope : 0 < (g 1 - g s) / (1 - s) := by
    have h1 : 0 < g 1 := hgpos 1 ⟨hs1, le_rfl⟩
    have h2 : g s ≤ 0 := hsS.2
    exact div_pos (by linarith) (by linarith)
  set z := γ t with hz
  have hz0 : 0 < w z := hgpos t ⟨ht.1, ht.2.le⟩
  have hzne : fderiv ℝ w z ≠ 0 := by
    intro h
    rw [← hteq, h] at hslope
    simp at hslope
  have hzball : z ∈ ball x₀ r := by
    rw [mem_ball, hz, hγ, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hsS.1.1.trans_lt ht.1), ← dist_eq_norm, dist_comm]
    calc t * dist x₀ p ≤ 1 * dist x₀ p := by gcongr; exact ht.2.le
      _ < r := by rw [one_mul]; exact hpx
  -- a ball around `z` where `∇w ≠ 0`
  have hcont : ContinuousOn (fderiv ℝ w) {x | 0 < w x} :=
    hsm.continuousOn_fderiv_of_isOpen hopen le_rfl
  have hnhds : {x | 0 < w x ∧ fderiv ℝ w x ≠ 0} ∩ ball x₀ r ∈ 𝓝 z := by
    refine Filter.inter_mem ?_ (isOpen_ball.mem_nhds hzball)
    have h1 : {x | 0 < w x} ∈ 𝓝 z := hopen.mem_nhds hz0
    have h2 : ∀ᶠ x in 𝓝 z, fderiv ℝ w x ≠ 0 :=
      (hcont.continuousAt h1).eventually_ne hzne
    filter_upwards [h1, h2] with x hx1 hx2 using ⟨hx1, hx2⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hnhds
  -- the integrand is positive on `B_δ(z)`
  have hlip : LipschitzWith L fun y ↦ max (w y) 0 := hw.max_const 0
  have hint : IntegrableOn (fun x ↦ ‖∇ (fun y ↦ max (w y) 0) x‖ ^ 2) (ball x₀ r) :=
    integrableOn_norm_sq_gradient_ball hlip x₀ r
  rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun _ ↦ by positivity) hint]
  refine lt_of_lt_of_le (measure_ball_pos volume z hδ) (measure_mono fun x hx ↦ ?_)
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hδsub hx
  refine ⟨?_, hx3⟩
  have heq : (fun y ↦ max (w y) 0) =ᶠ[𝓝 x] w := by
    filter_upwards [hopen.mem_nhds hx1] with y hy using max_eq_left hy.le
  rw [Function.mem_support, heq.gradient_eq]
  refine pow_ne_zero 2 (norm_ne_zero_iff.2 fun h ↦ hx2 ?_)
  rw [gradient] at h
  exact (LinearIsometryEquiv.map_eq_zero_iff _).1 h

/-- `Φ(u⁺, u⁻, x₀, 1) > 0` at a point `x₀` with `u x₀ = 0` that lies in the closure of both
phases. -/
private theorem acfPhi_posPart_negPart_pos (hd : 2 ≤ d) {u : E d → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) {x₀ : E d}
    (hx₀ : u x₀ = 0) (hpos : x₀ ∈ closure {x | 0 < u x}) (hneg : x₀ ∈ closure {x | u x < 0}) :
    0 < acfPhi (fun y ↦ max (u y) 0) (fun y ↦ max (-u y) 0) x₀ 1 := by
  have hI : ∀ w : E d → ℝ, LipschitzWith L w → ContDiffOn ℝ 1 w {x | 0 < w x} →
      x₀ ∈ closure {x | 0 < w x} → w x₀ = 0 →
      HarmonicOnNhd (fun y ↦ max (w y) 0) {x | 0 < max (w x) 0} →
      0 < acfIntegral (fun y ↦ max (w y) 0) x₀ 1 := by
    intro w hw hsm hcl hw0 hH
    rw [acfIntegral_eq_rpow_mul_setIntegral_add (by omega) (hw.max_const 0)
      (fun _ ↦ le_max_right _ _) hH (by simp [hw0]) one_pos, Real.one_rpow, one_mul]
    have h1 := setIntegral_norm_sq_gradient_posPart_pos hw hsm hcl hw0.le one_pos
    have h2 := radialM_nonneg (fun y ↦ max (w y) 0) x₀ 1
    have h3 : 0 ≤ ((d : ℝ) - 2) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    positivity
  have hneg' : {x | 0 < -u x} = {x | u x < 0} := by ext; simp
  have h1 := hI u hu ((hmin.contDiffOn_posSet hu).of_le (by exact_mod_cast le_top)) hpos hx₀
    (hmin.harmonicOnNhd_posPart hu)
  have h2 := hI (fun y ↦ -u y) hu.neg
    (by rw [hneg']; exact ((hmin.contDiffOn_negSet hu).neg).of_le (by exact_mod_cast le_top))
    (by rw [hneg']; exact hneg) (by simp [hx₀]) (hmin.harmonicOnNhd_negPart hu)
  rw [acfPhi, one_pow, div_one]
  exact mul_pos h1 h2

/-- Along a sequence of rescalings `u_{x₀,R_k}` whose Weiss defects tend to `0`, and whose limits
along subsequences have both phases nonempty, some subsequence has `W(u, x₀, R_{φ k}) → |B₁|/2`. -/
private theorem exists_tendsto_weissW_rescale (hd : 1 ≤ d) {u : E d → ℝ} {L : ℝ≥0}
    (hu : LipschitzWith L u) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) {x₀ : E d}
    (hx₀ : u x₀ = 0) {R : ℕ → ℝ} (hR : ∀ k, 0 < R k)
    (hD : ∀ ρ ρ' : ℝ, 0 < ρ → ρ < ρ' →
      Tendsto (fun k ↦ weissDefect (blowup u x₀ (R k)) 0 ρ ρ') atTop (𝓝 0))
    (hphase : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ f₀ : E d → ℝ,
      (∀ x, Tendsto (fun k ↦ u (x₀ + R (φ k) • x) / R (φ k)) atTop (𝓝 (f₀ x))) →
      Tendsto (fun k ↦ acfPhi (fun y ↦ max (u y) 0) (fun y ↦ max (-u y) 0) x₀ (R (φ k))) atTop
        (𝓝 (acfPhi (fun y ↦ max (f₀ y) 0) (fun y ↦ max (-f₀ y) 0) 0 1)) →
      (∃ x, 0 < f₀ x) ∧ ∃ x, f₀ x < 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ weissW u x₀ (R (φ k))) atTop
        (𝓝 (volume.real (ball (0 : E d) 1) / 2)) := by
  set f : ℕ → E d → ℝ := fun k ↦ blowup u x₀ (R k) with hfdef
  have hf : ∀ k, LipschitzWith L (f k) := fun k ↦ lipschitzWith_blowup hu x₀ (hR k)
  have hf0 : ∀ k, f k 0 = 0 := fun k ↦ by simp [hfdef, blowup, hx₀]
  have hpos : ∀ k, HarmonicOnNhd (f k) {x | 0 < f k x} := fun k ↦
    harmonicOnNhd_blowup_posSet (hmin.harmonicOnNhd_posSet hu) x₀ (hR k)
  have hneg : ∀ k, HarmonicOnNhd (f k) {x | f k x < 0} := fun k ↦
    harmonicOnNhd_blowup_negSet (hmin.harmonicOnNhd_negSet hu) x₀ (hR k)
  obtain ⟨φ, hφ, f₀, hf₀L, hconv, hhom, hf₀pos, hf₀neg, hacf, hW⟩ :=
    exists_subseq_tendsto_homogeneous hd hf hf0 hpos hneg hD
  have hlim : ∀ x, Tendsto (fun k ↦ u (x₀ + R (φ k) • x) / R (φ k)) atTop (𝓝 (f₀ x)) :=
    fun x ↦ (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ x)
  have hacf1 : Tendsto (fun k ↦ acfPhi (fun y ↦ max (u y) 0) (fun y ↦ max (-u y) 0) x₀
      (R (φ k))) atTop (𝓝 (acfPhi (fun y ↦ max (f₀ y) 0) (fun y ↦ max (-f₀ y) 0) 0 1)) := by
    refine (hacf 1).congr fun k ↦ ?_
    simp only [hfdef]
    rw [posPart_blowup u x₀ (hR _), negPart_blowup u x₀ (hR _), acfPhi_blowup _ _ x₀ (hR _),
      mul_one]
  obtain ⟨hp, hn⟩ := hphase φ hφ f₀ hlim hacf1
  obtain ⟨e, a, b, he, ha, hb, hf₀⟩ :=
    homogeneousTwoPhaseIn d f₀ L hf₀L hhom hf₀pos hf₀neg hp hn
  have hf₀eq : f₀ = twoPlane a b e 0 := funext hf₀
  have hnull : volume {x | f₀ x = 0} = 0 := by
    rw [hf₀eq]; exact volume_setOf_twoPlane_eq_zero he ha hb
  refine ⟨φ, hφ, ?_⟩
  have h := hW hnull 1 one_pos
  rw [hf₀eq, weissW_twoPlane he ha hb.le] at h
  refine h.congr fun k ↦ ?_
  simp only [hfdef]
  rw [weissW_blowup hu x₀ (hR _), mul_one]

/-- The conclusion of `TwoPhaseClassificationStatement` in a fixed dimension `d`: every
`L`-Lipschitz local minimizer `u : ℝᵈ → ℝ` of `J(v, B) = ∫_B |∇v|² + 1_{v > 0}` taking a positive
and a negative value is `x ↦ a (x·e + c)⁺ - b (x·e + c)⁻` with `‖e‖ = 1`, `a, b > 0` and
`a² - b² = 1`. -/
@[expose] public def TwoPhaseClassificationIn (d : ℕ) : Prop :=
  ∀ {u : E d → ℝ} {L : ℝ≥0}, LipschitzWith L u →
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) u → (∃ x, 0 < u x) → (∃ x, u x < 0) →
    ∃ (e : E d) (c a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = 1 ∧
      ∀ x, u x = twoPlane a b e c x

/-- **Classification of global two-phase minimizers in dimension `d ≥ 2`, given the
Friedland–Hayman inequality in dimension `d`.** The Friedland–Hayman
inequality is a hypothesis here; it enters only through the ACF monotonicity formula. -/
public theorem twoPhaseClassification_of_friedlandHayman (hd : 2 ≤ d)
    (hFH : FriedlandHaymanIn d) : TwoPhaseClassificationIn d := by
  intro u L hu hmin hpos hneg
  have hd1 : 1 ≤ d := by omega
  obtain ⟨xn, hxn⟩ := hneg
  -- Step 1: the Hopf point
  obtain ⟨y, ρ, x₀, c₁, hρ, hdist, hx₀, hfr, hcl, hc₁, hhopf⟩ :=
    hmin.exists_hopf_point_blowup hu hxn hpos
  have hclneg : x₀ ∈ closure {x | u x < 0} := frontier_subset_closure hfr
  -- Step 2: Weiss limits and ACF monotonicity
  obtain ⟨W₀, W₁, hW₀, hW₁, -, hrig⟩ := exists_tendsto_weissW hd1 hu hmin hx₀
  have hpair : IsACFPair (fun y ↦ max (u y) 0) (fun y ↦ max (-u y) 0) x₀ L :=
    { nonneg_left := fun _ ↦ le_max_right _ _
      nonneg_right := fun _ ↦ le_max_right _ _
      lipschitz_left := hu.max_const 0
      lipschitz_right := hu.neg.max_const 0
      harmonic_left := hmin.harmonicOnNhd_posPart hu
      harmonic_right := hmin.harmonicOnNhd_negPart hu
      mul_eq_zero := fun x ↦ by
        rcases le_total (u x) 0 with h | h
        · rw [max_eq_right h, zero_mul]
        · rw [max_eq_right (neg_nonpos.2 h), mul_zero]
      left_apply_eq_zero := by simp [hx₀]
      right_apply_eq_zero := by simp [hx₀] }
  have hmono := acfMonotoneIn_of_friedlandHayman hd hFH _ _ x₀ L hpair
  have hΦ1 := acfPhi_posPart_negPart_pos hd hu hmin hx₀ hcl hclneg
  have hc₀ : 0 < 1 / (8 * d * Real.exp ((d : ℝ) / 2)) := by
    have : (0 : ℝ) < d := by exact_mod_cast hd1
    positivity
  -- Step 3: blow-up
  set r : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1) with hrdef
  have hr : ∀ k, 0 < r k := fun k ↦ by positivity
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, hWup⟩ := exists_tendsto_weissW_rescale hd1 hu hmin hx₀ hr
    (fun ρ ρ' hρ hρρ' ↦ tendsto_weissDefect_blowup_nhdsGT hd1 hu hmin hx₀ hr hr0 hρ hρρ')
    (fun φ hφ f₀ hlim _ ↦ by
      obtain ⟨hnegb, z, -, hz⟩ := hhopf (fun k ↦ r (φ k)) f₀ (fun k ↦ hr _) hlim
      refine ⟨⟨z, hc₀.trans_le hz⟩, ⟨y - x₀, ?_⟩⟩
      have h := hnegb (hr0.comp hφ.tendsto_atTop) (y - x₀)
      have hin : 0 < inner ℝ (y - x₀) (ρ⁻¹ • (y - x₀)) := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ← dist_eq_norm, dist_comm,
          hdist]
        field_simp
        exact hρ
      rw [max_eq_left hin.le] at h
      by_contra hge
      rw [max_eq_right (by linarith [not_lt.1 hge])] at h
      nlinarith)
  have hW₀' : W₀ = volume.real (ball (0 : E d) 1) / 2 := by
    refine tendsto_nhds_unique (hW₀.comp ?_) hWup
    exact tendsto_nhdsWithin_iff.2 ⟨hr0.comp hφ.tendsto_atTop,
      Eventually.of_forall fun k ↦ hr _⟩
  -- Step 4: blow-down
  set R : ℕ → ℝ := fun k ↦ (k : ℝ) + 1 with hRdef
  have hR : ∀ k, 0 < R k := fun k ↦ by positivity
  have hR1 : ∀ k, 1 ≤ R k := fun k ↦ by simp [hRdef]
  have hRtop : Tendsto R atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  obtain ⟨ψ, hψ, hWdown⟩ := exists_tendsto_weissW_rescale hd1 hu hmin hx₀ hR
    (fun ρ ρ' hρ hρρ' ↦ tendsto_weissDefect_blowup_atTop hd1 hu hmin hx₀ hR hRtop hρ hρρ')
    (fun ψ hψ f₀ hlim hacf ↦ by
      obtain ⟨-, z, -, hz⟩ := hhopf (fun k ↦ R (ψ k)) f₀ (fun k ↦ hR _) hlim
      refine ⟨⟨z, hc₀.trans_le hz⟩, ?_⟩
      have hge : acfPhi (fun y ↦ max (u y) 0) (fun y ↦ max (-u y) 0) x₀ 1 ≤
          acfPhi (fun y ↦ max (f₀ y) 0) (fun y ↦ max (-f₀ y) 0) 0 1 :=
        ge_of_tendsto hacf (Eventually.of_forall fun k ↦
          hmono (mem_Ioi.2 one_pos) (mem_Ioi.2 (hR _)) (hR1 _))
      by_contra hnn
      push Not at hnn
      have hzero : (fun y ↦ max (-f₀ y) 0) = fun _ ↦ 0 :=
        funext fun y ↦ max_eq_right (neg_nonpos.2 (hnn y))
      rw [hzero] at hge
      have : acfPhi (fun y ↦ max (f₀ y) 0) (fun _ : E d ↦ (0 : ℝ)) 0 1 = 0 := by
        simp [acfPhi, acfIntegral]
      linarith)
  have hW₁' : W₁ = volume.real (ball (0 : E d) 1) / 2 :=
    tendsto_nhds_unique (hW₁.comp (hRtop.comp hψ.tendsto_atTop)) hWdown
  -- Step 5: rigidity
  have hD0 := hrig (hW₀'.trans hW₁'.symm)
  set v : E d → ℝ := blowup u x₀ 1 with hvdef
  have hvx : ∀ x, v x = u (x₀ + x) := fun x ↦ by simp [hvdef, blowup]
  have hv : LipschitzWith L v := lipschitzWith_blowup hu x₀ one_pos
  have hv0 : v 0 = 0 := by simp [hvx, hx₀]
  have hvD : ∀ ρ ρ' : ℝ, 0 < ρ → ρ < ρ' → weissDefect v 0 ρ ρ' = 0 := fun ρ ρ' hρ hρρ' ↦ by
    rw [hvdef, weissDefect_blowup u x₀ one_pos, one_mul, one_mul]
    exact hD0 ρ ρ' hρ hρρ'
  have hvhom := homogeneous_of_ae_inner_gradient_eq hv
    (ae_inner_gradient_eq_of_weissDefect_eq_zero hv hv0 hvD)
  obtain ⟨xp, hxp⟩ := hpos
  obtain ⟨e, a, b, he, ha, hb, hvtp⟩ := homogeneousTwoPhaseIn d v L hv hvhom
    (harmonicOnNhd_blowup_posSet (hmin.harmonicOnNhd_posSet hu) x₀ one_pos)
    (harmonicOnNhd_blowup_negSet (hmin.harmonicOnNhd_negSet hu) x₀ one_pos)
    ⟨xp - x₀, by rw [hvx, add_sub_cancel]; exact hxp⟩
    ⟨xn - x₀, by rw [hvx, add_sub_cancel]; exact hxn⟩
  have hux : ∀ x, u x = twoPlane a b e (-inner ℝ x₀ e) x := fun x ↦ by
    have h := hvtp (x - x₀)
    rw [hvx, add_sub_cancel] at h
    rw [h]
    unfold twoPlane
    rw [inner_sub_left, add_zero, ← sub_eq_add_neg]
  -- Step 6: the free boundary condition
  have hab : a ^ 2 - b ^ 2 = 1 := by
    have hfun : u = twoPlane a b e (-inner ℝ x₀ e) := funext hux
    rw [hfun] at hmin
    exact sq_sub_sq_eq_one_of_isLocalEnergyMinimizer_twoPlane he ha hb hmin
  exact ⟨e, -inner ℝ x₀ e, a, b, he, ha, hb, hab, hux⟩

/-- `TwoPhaseClassificationStatement` is `TwoPhaseClassificationIn d` for every `d`. -/
public theorem twoPhaseClassificationStatement_iff :
    TwoPhaseClassificationStatement ↔ ∀ d, TwoPhaseClassificationIn d :=
  ⟨fun h _ _ _ hu hmin hpos hneg ↦ h hu hmin hpos hneg,
    fun h _ _ _ hu hmin hpos hneg ↦ h _ hu hmin hpos hneg⟩

/-- **Classification of global two-phase minimizers in dimension one**, as
`TwoPhaseClassificationIn 1`. -/
public theorem twoPhaseClassificationIn_one : TwoPhaseClassificationIn 1 :=
  fun hu hmin hpos hneg ↦ twoPhaseClassification_one hu hmin hpos hneg

/-- **Classification of global two-phase minimizers, given the Friedland–Hayman inequality in
every dimension `d ≥ 2`.** In dimension `0` no function changes sign, dimension `1` is
`twoPhaseClassificationIn_one`, and `d ≥ 2` is `twoPhaseClassification_of_friedlandHayman`. -/
public theorem twoPhaseClassification_of_forall_friedlandHayman
    (hFH : ∀ d, 2 ≤ d → FriedlandHaymanIn d) : TwoPhaseClassificationStatement := by
  refine twoPhaseClassificationStatement_iff.2 fun d ↦ ?_
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · intro u L _ _ hpos hneg
      obtain ⟨x, hx⟩ := hpos
      obtain ⟨y, hy⟩ := hneg
      rw [Subsingleton.elim x y] at hx
      exact absurd hx (not_lt.2 hy.le)
    · exact twoPhaseClassificationIn_one
  · exact twoPhaseClassification_of_friedlandHayman hd (hFH d hd)

end EllipticBernoulli
