/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
import EllipticBernoulli.Sobolev.Lattice
import EllipticBernoulli.Sobolev.Energy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Scaling invariance of local energy minimizers

`IsLocalEnergyMinimizer.rescale`: if `u` is a local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` in
an open `U`, then for `r > 0` the rescaling `x ↦ u(y + r x)/r` is a local minimizer in
`{x | y + r x ∈ U}`.

Write `A x = y + r x`. Then `map A volume = r^{-d} volume`. Integrals, lower integrals and `L^p`
membership transform accordingly. Weak gradients transform as `G ↦ G ∘ A`, energies scale by
`r^{-d}`, and competitors correspond under the inverse map `z ↦ r v((z - y)/r)`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ContDiff

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The affine map `x ↦ y + r x` as a homeomorphism (`r ≠ 0`). -/
private noncomputable def affineHom (y : E d) {r : ℝ} (hr : r ≠ 0) : E d ≃ₜ E d :=
  (Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addLeft y)

private theorem affineHom_apply (y : E d) {r : ℝ} (hr : r ≠ 0) (x : E d) :
    affineHom y hr x = y + r • x := rfl

theorem map_affine_volume (y : E d) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun x : E d ↦ y + r • x) volume =
      ENNReal.ofReal ((r ^ d)⁻¹) • (volume : Measure (E d)) := by
  have h1 : (fun x : E d ↦ y + r • x) = (fun z ↦ y + z) ∘ (fun x ↦ r • x) := rfl
  rw [h1, ← Measure.map_map (measurable_const_add y) (measurable_const_smul r),
    Measure.map_addHaar_smul _ hr.ne', Measure.map_smul, map_add_left_eq_self,
    finrank_euclideanSpace_fin, abs_of_pos (by positivity)]
  exact (measurable_const_add y).aemeasurable

private theorem measurableEmbedding_affine (y : E d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (fun x : E d ↦ y + r • x) :=
  (affineHom y hr.ne').measurableEmbedding

/-- The restricted pushforward: `map A (vol|_{A⁻¹ T}) = r^{-d} vol|_T`. -/
theorem map_affine_restrict (y : E d) {r : ℝ} (hr : 0 < r) (T : Set (E d)) :
    Measure.map (fun x : E d ↦ y + r • x) (volume.restrict ((fun x ↦ y + r • x) ⁻¹' T)) =
      ENNReal.ofReal ((r ^ d)⁻¹) • volume.restrict T := by
  rw [← (measurableEmbedding_affine y hr).restrict_map, map_affine_volume y hr,
    Measure.restrict_smul]

/-- Lower integrals over preimages. -/
theorem setLIntegral_comp_affine (y : E d) {r : ℝ} (hr : 0 < r) (T : Set (E d))
    (g : E d → ℝ≥0∞) :
    ∫⁻ x in (fun x ↦ y + r • x) ⁻¹' T, g (y + r • x) =
      ENNReal.ofReal ((r ^ d)⁻¹) * ∫⁻ z in T, g z := by
  rw [← smul_eq_mul, ← lintegral_smul_measure, ← map_affine_restrict y hr T,
    (measurableEmbedding_affine y hr).lintegral_map]

/-- Integrals. -/
theorem integral_comp_affine (y : E d) {r : ℝ} (hr : 0 < r) (g : E d → ℝ) :
    ∫ x, g (y + r • x) = (r ^ d)⁻¹ * ∫ z, g z := by
  have := (measurableEmbedding_affine y hr).integral_map (μ := volume) g
  rw [map_affine_volume y hr, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul] at this
  exact this.symm

/-- `L^p` membership transfers along `A` on preimages. -/
theorem MemLp.comp_affine {p : ℝ≥0∞} {F : Type*} [NormedAddCommGroup F] {g : E d → F}
    (y : E d) {r : ℝ} (hr : 0 < r) {T : Set (E d)} (hg : MemLp g p (volume.restrict T)) :
    MemLp (fun x ↦ g (y + r • x)) p (volume.restrict ((fun x ↦ y + r • x) ⁻¹' T)) := by
  have hc : ENNReal.ofReal ((r ^ d)⁻¹) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : MemLp g p (ENNReal.ofReal ((r ^ d)⁻¹) • volume.restrict T) := hg.smul_measure hc
  rw [← map_affine_restrict y hr T] at h1
  exact (memLp_map_measure_iff h1.aestronglyMeasurable
    ((measurableEmbedding_affine y hr).measurable.aemeasurable)).1 h1

private theorem affine_inv_apply (y : E d) {r : ℝ} (hr : 0 < r) (x : E d) :
    (affineHom y hr.ne').symm x = r⁻¹ • (x - y) := by
  apply (affineHom y hr.ne').injective
  rw [Homeomorph.apply_symm_apply, affineHom_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
    add_sub_cancel]

/-- **`H¹_loc` under `x ↦ y + r x`.** If `f ∈ H¹_loc(U)` with weak gradient `G`, then
`x ↦ f(y + r x)/r ∈ H¹_loc({x | y + r x ∈ U})` with weak gradient `x ↦ G(y + r x)`. -/
theorem MemH1Loc.comp_affine {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ} {G : E d → E d}
    (hf : MemH1Loc U f G) (y : E d) {r : ℝ} (hr : 0 < r) :
    MemH1Loc ((fun x ↦ y + r • x) ⁻¹' U) (fun x ↦ f (y + r • x) / r)
      (fun x ↦ G (y + r • x)) := by
  set h := affineHom y hr.ne' with hh
  set V := (fun x : E d ↦ y + r • x) ⁻¹' U with hV
  have hVo : IsOpen V := hU.preimage (by fun_prop)
  have hL2 : ∀ K ⊆ V, IsCompact K → MemLp (fun x ↦ f (y + r • x) / r) 2 (volume.restrict K) ∧
      MemLp (fun x ↦ G (y + r • x)) 2 (volume.restrict K) := by
    intro K hKV hK
    have hK' : IsCompact (h '' K) := hK.image h.continuous
    have hK'U : h '' K ⊆ U := by rintro _ ⟨x, hx, rfl⟩; exact hKV hx
    have hpre : (fun x : E d ↦ y + r • x) ⁻¹' (h '' K) = K := by
      ext x; constructor
      · rintro ⟨x', hx', hxx⟩
        rw [← h.injective (show h x' = h x from hxx)]; exact hx'
      · intro hx; exact ⟨x, hx, rfl⟩
    obtain ⟨h1, h2⟩ := hf.2 _ hK'U hK'
    have e1 := EllipticBernoulli.MemLp.comp_affine y hr h1
    have e2 := EllipticBernoulli.MemLp.comp_affine y hr h2
    rw [hpre] at e1
    rw [hpre] at e2
    refine ⟨?_, e2⟩
    have := MeasureTheory.MemLp.mul_const e1 r⁻¹
    simpa [div_eq_mul_inv] using this
  have hint : ∀ {F : Type _} [NormedAddCommGroup F] {g : E d → F},
      (∀ K ⊆ V, IsCompact K → MemLp g 2 (volume.restrict K)) → LocallyIntegrableOn g V := by
    intro F _ g hg
    refine (locallyIntegrableOn_iff hVo.isLocallyClosed).2 fun K hKV hK ↦ ?_
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact (hg K hKV hK).integrable one_le_two
  refine ⟨HasWeakGradient.of_integral_eq (hint fun K hKV hK ↦ (hL2 K hKV hK).1)
    (hint fun K hKV hK ↦ (hL2 K hKV hK).2) fun φ hφ hφc hφV v ↦ ?_, hL2⟩
  -- the transported test function `ψ = φ ∘ A⁻¹`
  set ψ : E d → ℝ := φ ∘ h.symm with hψ
  have hsymm : ∀ z, h.symm z = r⁻¹ • (z - y) := affine_inv_apply y hr
  have hψs : ContDiff ℝ ∞ ψ := by
    have : ψ = fun z ↦ φ (r⁻¹ • (z - y)) := by funext z; simp [hψ, hsymm]
    rw [this]; exact hφ.comp ((contDiff_id.sub contDiff_const).const_smul _)
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph h.symm
  have hψU : tsupport ψ ⊆ U := by
    have hsupp : Function.support ψ = h '' Function.support φ := by
      ext z
      simp only [Function.mem_support, hψ, Function.comp_apply, mem_image]
      constructor
      · intro hz; exact ⟨h.symm z, hz, h.apply_symm_apply z⟩
      · rintro ⟨x, hx, rfl⟩; rwa [h.symm_apply_apply]
    rw [tsupport, hsupp, ← h.image_closure]
    rintro _ ⟨x, hx, rfl⟩
    exact hφV hx
  have hφψ : ∀ x, φ x = ψ (y + r • x) := fun x ↦ by
    simp only [hψ, Function.comp_apply]
    rw [show y + r • x = h x from rfl, h.symm_apply_apply]
  have hfd : ∀ x, fderiv ℝ φ x v = r * fderiv ℝ ψ (y + r • x) v := fun x ↦ by
    have hA : HasFDerivAt (fun x : E d ↦ y + r • x) (r • ContinuousLinearMap.id ℝ (E d)) x :=
      ((hasFDerivAt_id x).const_smul r).const_add y
    have hψd := (hψs.differentiable (by simp) (y + r • x)).hasFDerivAt
    have hcomp := hψd.comp x hA
    have hφeq : φ = ψ ∘ fun x ↦ y + r • x := funext hφψ
    rw [hφeq, hcomp.fderiv]
    simp [smul_eq_mul]
  have hweak := hf.1.integral_eq hψs hψc hψU v
  calc ∫ x, f (y + r • x) / r * fderiv ℝ φ x v
      = ∫ x, (fun z ↦ f z * fderiv ℝ ψ z v) (y + r • x) := by
        congr 1; funext x; rw [hfd]; field_simp
    _ = (r ^ d)⁻¹ * ∫ z, f z * fderiv ℝ ψ z v :=
        integral_comp_affine y hr (fun z ↦ f z * fderiv ℝ ψ z v)
    _ = (r ^ d)⁻¹ * -∫ z, inner ℝ (G z) v * ψ z := by rw [hweak]
    _ = -((r ^ d)⁻¹ * ∫ z, inner ℝ (G z) v * ψ z) := by ring
    _ = -∫ x, (fun z ↦ inner ℝ (G z) v * ψ z) (y + r • x) := by
        rw [integral_comp_affine y hr (fun z ↦ inner ℝ (G z) v * ψ z)]
    _ = -∫ x, inner ℝ (G (y + r • x)) v * φ x := by
        congr 2; funext x; rw [hφψ]

/-- The preimage of a ball under `x ↦ y + r x`. -/
theorem preimage_affine_ball (y x₀ : E d) {r : ℝ} (hr : 0 < r) (ρ : ℝ) :
    (fun x : E d ↦ y + r • x) ⁻¹' ball (y + r • x₀) (r * ρ) = ball x₀ ρ := by
  ext x
  simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
    norm_smul, Real.norm_of_nonneg hr.le]
  exact mul_lt_mul_iff_right₀ hr

/-- **Energies under `x ↦ y + r x`.** -/
theorem energyJ_comp_affine (y x₀ : E d) {r : ℝ} (hr : 0 < r) (ρ : ℝ) (f : E d → ℝ)
    (F : E d → E d) :
    energyJ (ball x₀ ρ) (fun _ ↦ 1) (fun x ↦ f (y + r • x) / r) (fun x ↦ F (y + r • x)) =
      ENNReal.ofReal ((r ^ d)⁻¹) * energyJ (ball (y + r • x₀) (r * ρ)) (fun _ ↦ 1) f F := by
  rw [energyJ, energyJ, ← preimage_affine_ball y x₀ hr ρ, ← setLIntegral_comp_affine y hr]
  have hP : posSet (fun x ↦ f (y + r • x) / r)
      ((fun x ↦ y + r • x) ⁻¹' ball (y + r • x₀) (r * ρ)) =
      (fun x ↦ y + r • x) ⁻¹' posSet f (ball (y + r • x₀) (r * ρ)) := by
    ext x; simp only [posSet, mem_ofPred_eq, mem_preimage, div_pos_iff_of_pos_right hr]
  rw [hP]
  refine setLIntegral_congr_fun ((measurableSet_ball).preimage (by fun_prop)) fun x _ ↦ ?_
  by_cases hm : y + r • x ∈ posSet f (ball (y + r • x₀) (r * ρ))
  · rw [indicator_of_mem hm, indicator_of_mem (show x ∈ (fun x ↦ y + r • x) ⁻¹'
      posSet f (ball (y + r • x₀) (r * ρ)) from hm)]
    rfl
  · rw [indicator_of_notMem hm, indicator_of_notMem (show x ∉ (fun x ↦ y + r • x) ⁻¹'
      posSet f (ball (y + r • x₀) (r * ρ)) from hm)]

/-- A.e. statements transfer along `x ↦ y + r x`. -/
theorem ae_restrict_comp_affine (y : E d) {r : ℝ} (hr : 0 < r) (T : Set (E d))
    {p : E d → Prop} (h : ∀ᵐ x ∂(volume.restrict ((fun x ↦ y + r • x) ⁻¹' T)), p (y + r • x)) :
    ∀ᵐ z ∂(volume.restrict T), p z := by
  have hc : ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  rw [← Measure.ae_ennreal_smul_measure_iff hc, ← map_affine_restrict y hr T,
    (measurableEmbedding_affine y hr).ae_map_iff]
  exact h

/-- **Scaling invariance of local energy minimizers.** -/
theorem IsLocalEnergyMinimizer.rescale {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) (y : E d) {r : ℝ} (hr : 0 < r) :
    IsLocalEnergyMinimizer ((fun x ↦ y + r • x) ⁻¹' U) (fun _ ↦ 1)
      (fun x ↦ u (y + r • x) / r) := by
  obtain ⟨G, hG, hm⟩ := hmin
  set V := (fun x : E d ↦ y + r • x) ⁻¹' U with hV
  have hVo : IsOpen V := hU.preimage (by fun_prop)
  have hGt := hG.comp_affine hU y hr
  refine ⟨fun x ↦ G (y + r • x), hGt, fun x₀ ρ hρ hB ↦ ⟨hGt, fun _ _ ↦ rfl,
    fun _ _ ↦ mem_univ _, fun vt Gvt hvt hvout _ ↦ ?_⟩⟩
  -- the inverse map `z ↦ r⁻¹ (z - y) = (-r⁻¹ y) + r⁻¹ z`
  set y' : E d := -(r⁻¹ • y) with hy'
  have hinv : ∀ z : E d, y + r • (y' + r⁻¹ • z) = z := fun z ↦ by
    rw [hy', smul_add, smul_neg, smul_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
      one_smul]; abel
  have hinv' : ∀ x : E d, y' + r⁻¹ • (y + r • x) = x := fun x ↦ by
    rw [hy', smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]; abel
  have hpreV : (fun z : E d ↦ y' + r⁻¹ • z) ⁻¹' V = U := by
    ext z; simp only [mem_preimage, hV, hinv]
  have hv := hvt.comp_affine hVo y' (inv_pos.2 hr)
  rw [hpreV] at hv
  set v : E d → ℝ := fun z ↦ vt (y' + r⁻¹ • z) / r⁻¹ with hvdef
  set Gv : E d → E d := fun z ↦ Gvt (y' + r⁻¹ • z) with hGvdef
  -- the ball and its image
  have hBimg : closedBall (y + r • x₀) (r * ρ) ⊆ U := by
    intro z hz
    have : y' + r⁻¹ • z ∈ closedBall x₀ ρ := by
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      have : y' + r⁻¹ • z - x₀ = r⁻¹ • (z - (y + r • x₀)) := by
        rw [hy', smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]; abel
      rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
      calc r⁻¹ * ‖z - (y + r • x₀)‖ ≤ r⁻¹ * (r * ρ) := by gcongr
        _ = ρ := by field_simp
    have := hB this
    rwa [hV, mem_preimage, hinv] at this
  have hpreB : (fun x : E d ↦ y + r • x) ⁻¹' (U \ ball (y + r • x₀) (r * ρ)) =
      V \ ball x₀ ρ := by
    rw [preimage_sdiff, preimage_affine_ball y x₀ hr ρ]
  -- `v = u` off the image ball
  have hvout' : ∀ᵐ z ∂(volume.restrict (U \ ball (y + r • x₀) (r * ρ))), v z = u z := by
    refine ae_restrict_comp_affine y hr _ (p := fun z ↦ v z = u z) ?_
    rw [hpreB]
    filter_upwards [hvout] with x hx
    simp only [hvdef, hinv', div_inv_eq_mul]
    rw [hx]; field_simp
  have hle := (hm (y + r • x₀) (r * ρ) (by positivity) hBimg).2.2.2 v Gv hv hvout'
    (ae_of_all _ fun _ ↦ mem_univ _)
  -- transport the energies back
  have e1 := energyJ_comp_affine y x₀ hr ρ u G
  have e2 := energyJ_comp_affine y x₀ hr ρ v Gv
  have hvt' : (fun x ↦ v (y + r • x) / r) = vt := by
    funext x; simp only [hvdef, hinv', div_inv_eq_mul]; field_simp
  have hGvt' : (fun x ↦ Gv (y + r • x)) = Gvt := by
    funext x; simp only [hGvdef, hinv']
  rw [hvt', hGvt'] at e2
  rw [e1, e2]
  gcongr

end EllipticBernoulli
