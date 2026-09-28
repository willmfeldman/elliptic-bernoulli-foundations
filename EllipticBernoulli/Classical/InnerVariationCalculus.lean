/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Setting
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import EllipticBernoulli.Viscosity.Calculus

/-!
# Calculus helpers for the inner-variation identity

Generic tools used by `Classical/InnerVariationCore.lean`:

* `integral_divergence_eq_zero`: `∫ div W = 0` for a Lipschitz, compactly supported field `W`
  (componentwise, from Mathlib's `LipschitzWith.integral_lineDeriv_mul_eq` against the constant
  function `1`).
* `lipschitzWith_of_locallyLipschitz_of_hasCompactSupport`: a locally Lipschitz function with
  compact support is Lipschitz.
* `LipAt` (Lipschitz on a neighbourhood of a point) and its closure properties.
* `gradCLM`: the Riesz map `(E d)* → E d` as a real continuous linear map, so that
  `∇u = gradCLM ∘ Du` can be differentiated; `inner_fderiv_gradient`,
  `trace_fderiv_gradient` (`tr D(∇u) = Δu`).
* `cutη`: the smooth monotone cut-off `s ↦ smoothTransition (2 s - 1)`.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient Laplacian RealInnerProductSpace NNReal ContDiff

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The divergence theorem for Lipschitz fields -/

/-- `∫ div W = 0` for a Lipschitz, compactly supported vector field `W` on `ℝᵈ`. -/
theorem integral_divergence_eq_zero {W : E d → E d} {C : ℝ≥0} (hW : LipschitzWith C W)
    (hWc : HasCompactSupport W) : ∫ x, divergence W x = 0 := by
  set b := stdOrthonormalBasis ℝ (E d)
  set g : _ → E d → ℝ := fun i y ↦ ⟪b i, W y⟫ with hg
  have hgL : ∀ i, LipschitzWith (‖innerSL ℝ (b i)‖₊ * C) (g i) := fun i ↦
    (innerSL ℝ (b i)).lipschitz.comp hW
  have hgc : ∀ i, HasCompactSupport (g i) := fun i ↦ hWc.comp_left (g := fun v ↦ ⟪b i, v⟫)
    (by simp)
  have hdiv : (fun x ↦ divergence W x) =ᵐ[volume] fun x ↦ ∑ i, fderiv ℝ (g i) x (b i) := by
    filter_upwards [hW.ae_differentiableAt] with x hx
    rw [divergence, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := ((innerSL ℝ (b i)).hasFDerivAt.comp x hx.hasFDerivAt).fderiv
    change ⟪b i, fderiv ℝ W x (b i)⟫ = fderiv ℝ ((innerSL ℝ (b i)) ∘ W) x (b i)
    rw [h]
    rfl
  have hint : ∀ i, Integrable (fun x ↦ fderiv ℝ (g i) x (b i)) := by
    intro i
    have hK := (hgc i).isCompact
    have hon : IntegrableOn (fun x ↦ fderiv ℝ (g i) x (b i)) (tsupport (g i)) :=
      Measure.integrableOn_of_bounded (M := (‖innerSL ℝ (b i)‖₊ * C : ℝ≥0) * ‖b i‖)
        hK.measure_lt_top.ne (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
        (Eventually.of_forall fun x ↦ ((fderiv ℝ (g i) x).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hgL i)) (norm_nonneg _)))
    have := hon.of_forall_diff_eq_zero MeasurableSet.univ fun x hx ↦ by
      rw [fderiv_of_notMem_tsupport ℝ hx.2]; rfl
    exact integrableOn_univ.1 this
  rw [integral_congr_ae hdiv, integral_finsetSum _ fun i _ ↦ hint i]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h1 := LipschitzWith.integral_lineDeriv_mul_eq (μ := volume)
    (LipschitzWith.const (1 : ℝ)) (hgL i) (hgc i) (-(b i))
  have h0 : ∀ x, lineDeriv ℝ (fun _ : E d ↦ (1 : ℝ)) x (-(b i)) = 0 := fun x ↦ by
    simp [lineDeriv]
  simp only [h0, zero_mul, integral_zero, neg_neg, mul_one] at h1
  rw [h1]
  refine integral_congr_ae ?_
  filter_upwards [(hgL i).ae_differentiableAt] with x hx
  exact hx.lineDeriv_eq_fderiv.symm

/-! ### Locally Lipschitz fields with compact support -/

/-- A locally Lipschitz function with compact support on `ℝᵈ` is Lipschitz. -/
theorem lipschitzWith_of_locallyLipschitz_of_hasCompactSupport {F : Type*}
    [NormedAddCommGroup F] {W : E d → F} (hW : LocallyLipschitz W) (hWc : HasCompactSupport W) :
    ∃ K, LipschitzWith K W := by
  set T := tsupport W
  set S := cthickening 1 T
  have hS : IsCompact S := hWc.isCompact.cthickening
  have hTS : T ⊆ S := self_subset_cthickening T
  obtain ⟨K, hK⟩ := (hW.locallyLipschitzOn (s := S)).exists_lipschitzOnWith_of_compact hS
  obtain ⟨M₀, hM₀⟩ := hS.exists_bound_of_continuousOn hW.continuous.continuousOn
  set M := max M₀ 0
  have hM : ∀ x ∈ S, ‖W x‖ ≤ M := fun x hx ↦ (hM₀ x hx).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hfar : ∀ x y, x ∈ T → y ∉ S → dist (W x) (W y) ≤ M * dist x y := by
    intro x y hx hy
    have hy0 : W y = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hy (hTS h)
    have h1 : 1 ≤ dist x y := by
      by_contra h
      exact hy (mem_cthickening_of_dist_le y x 1 T hx (by rw [dist_comm]; linarith))
    rw [hy0, dist_zero_right]
    calc ‖W x‖ ≤ M := hM x (hTS hx)
      _ = M * 1 := (mul_one M).symm
      _ ≤ M * dist x y := mul_le_mul_of_nonneg_left h1 hM0
  refine ⟨K + M.toNNReal, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  have hKM : ∀ r : ℝ, 0 ≤ r → (K : ℝ) * r ≤ ((K + M.toNNReal : ℝ≥0) : ℝ) * r := fun r hr ↦
    mul_le_mul_of_nonneg_right (by simp) hr
  have hMK : ∀ r : ℝ, 0 ≤ r → M * r ≤ ((K + M.toNNReal : ℝ≥0) : ℝ) * r := fun r hr ↦
    mul_le_mul_of_nonneg_right (by simp [Real.coe_toNNReal _ hM0]) hr
  by_cases hxS : x ∈ S <;> by_cases hyS : y ∈ S
  · exact (hK.dist_le_mul x hxS y hyS).trans (hKM _ dist_nonneg)
  · by_cases hxT : x ∈ T
    · exact (hfar x y hxT hyS).trans (hMK _ dist_nonneg)
    · rw [image_eq_zero_of_notMem_tsupport hxT,
        image_eq_zero_of_notMem_tsupport fun h ↦ hyS (hTS h), dist_self]
      positivity
  · by_cases hyT : y ∈ T
    · rw [dist_comm, dist_comm x]; exact (hfar y x hyT hxS).trans (hMK _ dist_nonneg)
    · rw [image_eq_zero_of_notMem_tsupport hyT,
        image_eq_zero_of_notMem_tsupport fun h ↦ hxS (hTS h), dist_self]
      positivity
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hxS (hTS h),
      image_eq_zero_of_notMem_tsupport fun h ↦ hyS (hTS h), dist_self]
    positivity

/-- Lipschitz on a neighbourhood of `x` is preserved by pairing. -/
theorem lipAt_prodMk {F G : Type*} [PseudoEMetricSpace F] [PseudoEMetricSpace G]
    {f : E d → F} {g : E d → G} {x : E d} (hf : ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t)
    (hg : ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K g t) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K (fun y ↦ (f y, g y)) t := by
  obtain ⟨K₁, t₁, ht₁, h₁⟩ := hf
  obtain ⟨K₂, t₂, ht₂, h₂⟩ := hg
  exact ⟨_, t₁ ∩ t₂, inter_mem ht₁ ht₂,
    (h₁.mono inter_subset_left).prodMk (h₂.mono inter_subset_right)⟩

/-- Lipschitz on a neighbourhood of `x` is preserved by post-composition with a `C¹` map. -/
theorem lipAt_comp_contDiff {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G} (hg : ContDiff ℝ 1 g) {f : E d → F}
    {x : E d} (hf : ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K (fun y ↦ g (f y)) t := by
  obtain ⟨K, t, ht, h⟩ := hf
  obtain ⟨K', t', ht', h'⟩ := hg.locallyLipschitz (f x)
  have hc : ContinuousAt f x := (h.continuousOn).continuousAt ht
  refine ⟨K' * K, t ∩ f ⁻¹' t', inter_mem ht (hc.preimage_mem_nhds ht'), ?_⟩
  exact h'.comp (h.mono inter_subset_left) fun y hy ↦ hy.2

/-- A function eventually equal to one that is Lipschitz near `x` is Lipschitz near `x`. -/
theorem lipAt_congr {F : Type*} [PseudoEMetricSpace F] {f g : E d → F} {x : E d}
    (hfg : f =ᶠ[𝓝 x] g) (hg : ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K g t) :
    ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t := by
  obtain ⟨K, t, ht, h⟩ := hg
  refine ⟨K, t ∩ {y | f y = g y}, inter_mem ht hfg, fun y hy z hz ↦ ?_⟩
  rw [hy.2, hz.2]
  exact h hy.1 hz.1

/-! ### The gradient as a differentiable map -/

/-- The Riesz map `(E d)* → E d` as a real continuous linear map. -/
private noncomputable def gradCLM : StrongDual ℝ (E d) →L[ℝ] E d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun L ↦ (toDual ℝ (E d)).symm L
      map_add' := fun a b ↦ by simp
      map_smul' := fun c L ↦ by simp }

private theorem gradient_eq_gradCLM (u : E d → ℝ) : ∇ u = fun y ↦ gradCLM (fderiv ℝ u y) := rfl

private theorem hasFDerivAt_gradient {u : E d → ℝ} {x : E d}
    (h : DifferentiableAt ℝ (fderiv ℝ u) x) :
    HasFDerivAt (∇ u) (gradCLM.comp (fderiv ℝ (fderiv ℝ u) x)) x := by
  rw [gradient_eq_gradCLM]
  exact gradCLM.hasFDerivAt.comp x h.hasFDerivAt

theorem differentiableAt_gradient {u : E d → ℝ} {x : E d}
    (h : DifferentiableAt ℝ (fderiv ℝ u) x) : DifferentiableAt ℝ (∇ u) x :=
  (hasFDerivAt_gradient h).differentiableAt

/-- `⟪D(∇u)(x) v, w⟫ = D²u(x)(v, w)`. -/
theorem inner_fderiv_gradient {u : E d → ℝ} {x : E d} (h : DifferentiableAt ℝ (fderiv ℝ u) x)
    (v w : E d) : ⟪fderiv ℝ (∇ u) x v, w⟫ = fderiv ℝ (fderiv ℝ u) x v w := by
  rw [(hasFDerivAt_gradient h).fderiv]
  change ⟪(toDual ℝ (E d)).symm (fderiv ℝ (fderiv ℝ u) x v), w⟫ = _
  rw [toDual_symm_apply]

/-- `tr D(∇u)(x) = Δu(x)`. -/
theorem trace_fderiv_gradient {u : E d → ℝ} {x : E d} (h : DifferentiableAt ℝ (fderiv ℝ u) x) :
    LinearMap.trace ℝ (E d) (fderiv ℝ (∇ u) x).toLinearMap = Δ u x := by
  rw [laplacian_eq_sum_fderiv_fderiv, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (E d))]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [real_inner_comm]
  exact inner_fderiv_gradient h _ _

/-- `C^{n+1}` at `x` gives a `C^n` gradient at `x`. -/
theorem contDiffAt_gradient {u : E d → ℝ} {x : E d} {n : ℕ∞} (h : ContDiffAt ℝ (n + 1) u x) :
    ContDiffAt ℝ n (∇ u) x := by
  rw [gradient_eq_gradCLM]
  exact gradCLM.contDiff.contDiffAt.comp x (h.fderiv_right le_rfl)

/-! ### Divergence of products -/

/-- `div (a V) = a div V + Da(V)`. -/
theorem divergence_smul {a : E d → ℝ} {V : E d → E d} {x : E d} (ha : DifferentiableAt ℝ a x)
    (hV : DifferentiableAt ℝ V x) :
    divergence (fun y ↦ a y • V y) x = a x * divergence V x + fderiv ℝ a x (V x) := by
  rw [divergence, fderiv_fun_smul ha hV, ContinuousLinearMap.coe_add, map_add,
    ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul, divergence]
  congr 1
  have : ((fderiv ℝ a x).smulRight (V x) : E d →ₗ[ℝ] E d) =
      (fderiv ℝ a x : E d →ₗ[ℝ] ℝ).smulRight (V x) := rfl
  rw [this, LinearMap.trace_smulRight]
  rfl

/-- `div (V - W) = div V - div W`. -/
theorem divergence_sub {V W : E d → E d} {x : E d} (hV : DifferentiableAt ℝ V x)
    (hW : DifferentiableAt ℝ W x) :
    divergence (fun y ↦ V y - W y) x = divergence V x - divergence W x := by
  rw [divergence, fderiv_fun_sub hV hW, ContinuousLinearMap.coe_sub, map_sub]
  rfl

/-- `div ∇u = Δu`. -/
theorem divergence_gradient {u : E d → ℝ} {x : E d} (h : DifferentiableAt ℝ (fderiv ℝ u) x) :
    divergence (∇ u) x = Δ u x :=
  trace_fderiv_gradient h

/-! ### The cut-off `η` -/

/-- The smooth monotone cut-off `η(s) = smoothTransition (2 s - 1)`: `0` for `s ≤ 1/2`, `1` for
`s ≥ 1`. -/
noncomputable def cutη (s : ℝ) : ℝ := Real.smoothTransition (2 * s - 1)

theorem contDiff_cutη : ContDiff ℝ ∞ cutη :=
  Real.smoothTransition.contDiff.comp (by fun_prop)

theorem cutη_eq_zero {s : ℝ} (hs : s ≤ 1 / 2) : cutη s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutη_eq_one {s : ℝ} (hs : 1 ≤ s) : cutη s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutη_nonneg (s : ℝ) : 0 ≤ cutη s := Real.smoothTransition.nonneg _

theorem cutη_le_one (s : ℝ) : cutη s ≤ 1 := Real.smoothTransition.le_one _

theorem monotone_cutη : Monotone cutη := fun a b hab ↦
  Real.smoothTransition.monotone (by linarith)

theorem deriv_cutη_nonneg (s : ℝ) : 0 ≤ deriv cutη s := monotone_cutη.deriv_nonneg

theorem continuous_deriv_cutη : Continuous (deriv cutη) :=
  contDiff_cutη.continuous_deriv (by simp)

/-- `η' = 0` off `[1/2, 1]`. -/
theorem deriv_cutη_eq_zero {s : ℝ} (hs : s < 1 / 2 ∨ 1 < s) : deriv cutη s = 0 := by
  rcases hs with hs | hs
  · have : cutη =ᶠ[𝓝 s] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hs] with t ht using cutη_eq_zero (le_of_lt ht)
    rw [this.deriv_eq, deriv_const]
  · have : cutη =ᶠ[𝓝 s] fun _ ↦ 1 := by
      filter_upwards [Ioi_mem_nhds hs] with t ht using cutη_eq_one (le_of_lt ht)
    rw [this.deriv_eq, deriv_const]

/-! ### The cut-off divergence identity -/

/-- **Cut-off divergence identity.** Let `u` be continuous and nonnegative on the open set `U`
and `C¹` on `Ω = {u > 0} ∩ U`, and let `V` be compactly supported in `U`, Lipschitz near every
point of `Ω` and differentiable a.e. on `Ω`. Then, for `ε > 0`,
`∫_Ω (η(u/ε) div V + η'(u/ε) ε⁻¹ ⟪∇u, V⟫) = 0`: this is `∫ div (η(u/ε) V) = 0`, the field
`η(u/ε) V` being Lipschitz with compact support in `Ω`. -/
theorem integral_cutoff_divergence_eq_zero {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hucont : ContinuousOn u U) (hunn : ∀ x ∈ U, 0 ≤ u x) (hu1 : ContDiffOn ℝ 1 u (posSet u U))
    {V : E d → E d} (hVc : HasCompactSupport V) (hVU : tsupport V ⊆ U)
    (hVlip : ∀ x ∈ posSet u U, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K V t)
    (hVd : ∀ᵐ x, x ∈ posSet u U → DifferentiableAt ℝ V x) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in posSet u U, (cutη (u x / ε) * divergence V x +
      deriv cutη (u x / ε) / ε * ⟪∇ u x, V x⟫) = 0 := by
  set Ω := posSet u U with hΩdef
  have hΩ : IsOpen Ω := hucont.isOpen_inter_preimage hU isOpen_Ioi
  set a : E d → ℝ := fun y ↦ cutη (u y / ε) with ha_def
  set W : E d → E d := fun y ↦ a y • V y with hW_def
  have haC : ∀ x ∈ Ω, ContDiffAt ℝ 1 a x := fun x hx ↦
    (contDiff_cutη.of_le (by simp)).contDiffAt.comp x
      (((hu1.contDiffAt (hΩ.mem_nhds hx))).div_const ε)
  -- `W` vanishes near every point outside `Ω`
  have hWzero : ∀ x ∉ Ω, W =ᶠ[𝓝 x] fun _ ↦ 0 := by
    intro x hx
    by_cases hxU : x ∈ U
    · have hux : u x = 0 := le_antisymm (not_lt.1 fun h ↦ hx ⟨hxU, h⟩) (hunn x hxU)
      have hc : ContinuousAt u x := hucont.continuousAt (hU.mem_nhds hxU)
      have hev : ∀ᶠ y in 𝓝 x, u y < ε / 2 := hc.eventually (gt_mem_nhds (by rw [hux]; linarith))
      filter_upwards [hev] with y hy
      have : a y = 0 := cutη_eq_zero (by rw [div_le_iff₀ hε]; linarith)
      simp [hW_def, this]
    · have hxV : x ∉ tsupport V := fun h ↦ hxU (hVU h)
      rw [notMem_tsupport_iff_eventuallyEq] at hxV
      filter_upwards [hxV] with y hy
      simp [hW_def, hy]
  -- `W` is Lipschitz with compact support
  have hWloc : ∀ x, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K W t := by
    intro x
    by_cases hx : x ∈ Ω
    · have h1 := lipAt_prodMk ((haC x hx).exists_lipschitzOnWith) (hVlip x hx)
      have h2 := lipAt_comp_contDiff (g := fun p : ℝ × E d ↦ p.1 • p.2)
        (contDiff_fst.smul contDiff_snd) h1
      exact h2
    · exact lipAt_congr (hWzero x hx) ⟨0, univ, univ_mem, (LipschitzWith.const _).lipschitzOnWith⟩
  have hWc : HasCompactSupport W := hVc.smul_left (f := a)
  obtain ⟨K, hK⟩ := lipschitzWith_of_locallyLipschitz_of_hasCompactSupport hWloc hWc
  have hint := integral_divergence_eq_zero hK hWc
  -- the divergence of `W`
  have hdiv0 : ∀ x ∉ Ω, divergence W x = 0 := fun x hx ↦ by
    rw [divergence, (hWzero x hx).fderiv_eq]
    simp
  have hdivΩ : ∀ᵐ x, x ∈ Ω → cutη (u x / ε) * divergence V x +
      deriv cutη (u x / ε) / ε * ⟪∇ u x, V x⟫ = divergence W x := by
    filter_upwards [hVd] with x hVx hx
    have hud : DifferentiableAt ℝ u x :=
      (hu1.contDiffAt (hΩ.mem_nhds hx)).differentiableAt one_ne_zero
    have had : HasFDerivAt a (deriv cutη (u x / ε) • (ε⁻¹ • fderiv ℝ u x)) x := by
      have h1 : HasFDerivAt (fun y ↦ u y / ε) (ε⁻¹ • fderiv ℝ u x) x := by
        have := hud.hasFDerivAt.const_smul ε⁻¹
        convert this using 1
        funext y; simp [div_eq_inv_mul]
      exact (contDiff_cutη.differentiable (by simp) _).hasDerivAt.comp_hasFDerivAt x h1
    rw [hW_def, divergence_smul had.differentiableAt (hVx hx), had.fderiv]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ha_def]
    rw [fderiv_apply_eq_inner_gradient]
    ring
  rw [setIntegral_congr_ae hΩ.measurableSet hdivΩ,
    setIntegral_eq_integral_of_forall_compl_eq_zero hdiv0, hint]

end EllipticBernoulli
