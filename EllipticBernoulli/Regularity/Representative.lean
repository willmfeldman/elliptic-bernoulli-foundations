/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Regularity.InteriorOscillation
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.Analysis.Convex.Integral

/-!
# The continuous representative

`ballLimit f x = lim_{s → 0⁺} ⨍_{B̄_s(x)} f`. On an open set `W` on which `f` is integrable and
its essential oscillation vanishes at every point (`EssOscVanishes`, from the De Giorgi
iteration):

* `tendsto_ballLimit`: the limit exists;
* `ballLimit_mem`: if `f ∈ S` a.e. near `x`, `S` closed and convex, then `ballLimit f x ∈ S`;
* `continuousOn_ballLimit`: `ballLimit f` is continuous on `W`;
* `ballLimit_ae_eq`: `ballLimit f = f` a.e. on `W` (Lebesgue differentiation,
  `IsUnifLocDoublingMeasure.ae_tendsto_average`; this part needs no oscillation hypothesis).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The limit of the averages of `f` over the closed balls `B̄_s(x)`, `s → 0⁺`. -/
def ballLimit (f : E d → ℝ) (x : E d) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun s ↦ ⨍ z in closedBall x s, f z

/-- An average over a closed ball of a function with values a.e. in a closed convex set lies in
that set. -/
theorem average_closedBall_mem {f : E d → ℝ} {x : E d} {s : ℝ} (hs : 0 < s)
    (hf : IntegrableOn f (closedBall x s)) {S : Set ℝ} (hS : Convex ℝ S) (hSc : IsClosed S)
    (h : ∀ᵐ z ∂(volume.restrict (closedBall x s)), f z ∈ S) :
    ⨍ z in closedBall x s, f z ∈ S :=
  hS.set_average_mem hSc (measure_closedBall_pos volume x hs).ne' measure_closedBall_lt_top.ne
    h hf

/-- If `f ∈ S` a.e. on a neighbourhood `W` of `x`, then eventually (as `s → 0⁺`) the average of
`f` over `B̄_s(x)` lies in `S`. -/
theorem eventually_average_mem {f : E d → ℝ} {x : E d} {W : Set (E d)} (hW : W ∈ 𝓝 x)
    (hf : IntegrableOn f W) {S : Set ℝ} (hS : Convex ℝ S) (hSc : IsClosed S)
    (h : ∀ᵐ z ∂(volume.restrict W), f z ∈ S) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), ⨍ z in closedBall x s, f z ∈ S := by
  obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.1 hW
  filter_upwards [Ioo_mem_nhdsGT hε] with s hs
  have hsub : closedBall x s ⊆ W := (closedBall_subset_ball hs.2).trans hεW
  exact average_closedBall_mem hs.1 (hf.mono_set hsub) hS hSc
    (ae_restrict_of_ae_restrict_of_subset hsub h)

/-- **Existence of the limit of ball averages** where the essential oscillation vanishes. -/
theorem tendsto_ballLimit {f : E d → ℝ} {x : E d} {W : Set (E d)} (hW : W ∈ 𝓝 x)
    (hf : IntegrableOn f W) (hosc : EssOscVanishes f x) :
    Tendsto (fun s ↦ ⨍ z in closedBall x s, f z) (𝓝[>] 0) (𝓝 (ballLimit f x)) := by
  refine tendsto_nhds_limUnder ?_
  refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨map_neBot, fun ε hε ↦ ?_⟩)
  obtain ⟨ρ, hρ, m, M, hMm, hb⟩ := hosc (ε / 2) (by positivity)
  have hW' : W ∩ ball x ρ ∈ 𝓝 x := inter_mem hW (ball_mem_nhds x hρ)
  have hev := eventually_average_mem hW' (hf.mono_set inter_subset_left) (convex_Icc m M)
    isClosed_Icc (ae_restrict_of_ae_restrict_of_subset inter_subset_right hb)
  refine ⟨_, image_mem_map hev, ?_⟩
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  rw [Real.dist_eq, abs_lt]
  simp only [mem_setOf_eq, mem_Icc] at hs ht
  constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]

/-- **`ballLimit f x ∈ S`** if `f ∈ S` a.e. near `x` (`S` closed and convex). -/
theorem ballLimit_mem {f : E d → ℝ} {x : E d} {W : Set (E d)} (hW : W ∈ 𝓝 x)
    (hf : IntegrableOn f W) (hosc : EssOscVanishes f x) {S : Set ℝ} (hS : Convex ℝ S)
    (hSc : IsClosed S) (h : ∀ᵐ z ∂(volume.restrict W), f z ∈ S) :
    ballLimit f x ∈ S :=
  hSc.mem_of_tendsto (tendsto_ballLimit hW hf hosc) (eventually_average_mem hW hf hS hSc h)

/-- **Continuity of the representative** on an open set where `f` is integrable and its essential
oscillation vanishes at every point. -/
theorem continuousOn_ballLimit {f : E d → ℝ} {W : Set (E d)} (hW : IsOpen W)
    (hf : IntegrableOn f W) (hosc : ∀ x ∈ W, EssOscVanishes f x) :
    ContinuousOn (ballLimit f) W := by
  intro y hy
  refine (Metric.tendsto_nhds.2 fun ε hε ↦ ?_).mono_left nhdsWithin_le_nhds
  obtain ⟨ρ, hρ, m, M, hMm, hb⟩ := hosc y hy (ε / 2) (by positivity)
  have hmem : ∀ x ∈ W ∩ ball y ρ, ballLimit f x ∈ Icc m M := fun x hx ↦
    ballLimit_mem ((hW.inter isOpen_ball).mem_nhds hx) (hf.mono_set inter_subset_left)
      (hosc x hx.1) (convex_Icc m M) isClosed_Icc
      (ae_restrict_of_ae_restrict_of_subset inter_subset_right hb)
  have hy' := hmem y ⟨hy, mem_ball_self hρ⟩
  filter_upwards [(hW.inter isOpen_ball).mem_nhds ⟨hy, mem_ball_self hρ⟩] with x hx
  have hx' := hmem x hx
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hx'.1, hx'.2, hy'.1, hy'.2]

/-- **`ballLimit f = f` a.e. on `W`** (Lebesgue differentiation). -/
theorem ballLimit_ae_eq {f : E d → ℝ} {W : Set (E d)} (hW : IsOpen W) (hf : IntegrableOn f W) :
    ∀ᵐ x ∂(volume.restrict W), ballLimit f x = f x := by
  set g : E d → ℝ := W.indicator f with hg
  have hgi : Integrable g := hf.integrable_indicator hW.measurableSet
  have hleb := IsUnifLocDoublingMeasure.ae_tendsto_average (μ := volume)
    hgi.locallyIntegrable 1
  filter_upwards [ae_restrict_of_ae hleb, ae_restrict_mem hW.measurableSet] with x hx hxW
  have h1 := hx (fun _ : ℝ ↦ x) id tendsto_id
    (eventually_nhdsWithin_of_forall fun s (hs : 0 < s) ↦ by
      simpa only [id, one_mul] using mem_closedBall_self hs.le)
  have hgx : g x = f x := indicator_of_mem hxW f
  rw [hgx] at h1
  have heq : (fun s ↦ ⨍ z in closedBall x (id s), g z) =ᶠ[𝓝[>] (0 : ℝ)]
      fun s ↦ ⨍ z in closedBall x s, f z := by
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW x hxW
    filter_upwards [Ioo_mem_nhdsGT hε] with s hs
    have hsub : closedBall x s ⊆ W := (closedBall_subset_ball hs.2).trans hεW
    simp only [id, setAverage_eq]
    congr 1
    exact setIntegral_congr_fun measurableSet_closedBall fun y hy ↦ indicator_of_mem (hsub hy) f
  exact (h1.congr' heq).limUnder_eq

end EllipticBernoulli
