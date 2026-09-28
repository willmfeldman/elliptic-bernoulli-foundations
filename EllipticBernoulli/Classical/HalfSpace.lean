/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Setting
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import EllipticBernoulli.Flatness.LinearizedRegularity
import EllipticBernoulli.Harmonic.Comparison
import EllipticBernoulli.Harmonic.Liouville
import EllipticBernoulli.Harmonic.ViscosityHarmonic
import EllipticBernoulli.Viscosity.Calculus

/-!
# A Liouville theorem in the half-space

* `eq_linear_of_halfSpace`: a Lipschitz function on `E d` that vanishes on `{⟪z, e⟫ ≤ 0}` and is
  harmonic in the half-space `{⟪z, e⟫ > 0}` is linear there: `v z = a ⟪z, e⟫`.

## Proof

The odd reflection `w z = v z - v (R z)`, with `R` the reflection across `e^⊥`
(`planeReflection`), equals `v` on the half-space, `-v ∘ R` on the other half, and `0` on the
plane; it is odd, `w (R z) = -w z`. It is harmonic off the plane. At a plane point `p`, a smooth
`φ` touching `w` from above gives `ψ = φ + φ ∘ R ≥ w + w ∘ R = 0` near `p`, with `ψ p = 0`, so
`0 ≤ Δψ(p) = 2 Δφ(p)`; the superharmonic case is the same argument for `-w`. So `w` is viscosity
harmonic, hence harmonic on `E d` (`harmonicOnNhd_of_isViscHarmonic`). It has linear growth,
so it is affine (`harmonic_liouville_affine`): `w z = a₀ + ⟪b, z⟫`, and `w = 0` on `e^⊥`
gives `w z = w (⟪z, e⟫ e) = ⟪z, e⟫ ⟪b, e⟫`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Laplacian RealInnerProductSpace NNReal

namespace EllipticBernoulli

variable {d : ℕ}

/-- Harmonicity is preserved by precomposition with the reflection across `e^⊥`. -/
private theorem harmonicAt_comp_planeReflection {v : E d → ℝ} (e : E d) {z : E d}
    (hv : HarmonicAt v (planeReflection e z)) :
    HarmonicAt (fun y ↦ v (planeReflection e y)) z := by
  refine ⟨hv.1.comp z (planeReflection e).contDiff.contDiffAt, ?_⟩
  have ht : Tendsto (planeReflection e) (𝓝 z) (𝓝 (planeReflection e z)) :=
    (planeReflection e).continuous.tendsto z
  filter_upwards [ht.eventually hv.2] with y hy
  rw [laplacian_comp_planeReflection]
  exact hy

/-- An odd function (under `R`) that is harmonic off the plane `e^⊥` is viscosity subharmonic
on `E d`. -/
private theorem isViscSubharmonicOn_univ_of_odd {w : E d → ℝ} {e : E d} (he : ‖e‖ = 1)
    (hodd : ∀ y, w (planeReflection e y) = -w y)
    (hharm : HarmonicOnNhd w {z | ⟪z, e⟫ ≠ 0}) : IsViscSubharmonicOn w univ := by
  intro φ hφ x _ ⟨_, heq, hle⟩
  rw [nhdsWithin_univ] at hle
  by_cases hx : ⟪x, e⟫ = 0
  · -- plane point: `ψ = φ + φ ∘ R` has a local minimum at `x`
    set R := planeReflection e with hR
    have hRx : R x = x := planeReflection_eq_self he hx
    have hw0 : w x = 0 := by
      have := hodd x
      rw [hRx] at this
      linarith
    have ht : Tendsto R (𝓝 x) (𝓝 x) := by
      have := R.continuous.tendsto x
      rwa [hRx] at this
    have hψ : ContDiff ℝ ∞ (fun y ↦ φ (R y)) := hφ.comp R.contDiff
    have hmin : IsLocalMin (fun y ↦ φ y + φ (R y)) x := by
      filter_upwards [hle, ht.eventually hle] with y hy hRy
      have := hodd y
      change φ x + φ (R x) ≤ φ y + φ (R y)
      rw [hRx, heq, hw0]
      linarith
    have hφ2 : ContDiffAt ℝ 2 φ x := hφ.contDiffAt.of_le (by norm_cast)
    have hψ2 : ContDiffAt ℝ 2 (fun y ↦ φ (R y)) x := hψ.contDiffAt.of_le (by norm_cast)
    have h := laplacian_nonneg_of_isLocalMin hmin (hφ2.add hψ2)
    have hadd := hφ2.laplacian_add hψ2
    rw [show (fun y ↦ φ y + φ (R y)) = φ + fun y ↦ φ (R y) from rfl, hadd,
      laplacian_comp_planeReflection, ← hR, hRx] at h
    linarith
  · have hW : IsOpen {z : E d | ⟪z, e⟫ ≠ 0} :=
      isOpen_ne_fun (continuous_id.inner continuous_const) continuous_const
    refine HarmonicOnNhd.isViscSubharmonicOn hW hharm φ hφ x hx ⟨hx, heq, ?_⟩
    exact nhdsWithin_le_nhds hle

public section

/-- **Half-space Liouville theorem.** A Lipschitz
function on `E d` that vanishes on `{⟪z, e⟫ ≤ 0}` and is harmonic on `{⟪z, e⟫ > 0}` is linear in
the half-space: `v z = a ⟪z, e⟫`. -/
theorem eq_linear_of_halfSpace {v : E d → ℝ} {e : E d} (he : ‖e‖ = 1) {L : ℝ≥0}
    (hv : LipschitzWith L v) (hzero : ∀ z, ⟪z, e⟫ ≤ 0 → v z = 0)
    (hharm : HarmonicOnNhd v {z | 0 < ⟪z, e⟫}) :
    ∃ a : ℝ, ∀ z, 0 < ⟪z, e⟫ → v z = a * ⟪z, e⟫ := by
  set R := planeReflection e with hR
  set w : E d → ℝ := fun z ↦ v z - v (R z) with hw
  have hRR : ∀ z, R (R z) = z := planeReflection_planeReflection e
  have hRe : ∀ z, ⟪R z, e⟫ = -⟪z, e⟫ := inner_planeReflection he
  have hodd : ∀ y, w (R y) = -w y := fun y ↦ by simp only [hw, hRR]; ring
  have hwc : Continuous w := hv.continuous.sub (hv.continuous.comp R.continuous)
  -- `w` is harmonic off the plane
  have hwH : HarmonicOnNhd w {z | ⟪z, e⟫ ≠ 0} := by
    intro z hz
    rcases lt_or_gt_of_ne (show ⟪z, e⟫ ≠ 0 from hz) with hneg | hpos
    · -- `w = -v ∘ R` near `z`
      have hRz : 0 < ⟪R z, e⟫ := by rw [hRe]; linarith
      have hvR : HarmonicAt (fun y ↦ v (R y)) z :=
        harmonicAt_comp_planeReflection e (hharm _ hRz)
      have hopen : IsOpen {y : E d | ⟪y, e⟫ < 0} :=
        isOpen_lt (continuous_id.inner continuous_const) continuous_const
      have heq : (fun y ↦ -v (R y)) =ᶠ[𝓝 z] w := by
        filter_upwards [hopen.mem_nhds hneg] with y hy
        simp only [hw, hzero y (le_of_lt hy)]
        ring
      exact (harmonicAt_congr_nhds heq).1 hvR.neg
    · have hopen : IsOpen {y : E d | 0 < ⟪y, e⟫} :=
        isOpen_lt continuous_const (continuous_id.inner continuous_const)
      have heq : v =ᶠ[𝓝 z] w := by
        filter_upwards [hopen.mem_nhds hpos] with y hy
        have : v (R y) = 0 := hzero _ (by rw [hRe]; linarith [show 0 < ⟪y, e⟫ from hy])
        simp only [hw, this, sub_zero]
      exact (harmonicAt_congr_nhds heq).1 (hharm z hpos)
  -- `w` is viscosity harmonic, hence harmonic on `E d`
  have hsub : IsViscSubharmonicOn w univ := isViscSubharmonicOn_univ_of_odd he hodd hwH
  have hsub' : IsViscSubharmonicOn (-w) univ :=
    isViscSubharmonicOn_univ_of_odd he (fun y ↦ by rw [Pi.neg_apply, Pi.neg_apply, ← hR, hodd y])
      hwH.neg
  have hsuper : IsViscSuperharmonicOn w univ := by simpa using hsub'.neg
  have hwh : HarmonicOnNhd w univ :=
    harmonicOnNhd_of_isViscHarmonic isOpen_univ hwc.continuousOn hsub hsuper
  -- linear growth
  have hw0 : w 0 = 0 := by simp [hw]
  have hgrowth : ∀ x, |w x| ≤ (2 * L) * (1 + ‖x‖) := by
    intro x
    have h1 := hv.dist_le_mul x 0
    have h2 := hv.dist_le_mul (R x) (R 0)
    rw [Real.dist_eq, dist_zero_right] at h1
    rw [Real.dist_eq, dist_eq_norm, ← map_sub, LinearIsometryEquiv.norm_map, sub_zero] at h2
    have hR0 : R 0 = 0 := map_zero R
    rw [hR0] at h2
    have : |w x| ≤ |v x - v 0| + |v (R x) - v 0| := by
      rw [show w x = (v x - v 0) - (v (R x) - v 0) by simp only [hw]; ring]
      exact abs_sub _ _
    have hL : (0 : ℝ) ≤ L := L.2
    nlinarith [norm_nonneg x]
  obtain ⟨a₀, b, hab⟩ := harmonic_liouville_affine hwh hgrowth
  have ha₀ : a₀ = 0 := by
    have := hab 0
    rw [hw0, inner_zero_right, add_zero] at this
    exact this.symm
  -- `w` vanishes on the plane
  have hplane : ∀ z, ⟪z, e⟫ = 0 → w z = 0 := fun z hz ↦ by
    simp only [hw, hR, planeReflection_eq_self he hz, sub_self]
  refine ⟨⟪b, e⟫, fun z hz ↦ ?_⟩
  have hvw : v z = w z := by
    have : v (R z) = 0 := hzero _ (by rw [hRe]; linarith)
    simp only [hw, this, sub_zero]
  have hperp : ⟪z - ⟪z, e⟫ • e, e⟫ = 0 := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]; ring
  have h1 := hab (z - ⟪z, e⟫ • e)
  rw [hplane _ hperp, ha₀, zero_add, inner_sub_right, real_inner_smul_right] at h1
  rw [hvw, hab z, ha₀, zero_add]
  linarith

end

end EllipticBernoulli
