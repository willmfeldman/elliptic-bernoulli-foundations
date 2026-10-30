/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
import EllipticBernoulli.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Invariance of the Laplacian and of harmonicity under isometries and rescalings

On finite-dimensional real inner product spaces:

* `laplacian_comp_linearIsometryEquiv`: `Δ (f ∘ l) = (Δ f) ∘ l` for a linear isometry equivalence
  `l` (no differentiability hypothesis);
* `HarmonicOnNhd.comp_linearIsometryEquiv`: harmonicity is invariant under linear isometries;
* `HarmonicOnNhd.rescale`: if `h` is harmonic on `S`, then for `x₀ ∈ F` and `r ∈ ℝ` the rescaling
  `x ↦ h (x₀ + r x) / r` is harmonic on `{x | x₀ + r x ∈ S}`. No condition on `r` is needed: for
  `r = 0` the rescaling is the zero function, since `a / 0 = 0` in Lean;
* `HarmonicOnNhd.rescale_comp_linearIsometryEquiv`: the same for `x ↦ h (x₀ + r Q x) / r`.

Dot notation caveat: these declarations live in the `EllipticBernoulli` namespace, so they are
called as `HarmonicOnNhd.rescale hh x₀ r`, not `hh.rescale x₀ r`.

## Provenance

`iteratedFDeriv_comp_linearIsometryEquiv_apply` and `laplacian_comp_linearIsometryEquiv` are
adapted (unchanged up to namespace and name) from viscosity-solution-theory v0.2.0 (commit 3a93109),
`ViscositySolns/Applications/Laplace/Weyl/LaplacianInvariance.lean`
(`iteratedFDeriv_comp_linearIsometryEquiv_apply`, `laplacian_comp_linearIsometryEquiv_right`),
which ports TauCeti, https://github.com/TauCetiProject/TauCeti,
`TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean`, commit
91f66a0514e6523efdccddb9e35fb82c96dd6405 (Apache-2.0;
`Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`). Changes: namespace
`ViscositySolns.Analysis` → `EllipticBernoulli`, `laplacian_comp_linearIsometryEquiv_right` renamed
`laplacian_comp_linearIsometryEquiv`, variable names `E, E', F` → `F, F', G`, module form.
-/

open Set Filter Topology InnerProductSpace
open scoped Laplacian

public section

namespace EllipticBernoulli

/-! ### Invariance of the Laplacian under linear isometries -/

section Invariance

variable
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ F'] in
/-- The iterated derivative transforms under a linear isometry equivalence on the right by
pulling the directions through the isometry. (Adapted from viscosity-solution-theory / TauCeti.) -/
theorem iteratedFDeriv_comp_linearIsometryEquiv_apply (l : F ≃ₗᵢ[ℝ] F') (f : F' → G)
    (i : ℕ) (x : F) (m : Fin i → F) :
    iteratedFDeriv ℝ i (f ∘ l) x m = iteratedFDeriv ℝ i f (l x) (fun j ↦ l (m j)) := by
  have h := l.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (x := x) (Set.mem_univ _) i
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  rw [← LinearIsometryEquiv.coe_toContinuousLinearEquiv l]
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rfl

/-- **Invariance of the Laplacian under isometries.** `Δ (f ∘ l) = (Δ f) ∘ l` for a linear
isometry equivalence `l`; no differentiability hypothesis is needed. (Adapted from
viscosity-solution-theory / TauCeti, `laplacian_comp_linearIsometryEquiv_right`.) -/
theorem laplacian_comp_linearIsometryEquiv (l : F ≃ₗᵢ[ℝ] F') (f : F' → G) :
    Δ (f ∘ l) = (Δ f) ∘ l := by
  ext x
  simp only [Function.comp_apply,
    laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ l) (stdOrthonormalBasis ℝ F),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ F).map l)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_comp_linearIsometryEquiv_apply l f 2 x]
  congr 1
  funext j
  fin_cases j <;> simp [OrthonormalBasis.map_apply]

end Invariance

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Harmonicity at a point is invariant under linear isometries. -/
theorem HarmonicAt.comp_linearIsometryEquiv {h : F → ℝ} (Q : F ≃ₗᵢ[ℝ] F) {x : F}
    (hh : HarmonicAt h (Q x)) : HarmonicAt (h ∘ Q) x := by
  refine ⟨hh.1.comp x Q.contDiff.contDiffAt, ?_⟩
  have := hh.2.comp_tendsto (Q.continuous.tendsto x)
  filter_upwards [this] with z hz
  simp only [Function.comp_apply, Pi.zero_apply] at hz
  rw [congrFun (laplacian_comp_linearIsometryEquiv Q h) z, Function.comp_apply, hz,
    Pi.zero_apply]

/-- Harmonicity on a set is invariant under linear isometries. -/
theorem HarmonicOnNhd.comp_linearIsometryEquiv {h : F → ℝ} {S : Set F}
    (hh : HarmonicOnNhd h S) (Q : F ≃ₗᵢ[ℝ] F) : HarmonicOnNhd (h ∘ Q) (Q ⁻¹' S) :=
  fun _ hx ↦ HarmonicAt.comp_linearIsometryEquiv Q (hh _ hx)

/-- **Affine invariance of harmonicity.** If `h` is harmonic on
`S`, then for `x₀ ∈ F` and `r ∈ ℝ`, `x ↦ h (x₀ + r x) / r` is harmonic on
`{x | x₀ + r x ∈ S}`. -/
theorem HarmonicOnNhd.rescale {h : F → ℝ} {S : Set F} (hh : HarmonicOnNhd h S) (x₀ : F)
    (r : ℝ) :
    HarmonicOnNhd (fun x ↦ h (x₀ + r • x) / r) ((fun x ↦ x₀ + r • x) ⁻¹' S) := by
  have h1 := (HarmonicOnNhd.comp_add_smul hh x₀ r).const_smul (c := r⁻¹)
  convert h1 using 1
  ext x
  simp [div_eq_inv_mul]

/-- Affine invariance of harmonicity with a rotation: if `h` is harmonic on `S`, then for a linear
isometry `Q`, `x₀ ∈ F` and `r ∈ ℝ`, `x ↦ h (x₀ + r Q x) / r` is harmonic on
`{x | x₀ + r Q x ∈ S}`. -/
theorem HarmonicOnNhd.rescale_comp_linearIsometryEquiv {h : F → ℝ} {S : Set F}
    (hh : HarmonicOnNhd h S) (Q : F ≃ₗᵢ[ℝ] F) (x₀ : F) (r : ℝ) :
    HarmonicOnNhd (fun x ↦ h (x₀ + r • Q x) / r) ((fun x ↦ x₀ + r • Q x) ⁻¹' S) :=
  HarmonicOnNhd.comp_linearIsometryEquiv (HarmonicOnNhd.rescale hh x₀ r) Q

end EllipticBernoulli
