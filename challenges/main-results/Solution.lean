module

public import EllipticBernoulli.Variational.Existence
public import EllipticBernoulli.Variational.Continuity
public import EllipticBernoulli.Variational.Perturbation
public import EllipticBernoulli.Variational.OneSided
public import EllipticBernoulli.Variational.EnergyMinimizer
public import EllipticBernoulli.Lipschitz.Estimate
public import EllipticBernoulli.Nondegeneracy.SmallestSuper
public import EllipticBernoulli.Nondegeneracy.ExteriorBall
public import EllipticBernoulli.Nondegeneracy.Equivalences
public import EllipticBernoulli.Nondegeneracy.Minimizer
public import EllipticBernoulli.Nondegeneracy.LargestSub2D
public import EllipticBernoulli.Flatness.Classical
public import EllipticBernoulli.Hodograph.Chart
public import EllipticBernoulli.Classical.Viscosity
public import EllipticBernoulli.Classical.InnerVariation
public import EllipticBernoulli.Classical.GradientBound
public import EllipticBernoulli.Blowup.PlanarClassification
public import EllipticBernoulli.Sphere.CapInequality
public import EllipticBernoulli.TwoPhase.ClassificationMain
public import EllipticBernoulli.TwoPhase.WeissLocal
public import EllipticBernoulli.QuantChart.Two
public import EllipticBernoulli.QuantChart.Three

/-!
# Solution: the main results of the library

Discharges every statement of `Challenge.lean` through the library modules imported above, section
by section.
-/

@[expose] public noncomputable section

namespace EllipticBernoulli

section ObstacleExistence

open Set Filter Topology MeasureTheory Metric

variable {d : ℕ}

theorem challenge_exists_isObstacleMinimizer {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d}
    {K : E d → Set ℝ} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ C, ∀ x ∈ U, |Q x| ≤ C)
    (hQm : Measurable Q)
    (hu : MemH1Loc U u Gu) (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) (hK : ∀ y, IsClosed (K y))
    (huK : ∀ y ∈ U, u y ∈ K y) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), IsObstacleMinimizer U (ball x₀ r) Q u K w Gw :=
  exists_isObstacleMinimizer hU hQ hQm hu hr hB hK huK

theorem challenge_isObstacleMinimizer_exists_continuousOn {U : Set (E d)} {Q u : E d → ℝ}
    {K : E d → Set ℝ} {w : E d → ℝ} {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U)
    (hQ : ∃ L, LipschitzOnWith L Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y) (hB : closedBall x₀ r ⊆ U)
    (hr : 0 < r) (hK : K = (fun y ↦ Icc 0 (u y)) ∨ K = (fun y ↦ Ici (u y)))
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u K w Gw) :
    ∃ w' : E d → ℝ, (∀ᵐ y ∂volume.restrict U, w' y = w y) ∧
      IsObstacleMinimizer U (ball x₀ r) Q u K w' Gw ∧ ContinuousOn w' U :=
  IsObstacleMinimizer.exists_continuousOn hU hQ hQpos hQb hu hu0 hB hr hK hw

end ObstacleExistence

section EnergyPerturbation

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

variable {d : ℕ}

theorem challenge_energy_decrease_of_not_super {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (htouch : φ x₀ = w x₀ ∧ ∀ᶠ y in 𝓝[≠] x₀, φ y < w y)
    (hfail : 0 < Δ φ x₀ ∧ (φ x₀ = 0 → Q x₀ < ‖∇ φ x₀‖)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, w y ≤ w' y ∧ w' y ≤ max (w y) (φ y + η)) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw :=
  energy_decrease_of_not_super hU hQ hQpos hQb hw hw0 hGw hB hBU hφ hx₀ htouch hfail

theorem challenge_energy_decrease_of_not_sub {U : Set (E d)} {Q w : E d → ℝ} {Gw : E d → E d}
    (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U) (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hw : ContinuousOn w U) (hw0 : ∀ x ∈ U, 0 ≤ w x)
    (hGw : MemH1Loc U w Gw) {B : Set (E d)} (hB : IsOpen B) (hBU : CompactlyContained B U)
    {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ : E d} (hx₀ : x₀ ∈ B)
    (hx₀pos : x₀ ∈ closure (posSet w U))
    (htouch : max (φ x₀) 0 = w x₀ ∧
      ∀ᶠ y in 𝓝[(closure (posSet w U) ∩ U) \ {x₀}] x₀, w y < max (φ y) 0)
    (hfail : Δ φ x₀ < 0 ∧ (φ x₀ = 0 → ‖∇ φ x₀‖ < Q x₀)) :
    ∀ ρ > 0, ball x₀ ρ ⊆ B → ∀ η > 0, ∃ (w' : E d → ℝ) (Gw' : E d → E d),
      MemH1Loc U w' Gw' ∧ (∀ y ∈ U \ ball x₀ ρ, w' y = w y) ∧
      (∀ y ∈ U, min (w y) (max (φ y - η) 0) ≤ w' y ∧ w' y ≤ w y) ∧
      energyJ B Q w' Gw' < energyJ B Q w Gw :=
  energy_decrease_of_not_sub hU hQ hQpos hQb hw hw0 hGw hB hBU hφ hx₀ hx₀pos htouch
    hfail

end EnergyPerturbation

section ViscosityMinimizers

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian

variable {d : ℕ}

theorem challenge_isUpwardMinimizer_isViscSuper {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ y ∈ U, 0 ≤ Q y) (hu : ContinuousOn u U)
    (hu0 : ∀ y ∈ U, 0 ≤ u y) (hmin : IsUpwardMinimizer U Q u) : IsViscSuper U Q u :=
  IsUpwardMinimizer.isViscSuper hU hQ hQ0 hu hu0 hmin

theorem challenge_isDownwardMinimizer_isViscSub {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hu : ContinuousOn u U) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    (hmin : IsDownwardMinimizer U Q u) : IsViscSub U Q u :=
  IsDownwardMinimizer.isViscSub hU hQ hu hu0 hmin

theorem challenge_isLocalEnergyMinimizer_isViscSolution {U : Set (E d)} {Q u : E d → ℝ}
    (hU : IsOpen U) (hQ : ContinuousOn Q U) (hQ0 : ∀ y ∈ U, 0 ≤ Q y) (hu : ContinuousOn u U)
    (hu0 : ∀ y ∈ U, 0 ≤ u y) (hmin : IsLocalEnergyMinimizer U Q u) : IsViscSolution U Q u :=
  IsLocalEnergyMinimizer.isViscSolution hU hQ hQ0 hu hu0 hmin

theorem challenge_isObstacleMinimizer_isViscSuper_of_upper {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : IsViscSuper U Q u) (hr : closedBall x₀ r ⊆ U)
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Icc 0 (u y)) w Gw)
    (hwc : ContinuousOn w U) : IsViscSuper U Q w :=
  IsObstacleMinimizer.isViscSuper_of_upper hU hQ hQpos hQb hu hr hw hwc

theorem challenge_isObstacleMinimizer_isViscSub_of_lower {U : Set (E d)} {Q u w : E d → ℝ}
    {Gw : E d → E d} {x₀ : E d} {r : ℝ} (hU : IsOpen U) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ x ∈ U, c ≤ Q x) (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C)
    (hu : IsViscSub U Q u) (hr : closedBall x₀ r ⊆ U)
    (hw : IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Ici (u y)) w Gw)
    (hwc : ContinuousOn w U) : IsViscSub U Q w :=
  IsObstacleMinimizer.isViscSub_of_lower hU hQ hQpos hQb hu hr hw hwc

end ViscosityMinimizers

section EnergyMinimizerRegularity

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Laplacian

variable {d : ℕ}

theorem challenge_isLocalEnergyMinimizer_exists_regular_representative {U : Set (E d)}
    {Q u : E d → ℝ} (hU : IsOpen U) (hQc : ContinuousOn Q U) (hQ0 : ∀ x ∈ U, 0 ≤ Q x)
    (hQb : ∃ C, ∀ x ∈ U, Q x ≤ C) (hu0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U Q u) :
    ∃ v : E d → ℝ, (∀ᵐ x ∂volume.restrict U, v x = u x) ∧ IsLocalEnergyMinimizer U Q v ∧
      LocallyLipschitzOn U v ∧ (∀ x ∈ U, 0 ≤ v x) ∧ IsOpen (posSet v U) ∧
      ContDiffOn ℝ ∞ v (posSet v U) ∧ ∀ x ∈ posSet v U, Δ v x = 0 :=
  IsLocalEnergyMinimizer.exists_regular_representative hU hQc hQ0 hQb hu0 hmin

end EnergyMinimizerRegularity

section LipschitzEstimate

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped NNReal

variable {d : ℕ}

theorem challenge_lipschitzOnWith_of_isViscSuper (hd : 1 ≤ d) :
    ∃ C : ℝ, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) (r Qmax M : ℝ),
      IsOpen U → 0 < r → ball x₀ (2 * r) ⊆ U → IsViscSuper U Q u →
      HarmonicOnNhd u (posSet u U) → (∀ y ∈ ball x₀ (2 * r), Q y ≤ Qmax) → 0 ≤ Qmax →
      (∀ y ∈ ball x₀ (2 * r), u y ≤ M) →
      LipschitzOnWith (C * (Qmax + M / r)).toNNReal u (ball x₀ r) :=
  lipschitzOnWith_of_isViscSuper hd

theorem challenge_locallyLipschitzOn_of_isViscSuper {U : Set (E d)} {Q u : E d → ℝ} (hU : IsOpen U)
    (hu : IsViscSuper U Q u) (hharm : HarmonicOnNhd u (posSet u U)) (hQ : ContinuousOn Q U) :
    LocallyLipschitzOn U u :=
  locallyLipschitzOn_of_isViscSuper hU hu hharm hQ

end LipschitzEstimate

section Nondegeneracy

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Laplacian NNReal

variable {d : ℕ}

theorem challenge_isLocalSmallestSuper_exists_le_of_closedBall_subset {U : Set (E d)}
    {Q u : E d → ℝ} {q₀ : ℝ} (hd : 1 ≤ d) (hU : IsOpen U) (hu : IsLocalSmallestSuper U Q u)
    (hq₀ : 0 < q₀) (hQ : ∀ y ∈ U, q₀ ≤ Q y) :
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, q₀ / (8 * d) * r ≤ u y :=
  IsLocalSmallestSuper.exists_le_of_closedBall_subset hd hU hu hq₀ hQ

theorem challenge_exists_le_of_exteriorBall_sameRadius (hd : 1 ≤ d) {Q v : E d → ℝ}
    {x₀ p : E d} {s q₀ : ℝ} (hs : 0 < s) (hq₀ : 0 < q₀) (hv : IsViscSub (ball x₀ s) Q v)
    (hQ : ∀ y ∈ ball x₀ s, q₀ ≤ Q y) (hx₀ : x₀ ∈ freeBoundary v (ball x₀ s))
    (hp : ‖x₀ - p‖ = s) (hball : ∀ y ∈ ball p s ∩ ball x₀ s, v y = 0) :
    ∃ y ∈ ball x₀ s, q₀ / (128 * d * Real.exp (3 * d)) * s ≤ v y :=
  exists_le_of_exteriorBall_sameRadius hd hs hq₀ hv hQ hx₀ hp hball

theorem challenge_nondegenerate_sup_iff_average (hd : 1 ≤ d) (L : ℝ≥0) (c : ℝ) (hc : 0 < c) :
    ∃ c' > 0, ∀ (u : E d → ℝ) (x₀ : E d),
      (∀ y ∈ ball x₀ 1, 0 ≤ u y) → LipschitzOnWith L u (ball x₀ 1) →
      HarmonicOnNhd u (posSet u (ball x₀ 1)) → x₀ ∈ freeBoundary u (ball x₀ 1) →
      ((∀ r ∈ Ioo (0 : ℝ) 1,
          c * r ≤ ⨍ z, u (x₀ + r • (z : E d)) ∂(volume : Measure (E d)).toSphere) →
        ∀ r ∈ Ioo (0 : ℝ) 1, ∃ y ∈ sphere x₀ r, c' * r ≤ u y) ∧
      ((∀ r ∈ Ioo (0 : ℝ) 1, ∃ y ∈ sphere x₀ r, c * r ≤ u y) →
        ∀ r ∈ Ioo (0 : ℝ) 1,
          c' * r ≤ ⨍ z, u (x₀ + r • (z : E d)) ∂(volume : Measure (E d)).toSphere) :=
  nondegenerate_sup_iff_average hd L c hc

theorem challenge_isDownwardMinimizer_exists_le_of_closedBall_subset {U : Set (E d)}
    {Q u : E d → ℝ} {q₀ : ℝ} (hd : 1 ≤ d) (hU : IsOpen U) (hu : IsDownwardMinimizer U Q u)
    (hlip : LocallyLipschitzOn U u) (hu0 : ∀ y ∈ U, 0 ≤ u y) (hq₀ : 0 < q₀)
    (hQ : ∀ y ∈ U, q₀ ≤ Q y) (hQb : ∃ C, ∀ y ∈ U, Q y ≤ C) (hQm : Measurable Q) :
    ∀ z ∈ closure (posSet u U), ∀ r, 0 < r → closedBall z r ⊆ U →
      ∃ y ∈ closedBall z r, q₀ / (8 * d * Real.exp ((d : ℝ) / 2)) * r ≤ u y :=
  IsDownwardMinimizer.exists_le_of_closedBall_subset hd hU hu hlip hu0 hq₀ hQ hQb hQm

theorem challenge_exists_pos_le_of_isLocalLargestSub (q₀ : ℝ) (K : ℝ≥0) (hq₀ : 0 < q₀) :
    ∃ c > 0, ∀ {Q u : E 2 → ℝ} {x₀ : E 2} {R : ℝ}, 0 < R →
      (∀ y ∈ ball x₀ R, q₀ ≤ Q y) → IsLocalLargestSub (ball x₀ R) Q u →
      LipschitzOnWith K u (ball x₀ R) → ContDiffOn ℝ 2 u (posSet u (ball x₀ R)) →
      (∀ y ∈ posSet u (ball x₀ R), Δ u y = 0) → x₀ ∈ freeBoundary u (ball x₀ R) →
      ∀ r, 0 < r → r ≤ R / 2 → ∃ y ∈ closedBall x₀ r, c * r ≤ u y :=
  exists_pos_le_of_isLocalLargestSub q₀ K hq₀

end Nondegeneracy

section FlatnessRegularity

open Set Filter Topology Metric
open scoped NNReal

variable {d : ℕ}

theorem challenge_isC1GammaHypersurfaceNear_of_flat (hd : 2 ≤ d) (L : ℝ≥0) (qmin qmax : ℝ)
    (hqmin : 0 < qmin) :
    ∃ εbar > 0, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsC1GammaHypersurfaceNear (freeBoundary u U) x₀ (r / 2) :=
  isC1GammaHypersurfaceNear_of_flat hd L qmin qmax hqmin

theorem challenge_isClassicalNear_of_flat (hd : 2 ≤ d) (L : ℝ≥0) (qmin qmax : ℝ)
    (hqmin : 0 < qmin) :
    ∃ εbar > 0, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ e : E d) (r : ℝ), IsOpen U →
      LipschitzOnWith L Q U → (∀ y ∈ U, qmin ≤ Q y ∧ Q y ≤ qmax) → IsViscSolution U Q u →
      x₀ ∈ freeBoundary u U → ‖e‖ = 1 → 0 < r → r ≤ εbar → ball x₀ r ⊆ U →
      (∀ y ∈ ball x₀ r, Q x₀ * max (inner ℝ (y - x₀) e - εbar * r) 0 ≤ u y ∧
        u y ≤ Q x₀ * max (inner ℝ (y - x₀) e + εbar * r) 0) →
      IsClassicalNear U Q u x₀ :=
  isClassicalNear_of_flat hd L qmin qmax hqmin

end FlatnessRegularity

section FlatChart

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

variable {d : ℕ}

theorem challenge_flat_chart (hd : 2 ≤ d) {U : Set (E d)} {u : E d → ℝ} {x₀ e : E d}
    (hU : IsOpen U) (hc : ContinuousOn u U) (hnn : ∀ x ∈ U, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) (hx₀ : x₀ ∈ freeBoundary u U) (he : ‖e‖ = 1)
    (hblow : IsBlowupLimit u x₀ (fun y ↦ max (inner ℝ y e) 0)) :
    ∃ ρ > 0, ball x₀ ρ ⊆ U ∧ ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ) ∧
      (∀ x ∈ ball x₀ ρ, u x = max (F x) 0) ∧ (∀ x ∈ ball x₀ ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ, F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ ball x₀ ρ, 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ | 0 < F x} :=
  flat_chart hd hU hc hnn hmin hx₀ he hblow

end FlatChart

section ClassicalSolutions

open Set Filter Topology MeasureTheory Metric
open scoped NNReal

variable {d : ℕ}

theorem challenge_isClassicalSolution_isViscSolution {U : Set (E d)} {Q u : E d → ℝ}
    (hu : IsClassicalSolution U Q u) (hQ : ContinuousOn Q U) : IsViscSolution U Q u :=
  IsClassicalSolution.isViscSolution hu hQ

theorem challenge_isClassicalSolution_integral_innerVarIntegrand_eq_zero {U : Set (E d)}
    {Q u : E d → ℝ} {ξ : E d → E d}
    (hu : IsClassicalSolution U Q u) (hQ : ∃ K, LipschitzOnWith K Q U)
    (hQpos : ∃ c > 0, ∀ y ∈ U, c ≤ Q y) (hξ : ∃ K, LipschitzWith K ξ) (hξc : HasCompactSupport ξ)
    (hξU : tsupport ξ ⊆ U) :
    ∫ x in U, innerVarIntegrand Q u ((posSet u U).indicator 1) ξ x = 0 :=
  IsClassicalSolution.integral_innerVarIntegrand_eq_zero hu hQ hQpos hξ hξc hξU

theorem challenge_classical_lipschitz_bound (L : ℝ≥0) :
    ∃ w : ℝ → ℝ, ContinuousOn w (Ico 0 1) ∧ MonotoneOn w (Ico 0 1) ∧
      Tendsto w (𝓝[>] 0) (𝓝 0) ∧
      ∀ u : E d → ℝ, IsClassicalSolution (ball 0 1) (fun _ ↦ 1) u →
        LipschitzOnWith L u (ball 0 1) →
        u 0 = 0 → ∀ r ∈ Ioo (0 : ℝ) 1, LipschitzOnWith (1 + w r).toNNReal u (ball 0 r) :=
  classical_lipschitz_bound L

end ClassicalSolutions

section PlanarClassification

open Set Filter Topology MeasureTheory

theorem challenge_classification_homogeneous_planar {q : ℝ} (hq : 0 < q) {v χ : E 2 → ℝ}
    (h : IsInnerVarSolution univ (fun _ ↦ q) v χ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ y : E 2, v (t • y) = t * v y) :
    ∃ e : E 2, ‖e‖ = 1 ∧
      (((∀ y, v y = q * max (inner ℝ y e) 0) ∧
          ∀ᵐ y, χ y = {z : E 2 | 0 < inner ℝ z e}.indicator 1 y) ∨
        (∃ α : ℝ, 0 ≤ α ∧ (∀ y, v y = α * |inner ℝ y e|) ∧ ∀ᵐ y, χ y = 1) ∨
        ((∀ y, v y = 0) ∧ ∀ᵐ y, χ y = 0)) :=
  classification_homogeneous_planar hq h hhom

end PlanarClassification

section FriedlandHayman

open Metric

theorem challenge_friedlandHayman {d : ℕ} (hd : 2 ≤ d) (Γ₁ Γ₂ : Set (sphere (0 : E d) 1))
    (hΓ₁ : IsOpen Γ₁) (hΓ₂ : IsOpen Γ₂) (hne₁ : Γ₁.Nonempty) (hne₂ : Γ₂.Nonempty)
    (hdisj : Disjoint Γ₁ Γ₂) :
    2 ≤ sphExponent Γ₁ + sphExponent Γ₂ :=
  friedlandHayman d hd Γ₁ Γ₂ hΓ₁ hΓ₂ hne₁ hne₂ hdisj

end FriedlandHayman

section AcfMonotonicity

open Set
open scoped NNReal

theorem challenge_acfMonotoneIn {d : ℕ} (hd : 2 ≤ d) {u₁ u₂ : E d → ℝ} {x₀ : E d} {L : ℝ≥0}
    (hnn₁ : ∀ x, 0 ≤ u₁ x) (hnn₂ : ∀ x, 0 ≤ u₂ x)
    (hlip₁ : LipschitzWith L u₁) (hlip₂ : LipschitzWith L u₂)
    (hharm₁ : InnerProductSpace.HarmonicOnNhd u₁ {x | 0 < u₁ x})
    (hharm₂ : InnerProductSpace.HarmonicOnNhd u₂ {x | 0 < u₂ x})
    (hmul : ∀ x, u₁ x * u₂ x = 0) (hx₁ : u₁ x₀ = 0) (hx₂ : u₂ x₀ = 0) :
    MonotoneOn (fun r ↦ acfPhi u₁ u₂ x₀ r) (Ioi 0) :=
  acfMonotoneIn hd u₁ u₂ x₀ L
    ⟨hnn₁, hnn₂, hlip₁, hlip₂, hharm₁, hharm₂, hmul, hx₁, hx₂⟩

end AcfMonotonicity

section TwoPhaseClassification

open Set
open scoped NNReal

theorem challenge_twoPhaseClassification {d : ℕ} {u : E d → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hpos : ∃ x, 0 < u x)
    (hneg : ∃ x, u x < 0) :
    ∃ (e : E d) (c a b : ℝ), ‖e‖ = 1 ∧ 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = 1 ∧
      ∀ x, u x = a * max (inner ℝ x e + c) 0 - b * max (-(inner ℝ x e + c)) 0 :=
  twoPhaseClassification hu hmin hpos hneg

end TwoPhaseClassification

section WeissLocal

open Set Metric MeasureTheory
open scoped NNReal

theorem challenge_weissMonotoneLocal {d : ℕ} (hd : 2 ≤ d) {U : Set (E d)} {u : E d → ℝ} {L : ℝ≥0}
    {x₀ : E d} {R : ℝ} (hU : IsOpen U) (hB : ball x₀ R ⊆ U)
    (hmin : IsLocalEnergyMinimizer U (fun _ ↦ 1) u) (hlip : LipschitzOnWith L u (ball x₀ R))
    (hu : u x₀ = 0) :
    (∀ r s : ℝ, 0 < r → r < s → s < R →
      weissDefect u x₀ r s ≤ weissW u x₀ s - weissW u x₀ r ∧ 0 ≤ weissDefect u x₀ r s) ∧
    (∀ r : ℝ, 0 < r → r < R →
      |weissW u x₀ r| ≤ ((L : ℝ) ^ 2 + 1) * volume.real (ball (0 : E d) 1) +
        (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ) ∧
    ∀ r s : ℝ, 0 < r → r < s → s < R → weissW u x₀ r = weissW u x₀ s →
      ∀ x : E d, r < ‖x - x₀‖ → ‖x - x₀‖ < s → ∀ τ : ℝ, 0 < τ → r < τ * ‖x - x₀‖ →
        τ * ‖x - x₀‖ < s → u (x₀ + τ • (x - x₀)) = τ * u x :=
  weissMonotoneLocal hd hU hB hmin hlip hu

end WeissLocal

section QuantFlatChart

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

theorem challenge_quantFlatChart :
    ∀ {d : ℕ}, 2 ≤ d → ∃ ε₀ > 0, ∃ α > 0, ∃ C > 0, ∀ {u : E d → ℝ} {e : E d} {ε : ℝ},
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 → ε ≤ ε₀ →
    (∀ x ∈ ball (0 : E d) 1, |u x - max (inner ℝ x e) 0| ≤ ε) →
    ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball 0 (1 / 2)) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), u x = max (F x) 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), 0 < F x → Δ F x = 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), 0 ≤ F x →
        1 / 2 ≤ inner ℝ (∇ F x) e ∧ ‖∇ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), ∀ y ∈ ball (0 : E d) (1 / 2), 0 ≤ F x → 0 ≤ F y →
        ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ ≤ C * ‖x - y‖ ^ α) :=
  quantFlatChart

end QuantFlatChart

section QuantFlatChartThree

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

theorem challenge_quantFlatChartThree :
    ∀ {d : ℕ}, 2 ≤ d → ∃ ε₀ > 0, ∃ C₀ > 0, ∀ {u : E d → ℝ} {e : E d} {ε : ℝ},
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 → ε ≤ ε₀ →
    (∀ x ∈ ball (0 : E d) 1, |u x - max (inner ℝ x e) 0| ≤ ε) →
    ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball 0 (1 / 4)) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), u x = max (F x) 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), 0 < F x → Δ F x = 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), 0 ≤ F x →
        1 / 2 ≤ inner ℝ (∇ F x) e ∧ ‖iteratedFDeriv ℝ 3 F x‖ ≤ C₀) :=
  quantFlatChartThree

end QuantFlatChartThree

end EllipticBernoulli
