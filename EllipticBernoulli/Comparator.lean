/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Harmonic.Harnack
public import EllipticBernoulli.Harmonic.GradientEstimate
public import EllipticBernoulli.Harmonic.DirichletBall
public import EllipticBernoulli.Harmonic.ViscosityHarmonic
public import EllipticBernoulli.Harmonic.Comparison
public import EllipticBernoulli.Harmonic.WeylWeakGradient
public import EllipticBernoulli.Harmonic.Limit
public import EllipticBernoulli.Viscosity.Harmonic
public import EllipticBernoulli.Viscosity.Stability
public import EllipticBernoulli.Viscosity.Lattice
public import EllipticBernoulli.Variational.Existence
public import EllipticBernoulli.Variational.Continuity
public import EllipticBernoulli.Variational.Perturbation
public import EllipticBernoulli.Variational.OneSided
public import EllipticBernoulli.Lipschitz.Estimate
public import EllipticBernoulli.Nondegeneracy.SmallestSuper
public import EllipticBernoulli.Nondegeneracy.ExteriorBall
public import EllipticBernoulli.Nondegeneracy.Equivalences
public import EllipticBernoulli.Nondegeneracy.Minimizer
public import EllipticBernoulli.Nondegeneracy.LargestSub2D
public import EllipticBernoulli.Flatness.Harnack
public import EllipticBernoulli.Flatness.Improvement
public import EllipticBernoulli.Flatness.Classical
public import EllipticBernoulli.Classical.Viscosity
public import EllipticBernoulli.Classical.GradientBound
public import EllipticBernoulli.Classical.InnerVariation
public import EllipticBernoulli.Blowup.PlanarClassification

/-!
# Comparator challenges

An API-regression smoke test for the headline theorems, following
`ViscositySolns/Comparator.lean` (viscosity-solution-theory v0.2.0). Each `challenge_*` theorem
restates a headline statement of `EllipticBernoulli/Statements/*` and is discharged by the library
theorem that proves it.

The standalone comparator workspaces in `challenges/` restate a selection of the same statements
over `Mathlib` only; this file guards the library side of that surface on every build.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* B. Orcan-Ekmekci, *On the geometry and regularity of largest subsolutions for a free boundary
  problem in ℝ²: elliptic case*, Calc. Var. Partial Differential Equations 49 (2014), no. 3–4,
  937–962.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free
  Bound. 13 (2011), no. 2, 223–238; arXiv:0912.2057.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
-/

open Set Filter Topology MeasureTheory Metric
open scoped NNReal ContDiff Gradient Laplacian RealInnerProductSpace

public section

namespace EllipticBernoulli.Comparator

open EllipticBernoulli

universe u

/-! ### Harmonic toolkit -/

/-- Challenge: Harnack's inequality on balls. -/
theorem challenge_harnack : HarnackStatement := harnack_ball

/-- Challenge: the interior gradient estimate for harmonic functions. -/
theorem challenge_gradient_estimate : GradientEstimateStatement := norm_gradient_le_of_harmonic

/-- Challenge: the Dirichlet problem on a ball with continuous boundary data. -/
theorem challenge_dirichlet_ball : DirichletBallStatement := exists_harmonic_ball_boundary

/-- Challenge: viscosity-harmonic functions are harmonic. -/
theorem challenge_visc_harmonic : ViscHarmonicStatement := harmonicOnNhd_of_isViscHarmonic

/-- Challenge: the comparison principles for viscosity sub/superharmonic functions. -/
theorem challenge_visc_comparison :
    ViscSubComparisonStatement ∧ ViscSuperComparisonStatement ∧ ViscComparisonStatement :=
  ⟨IsViscSubharmonicOn.le_of_frontier_le, IsViscSuperharmonicOn.le_of_le_frontier,
    viscComparison⟩

/-- Challenge: Weyl's lemma for `H¹_loc` weak solutions. -/
theorem challenge_weak_harmonic : WeakHarmonicStatement := harmonic_of_hasWeakGradient

/-- Challenge: locally uniform limits of harmonic functions are harmonic. -/
theorem challenge_harmonic_limit : HarmonicLimitStatement.{u} :=
  harmonicOnNhd_of_tendstoLocallyUniformlyOn

/-! ### Viscosity toolkit -/

/-- Challenge: viscosity super/subsolutions are super/subharmonic in `{u > 0}`, and viscosity
solutions are harmonic there. -/
theorem challenge_visc_posSet :
    ViscSuperharmonicPosSetStatement ∧ ViscSubharmonicPosSetStatement ∧
      ViscSolutionHarmonicStatement :=
  ⟨IsViscSuper.isViscSuperharmonicOn_posSet, IsViscSub.isViscSubharmonicOn_posSet,
    IsViscSolution.harmonicOnNhd_posSet⟩

/-- Challenge: stability of supersolutions and relaxed subsolutions under locally uniform
limits. -/
theorem challenge_visc_stability : ViscStabilityStatement.{u} :=
  ⟨isViscSuper_of_tendstoLocallyUniformlyOn, isRelaxedSub_of_tendstoLocallyUniformlyOn⟩

/-- Challenge: the lattice properties (`min` of supersolutions, `max` of subsolutions). -/
theorem challenge_visc_min_max : ViscMinMaxStatement := ⟨IsViscSuper.min, IsViscSub.max⟩

/-! ### Variational theory -/

/-- Challenge: existence for the obstacle problem (direct method). -/
theorem challenge_obstacle_existence : ObstacleExistenceStatement := exists_isObstacleMinimizer

/-- Challenge: continuity of obstacle minimizers on all of `U`. -/
theorem challenge_obstacle_continuity : ObstacleContinuityStatement :=
  IsObstacleMinimizer.exists_continuousOn

/-- Challenge: the energy-decreasing perturbations. -/
theorem challenge_energy_decrease : EnergyDecreaseSuperStatement ∧ EnergyDecreaseSubStatement :=
  ⟨energy_decrease_of_not_super, energy_decrease_of_not_sub⟩

/-- Challenge: one-sided minimizers are one-sided viscosity solutions. -/
theorem challenge_one_sided : OneSidedViscStatement :=
  ⟨IsUpwardMinimizer.isViscSuper, IsDownwardMinimizer.isViscSub,
    IsLocalEnergyMinimizer.isViscSolution⟩

/-- Challenge: obstacle minimizers are super/subsolutions off the obstacle. -/
theorem challenge_obstacle_visc : ObstacleViscStatement :=
  ⟨IsObstacleMinimizer.isViscSuper_of_upper, IsObstacleMinimizer.isViscSub_of_lower⟩

/-! ### Lipschitz estimate and non-degeneracy -/

/-- Challenge: the Lipschitz estimate for viscosity supersolutions harmonic in `{u > 0}`. -/
theorem challenge_lipschitz_estimate : LipschitzEstimateStatement ∧ LocalLipschitzStatement :=
  ⟨lipschitzOnWith_of_isViscSuper, locallyLipschitzOn_of_isViscSuper⟩

/-- Challenge: the non-degeneracy suite. -/
theorem challenge_nondegeneracy :
    SmallestSuperNondegStatement ∧ ExteriorBallNondegStatement ∧ NondegEquivStatement ∧
      DownwardNondegStatement :=
  ⟨IsLocalSmallestSuper.isUniformlyNondegenerateNear, exists_le_of_exteriorBall,
    nondegenerate_sup_iff_average, IsDownwardMinimizer.isUniformlyNondegenerateNear⟩

/-- Challenge: non-degeneracy of local largest subsolutions in `d = 2` (Abedin–Feldman–Stinson,
Theorem B.1, after Orcan-Ekmekci). -/
theorem challenge_nondegeneracy_largest_sub_2d : LargestSubNondeg2DStatement :=
  isNondegenerateAt_of_isLocalLargestSub

/-- Challenge: quantitative non-degeneracy, with constants depending only on the data: local
smallest supersolutions (`q₀ / (8d)`), downward minimizers (`q₀ / (8 d e^{d/2})`), and local
largest subsolutions in `d = 2` (`c(q₀, K)`). -/
theorem challenge_nondegeneracy_quant :
    SmallestSuperNondegQuantStatement ∧ DownwardNondegQuantStatement ∧
      LargestSubNondeg2DQuantStatement :=
  ⟨IsLocalSmallestSuper.exists_le_of_closedBall_subset,
    IsDownwardMinimizer.exists_le_of_closedBall_subset, exists_pos_le_of_isLocalLargestSub⟩

/-- Challenge: the exterior-ball lemma with domain and exterior ball of the same radius
(Abedin–Feldman–Stinson, Lemma B.2). -/
theorem challenge_exterior_ball_same_radius : ExteriorBallSameRadiusStatement :=
  exists_le_of_exteriorBall_sameRadius'

/-! ### De Silva's flatness theory -/

/-- Challenge: De Silva's Harnack inequality for flat solutions. -/
theorem challenge_flat_harnack : FlatHarnackStatement := flat_harnack

/-- Challenge: De Silva's improvement of flatness. -/
theorem challenge_improvement : ImprovementStatement := improvement_of_flatness

/-- Challenge: flat free boundaries are `C^{1,γ}` graphs, and flat solutions are classical. -/
theorem challenge_flat_regularity : FlatGraphStatement ∧ FlatClassicalStatement :=
  ⟨isC1GammaHypersurfaceNear_of_flat, isClassicalNear_of_flat⟩

/-! ### Classical solutions and blow-up classification -/

/-- Challenge: classical solutions are viscosity solutions. -/
theorem challenge_classical_visc : ClassicalViscStatement := IsClassicalSolution.isViscSolution

/-- Challenge: classical solutions satisfy the inner-variation identity. -/
theorem challenge_classical_inner_variation : ClassicalInnerVarStatement :=
  IsClassicalSolution.integral_innerVarIntegrand_eq_zero

/-- Challenge: the Alt–Caffarelli gradient bound, with a modulus depending on the Lipschitz
bound. -/
theorem challenge_classical_lipschitz_bound : ClassicalLipschitzBoundStatement :=
  classical_lipschitz_bound

/-- Challenge: planar classification of 1-homogeneous inner variational solutions. -/
theorem challenge_planar_classification : PlanarHomogeneousClassificationStatement :=
  classification_homogeneous_planar

end EllipticBernoulli.Comparator
