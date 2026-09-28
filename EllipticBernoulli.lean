/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Common.Calculus
public import EllipticBernoulli.Basic.KLimit
public import EllipticBernoulli.Basic.Setting
public import EllipticBernoulli.Basic.Sobolev
public import EllipticBernoulli.Basic.Touching
public import EllipticBernoulli.Classical.BlowupExtraction
public import EllipticBernoulli.Classical.Gradient
public import EllipticBernoulli.Classical.GradientBound
public import EllipticBernoulli.Classical.HalfSpace
public import EllipticBernoulli.Classical.InnerVariation
public import EllipticBernoulli.Classical.InnerVariationCalculus
public import EllipticBernoulli.Classical.InnerVariationCore
public import EllipticBernoulli.Classical.Modulus
public import EllipticBernoulli.Classical.OneDim
public import EllipticBernoulli.Classical.Rigidity
public import EllipticBernoulli.Classical.Viscosity
public import EllipticBernoulli.Defs.Regularity
public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Viscosity
public import EllipticBernoulli.Flatness.Barriers
public import EllipticBernoulli.Flatness.Classical
public import EllipticBernoulli.Flatness.Graph
public import EllipticBernoulli.Flatness.GraphAux
public import EllipticBernoulli.Flatness.Harnack
public import EllipticBernoulli.Flatness.Improvement
public import EllipticBernoulli.Flatness.Iteration
public import EllipticBernoulli.Flatness.Linearized
public import EllipticBernoulli.Flatness.LinearizedLimit
public import EllipticBernoulli.Flatness.MovingCompactness
public import EllipticBernoulli.Flatness.TestCalculus
public import EllipticBernoulli.Flatness.LinearizedRegularity
public import EllipticBernoulli.Flatness.OneStep
public import EllipticBernoulli.Harmonic.Basic
public import EllipticBernoulli.Harmonic.Comparison
public import EllipticBernoulli.Harmonic.DirichletBall
public import EllipticBernoulli.Harmonic.GradientEstimate
public import EllipticBernoulli.Harmonic.Harnack
public import EllipticBernoulli.Harmonic.Limit
public import EllipticBernoulli.Harmonic.Liouville
public import EllipticBernoulli.Harmonic.MaxPrinciple
public import EllipticBernoulli.Harmonic.MeanValue
public import EllipticBernoulli.Harmonic.Radial
public import EllipticBernoulli.Harmonic.StrongMax
public import EllipticBernoulli.Harmonic.SubMeanValue
public import EllipticBernoulli.Harmonic.ViscosityHarmonic
public import EllipticBernoulli.Harmonic.WeylWeakGradient
public import EllipticBernoulli.Lipschitz.Barrier
public import EllipticBernoulli.Lipschitz.Estimate
public import EllipticBernoulli.Lipschitz.LinearGrowth
public import EllipticBernoulli.Nondegeneracy.Barriers
public import EllipticBernoulli.Nondegeneracy.Equivalences
public import EllipticBernoulli.Nondegeneracy.ExteriorBall
public import EllipticBernoulli.Nondegeneracy.LargestSub2D
public import EllipticBernoulli.Nondegeneracy.Minimizer
public import EllipticBernoulli.Nondegeneracy.Planar.CircleMean
public import EllipticBernoulli.Nondegeneracy.Planar.LargestSub
public import EllipticBernoulli.Nondegeneracy.Planar.PlanarGreen
public import EllipticBernoulli.Nondegeneracy.Planar.RieszMeasure
public import EllipticBernoulli.Nondegeneracy.SmallestSuper
public import EllipticBernoulli.Registry.README
public import EllipticBernoulli.Regularity.BoundaryPoincare
public import EllipticBernoulli.Regularity.Caccioppoli
public import EllipticBernoulli.Regularity.Cutoff
public import EllipticBernoulli.Regularity.DeGiorgi
public import EllipticBernoulli.Regularity.DeGiorgiSeq
public import EllipticBernoulli.Regularity.InteriorCaccioppoli
public import EllipticBernoulli.Regularity.InteriorObstacle
public import EllipticBernoulli.Regularity.InteriorOscillation
public import EllipticBernoulli.Regularity.Isoperimetric
public import EllipticBernoulli.Regularity.Iteration
public import EllipticBernoulli.Regularity.ObstacleBoundary
public import EllipticBernoulli.Regularity.ObstacleCaccioppoli
public import EllipticBernoulli.Regularity.Oscillation
public import EllipticBernoulli.Regularity.Representative
public import EllipticBernoulli.Sobolev.BallAverage
public import EllipticBernoulli.Sobolev.Closure
public import EllipticBernoulli.Sobolev.Compactness
public import EllipticBernoulli.Sobolev.Cutoff
public import EllipticBernoulli.Sobolev.Energy
public import EllipticBernoulli.Sobolev.FrechetKolmogorov
public import EllipticBernoulli.Sobolev.IBP
public import EllipticBernoulli.Sobolev.L2
public import EllipticBernoulli.Sobolev.L2Inner
public import EllipticBernoulli.Sobolev.Lattice
public import EllipticBernoulli.Sobolev.Lipschitz
public import EllipticBernoulli.Sobolev.LocalCompactness
public import EllipticBernoulli.Sobolev.Mollify
public import EllipticBernoulli.Sobolev.Poincare
public import EllipticBernoulli.Sobolev.RayPoincare
public import EllipticBernoulli.Sobolev.SobolevGNS
public import EllipticBernoulli.Sobolev.SobolevInequality
public import EllipticBernoulli.Sobolev.SobolevOne
public import EllipticBernoulli.Sobolev.TranslationEstimate
public import EllipticBernoulli.Sobolev.Uniqueness
public import EllipticBernoulli.Sobolev.WeakCompactness
public import EllipticBernoulli.Sobolev.ZeroExtension
public import EllipticBernoulli.Statements.Classical
public import EllipticBernoulli.Statements.Flatness
public import EllipticBernoulli.Statements.Harmonic
public import EllipticBernoulli.Statements.Lipschitz
public import EllipticBernoulli.Statements.Nondegeneracy
public import EllipticBernoulli.Statements.Variational
public import EllipticBernoulli.Statements.Viscosity
public import EllipticBernoulli.Variational.Continuity
public import EllipticBernoulli.Variational.Existence
public import EllipticBernoulli.Variational.OneSided
public import EllipticBernoulli.Variational.Perturbation
public import EllipticBernoulli.Variational.PerturbationCalculus
public import EllipticBernoulli.Viscosity.Affine
public import EllipticBernoulli.Viscosity.Basic
public import EllipticBernoulli.Viscosity.Calculus
public import EllipticBernoulli.Viscosity.Harmonic
public import EllipticBernoulli.Viscosity.Jet
public import EllipticBernoulli.Viscosity.KLimit
public import EllipticBernoulli.Viscosity.Lattice
public import EllipticBernoulli.Viscosity.Local
public import EllipticBernoulli.Viscosity.Stability
public import EllipticBernoulli.Statements.Blowup
public import EllipticBernoulli.Blowup.PlanarClassification
public import EllipticBernoulli.Blowup.Constancy
public import EllipticBernoulli.Blowup.Flux
public import EllipticBernoulli.Blowup.Homogeneous

/-!
# EllipticBernoulli

Root module: publicly imports every public module of the library.

* `Common/*`, `Basic/*`, `Defs/*`: the vocabulary (setting, Sobolev notions and energies,
  viscosity, variational and regularity notions).
* `Statements/*`: the headline statements, one `Prop` per result.
* `Harmonic/*`, `Viscosity/*`, `Sobolev/*`: the harmonic, viscosity and Sobolev toolkits.
* `Variational/*`, `Regularity/*`: the direct method, De Giorgi continuity of obstacle minimizers,
  energy-decreasing perturbations and one-sided minimizers.
* `Lipschitz/*`, `Nondegeneracy/*`: the Lipschitz estimate and non-degeneracy.
* `Flatness/*`: De Silva's flatness theory, up to classical regularity.
* `Classical/*`: classical solutions.
* `Blowup/*`: the classification of planar 1-homogeneous inner variational solutions.
* `Registry/*`: reserved for results assumed without proof (there are none).
-/
