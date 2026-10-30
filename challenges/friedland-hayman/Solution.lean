module

public import EllipticBernoulli.Sphere.CapInequality

/-!
# Solution: the Friedland–Hayman inequality

Discharges the challenge through the library module imported above: `friedlandHayman`
(`FriedlandHaymanStatement`).

## References

* S. Friedland, W. K. Hayman, *Eigenvalue inequalities for the Dirichlet problem on spheres and the
  growth of subharmonic functions*, Comment. Math. Helv. 51 (1976), 133–161.
-/

@[expose] public noncomputable section

open Metric

namespace EllipticBernoulli

theorem challenge_friedlandHayman {d : ℕ} (hd : 2 ≤ d) (Γ₁ Γ₂ : Set (sphere (0 : E d) 1))
    (hΓ₁ : IsOpen Γ₁) (hΓ₂ : IsOpen Γ₂) (hne₁ : Γ₁.Nonempty) (hne₂ : Γ₂.Nonempty)
    (hdisj : Disjoint Γ₁ Γ₂) :
    2 ≤ sphExponent Γ₁ + sphExponent Γ₂ :=
  friedlandHayman d hd Γ₁ Γ₂ hΓ₁ hΓ₂ hne₁ hne₂ hdisj

end EllipticBernoulli
