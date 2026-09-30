/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import EllipticBernoulli.Lipschitz.Barrier
import EllipticBernoulli.Harmonic.Harnack
import EllipticBernoulli.Viscosity.Basic

/-!
# Linear growth away from the zero set (Caffarelli–Salsa, Lemma 11.19)

This is Step 1 of the Lipschitz estimate (`Lipschitz/Estimate.lean`). Let `u` be a viscosity
supersolution in `U` (Abedin–Feldman–Stinson, Definition 2.1(i)), harmonic in
`B_δ(x)`, and let `y ∈ ∂B_δ(x)` be a zero of `u`. Then `u(x) ≤ C₁(d) Q(y) δ`
(`exists_le_mul_of_isViscSuper_sphere`).

**Proof.** By Harnack (`harnack_ball`), `u ≥ u(x)/C` on `B_{δ/2}(x)`. The Gaussian barrier
`Φ = radialSubBarrier x δ λ A` (`Lipschitz/Barrier.lean`) with `λ = 8(d+1)/δ²` is strictly
subharmonic on `{|z - x| ≥ δ/4}`, vanishes on `∂B_δ(x)` and is `≤ 0` outside; `A` is chosen so
that `Φ = u(x)/C` on `∂B_{δ/4}(x)`. On the closed annulus `δ/4 ≤ |z - x| ≤ δ`, `u - Φ ≥ 0` on
the boundary and has no interior negative minimum (there `Δ(u - Φ) = -ΔΦ < 0`, while
`laplacian_nonneg_of_isLocalMin`), so `Φ ≤ u` there, hence near `y`. So `Φ` touches `u` from below
at `y`; since `ΔΦ(y) > 0` the supersolution property forces `|∇Φ(y)| ≤ Q(y)`, which is the
claim. Only a *strict* minimum principle is needed, so no comparison theorem is used.

Corollary (`exists_le_mul_of_isViscSuper`): if `u` is harmonic in `{u > 0}`, `Q ≤ Qmax` on
`B̄_ρ(x) ⊆ U` and `u` vanishes somewhere in `B̄_ρ(x)`, then `u(x) ≤ C₁ Qmax ρ`.

Dimension: `1 ≤ d`, inherited from `HarnackStatement`.

## References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Nearest zero.** If `u ≥ 0` is continuous on `U ⊇ B̄_ρ(x)`, `u(x) > 0` and `u` vanishes
somewhere in `B̄_ρ(x)`, then there is a zero `y ∈ B̄_ρ(x)` with `u > 0` on `B_{|y - x|}(x)`. -/
theorem exists_nearest_zero {U : Set (E d)} {u : E d → ℝ} (hc : ContinuousOn u U)
    (hnn : ∀ z ∈ U, 0 ≤ u z) {x : E d} {ρ : ℝ} (hρU : closedBall x ρ ⊆ U) (hux : 0 < u x)
    (hZ : ∃ y ∈ closedBall x ρ, u y = 0) :
    ∃ y ∈ closedBall x ρ, u y = 0 ∧ 0 < dist y x ∧ ∀ z ∈ ball x (dist y x), 0 < u z := by
  set Z := closedBall x ρ ∩ u ⁻¹' {0} with hZdef
  have hZc : IsClosed Z :=
    (hc.mono hρU).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton
  have hZk : IsCompact Z := (isCompact_closedBall x ρ).of_isClosed_subset hZc inter_subset_left
  obtain ⟨y₀, hy₀, hy₀0⟩ := hZ
  obtain ⟨y, ⟨hyB, hy0⟩, hmin⟩ :=
    hZk.exists_isMinOn ⟨y₀, hy₀, hy₀0⟩ (continuous_id.dist continuous_const).continuousOn
  have hy0' : u y = 0 := hy0
  refine ⟨y, hyB, hy0', dist_pos.2 fun h ↦ by rw [h] at hy0'; linarith, fun z hz ↦ ?_⟩
  have hzB : z ∈ closedBall x ρ :=
    mem_closedBall.2 ((mem_ball.1 hz).le.trans (mem_closedBall.1 hyB))
  refine lt_of_le_of_ne (hnn z (hρU hzB)) fun h ↦ ?_
  have := hmin ⟨hzB, h.symm⟩
  simp only [id] at this
  exact absurd (mem_ball.1 hz) (not_lt.2 this)

/-- **Linear growth at a boundary zero** (Caffarelli–Salsa, Lemma 11.19; Step 1). For `1 ≤ d` there
is `C₁ ≥ 0` such that: if `u` is a viscosity supersolution in `U`, harmonic in `B_δ(x)`, with
`u(x) > 0`, `B̄_δ(x) ⊆ U`, and `u(y) = 0` for some `y` with `|y - x| = δ`, then
`u(x) ≤ C₁ Q(y) δ`. -/
theorem exists_le_mul_of_isViscSuper_sphere (hd : 1 ≤ d) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (U : Set (E d)) (Q u : E d → ℝ) (x y : E d) (δ : ℝ),
      IsViscSuper U Q u → HarmonicOnNhd u (ball x δ) → 0 < δ → closedBall x δ ⊆ U →
      0 < u x → dist y x = δ → u y = 0 → u x ≤ C₁ * Q y * δ := by
  obtain ⟨CH, hCH⟩ := harnack_ball hd
  set C := max CH 1 with hCdef
  have hC : 0 < C := lt_of_lt_of_le one_pos (le_max_right _ _)
  set μ : ℝ := 8 * ((d : ℝ) + 1) with hμ
  have hμ0 : 0 < μ := by positivity
  set E₁ := Real.exp (-(μ / 16)) with hE₁
  set E₂ := Real.exp (-μ) with hE₂
  have hE₂0 : 0 < E₂ := Real.exp_pos _
  set D := E₁ - E₂ with hD
  have hD0 : 0 < D := sub_pos.2 (Real.exp_lt_exp.2 (by linarith))
  refine ⟨C * D / (2 * μ * E₂), by positivity, ?_⟩
  intro U Q u x y δ hu hh hδ hδU hux hyx huy
  have hnn : ∀ z ∈ U, 0 ≤ u z := hu.2.1
  -- Harnack: `u x ≤ C u z` on `B_{δ/2}(x)`
  have hharn : ∀ z ∈ ball x (δ / 2), u x ≤ C * u z := by
    intro z hz
    have h2 : 2 * (δ / 2) = δ := by ring
    have hh' : HarmonicOnNhd u (ball x (2 * (δ / 2))) := by rwa [h2]
    have hnn' : ∀ w ∈ ball x (2 * (δ / 2)), 0 ≤ u w := fun w hw ↦
      hnn w (hδU (ball_subset_closedBall (by rwa [h2] at hw)))
    have := hCH u x (δ / 2) (by positivity) hh' hnn' x (mem_ball_self (by positivity)) z hz
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (hnn z (hδU (ball_subset_closedBall (ball_subset_ball (by linarith) hz)))))
  -- the barrier
  set lam := μ / δ ^ 2 with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamδ : lam * δ ^ 2 = μ := by rw [hlam]; field_simp
  set A := u x / (C * D) with hA
  have hA0 : 0 < A := by positivity
  have hAuD : A * (C * D) = u x := div_mul_cancel₀ _ (by positivity)
  set Φ := radialSubBarrier x δ lam A with hΦ
  have hΦs : ContDiff ℝ ∞ Φ := contDiff_radialSubBarrier
  have hΦ2 : ContDiff ℝ 2 Φ := contDiff_radialSubBarrier
  have hΦin : ∀ z : E d, ‖z - x‖ = δ / 4 → Φ z = u x / C := by
    intro z hz
    rw [hΦ, radialSubBarrier_apply, hz, hlamδ]
    have : lam * (δ / 4) ^ 2 = μ / 16 := by rw [← hlamδ]; ring
    rw [this, ← hE₁, ← hE₂, ← hD, hA]
    field_simp
  have hΦlap : ∀ z : E d, δ / 4 ≤ ‖z - x‖ → 0 < Δ Φ z := by
    intro z hz
    refine laplacian_radialSubBarrier_pos hA0 hlam0 ?_
    have h1 : (δ / 4) ^ 2 ≤ ‖z - x‖ ^ 2 := pow_le_pow_left₀ (by positivity) hz 2
    have h2 : 2 * lam * (δ / 4) ^ 2 = μ / 8 := by rw [← hlamδ]; ring
    have h3 : 2 * lam * (δ / 4) ^ 2 ≤ 2 * lam * ‖z - x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [hμ] at h2
    linarith
  -- strict minimum principle on the closed annulus
  have hann : ∀ z ∈ U, δ / 4 ≤ ‖z - x‖ → Φ z ≤ u z := by
    intro z hzU hz
    rcases le_or_gt δ ‖z - x‖ with hzδ | hzδ
    · exact (radialSubBarrier_nonpos hA0.le hlam0.le hδ.le hzδ).trans (hnn z hzU)
    by_contra hneg
    rw [not_le] at hneg
    set K := closedBall x δ \ ball x (δ / 4) with hK
    have hKk : IsCompact K := (isCompact_closedBall x δ).diff isOpen_ball
    have hzK : z ∈ K := ⟨mem_closedBall_iff_norm.2 hzδ.le, fun h ↦
      absurd (mem_ball_iff_norm.1 h) (not_lt.2 hz)⟩
    have hwc : ContinuousOn (u - Φ) K :=
      (hu.1.mono (sdiff_subset.trans hδU)).sub hΦs.continuous.continuousOn
    obtain ⟨z₀, hz₀K, hmin⟩ := hKk.exists_isMinOn ⟨z, hzK⟩ hwc
    have hw0 : u z₀ - Φ z₀ < 0 := by
      have := hmin hzK
      simp only [Pi.sub_apply, mem_ofPred_eq] at this
      linarith
    have hz₀U : z₀ ∈ U := hδU hz₀K.1
    have hr₁ : ‖z₀ - x‖ ≤ δ := mem_closedBall_iff_norm.1 hz₀K.1
    have hr₂ : δ / 4 ≤ ‖z₀ - x‖ := not_lt.1 fun h ↦ hz₀K.2 (mem_ball_iff_norm.2 h)
    rcases hr₁.lt_or_eq with hr₁ | hr₁
    · rcases hr₂.lt_or_eq with hr₂ | hr₂
      · -- interior point: `Δ(u - Φ) < 0` contradicts the minimum
        have hz₀b : z₀ ∈ ball x δ := mem_ball_iff_norm.2 hr₁
        have hH := hh z₀ hz₀b
        have hopen : IsOpen {w : E d | δ / 4 < ‖w - x‖ ∧ ‖w - x‖ < δ} :=
          (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
            (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
        have hloc : IsLocalMin (u - Φ) z₀ := by
          filter_upwards [hopen.mem_nhds ⟨hr₂, hr₁⟩] with w hw
          exact hmin ⟨mem_closedBall_iff_norm.2 hw.2.le,
            fun h ↦ absurd (mem_ball_iff_norm.1 h) (not_lt.2 hw.1.le)⟩
        have h1 := laplacian_nonneg_of_isLocalMin hloc (hH.1.sub hΦ2.contDiffAt)
        rw [hH.1.laplacian_sub hΦ2.contDiffAt, hH.2.self_of_nhds] at h1
        have h2 := hΦlap z₀ hr₂.le
        simp only [Pi.zero_apply] at h1
        linarith
      · -- inner sphere: Harnack
        have hz₀b : z₀ ∈ ball x (δ / 2) := mem_ball_iff_norm.2 (by rw [← hr₂]; linarith)
        have h1 := hharn z₀ hz₀b
        have h2 := hΦin z₀ hr₂.symm
        rw [h2] at hw0
        have : u x / C ≤ u z₀ := by rw [div_le_iff₀ hC, mul_comm]; exact h1
        linarith
    · -- outer sphere: `Φ = 0 ≤ u`
      have := radialSubBarrier_eq_zero (lam := lam) (A := A) hr₁
      rw [← hΦ] at this
      rw [this] at hw0
      linarith [hnn z₀ hz₀U]
  -- `Φ` touches `u` from below at `y`
  have hyx' : ‖y - x‖ = δ := by rw [← dist_eq_norm]; exact hyx
  have hyU : y ∈ U := hδU (mem_closedBall.2 hyx.le)
  have hΦy : Φ y = 0 := radialSubBarrier_eq_zero hyx'
  have htouch : TouchesBelow Φ u U y := by
    refine ⟨hyU, by rw [hΦy, huy], ?_⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds y (by positivity : 0 < 3 * δ / 4)] with w hw hwU
    refine hann w hwU ?_
    have h1 : ‖w - y‖ < 3 * δ / 4 := mem_ball_iff_norm.1 hw
    have h2 : ‖y - x‖ ≤ ‖w - y‖ + ‖w - x‖ := by
      calc ‖y - x‖ = ‖(w - x) - (w - y)‖ := by congr 1; abel
        _ ≤ ‖w - x‖ + ‖w - y‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  rcases hu.2.2 Φ hΦs y hyU htouch with hlap | ⟨-, hgrad⟩
  · exact absurd hlap (not_le.2 (hΦlap y (by rw [hyx']; linarith)))
  rw [hΦ, norm_gradient_radialSubBarrier hlam0.le, hyx', abs_of_pos hA0] at hgrad
  -- `2 A λ δ e^{-λδ²} ≤ Q y`, i.e. `2 A μ E₂ ≤ Q y δ`
  have hexp : Real.exp (-(lam * δ ^ 2)) = E₂ := by rw [hlamδ]
  rw [hexp] at hgrad
  have h1 : 2 * A * μ * E₂ ≤ Q y * δ := by
    have := mul_le_mul_of_nonneg_right hgrad hδ.le
    calc 2 * A * μ * E₂ = 2 * A * lam * δ * E₂ * δ := by rw [← hlamδ]; ring
      _ ≤ Q y * δ := this
  have key : 2 * μ * E₂ * u x ≤ C * D * (Q y * δ) := by
    rw [← hAuD]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ C * D)
    exact le_of_eq_of_le (by ring) this
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- **Linear growth near the zero set** (Caffarelli–Salsa, Lemma 11.19; Step 1, ball form).
For `1 ≤ d` there is `C₁ ≥ 0` such that: if `u` is a
viscosity supersolution in `U`, harmonic in `{u > 0}`, `B̄_ρ(x) ⊆ U`, `Q ≤ Qmax` on `B̄_ρ(x)`
with `0 ≤ Qmax`, and `u` vanishes somewhere in `B̄_ρ(x)`, then `u(x) ≤ C₁ Qmax ρ`. -/
theorem exists_le_mul_of_isViscSuper (hd : 1 ≤ d) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (U : Set (E d)) (Q u : E d → ℝ) (x : E d) (ρ Qmax : ℝ),
      IsOpen U → IsViscSuper U Q u → HarmonicOnNhd u (posSet u U) → closedBall x ρ ⊆ U →
      (∀ y ∈ closedBall x ρ, Q y ≤ Qmax) → 0 ≤ Qmax → (∃ y ∈ closedBall x ρ, u y = 0) →
      u x ≤ C₁ * Qmax * ρ := by
  obtain ⟨C₁, hC₁, hA⟩ := exists_le_mul_of_isViscSuper_sphere hd
  refine ⟨C₁, hC₁, ?_⟩
  intro U Q u x ρ Qmax hU hu hh hρU hQ hQmax hZ
  obtain ⟨y₀, hy₀, -⟩ := id hZ
  have hρ : 0 ≤ ρ := dist_nonneg.trans (mem_closedBall.1 hy₀)
  rcases (hu.2.1 x (hρU (mem_closedBall_self hρ))).lt_or_eq with hux | hux
  swap
  · rw [← hux]; positivity
  obtain ⟨y, hyB, huy, hδ, hpos⟩ := exists_nearest_zero hu.1 hu.2.1 hρU hux hZ
  set δ := dist y x
  have hδρ : δ ≤ ρ := mem_closedBall.1 hyB
  have hδU : closedBall x δ ⊆ U := (closedBall_subset_closedBall hδρ).trans hρU
  have hh' : HarmonicOnNhd u (ball x δ) := fun z hz ↦
    hh z ⟨hδU (ball_subset_closedBall hz), hpos z hz⟩
  have h1 := hA U Q u x y δ hu hh' hδ hδU hux rfl huy
  calc u x ≤ C₁ * Q y * δ := h1
    _ ≤ C₁ * Qmax * δ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hQ y hyB) hC₁) hδ.le
    _ ≤ C₁ * Qmax * ρ := mul_le_mul_of_nonneg_left hδρ (by positivity)

end EllipticBernoulli
