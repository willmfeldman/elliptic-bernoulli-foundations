/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Nondegeneracy
import EllipticBernoulli.Nondegeneracy.Barriers
import EllipticBernoulli.Viscosity.Local

/-!
# Non-degeneracy of subsolutions at outer-regular points (Abedin–Feldman–Stinson, Lemma B.2)

* `exists_le_of_exteriorBall` (`ExteriorBallNondegStatement`): a viscosity subsolution in
  `B_{4s}(x₀)` with `Q ≥ q₀ > 0` and an exterior touching ball `B_s(p)` at the free boundary
  point `x₀` satisfies `sup_{B_{4s}(x₀)} v ≥ q₀ s / (32 d e^{3d})`.
* `exists_le_of_exteriorBall_sameRadius`: the form of Lemma B.2 itself, with exterior ball and
  domain of the same radius `s`, and constant `q₀ / (128 d e^{3d})`;
  `exists_le_of_exteriorBall_sameRadius'` restates it as `ExteriorBallSameRadiusStatement`. The
  source gives no explicit constant.

## Proof

The radial barrier `H = A (1 - exp(-λ(|y - p|² - s²)))` (`expProfile`), `λ = 4d/s²`,
`A = q₀ s / (16 d e^{3d})`, is strictly superharmonic off `B_{s/2}(p)`, with `|∇H| ≤ q₀/2` where
`H ≤ 0`. If `v < A/2` on `B_{4s}(x₀)`, then `v ≤ H₊` off `K = B̄_{3s}(x₀) \ B_{s/2}(p)`, hence on
`K` by comparison with strict barriers (`IsViscSub.le_max_of_barrier`); so `H₊` touches `v` from
above at `x₀`, where `ΔH < 0` and `|∇H| < Q`, contradicting the subsolution property.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
  in the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Abedin–Feldman–Stinson, Lemma B.2**, quantitative form with domain `B_{4s}(x₀)`
(`ExteriorBallNondegStatement`): `c = q₀ / (32 d e^{3d})`. Assumes `1 ≤ d`. -/
theorem exists_le_of_exteriorBall : ExteriorBallNondegStatement := by
  intro d hd Q v x₀ p s q₀ hs hq₀ hv hQ hx₀ hp hext
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set W := ball x₀ (4 * s) with hW
  set lam : ℝ := 4 * d / s ^ 2 with hlam_def
  have hs2 : 0 < s ^ 2 := by positivity
  have hlam : 0 < lam := by positivity
  set eD := Real.exp (3 * d) with heD
  have heD1 : 1 ≤ eD := Real.one_le_exp (by positivity)
  set A : ℝ := q₀ * s / (16 * d * eD) with hA_def
  have hA : 0 < A := by positivity
  set H := expProfile p s lam A with hH_def
  have hHs : ContDiff ℝ ∞ H := contDiff_expProfile
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  -- `c s = A / 2`
  have hcA : q₀ / (32 * d * eD) * s = A / 2 := by rw [hA_def]; field_simp; norm_num
  rw [hcA] at hcon
  set K := closedBall x₀ (3 * s) \ ball p (s / 2) with hK_def
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hKW : K ⊆ W := fun y hy ↦ closedBall_subset_ball (by linarith) hy.1
  have hvx₀ : v x₀ = 0 := eq_zero_of_mem_freeBoundary isOpen_ball hv.1 hv.2.1 hx₀
  -- on `K`, `|y - p| ≥ s/2`
  have hKp : ∀ y ∈ K, s / 2 ≤ ‖y - p‖ := fun y hy ↦ by
    have := hy.2; rw [mem_ball, not_lt, dist_eq_norm] at this; exact this
  have hlap : ∀ y ∈ K, Δ H y < 0 := fun y hy ↦ by
    rw [hH_def, laplacian_expProfile]
    have h1 : s ^ 2 / 4 ≤ ‖y - p‖ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) (hKp y hy) 2; linarith
    have h2 : 2 * (d : ℝ) - 4 * lam * ‖y - p‖ ^ 2 < 0 := by
      have : d ≤ lam * ‖y - p‖ ^ 2 := by
        rw [hlam_def, div_mul_eq_mul_div, le_div_iff₀ hs2]
        linarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ d)]
      linarith
    exact mul_neg_of_pos_of_neg (by positivity) h2
  -- gradient bound where `H ≤ 0`
  have hgradle : ∀ y, s / 2 ≤ ‖y - p‖ → ‖y - p‖ ≤ s → ‖∇ H y‖ ≤ q₀ / 2 := fun y h1 h2 ↦ by
    rw [hH_def, norm_gradient_expProfile]
    have hE : Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) ≤ eD := by
      rw [heD]; refine Real.exp_le_exp.2 ?_
      have : s ^ 2 / 4 ≤ ‖y - p‖ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) h1 2; linarith
      have : lam * (s ^ 2 - ‖y - p‖ ^ 2) ≤ lam * (3 / 4 * s ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hlam.le
      have hl : lam * (3 / 4 * s ^ 2) = 3 * d := by rw [hlam_def]; field_simp
      linarith
    rw [abs_of_nonneg (by positivity)]
    calc A * lam * Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) * (2 * ‖y - p‖)
        ≤ A * lam * eD * (2 * s) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hE (by positivity)) (by linarith) (by positivity)
            (by positivity)
      _ = q₀ / 2 := by rw [hA_def, hlam_def]; field_simp; ring
  have hgrad : ∀ y ∈ K, H y < 0 → ‖∇ H y‖ < Q y := fun y hy hHy ↦ by
    have hlt : ‖y - p‖ < s := by
      by_contra h
      push Not at h
      have : 0 ≤ H y := by
        rw [hH_def]; unfold expProfile
        have : Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have := pow_le_pow_left₀ hs.le h 2
          linarith [mul_nonneg hlam.le (sub_nonneg.2 this)]
        linarith [mul_le_mul_of_nonneg_left this hA.le]
      linarith
    exact (hgradle y (hKp y hy) hlt.le).trans_lt
      (by linarith [hQ y (hKW hy)])
  -- outside `K`
  have hout : ∀ y ∈ W \ K, v y ≤ max (H y) 0 := by
    rintro y ⟨hyW, hyK⟩
    by_cases hyp : y ∈ ball p (s / 2)
    · rw [hext y ⟨ball_subset_ball (by linarith) hyp, hyW⟩]; exact le_max_right _ _
    · have hy3 : 3 * s < ‖y - x₀‖ := by
        by_contra h
        push Not at h
        exact hyK ⟨by rw [mem_closedBall, dist_eq_norm]; exact h, hyp⟩
      have hyp2 : 2 * s < ‖y - p‖ := by
        have := norm_add_le (y - p) (p - x₀)
        rw [sub_add_sub_cancel, norm_sub_rev p x₀, hp] at this
        linarith
      refine (hcon y hyW).le.trans (le_trans ?_ (le_max_left _ _))
      rw [hH_def]; unfold expProfile
      have h4 : 4 * s ^ 2 ≤ ‖y - p‖ ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hyp2.le 2; linarith
      have h12 : 12 ≤ lam * (‖y - p‖ ^ 2 - s ^ 2) := by
        have : lam * (3 * s ^ 2) = 12 * d := by rw [hlam_def]; field_simp; ring
        have : lam * (3 * s ^ 2) ≤ lam * (‖y - p‖ ^ 2 - s ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hlam.le
        linarith
      have hE : Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) ≤ 1 / 2 := by
        have h1 : Real.exp (-(lam * (‖y - p‖ ^ 2 - s ^ 2))) ≤ Real.exp (-1) :=
          Real.exp_le_exp.2 (by linarith)
        have h2 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
          have := Real.add_one_le_exp (1 : ℝ); linarith
        linarith
      linarith [mul_le_mul_of_nonneg_left hE hA.le]
  have hle := hv.le_max_of_barrier (by omega) isOpen_ball hKc hKW (contDiff_two_of_smooth hHs)
    hlap hgrad hout
  -- touching at `x₀`
  have hx₀K : ∀ y ∈ ball x₀ (s / 2), y ∈ K := fun y hy ↦ by
    rw [mem_ball, dist_eq_norm] at hy
    refine ⟨by rw [mem_closedBall, dist_eq_norm]; linarith, fun hyp ↦ ?_⟩
    rw [mem_ball, dist_eq_norm] at hyp
    have := norm_add_le (x₀ - y) (y - p)
    rw [sub_add_sub_cancel, hp, norm_sub_rev x₀ y] at this
    linarith
  have hHx₀ : H x₀ = 0 := expProfile_eq_zero hp
  have htouch : TouchesAbove (fun y ↦ max (H y) 0) v (closure (posSet v W) ∩ W) x₀ := by
    refine ⟨⟨frontier_subset_closure hx₀.1, mem_ball_self (by positivity)⟩,
      by simp only [hHx₀, max_self, hvx₀], ?_⟩
    refine mem_nhdsWithin_of_mem_nhds (Filter.mem_of_superset (ball_mem_nhds x₀ (by positivity))
      fun y hy ↦ hle y (hx₀K y hy))
  rcases hv.2.2 H hHs x₀ htouch with h1 | ⟨-, h2⟩
  · have := hlap x₀ (hx₀K x₀ (mem_ball_self (by positivity)))
    linarith
  · have h3 := hgradle x₀ (by rw [hp]; linarith) hp.le
    have := hQ x₀ (mem_ball_self (by positivity))
    linarith

/-- **Abedin–Feldman–Stinson, Lemma B.2**, in its original form:
exterior touching ball and domain of the same radius `s` (the source takes `s = 1`), with
`c = q₀ / (128 d e^{3d})`. The conclusion is for the supremum over the open ball `B_s(x₀)`; the
source's `max_{∂B_1} u` presumes `u` defined up to `∂B_1`. Proof: the exterior ball
`B_{s/4}(p')`, `p' = x₀ + (p - x₀)/4`, lies inside `B_s(p)`; apply `exists_le_of_exteriorBall`
with radius `s/4`. Assumes `1 ≤ d`. -/
theorem exists_le_of_exteriorBall_sameRadius (hd : 1 ≤ d) {Q v : E d → ℝ} {x₀ p : E d}
    {s q₀ : ℝ} (hs : 0 < s) (hq₀ : 0 < q₀) (hv : IsViscSub (ball x₀ s) Q v)
    (hQ : ∀ y ∈ ball x₀ s, q₀ ≤ Q y) (hx₀ : x₀ ∈ freeBoundary v (ball x₀ s))
    (hp : ‖x₀ - p‖ = s) (hext : ∀ y ∈ ball p s ∩ ball x₀ s, v y = 0) :
    ∃ y ∈ ball x₀ s, q₀ / (128 * d * Real.exp (3 * d)) * s ≤ v y := by
  set p' : E d := x₀ + (1 / 4 : ℝ) • (p - x₀) with hp'
  have h4 : 4 * (s / 4) = s := by ring
  have hp'n : ‖x₀ - p'‖ = s / 4 := by
    rw [hp', sub_add_cancel_left, norm_neg, norm_smul, ← norm_neg (p - x₀), neg_sub, hp]
    norm_num; ring
  have hp'p : ‖p' - p‖ = 3 * s / 4 := by
    have : p' - p = (3 / 4 : ℝ) • (x₀ - p) := by
      rw [hp']; module
    rw [this, norm_smul, hp]; norm_num; ring
  have hsub : ball p' (s / 4) ⊆ ball p s := fun y hy ↦ by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have := norm_add_le (y - p') (p' - p)
    rw [sub_add_sub_cancel] at this
    linarith
  obtain ⟨y, hy, hle⟩ := exists_le_of_exteriorBall hd (by positivity : 0 < s / 4) hq₀
    (by rwa [h4]) (by rwa [h4]) (by rwa [h4]) hp'n
    (fun y hy ↦ hext y ⟨hsub hy.1, by rw [← h4]; exact hy.2⟩)
  refine ⟨y, by rwa [h4] at hy, le_of_eq_of_le ?_ hle⟩
  field_simp
  ring

/-- **Exterior-ball non-degeneracy, same radius** (`ExteriorBallSameRadiusStatement`;
Abedin–Feldman–Stinson, Lemma B.2, in its original form): the statement of
`exists_le_of_exteriorBall_sameRadius`, with `c = q₀ / (128 d e^{3d})`. -/
theorem exists_le_of_exteriorBall_sameRadius' : ExteriorBallSameRadiusStatement :=
  fun hd ↦ exists_le_of_exteriorBall_sameRadius hd

end EllipticBernoulli
