/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Flatness
public import EllipticBernoulli.Flatness.Linearized
import EllipticBernoulli.Flatness.LinearizedLimit
import EllipticBernoulli.Flatness.LinearizedRegularity

/-!
# De Silva's improvement of flatness

De Silva (2011), Lemma 4.1, with `f = 0`, `a_{ij} = δ_{ij}`, `g = Q`.

* `norm_le_of_linearized_taylor`: the tangential gradient `p` of a bounded solution of the
  linearized problem is bounded, `‖p‖ ≤ 16 + C₀` (De Silva's `|ν̃| ≤ C̃`).
* `eventually_forall_abs_le_of_tendsto`: the pointwise convergence of `linearized_limit` upgrades,
  on a compact set, to a uniform bound for large `k` (De Silva's "for `k` large enough").
* `improve_of_approx`: Step 3 of Lemma 4.1 for a single solution, with two corrections to
  De Silva: the normalization `ν = (e + ε p)/√(1 + ε²|p|²)` (De Silva's `ν` is not a unit vector)
  and the passage from `Ω_r(u)` to `B_r` across the zero phase by `le_of_le_on_closure_posSet`,
  using the linear approximation (4.9) on `Ω_{2r}(u)` (a step De Silva leaves unjustified).
* `improvement_of_flatness : ImprovementStatement` (`|Q - 1| ≤ ε²`, `‖ν - e‖ ≤ C ε`; De Silva's
  display (4.2) prints `|ν − e_n| ≤ C ε²`, but the proof gives `C ε`), by contradiction: a
  sequence of counterexamples with `ε k → 0`, a subsequence with `e k → e₀` (compactness of the
  unit sphere), `linearized_limit`, `linearized_C2_at_origin`, the uniform upgrade and
  `improve_of_approx`. The constants are `r₀ = min(1/16, 1/(4(9C₀ + 1)))`
  and `C = 2 (17 + C₀)`, with `C₀` from `linearized_C2_at_origin`.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **The tangential gradient of the linearized limit is bounded** (De Silva (2011), Lemma 4.1,
Step 3: `|ν̃| ≤ C̃`). If `|w| ≤ 1` on `halfBall e (1/2)`, `w 0 = 0`, `⟪p, e⟫ = 0` and
`|w x - w 0 - ⟪p, x⟫| ≤ C₀ r²` on `B_r ∩ {⟪x, e⟫ ≥ 0}` for `r < 1/4`, then `‖p‖ ≤ 16 + C₀`. -/
theorem norm_le_of_linearized_taylor {w : E d → ℝ} {e p : E d} {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hw1 : ∀ x ∈ halfBall e (1 / 2), |w x| ≤ 1) (hw0 : w 0 = 0) (hpe : ⟪p, e⟫ = 0)
    (hp : ∀ r ∈ Ioo (0 : ℝ) (1 / 4), ∀ x ∈ ball (0 : E d) r, ⟪x, e⟫ ≥ 0 →
      |w x - w 0 - ⟪p, x⟫| ≤ C₀ * r ^ 2) :
    ‖p‖ ≤ 16 + C₀ := by
  rcases eq_or_ne p 0 with h0 | h0
  · rw [h0, norm_zero]; linarith
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 h0
  set x : E d := (1 / (16 * ‖p‖)) • p with hx
  have hxn : ‖x‖ = 1 / 16 := by
    rw [hx, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hxe : ⟪x, e⟫ = 0 := by rw [hx, inner_smul_left, hpe, mul_zero]
  have hpx : ⟪p, x⟫ = ‖p‖ / 16 := by
    rw [hx, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hxb : x ∈ ball (0 : E d) (1 / 8) := by
    rw [mem_ball, dist_zero_right, hxn]; norm_num
  have h1 := hp (1 / 8) ⟨by norm_num, by norm_num⟩ x hxb hxe.ge
  have h2 := hw1 x ⟨hxe.ge, ball_subset_ball (by norm_num) hxb⟩
  rw [hw0, sub_zero, hpx] at h1
  have h3 := (abs_le.1 h1).1
  have h4 := (abs_le.1 h2).2
  linarith

/-- **Uniform upgrade of pointwise convergence on a compact set.** Suppose that along every
subsequence `ψ` and every sequence `y k ∈ D (ψ k) ∩ S` converging to `x ∈ S` the values
`F (ψ k) (y k)` converge to a limit of absolute value `≤ B`. Then for every `η > 0`, eventually
`|F k| ≤ B + η` on `D k ∩ S`. (De Silva (2011), Lemma 4.1, Step 3: "for `k` large enough".) -/
theorem eventually_forall_abs_le_of_tendsto {D : ℕ → Set (E d)} {S : Set (E d)}
    (hS : IsCompact S) {F : ℕ → E d → ℝ} {B η : ℝ} (hη : 0 < η)
    (hlim : ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ y : ℕ → E d, (∀ k, y k ∈ D (ψ k) ∩ S) →
      ∀ x ∈ S, Tendsto y atTop (𝓝 x) → ∃ L, |L| ≤ B ∧ Tendsto (fun k ↦ F (ψ k) (y k)) atTop (𝓝 L)) :
    ∀ᶠ k in atTop, ∀ y ∈ D k ∩ S, |F k y| ≤ B + η := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨ψ₁, hψ₁, hbad⟩ := Filter.extraction_of_frequently_atTop hcon
  have hbad' : ∀ k, ∃ y ∈ D (ψ₁ k) ∩ S, B + η < |F (ψ₁ k) y| := by
    intro k
    have := hbad k
    push Not at this
    obtain ⟨y, hy, hlt⟩ := this
    exact ⟨y, hy, hlt⟩
  choose y hyD hylt using hbad'
  obtain ⟨x, hxS, ψ₂, hψ₂, hlimx⟩ := hS.tendsto_subseq fun k ↦ (hyD k).2
  obtain ⟨L, hLB, hL⟩ := hlim (ψ₁ ∘ ψ₂) (hψ₁.comp hψ₂) (y ∘ ψ₂) (fun k ↦ hyD (ψ₂ k)) x hxS hlimx
  have : B + η ≤ |L| :=
    ge_of_tendsto hL.abs (Eventually.of_forall fun k ↦ (hylt (ψ₂ k)).le)
  linarith

/-- **Step 3 of De Silva (2011), Lemma 4.1, for one solution**, with two corrections to De Silva.
Let `u ≥ 0` be continuous on `U ⊇ B_1` and `ε`-flat on `B_1` in direction `e`, and let `p ⊥ e`,
`‖p‖ ≤ C̃`. Suppose the linear approximation (4.9) holds on `Ω_{2r}(u) = closure {u > 0} ∩ B_{2r}`:
`|u - ⟪·, e⟫ - ε ⟪p, ·⟫| ≤ ε r / 4`. If `ε C̃² ≤ 1/4` and `ε (1 + C̃) < r ≤ 1/2`, then with
`ν = (e + ε p)/√(1 + ε²|p|²)`:
`‖ν - e‖ ≤ 2 C̃ ε` and `(⟪y, ν⟫ - r ε / 2)₊ ≤ u(y) ≤ (⟪y, ν⟫ + r ε / 2)₊` on `B_r`.

* **Normalization.** De Silva prints `ν = (ε ν̃, 1)/√(ε² + 1)`, not a unit vector unless
  `|ν̃| = 1`. The correct normalization is `√(1 + ε²|p|²)`, and
  `√(1 + ε²|p|²) - 1 ≤ ε² C̃²/2`; the error `|⟪y, ν⟫ - ⟪y, e + ε p⟫| ≤ 2r · ε² C̃²/2 ≤ r ε / 4`
  needs `ε C̃² ≤ 1/4`.
* **Zero phase.** De Silva passes from `Ω_r(u)` to `B_r` "together with (4.3)". For the lower
  bound at zero-phase points of `B_r`, flatness only gives `⟪y, e⟫ ≤ ε`, not
  `⟪y, ν⟫ ≤ r ε / 2`. We use `le_of_le_on_closure_posSet` (the first point of `closure {u > 0}`
  upward along `e`) with the approximation on `Ω_{2r}(u)`, `a = ε`, `b = ε C̃`, which needs
  `r + ε (1 + C̃) < 2 r`. -/
theorem improve_of_approx {U : Set (E d)} {u : E d → ℝ} {e p : E d} {ε r Ct : ℝ}
    (hB : ball (0 : E d) 1 ⊆ U) (hcu : ContinuousOn u U) (hu0 : ∀ y ∈ U, 0 ≤ u y)
    (he : ‖e‖ = 1) (hpe : ⟪p, e⟫ = 0) (hp : ‖p‖ ≤ Ct) (hε : 0 < ε) (hr : 0 < r)
    (hr1 : r ≤ 1 / 2) (hεC : ε * Ct ^ 2 ≤ 1 / 4) (hεr : ε * (1 + Ct) < r)
    (hflat : ∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + ε) 0)
    (happ : ∀ y ∈ closure (posSet u U) ∩ ball 0 (2 * r),
      |u y - (⟪y, e⟫ + ε * ⟪p, y⟫)| ≤ ε * r / 4) :
    ∃ ν : E d, ‖ν‖ = 1 ∧ ‖ν - e‖ ≤ 2 * Ct * ε ∧ ∀ y ∈ ball (0 : E d) r,
      max (⟪y, ν⟫ - r * ε / 2) 0 ≤ u y ∧ u y ≤ max (⟪y, ν⟫ + r * ε / 2) 0 := by
  have hCt : 0 ≤ Ct := (norm_nonneg p).trans hp
  have hep : ⟪e, p⟫ = 0 := by rw [real_inner_comm]; exact hpe
  set N : E d := e + ε • p with hN
  set n : ℝ := ‖N‖ with hn
  -- `n² = 1 + ε² |p|²` since `p ⊥ e` (corrected normalization)
  have hn2 : n ^ 2 = 1 + ε ^ 2 * ‖p‖ ^ 2 := by
    rw [hn, hN, norm_add_sq_real, inner_smul_right, hep, norm_smul, he, Real.norm_eq_abs,
      abs_of_pos hε]
    ring
  have hn0 : 0 ≤ n := norm_nonneg _
  have hn1 : 1 ≤ n := by
    by_contra h
    have := pow_lt_one₀ hn0 (not_le.1 h) two_ne_zero
    linarith [mul_nonneg (sq_nonneg ε) (sq_nonneg ‖p‖)]
  have hnpos : 0 < n := by linarith
  have hnsub : n - 1 ≤ ε ^ 2 * Ct ^ 2 / 2 := by
    have h1 : n - 1 ≤ ε ^ 2 * ‖p‖ ^ 2 / 2 := by
      linarith [mul_le_mul_of_nonneg_left (show 2 ≤ n + 1 by linarith) (sub_nonneg.2 hn1)]
    have h2 : ε ^ 2 * ‖p‖ ^ 2 ≤ ε ^ 2 * Ct ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg p) hp 2) (sq_nonneg ε)
    linarith
  set ν : E d := n⁻¹ • N with hν
  have hνn : ‖ν‖ = 1 := by
    rw [hν, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hnpos, ← hn, inv_mul_cancel₀ hnpos.ne']
  have hνN : ‖N - ν‖ = n - 1 := by
    have : N - ν = (1 - n⁻¹) • N := by rw [hν, sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs, ← hn]
    have : 0 ≤ 1 - n⁻¹ := by
      rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hn1
    rw [abs_of_nonneg this]
    field_simp
  -- `‖ν - e‖ ≤ 2 C̃ ε`
  have hNe : ‖N - e‖ = ε * ‖p‖ := by
    rw [hN, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hnle : n ≤ 1 + ε * ‖p‖ := by
    calc n = ‖e + ε • p‖ := rfl
      _ ≤ ‖e‖ + ‖ε • p‖ := norm_add_le _ _
      _ = 1 + ε * ‖p‖ := by rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have hνe : ‖ν - e‖ ≤ 2 * Ct * ε := by
    calc ‖ν - e‖ = ‖(N - e) - (N - ν)‖ := by congr 1; abel
      _ ≤ ‖N - e‖ + ‖N - ν‖ := norm_sub_le _ _
      _ = ε * ‖p‖ + (n - 1) := by rw [hNe, hνN]
      _ ≤ 2 * Ct * ε := by
        have hεCt : ε * Ct ≤ 1 / 2 := by linarith
        linarith [mul_le_mul_of_nonneg_left hp hε.le,
          mul_le_mul_of_nonneg_left hεCt (mul_nonneg hε.le hCt)]
  -- `⟪y, N⟫ = ⟪y, e⟫ + ε ⟪p, y⟫`, and `⟪y, ν⟫` is within `r ε / 4` of it on `B_{2r}`
  have hyN : ∀ y : E d, ⟪y, N⟫ = ⟪y, e⟫ + ε * ⟪p, y⟫ := fun y ↦ by
    rw [hN, inner_add_right, inner_smul_right, real_inner_comm p y]
  have hyν : ∀ y ∈ ball (0 : E d) (2 * r), |⟪y, N⟫ - ⟪y, ν⟫| ≤ ε * r / 4 := by
    intro y hy
    rw [mem_ball, dist_zero_right] at hy
    rw [← inner_sub_right]
    calc |⟪y, N - ν⟫| ≤ ‖y‖ * ‖N - ν‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * r) * (ε ^ 2 * Ct ^ 2 / 2) := by
          rw [hνN]
          exact mul_le_mul hy.le hnsub (by linarith) (by linarith)
      _ = ε * r * (ε * Ct ^ 2) := by ring
      _ ≤ ε * r * (1 / 4) := mul_le_mul_of_nonneg_left hεC (mul_pos hε hr).le
      _ = ε * r / 4 := by ring
  have hkey : ∀ y ∈ closure (posSet u U) ∩ ball (0 : E d) (2 * r),
      |u y - ⟪y, ν⟫| ≤ r * ε / 2 := by
    intro y hy
    have h1 := happ y hy
    have h2 := hyν y hy.2
    rw [hyN] at h2
    calc |u y - ⟪y, ν⟫| = |(u y - (⟪y, e⟫ + ε * ⟪p, y⟫)) +
          ((⟪y, e⟫ + ε * ⟪p, y⟫) - ⟪y, ν⟫)| := by ring_nf
      _ ≤ |u y - (⟪y, e⟫ + ε * ⟪p, y⟫)| + |(⟪y, e⟫ + ε * ⟪p, y⟫) - ⟪y, ν⟫| := abs_add_le _ _
      _ ≤ ε * r / 4 + ε * r / 4 := add_le_add h1 h2
      _ = r * ε / 2 := by ring
  have hB2 : ball (0 : E d) (2 * r) ⊆ U := (ball_subset_ball (by linarith)).trans hB
  have hBr : ball (0 : E d) r ⊆ ball (0 : E d) (2 * r) := ball_subset_ball (by linarith)
  -- the zero phase (the step De Silva leaves unjustified)
  have hlow := le_of_le_on_closure_posSet (U := U) (u := u) (φ := fun y ↦ ⟪y, ν⟫ - r * ε / 2)
    (e := e) (x := 0) (δ := 2 * r) (δ' := r) (a := ε) (b := ε * Ct) he hB2 hcu hu0 hε.le
    (mul_nonneg hε.le hCt) (by linarith)
    (fun y hy hya ↦ by
      have h1 := (hflat y ((ball_subset_ball (by linarith)) hy)).1
      have : ⟪y, e⟫ - ε ≤ u y := (le_max_left _ _).trans h1
      linarith)
    (fun y hy hy0 ↦ by
      have hyn : ‖y‖ ≤ 1 := by
        rw [mem_ball, dist_zero_right] at hy; linarith
      have h1 : 0 < ⟪y, ν⟫ := by
        have : 0 < r * ε / 2 := half_pos (mul_pos hr hε)
        linarith
      have h2 : 0 < ⟪y, N⟫ := by
        rw [hν, inner_smul_right] at h1
        exact pos_of_mul_pos_right h1 (inv_nonneg.2 hn0)
      rw [hyN] at h2
      have h3 : ⟪p, y⟫ ≤ Ct := by
        calc ⟪p, y⟫ ≤ ‖p‖ * ‖y‖ := real_inner_le_norm _ _
          _ ≤ Ct * 1 := mul_le_mul hp hyn (norm_nonneg _) hCt
          _ = Ct := mul_one _
      linarith [mul_le_mul_of_nonneg_left h3 hε.le])
    (fun y _ t ht _ ↦ by
      have heν : ⟪e, ν⟫ = n⁻¹ := by
        rw [hν, inner_smul_right, hN, inner_add_right, inner_smul_right,
          real_inner_self_eq_norm_sq, he, hep]
        simp
      have h1 : ⟪y + t • e, ν⟫ = ⟪y, ν⟫ + t * n⁻¹ := by
        rw [inner_add_left, inner_smul_left, heν]
        simp
      rw [h1]
      have : 0 ≤ t * n⁻¹ := mul_nonneg ht (inv_nonneg.2 hn0)
      linarith)
    (fun y hy ↦ by
      linarith [(abs_le.1 (hkey y hy)).1])
  refine ⟨ν, hνn, hνe, fun y hy ↦ ⟨max_le (hlow y hy) (hu0 y (hB2 (hBr hy))), ?_⟩⟩
  -- the upper bound: at positive points, from the approximation on `Ω_{2r}`
  rcases le_or_gt (u y) 0 with h | h
  · exact h.trans (le_max_right _ _)
  · have hmem : y ∈ closure (posSet u U) ∩ ball (0 : E d) (2 * r) :=
      ⟨subset_closure ⟨hB2 (hBr hy), h⟩, hBr hy⟩
    have := (abs_le.1 (hkey y hmem)).2
    exact le_trans (by linarith) (le_max_left _ _)

/-- **De Silva's improvement of flatness** (`ImprovementStatement`; De Silva (2011), Lemma 4.1).

By contradiction, as in De Silva's proof. Fix `r ≤ r₀ = min(1/16, 1/(4(9C₀ + 1)))`. A sequence of
counterexamples with `ε k ≤ 1/(k+1)` has a subsequence with `e k → e₀`; `linearized_limit` gives
the limit `w` of `ũ_k = (u k - ⟪·, e k⟫)/ε k`, and `linearized_C2_at_origin` gives `p ⊥ e₀` with
`|w - ⟪p, ·⟫| ≤ 9 C₀ r²` on `H⁺ ∩ B̄_{2r}` and `‖p‖ ≤ 16 + C₀`. With `p_k = p - ⟪p, e k⟫ e k`
(`p_k ⊥ e k`, `p_k → p`), the pointwise convergence upgrades to
`|ũ_k - ⟪p_k, ·⟫| ≤ (9 C₀ + 1) r² ≤ r/4` on `Ω_{2r}(u k)` for large `k` (De Silva's (4.9) on
`Ω_{2r}`), and `improve_of_approx` (with its two corrections) contradicts the choice of `u k`,
with `C = 2 (17 + C₀)`. -/
theorem improvement_of_flatness : ImprovementStatement := by
  intro d hd
  obtain ⟨C₀, hC₀, H2⟩ := linearized_C2_at_origin (d := d) hd
  set Ct : ℝ := 17 + C₀ with hCt
  set C₁ : ℝ := 9 * C₀ + 1 with hC₁
  have hCt0 : 0 < Ct := by positivity
  have hC₁0 : 0 < C₁ := by positivity
  refine ⟨min (1 / 16) (1 / (4 * C₁)), by positivity, 2 * Ct, by positivity, fun r hr hrr₀ ↦ ?_⟩
  have hr16 : r ≤ 1 / 16 := hrr₀.trans (min_le_left _ _)
  have hrC : r * C₁ ≤ 1 / 4 := by
    have := hrr₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  by_contra hcon
  -- a sequence of counterexamples
  have hk : ∀ k : ℕ, ∃ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (ε : ℝ),
      (IsOpen U ∧ ball (0 : E d) 1 ⊆ U ∧ IsViscSolution U Q u ∧ (0 : E d) ∈ freeBoundary u U ∧
        ‖e‖ = 1 ∧ 0 < ε ∧ ε ≤ 1 / ((k : ℝ) + 1) ∧ (∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2) ∧
        ∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + ε) 0) ∧
      ¬ ∃ ν : E d, ‖ν‖ = 1 ∧ ‖ν - e‖ ≤ 2 * Ct * ε ∧ ∀ y ∈ ball (0 : E d) r,
        max (⟪y, ν⟫ - r * ε / 2) 0 ≤ u y ∧ u y ≤ max (⟪y, ν⟫ + r * ε / 2) 0 := by
    intro k
    by_contra hk
    refine hcon ⟨1 / ((k : ℝ) + 1), by positivity, fun U Q u e ε h1 h2 h3 h4 h5 h6 h7 h8 h9 ↦ ?_⟩
    by_contra hc
    exact hk ⟨U, Q, u, e, ε, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, hc⟩
  choose U Q u e ε hyp hnot using hk
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    refine squeeze_zero (fun k ↦ (hyp k).2.2.2.2.2.1.le) (fun k ↦ (hyp k).2.2.2.2.2.2.1) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- directions: a convergent subsequence
  obtain ⟨e₀, he₀s, σ, hσ, he₀⟩ := (isCompact_sphere (0 : E d) 1).tendsto_subseq
    (x := e) fun k ↦ by rw [mem_sphere_zero_iff_norm]; exact (hyp k).2.2.2.2.1
  have he₀1 : ‖e₀‖ = 1 := mem_sphere_zero_iff_norm.1 he₀s
  have hσt : Tendsto σ atTop atTop := hσ.tendsto_atTop
  obtain ⟨φ, hφ, w, hw, hw1, hw0, hconv⟩ := linearized_limit hd (U := fun k ↦ U (σ k))
    (Q := fun k ↦ Q (σ k)) (u := fun k ↦ u (σ k)) (e := fun k ↦ e (σ k)) (ε := fun k ↦ ε (σ k))
    (e₀ := e₀) (fun k ↦ (hyp (σ k)).1) (fun k ↦ (hyp (σ k)).2.1) (fun k ↦ (hyp (σ k)).2.2.1)
    (fun k ↦ (hyp (σ k)).2.2.2.1) (fun k ↦ (hyp (σ k)).2.2.2.2.1) he₀
    (fun k ↦ (hyp (σ k)).2.2.2.2.2.1) (hε0.comp hσt) (fun k ↦ (hyp (σ k)).2.2.2.2.2.2.2.1)
    (fun k ↦ (hyp (σ k)).2.2.2.2.2.2.2.2)
  obtain ⟨p, hpe₀, hp⟩ := H2 he₀1 hw fun x hx hx' ↦ hw1 x ⟨hx, hx'⟩
  have hpC : ‖p‖ ≤ 16 + C₀ := norm_le_of_linearized_taylor hC₀ hw1 hw0 hpe₀ hp
  -- the index along the subsequence, and the tangential projections `p_k`
  set τ : ℕ → ℕ := fun k ↦ σ (φ k) with hτ
  have hτt : Tendsto τ atTop atTop := hσt.comp hφ.tendsto_atTop
  set pk : ℕ → E d := fun k ↦ p - ⟪p, e (τ k)⟫ • e (τ k) with hpk
  have hpkt : ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → Tendsto (fun k ↦ pk (ψ k)) atTop (𝓝 p) := by
    intro ψ hψ
    have he' : Tendsto (fun k ↦ e (τ (ψ k))) atTop (𝓝 e₀) := he₀.comp (hφ.tendsto_atTop.comp hψ)
    have := (tendsto_const_nhds (x := p)).sub
      ((tendsto_const_nhds (x := p)).inner (𝕜 := ℝ) he' |>.smul he')
    simpa [hpe₀] using this
  have hpke : ∀ k, ⟪pk k, e (τ k)⟫ = 0 := fun k ↦ by
    rw [hpk, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
      (hyp (τ k)).2.2.2.2.1]
    simp
  -- the uniform bound on `Ω_{2r}` (De Silva (4.9))
  set F : ℕ → E d → ℝ := fun k y ↦ (u (τ k) y - ⟪y, e (τ k)⟫) / ε (τ k) - ⟪pk k, y⟫ with hF
  have hunif := eventually_forall_abs_le_of_tendsto
    (D := fun k ↦ closure (posSet (u (τ k)) (U (τ k))) ∩ ball 0 (1 / 2))
    (isCompact_closedBall (0 : E d) (2 * r))
    (F := F) (B := C₀ * (3 * r) ^ 2) (η := r ^ 2) (by positivity) (by
      intro ψ hψ y hy x hx hyx
      have hψt := hψ.tendsto_atTop
      have he' : Tendsto (fun k ↦ e (τ (ψ k))) atTop (𝓝 e₀) :=
        he₀.comp (hφ.tendsto_atTop.comp hψt)
      have hx2 : ‖x‖ ≤ 2 * r := by rw [mem_closedBall, dist_zero_right] at hx; exact hx
      -- the limit point lies in the half-ball
      have hxe : 0 ≤ ⟪x, e₀⟫ := by
        have h1 : Tendsto (fun k ↦ ⟪y k, e (τ (ψ k))⟫) atTop (𝓝 ⟪x, e₀⟫) := hyx.inner (𝕜 := ℝ) he'
        have h2 : Tendsto (fun k ↦ -ε (τ (ψ k))) atTop (𝓝 0) := by
          simpa using (hε0.comp (hτt.comp hψt)).neg
        refine le_of_tendsto_of_tendsto h2 h1 (Eventually.of_forall fun k ↦ ?_)
        have hyk := hy k
        exact (abs_normalized_le_one (hyp (τ (ψ k))).2.2.2.2.2.1
          (hyp (τ (ψ k))).2.2.1.1.1 (hyp (τ (ψ k))).2.1 (hyp (τ (ψ k))).2.2.2.2.2.2.2.2
          ⟨hyk.1.1, ball_subset_ball (by norm_num) hyk.1.2⟩).2
      have hxK : x ∈ halfBall e₀ (1 / 2) :=
        ⟨hxe, by rw [mem_ball, dist_zero_right]; linarith⟩
      refine ⟨w x - ⟪p, x⟫, ?_, ?_⟩
      · have h := hp (3 * r) ⟨by positivity, by linarith⟩ x
          (by rw [mem_ball, dist_zero_right]; linarith) hxe
        rwa [hw0, sub_zero] at h
      · have h1 := hconv x hxK ψ hψt y (Eventually.of_forall fun k ↦ (hy k).1) hyx
        exact h1.sub ((hpkt ψ hψt).inner (𝕜 := ℝ) hyx))
  -- smallness for large `k`
  have hsmall : ∀ᶠ k in atTop, ε (τ k) * Ct ^ 2 ≤ 1 / 4 ∧ ε (τ k) * (1 + Ct) < r := by
    have h := hε0.comp hτt
    have h1 : Tendsto (fun k ↦ ε (τ k) * Ct ^ 2) atTop (𝓝 0) := by
      simpa using h.mul_const (Ct ^ 2)
    have h2 : Tendsto (fun k ↦ ε (τ k) * (1 + Ct)) atTop (𝓝 0) := by
      simpa using h.mul_const (1 + Ct)
    filter_upwards [(tendsto_order.1 h1).2 (1 / 4) (by norm_num),
      (tendsto_order.1 h2).2 r hr] with k hk1 hk2 using ⟨hk1.le, hk2⟩
  have hpkn : ∀ᶠ k in atTop, ‖pk k‖ ≤ Ct := by
    have h := (hpkt id tendsto_id).norm
    filter_upwards [(tendsto_order.1 h).2 (‖p‖ + 1) (by linarith)] with k hk
    simp only [id] at hk
    linarith
  obtain ⟨k, hk1, hk2, hk3⟩ := (hunif.and (hsmall.and hpkn)).exists
  obtain ⟨-, hBU, hu, -, he, hε, -, -, hflat⟩ := hyp (τ k)
  refine hnot (τ k) (improve_of_approx hBU hu.1.1 hu.1.2.1 he (hpke k) hk3 hε hr (by linarith)
    hk2.1 hk2.2 hflat fun y hy ↦ ?_)
  have hy' : y ∈ closure (posSet (u (τ k)) (U (τ k))) ∩ ball 0 (1 / 2) ∩ closedBall 0 (2 * r) :=
    ⟨⟨hy.1, ball_subset_ball (by linarith) hy.2⟩, ball_subset_closedBall hy.2⟩
  have h := hk1 y hy'
  simp only [hF] at h
  have hid : u (τ k) y - (⟪y, e (τ k)⟫ + ε (τ k) * ⟪pk k, y⟫) =
      ε (τ k) * ((u (τ k) y - ⟪y, e (τ k)⟫) / ε (τ k) - ⟪pk k, y⟫) := by
    field_simp
    ring
  rw [hid, abs_mul, abs_of_pos hε]
  have hbd : C₀ * (3 * r) ^ 2 + r ^ 2 ≤ r / 4 := by
    have : C₀ * (3 * r) ^ 2 + r ^ 2 = r * (r * C₁) := by rw [hC₁]; ring
    rw [this]
    linarith [mul_le_mul_of_nonneg_left hrC hr.le]
  calc ε (τ k) * |(u (τ k) y - ⟪y, e (τ k)⟫) / ε (τ k) - ⟪pk k, y⟫|
      ≤ ε (τ k) * (r / 4) := mul_le_mul_of_nonneg_left (h.trans hbd) hε.le
    _ = ε (τ k) * r / 4 := by ring

end EllipticBernoulli
