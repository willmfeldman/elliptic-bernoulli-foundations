/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
import EllipticBernoulli.Flatness.Harnack
import EllipticBernoulli.Flatness.Improvement
import EllipticBernoulli.Viscosity.Affine

/-!
# Iterating the improvement of flatness: pointwise `C^{1,α}` flatness

De Silva (2011), §5 (proof of Theorem 1.1: "a standard iteration argument"), with `f = 0`,
`a_{ij} = δ_{ij}`, `g = Q` Lipschitz (De Silva allows a Hölder `g`).

De Silva iterates Lemma 4.1 only at the origin, where `g(0) = 1`. Applying it at every
free-boundary point `y ∈ B_{1/2}` needs steps De Silva leaves unstated: re-centre at `y`;
normalize by `Q(y) ≠ 1`, which degrades the flatness from `ε` to `5ε` and needs `ε ≤ 1/10`; and
use `y ∈ F(u)` for Lemma 4.1's hypothesis `0 ∈ F(u)`. They are `flat_at_freeBoundary_point`,
`normalize_flat_scalar` and `flat_C1alpha_at_point` below.

* `IsFlatC1AlphaAt u Q y ν C α R`: two-sided flatness `Q(y) (⟪x - y, ν⟫ ∓ C s^{1+α})₊` of `u` in
  every ball `B_s(y)`, `0 < s ≤ R` (the input of `Flatness/Graph.lean`).
* Scalar bookkeeping, independent of the PDE: `exists_pow_mul_lt_le` (choice of the level `k`
  for a radius `s`), `half_pow_eq_rpow` (`2^{-k} = (r̄^k)^α` with `α = log 2 / log (1/r̄)`),
  `exists_level_le` (the error `ρ₀ r̄^k 2^{-k} ≤ K s^{1+α}`),
  `exists_tendsto_of_norm_sub_le_geometric` (the normals converge geometrically) and
  `exists_seq_of_step` (the recursion producing the normals).
* `flat_at_freeBoundary_point`: `ε`-flatness on `B_1` gives `2ε`-flatness on `B_{1/2}(y)` at every
  free-boundary point `y ∈ B_{1/2}`, in the same direction (`|⟪y, e⟫| ≤ ε`).
* `normalize_flat_scalar`, `flat_level_step` (one application of Lemma 4.1 to the rescaling
  `u(y + ρ ·)/(ρ Q(y))`, via `IsViscSolution.rescale`) and `flat_C1alpha_at_point` (the
  iteration at one free-boundary point).
* `flat_pointwise_C1alpha`: the output theorem, used in `Flatness/Graph.lean`. Constants:
  `r̄ = min(r₀, 1/4)`, `ε̄ = min(ε₀(r̄)/5, 1/10)`, `α = log 2 / log (1/r̄)`,
  `C = max(10 C_I, K (5 + 10 C_I))` with `K = 2^α r̄^{-(1+α)}`.

## Iteration scheme

Fix `r̄ = min(r₀, 1/4)` (`r₀` from `ImprovementStatement`), `ε₀ = ε₀(r̄)`, `α = log 2 / log (1/r̄)`.
At a free-boundary point `y ∈ B_{1/2}` put `w₀(z) = u(y + z/2)/(Q(y)/2)`, `q₀(z) = Q(y + z/2)/Q(y)`
(`IsViscSolution.rescale`); `w₀` is `5ε`-flat on `B_1` in direction `e`, and `|q₀ - 1| ≤ ε²`.
Step `k`: `w_k(z) = w₀(r̄^k z)/r̄^k` is `ε_k = 2^{-k} 5ε`-flat in direction `ν_k`, and
`|q₀(r̄^k ·) - 1| ≤ ε² r̄^k ≤ ε_k²` because `r̄ ≤ 1/4` (this is where `Lip Q ≤ ε²` is used).
Lemma 4.1 gives `ν_{k+1}` with `‖ν_{k+1} - ν_k‖ ≤ C ε_k`. The normals converge to `ν(y)` with
`‖ν_k - ν(y)‖ ≤ 2 C ε_k`, and the scalar lemmas turn the flatness at the levels into
`IsFlatC1AlphaAt` with constant `C' ε`.

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Pointwise `C^{1,α}` flatness** of `u` at the free-boundary point `y`, with unit normal `ν`,
constant `C`, exponent `α`, up to radius `R`: for `0 < s ≤ R`, on `B_s(y)`,
`Q(y) (⟪x - y, ν⟫ - C s^{1+α})₊ ≤ u(x) ≤ Q(y) (⟪x - y, ν⟫ + C s^{1+α})₊`. -/
def IsFlatC1AlphaAt (u Q : E d → ℝ) (y ν : E d) (C α R : ℝ) : Prop :=
  ‖ν‖ = 1 ∧ ∀ s ∈ Ioc (0 : ℝ) R, ∀ x ∈ ball y s,
    Q y * max (⟪x - y, ν⟫ - C * s ^ (1 + α)) 0 ≤ u x ∧
    u x ≤ Q y * max (⟪x - y, ν⟫ + C * s ^ (1 + α)) 0

end EllipticBernoulli

end

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Scalar bookkeeping (independent of the PDE) -/

/-- For `0 < r < 1` and `0 < s ≤ ρ` there is a level `k` with `r^{k+1} ρ < s ≤ r^k ρ`. -/
theorem exists_pow_mul_lt_le {r s ρ : ℝ} (hr1 : r < 1) (hs : 0 < s) (hsρ : s ≤ ρ) :
    ∃ k : ℕ, r ^ (k + 1) * ρ < s ∧ s ≤ r ^ k * ρ := by
  have hρ : 0 < ρ := hs.trans_le hsρ
  have hex : ∃ n : ℕ, r ^ n * ρ < s := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hs hρ) hr1
    exact ⟨n, by rwa [lt_div_iff₀ hρ] at hn⟩
  classical
  set n := Nat.find hex with hn
  have hn0 : n ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [← hn, h, pow_zero, one_mul] at this
    linarith
  refine ⟨n - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
    exact Nat.find_spec hex
  · exact not_lt.1 (Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hn0) one_pos))

/-- `2^{-k} = (r^k)^α` for `α = log 2 / log (1/r)`, `0 < r < 1`. -/
theorem half_pow_eq_rpow {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ) :
    ((1 : ℝ) / 2) ^ k = (r ^ k) ^ (Real.log 2 / Real.log r⁻¹) := by
  have hl : Real.log r⁻¹ ≠ 0 := by
    rw [Real.log_inv]; exact neg_ne_zero.2 (Real.log_neg hr0 hr1).ne
  rw [Real.rpow_def_of_pos (pow_pos hr0 k), Real.log_pow, Real.log_inv]
  have : Real.log r * ↑k * (Real.log 2 / -Real.log r) = -(k * Real.log 2) := by
    have : Real.log r ≠ 0 := (Real.log_neg hr0 hr1).ne
    field_simp
  rw [mul_comm (k : ℝ) (Real.log r), this, Real.exp_neg, ← Real.log_pow,
    Real.exp_log (by positivity)]
  simp

/-- The exponent `α = log 2 / log (1/r)` lies in `(0, 1/2]` for `0 < r ≤ 1/4`. -/
theorem log_two_div_log_inv_mem {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 4) :
    Real.log 2 / Real.log r⁻¹ ∈ Ioc (0 : ℝ) (1 / 2) := by
  have h4 : (4 : ℝ) ≤ r⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hr0]; linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : Real.log 4 ≤ Real.log r⁻¹ := Real.log_le_log (by norm_num) h4
  have h42 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hlr : 0 < Real.log r⁻¹ := by linarith
  refine ⟨div_pos hl2 hlr, ?_⟩
  rw [div_le_iff₀ hlr]
  linarith

/-- **The level of a radius and its error** (the scalar recursion of the iteration). For
`0 < r < 1`, `0 < ρ`, `0 < s ≤ ρ` and `α = log 2 / log (1/r)` there is a level `k` with
`s ≤ ρ r^k` and `ρ r^k 2^{-k} ≤ K s^{1+α}`, where `K = ρ^{-α} r^{-(1+α)}`. -/
theorem exists_level_le {r s ρ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hs : 0 < s) (hsρ : s ≤ ρ) :
    ∃ k : ℕ, s ≤ r ^ k * ρ ∧
      ρ * r ^ k * ((1 : ℝ) / 2) ^ k ≤
        ρ ^ (-(Real.log 2 / Real.log r⁻¹)) * r ^ (-(1 + Real.log 2 / Real.log r⁻¹)) *
          s ^ (1 + Real.log 2 / Real.log r⁻¹) := by
  have hρ : 0 < ρ := hs.trans_le hsρ
  obtain ⟨k, hk1, hk2⟩ := exists_pow_mul_lt_le hr1 hs hsρ
  refine ⟨k, hk2, ?_⟩
  set α := Real.log 2 / Real.log r⁻¹ with hα
  have hα0 : 0 ≤ α := by
    have : 0 ≤ Real.log r⁻¹ := Real.log_nonneg (one_le_inv₀ hr0 |>.2 hr1.le)
    exact div_nonneg (Real.log_nonneg (by norm_num)) this
  rw [half_pow_eq_rpow hr0 hr1 k, ← hα]
  have hrk : 0 < r ^ k := pow_pos hr0 k
  -- `ρ r^k (r^k)^α = ρ (r^k)^{1+α}` and `r^k < s/(r ρ)`
  have h1 : ρ * r ^ k * (r ^ k) ^ α = ρ * (r ^ k) ^ (1 + α) := by
    rw [Real.rpow_add hrk, Real.rpow_one]; ring
  have hlt : r ^ k ≤ s / (r * ρ) := by
    rw [le_div_iff₀ (mul_pos hr0 hρ)]
    have : r ^ (k + 1) * ρ = r ^ k * (r * ρ) := by ring
    linarith
  have h2 : (r ^ k) ^ (1 + α) ≤ (s / (r * ρ)) ^ (1 + α) :=
    Real.rpow_le_rpow hrk.le hlt (by linarith)
  rw [h1]
  calc ρ * (r ^ k) ^ (1 + α) ≤ ρ * (s / (r * ρ)) ^ (1 + α) :=
        mul_le_mul_of_nonneg_left h2 hρ.le
    _ = ρ ^ (-α) * r ^ (-(1 + α)) * s ^ (1 + α) := by
        rw [Real.div_rpow hs.le (mul_pos hr0 hρ).le, Real.mul_rpow hr0.le hρ.le,
          Real.rpow_neg hρ.le, Real.rpow_neg hr0.le, Real.rpow_add hρ, Real.rpow_one]
        field_simp

/-- **Geometric convergence of the normals.** If `‖ν_{k+1} - ν_k‖ ≤ A 2^{-k}`, then `ν_k → ν∞`
with `‖ν_k - ν∞‖ ≤ 2 A 2^{-k}`. -/
theorem exists_tendsto_of_norm_sub_le_geometric {F : Type*} [NormedAddCommGroup F]
    [CompleteSpace F] {ν : ℕ → F} {A : ℝ} (h : ∀ k, ‖ν (k + 1) - ν k‖ ≤ A * ((1 : ℝ) / 2) ^ k) :
    ∃ ν' : F, Tendsto ν atTop (𝓝 ν') ∧ ∀ k, ‖ν k - ν'‖ ≤ 2 * A * ((1 : ℝ) / 2) ^ k := by
  have h2 : ∀ k, dist (ν k) (ν (k + 1)) ≤ 2 * A / 2 / 2 ^ k := fun k ↦ by
    rw [dist_comm, dist_eq_norm]
    calc ‖ν (k + 1) - ν k‖ ≤ A * ((1 : ℝ) / 2) ^ k := h k
      _ = 2 * A / 2 / 2 ^ k := by rw [div_pow, one_pow]; ring
  obtain ⟨ν', hν'⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric_two h2)
  refine ⟨ν', hν', fun k ↦ ?_⟩
  have := dist_le_of_le_geometric_two_of_tendsto h2 hν' k
  rw [dist_eq_norm] at this
  calc ‖ν k - ν'‖ ≤ 2 * A / 2 ^ k := this
    _ = 2 * A * ((1 : ℝ) / 2) ^ k := by rw [div_pow, one_pow]; ring

/-- **The recursion.** From an initial state satisfying `P 0` and a step producing, from any state
satisfying `P k`, a state satisfying `P (k+1)` related by `R k`, build the whole sequence. -/
theorem exists_seq_of_step {α : Type*} {P : ℕ → α → Prop} {R : ℕ → α → α → Prop} {a : α}
    (h0 : P 0 a) (hstep : ∀ k x, P k x → ∃ y, R k x y ∧ P (k + 1) y) :
    ∃ ν : ℕ → α, ν 0 = a ∧ ∀ k, P k (ν k) ∧ R k (ν k) (ν (k + 1)) := by
  choose g hg using hstep
  let f : (k : ℕ) → {x // P k x} := fun k ↦
    Nat.rec (motive := fun k ↦ {x // P k x}) ⟨a, h0⟩
      (fun k x ↦ ⟨g k x.1 x.2, (hg k x.1 x.2).2⟩) k
  exact ⟨fun k ↦ (f k).1, rfl, fun k ↦ ⟨(f k).2, (hg k (f k).1 (f k).2).1⟩⟩

/-! ### Flatness at nearby free-boundary points -/

/-- **Initial flatness at nearby free-boundary points.** If `u` is `ε`-flat on `B_1` in direction
`e` and `y ∈ F(u) ∩ B_{1/2}`, then `|⟪y, e⟫| ≤ ε` and `u` is `2ε`-flat on `B_{1/2}(y)` in the same
direction, centred at `y`. -/
theorem flat_at_freeBoundary_point {U : Set (E d)} {u : E d → ℝ} {e y : E d} {ε : ℝ}
    (hU : IsOpen U) (hB : ball (0 : E d) 1 ⊆ U) (hcu : ContinuousOn u U)
    (hflat : ∀ x ∈ ball (0 : E d) 1, max (⟪x, e⟫ - ε) 0 ≤ u x ∧ u x ≤ max (⟪x, e⟫ + ε) 0)
    (hy : y ∈ freeBoundary u U ∩ ball 0 (1 / 2)) :
    |⟪y, e⟫| ≤ ε ∧ ∀ x ∈ ball y (1 / 2),
      max (⟪x - y, e⟫ - 2 * ε) 0 ≤ u x ∧ u x ≤ max (⟪x - y, e⟫ + 2 * ε) 0 := by
  obtain ⟨⟨hfr, hyU⟩, hy2⟩ := hy
  have hy1 : y ∈ ball (0 : E d) 1 := ball_subset_ball (by norm_num) hy2
  have hopen : IsOpen (posSet u U) := hcu.isOpen_inter_preimage hU isOpen_Ioi
  have hnot : ¬ 0 < u y := fun h ↦ by
    rw [hopen.frontier_eq] at hfr
    exact hfr.2 ⟨hyU, h⟩
  have hup : ⟪y, e⟫ ≤ ε := by
    have := (hflat y hy1).1
    have : ⟪y, e⟫ - ε ≤ u y := (le_max_left _ _).trans this
    linarith [not_lt.1 hnot]
  have hlo : -ε ≤ ⟪y, e⟫ := by
    have htrap : ∀ x ∈ ball (0 : E d) 1, max (⟪x, e⟫ + -ε) 0 ≤ u x ∧
        u x ≤ max (⟪x, e⟫ + ε) 0 := fun x hx ↦ by simpa [sub_eq_add_neg] using hflat x hx
    have h := trap_of_mem_closure_posSet hcu hB htrap ⟨frontier_subset_closure hfr, hy1⟩
    have h0 : 0 ≤ u y := (le_max_right _ _).trans (hflat y hy1).1
    linarith [h.2]
  refine ⟨abs_le.2 ⟨hlo, hup⟩, fun x hx ↦ ?_⟩
  have hx1 : x ∈ ball (0 : E d) 1 := by
    rw [mem_ball, dist_zero_right] at hy2 ⊢
    rw [mem_ball, dist_eq_norm] at hx
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ < 1 := by linarith
  have hxy : ⟪x - y, e⟫ = ⟪x, e⟫ - ⟪y, e⟫ := inner_sub_left x y e
  obtain ⟨h1, h2⟩ := hflat x hx1
  constructor
  · exact le_trans (max_le_max (by linarith) le_rfl) h1
  · exact h2.trans (max_le_max (by linarith) le_rfl)

/-! ### One step of the iteration -/

/-- `(ρ a - ρ b)₊ = ρ (a - b)₊` for `ρ ≥ 0`. -/
theorem max_mul_sub_mul_zero {ρ a b : ℝ} (hρ : 0 ≤ ρ) :
    max (ρ * a - ρ * b) 0 = ρ * max (a - b) 0 := by
  rw [mul_max_of_nonneg _ _ hρ, mul_zero, mul_sub]

/-- `(ρ a + ρ b)₊ = ρ (a + b)₊` for `ρ ≥ 0`. -/
theorem max_mul_add_mul_zero {ρ a b : ℝ} (hρ : 0 ≤ ρ) :
    max (ρ * a + ρ * b) 0 = ρ * max (a + b) 0 := by
  rw [mul_max_of_nonneg _ _ hρ, mul_zero, mul_add]

/-- **Normalization at a free-boundary point** (the scalar part). If `|q - 1| ≤ ε²`,
`0 < ε ≤ 1/10` and `|t| < 1/2`, then `2ε`-flatness implies `q`-scaled `5ε/2`-flatness:
`q (t - 5ε/2)₊ ≤ (t - 2ε)₊` and `(t + 2ε)₊ ≤ q (t + 5ε/2)₊`. -/
theorem normalize_flat_scalar {q ε t : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (hq : |q - 1| ≤ ε ^ 2) (ht : |t| < 1 / 2) :
    q * max (t - 5 * ε / 2) 0 ≤ max (t - 2 * ε) 0 ∧
      max (t + 2 * ε) 0 ≤ q * max (t + 5 * ε / 2) 0 := by
  obtain ⟨hq1, hq2⟩ := abs_le.1 hq
  obtain ⟨ht1, ht2⟩ := abs_lt.1 ht
  have hq0 : 0 ≤ q := by linarith [mul_le_mul_of_nonneg_left hε1 hε.le]
  constructor
  · rcases le_or_gt (t - 5 * ε / 2) 0 with h | h
    · rw [max_eq_right h, mul_zero]; exact le_max_right _ _
    · rw [max_eq_left h.le]
      refine le_trans ?_ (le_max_left _ _)
      have : q * (t - 5 * ε / 2) ≤ (1 + ε ^ 2) * (t - 5 * ε / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) h.le
      linarith [pow_pos hε 3, mul_le_mul_of_nonneg_left hε1 hε.le,
        mul_le_mul_of_nonneg_left ht2.le (sq_nonneg ε)]
  · rcases le_or_gt (t + 2 * ε) 0 with h | h
    · rw [max_eq_right h]; exact mul_nonneg hq0 (le_max_right _ _)
    · rw [max_eq_left h.le, max_eq_left (by linarith)]
      have : (1 - ε ^ 2) * (t + 5 * ε / 2) ≤ q * (t + 5 * ε / 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith [mul_le_mul_of_nonneg_left hε1 hε.le, mul_le_mul_of_nonneg_left hε1 (sq_nonneg ε),
        mul_le_mul_of_nonneg_left ht2.le (sq_nonneg ε)]

/-- **One step of the iteration** (De Silva (2011), §5: Lemma 4.1 applied to the rescaling
`w(z) = u(y + ρ z)/(ρ q)`, `Q_w(z) = Q(y + ρ z)/q`, `IsViscSolution.rescale`). Let `Himp` be
the improvement property at radius `r` (from `ImprovementStatement`). If `u` is `q`-scaled
`ρ η`-flat on `B_ρ(y)` in direction `ν`, `y ∈ F(u)`, `|Q/q - 1| ≤ η²` on `B_ρ(y)` and
`η ≤ ε₀`, then there is `ν'` with `‖ν' - ν‖ ≤ C_I η` such that `u` is `q`-scaled
`(r ρ)(η/2)`-flat on `B_{rρ}(y)` in direction `ν'`. -/
theorem flat_level_step {U : Set (E d)} {Q u : E d → ℝ} {y ν : E d} {ρ η q r ε₀ CI : ℝ}
    (Himp : ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U →
      ball (0 : E d) 1 ⊆ U → IsViscSolution U Q u → (0 : E d) ∈ freeBoundary u U → ‖e‖ = 1 →
      0 < ε → ε ≤ ε₀ → (∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2) →
      (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + ε) 0) →
      ∃ ν : E d, ‖ν‖ = 1 ∧ ‖ν - e‖ ≤ CI * ε ∧ ∀ y ∈ ball (0 : E d) r,
        max (⟪y, ν⟫ - r * ε / 2) 0 ≤ u y ∧ u y ≤ max (⟪y, ν⟫ + r * ε / 2) 0)
    (hU : IsOpen U) (hB : ball y ρ ⊆ U) (hu : IsViscSolution U Q u) (hy : y ∈ freeBoundary u U)
    (hρ : 0 < ρ) (hq : 0 < q) (hη : 0 < η) (hηε₀ : η ≤ ε₀) (hν : ‖ν‖ = 1)
    (hQ : ∀ x ∈ ball y ρ, |Q x / q - 1| ≤ η ^ 2)
    (hflat : ∀ x ∈ ball y ρ, q * max (⟪x - y, ν⟫ - ρ * η) 0 ≤ u x ∧
      u x ≤ q * max (⟪x - y, ν⟫ + ρ * η) 0) :
    ∃ ν' : E d, ‖ν'‖ = 1 ∧ ‖ν' - ν‖ ≤ CI * η ∧ ∀ x ∈ ball y (r * ρ),
      q * max (⟪x - y, ν'⟫ - (r * ρ) * (η / 2)) 0 ≤ u x ∧
        u x ≤ q * max (⟪x - y, ν'⟫ + (r * ρ) * (η / 2)) 0 := by
  have hA : ∀ z : E d, z ∈ ball (0 : E d) 1 → y + ρ • z ∈ ball y ρ := by
    intro z hz
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ]
    rw [mem_ball, dist_zero_right] at hz
    exact mul_lt_of_lt_one_right hρ hz
  have hAi : ∀ z v : E d, ⟪(y + ρ • z) - y, v⟫ = ρ * ⟪z, v⟫ := fun z v ↦ by
    rw [add_sub_cancel_left, inner_smul_left]; simp
  have hρq : 0 < ρ * q := mul_pos hρ hq
  have hw := hu.rescale y hρ hq
  have hUw : IsOpen ((fun z ↦ y + ρ • z) ⁻¹' U) := hU.preimage (by fun_prop)
  have hBw : ball (0 : E d) 1 ⊆ (fun z ↦ y + ρ • z) ⁻¹' U := fun z hz ↦ hB (hA z hz)
  have h0w : (0 : E d) ∈ freeBoundary (fun z ↦ u (y + ρ • z) / (ρ * q))
      ((fun z ↦ y + ρ • z) ⁻¹' U) := by
    rw [freeBoundary_rescale y hρ hq, mem_preimage, smul_zero, add_zero]
    exact hy
  have hQw : ∀ z ∈ ball (0 : E d) 1, |Q (y + ρ • z) / q - 1| ≤ η ^ 2 := fun z hz ↦
    hQ _ (hA z hz)
  have hflatw : ∀ z ∈ ball (0 : E d) 1,
      max (⟪z, ν⟫ - η) 0 ≤ u (y + ρ • z) / (ρ * q) ∧
        u (y + ρ • z) / (ρ * q) ≤ max (⟪z, ν⟫ + η) 0 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hflat _ (hA z hz)
    rw [hAi, max_mul_sub_mul_zero hρ.le] at h1
    rw [hAi, max_mul_add_mul_zero hρ.le] at h2
    constructor
    · rw [le_div_iff₀ hρq]; linarith
    · rw [div_le_iff₀ hρq]; linarith
  obtain ⟨ν', hν', hνν, hflat'⟩ := Himp _ _ _ ν η hUw hBw hw h0w hν hη hηε₀ hQw hflatw
  refine ⟨ν', hν', hνν, fun x hx ↦ ?_⟩
  set z : E d := ρ⁻¹ • (x - y) with hz
  have hxz : y + ρ • z = x := by
    rw [hz, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul, add_sub_cancel]
  have hzb : z ∈ ball (0 : E d) r := by
    rw [mem_ball, dist_zero_right, hz, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hρ]
    rw [mem_ball, dist_eq_norm] at hx
    rw [inv_mul_lt_iff₀ hρ]; linarith
  obtain ⟨h1, h2⟩ := hflat' z hzb
  rw [hxz] at h1 h2
  have hxy : ⟪x - y, ν'⟫ = ρ * ⟪z, ν'⟫ := by rw [← hxz, hAi]
  have hc : (r * ρ) * (η / 2) = ρ * (r * η / 2) := by ring
  rw [hxy, hc, max_mul_sub_mul_zero hρ.le, max_mul_add_mul_zero hρ.le]
  constructor
  · rw [le_div_iff₀ hρq] at h1; linarith
  · rw [div_le_iff₀ hρq] at h2; linarith

/-- **The iteration at one free-boundary point** (De Silva (2011), §5, "a standard iteration
argument"). With the improvement property `Himp` at radius `r ≤ 1/4` (constants `ε₀`, `C_I`),
`α = log 2 / log (1/r)` and `K = (1/2)^{-α} r^{-(1+α)}`, an `ε`-flat solution
(`5 ε ≤ ε₀`, `ε ≤ 1/10`, `|Q - 1| ≤ ε²`, `Lip Q ≤ ε²` on `B_1`) has at every
`y ∈ F(u) ∩ B_{1/2}` a unit normal `ν` with `‖ν - e‖ ≤ 10 C_I ε` and
`IsFlatC1AlphaAt u Q y ν (C ε) α (1/4)` for every `C ≥ K (5 + 10 C_I)`.

Bookkeeping: levels `ρ_k = r^k/2`, flatness `η_k = 2^{-k} 5ε` of
`u(y + ρ_k ·)/(ρ_k Q(y))`; level `0` is `flat_at_freeBoundary_point` plus
`normalize_flat_scalar`; `|Q(y + ρ_k z)/Q(y) - 1| ≤ 2 ε² ρ_k ≤ ε² 4^{-k} ≤ η_k²` uses `r ≤ 1/4`
and `Lip Q ≤ ε²`; the step is `flat_level_step`; the normals converge geometrically
(`exists_tendsto_of_norm_sub_le_geometric`), and `exists_level_le` converts levels to radii. -/
theorem flat_C1alpha_at_point {U : Set (E d)} {Q u : E d → ℝ} {e y : E d} {ε r ε₀ CI C : ℝ}
    (Himp : ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U →
      ball (0 : E d) 1 ⊆ U → IsViscSolution U Q u → (0 : E d) ∈ freeBoundary u U → ‖e‖ = 1 →
      0 < ε → ε ≤ ε₀ → (∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2) →
      (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + ε) 0) →
      ∃ ν : E d, ‖ν‖ = 1 ∧ ‖ν - e‖ ≤ CI * ε ∧ ∀ y ∈ ball (0 : E d) r,
        max (⟪y, ν⟫ - r * ε / 2) 0 ≤ u y ∧ u y ≤ max (⟪y, ν⟫ + r * ε / 2) 0)
    (hr0 : 0 < r) (hr : r ≤ 1 / 4) (hCI : 0 < CI)
    (hC : (1 / 2 : ℝ) ^ (-(Real.log 2 / Real.log r⁻¹)) *
      r ^ (-(1 + Real.log 2 / Real.log r⁻¹)) * (5 + 10 * CI) ≤ C)
    (hU : IsOpen U) (hB : ball (0 : E d) 1 ⊆ U) (hu : IsViscSolution U Q u) (he : ‖e‖ = 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) (hεε₀ : 5 * ε ≤ ε₀)
    (hQ : ∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2)
    (hL : LipschitzOnWith (ε ^ 2).toNNReal Q (ball 0 1))
    (hflat : ∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + ε) 0)
    (hy : y ∈ freeBoundary u U ∩ ball 0 (1 / 2)) :
    ∃ ν : E d, ‖ν - e‖ ≤ 10 * CI * ε ∧
      IsFlatC1AlphaAt u Q y ν (C * ε) (Real.log 2 / Real.log r⁻¹) (1 / 4) := by
  have hr1 : r < 1 := by linarith
  obtain ⟨hyF, hy2⟩ := hy
  have hy1 : y ∈ ball (0 : E d) 1 := ball_subset_ball (by norm_num) hy2
  have hyn : ‖y‖ < 1 / 2 := by rw [mem_ball, dist_zero_right] at hy2; exact hy2
  set q := Q y with hqdef
  have hq := hQ y hy1
  have hε2 : ε ^ 2 ≤ 1 / 100 :=
    calc ε ^ 2 ≤ (1 / 10) ^ 2 := pow_le_pow_left₀ hε.le hε1 2
      _ = 1 / 100 := by norm_num
  have hqh : 1 / 2 ≤ q := by linarith [(abs_le.1 hq).1]
  have hq0 : 0 < q := by linarith
  obtain ⟨-, hflat2⟩ := flat_at_freeBoundary_point hU hB hu.1.1 hflat ⟨hyF, hy2⟩
  -- levels
  set ρ : ℕ → ℝ := fun k ↦ r ^ k / 2 with hρ
  set η : ℕ → ℝ := fun k ↦ (1 / 2 : ℝ) ^ k * (5 * ε) with hη
  have hρpos : ∀ k, 0 < ρ k := fun k ↦ by simp only [hρ]; positivity
  have hρle : ∀ k, ρ k ≤ 1 / 2 := fun k ↦ by
    simp only [hρ]
    have := pow_le_one₀ hr0.le hr1.le (n := k)
    linarith
  have hηpos : ∀ k, 0 < η k := fun k ↦ by simp only [hη]; positivity
  have hρs : ∀ k, ρ (k + 1) = r * ρ k := fun k ↦ by simp only [hρ]; ring
  have hηs : ∀ k, η (k + 1) = η k / 2 := fun k ↦ by simp only [hη]; ring
  have hballU : ∀ k, ball y (ρ k) ⊆ U := by
    intro k x hx
    apply hB
    rw [mem_ball, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hx
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ < 1 := by linarith [hρle k]
  have hball1 : ∀ k, ball y (ρ k) ⊆ ball (0 : E d) 1 := by
    intro k x hx
    rw [mem_ball, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hx
    calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
      _ < 1 := by linarith [hρle k]
  -- the coefficient at level `k` (uses `Lip Q ≤ ε²` and `r ≤ 1/4`)
  have hQk : ∀ k, ∀ x ∈ ball y (ρ k), |Q x / q - 1| ≤ η k ^ 2 := by
    intro k x hx
    have hL' := hL.dist_le_mul x (hball1 k hx) y hy1
    rw [Real.coe_toNNReal _ (sq_nonneg ε), Real.dist_eq, ← hqdef] at hL'
    have hxy : dist x y < ρ k := hx
    have h1 : |Q x - q| ≤ ε ^ 2 * ρ k :=
      hL'.trans (mul_le_mul_of_nonneg_left hxy.le (sq_nonneg ε))
    have h2 : |Q x / q - 1| = |Q x - q| / q := by
      rw [div_sub_one hq0.ne', abs_div, abs_of_pos hq0]
    have hrk : r ^ k ≤ (1 / 4 : ℝ) ^ k := pow_le_pow_left₀ hr0.le hr k
    have hηk : η k ^ 2 = 25 * ε ^ 2 * (1 / 4 : ℝ) ^ k := by
      simp only [hη]
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
      ring
    rw [h2, div_le_iff₀ hq0, hηk]
    have h3 : ε ^ 2 * ρ k ≤ ε ^ 2 * (1 / 4 : ℝ) ^ k / 2 := by
      simp only [hρ]
      have := mul_le_mul_of_nonneg_left hrk (sq_nonneg ε)
      linarith
    have h4 : 0 ≤ ε ^ 2 * (1 / 4 : ℝ) ^ k := by positivity
    linarith [mul_le_mul_of_nonneg_left hqh h4]
  -- the level predicate
  set P : ℕ → E d → Prop := fun k ν ↦ ‖ν‖ = 1 ∧ ∀ x ∈ ball y (ρ k),
    q * max (⟪x - y, ν⟫ - ρ k * η k) 0 ≤ u x ∧ u x ≤ q * max (⟪x - y, ν⟫ + ρ k * η k) 0
    with hP
  set R : ℕ → E d → E d → Prop := fun k ν ν' ↦ ‖ν' - ν‖ ≤ CI * η k with hR
  have h0 : P 0 e := by
    refine ⟨he, fun x hx ↦ ?_⟩
    have hρη : ρ 0 * η 0 = 5 * ε / 2 := by simp only [hρ, hη]; ring
    have hρ0 : ρ 0 = 1 / 2 := by simp only [hρ]; ring
    rw [hρη]
    rw [hρ0] at hx
    have ht : |⟪x - y, e⟫| < 1 / 2 := by
      calc |⟪x - y, e⟫| ≤ ‖x - y‖ * ‖e‖ := abs_real_inner_le_norm _ _
        _ < 1 / 2 := by rw [he, mul_one, ← dist_eq_norm]; exact hx
    obtain ⟨hs1, hs2⟩ := normalize_flat_scalar hε hε1 hq ht
    obtain ⟨hf1, hf2⟩ := hflat2 x hx
    exact ⟨hs1.trans hf1, hf2.trans hs2⟩
  have hstep : ∀ k ν, P k ν → ∃ ν', R k ν ν' ∧ P (k + 1) ν' := by
    rintro k ν ⟨hν, hfl⟩
    have hηε₀ : η k ≤ ε₀ := by
      simp only [hη]
      have := pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (n := k)
      linarith [mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ 5 * ε)]
    obtain ⟨ν', hν', hνν, hfl'⟩ := flat_level_step Himp hU (hballU k) hu hyF (hρpos k) hq0
      (hηpos k) hηε₀ hν (hQk k) hfl
    refine ⟨ν', hνν, hν', fun x hx ↦ ?_⟩
    rw [hρs, hηs]
    rw [hρs] at hx
    exact hfl' x hx
  obtain ⟨νs, hν0, hνs⟩ := exists_seq_of_step h0 hstep
  have hgeo : ∀ k, ‖νs (k + 1) - νs k‖ ≤ CI * (5 * ε) * ((1 : ℝ) / 2) ^ k := fun k ↦ by
    have := (hνs k).2
    simp only [hR, hη] at this
    linarith
  obtain ⟨ν, hνlim, hνdist⟩ := exists_tendsto_of_norm_sub_le_geometric hgeo
  have hνn : ‖ν‖ = 1 := by
    have h := hνlim.norm
    have hc : (fun k ↦ ‖νs k‖) = fun _ ↦ (1 : ℝ) := funext fun k ↦ (hνs k).1.1
    rw [hc] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  refine ⟨ν, ?_, hνn, fun s hs x hx ↦ ?_⟩
  · have := hνdist 0
    rw [hν0, norm_sub_rev] at this
    simp only [pow_zero, mul_one] at this
    linarith
  -- from levels to radii
  set α := Real.log 2 / Real.log r⁻¹ with hα
  obtain ⟨k, hsk, hks⟩ := exists_level_le hr0 hr1 hs.1 (hs.2.trans (by norm_num) : s ≤ 1 / 2)
  have hsρ : s ≤ ρ k := by simp only [hρ]; linarith
  have hxk : x ∈ ball y (ρ k) := ball_subset_ball hsρ hx
  obtain ⟨hl, hu'⟩ := (hνs k).1.2 x hxk
  have hxy : ‖x - y‖ < s := by rw [← dist_eq_norm]; exact hx
  have hinner : |⟪x - y, νs k⟫ - ⟪x - y, ν⟫| ≤ s * (2 * (CI * (5 * ε)) * ((1 : ℝ) / 2) ^ k) := by
    rw [← inner_sub_right]
    calc |⟪x - y, νs k - ν⟫| ≤ ‖x - y‖ * ‖νs k - ν‖ := abs_real_inner_le_norm _ _
      _ ≤ s * (2 * (CI * (5 * ε)) * ((1 : ℝ) / 2) ^ k) :=
          mul_le_mul hxy.le (hνdist k) (norm_nonneg _) hs.1.le
  set K := (1 / 2 : ℝ) ^ (-α) * r ^ (-(1 + α)) with hK
  have hsα : 0 ≤ s ^ (1 + α) := Real.rpow_nonneg hs.1.le _
  have herr : ρ k * η k + s * (2 * (CI * (5 * ε)) * ((1 : ℝ) / 2) ^ k) ≤
      C * ε * s ^ (1 + α) := by
    have h2k : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
    have h1 : s * (2 * (CI * (5 * ε)) * ((1 : ℝ) / 2) ^ k) ≤
        ρ k * (2 * (CI * (5 * ε)) * ((1 : ℝ) / 2) ^ k) :=
      mul_le_mul_of_nonneg_right hsρ (by positivity)
    have h2 : ρ k * η k + ρ k * (2 * (CI * (5 * ε)) * ((1 : ℝ) / 2) ^ k) =
        (1 / 2 * r ^ k * (1 / 2) ^ k) * (ε * (5 + 10 * CI)) := by
      simp only [hρ, hη]; ring
    have h3 : (1 / 2 * r ^ k * (1 / 2) ^ k) * (ε * (5 + 10 * CI)) ≤
        (K * s ^ (1 + α)) * (ε * (5 + 10 * CI)) :=
      mul_le_mul_of_nonneg_right hks (by positivity)
    have h4 : (K * s ^ (1 + α)) * (ε * (5 + 10 * CI)) ≤ C * ε * s ^ (1 + α) := by
      have : K * (5 + 10 * CI) * (ε * s ^ (1 + α)) ≤ C * (ε * s ^ (1 + α)) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
      linarith
    linarith
  obtain ⟨hi1, hi2⟩ := abs_le.1 hinner
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) hq0.le) hl
    linarith
  · refine hu'.trans (mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) hq0.le)
    linarith

/-! ### The output theorem -/

/-- **Pointwise `C^{1,α}` flatness at every free-boundary point** (De Silva (2011), §5, the
"standard iteration argument" of the proof of Theorem 1.1). There are `ε̄ > 0`,
`α ∈ (0, 1)` and `C > 0` (depending on `d` only) with the following property. Let `u` be a
viscosity solution in `U ⊇ B_1` with coefficient `Q`, `|Q - 1| ≤ ε²` and `Lip(Q; B_1) ≤ ε²` on
`B_1`, and `(⟪y, e⟫ - ε)₊ ≤ u ≤ (⟪y, e⟫ + ε)₊` on `B_1`, `0 < ε ≤ ε̄`. Then every free-boundary
point `y ∈ B_{1/2}` has a unit normal `ν(y)` with `‖ν(y) - e‖ ≤ C ε` and
`IsFlatC1AlphaAt u Q y (ν y) (C ε) α (1/4)`.

The smallness is scale-correct (`ε` and `ε²`, as in Lemma 4.1 and §5: `|g_k - 1| ≤ ε_k²`). -/
theorem flat_pointwise_C1alpha (hd : 2 ≤ d) : ∃ εbar > 0, ∃ α ∈ Ioo (0 : ℝ) 1, ∃ C > 0,
    ∀ (U : Set (E d)) (Q u : E d → ℝ) (e : E d) (ε : ℝ), IsOpen U → ball (0 : E d) 1 ⊆ U →
    IsViscSolution U Q u → ‖e‖ = 1 → 0 < ε → ε ≤ εbar →
    (∀ y ∈ ball (0 : E d) 1, |Q y - 1| ≤ ε ^ 2) → LipschitzOnWith (ε ^ 2).toNNReal Q (ball 0 1) →
    (∀ y ∈ ball (0 : E d) 1, max (⟪y, e⟫ - ε) 0 ≤ u y ∧ u y ≤ max (⟪y, e⟫ + ε) 0) →
    ∃ ν : E d → E d, ∀ y ∈ freeBoundary u U ∩ ball 0 (1 / 2),
      ‖ν y - e‖ ≤ C * ε ∧ IsFlatC1AlphaAt u Q y (ν y) (C * ε) α (1 / 4) := by
  obtain ⟨r₀, hr₀, CI, hCI, H⟩ := improvement_of_flatness hd
  set r := min r₀ (1 / 4) with hr
  have hr0 : 0 < r := lt_min hr₀ (by norm_num)
  have hr4 : r ≤ 1 / 4 := min_le_right _ _
  obtain ⟨ε₀, hε₀, Himp⟩ := H r hr0 (min_le_left _ _)
  set α := Real.log 2 / Real.log r⁻¹ with hα
  have hαmem := log_two_div_log_inv_mem hr0 hr4
  set K := (1 / 2 : ℝ) ^ (-α) * r ^ (-(1 + α)) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨min (ε₀ / 5) (1 / 10), by positivity, α, ⟨hαmem.1, by linarith [hαmem.2]⟩,
    max (10 * CI) (K * (5 + 10 * CI)), by positivity, ?_⟩
  intro U Q u e ε hU hB hu he hε hεb hQ hL hflat
  have hε1 : ε ≤ 1 / 10 := hεb.trans (min_le_right _ _)
  have hεε₀ : 5 * ε ≤ ε₀ := by
    have := hεb.trans (min_le_left _ _); linarith
  have hpt : ∀ y, ∃ ν : E d, y ∈ freeBoundary u U ∩ ball 0 (1 / 2) →
      ‖ν - e‖ ≤ max (10 * CI) (K * (5 + 10 * CI)) * ε ∧
        IsFlatC1AlphaAt u Q y ν (max (10 * CI) (K * (5 + 10 * CI)) * ε) α (1 / 4) := by
    intro y
    by_cases hy : y ∈ freeBoundary u U ∩ ball 0 (1 / 2)
    · obtain ⟨ν, hν1, hν2⟩ := flat_C1alpha_at_point Himp hr0 hr4 hCI (le_max_right _ _) hU hB
        hu he hε hε1 hεε₀ hQ hL hflat hy
      refine ⟨ν, fun _ ↦ ⟨hν1.trans ?_, hν2⟩⟩
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le
    · exact ⟨e, fun h ↦ absurd h hy⟩
  choose ν hν using hpt
  exact ⟨ν, fun y hy ↦ hν y hy⟩

end EllipticBernoulli
