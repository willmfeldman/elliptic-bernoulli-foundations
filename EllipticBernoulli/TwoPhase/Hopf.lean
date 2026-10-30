/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Defs
import EllipticBernoulli.TwoPhase.Regularity
import EllipticBernoulli.Harmonic.Basic
import EllipticBernoulli.Harmonic.Comparison
import EllipticBernoulli.Harmonic.Radial

/-!
# The Hopf point

Throughout, `u : ℝᵈ → ℝ` is `L`-Lipschitz and a local minimizer of
`J(v, B) = ∫_B |∇v|² + 1_{v > 0}` on `ℝᵈ`, with no sign condition.

* `IsLocalEnergyMinimizer.exists_hopf_point`: if `u` takes a negative
  and a positive value, there is a ball `B_ρ(y) ⊆ {u < 0}` touching `{u ≥ 0}` at a point `x₀` with
  `u(x₀) = 0`, `x₀ ∈ ∂{u < 0} ∩ closure {u > 0}`, and `u⁻ ≥ c₁ (ρ - |x - y|)` on the annulus
  `B̄_ρ(y) \ B_{ρ/2}(y)`.
* `IsLocalEnergyMinimizer.exists_le_rescale_of_mem_closure_posSet` (the positive phase survives
  blow-up): for every `z ∈ closure {u > 0}`, every pointwise limit of
  rescalings `u(z + r_k x) / r_k` (with any `r_k > 0`) takes a value `≥ c_d` on `B̄₁`.
* `le_negPart_of_tendsto_rescale_of_annulus` (the negative phase survives blow-up): at
  the Hopf point, every pointwise limit `u₀` of rescalings with `r_k → 0⁺` satisfies
  `u₀⁻(x) ≥ c₁ (x · ν)⁺`, `ν = (y - x₀)/ρ`.
* `IsLocalEnergyMinimizer.exists_hopf_point_blowup`: the two combined.

Pointwise limits suffice (no uniform convergence is assumed), because the rescalings are
equi-Lipschitz.

## The barrier

The lower bound on the annulus compares `u⁻ = -u`, which is harmonic on `B_ρ(y) ⊆ {u < 0}`, with
`h = m₀ · annulusBarrier y (ρ/2) ρ d`, where `m₀ = min_{∂B_{ρ/2}(y)} u⁻ > 0`. The function `h` is
subharmonic off `y` (`laplacian_annulusBarrier_pos`, since `d > d - 2`), equals `m₀` on the inner
sphere and `0` on the outer one, so `h ≤ u⁻` on the annulus by
`le_of_sphere_le_of_laplacian_nonpos_annulus` (with `w := h`, `H := u⁻`). Finally
`|x - y|^{-d} - ρ^{-d} ≥ (ρ - |x - y|) / ρ^{d+1}` for `|x - y| ≤ ρ`.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient Laplacian NNReal ContDiff

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- `(ρ - s) / ρ^{n+1} ≤ s^{-n} - ρ^{-n}` for `0 < s ≤ ρ` and `n ≥ 1`. -/
theorem div_pow_succ_le_rpow_neg_sub {n : ℕ} (hn : 1 ≤ n) {s ρ : ℝ} (hs : 0 < s) (hsρ : s ≤ ρ) :
    (ρ - s) / ρ ^ (n + 1) ≤ s ^ (-(n : ℝ)) - ρ ^ (-(n : ℝ)) := by
  have hρ : 0 < ρ := hs.trans_le hsρ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Real.rpow_neg hs.le, Real.rpow_neg hρ.le, Real.rpow_natCast, Real.rpow_natCast,
    inv_sub_inv (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : s ^ (k + 1) ≤ ρ ^ (k + 1) := pow_le_pow_left₀ hs.le hsρ _
  have h2 : s ^ k ≤ ρ ^ k := pow_le_pow_left₀ hs.le hsρ _
  have h3 : ρ ^ k * (ρ - s) ≤ ρ ^ (k + 1) - s ^ (k + 1) := by
    rw [pow_succ, pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right h2 hs.le]
  have hρs : 0 ≤ ρ - s := sub_nonneg.2 hsρ
  calc (ρ - s) * (s ^ (k + 1) * ρ ^ (k + 1))
      ≤ (ρ - s) * (ρ ^ (k + 1) * ρ ^ (k + 1)) := by gcongr
    _ = ρ ^ k * (ρ - s) * ρ ^ (k + 1 + 1) := by ring
    _ ≤ (ρ ^ (k + 1) - s ^ (k + 1)) * ρ ^ (k + 1 + 1) := by gcongr

/-- A space `E d` containing two distinct points has `1 ≤ d`. -/
theorem one_le_of_ne {x y : E d} (hxy : x ≠ y) : 1 ≤ d := by
  rcases Nat.eq_zero_or_pos d with rfl | h
  · exact absurd (Subsingleton.elim x y) hxy
  · exact h

/-- **The Hopf point.** If `u(x₋) < 0` and `u` takes a positive
value, there are `y`, `ρ > 0` and `x₀` with `|x₀ - y| = ρ` such that
(i) `B_ρ(y) ⊆ {u < 0}` and `u(x₀) = 0`;
(ii) `x₀ ∈ ∂{u < 0} ∩ closure {u > 0}`;
(iii) there is `c₁ > 0` with `-u(x) ≥ c₁ (ρ - |x - y|)` on the closed annulus
`B̄_ρ(y) \ B_{ρ/2}(y)`. -/
theorem IsLocalEnergyMinimizer.exists_hopf_point {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) {xn : E d}
    (hneg : u xn < 0) (hpos : ∃ x, 0 < u x) :
    ∃ (y : E d) (ρ : ℝ) (x₀ : E d), 0 < ρ ∧ dist x₀ y = ρ ∧ ball y ρ ⊆ {x | u x < 0} ∧
      u x₀ = 0 ∧ x₀ ∈ frontier {x | u x < 0} ∧ x₀ ∈ closure {x | 0 < u x} ∧
      ∃ c₁ > 0, ∀ x ∈ closedBall y ρ \ ball y (ρ / 2), c₁ * (ρ - dist x y) ≤ -u x := by
  obtain ⟨xp, hxp⟩ := hpos
  have hd : 1 ≤ d := one_le_of_ne (x := xn) (y := xp) fun h ↦ by
    rw [h] at hneg; linarith
  set S : Set (E d) := {x | 0 ≤ u x}
  have hS : IsClosed S := isClosed_le continuous_const hu.continuous
  have hSne : S.Nonempty := ⟨xp, show 0 ≤ u xp from le_of_lt hxp⟩
  set y := xn
  set ρ := infDist y S
  have hρ : 0 < ρ := (hS.notMem_iff_infDist_pos hSne).1 fun h ↦ by
    have : 0 ≤ u y := h
    linarith
  obtain ⟨x₀, hx₀S, hx₀d⟩ := hS.exists_infDist_eq_dist hSne y
  have hdist : dist x₀ y = ρ := by rw [dist_comm, ← hx₀d]
  have hball : ball y ρ ⊆ {x | u x < 0} := fun z hz ↦ by
    by_contra h
    have hzS : z ∈ S := show 0 ≤ u z from not_lt.1 h
    have := infDist_le_dist_of_mem (x := y) hzS
    rw [mem_ball, dist_comm] at hz
    linarith
  have hopen : IsOpen {x | u x < 0} := isOpen_lt hu.continuous continuous_const
  have hclosure : closedBall y ρ ⊆ closure {x | u x < 0} := by
    rw [← closure_ball y hρ.ne']
    exact closure_mono hball
  have hnonpos : ∀ x ∈ closedBall y ρ, u x ≤ 0 := fun x hx ↦
    closure_minimal (fun z (hz : u z < 0) ↦ (le_of_lt hz : u z ≤ 0))
      (isClosed_le hu.continuous continuous_const) (hclosure hx)
  have hx₀B : x₀ ∈ closedBall y ρ := by rw [mem_closedBall, hdist]
  have hu0 : u x₀ = 0 := le_antisymm (hnonpos x₀ hx₀B) hx₀S
  have hfront : x₀ ∈ frontier {x | u x < 0} := by
    rw [hopen.frontier_eq]
    exact ⟨hclosure hx₀B, fun h ↦ by
      have : u x₀ < 0 := h
      linarith⟩
  refine ⟨y, ρ, x₀, hρ, hdist, hball, hu0, hfront,
    (hmin.apply_eq_zero_and_mem_closure_of_mem_frontier hu hfront).2, ?_⟩
  -- the barrier
  have : Nontrivial (E d) := nontrivial_E_of_one_le hd
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hρ2ρ : ρ / 2 < ρ := half_lt_self hρ
  obtain ⟨xm, hxm, hxmin⟩ := (isCompact_sphere y (ρ / 2)).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hρ2.le) hu.continuous.neg.continuousOn
  set m₀ := -u xm
  have hm₀ : 0 < m₀ := by
    have : u xm < 0 := hball (sphere_subset_ball hρ2ρ hxm)
    simp only [m₀]; linarith
  set γ : ℝ := (d : ℝ)
  have hγ : 0 < γ := by simp only [γ]; exact_mod_cast hd
  set Dn := (ρ / 2) ^ (-γ) - ρ ^ (-γ)
  have hDn : 0 < Dn := annulusBarrier_denom_pos hρ2 hρ2ρ hγ
  set h : E d → ℝ := m₀ • annulusBarrier y (ρ / 2) ρ γ
  set A : Set (E d) := ball y ρ \ closedBall y (ρ / 2)
  have hAopen : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  have hAne : ∀ x ∈ closedBall y ρ \ ball y (ρ / 2), x ≠ y := fun x hx hxy ↦ by
    have := hx.2
    rw [hxy, mem_ball, dist_self] at this
    exact this hρ2
  have hAne' : ∀ x ∈ A, x ≠ y := fun x hx ↦
    hAne x ⟨ball_subset_closedBall hx.1, fun h' ↦ hx.2 (ball_subset_closedBall h')⟩
  have hhs : ContDiffOn ℝ ∞ h {x | x ≠ y} :=
    (contDiffOn_annulusBarrier y (ρ / 2) ρ γ).const_smul m₀
  have hcmp := le_of_sphere_le_of_laplacian_nonpos_annulus hd (z := y) (ρ₁ := ρ / 2) (ρ₂ := ρ)
    (w := h) (H := fun x ↦ -u x)
    (isViscSubharmonicOn_of_laplacian_nonneg hAopen
      ((hhs.mono fun x hx ↦ hAne' x hx).of_le (by norm_cast)) fun x hx ↦ by
        have hc : ContDiffAt ℝ 2 (annulusBarrier y (ρ / 2) ρ γ) x :=
          ((contDiffOn_annulusBarrier y (ρ / 2) ρ γ).contDiffAt
            (isOpen_ne.mem_nhds (hAne' x hx))).of_le (by norm_cast)
        rw [laplacian_smul _ hc]
        exact mul_nonneg hm₀.le (laplacian_annulusBarrier_pos (hAne' x hx) hρ2 hρ2ρ hγ
          (by simp only [γ]; linarith)).le)
    (hhs.continuousOn.mono fun x hx ↦ hAne x hx)
    ((hmin.contDiffOn_negSet hu).neg.mono fun x hx ↦ hball hx.1)
    (fun x hx ↦ by
      have hx' : u x < 0 := hball hx.1
      have hh := (hmin.harmonicOnNhd_negSet hu x hx').2.eq_of_nhds
      rw [show (fun x ↦ -u x) = -u from rfl, laplacian_neg, Pi.neg_apply, hh, Pi.zero_apply,
        neg_zero])
    hu.continuous.neg.continuousOn
    (fun x hx ↦ by
      simp only [h, Pi.smul_apply, smul_eq_mul, annulusBarrier_eq_one hρ2 hρ2ρ hγ x hx,
        mul_one]
      exact hxmin hx)
    (fun x hx ↦ by
      simp only [h, Pi.smul_apply, smul_eq_mul, annulusBarrier_eq_zero x hx, mul_zero]
      have := hnonpos x (sphere_subset_closedBall hx)
      linarith)
  refine ⟨m₀ / (Dn * ρ ^ (d + 1)), by positivity, fun x hx ↦ ?_⟩
  refine le_trans ?_ (hcmp x hx)
  have hs : 0 < dist x y := dist_pos.2 (hAne x hx)
  have hsρ : dist x y ≤ ρ := hx.1
  have key := div_pow_succ_le_rpow_neg_sub hd hs hsρ
  simp only [h, Pi.smul_apply, smul_eq_mul, annulusBarrier, ← dist_eq_norm]
  calc m₀ / (Dn * ρ ^ (d + 1)) * (ρ - dist x y)
      = m₀ * ((ρ - dist x y) / ρ ^ (d + 1) / Dn) := by field_simp
    _ ≤ m₀ * ((dist x y ^ (-γ) - ρ ^ (-γ)) / Dn) := by gcongr

/-! ### Both phases survive blow-up -/

/-- **The positive phase survives blow-up.** Let `d ≥ 1`,
`z ∈ closure {u > 0}` and `r_k > 0` (any sequence: `r_k → 0` and `r_k → ∞` are both allowed). If
the rescalings `u(z + r_k x) / r_k` converge pointwise to `u₀`, then `u₀(y) ≥ c_d` for some
`y ∈ B̄₁`, with `c_d = 1 / (8 d e^{d/2})`. -/
theorem IsLocalEnergyMinimizer.exists_le_rescale_of_mem_closure_posSet (hd : 1 ≤ d)
    {u : E d → ℝ} {L : ℝ≥0} (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hu : LipschitzWith L u) {z : E d} (hz : z ∈ closure {x | 0 < u x}) {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) {u₀ : E d → ℝ}
    (hlim : ∀ x, Tendsto (fun k ↦ u (z + r k • x) / r k) atTop (𝓝 (u₀ x))) :
    ∃ y ∈ closedBall (0 : E d) 1, 1 / (8 * d * Real.exp ((d : ℝ) / 2)) ≤ u₀ y := by
  set c := 1 / (8 * d * Real.exp ((d : ℝ) / 2))
  have hpt : ∀ k, ∃ x ∈ closedBall (0 : E d) 1, c ≤ u (z + r k • x) / r k := by
    intro k
    obtain ⟨y, hy, hle⟩ := hmin.exists_le_of_mem_closure_posSet hd hu hz (hr k)
    refine ⟨(r k)⁻¹ • (y - z), ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.2 (hr k)), ← dist_eq_norm, inv_mul_le_iff₀ (hr k), mul_one]
      exact hy
    · rw [smul_smul, mul_inv_cancel₀ (hr k).ne', one_smul, add_sub_cancel,
        le_div_iff₀ (hr k)]
      exact hle
  choose x hx hxc using hpt
  obtain ⟨a, ha, φ, hφ, hlimx⟩ := (isCompact_closedBall (0 : E d) 1).tendsto_subseq hx
  refine ⟨a, ha, ?_⟩
  have hb : ∀ k, c - L * dist (x (φ k)) a ≤ u (z + r (φ k) • a) / r (φ k) := by
    intro k
    have hk := hr (φ k)
    have hL := hu.dist_le_mul (z + r (φ k) • x (φ k)) (z + r (φ k) • a)
    rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos hk] at hL
    have h1 : u (z + r (φ k) • x (φ k)) / r (φ k) - u (z + r (φ k) • a) / r (φ k) ≤
        L * dist (x (φ k)) a := by
      rw [← sub_div, div_le_iff₀ hk]
      calc _ ≤ |u (z + r (φ k) • x (φ k)) - u (z + r (φ k) • a)| := le_abs_self _
        _ = dist (u (z + r (φ k) • x (φ k))) (u (z + r (φ k) • a)) := (Real.dist_eq _ _).symm
        _ ≤ L * (r (φ k) * dist (x (φ k)) a) := hL
        _ = L * dist (x (φ k)) a * r (φ k) := by ring
    linarith [hxc (φ k)]
  have hlo : Tendsto (fun k ↦ c - L * dist (x (φ k)) a) atTop (𝓝 (c - L * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul
      ((tendsto_iff_dist_tendsto_zero.1 hlimx)))
  rw [mul_zero, sub_zero] at hlo
  exact le_of_tendsto_of_tendsto' hlo ((hlim a).comp hφ.tendsto_atTop) hb

/-- `ρ - |x₀ + t x - y| = t (2 ⟨x, y - x₀⟩ - t |x|²) / (ρ + |t x - (y - x₀)|)` when
`|y - x₀| = ρ > 0`. -/
private theorem sub_dist_eq {x₀ y x : E d} {ρ t : ℝ} (hρ : 0 < ρ) (hdist : dist x₀ y = ρ) :
    ρ - dist (x₀ + t • x) y = t * ((2 * inner ℝ x (y - x₀) - t * ‖x‖ ^ 2) /
      (ρ + ‖t • x - (y - x₀)‖)) := by
  have he : ‖y - x₀‖ = ρ := by rw [← dist_eq_norm, dist_comm, hdist]
  have hb : dist (x₀ + t • x) y = ‖t • x - (y - x₀)‖ := by
    rw [dist_eq_norm]; congr 1; abel
  have hpos : 0 < ρ + ‖t • x - (y - x₀)‖ := by positivity
  rw [hb, mul_div_assoc', eq_div_iff hpos.ne']
  have hsq : ‖t • x - (y - x₀)‖ ^ 2 = t ^ 2 * ‖x‖ ^ 2 - 2 * t * inner ℝ x (y - x₀) + ρ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_left, he]
    simp only [conj_trivial]
    ring
  nlinarith [hsq]

/-- **The negative phase survives blow-up at the Hopf point.**
Let `ρ > 0`, `|x₀ - y| = ρ`, and `-u(x) ≥ c₁ (ρ - |x - y|)` on `B̄_ρ(y) \ B_{ρ/2}(y)` (the
conclusion (iii) of `IsLocalEnergyMinimizer.exists_hopf_point`). If `r_k → 0⁺` and the rescalings
`u(x₀ + r_k x) / r_k` converge pointwise to `u₀`, then `u₀⁻(x) ≥ c₁ (x · ν)⁺` with
`ν = (y - x₀) / ρ`. -/
theorem le_negPart_of_tendsto_rescale_of_annulus {u : E d → ℝ} {x₀ y : E d} {ρ c₁ : ℝ}
    (hρ : 0 < ρ) (hdist : dist x₀ y = ρ)
    (hbound : ∀ x ∈ closedBall y ρ \ ball y (ρ / 2), c₁ * (ρ - dist x y) ≤ -u x)
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0)) {u₀ : E d → ℝ}
    (hlim : ∀ x, Tendsto (fun k ↦ u (x₀ + r k • x) / r k) atTop (𝓝 (u₀ x))) (x : E d) :
    c₁ * max (inner ℝ x (ρ⁻¹ • (y - x₀))) 0 ≤ max (-u₀ x) 0 := by
  set a := inner ℝ x (ρ⁻¹ • (y - x₀))
  rcases le_or_gt a 0 with ha | ha
  · rw [max_eq_right ha, mul_zero]; exact le_max_right _ _
  rw [max_eq_left ha.le]
  refine le_trans ?_ (le_max_left _ _)
  set g : ℝ → ℝ := fun t ↦ (2 * inner ℝ x (y - x₀) - t * ‖x‖ ^ 2) / (ρ + ‖t • x - (y - x₀)‖)
  have he : ‖y - x₀‖ = ρ := by rw [← dist_eq_norm, dist_comm, hdist]
  have hg0 : g 0 = a := by
    simp only [g, zero_smul, zero_sub, norm_neg, he, zero_mul, sub_zero, a, inner_smul_right]
    field_simp
    ring
  have hgc : ContinuousAt g 0 := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    simp only [zero_smul, zero_sub, norm_neg, he]
    linarith
  have hgt : Tendsto (fun k ↦ g (r k)) atTop (𝓝 a) := hg0 ▸ hgc.tendsto.comp hr0
  have hdc : Tendsto (fun k ↦ dist (x₀ + r k • x) y) atTop (𝓝 ρ) := by
    have : ContinuousAt (fun t : ℝ ↦ dist (x₀ + t • x) y) 0 := by fun_prop
    have h := this.tendsto.comp hr0
    simp only [zero_smul, add_zero, hdist] at h
    exact h
  have hρ2 : ρ / 2 < ρ := half_lt_self hρ
  have hev : ∀ᶠ k in atTop, c₁ * g (r k) ≤ -(u (x₀ + r k • x) / r k) := by
    filter_upwards [hgt.eventually (lt_mem_nhds ha), hdc.eventually (lt_mem_nhds hρ2)]
      with k hgk hdk
    have hk := hr k
    have hid := sub_dist_eq (x := x) (t := r k) hρ hdist
    have hmem : x₀ + r k • x ∈ closedBall y ρ \ ball y (ρ / 2) := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall]
        have : 0 ≤ r k * g (r k) := mul_nonneg hk.le hgk.le
        linarith
      · rw [mem_ball, not_lt]; exact hdk.le
    have hb := hbound _ hmem
    rw [hid] at hb
    rw [← neg_div, le_div_iff₀ hk]
    linarith
  exact le_of_tendsto_of_tendsto (hgt.const_mul c₁) (hlim x).neg hev

/-- **Both phases survive blow-up at the Hopf point.** If `u` takes a negative and a positive value,
there are `y`, `ρ > 0`, `x₀` with `|x₀ - y| = ρ`, `u(x₀) = 0`, `x₀ ∈ ∂{u < 0} ∩ closure {u > 0}`,
and `c₁ > 0`, such that for every sequence `r_k > 0` along which the rescalings
`u(x₀ + r_k x) / r_k` converge pointwise to `u₀`:
* if `r_k → 0`, then `u₀⁻(x) ≥ c₁ (x · ν)⁺` for every `x`, with `ν = (y - x₀) / ρ`;
* `u₀(z) ≥ c_d = 1 / (8 d e^{d/2})` for some `z ∈ B̄₁` (whatever the behaviour of `r_k`, so in
  particular for `r_k → 0` and for `r_k → ∞`). -/
theorem IsLocalEnergyMinimizer.exists_hopf_point_blowup {u : E d → ℝ} {L : ℝ≥0}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hu : LipschitzWith L u) {xn : E d}
    (hneg : u xn < 0) (hpos : ∃ x, 0 < u x) :
    ∃ (y : E d) (ρ : ℝ) (x₀ : E d) (c₁ : ℝ), 0 < ρ ∧ dist x₀ y = ρ ∧ u x₀ = 0 ∧
      x₀ ∈ frontier {x | u x < 0} ∧ x₀ ∈ closure {x | 0 < u x} ∧ 0 < c₁ ∧
      ∀ (r : ℕ → ℝ) (u₀ : E d → ℝ), (∀ k, 0 < r k) →
        (∀ x, Tendsto (fun k ↦ u (x₀ + r k • x) / r k) atTop (𝓝 (u₀ x))) →
        (Tendsto r atTop (𝓝 0) →
          ∀ x, c₁ * max (inner ℝ x (ρ⁻¹ • (y - x₀))) 0 ≤ max (-u₀ x) 0) ∧
        ∃ z ∈ closedBall (0 : E d) 1, 1 / (8 * d * Real.exp ((d : ℝ) / 2)) ≤ u₀ z := by
  obtain ⟨xp, hxp⟩ := hpos
  have hd : 1 ≤ d := one_le_of_ne (x := xn) (y := xp) fun h ↦ by
    rw [h] at hneg; linarith
  obtain ⟨y, ρ, x₀, hρ, hdist, -, hu0, hfront, hcl, c₁, hc₁, hbound⟩ :=
    hmin.exists_hopf_point hu hneg ⟨xp, hxp⟩
  refine ⟨y, ρ, x₀, c₁, hρ, hdist, hu0, hfront, hcl, hc₁, fun r u₀ hr hlim ↦ ⟨fun hr0 ↦
    le_negPart_of_tendsto_rescale_of_annulus hρ hdist hbound hr hr0 hlim,
    hmin.exists_le_rescale_of_mem_closure_posSet hd hu hcl hr hlim⟩⟩

end EllipticBernoulli
