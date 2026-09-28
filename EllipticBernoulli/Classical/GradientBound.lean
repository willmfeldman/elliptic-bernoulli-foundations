/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Classical
import EllipticBernoulli.Classical.BlowupExtraction
import EllipticBernoulli.Classical.Modulus
import EllipticBernoulli.Classical.Rigidity
import EllipticBernoulli.Classical.Viscosity
import EllipticBernoulli.Common.Calculus
import EllipticBernoulli.Harmonic.Basic
import EllipticBernoulli.Harmonic.Limit
import EllipticBernoulli.Lipschitz.Estimate
import EllipticBernoulli.Lipschitz.LinearGrowth
import EllipticBernoulli.Viscosity.Affine
import EllipticBernoulli.Viscosity.Local
import EllipticBernoulli.Viscosity.Stability

/-!
# The Alt–Caffarelli gradient bound

`classical_lipschitz_bound` (`ClassicalLipschitzBoundStatement`): for each `L` there is a modulus
`w`, continuous and monotone on `[0, 1)` with `w(0+) = 0`, such that every classical solution `u`
in `B_1` with `Q ≡ 1`, `L`-Lipschitz and with `u(0) = 0`, is `(1 + w(r))`-Lipschitz on `B_r`. The
modulus depends on `n` and `L`, and it is uniform over the whole class. Kriventsov–Weiss,
Proposition 9.1, state the bound with `ω` depending on `n` only; the form proved here is weaker.

Kriventsov–Weiss refer to Alt–Caffarelli, Theorem 6.3, which is proved for the weak solutions of
Alt–Caffarelli (with non-degeneracy bounds and `Δu` equal to `Q` times surface measure on the
reduced free boundary). Classical solutions need not be weak solutions in that sense: `u = |x_n|`
is classical (points with `{u > 0}` on both sides of the free boundary are allowed), but its
reduced free boundary is empty. We prove the statement by the blow-up argument of Alt–Caffarelli,
Remark 6.4, made uniform over the class. It needs neither the flatness theory nor the gradient up
to the free boundary.

## Proof

Let `𝒞_L` be the class, and `ℓ(s) = sup {‖∇u(y)‖ : u ∈ 𝒞_L, y ∈ B_s ∩ B_1, u(y) > 0}`
(`gradSup`, with `sup ∅ = 0`). `ℓ ≤ L` and `ℓ` is monotone; let `ℓ₀ = lim_{s→0+} ℓ(s)`.

1. **`ℓ₀ ≤ 1`** (`gradLim_le_one`). Otherwise pick `u_k ∈ 𝒞_L`, `|y_k| < r_k → 0`, `u_k(y_k) > 0`,
   `‖∇u_k(y_k)‖ > ℓ₀ − 1/(k+1)`. Let `d_k ≤ |y_k|` be the distance to the nearest zero
   (`exists_nearest_zero`) and `v_k(z) = u_k(y_k + d_k z)/d_k`. The `v_k` are `L`-Lipschitz on
   `B_{ρ_k}`, `ρ_k → ∞`, positive and harmonic on `B_1`, and viscosity supersolutions
   (`IsClassicalSolution.isViscSuper`, `IsViscSuper.rescale`). A subsequence converges locally
   uniformly to `v` (`exists_blowup_subseq`). By the harmonic limit theorem, `v` is harmonic in
   `{v > 0}` with `∇v_k → ∇v` there; `‖∇v‖ ≤ ℓ₀` on `{v > 0}`, because the rescaled positive points
   lie in `B_{r_k(1+|z|)}`; and `‖∇v(0)‖ ≥ ℓ₀`, so `v(0) > 0`. By stability `v` is a
   supersolution on every ball. This contradicts `false_of_isViscSuper_of_norm_gradient_attained`.
2. **Modulus.** `g(s) = max(ℓ(s) − 1, 0)` is monotone with `g(0) = 0` and `g(0+) = 0`; its average
   `w = avgModulus g` is continuous and monotone and dominates `g`.
3. **Lipschitz bound.** On `B_r`, `‖∇u‖ ≤ ℓ(r) ≤ 1 + w(r)` at positive points and `u = 0`
   elsewhere, so `sub_le_mul_dist_of_norm_gradient_le` gives the Lipschitz bound.

No dimension restriction is needed: every tool used holds for all `n` (for `n = 0` all gradients
vanish).

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free boundary*,
  J. Reine Angew. Math. 325 (1981), 105–144.
* D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131. Result numbers are those of arXiv:2306.10131v2.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped NNReal ContDiff Gradient Laplacian

public section

namespace EllipticBernoulli

variable {n : ℕ}

/-! ### The class `𝒞_L` and the gradient supremum `ℓ(s)` -/

/-- The class `𝒞_L`: classical solutions in `B_1` with `Q ≡ 1`, `L`-Lipschitz, vanishing at `0`. -/
private def InClass (L : ℝ≥0) (u : E n → ℝ) : Prop :=
  IsClassicalSolution (ball (0 : E n) 1) (fun _ ↦ 1) u ∧ LipschitzOnWith L u (ball 0 1) ∧ u 0 = 0

/-- The gradient norms `‖∇u(y)‖`, `u ∈ 𝒞_L`, `y ∈ B_s ∩ B_1`, `u(y) > 0`. -/
private def gradSet (L : ℝ≥0) (s : ℝ) : Set ℝ :=
  {a | ∃ u : E n → ℝ, InClass L u ∧
    ∃ y ∈ ball (0 : E n) s, y ∈ ball (0 : E n) 1 ∧ 0 < u y ∧ ‖∇ u y‖ = a}

/-- `ℓ(s)`, the supremum of `gradSet L s` (`0` if it is empty). -/
private noncomputable def gradSup (L : ℝ≥0) (s : ℝ) : ℝ := sSup (gradSet (n := n) L s)

private theorem le_of_mem_gradSet {L : ℝ≥0} {s a : ℝ} (ha : a ∈ gradSet (n := n) L s) :
    a ≤ L := by
  obtain ⟨u, ⟨-, hL, -⟩, y, -, hy1, -, rfl⟩ := ha
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hy1) hL

private theorem bddAbove_gradSet (L : ℝ≥0) (s : ℝ) : BddAbove (gradSet (n := n) L s) :=
  ⟨L, fun _ ha ↦ le_of_mem_gradSet ha⟩

private theorem gradSup_nonneg (L : ℝ≥0) (s : ℝ) : 0 ≤ gradSup (n := n) L s :=
  Real.sSup_nonneg fun _ ⟨_, _, _, _, _, _, ha⟩ ↦ ha ▸ norm_nonneg _

private theorem le_gradSup {L : ℝ≥0} {s : ℝ} {u : E n → ℝ} (hu : InClass L u) {y : E n}
    (hys : y ∈ ball (0 : E n) s) (hy1 : y ∈ ball (0 : E n) 1) (hpos : 0 < u y) :
    ‖∇ u y‖ ≤ gradSup (n := n) L s :=
  le_csSup (bddAbove_gradSet L s) ⟨u, hu, y, hys, hy1, hpos, rfl⟩

private theorem gradSup_mono (L : ℝ≥0) : Monotone (gradSup (n := n) L) := by
  intro s s' hss
  rcases (gradSet (n := n) L s).eq_empty_or_nonempty with h | h
  · rw [gradSup, h, Real.sSup_empty]; exact gradSup_nonneg L s'
  · refine csSup_le_csSup (bddAbove_gradSet L s') h ?_
    rintro _ ⟨u, hu, y, hys, hy1, hpos, rfl⟩
    exact ⟨u, hu, y, ball_subset_ball hss hys, hy1, hpos, rfl⟩

private theorem gradSup_zero (L : ℝ≥0) : gradSup (n := n) L 0 = 0 := by
  have : gradSet (n := n) L 0 = ∅ := by
    ext a
    simp only [gradSet, ball_zero, mem_empty_iff_false, false_and, exists_false, and_false,
      mem_setOf_eq]
  rw [gradSup, this, Real.sSup_empty]

/-! ### Blow-up helpers -/

/-- Harmonic limits along a sequence that is harmonic on `U` only eventually. -/
private theorem harmonic_limit_eventually {F : ℕ → E n → ℝ} {f : E n → ℝ} {U : Set (E n)}
    (hU : IsOpen U) (hF : ∀ᶠ k in atTop, HarmonicOnNhd (F k) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    HarmonicOnNhd f U ∧ ∀ z ∈ U, Tendsto (fun k ↦ fderiv ℝ (F k) z) atTop (𝓝 (fderiv ℝ f z)) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hF
  have hG : TendstoLocallyUniformlyOn (fun k ↦ F (k + K)) f atTop U := fun s hs x hx ↦ by
    obtain ⟨t, ht, h⟩ := hconv s hs x hx
    exact ⟨t, ht, (tendsto_add_atTop_nat K).eventually h⟩
  obtain ⟨hf, hd⟩ := harmonicOnNhd_of_tendstoLocallyUniformlyOn' hU
    (fun k ↦ hK (k + K) (Nat.le_add_left K k)) hG
  exact ⟨hf, fun z hz ↦ (tendsto_add_atTop_iff_nat K).1 (hd.tendsto_at hz)⟩

/-- The derivative of the rescaling `z ↦ u(y + d z)/d` at a differentiability point. -/
private theorem norm_fderiv_rescale {u : E n → ℝ} {y z : E n} {d : ℝ} (hd : 0 < d)
    (hu : DifferentiableAt ℝ u (y + d • z)) :
    ‖fderiv ℝ (fun z ↦ u (y + d • z) / d) z‖ = ‖∇ u (y + d • z)‖ := by
  have hA : HasFDerivAt (fun z : E n ↦ y + d • z) (d • ContinuousLinearMap.id ℝ (E n)) z :=
    ((hasFDerivAt_id z).const_smul d).const_add y
  have hc := (hu.hasFDerivAt.comp z hA).const_mul d⁻¹
  have hfun : (fun z ↦ u (y + d • z) / d) = fun z ↦ d⁻¹ * (u ∘ fun z ↦ y + d • z) z := by
    funext w; simp [div_eq_inv_mul]
  have hL : d⁻¹ • (fderiv ℝ u (y + d • z)).comp (d • ContinuousLinearMap.id ℝ (E n)) =
      fderiv ℝ u (y + d • z) := by
    ext w
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    field_simp
  rw [hfun, hc.fderiv, hL, norm_gradient_eq_norm_fderiv]

/-! ### Step 1: `ℓ₀ ≤ 1` -/

/-- **The blow-up limit of `ℓ` is at most `1`.** -/
private theorem gradLim_le_one (L : ℝ≥0) : sInf (gradSup (n := n) L '' Ioi 0) ≤ 1 := by
  set ℓ₀ := sInf (gradSup (n := n) L '' Ioi 0) with hℓ₀def
  by_contra hcon
  push Not at hcon
  have hℓle : ∀ s, 0 < s → ℓ₀ ≤ gradSup (n := n) L s := fun s hs ↦
    csInf_le ⟨0, by rintro _ ⟨t, -, rfl⟩; exact gradSup_nonneg L t⟩ (mem_image_of_mem _ hs)
  have hlim : Tendsto (gradSup (n := n) L) (𝓝[>] 0) (𝓝 ℓ₀) := (gradSup_mono L).tendsto_nhdsGT 0
  -- scales
  have hk2 : Tendsto (fun k : ℕ ↦ (k : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  set r : ℕ → ℝ := fun k ↦ ((k : ℝ) + 2)⁻¹ with hr
  set ρ : ℕ → ℝ := fun k ↦ ((k : ℝ) + 2) / 2 with hρ
  have hr0 : ∀ k, 0 < r k := fun k ↦ by positivity
  have hr2 : ∀ k, r k ≤ 1 / 2 := fun k ↦ by
    rw [hr, inv_le_comm₀ (by positivity) (by norm_num)]; norm_num
  have hρ0 : ∀ k, 0 < ρ k := fun k ↦ by positivity
  have hρ1 : ∀ k, 1 ≤ ρ k := fun k ↦ by
    rw [hρ, le_div_iff₀ (by norm_num)]; have := k.cast_nonneg (α := ℝ); linarith
  have hrρ : ∀ k, r k * ρ k = 1 / 2 := fun k ↦ by
    rw [hr, hρ]; field_simp
  have hrt : Tendsto r atTop (𝓝 0) := hk2.inv_tendsto_atTop
  have hρt : Tendsto ρ atTop atTop := hk2.atTop_div_const two_pos
  -- near-maximizers
  have hex : ∀ k : ℕ, ∃ u : E n → ℝ, InClass L u ∧ ∃ y ∈ ball (0 : E n) (r k),
      y ∈ ball (0 : E n) 1 ∧ 0 < u y ∧ ℓ₀ - 1 / ((k : ℝ) + 1) < ‖∇ u y‖ := by
    intro k
    have hne : (gradSet (n := n) L (r k)).Nonempty := by
      by_contra h
      rw [not_nonempty_iff_eq_empty] at h
      have := hℓle (r k) (hr0 k)
      rw [gradSup, h, Real.sSup_empty] at this
      linarith
    have hlt : ℓ₀ - 1 / ((k : ℝ) + 1) < sSup (gradSet (n := n) L (r k)) := by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      have := hℓle (r k) (hr0 k)
      rw [gradSup] at this
      linarith
    obtain ⟨a, ⟨u, hu, y, hy, hy1, hpos, rfl⟩, ha⟩ := exists_lt_of_lt_csSup hne hlt
    exact ⟨u, hu, y, hy, hy1, hpos, ha⟩
  choose u hu y hy hy1 hpos hgy using hex
  -- nearest zeros
  have hcb : ∀ k, closedBall (y k) ‖y k‖ ⊆ ball (0 : E n) 1 := fun k z hz ↦ by
    rw [mem_closedBall, dist_eq_norm] at hz
    have hyk := mem_ball_zero_iff.1 (hy k)
    rw [mem_ball_zero_iff]
    calc ‖z‖ = ‖(z - y k) + y k‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y k‖ + ‖y k‖ := norm_add_le _ _
      _ < 1 := by linarith [hr2 k]
  have hnz : ∀ k, ∃ x ∈ closedBall (y k) ‖y k‖, u k x = 0 ∧ 0 < dist x (y k) ∧
      ∀ z ∈ ball (y k) (dist x (y k)), 0 < u k z := fun k ↦
    exists_nearest_zero (hu k).2.1.continuousOn (hu k).1.nonneg (hcb k) (hpos k)
      ⟨0, mem_closedBall.2 (by rw [dist_comm, dist_zero_right]), (hu k).2.2⟩
  choose x hxB hx0 hdpos hballpos using hnz
  set dd : ℕ → ℝ := fun k ↦ dist (x k) (y k) with hdd
  have hdle : ∀ k, dd k ≤ ‖y k‖ := fun k ↦ mem_closedBall.1 (hxB k)
  have hyr : ∀ k, ‖y k‖ < r k := fun k ↦ mem_ball_zero_iff.1 (hy k)
  -- the rescalings
  set A : ℕ → E n → E n := fun k z ↦ y k + dd k • z with hA
  set v : ℕ → E n → ℝ := fun k z ↦ u k (y k + dd k • z) / dd k with hv
  have hnormA : ∀ k z, ‖A k z‖ < r k * (1 + ‖z‖) := fun k z ↦ by
    calc ‖A k z‖ ≤ ‖y k‖ + dd k * ‖z‖ := by
          rw [hA]; refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hdpos k)]
      _ < r k * (1 + ‖z‖) := by
          have := mul_le_mul_of_nonneg_right ((hdle k).trans (hyr k).le) (norm_nonneg z)
          linarith [hyr k]
  have hmap : ∀ k z, z ∈ ball (0 : E n) (ρ k) → A k z ∈ ball (0 : E n) 1 := fun k z hz ↦ by
    rw [mem_ball_zero_iff] at hz ⊢
    calc ‖A k z‖ ≤ ‖y k‖ + dd k * ‖z‖ := by
          rw [hA]; refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hdpos k)]
      _ < 1 := by
          have h1 : dd k * ‖z‖ ≤ r k * ρ k :=
            mul_le_mul ((hdle k).trans (hyr k).le) hz.le (norm_nonneg z) (hr0 k).le
          linarith [hyr k, hr2 k, hrρ k]
  have hpos1 : ∀ k z, z ∈ ball (0 : E n) 1 → 0 < v k z := fun k z hz ↦ by
    refine div_pos (hballpos k _ ?_) (hdpos k)
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (hdpos k)]
    have := mem_ball_zero_iff.1 hz
    calc dd k * ‖z‖ < dd k * 1 := mul_lt_mul_of_pos_left this (hdpos k)
      _ = dist (x k) (y k) := mul_one _
  have hvnn : ∀ k z, z ∈ ball (0 : E n) (ρ k) → 0 ≤ v k z := fun k z hz ↦
    div_nonneg ((hu k).1.nonneg _ (hmap k z hz)) (hdpos k).le
  have hApos : ∀ k z, 0 < v k z → 0 < u k (A k z) := fun k z h ↦
    (div_pos_iff_of_pos_right (hdpos k)).1 h
  have hudiff : ∀ k z, z ∈ ball (0 : E n) (ρ k) → 0 < v k z →
      DifferentiableAt ℝ (u k) (A k z) := fun k z hz h ↦
    ((hu k).1.harmonicAt _ (hmap k z hz) (hApos k z h)).1.differentiableAt (by norm_num)
  have hharmv : ∀ k z, z ∈ ball (0 : E n) (ρ k) → 0 < v k z → HarmonicAt (v k) z := by
    intro k z hz h
    have h1 := HarmonicAt.comp_add_smul ((hu k).1.harmonicAt _ (hmap k z hz) (hApos k z h))
    have h2 := InnerProductSpace.HarmonicAt.const_smul (c := (dd k)⁻¹) h1
    refine (harmonicAt_congr_nhds (Eventually.of_forall fun w ↦ ?_)).1 h2
    simp [hv, div_eq_inv_mul]
  have hgradv : ∀ k z, z ∈ ball (0 : E n) (ρ k) → 0 < v k z →
      ‖fderiv ℝ (v k) z‖ = ‖∇ (u k) (A k z)‖ := fun k z hz h ↦
    norm_fderiv_rescale (hdpos k) (hudiff k z hz h)
  have hLipv : ∀ k, LipschitzOnWith L (v k) (ball 0 (ρ k)) := by
    intro k
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
    have h := (hu k).2.1.dist_le_mul _ (hmap k a ha) _ (hmap k b hb)
    have hAd : dist (A k a) (A k b) = dd k * dist a b := by
      rw [hA, dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_pos (hdpos k)]
    rw [hAd] at h
    rw [hv, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (hdpos k), div_le_iff₀ (hdpos k)]
    rw [Real.dist_eq] at h
    linarith
  have hv0 : ∀ k, |v k 0| ≤ L := by
    intro k
    have hxk : x k ∈ ball (0 : E n) 1 := hcb k (hxB k)
    have h := (hu k).2.1.dist_le_mul _ (hy1 k) _ hxk
    rw [Real.dist_eq, hx0, sub_zero, abs_of_pos (hpos k), dist_comm] at h
    have : v k 0 = u k (y k) / dd k := by simp [hv]
    rw [this, abs_of_pos (div_pos (hpos k) (hdpos k)), div_le_iff₀ (hdpos k)]
    exact h
  have hsuperv : ∀ k, IsViscSuper ((fun z ↦ y k + dd k • z) ⁻¹' ball (0 : E n) 1)
      (fun _ ↦ 1) (v k) := by
    intro k
    have h := (IsClassicalSolution.isViscSuper (hu k).1).rescale (y k) (hdpos k) one_pos
    simp only [div_one, mul_one] at h
    exact h
  -- extraction
  obtain ⟨φ, hφ, V, hVL, hconv⟩ := exists_blowup_subseq hρt hρ0 hLipv hv0
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hVc : Continuous V := hVL.continuous
  have hconvU : ∀ U : Set (E n), TendstoLocallyUniformlyOn (fun k ↦ v (φ k)) V atTop U :=
    fun U ↦ (tendstoLocallyUniformlyOn_univ.2 hconv).mono (subset_univ U)
  have hpt : ∀ z, Tendsto (fun k ↦ v (φ k) z) atTop (𝓝 (V z)) := fun z ↦
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ z)
  have hbig : ∀ R : ℝ, ∀ᶠ k in atTop, R < ρ (φ k) := fun R ↦
    (hρt.comp hφt).eventually_gt_atTop R
  have hV0 : ∀ z, 0 ≤ V z := fun z ↦ by
    refine ge_of_tendsto (hpt z) ?_
    filter_upwards [hbig ‖z‖] with k hk
    exact hvnn _ z (mem_ball_zero_iff.2 hk)
  have hsuperV : ∀ R, 0 < R → IsViscSuper (ball (0 : E n) R) (fun _ ↦ 1) V := by
    intro R _
    refine isViscSuper_of_tendstoLocallyUniformlyOn isOpen_ball continuousOn_const ?_
      (hconvU _)
    filter_upwards [hbig R] with k hk
    exact (hsuperv (φ k)).mono isOpen_ball fun z hz ↦
      hmap (φ k) z (ball_subset_ball hk.le hz)
  -- harmonic limit on `B_1`: the gradient at `0`
  have hB1 : ∀ k, HarmonicOnNhd (v k) (ball (0 : E n) 1) := fun k z hz ↦
    hharmv k z (ball_subset_ball (hρ1 k) hz) (hpos1 k z hz)
  obtain ⟨-, hd1⟩ := harmonic_limit_eventually isOpen_ball
    (Eventually.of_forall fun k ↦ hB1 (φ k)) (hconvU _)
  have hgrad0 : ℓ₀ ≤ ‖fderiv ℝ V 0‖ := by
    have hn := (continuous_norm.tendsto _).comp (hd1 0 (mem_ball_self one_pos))
    have hlow : Tendsto (fun k ↦ ℓ₀ - 1 / ((φ k : ℝ) + 1)) atTop (𝓝 ℓ₀) := by
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφt).const_sub ℓ₀
      simpa using this
    refine le_of_tendsto_of_tendsto' hlow hn fun k ↦ ?_
    simp only [Function.comp_apply]
    rw [hgradv (φ k) 0 (mem_ball_self (hρ0 _)) (hpos1 _ 0 (mem_ball_self one_pos))]
    have : A (φ k) 0 = y (φ k) := by simp [hA]
    rw [this]
    exact (hgy (φ k)).le
  have hVpos0 : 0 < V 0 := by
    rcases (hV0 0).lt_or_eq with h | h
    · exact h
    · have hmin : IsLocalMin V 0 := Eventually.of_forall fun z ↦ by rw [← h]; exact hV0 z
      rw [hmin.fderiv_eq_zero, norm_zero] at hgrad0
      linarith
  -- harmonic limit near positive points: harmonicity and the gradient bound
  have hlocal : ∀ z, 0 < V z → HarmonicAt V z ∧ ‖fderiv ℝ V z‖ ≤ ℓ₀ := by
    intro z hz
    obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hVc :
      IsOpen {w | V z / 2 < V w}) z (by simp only [mem_setOf_eq]; linarith)
    set s := δ / 2 with hs
    have hs0 : 0 < s := by positivity
    have hsub : closedBall z s ⊆ ball z δ := closedBall_subset_ball (by linarith)
    have hunif := Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) _ (isCompact_closedBall z s))
      (V z / 2) (by linarith)
    have hev : ∀ᶠ k in atTop, HarmonicOnNhd (v (φ k)) (ball z s) := by
      filter_upwards [hunif, hbig (‖z‖ + s)] with k hk hkρ w hw
      have hwρ : w ∈ ball (0 : E n) (ρ (φ k)) := by
        rw [mem_ball_zero_iff]
        calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ < ρ (φ k) := by rw [← dist_eq_norm]; linarith [mem_ball.1 hw]
      have hVw : V z / 2 < V w := hδV (hsub (ball_subset_closedBall hw))
      have hdw := hk w (ball_subset_closedBall hw)
      rw [Real.dist_eq, abs_lt] at hdw
      exact hharmv _ w hwρ (by linarith)
    obtain ⟨hVh, hdz⟩ := harmonic_limit_eventually isOpen_ball hev (hconvU _)
    refine ⟨hVh z (mem_ball_self hs0), ?_⟩
    have hn := (continuous_norm.tendsto _).comp (hdz z (mem_ball_self hs0))
    -- the scales `r_k (1 + |z|) → 0+`
    have hsk : Tendsto (fun k ↦ r (φ k) * (1 + ‖z‖)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ ?_⟩
      · have := (hrt.comp hφt).mul_const (1 + ‖z‖)
        simpa using this
      · exact mul_pos (hr0 _) (by positivity)
    refine le_of_tendsto_of_tendsto hn (hlim.comp hsk) ?_
    filter_upwards [hbig ‖z‖, (hpt z).eventually (lt_mem_nhds hz)] with k hkρ hkpos
    have hzρ : z ∈ ball (0 : E n) (ρ (φ k)) := mem_ball_zero_iff.2 hkρ
    simp only [Function.comp_apply]
    rw [hgradv _ z hzρ hkpos]
    exact le_gradSup (hu (φ k)) (mem_ball_zero_iff.2 (hnormA _ z)) (hmap _ z hzρ)
      (hApos _ z hkpos)
  exact false_of_isViscSuper_of_norm_gradient_attained hVc hV0 hsuperV
    (fun z hz ↦ (hlocal z hz).1) hcon
    (fun z hz ↦ by rw [norm_gradient_eq_norm_fderiv]; exact (hlocal z hz).2) hVpos0
    (by rw [norm_gradient_eq_norm_fderiv]; exact hgrad0)

/-! ### Steps 2–3: the modulus and the Lipschitz bound -/

/-- **The Alt–Caffarelli gradient bound** (`ClassicalLipschitzBoundStatement`; Alt–Caffarelli,
Theorem 6.3, as cited in Kriventsov–Weiss, Proposition 9.1; proved here by the blow-up argument of
Alt–Caffarelli, Remark 6.4, made uniform over the class). The modulus depends on `n` and `L`. -/
theorem classical_lipschitz_bound : ClassicalLipschitzBoundStatement := by
  intro n L
  set ℓ := gradSup (n := n) L with hℓ
  set g : ℝ → ℝ := fun s ↦ max (ℓ s - 1) 0 with hg
  have hgm : Monotone g := fun a b hab ↦
    max_le_max (sub_le_sub_right (gradSup_mono L hab) 1) le_rfl
  have hg0 : g 0 = 0 := by simp [hg, hℓ, gradSup_zero]
  have hglim : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h := (((gradSup_mono (n := n) L).tendsto_nhdsGT 0).sub_const 1).max
      (tendsto_const_nhds (x := (0 : ℝ)))
    rwa [max_eq_right (by linarith [gradLim_le_one (n := n) L])] at h
  obtain ⟨hwc, hwm, -, hwt, hwg⟩ := exists_continuous_monotone_majorant hgm hg0 hglim
  refine ⟨avgModulus g, hwc.mono Ico_subset_Ici_self, hwm.mono Ico_subset_Ici_self, hwt, ?_⟩
  intro u hu hL hu0 r hr
  have hgr := hwg r hr.1.le
  have hgnn : 0 ≤ g r := le_max_right _ _
  have hK : 0 ≤ 1 + avgModulus g r := by linarith
  have hsub : ball (0 : E n) r ⊆ ball 0 1 := ball_subset_ball hr.2.le
  have hbound : ∀ p ∈ ball (0 : E n) r, 0 < u p → ‖∇ u p‖ ≤ 1 + avgModulus g r :=
    fun p hp hpos ↦
      calc ‖∇ u p‖ ≤ ℓ r := le_gradSup ⟨hu, hL, hu0⟩ hp (hsub hp) hpos
        _ ≤ 1 + g r := by have := le_max_left (ℓ r - 1) 0; simp only [hg]; linarith
        _ ≤ 1 + avgModulus g r := by linarith
  have key : ∀ a ∈ ball (0 : E n) r, ∀ b ∈ ball (0 : E n) r,
      u a - u b ≤ (1 + avgModulus g r) * dist a b := fun a ha b hb ↦
    sub_le_mul_dist_of_norm_gradient_le (convex_ball 0 r) hK (hL.continuousOn.mono hsub)
      (fun p hp ↦ hu.nonneg p (hsub hp))
      (fun p hp hpos ↦ (hu.harmonicAt p (hsub hp) hpos).1.differentiableAt (by norm_num))
      hbound ha hb
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [Real.coe_toNNReal _ hK, Real.dist_eq, abs_sub_le_iff]
  exact ⟨key a ha b hb, by rw [dist_comm]; exact key b hb a ha⟩

end EllipticBernoulli
