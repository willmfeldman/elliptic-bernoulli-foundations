/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Variational
import EllipticBernoulli.Sobolev.Closure
import EllipticBernoulli.Sobolev.Compactness
import EllipticBernoulli.Sobolev.Energy
import EllipticBernoulli.Sobolev.SobolevInequality
import EllipticBernoulli.Sobolev.Uniqueness

/-!
# Existence for the obstacle problem (direct method)

* `exists_isObstacleMinimizer : ObstacleExistenceStatement`: for bounded measurable `Q`,
  `u ∈ H¹_loc(U)`, a ball `B = ball x₀ r` with `closedBall x₀ r ⊆ U` and closed constraint sets
  `K y ∋ u y`, there is an obstacle minimizer `w` of `J_Q(·; B)` (`IsObstacleMinimizer`) whose
  representative equals `u` pointwise on `U \ B` and satisfies `w y ∈ K y` pointwise on `U`.
* `IsObstacleMinimizer.congr_Q`, `exists_isObstacleMinimizer_of_aemeasurable`: only `Q` a.e. on
  `B` matters, so a.e.-measurability of `Q` on `U` suffices.
* Specializations: `exists_obstacle_below` (`K y = Icc 0 (u y)`) and `exists_obstacle_above`
  (`K y = Ici (u y)`), the obstacle problems (6.1) and (6.3) in the proof of
  Abedin–Feldman–Stinson, Lemma 6.3, without continuity; and `exists_localMinimizer_ball`
  (`K y = univ`).

## Proof

Direct method (Evans, *PDE*, §8.2; Alt–Caffarelli, §1; Velichkov, Ch. 2):
1. a minimizing sequence `(v k, G k)` with `J_Q(v k; B) → m := inf J_Q(·; B) ≤ J_Q(u; B) < ∞`;
2. uniform `L²(K)` bounds on compact `K ⊆ U`: `G k = Gu` a.e. off `B` (uniqueness of weak
   gradients on the open set `U \ closedBall x₀ r`, the sphere being null) and the Poincaré
   inequality `integral_sq_le_of_ae_eq_zero_off_ball` for `v k - u` (this needs `1 ≤ d`);
3. a subsequence with `G k ⇀ G₀` weakly in `L²_loc`, `v k → w₀` in `L²_loc` (local Rellich) and
   a.e. on `closedBall x₀ r`; since each `K y` is closed, `w₀ y ∈ K y` a.e. on the ball;
4. the good representative `w := w₀` on `{y ∈ B | w₀ y ∈ K y}`, `w := u` elsewhere, equal to `w₀`
   a.e. on `B`; still `v k → w` in `L²_loc(U)`, so `G₀` is a weak gradient of `w`
   (`HasWeakGradient.of_tendsto`), and `J_Q(w; B) ≤ liminf J_Q(v k; B) = m` (`energyJ_le_liminf`).

For `d = 0` the space `E 0` is a point: `ball x₀ r` is everything, every function has every weak
gradient, and a constant (a nonpositive element of `K x₀` if there is one, else `u x₀`) is a
minimizer.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace EllipticBernoulli

variable {d : ℕ}

section Helpers

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]

/-- `‖f‖_{L²} ≤ M^{1/2}` from `∫⁻ |f|² ≤ M`. -/
private theorem eLpNorm_two_le_of_lintegral_le {μ : Measure X} {f : X → F} {M : ℝ≥0∞}
    (h : ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ∂μ ≤ M) : eLpNorm f 2 μ ≤ M ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  refine ENNReal.rpow_le_rpow (le_trans (le_of_eq ?_) h) (by norm_num)
  refine lintegral_congr fun x ↦ ?_
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _), ENNReal.rpow_two]

/-- `‖f‖_{L²} ≤ A^{1/2}` from `∫ f² ≤ A`, for `f ∈ L²`. -/
private theorem eLpNorm_two_le_of_integral_le {μ : Measure X} {f : X → ℝ} (hf : MemLp f 2 μ)
    {A : ℝ} (h : ∫ x, f x ^ 2 ∂μ ≤ A) : eLpNorm f 2 μ ≤ ENNReal.ofReal (A ^ (1 / 2 : ℝ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [one_div]
  exact Real.rpow_le_rpow (integral_nonneg fun x ↦ sq_nonneg _) h (by norm_num)

/-- A subsequence of a weakly convergent sequence converges weakly. -/
private theorem TendstoWeakL2.comp_strictMono {μ : Measure X} [InnerProductSpace ℝ F]
    {Ω : Set X} {f : ℕ → X → F} {f₀ : X → F} (h : TendstoWeakL2 μ Ω f f₀ atTop) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : TendstoWeakL2 μ Ω (fun n ↦ f (φ n)) f₀ atTop :=
  ⟨fun _ ↦ h.1 _, h.2.1, fun g hg ↦ (h.2.2 g hg).comp hφ.tendsto_atTop⟩

end Helpers

/-- A.e. on `U \ ball x₀ r` equals a.e. on the open set `U \ closedBall x₀ r`. -/
private theorem restrict_diff_ball_eq {U : Set (E d)} {x₀ : E d} {r : ℝ} (hr : 0 < r) :
    volume.restrict (U \ ball x₀ r) = volume.restrict (U \ closedBall x₀ r) :=
  Measure.restrict_congr_set ((ae_eq_refl U).diff (ball_ae_eq_closedBall x₀ hr))

/-- **Uniform local `L²` bounds for admissible sequences.** If `v k = u` a.e. off the ball
`B = ball x₀ r` and the Dirichlet energies `∫_B |G k|²` are bounded, then `v k` and `G k` are
bounded in `L²(K)` for every compact `K ⊆ U` (Poincaré inequality for `v k - u`, `1 ≤ d`). -/
private theorem bdd_of_admissible (hd : 1 ≤ d) {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    {Gu : E d → E d} (hu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r)
    (hBU : closedBall x₀ r ⊆ U) {v : ℕ → E d → ℝ} {G : ℕ → E d → E d}
    (hv : ∀ k, MemH1Loc U (v k) (G k))
    (hvu : ∀ k, ∀ᵐ y ∂(volume.restrict (U \ ball x₀ r)), v k y = u y) {M : ℝ≥0∞}
    (hM : M ≠ ⊤) (hGM : ∀ k, ∫⁻ x in ball x₀ r, ENNReal.ofReal (‖G k x‖ ^ 2) ≤ M) :
    ∀ K ⊆ U, IsCompact K → ∃ C : ℝ, ∀ n, eLpNorm (v n) 2 (volume.restrict K) ≤ ENNReal.ofReal C ∧
      eLpNorm (G n) 2 (volume.restrict K) ≤ ENNReal.ofReal C := by
  set B := ball x₀ r with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hBcb : volume.restrict B ≤ volume.restrict (closedBall x₀ r) :=
    Measure.restrict_mono ball_subset_closedBall le_rfl
  have hcb := hu.2 _ hBU (isCompact_closedBall x₀ r)
  have hvcb : ∀ k, MemLp (v k) 2 (volume.restrict (closedBall x₀ r)) ∧
      MemLp (G k) 2 (volume.restrict (closedBall x₀ r)) :=
    fun k ↦ (hv k).2 _ hBU (isCompact_closedBall x₀ r)
  -- the gradients agree with `Gu` a.e. off `B`
  have hGu : ∀ k, ∀ᵐ y ∂(volume.restrict (U \ B)), G k y = Gu y := by
    intro k
    rw [restrict_diff_ball_eq hr]
    refine (hv k).1.ae_eq_of_ae_eq_on (hU.sdiff isClosed_closedBall) diff_subset hu.1 ?_
    rw [← restrict_diff_ball_eq hr]
    exact hvu k
  -- `L²(B)` bounds on the gradients
  set A : ℝ≥0∞ := M ^ (1 / 2 : ℝ) with hAdef
  have hAtop : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hM
  have hGB : ∀ k, eLpNorm (G k) 2 (volume.restrict B) ≤ A :=
    fun k ↦ eLpNorm_two_le_of_lintegral_le (hGM k)
  have hGuB : MemLp Gu 2 (volume.restrict B) := hcb.2.mono_measure hBcb
  set A' : ℝ := (A + eLpNorm Gu 2 (volume.restrict B)).toReal with hA'def
  have hGdiff : ∀ k, eLpNorm (G k - Gu) 2 (volume.restrict B) ≤ ENNReal.ofReal A' := by
    intro k
    rw [hA'def, ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨hAtop, hGuB.2.ne⟩)]
    refine (eLpNorm_sub_le ((hvcb k).2.mono_measure hBcb).1 hGuB.1 (by norm_num)).trans ?_
    gcongr
    exact hGB k
  -- Poincaré for `v k - u`
  obtain ⟨CP, hCP, hP⟩ := integral_sq_le_of_ae_eq_zero_off_ball hd
  set A'' : ℝ := CP * r ^ 2 * max A' 0 ^ 2 with hA''def
  have hvB : ∀ k, eLpNorm (v k - u) 2 (volume.restrict B) ≤ ENNReal.ofReal (A'' ^ (1 / 2 : ℝ)) := by
    intro k
    have hmem : MemLp (v k - u) 2 (volume.restrict B) :=
      ((hvcb k).1.sub hcb.1).mono_measure hBcb
    refine eLpNorm_two_le_of_integral_le hmem ?_
    have h0 : ∀ᵐ y ∂(volume.restrict (U \ B)), (v k - u) y = 0 := by
      filter_upwards [hvu k] with y hy
      simp [hy]
    refine (hP U (v k - u) (G k - Gu) x₀ r hU ((hv k).sub hu) hr hBU h0).trans ?_
    rw [hA''def]
    have hGm : MemLp (G k - Gu) 2 (volume.restrict B) :=
      ((hvcb k).2.mono_measure hBcb).sub hGuB
    have := integral_norm_sq_le_of_eLpNorm_le hGm (hGdiff k)
    gcongr
  intro K hKU hK
  -- pointwise decompositions on `K`
  have hdecv : ∀ k, v k =ᵐ[volume.restrict K] B.indicator (v k - u) + u := by
    intro k
    have h1 : ∀ᵐ y ∂volume, y ∈ U \ B → v k y = u y :=
      (ae_restrict_iff' (hU.measurableSet.diff hBm)).1 (hvu k)
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem hK.measurableSet] with y hy hyK
    by_cases hyB : y ∈ B
    · simp [indicator_of_mem hyB]
    · simp [indicator_of_notMem hyB, hy ⟨hKU hyK, hyB⟩]
  have hdecG : ∀ k, G k =ᵐ[volume.restrict K] B.indicator (G k) + Bᶜ.indicator Gu := by
    intro k
    have h1 : ∀ᵐ y ∂volume, y ∈ U \ B → G k y = Gu y :=
      (ae_restrict_iff' (hU.measurableSet.diff hBm)).1 (hGu k)
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem hK.measurableSet] with y hy hyK
    by_cases hyB : y ∈ B
    · simp [hyB]
    · simp [hyB, hy ⟨hKU hyK, hyB⟩]
  have huK := hu.2 K hKU hK
  set Cv : ℝ≥0∞ := ENNReal.ofReal (A'' ^ (1 / 2 : ℝ)) + eLpNorm u 2 (volume.restrict K)
  set CG : ℝ≥0∞ := A + eLpNorm Gu 2 (volume.restrict K)
  have hCv : Cv ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, huK.1.2.ne⟩
  have hCG : CG ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hAtop, huK.2.2.ne⟩
  refine ⟨max Cv.toReal CG.toReal, fun n ↦ ⟨?_, ?_⟩⟩
  · rw [eLpNorm_congr_ae (hdecv n)]
    have hvK := (hv n).2 K hKU hK
    refine (eLpNorm_add_le ((hvK.1.sub huK.1).1.indicator hBm) huK.1.1 (by norm_num)).trans ?_
    refine le_trans ?_ ((ENNReal.ofReal_toReal hCv).symm.le.trans
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    refine add_le_add ?_ le_rfl
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hBm]
    exact hvB n
  · rw [eLpNorm_congr_ae (hdecG n)]
    have hvK := (hv n).2 K hKU hK
    refine (eLpNorm_add_le (hvK.2.1.indicator hBm) (huK.2.1.indicator hBm.compl)
      (by norm_num)).trans ?_
    refine le_trans ?_ ((ENNReal.ofReal_toReal hCG).symm.le.trans
      (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
    refine add_le_add ?_ ?_
    · refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
      rw [eLpNorm_indicator_eq_eLpNorm_restrict hBm]
      exact hGB n
    · exact eLpNorm_indicator_le _

/-- **The direct method** (`1 ≤ d`). -/
private theorem exists_isObstacleMinimizer_of_one_le (hd : 1 ≤ d) {U : Set (E d)}
    {Q u : E d → ℝ} {Gu : E d → E d} {K : E d → Set ℝ} {x₀ : E d} {r : ℝ} (hU : IsOpen U)
    (hQb : ∃ C, ∀ x ∈ U, |Q x| ≤ C) (hQm : Measurable Q) (hu : MemH1Loc U u Gu) (hr : 0 < r)
    (hBU : closedBall x₀ r ⊆ U) (hK : ∀ y, IsClosed (K y)) (huK : ∀ y ∈ U, u y ∈ K y) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), IsObstacleMinimizer U (ball x₀ r) Q u K w Gw := by
  classical
  set B := ball x₀ r with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hcbc : IsCompact (closedBall x₀ r) := isCompact_closedBall x₀ r
  -- the admissible class and the infimum `m` of the energy over it
  let Adm : (E d → ℝ) × (E d → E d) → Prop := fun p ↦ MemH1Loc U p.1 p.2 ∧
    (∀ᵐ y ∂(volume.restrict (U \ B)), p.1 y = u y) ∧ (∀ᵐ y ∂(volume.restrict U), p.1 y ∈ K y)
  set m : ℝ≥0∞ := ⨅ p : {p // Adm p}, energyJ B Q p.1.1 p.1.2 with hmdef
  have hm_le : ∀ v Gv, Adm (v, Gv) → m ≤ energyJ B Q v Gv :=
    fun v Gv h ↦ iInf_le_of_le ⟨(v, Gv), h⟩ le_rfl
  have huAdm : Adm (u, Gu) :=
    ⟨hu, ae_of_all _ fun _ ↦ rfl, (ae_restrict_iff' hU.measurableSet).2 (ae_of_all _ huK)⟩
  obtain ⟨CQ, hCQ⟩ := hQb
  have hBc : closure B = closedBall x₀ r := closure_ball x₀ hr.ne'
  have hJu : energyJ B Q u Gu < ⊤ :=
    energyJ_lt_top hu (hBc ▸ hcbc) (hBc ▸ hBU)
      (fun x hx ↦ hCQ x (hBU (ball_subset_closedBall hx)))
  have hmtop : m ≠ ⊤ := ((hm_le u Gu huAdm).trans_lt hJu).ne
  -- a minimizing sequence
  have hseq : ∀ k : ℕ, ∃ p : {p // Adm p},
      energyJ B Q p.1.1 p.1.2 < m + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
    fun k ↦ iInf_lt_iff.1 (ENNReal.lt_add_right hmtop (ENNReal.inv_ne_zero.2
      (ENNReal.natCast_ne_top _)))
  choose p hp using hseq
  set v : ℕ → E d → ℝ := fun k ↦ (p k).1.1 with hvdef
  set G : ℕ → E d → E d := fun k ↦ (p k).1.2 with hGdef
  have hvAdm : ∀ k, Adm (v k, G k) := fun k ↦ (p k).2
  have hJtend : Tendsto (fun k ↦ energyJ B Q (v k) (G k)) atTop (𝓝 m) := by
    have h2 : Tendsto (fun k : ℕ ↦ m + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 m) := by
      simpa using tendsto_const_nhds.add
        (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
      (fun k ↦ hm_le _ _ (hvAdm k)) (fun k ↦ (hp k).le)
  -- bounds
  set M : ℝ≥0∞ := energyJ B Q u Gu + 1 with hMdef
  have hMtop : M ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hJu.ne, ENNReal.one_ne_top⟩
  have hGM : ∀ k, ∫⁻ x in B, ENNReal.ofReal (‖G k x‖ ^ 2) ≤ M := by
    intro k
    calc ∫⁻ x in B, ENNReal.ofReal (‖G k x‖ ^ 2) ≤ energyJ B Q (v k) (G k) := by
          refine lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal ?_
          have : 0 ≤ Q x ^ 2 * (posSet (v k) B).indicator 1 x :=
            mul_nonneg (sq_nonneg _) (indicator_nonneg (fun _ _ ↦ zero_le_one) _)
          linarith
      _ ≤ m + ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := (hp k).le
      _ ≤ M := add_le_add (hm_le u Gu huAdm)
          (ENNReal.inv_le_one.2 (Nat.one_le_cast.2 (Nat.succ_pos k)))
  have hbdd := bdd_of_admissible hd hU hu hr hBU (fun k ↦ (hvAdm k).1) (fun k ↦ (hvAdm k).2.1)
    hMtop hGM
  -- compactness: weak limit of the gradients, strong `L²_loc` and a.e. limit of the functions
  obtain ⟨φ₁, hφ₁, G₀, hG₀⟩ := exists_tendstoWeakL2Loc_subseq hU G
    (fun n K' hK'U hK' ↦ ((hvAdm n).1.2 K' hK'U hK').2)
    (fun K' hK'U hK' ↦ let ⟨C, hC⟩ := hbdd K' hK'U hK'; ⟨C, fun n ↦ (hC n).2⟩)
  obtain ⟨φ₂, hφ₂, w₀, hw₀m, hw₀⟩ := exists_tendstoLpLoc_subseq_of_H1Loc hU
    (fun n ↦ v (φ₁ n)) (fun n ↦ G (φ₁ n)) (fun n ↦ (hvAdm _).1)
    (fun K' hK'U hK' ↦ let ⟨C, hC⟩ := hbdd K' hK'U hK'; ⟨C, fun n ↦ hC (φ₁ n)⟩)
  obtain ⟨φ₃, hφ₃, hae⟩ := hw₀.exists_subseq_ae_tendsto hBU hcbc
    (fun k ↦ ((hvAdm _).1.2 _ hBU hcbc).1.1) hw₀m.aestronglyMeasurable
  set ψ : ℕ → ℕ := fun n ↦ φ₁ (φ₂ (φ₃ n)) with hψdef
  have hψ : StrictMono ψ := hφ₁.comp (hφ₂.comp hφ₃)
  have hGψ : ∀ K' ⊆ U, IsCompact K' → TendstoWeakL2 volume K' (fun n ↦ G (ψ n)) G₀ atTop :=
    fun K' hK'U hK' ↦ (hG₀ K' hK'U hK').comp_strictMono (hφ₂.comp hφ₃)
  -- the limit satisfies the constraint a.e. on the closed ball
  have hw₀K : ∀ᵐ y ∂(volume.restrict (closedBall x₀ r)), w₀ y ∈ K y := by
    have hvK : ∀ᵐ y ∂(volume.restrict (closedBall x₀ r)), ∀ k, v k y ∈ K y :=
      ae_all_iff.2 fun k ↦ ae_restrict_of_ae_restrict_of_subset hBU (hvAdm k).2.2
    filter_upwards [hae, hvK] with y hy hyK
    exact (hK y).mem_of_tendsto hy (Eventually.of_forall fun i ↦ hyK _)
  have hw₀K' : ∀ᵐ y ∂volume, y ∈ B → w₀ y ∈ K y :=
    (ae_restrict_iff' hBm).1 (ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hw₀K)
  -- the good representative
  set w : E d → ℝ := fun y ↦ if y ∈ B ∧ w₀ y ∈ K y then w₀ y else u y with hwdef
  have hwB : ∀ᵐ y ∂volume, y ∈ B → w y = w₀ y := by
    filter_upwards [hw₀K'] with y hy hyB
    simp [hwdef, hyB, hy hyB]
  have hwoff : ∀ y ∈ U \ B, w y = u y := fun y hy ↦ by simp [hwdef, hy.2]
  have hwK : ∀ y ∈ U, w y ∈ K y := by
    intro y hy
    by_cases h : y ∈ B ∧ w₀ y ∈ K y
    · simp only [hwdef, if_pos h]; exact h.2
    · simp only [hwdef, if_neg h]; exact huK y hy
  have hwm : AEStronglyMeasurable w (volume.restrict U) := by
    have hpw : AEStronglyMeasurable (B.piecewise w₀ u) (volume.restrict U) :=
      AEStronglyMeasurable.piecewise hBm hw₀m.aestronglyMeasurable.restrict
        hu.1.1.aestronglyMeasurable.restrict
    refine hpw.congr ?_
    filter_upwards [ae_restrict_of_ae hwB] with y hy
    by_cases hyB : y ∈ B
    · rw [piecewise_eq_of_mem _ _ _ hyB, hy hyB]
    · rw [piecewise_eq_of_notMem _ _ _ hyB]; simp [hwdef, hyB]
  -- strong `L²_loc` convergence to `w`
  have hvw : TendstoLpLoc 2 volume U (fun n ↦ v (ψ n)) w atTop := by
    intro K' hK'U hK'
    have h0 := (hw₀ K' hK'U hK').comp hφ₃.tendsto_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0 (fun _ ↦ zero_le)
      fun n ↦ eLpNorm_mono_ae ?_
    have h1 : ∀ᵐ y ∂volume, y ∈ U \ B → v (ψ n) y = u y :=
      (ae_restrict_iff' (hU.measurableSet.diff hBm)).1 (hvAdm _).2.1
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_of_ae hwB,
      ae_restrict_mem hK'.measurableSet] with y hy1 hy2 hyK
    by_cases hyB : y ∈ B
    · simp [hψdef, hy2 hyB]
    · simp [hy1 ⟨hK'U hyK, hyB⟩, hwoff y ⟨hK'U hyK, hyB⟩]
  -- closure: `G₀` is a weak gradient of `w`, and `w ∈ H¹_loc(U)`
  have hwg : HasWeakGradient U w G₀ :=
    HasWeakGradient.of_tendsto hU (fun k ↦ (hvAdm (ψ k)).1.1) hwm hvw hGψ
  have hwH : MemH1Loc U w G₀ := by
    refine ⟨hwg, fun K' hK'U hK' ↦ ⟨?_, (hGψ K' hK'U hK').2.1⟩⟩
    obtain ⟨n, hn⟩ := ((hvw K' hK'U hK').eventually (gt_mem_nhds ENNReal.zero_lt_top)).exists
    have hvn := ((hvAdm (ψ n)).1.2 K' hK'U hK').1
    have hdiff : MemLp (v (ψ n) - w) 2 (volume.restrict K') :=
      ⟨hvn.1.sub (hwm.mono_measure (Measure.restrict_mono hK'U le_rfl)), hn⟩
    simpa using hvn.sub hdiff
  -- lower semicontinuity
  have hlsc : energyJ B Q w G₀ ≤ m := by
    have h := energyJ_le_liminf hBm hQm.aemeasurable (v := fun k ↦ v (ψ k)) (v₀ := w)
      (fun k ↦ ((hvAdm _).1.2 _ hBU hcbc).1.1.aemeasurable.mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)) ?_
      ((hGψ _ hBU hcbc).mono_set hBm ball_subset_closedBall)
    · have h2 : Tendsto (fun k ↦ energyJ B Q (v (ψ k)) (G (ψ k))) atTop (𝓝 m) :=
        hJtend.comp hψ.tendsto_atTop
      rwa [h2.liminf_eq] at h
    · filter_upwards [ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall hae,
        ae_restrict_of_ae hwB, ae_restrict_mem hBm] with y hy1 hy2 hyB
      rw [hy2 hyB]
      exact hy1
  exact ⟨w, G₀, hwH, hwoff, hwK, fun v' Gv' hv' hbd hKv' ↦
    hlsc.trans (hm_le v' Gv' ⟨hv', hbd, hKv'⟩)⟩

/-- **The zero-dimensional case.** `E 0` is a point, so `ball x₀ r` is everything and every
function has every weak gradient; a constant minimizes the positivity term. -/
private theorem exists_isObstacleMinimizer_dim_zero {U : Set (E 0)} {Q u : E 0 → ℝ}
    {K : E 0 → Set ℝ} {x₀ : E 0} {r : ℝ} (hr : 0 < r) (hBU : closedBall x₀ r ⊆ U)
    (huK : ∀ y ∈ U, u y ∈ K y) :
    ∃ (w : E 0 → ℝ) (Gw : E 0 → E 0), IsObstacleMinimizer U (ball x₀ r) Q u K w Gw := by
  classical
  have hsub : ∀ y : E 0, y = x₀ := fun y ↦ Subsingleton.elim _ _
  have hyB : ∀ y : E 0, y ∈ ball x₀ r := fun y ↦ by rw [hsub y]; exact mem_ball_self hr
  have hx₀U : x₀ ∈ U := hBU (mem_closedBall_self hr.le)
  by_cases hc : ∃ c ∈ K x₀, c ≤ 0
  · obtain ⟨c, hcK, hc0⟩ := hc
    refine ⟨fun _ ↦ c, fun _ ↦ 0, memH1Loc_const c, fun y hy ↦ absurd (hyB y) hy.2,
      fun y _ ↦ by rw [hsub y]; exact hcK, fun v Gv _ _ _ ↦ ?_⟩
    have h0 : energyJ (ball x₀ r) Q (fun _ ↦ c) (fun _ ↦ 0) = 0 := by
      have hpos : posSet (fun _ ↦ c) (ball x₀ r) = ∅ := by
        ext y; simp [posSet, not_lt.2 hc0]
      simp [energyJ, hpos]
    rw [h0]
    exact zero_le
  · push Not at hc
    refine ⟨fun _ ↦ u x₀, fun _ ↦ 0, memH1Loc_const _, fun y hy ↦ absurd (hyB y) hy.2,
      fun y _ ↦ by rw [hsub y]; exact huK x₀ hx₀U, fun v Gv _ _ hKv ↦ ?_⟩
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (ball_subset_closedBall.trans hBU) hKv]
      with y hy
    have hvy : 0 < v y := by
      have h := hsub y
      subst h
      exact hc _ hy
    refine ENNReal.ofReal_le_ofReal ?_
    rw [indicator_of_mem (show y ∈ posSet v (ball x₀ r) from ⟨hyB y, hvy⟩)]
    have hind : (posSet (fun _ ↦ u x₀) (ball x₀ r)).indicator (1 : E 0 → ℝ) y ≤ 1 := by
      unfold Set.indicator; split_ifs <;> simp
    simp only [norm_zero, Pi.one_apply, mul_one]
    nlinarith [sq_nonneg (Q y), sq_nonneg ‖Gv y‖]

public section

/-- **Existence for the obstacle problem** (`ObstacleExistenceStatement`; Evans §8.2, Alt–Caffarelli
1981 §1). Direct method: a minimizing sequence is bounded in `H¹_loc(U)` (Poincaré inequality for
`v - u`, which vanishes off the ball), has a subsequence converging strongly in `L²_loc` and a.e.
(local Rellich), with gradients converging weakly in `L²_loc`; the limit is admissible (closedness
of the weak-gradient relation, closedness of each `K y`) and minimal (lower semicontinuity of
`energyJ`). The good representative is obtained by redefining the limit on a null set. For `d = 0`
the space is a point and a constant minimizer is written down directly. -/
theorem exists_isObstacleMinimizer : ObstacleExistenceStatement := by
  intro d U Q u Gu K x₀ r hU hQb hQm hu hr hBU hK huK
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact exists_isObstacleMinimizer_dim_zero hr hBU huK
  · exact exists_isObstacleMinimizer_of_one_le hd hU hQb hQm hu hr hBU hK huK

/-- `IsObstacleMinimizer U B Q …` only depends on `Q` a.e. on `B`. -/
theorem IsObstacleMinimizer.congr_Q {U B : Set (E d)} {Q Q' u w : E d → ℝ} {K : E d → Set ℝ}
    {Gw : E d → E d} (hQ : ∀ᵐ x ∂(volume.restrict B), Q x = Q' x)
    (h : IsObstacleMinimizer U B Q u K w Gw) : IsObstacleMinimizer U B Q' u K w Gw := by
  have hJ : ∀ (v : E d → ℝ) (G : E d → E d), energyJ B Q v G = energyJ B Q' v G := by
    intro v G
    refine lintegral_congr_ae ?_
    filter_upwards [hQ] with x hx
    rw [hx]
  refine ⟨h.1, h.2.1, h.2.2.1, fun v Gv hv hbd hKv ↦ ?_⟩
  rw [← hJ, ← hJ]
  exact h.2.2.2 v Gv hv hbd hKv

/-- `exists_isObstacleMinimizer` with `Q` only a.e.-measurable on `U` (e.g. `ContinuousOn Q U`,
via `ContinuousOn.aemeasurable`). -/
theorem exists_isObstacleMinimizer_of_aemeasurable {U : Set (E d)} {Q u : E d → ℝ}
    {Gu : E d → E d} {K : E d → Set ℝ} {x₀ : E d} {r : ℝ} (hU : IsOpen U)
    (hQb : ∃ C, ∀ x ∈ U, |Q x| ≤ C) (hQm : AEMeasurable Q (volume.restrict U))
    (hu : MemH1Loc U u Gu) (hr : 0 < r) (hBU : closedBall x₀ r ⊆ U) (hK : ∀ y, IsClosed (K y))
    (huK : ∀ y ∈ U, u y ∈ K y) :
    ∃ (w : E d → ℝ) (Gw : E d → E d), IsObstacleMinimizer U (ball x₀ r) Q u K w Gw := by
  obtain ⟨C, hC⟩ := hQb
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x₀ (hBU (mem_closedBall_self hr.le)))
  set Q' : E d → ℝ := fun x ↦ max (-C) (min (hQm.mk Q x) C) with hQ'def
  have hQ'm : Measurable Q' :=
    measurable_const.max (hQm.measurable_mk.min measurable_const)
  have hQ'b : ∀ x ∈ U, |Q' x| ≤ C := fun x _ ↦
    abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have hQQ' : ∀ᵐ x ∂(volume.restrict U), Q' x = Q x := by
    filter_upwards [hQm.ae_eq_mk.symm, ae_restrict_mem hU.measurableSet] with x hx hxU
    have := abs_le.1 (hC x hxU)
    simp only [hQ'def, hx]
    rw [min_eq_left this.2, max_eq_right this.1]
  obtain ⟨w, Gw, h⟩ := exists_isObstacleMinimizer hU ⟨C, hQ'b⟩ hQ'm hu hr hBU hK huK
  exact ⟨w, Gw, h.congr_Q (ae_restrict_of_ae_restrict_of_subset
    (ball_subset_closedBall.trans hBU) hQQ')⟩

/-- **Specialization (a):** the two-sided obstacle `0 ≤ w ≤ u` (without continuity). -/
theorem exists_obstacle_below {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d} (hU : IsOpen U)
    (hQc : ContinuousOn Q U) (hQb : ∃ C, ∀ x ∈ U, |Q x| ≤ C) (hu0 : ∀ x ∈ U, 0 ≤ u x)
    (hGu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d),
      IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Icc 0 (u y)) w Gw :=
  exists_isObstacleMinimizer_of_aemeasurable hU hQb (hQc.aemeasurable hU.measurableSet) hGu hr
    hB (fun _ ↦ isClosed_Icc) fun y hy ↦ ⟨hu0 y hy, le_rfl⟩

/-- **Specialization (b):** the one-sided obstacle `u ≤ w` (without continuity). -/
theorem exists_obstacle_above {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d} (hU : IsOpen U)
    (hQc : ContinuousOn Q U) (hQb : ∃ C, ∀ x ∈ U, |Q x| ≤ C) (hGu : MemH1Loc U u Gu) {x₀ : E d}
    {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d),
      IsObstacleMinimizer U (ball x₀ r) Q u (fun y ↦ Ici (u y)) w Gw :=
  exists_isObstacleMinimizer_of_aemeasurable hU hQb (hQc.aemeasurable hU.measurableSet) hGu hr
    hB (fun _ ↦ isClosed_Ici) fun _ _ ↦ self_mem_Ici

/-- **Specialization (c):** the unconstrained problem on a ball (a local energy minimizer on
`ball x₀ r` with boundary values `u`). -/
theorem exists_localMinimizer_ball {U : Set (E d)} {Q u : E d → ℝ} {Gu : E d → E d}
    (hU : IsOpen U) (hQc : ContinuousOn Q U) (hQb : ∃ C, ∀ x ∈ U, |Q x| ≤ C)
    (hGu : MemH1Loc U u Gu) {x₀ : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x₀ r ⊆ U) :
    ∃ (w : E d → ℝ) (Gw : E d → E d),
      IsObstacleMinimizer U (ball x₀ r) Q u (fun _ ↦ univ) w Gw :=
  exists_isObstacleMinimizer_of_aemeasurable hU hQb (hQc.aemeasurable hU.measurableSet) hGu hr
    hB (fun _ ↦ isClosed_univ) fun _ _ ↦ mem_univ _

end

end EllipticBernoulli
