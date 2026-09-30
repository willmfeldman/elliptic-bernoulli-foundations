/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Setting
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Arzelà–Ascoli extraction of Lipschitz blow-ups

## Main results

* `exists_subseq_tendstoLocallyUniformly_of_lipschitzWith`: a sequence of `L`-Lipschitz functions
  on `E d`, bounded at `0`, has a locally uniformly convergent subsequence.
* `exists_blowup_subseq`: the same for functions that are `L`-Lipschitz on balls `B_{ρ_k}` with
  `ρ_k → ∞`; the limit is `L`-Lipschitz on `E d`.

## Proof

Arzelà–Ascoli (`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`) in the space of functions with
the topology of uniform convergence on compacts, which is first countable because `E d` is
exhausted by the closed balls `B̄_m`. For `exists_blowup_subseq`, extend each `f_k` from `B_{ρ_k}`
to an `L`-Lipschitz function on `E d` (McShane, `LipschitzOnWith.extend_real`); every compact set
lies in `B_{ρ_k}` for large `k`, where the extensions agree with the `f_k`.

## References

* D. Kriventsov, G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131. Result numbers are those of arXiv:2306.10131v2.
-/

open Set Filter Topology Metric
open scoped NNReal UniformConvergence

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Arzelà–Ascoli** for uniformly Lipschitz functions on `E d` that are bounded at `0`: some
subsequence converges locally uniformly. -/
theorem exists_subseq_tendstoLocallyUniformly_of_lipschitzWith {g : ℕ → E d → ℝ} {L : ℝ≥0}
    (hg : ∀ k, LipschitzWith L (g k)) {M : ℝ} (hM : ∀ k, |g k 0| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g₀ : E d → ℝ,
      TendstoLocallyUniformly (fun k ↦ g (φ k)) g₀ atTop := by
  obtain ⟨𝔖, h𝔖⟩ : ∃ 𝔖 : Set (Set (E d)), 𝔖 = {K | IsCompact K} := ⟨_, rfl⟩
  have hmem : ∀ K, K ∈ 𝔖 ↔ IsCompact K := fun K ↦ by rw [h𝔖]; rfl
  have : IsCountablyGenerated (uniformity (E d →ᵤ[𝔖] ℝ)) :=
    UniformOnFun.isCountablyGenerated_uniformity 𝔖
      (t := fun m : ℕ ↦ closedBall (0 : E d) m)
      (fun m ↦ (hmem _).2 (isCompact_closedBall _ _))
      (fun a b hab ↦ closedBall_subset_closedBall (by exact_mod_cast hab))
      (fun K hK ↦ by
        obtain ⟨r, hr⟩ := (IsCompact.isBounded ((hmem K).1 hK)).subset_closedBall (0 : E d)
        obtain ⟨m, hm⟩ := exists_nat_ge r
        exact ⟨m, hr.trans (closedBall_subset_closedBall hm)⟩)
  set x : ℕ → (E d →ᵤ[𝔖] ℝ) := fun k ↦ UniformOnFun.ofFun 𝔖 (g k)
  set s : Set (E d →ᵤ[𝔖] ℝ) := range x
  have hid : (UniformOnFun.ofFun 𝔖 ∘ UniformOnFun.toFun 𝔖 : (E d →ᵤ[𝔖] ℝ) → _) = id := rfl
  have hcl : IsCompact (closure s) := by
    refine ArzelaAscoli.isCompact_closure_of_isClosedEmbedding (F := UniformOnFun.toFun 𝔖)
      (fun K hK ↦ (hmem K).1 hK) (by rw [hid]; exact IsClosedEmbedding.id) (fun K _ ↦ ?_)
      (fun K _ y _ ↦ ?_)
    · have hL : ∀ c : s, LipschitzWith L
          ((UniformOnFun.toFun 𝔖 ∘ (Subtype.val : s → (E d →ᵤ[𝔖] ℝ))) c) := by
        rintro ⟨_, k, rfl⟩
        exact hg k
      exact ((LipschitzWith.uniformEquicontinuous _ L hL).equicontinuous).equicontinuousOn K
    · refine ⟨closedBall 0 (M + L * ‖y‖), isCompact_closedBall _ _, ?_⟩
      rintro _ ⟨k, rfl⟩
      rw [mem_closedBall, Real.dist_eq, sub_zero]
      have h1 := (hg k).dist_le_mul y 0
      rw [Real.dist_eq, dist_zero_right] at h1
      have h2 := abs_sub_abs_le_abs_sub (g k y) (g k 0)
      change |g k y| ≤ M + L * ‖y‖
      linarith [hM k]
  obtain ⟨a, -, φ, hφ, hlim⟩ := hcl.tendsto_subseq (x := x) fun k ↦ subset_closure ⟨k, rfl⟩
  refine ⟨φ, hφ, UniformOnFun.toFun 𝔖 a, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  exact fun K hK ↦ (UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 hlim) K ((hmem K).2 hK)

/-- **Blow-up extraction** (Arzelà–Ascoli, as in the proof of Kriventsov–Weiss,
Proposition 3.5). Let `f_k` be `L`-Lipschitz on `B_{ρ_k}`,
`ρ_k → ∞`, `ρ_k > 0`, with `f_k(0)` bounded. Then a subsequence converges locally uniformly on
`E d` to an `L`-Lipschitz function. -/
theorem exists_blowup_subseq {f : ℕ → E d → ℝ} {L : ℝ≥0} {ρ : ℕ → ℝ}
    (hρ : Tendsto ρ atTop atTop) (hρ0 : ∀ k, 0 < ρ k)
    (hLip : ∀ k, LipschitzOnWith L (f k) (ball 0 (ρ k))) {M : ℝ} (hM : ∀ k, |f k 0| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : E d → ℝ, LipschitzWith L f₀ ∧
      TendstoLocallyUniformly (fun k ↦ f (φ k)) f₀ atTop := by
  choose g hg hfg using fun k ↦ (hLip k).extend_real
  have hg0 : ∀ k, |g k 0| ≤ M := fun k ↦ by
    rw [← hfg k (mem_ball_self (hρ0 k))]; exact hM k
  obtain ⟨φ, hφ, g₀, hlim⟩ := exists_subseq_tendstoLocallyUniformly_of_lipschitzWith hg hg0
  refine ⟨φ, hφ, g₀, LipschitzWith.of_dist_le_mul fun y z ↦ le_of_tendsto'
    (((tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ y)).dist
      ((tendstoLocallyUniformlyOn_univ.2 hlim).tendsto_at (mem_univ z)))
    fun k ↦ (hg (φ k)).dist_le_mul y z, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hlim ⊢
  intro K hK
  obtain ⟨r, hr⟩ := (IsCompact.isBounded hK).subset_ball (0 : E d)
  refine (hlim K hK).congr ?_
  filter_upwards [(hρ.comp hφ.tendsto_atTop).eventually_gt_atTop r] with k hk
  exact fun y hy ↦ (hfg (φ k) (mem_ball.2 ((mem_ball.1 (hr hy)).trans hk))).symm

end EllipticBernoulli
