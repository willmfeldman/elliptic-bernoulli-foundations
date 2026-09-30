/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Harmonic
public import EllipticBernoulli.Harmonic.Limit
public import EllipticBernoulli.Harmonic.MaxPrinciple
import ViscositySolns.Applications.Laplace.Dirichlet
import ViscositySolns.Applications.Laplace.ExteriorSphere

/-!
# The Dirichlet problem on a ball with continuous data

* `exists_lipschitzWith_abs_sub_le_of_continuousOn` (Lipschitz approximation): a
  function continuous on a compact set `S` of a metric space is uniformly approximated on `S` by
  globally Lipschitz functions, namely the inf-convolutions `y ↦ ⨅ z ∈ S, g z + K dist y z`.
* `exists_harmonic_ball_boundary_of_lipschitzWith`: the Dirichlet problem on `ball x r ⊆ E d`
  with Lipschitz data, from `ViscositySolns.dirichlet_harmonic_modulus_of_uniformExteriorSphere`
  (CIL Perron method with exterior-sphere barriers, in the `viscosity_solns` dependency) and
  `ViscositySolns.uniformExteriorSphere_ball`.
* `exists_harmonic_ball_boundary` (`DirichletBallStatement`): continuous data.

## Proof of `exists_harmonic_ball_boundary`

Approximate `g` on the sphere `S = sphere x r` within `1/(n+1)` by Lipschitz `G n`, and let `h n`
solve the Dirichlet problem with data `G n`. By the weak maximum principle
(`le_of_harmonic_boundary`) `|h n - h m| ≤ 1/(n+1) + 1/(m+1)` on `closedBall x r`, so `h n`
converges uniformly there to some `h`. The limit is continuous on `closedBall x r`, harmonic in
`ball x r` (`harmonicOnNhd_of_tendstoLocallyUniformlyOn'`) and equals `g` on `S`.
-/

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian NNReal

public section

namespace EllipticBernoulli

/-! ### Lipschitz approximation -/

/-- **Lipschitz approximation on a compact set.** If `g` is continuous on a compact subset `S`
of a pseudometric space, then for every `δ > 0` there is a globally Lipschitz `G` with
`|G - g| ≤ δ` on `S`. -/
theorem exists_lipschitzWith_abs_sub_le_of_continuousOn {X : Type*} [PseudoMetricSpace X]
    {S : Set X} (hS : IsCompact S) {g : X → ℝ} (hg : ContinuousOn g S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℝ≥0, ∃ G : X → ℝ, LipschitzWith K G ∧ ∀ y ∈ S, |G y - g y| ≤ δ := by
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨0, fun _ ↦ 0, LipschitzWith.const _, by simp⟩
  have : Nonempty S := hSne.coe_sort
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hg
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ hSne.some_mem)
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hg) δ hδ
  set K : ℝ≥0 := ⟨2 * B / η, by positivity⟩ with hK
  have hKη : (K : ℝ) * η = 2 * B := by
    change 2 * B / η * η = 2 * B
    field_simp
  set G : X → ℝ := fun y ↦ ⨅ z : S, (g z + K * dist y z) with hG
  have hBdd : ∀ y : X, BddBelow (range fun z : S ↦ g z + K * dist y (z : X)) := fun y ↦ by
    refine ⟨-B, ?_⟩
    rintro w ⟨z, rfl⟩
    have h1 := hB z z.2
    rw [Real.norm_eq_abs, abs_le] at h1
    have : 0 ≤ (K : ℝ) * dist y z := by positivity
    dsimp only
    linarith
  refine ⟨K, G, LipschitzWith.of_le_add_mul K fun y₁ y₂ ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← sub_le_iff_le_add]
    refine le_ciInf fun z ↦ ?_
    rw [sub_le_iff_le_add]
    calc G y₁ ≤ g z + K * dist y₁ z := ciInf_le (hBdd y₁) z
      _ ≤ g z + K * dist y₂ z + K * dist y₁ y₂ := by
        rw [add_assoc, ← mul_add, add_comm (dist y₂ z)]
        gcongr
        exact dist_triangle _ _ _
  · have hup : G y ≤ g y := by
      simpa using ciInf_le (hBdd y) ⟨y, hy⟩
    have hlow : g y - δ ≤ G y := by
      refine le_ciInf fun z ↦ ?_
      by_cases hyz : dist y z < η
      · have := hηg y hy z z.2 hyz
        rw [Real.dist_eq, abs_lt] at this
        have : 0 ≤ (K : ℝ) * dist y z := by positivity
        linarith
      · have h1 := hB z z.2
        have h2 := hB y hy
        rw [Real.norm_eq_abs, abs_le] at h1 h2
        have : (K : ℝ) * η ≤ K * dist y z := by gcongr; exact not_lt.1 hyz
        linarith
    rw [abs_le]
    constructor <;> linarith

/-! ### Lipschitz data -/

variable {d : ℕ}

/-- **The Dirichlet problem on a ball with Lipschitz data** (`viscosity_solns`). -/
theorem exists_harmonic_ball_boundary_of_lipschitzWith (x : E d) {r : ℝ} (hr : 0 < r)
    {K : ℝ≥0} {G : E d → ℝ} (hG : LipschitzWith K G) :
    ∃ h : E d → ℝ, ContinuousOn h (closedBall x r) ∧ HarmonicOnNhd h (ball x r) ∧
      EqOn h G (sphere x r) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall x r).exists_bound_of_continuousOn
    hG.continuous.continuousOn
  obtain ⟨ϖ, -, hsol⟩ := ViscositySolns.dirichlet_harmonic_modulus_of_uniformExteriorSphere
    isOpen_ball isBounded_ball (ViscositySolns.uniformExteriorSphere_ball x hr) K M
  rw [closure_ball x hr.ne'] at hsol
  obtain ⟨h, hc, h2, hΔ, hfr, -⟩ := hsol G hG.lipschitzOnWith fun y hy ↦ by
    simpa [Real.norm_eq_abs] using hM y hy
  refine ⟨h, hc, (harmonicOnNhd_iff_contDiffOn_laplacian_eq_zero isOpen_ball).2 ⟨h2, hΔ⟩,
    fun y hy ↦ hfr y ?_⟩
  rwa [frontier_ball x hr.ne']

/-! ### Continuous data -/

/-- **Dirichlet problem on a ball with continuous data** (`DirichletBallStatement`). -/
theorem exists_harmonic_ball_boundary : DirichletBallStatement := by
  intro d hd x r g hr hg
  have := nontrivial_E_of_one_le hd
  -- Lipschitz approximations `G n` and their harmonic extensions `h n`
  have happrox : ∀ n : ℕ, ∃ K : ℝ≥0, ∃ G : E d → ℝ, LipschitzWith K G ∧
      ∀ y ∈ sphere x r, |G y - g y| ≤ 1 / ((n : ℝ) + 1) := fun n ↦
    exists_lipschitzWith_abs_sub_le_of_continuousOn (isCompact_sphere x r) hg (by positivity)
  choose K G hGL hGg using happrox
  have hsol : ∀ n, ∃ h : E d → ℝ, ContinuousOn h (closedBall x r) ∧
      HarmonicOnNhd h (ball x r) ∧ EqOn h (G n) (sphere x r) := fun n ↦
    exists_harmonic_ball_boundary_of_lipschitzWith x hr (hGL n)
  choose H hHc hHh hHG using hsol
  have hcl : closure (ball x r) = closedBall x r := closure_ball x hr.ne'
  have hfr : frontier (ball x r) = sphere x r := frontier_ball x hr.ne'
  -- uniform Cauchy estimate
  have hcauchy : ∀ n m, ∀ y ∈ closedBall x r,
      |H n y - H m y| ≤ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by
    intro n m
    have key : ∀ n m, ∀ y ∈ closedBall x r,
        H n y ≤ H m y + (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) := by
      intro n m y hy
      have hk : HarmonicOnNhd (fun z ↦ H m z + (1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)))
          (ball x r) := fun z hz ↦ by
        have := (hHh m z hz).add (harmonicAt_const (c := (1 / ((n : ℝ) + 1) +
          1 / ((m : ℝ) + 1))))
        exact this
      refine le_of_harmonic_boundary isOpen_ball isBounded_ball (hHh n) hk
        (by rw [hcl]; exact hHc n) (by rw [hcl]; exact (hHc m).add continuousOn_const)
        (fun z hz ↦ ?_) y (by rw [hcl]; exact hy)
      rw [hfr] at hz
      rw [hHG n hz, hHG m hz]
      have h1 := hGg n z hz
      have h2 := hGg m z hz
      rw [abs_le] at h1 h2
      linarith
    intro y hy
    rw [abs_le]
    constructor
    · linarith [key m n y hy]
    · linarith [key n m y hy]
  -- the pointwise limit
  have hcs : ∀ y ∈ closedBall x r, CauchySeq fun n ↦ H n y := by
    intro y hy
    refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [Real.dist_eq]
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
    have hb : ∀ k : ℕ, N ≤ k → 1 / ((k : ℝ) + 1) < ε / 2 := fun k hk ↦ by
      rw [div_lt_iff₀ (by positivity)]
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      have := (div_lt_iff₀ hε).1 hN
      nlinarith
    have := hcauchy n N y hy
    linarith [hb n hn, hb N le_rfl]
  set h : E d → ℝ := fun y ↦ limUnder atTop fun n ↦ H n y with hh_def
  have hlim : ∀ y ∈ closedBall x r, Tendsto (fun n ↦ H n y) atTop (𝓝 (h y)) :=
    fun y hy ↦ (hcs y hy).tendsto_limUnder
  have hdist : ∀ n, ∀ y ∈ closedBall x r, |H n y - h y| ≤ 1 / ((n : ℝ) + 1) := by
    intro n y hy
    have ht : Tendsto (fun m : ℕ ↦ 1 / ((n : ℝ) + 1) + 1 / ((m : ℝ) + 1)) atTop
        (𝓝 (1 / ((n : ℝ) + 1) + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at ht
    exact le_of_tendsto_of_tendsto ((tendsto_const_nhds.sub (hlim y hy)).abs) ht
      (Eventually.of_forall fun m ↦ hcauchy n m y hy)
  have hunif : TendstoUniformlyOn H h atTop (closedBall x r) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    filter_upwards [eventually_ge_atTop N] with n hn y hy
    rw [Real.dist_eq, abs_sub_comm]
    refine (hdist n y hy).trans_lt ?_
    rw [div_lt_iff₀ (by positivity)]
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    have := (div_lt_iff₀ hε).1 hN
    nlinarith
  refine ⟨h, hunif.continuousOn (Frequently.of_forall hHc), ?_, fun y hy ↦ ?_⟩
  · exact (harmonicOnNhd_of_tendstoLocallyUniformlyOn' isOpen_ball hHh
      (hunif.mono ball_subset_closedBall).tendstoLocallyUniformlyOn).1
  · have hy' : y ∈ closedBall x r := sphere_subset_closedBall hy
    have hle : ∀ n : ℕ, |h y - g y| ≤ 2 / ((n : ℝ) + 1) := fun n ↦ by
      have h1 := hdist n y hy'
      have h2 := hGg n y hy
      rw [hHG n hy] at h1
      calc |h y - g y| ≤ |G n y - h y| + |G n y - g y| := by
            rw [abs_sub_comm (G n y) (h y)]; exact abs_sub_le _ _ _
        _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := add_le_add h1 h2
        _ = 2 / ((n : ℝ) + 1) := by ring
    have ht : Tendsto (fun n : ℕ ↦ 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
      rw [mul_zero] at this
      exact this.congr fun n ↦ mul_one_div _ _
    have h0 : |h y - g y| ≤ 0 := ge_of_tendsto ht (Eventually.of_forall hle)
    have := abs_nonpos_iff.1 h0
    linarith

end EllipticBernoulli
