/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.L2
public import EllipticBernoulli.Sobolev.Lattice
public import EllipticBernoulli.Sobolev.LocalCompactness

/-!
# Closure of weak gradients under limits

* `TendstoWeakL2.congr_ae`: the weak limit may be changed on a null set.
* `TendstoWeakL2.of_ae_eq_off`: weak convergence on `Ω₀` extends to `Ω` if the sequence already
  equals the limit a.e. on `Ω \ Ω₀`.
* `TendstoWeakL2.mono_set`: weak convergence on `Ω` restricts to measurable `K ⊆ Ω`.
* `TendstoWeakL2.ae_eq_of_tendsto`: weak limits are unique a.e.
* `exists_tendstoWeakL2_subseq_of_monotone`, `exists_tendstoWeakL2Loc_subseq`: diagonal weak
  compactness, one subsequence converging weakly in `L²(K)` for every compact `K ⊆ U`.
* `TendstoLpLoc.exists_subseq_ae_tendsto`: an a.e. convergent subsequence on a compact set.
* `HasWeakGradient.of_tendsto`: if `G k` is a weak gradient of `v k` on the open set
  `U`, `v k → v₀` in `L²_loc(U)` and `G k ⇀ G₀` weakly in `L²(K)` for every compact `K ⊆ U`, then
  `G₀` is a weak gradient of `v₀` on `U`.

For the direct method: `exists_tendstoWeakL2Loc_subseq` gives the weak-convergence hypothesis
of `HasWeakGradient.of_tendsto` directly. Alternatively, with weak convergence on one compact `K₀`
and `G k = G₀` a.e. off a smaller set, `TendstoWeakL2.of_ae_eq_off` supplies it on every compact
`K ⊆ U`.
-/

open Set Filter Topology MeasureTheory
open scoped ENNReal ContDiff

@[expose] public noncomputable section

namespace EllipticBernoulli

section WeakL2

variable {X F ι : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure X} {f : ι → X → F} {f₀ g₀ : X → F} {l : Filter ι}

/-- The weak limit may be changed on a null set. -/
theorem TendstoWeakL2.congr_ae {Ω : Set X} (h : TendstoWeakL2 μ Ω f f₀ l)
    (hfg : f₀ =ᵐ[μ.restrict Ω] g₀) : TendstoWeakL2 μ Ω f g₀ l := by
  refine ⟨h.1, h.2.1.ae_eq hfg, fun φ hφ ↦ ?_⟩
  have e : ∫ x in Ω, inner ℝ (f₀ x) (φ x) ∂μ = ∫ x in Ω, inner ℝ (g₀ x) (φ x) ∂μ :=
    integral_congr_ae (by filter_upwards [hfg] with x hx; rw [hx])
  rw [← e]
  exact h.2.2 φ hφ

/-- **Extension of weak convergence.** If `f i ⇀ f₀` weakly in `L²(Ω₀)`, `f₀ ∈ L²(Ω)` and every
`f i` equals `f₀` a.e. on `Ω \ Ω₀`, then `f i ⇀ f₀` weakly in `L²(Ω)`. -/
theorem TendstoWeakL2.of_ae_eq_off {Ω₀ Ω : Set X} (hΩ₀ : MeasurableSet Ω₀) (hΩ : MeasurableSet Ω)
    (h : TendstoWeakL2 μ Ω₀ f f₀ l) (hf₀ : MemLp f₀ 2 (μ.restrict Ω))
    (heq : ∀ i, ∀ᵐ x ∂(μ.restrict (Ω \ Ω₀)), f i x = f₀ x) :
    TendstoWeakL2 μ Ω f f₀ l := by
  have hD : MeasurableSet (Ω \ Ω₀) := hΩ.diff hΩ₀
  -- membership in `L²(Ω)`
  have hmem : ∀ i, MemLp (f i) 2 (μ.restrict Ω) := by
    intro i
    have h1 : MemLp (Ω₀.indicator (f i)) 2 (μ.restrict Ω) :=
      ((memLp_indicator_iff_restrict hΩ₀).2 (h.1 i)).restrict Ω
    have h2 : MemLp ((Ω \ Ω₀).indicator f₀) 2 (μ.restrict Ω) := hf₀.indicator hD
    refine (h1.add h2).ae_eq ?_
    have := heq i
    rw [ae_restrict_iff' hD] at this
    filter_upwards [ae_restrict_of_ae this, ae_restrict_mem hΩ] with x hx hxΩ
    by_cases hx0 : x ∈ Ω₀
    · simp [indicator_of_mem hx0, indicator_of_notMem (fun h' : x ∈ Ω \ Ω₀ ↦ h'.2 hx0)]
    · simp [indicator_of_notMem hx0, indicator_of_mem (show x ∈ Ω \ Ω₀ from ⟨hxΩ, hx0⟩),
        hx ⟨hxΩ, hx0⟩]
  refine ⟨hmem, hf₀, fun φ hφ ↦ ?_⟩
  set φ' : X → F := Ω.indicator φ with hφ'def
  have hφ' : MemLp φ' 2 (μ.restrict Ω₀) := ((memLp_indicator_iff_restrict hΩ).2 hφ).restrict Ω₀
  have hdec : ∀ g : X → F, MemLp g 2 (μ.restrict Ω) →
      ∫ x in Ω, inner ℝ (g x) (φ x) ∂μ =
        (∫ x in Ω₀, inner ℝ (g x) (φ' x) ∂μ) + ∫ x in Ω \ Ω₀, inner ℝ (g x) (φ x) ∂μ := by
    intro g hg
    rw [← integral_inter_add_sdiff hΩ₀ (integrable_inner_of_memLp hg hφ)]
    congr 1
    have e : (fun x ↦ inner ℝ (g x) (φ' x)) = Ω.indicator (fun x ↦ inner ℝ (g x) (φ x)) := by
      funext x
      by_cases hx : x ∈ Ω
      · simp [hφ'def, indicator_of_mem hx]
      · simp [hφ'def, indicator_of_notMem hx]
    rw [e, setIntegral_indicator hΩ, inter_comm]
  have hc : ∀ i, ∫ x in Ω \ Ω₀, inner ℝ (f i x) (φ x) ∂μ =
      ∫ x in Ω \ Ω₀, inner ℝ (f₀ x) (φ x) ∂μ := fun i ↦
    integral_congr_ae (by filter_upwards [heq i] with x hx; rw [hx])
  rw [hdec f₀ hf₀]
  simp_rw [hdec _ (hmem _), hc]
  exact (h.2.2 φ' hφ').add_const _

/-- Weak convergence on `Ω` restricts to measurable subsets. -/
theorem TendstoWeakL2.mono_set {Ω K : Set X} (hK : MeasurableSet K) (hKΩ : K ⊆ Ω)
    (h : TendstoWeakL2 μ Ω f f₀ l) : TendstoWeakL2 μ K f f₀ l := by
  have hmono : μ.restrict K ≤ μ.restrict Ω := Measure.restrict_mono hKΩ le_rfl
  refine ⟨fun i ↦ (h.1 i).mono_measure hmono, h.2.1.mono_measure hmono, fun φ hφ ↦ ?_⟩
  have hφ' : MemLp (K.indicator φ) 2 (μ.restrict Ω) :=
    ((memLp_indicator_iff_restrict hK).2 hφ).restrict Ω
  have e : ∀ g : X → F, ∫ x in Ω, inner ℝ (g x) (K.indicator φ x) ∂μ =
      ∫ x in K, inner ℝ (g x) (φ x) ∂μ := by
    intro g
    have : (fun x ↦ inner ℝ (g x) (K.indicator φ x)) =
        K.indicator (fun x ↦ inner ℝ (g x) (φ x)) := by
      funext x
      by_cases hx : x ∈ K
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
    rw [this, setIntegral_indicator hK, inter_eq_right.2 hKΩ]
  have := h.2.2 _ hφ'
  simp_rw [e] at this
  exact this

/-- **Uniqueness of weak limits** in `L²(Ω)`. -/
theorem TendstoWeakL2.ae_eq_of_tendsto [l.NeBot] {Ω : Set X} (h₁ : TendstoWeakL2 μ Ω f f₀ l)
    (h₂ : TendstoWeakL2 μ Ω f g₀ l) : f₀ =ᵐ[μ.restrict Ω] g₀ := by
  have hφ : MemLp (f₀ - g₀) 2 (μ.restrict Ω) := h₁.2.1.sub h₂.2.1
  have e : ∫ x in Ω, inner ℝ (f₀ x) ((f₀ - g₀) x) ∂μ =
      ∫ x in Ω, inner ℝ (g₀ x) ((f₀ - g₀) x) ∂μ :=
    tendsto_nhds_unique (h₁.2.2 _ hφ) (h₂.2.2 _ hφ)
  have hi1 := integrable_inner_of_memLp h₁.2.1 hφ
  have hi2 := integrable_inner_of_memLp h₂.2.1 hφ
  have hfun : (fun x ↦ ‖(f₀ - g₀) x‖ ^ 2) =
      fun x ↦ inner ℝ (f₀ x) ((f₀ - g₀) x) - inner ℝ (g₀ x) ((f₀ - g₀) x) := by
    funext x
    rw [← inner_sub_left, ← Pi.sub_apply f₀ g₀ x, real_inner_self_eq_norm_sq]
  have hint : Integrable (fun x ↦ ‖(f₀ - g₀) x‖ ^ 2) (μ.restrict Ω) := by
    rw [hfun]; exact hi1.sub hi2
  have h0 : ∫ x in Ω, ‖(f₀ - g₀) x‖ ^ 2 ∂μ = 0 := by
    rw [hfun, integral_sub hi1 hi2, e, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg (fun x ↦ by positivity) hint).1 h0
  filter_upwards [hae] with x hx
  have : ‖(f₀ - g₀) x‖ = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hx
  rw [norm_eq_zero, Pi.sub_apply, sub_eq_zero] at this
  exact this

end WeakL2

section Diagonal

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] {μ : Measure X}

/-- **Diagonal weak compactness.** A sequence bounded in `L²(K m)` for every set of a monotone
sequence of measurable sets `K m` has a subsequence converging weakly in every `L²(K m)` to a
single limit. -/
theorem exists_tendstoWeakL2_subseq_of_monotone (K : ℕ → Set X) (hKm : ∀ m, MeasurableSet (K m))
    (hmono : Monotone K) (f : ℕ → X → F) (hf : ∀ n m, MemLp (f n) 2 (μ.restrict (K m)))
    (hC : ∀ m, ∃ C : ℝ, ∀ n, eLpNorm (f n) 2 (μ.restrict (K m)) ≤ ENNReal.ofReal C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f₀ : X → F,
      ∀ m, TendstoWeakL2 μ (K m) (fun n ↦ f (φ n)) f₀ atTop := by
  classical
  choose C hC using hC
  have hex : ∀ (ψ : ℕ → ℕ) (m : ℕ), ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ g : X → F, TendstoWeakL2 μ (K m) (fun n ↦ f (ψ (σ n))) g atTop :=
    fun ψ m ↦ exists_tendstoWeakL2_subseq μ (K m) (fun n ↦ f (ψ n)) (C m)
      (fun n ↦ hf _ m) (fun n ↦ hC m _)
  choose σ hσ L hL using hex
  -- the nested chain of subsequences
  let Q : ℕ → ℕ → ℕ := fun m ↦ Nat.rec id (fun m q ↦ q ∘ σ q m) m
  have hQs : ∀ m, Q (m + 1) = Q m ∘ σ (Q m) m := fun m ↦ rfl
  have hQmono : ∀ m, StrictMono (Q m) := by
    intro m
    induction m with
    | zero => exact strictMono_id
    | succ m ih => rw [hQs]; exact ih.comp (hσ _ _)
  have hQfac : ∀ m j, ∃ R : ℕ → ℕ, StrictMono R ∧ Q (m + j) = Q m ∘ R := by
    intro m j
    induction j with
    | zero => exact ⟨id, strictMono_id, rfl⟩
    | succ j ih =>
      obtain ⟨R, hR, hRe⟩ := ih
      refine ⟨R ∘ σ (Q (m + j)) (m + j), hR.comp (hσ _ _), ?_⟩
      change Q (m + j + 1) = _
      rw [hQs, hRe]
      rfl
  -- the diagonal subsequence
  set φ : ℕ → ℕ := fun n ↦ Q (n + 1) n with hφdef
  have hφ : StrictMono φ := strictMono_nat_of_lt_succ fun n ↦ by
    change Q (n + 1) n < Q (n + 1 + 1) (n + 1)
    rw [hQs (n + 1), Function.comp_apply]
    exact (hQmono (n + 1)).lt_iff_lt.2
      (lt_of_lt_of_le (Nat.lt_succ_self n) ((hσ _ _).id_le (n + 1)))
  have hconv : ∀ m, TendstoWeakL2 μ (K m) (fun n ↦ f (φ n)) (L (Q m) m) atTop := by
    intro m
    have base := hL (Q m) m
    have hfac : ∀ n, m ≤ n → ∃ k, n ≤ k ∧ φ n = Q (m + 1) k := by
      intro n hn
      obtain ⟨R, hR, hRe⟩ := hQfac (m + 1) (n - m)
      refine ⟨R n, hR.id_le n, ?_⟩
      have e : n + 1 = m + 1 + (n - m) := by omega
      change Q (n + 1) n = _
      rw [e, hRe]
      rfl
    choose! k hk hkφ using hfac
    have hk_tend : Tendsto k atTop atTop :=
      tendsto_atTop_mono' atTop ((eventually_ge_atTop m).mono fun n hn ↦ hk n hn) tendsto_id
    refine ⟨fun n ↦ hf _ m, base.2.1, fun ψ hψ ↦ ?_⟩
    refine ((base.2.2 ψ hψ).comp hk_tend).congr' ?_
    filter_upwards [eventually_ge_atTop m] with n hn
    simp only [Function.comp_apply, hkφ n hn, hQs]
  have hcons : ∀ j m, j ≤ m → L (Q j) j =ᵐ[μ.restrict (K j)] L (Q m) m := fun j m hjm ↦
    (hconv j).ae_eq_of_tendsto ((hconv m).mono_set (hKm j) (hmono hjm))
  -- glue the limits
  let idx : X → ℕ := fun x ↦ if h : ∃ m, x ∈ K m then Nat.find h else 0
  refine ⟨φ, hφ, fun x ↦ L (Q (idx x)) (idx x) x, fun m ↦ (hconv m).congr_ae ?_⟩
  have hall : ∀ᵐ x ∂(μ.restrict (K m)), ∀ j, j ≤ m → x ∈ K j → L (Q j) j x = L (Q m) m x := by
    rw [ae_all_iff]
    intro j
    by_cases hjm : j ≤ m
    · have h := hcons j m hjm
      rw [EventuallyEq, ae_restrict_iff' (hKm j)] at h
      filter_upwards [ae_restrict_of_ae h] with x hx _ hxj using hx hxj
    · exact Eventually.of_forall fun x h ↦ absurd h hjm
  filter_upwards [hall, ae_restrict_mem (hKm m)] with x hx hxm
  have hex : ∃ j, x ∈ K j := ⟨m, hxm⟩
  have hidx : idx x = Nat.find hex := dite_eq_left hex
  change L (Q m) m x = L (Q (idx x)) (idx x) x
  rw [hidx]
  exact (hx _ (Nat.find_min' hex hxm) (Nat.find_spec hex)).symm

end Diagonal

section LocalWeak

variable {d : ℕ}

/-- **Diagonal weak `L²_loc` compactness.** A sequence
bounded in `L²(K)` for every compact `K ⊆ U` has a subsequence converging weakly in `L²(K)` for
every compact `K ⊆ U`, to a single limit. -/
theorem exists_tendstoWeakL2Loc_subseq {U : Set (E d)} (hU : IsOpen U) (G : ℕ → E d → E d)
    (hG : ∀ n, ∀ K ⊆ U, IsCompact K → MemLp (G n) 2 (volume.restrict K))
    (hbdd : ∀ K ⊆ U, IsCompact K → ∃ C : ℝ, ∀ n,
      eLpNorm (G n) 2 (volume.restrict K) ≤ ENNReal.ofReal C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G₀ : E d → E d,
      ∀ K ⊆ U, IsCompact K → TendstoWeakL2 volume K (fun n ↦ G (φ n)) G₀ atTop := by
  obtain ⟨φ, hφ, G₀, hconv⟩ := exists_tendstoWeakL2_subseq_of_monotone (exhaust U)
    (fun m ↦ (isCompact_exhaust U m).measurableSet) (exhaust_mono U) G
    (fun n m ↦ hG n _ (exhaust_subset U m) (isCompact_exhaust U m))
    (fun m ↦ hbdd _ (exhaust_subset U m) (isCompact_exhaust U m))
  refine ⟨φ, hφ, G₀, fun K hKU hK ↦ ?_⟩
  obtain ⟨M, hM⟩ := exists_subset_exhaust hU hK hKU
  exact (hconv M).mono_set hK.measurableSet hM

end LocalWeak

section Closure

variable {d : ℕ}

/-- `L²_loc` convergence gives an a.e. convergent subsequence on any compact `K ⊆ U` (via
convergence in measure). -/
theorem TendstoLpLoc.exists_subseq_ae_tendsto {U K : Set (E d)} {v : ℕ → E d → ℝ}
    {v₀ : E d → ℝ} (hv : TendstoLpLoc 2 volume U v v₀ atTop) (hKU : K ⊆ U) (hK : IsCompact K)
    (_hvm : ∀ k, AEStronglyMeasurable (v k) (volume.restrict K))
    (_hv₀ : AEStronglyMeasurable v₀ (volume.restrict K)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂(volume.restrict K), Tendsto (fun i ↦ v (ns i) x) atTop (𝓝 (v₀ x)) :=
  (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero (hv K hKU hK)).exists_seq_tendsto_ae

/-- **Closure of weak gradients.** Let `U` be open, `G k` a weak gradient of `v k` on
`U`, `v₀` a.e.-strongly measurable on `U` with `v k → v₀` in `L²_loc(U)`, and `G k ⇀ G₀` weakly in
`L²(K)` for every compact `K ⊆ U`. Then `G₀` is a weak gradient of `v₀` on `U`. -/
theorem HasWeakGradient.of_tendsto {U : Set (E d)} (hU : IsOpen U) {v : ℕ → E d → ℝ}
    {G : ℕ → E d → E d} {v₀ : E d → ℝ} {G₀ : E d → E d}
    (hvG : ∀ k, HasWeakGradient U (v k) (G k))
    (_hv₀ : AEStronglyMeasurable v₀ (volume.restrict U))
    (hv : TendstoLpLoc 2 volume U v v₀ atTop)
    (hG : ∀ K ⊆ U, IsCompact K → TendstoWeakL2 volume K G G₀ atTop) :
    HasWeakGradient U v₀ G₀ := by
  -- eventually `v k - v₀ ∈ L²(K)` on every compact `K ⊆ U`
  have hev : ∀ K ⊆ U, IsCompact K →
      ∀ᶠ k in atTop, MemLp (fun x ↦ v k x - v₀ x) 2 (volume.restrict K) := by
    intro K hKU hK
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    filter_upwards [(hv K hKU hK).eventually (gt_mem_nhds ENNReal.zero_lt_top)] with k hk
    exact hk
  have hv₀int : ∀ K ⊆ U, IsCompact K → IntegrableOn v₀ K := by
    intro K hKU hK
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    obtain ⟨k, hk⟩ := (hev K hKU hK).exists
    have h1 : IntegrableOn (v k) K := (hvG k).1.integrableOn_compact_subset hKU hK
    have h2 : IntegrableOn (fun x ↦ v k x - v₀ x) K := hk.integrable one_le_two
    have e : v₀ = v k - fun x ↦ v k x - v₀ x := by funext x; simp
    rw [e]
    exact h1.sub h2
  have hloc₀ : LocallyIntegrableOn v₀ U :=
    (locallyIntegrableOn_iff hU.isLocallyClosed).2 hv₀int
  have hlocG : LocallyIntegrableOn G₀ U :=
    (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK ↦ by
      have : IsFiniteMeasure (volume.restrict K) :=
        isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
      exact (hG K hKU hK).2.1.integrable one_le_two
  refine ⟨hloc₀, hlocG, fun φ hφ hφc hφU e ↦ ?_⟩
  set T := tsupport φ with hTdef
  have hT : IsCompact T := hφc
  have hTm : MeasurableSet T := hT.measurableSet
  set ψ : E d → ℝ := fun x ↦ fderiv ℝ φ x e with hψ
  have hψc : Continuous ψ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ0 : ∀ x ∉ T, ψ x = 0 := fun x hx ↦ fderiv_apply_eq_zero_of_notMem_tsupport hx e
  have hφ0 : ∀ x ∉ T, φ x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport hx
  -- reduce the integrals over `U` to integrals over `T`
  have hUT : ∀ F : E d → ℝ, (∀ x ∉ T, F x = 0) → ∫ x in U, F x = ∫ x in T, F x := fun F hF ↦
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hφU fun x hx ↦ hF x hx.2
  have hψL : MemLp ψ 2 (volume.restrict T) :=
    (hψc.memLp_of_hasCompactSupport (hφc.fderiv_apply (𝕜 := ℝ) e)).restrict T
  -- left-hand side
  have hL : Tendsto (fun k ↦ ∫ x in U, v k x * ψ x) atTop (𝓝 (∫ x in U, v₀ x * ψ x)) := by
    have hk : ∀ k, ∫ x in U, v k x * ψ x = ∫ x in T, v k x * ψ x := fun k ↦
      hUT _ fun x hx ↦ by simp [hψ0 x hx]
    rw [hUT (fun x ↦ v₀ x * ψ x) fun x hx ↦ by simp [hψ0 x hx]]
    simp_rw [hk]
    have hi : ∀ k, IntegrableOn (fun x ↦ v k x * ψ x) T := fun k ↦
      ((hvG k).1.integrableOn_compact_subset hφU hT).mul_continuousOn hψc.continuousOn hT
    have hi₀ : IntegrableOn (fun x ↦ v₀ x * ψ x) T :=
      (hv₀int T hφU hT).mul_continuousOn hψc.continuousOn hT
    rw [← tendsto_sub_nhds_zero_iff]
    have hlim : Tendsto (fun k ↦ (eLpNorm (v k - v₀) 2 (volume.restrict T)).toReal *
        (eLpNorm ψ 2 (volume.restrict T)).toReal) atTop (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
        (hv T hφU hT)).mul_const (eLpNorm ψ 2 (volume.restrict T)).toReal
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hev T hφU hT] with k hk
    rw [← integral_sub (hi k) hi₀, Real.norm_eq_abs]
    have e1 : (fun x ↦ v k x * ψ x - v₀ x * ψ x) = fun x ↦ (v k x - v₀ x) * ψ x := by
      funext x; ring
    rw [e1]
    refine (abs_integral_mul_le_L2 hk hψL).trans (le_of_eq ?_)
    rfl
  -- right-hand side
  have hR : Tendsto (fun k ↦ ∫ x in U, inner ℝ (G k x) e * φ x) atTop
      (𝓝 (∫ x in U, inner ℝ (G₀ x) e * φ x)) := by
    have hk : ∀ k, ∫ x in U, inner ℝ (G k x) e * φ x = ∫ x in T, inner ℝ (G k x) e * φ x :=
      fun k ↦ hUT _ fun x hx ↦ by simp [hφ0 x hx]
    rw [hUT (fun x ↦ inner ℝ (G₀ x) e * φ x) fun x hx ↦ by simp [hφ0 x hx]]
    simp_rw [hk]
    have hφe : MemLp (fun x ↦ φ x • e) 2 (volume.restrict T) :=
      ((hφ.continuous.smul continuous_const).memLp_of_hasCompactSupport
        (hφc.smul_right (f' := fun _ ↦ e))).restrict T
    have h := (hG T hφU hT).2.2 _ hφe
    have e2 : ∀ g : E d → E d, (fun x ↦ inner ℝ (g x) (φ x • e)) =
        fun x ↦ inner ℝ (g x) e * φ x := by
      intro g; funext x; rw [inner_smul_right, mul_comm]
    simp_rw [e2] at h
    exact h
  have hk : ∀ k, ∫ x in U, v k x * ψ x = -∫ x in U, inner ℝ (G k x) e * φ x :=
    fun k ↦ (hvG k).2.2 φ hφ hφc hφU e
  simp_rw [hk] at hL
  exact tendsto_nhds_unique hL hR.neg

end Closure

end EllipticBernoulli
