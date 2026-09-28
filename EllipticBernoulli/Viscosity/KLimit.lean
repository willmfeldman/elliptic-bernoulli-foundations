/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.KLimit
public import Mathlib.Topology.Compactness.Compact

/-!
# Upper Kuratowski limits

Elementary facts on `upperKLimit` (`Basic/KLimit.lean`), used in the stability of relaxed
subsolutions (Abedin–Feldman–Stinson, Lemma 2.4(ii); `Viscosity/Stability.lean`):
`isClosed_upperKLimit`, `upperKLimit_subset_closure`, `mem_upperKLimit_of_eventually_mem`,
`IsCompact.eventually_forall_not_mem_of_disjoint_upperKLimit`.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology

public section

namespace EllipticBernoulli


section KLimit

variable {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} {l : Filter ι}

/-- The upper Kuratowski limit is closed. -/
theorem isClosed_upperKLimit : IsClosed (upperKLimit A l) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have : ∃ N ∈ 𝓝 x, ¬ ∃ᶠ i in l, (A i ∩ N).Nonempty := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hx hcon
  obtain ⟨N, hN, hfr⟩ := this
  obtain ⟨t, htN, ht, hxt⟩ := mem_nhds_iff.1 hN
  filter_upwards [ht.mem_nhds hxt] with y hy hyA
  exact hfr ((hyA t (ht.mem_nhds hy)).mono fun i hi ↦ hi.mono (inter_subset_inter_right _ htN))

/-- If eventually `A i ⊆ S`, then the upper Kuratowski limit lies in `closure S`. -/
theorem upperKLimit_subset_closure {S : Set X} (h : ∀ᶠ i in l, A i ⊆ S) :
    upperKLimit A l ⊆ closure S := by
  intro x hx
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨i, ⟨y, hyA, hyt⟩, hi⟩ := ((hx t ht).and_eventually h).exists
  exact ⟨y, hyt, hi hyA⟩

/-- A point which eventually belongs to `A i` belongs to the upper Kuratowski limit. -/
theorem mem_upperKLimit_of_eventually_mem [l.NeBot] {x : X} (h : ∀ᶠ i in l, x ∈ A i) :
    x ∈ upperKLimit A l :=
  fun _ hN ↦ (h.mono fun _ hi ↦ ⟨x, hi, mem_of_mem_nhds hN⟩).frequently

/-- A compact set disjoint from the upper Kuratowski limit is eventually disjoint from `A i`. -/
theorem IsCompact.eventually_forall_not_mem_of_disjoint_upperKLimit {K : Set X}
    (hK : IsCompact K) (h : ∀ y ∈ K, y ∉ upperKLimit A l) :
    ∀ᶠ i in l, ∀ y ∈ K, y ∉ A i := by
  refine hK.induction_on (p := fun s ↦ ∀ᶠ i in l, ∀ y ∈ s, y ∉ A i) (by simp)
    (fun s t hst ht ↦ ht.mono fun i hi y hy ↦ hi y (hst hy))
    (fun s t hs ht ↦ (hs.and ht).mono fun i hi y hy ↦ hy.elim (hi.1 y) (hi.2 y)) ?_
  intro x hx
  have : ∃ N ∈ 𝓝 x, ¬ ∃ᶠ i in l, (A i ∩ N).Nonempty := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact h x hx hcon
  obtain ⟨N, hN, hfr⟩ := this
  refine ⟨N, mem_nhdsWithin_of_mem_nhds hN, ?_⟩
  rw [not_frequently] at hfr
  exact hfr.mono fun i hi y hy hyA ↦ hi ⟨y, hyA, hy⟩

end KLimit

end EllipticBernoulli

end
