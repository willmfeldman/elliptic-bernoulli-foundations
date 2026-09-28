/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Data.Real.Basic

/-!
# Upper Kuratowski limits

`upperKLimit A l`: the `limsup*` of a family of sets, used in the stability of relaxed
subsolutions (Abedin–Feldman–Stinson, Lemma 2.4(ii); stated here as `ViscStabilityStatement`).

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {X ι : Type*}

/-- Upper Kuratowski limit of a family of sets along a filter (the `limsup*` of
Abedin–Feldman–Stinson): `x` belongs to it iff every neighbourhood of `x` meets `A i` for
frequently many `i` along `l`. For `l = atTop` on `ℕ` in a metric space this is the set of limits
`x = lim x_{j_k}` of subsequences with `x_{j_k} ∈ A_{j_k}`, as used by Abedin–Feldman–Stinson
(e.g. in the proof of Lemma 5.1). -/
def upperKLimit [TopologicalSpace X] (A : ι → Set X) (l : Filter ι) : Set X :=
  {x | ∀ N ∈ 𝓝 x, ∃ᶠ i in l, (A i ∩ N).Nonempty}

end EllipticBernoulli
