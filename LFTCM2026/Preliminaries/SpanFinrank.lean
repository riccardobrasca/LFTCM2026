/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

public import Mathlib

/-!
# The missing `Submodule.spanFinrank` API

Mathlib knows that the minimal number of generators of a submodule over a division ring is its
dimension (`Module.finrank_eq_spanFinrank_of_free` and `Submodule.spanFinrank_top`), but it states
the basic dimension lemmas for subspaces in terms of `Module.finrank` only. The session
`4_WorkingWithMathlib` states its worked example with `Submodule.spanFinrank`, so it needs the
`spanFinrank` version of each of them.

They are all the same one-line argument: rewrite with `Submodule.spanFinrank_eq_finrank` and apply
the `Module.finrank` lemma. Nothing here is deep; it is simply missing from Mathlib.
-/

public section

namespace Submodule

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M]

/-- Over a division ring, the minimal number of generators of a submodule is its dimension. -/
lemma spanFinrank_eq_finrank (p : Submodule K M) : p.spanFinrank = Module.finrank K p := by
  rw [Module.finrank_eq_spanFinrank_of_free, spanFinrank_top]

/-- The `spanFinrank` version of `Submodule.finrank_le`. -/
lemma spanFinrank_le [Module.Finite K M] (p : Submodule K M) :
    p.spanFinrank ≤ Module.finrank K M := by
  rw [spanFinrank_eq_finrank]
  exact p.finrank_le

/-- Grassmann's formula, the `spanFinrank` version of
`Submodule.finrank_sup_add_finrank_inf_eq`. -/
lemma spanFinrank_sup_add_spanFinrank_inf_eq [FiniteDimensional K M] (p q : Submodule K M) :
    (p ⊔ q).spanFinrank + (p ⊓ q).spanFinrank = p.spanFinrank + q.spanFinrank := by
  simp only [spanFinrank_eq_finrank]
  exact finrank_sup_add_finrank_inf_eq p q

/-- The `spanFinrank` version of `Submodule.finrank_lt_finrank_of_lt`. -/
lemma spanFinrank_lt_spanFinrank_of_lt [FiniteDimensional K M] {p q : Submodule K M} (h : p < q) :
    p.spanFinrank < q.spanFinrank := by
  simp only [spanFinrank_eq_finrank]
  exact finrank_lt_finrank_of_lt h

/-- The `spanFinrank` version of `Submodule.eq_of_le_of_finrank_eq`. -/
lemma eq_of_le_of_spanFinrank_eq [FiniteDimensional K M] {p q : Submodule K M} (hpq : p ≤ q)
    (h : p.spanFinrank = q.spanFinrank) : p = q :=
  eq_of_le_of_finrank_eq hpq (by simpa only [spanFinrank_eq_finrank] using h)

end Submodule
