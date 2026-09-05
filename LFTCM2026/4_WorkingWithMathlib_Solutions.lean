/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import LFTCM2026.Preliminaries

open Nat

/-!
# Working with Mathlib

Two questions come up constantly once one starts using Mathlib: "Is what I need already
there? How do I find it?", and, when dealing with non-trivial concepts, "how do I state it?".
-/

/-!
## Part 1: searching in Mathlib

Mathlib is very large, and it already contains most of the elementary mathematics you will need.
So, in front of a goal, the first question to ask is not "how do I prove this?" but "is it already
there?". The answer is very often yes, and the real difficulty is finding the *name*.

Our running example: for integers `a`, `b` and `c`, `a - b + c = a + (c - b)`.
This is surely in Mathlib. How do we find it?

Sections 1 and 2 work offline. The `#leansearch` and `#loogle` commands in sections 3–5 send queries
to external servers when Lean elaborates them. Put the cursor on a query to see the answers in the
Infoview; clicking a suggestion replaces the query with a `#check` command.

A connection or response error can mean that the network or server is unavailable. Retry later,
or comment out the query and continue with the offline tools. Online results may use a different
Mathlib version: always check the suggested name and statement in this project.
-/

/-!
### 1. Guessing the name

Names in Mathlib usually *describe the statement*. Useful ingredients include:

* operations: `add`, `sub`, `mul`, `div`, `neg`, `inv`, `pow`, `abs`, `sqrt`, ...;
* relations: `eq`, `le`, `lt`, `ne`, `dvd`, `mem`, `subset`, ...;
* qualifiers: `comm`, `assoc`, `left`, `right`, `self`, `cancel`, `zero`, `one`, `nonneg`, `pos`,
  ...

Types and predicates use `UpperCamelCase` (`Finset`, `Continuous`, `LinearIndependent`), while
theorem names use `snake_case` (`add_comm`). Other definitions use `lowerCamelCase`, as in
`Submodule.spanFinrank`; these words keep their internal capitals in theorem names too.
Results often live in a namespace, as in `Nat.factorial_pos`. Two other useful patterns are
`conclusion_of_hypothesis` and `property_iff_characterization`. The conventions are documented at
<https://leanprover-community.github.io/contribute/naming.html>.

`#check` prints the type or statement attached to a name. Use Go to Definition (`F12`) on the name
to read its source and discover nearby lemmas.
-/

-- `a + b = b + a`: an addition, commuted.
#check add_comm

-- `0 ≤ a - b ↔ b ≤ a`: a subtraction being nonnegative.
#check sub_nonneg

-- Our running example: a subtraction and an addition, commuted.
#check add_comm_sub

example (a b c : ℤ) : a - b + c = a + (c - b) := by
  exact add_comm_sub a b c
  done

/- The first guess is not always right, but it is usually close, and this is what matters: in
VS Code you do not type the whole name, you type the beginning of it and press `Ctrl+Space` to see
all the names starting like that.

For instance the triangle inequality is *not* called `abs_add`, but typing `abs_add` and asking for
the completions shows it immediately: the statement is an inequality, and the name says so. -/
#check abs_add_le

/-!
### 2. Asking Lean: `exact?`, `apply?`, `simp?`

These tactics search the imported library and suggest proof steps. Searching can be slow: in a
finished proof, click the suggestion in the Infoview to replace the search with the proof it found.
-/

/- `exact?` looks for a proof using library lemmas and the local hypotheses. -/
example (a b c : ℤ) : a - b + c = a + (c - b) := by
  exact?
  done

example (n : ℕ) : 0 < n ! := by
  exact?
  done

/- A continuous function on a compact set attains its minimum. In Mathlib the conclusion is
written with `IsMinOn`: `IsMinOn f s x` says that `f x ≤ f y` for every `y ∈ s`.

The next two demonstrations are commented out in this solutions file because the statement is
false when `s` is empty. Uncomment them to try the searches. In general, a failed search does
*not* mean that the statement is false. -/
/-
example {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  exact?
  done
-/

/- `apply?` also lists the lemmas that close the goal *up to* some hypotheses. The list is long,
but it contains `refine IsCompact.exists_isMinOn hs ?_ hf`, with `s.Nonempty` as the remaining
goal: the assumption our statement was missing. A search that fails is informative too.

Here `apply?` admits the goal with `sorry` after printing its partial suggestions. This is not a
completed proof: choose a suggestion and prove its remaining goals. -/
/-
example {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  apply?
  done
-/

/- Inspect the lemma, add the missing assumption, and use it. Try `exact?` here as well. -/
#check IsCompact.exists_isMinOn

example {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ} (hs : IsCompact s)
    (hne : s.Nonempty) (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  exact IsCompact.exists_isMinOn hs hne hf
  done

/- `simp?` simplifies the goal and suggests a `simp only [...]` proof listing the lemmas it used.
It is useful for discovering simplification lemmas. -/
example (a b : ℤ) : a - b + b = a := by
  simp?
  done

/-!
### 3. LeanSearch: searching in English

<https://leansearch.net/> answers queries written in natural language, and is available inside Lean
as the `#leansearch` command (it also works as a term and as a tactic). The query is a string, and
it must end with `.` or `?`.
-/

#leansearch "Triangle inequality for the absolute value: |a + b| ≤ |a| + |b|."

#leansearch "The sum of the first n natural numbers is n(n+1)/2."

/- Look for `Finset.sum_range_id`. It sums over `Finset.range n = {0, ..., n - 1}`, so we use
`n + 1`, simplify `(n + 1) - 1`, and exchange the factors. -/
#check Finset.sum_range_id

example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  rw [Finset.sum_range_id]
  rw [Nat.add_sub_cancel, Nat.mul_comm] -- `grind` works too
  done

/-!
### 4. Loogle: searching by shape

<https://loogle.lean-lang.org/> searches Mathlib by *pattern*. It is a bit more technical than
LeanSearch, since one has to describe the shape of the statement rather than its content, but it is
also much more precise. It is available inside Lean as the `#loogle` command (it also works as a
tactic). A query is a list of filters, separated by commas, that must all be satisfied:

* a pattern, where `_` matches anything: `_ - _ + _ = _`;
* `⊢` (typed `\vdash`) in front of a pattern restricts the match to the conclusion of the
  statement — the web interface also accepts the ASCII form `|-`, but the `#loogle` command does
  not;
* a constant, such as `Finset.sum`, asks for the statements mentioning it;
* a string, such as `"comm"`, asks for the *names* containing it.
-/

-- The running example, described by its shape.
#loogle _ - _ + _ = _ + (_ - _)

-- The triangle inequality, described by its conclusion.
#loogle ⊢ |_ + _| ≤ _

-- Everything about `Real.sqrt` whose conclusion is an inequality.
#loogle Real.sqrt, ⊢ _ ≤ _

-- Everything mentioning `Finset.sum` whose name contains "comm".
#loogle "comm", Finset.sum

/-!
### 5. A complete example

In a finite-dimensional vector space, a linearly independent family has at most `Module.finrank K V`
elements.
-/

#leansearch "The cardinality of a linearly independent family is at most the dimension."

#loogle LinearIndependent, Module.finrank

/- Look for `LinearIndependent.fintype_card_le_finrank`. Compare its hypotheses with ours:
Mathlib often states a more general result than the one we need. -/
#check LinearIndependent.fintype_card_le_finrank

-- `hv.fintype_card_le_finrank` is dot notation for `LinearIndependent.fintype_card_le_finrank hv`.
example {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] (v : ι → V) (hv : LinearIndependent K v) :
    Fintype.card ι ≤ Module.finrank K V := by
  exact hv.fintype_card_le_finrank
  done

/-!
### Exercises

Each result is in Mathlib. Find a suitable lemma, inspect it with `#check`, and replace `sorry`
with a proof using it. Check which arguments and hypotheses the lemma needs.
-/

theorem mathlib_ex1 (x : ℝ) (hx : 0 ≤ x) : Real.sqrt x ^ 2 = x := by
  exact Real.sq_sqrt hx
  done

theorem mathlib_ex2 (x : ℝ) : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by
  exact Real.cos_sq_add_sin_sq x
  done

theorem mathlib_ex3 (s t : Finset ℕ) : (s ∪ t).card + (s ∩ t).card = s.card + t.card := by
  exact Finset.card_union_add_card_inter s t
  done

theorem mathlib_ex4 (n k : ℕ) (h : k ≤ n) :
    n.choose k * k.factorial * (n - k).factorial = n.factorial := by
  exact Nat.choose_mul_factorial_mul_factorial h
  done

/- There are infinitely many primes: for every `n` there is a prime at least as large as `n`. -/
theorem mathlib_ex5 (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime := by
  exact Nat.exists_infinite_primes n
  done

/-!
## Part 2: stating mathematics in Lean

Knowing how to search is only half of the job: to use Mathlib we also need to *state* things the
way Mathlib does. We start with sets, which we have already met, and then look at a statement from
linear algebra, where the Mathlib formulation is further from the informal one.

### Sets

We already worked with sets in the logic session. Let us now look at what they really are.

In Lean every object has a type, and a set is always a set of elements of a *fixed* type: for a
type `X`, the sets of elements of `X` form the type `Set X`. A set of natural numbers is a
`Set ℕ`, a set of real numbers is a `Set ℝ`, and there is no "set of everything" containing both.

In fact, `Set X` is defined as `X → Prop`: a set is a predicate on `X`. Set-builder notation
`{x : X | ...}` describes the elements satisfying the property after the `|`.
-/

-- The set of even natural numbers, as a `def` so that we can reuse it below.
def Evens : Set ℕ := {n : ℕ | ∃ k, n = k + k}

/- Membership is written `∈` (`\mem`). For a set written as `{x | ...}`, the statement
`a ∈ {x | ...}` *is* the property after the `|`, with `a` in place of `x`, no lemma is needed to
pass from one to the other. So proving `10 ∈ Evens` means proving `∃ k, 10 = k + k`. -/
example : 10 ∈ Evens := by
  use 5
  done

def Reals01 : Set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ 1}

-- A union needs two sets of the same type. Uncomment the line to see the error.
-- #check Evens ∪ Reals01

/- Union `∪` (`\cup`) and intersection `∩` (`\cap`) we already know from the logic session:
membership in `A ∪ B` behaves like `∨`, and membership in `A ∩ B` like `∧`. The corresponding
lemmas are named exactly as Part 1 predicts: -/
#check Set.mem_union
#check Set.mem_inter_iff

/-!
### The empty set and `Set.univ`

The *empty set* is written `∅` (`\empty`), and membership in it is `False`. By the discussion
above there is one empty set *for each type*: `(∅ : Set ℕ)` and `(∅ : Set ℝ)` are two different
objects. They cannot be compared: `=` only compares two elements of the same type, so asking
whether these two empty sets are equal is not even a well-formed question.

At the other extreme, `Set.univ : Set X` is the set of *all* the elements of `X`. Again, one for
each type. Membership in it is trivially true.
-/

#check (∅ : Set ℕ)
#check (∅ : Set ℝ)
-- #check (∅ : Set ℕ) = (∅ : Set ℝ)  -- uncomment to see the error

#check Set.mem_empty_iff_false
#check Set.mem_univ

/-!
### The `ext` tactic

In the logic session we proved that two sets are equal starting with `apply Set.ext` followed by
`intro x`. The tactic `ext x` does both at once: on a goal `A = B` between two sets it introduces
an element `x` and leaves the goal `x ∈ A ↔ x ∈ B`. (It is in fact much more general: `ext`
applies to any goal saying that two objects made of the same pieces are equal — for instance two
functions that agree at every point.)
-/

/- Membership in `A ∪ ∅` is `x ∈ A ∨ x ∈ ∅`, and `x ∈ ∅` is `False`. So in the second case the
hypothesis `hxempty` is a proof of `False`, and `exfalso` followed by `exact hxempty` closes the
goal. -/
example {X : Type*} (A : Set X) : A ∪ ∅ = A := by
  ext x
  constructor
  · intro hx
    rcases hx with hxA | hxempty
    · exact hxA
    · exfalso
      exact hxempty
  · intro hx
    left
    exact hx
  done

/- Two exercises. Remember that membership in `Set.univ` is trivially true (`Set.mem_univ`). Both
are of course in Mathlib, and `exact?` finds them; the point here is to practice `ext`. -/

-- In Mathlib: `Set.inter_univ A`.
theorem mathlib_ex6 {X : Type*} (A : Set X) : A ∩ Set.univ = A := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    constructor
    · exact hx
    · exact Set.mem_univ x
  done

-- In Mathlib: `Set.inter_empty A`.
theorem mathlib_ex7 {X : Type*} (A : Set X) : A ∩ ∅ = ∅ := by
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exfalso
    exact hx
  done

/-!
### A worked example: planes in three-dimensional space

Here is a theorem one might meet in a first-year linear-algebra course: two distinct planes
through the origin in `ℝ³` intersect in a line.

We represent `ℝ³` by `Fin 3 → ℝ`: a vector assigns a real coordinate to each of the three indices.
A linear subspace is a `Submodule`, which packages a set together with its closure properties.
For submodules, `U ≤ W` means inclusion, `U ⊓ W` is intersection, and `U ⊔ W` is their sum
(not their set-theoretic union). Type `⊓` with `\inf` and `⊔` with `\sup`.

We will use `U.spanFinrank`, which takes the submodule directly. For these finite-dimensional
real subspaces it is the minimal number of generators, hence the same dimension. Thus “the
intersection is a line” becomes `(U ⊓ W).spanFinrank = 1`.

Grassmann's formula gives `dim (U ∩ W) ≥ 2 + 2 - 3 = 1`. Since the two planes have the same
dimension but are distinct, their intersection is a proper subspace of `U`, so its dimension is
less than `2`. The tactic `omega` combines these bounds using natural-number arithmetic.

In our Mathlib version the dimension lemmas below use `Module.finrank`. Their `spanFinrank`
versions are short wrappers supplied by `Preliminaries`, already imported above. This is a common
part of formalization: finding a theorem, then adapting it to the representation we chose.
-/

example (U W : Submodule ℝ (Fin 3 → ℝ))
    (hU : U.spanFinrank = 2) (hW : W.spanFinrank = 2) (hne : U ≠ W) :
    (U ⊓ W).spanFinrank = 1 := by
  -- Grassmann's formula.
  have h_grassmann : (U ⊔ W).spanFinrank + (U ⊓ W).spanFinrank = U.spanFinrank + W.spanFinrank :=
    Submodule.spanFinrank_sup_add_spanFinrank_inf_eq U W
  -- `U ⊔ W` is a subspace of `ℝ³`, whose dimension is `3`.
  have h_sup : (U ⊔ W).spanFinrank ≤ Module.finrank ℝ (Fin 3 → ℝ) :=
    Submodule.spanFinrank_le (U ⊔ W)
  have h_three : Module.finrank ℝ (Fin 3 → ℝ) = 3 := Module.finrank_fin_fun ℝ
  -- `U` is not contained in `W`: a subspace of `W` with the same dimension as `W` is `W` itself.
  have h_not_le : ¬ U ≤ W := by
    intro hle
    apply hne
    apply Submodule.eq_of_le_of_spanFinrank_eq hle
    rw [hU, hW]
    done
  -- So `U ⊓ W` is a proper subspace of `U`, and its dimension is smaller.
  have h_lt : U ⊓ W < U := inf_lt_left.mpr h_not_le
  have h_inf : (U ⊓ W).spanFinrank < U.spanFinrank :=
    Submodule.spanFinrank_lt_spanFinrank_of_lt h_lt
  omega
  done

/-!
## Exercises: translating mathematics into Mathlib

Choose statements from subjects you know; the later exercises are a menu, not a required sequence.
Write an `example` expressing each statement, ending with this placeholder proof:

```lean
:= by
  sorry
  done
```

Only formulate the result; leave the proof as `sorry`. First choose the types and structures,
then the hypotheses, then the conclusion. For example, `{R : Type*} [CommRing R]` introduces a
commutative ring. Search for unfamiliar vocabulary and inspect candidate declarations with `#check`.

The difficulty rating concerns Mathlib vocabulary, not proofs. A statement with no errors may
still say the wrong thing: read it back in English and compare its assumptions and conclusion.

In this solutions file, each prompt is followed by one possible idiomatic declaration, and a
comment names the Mathlib result that proves it, found with the tools of Part 1. Complete proofs
are included for reference; participants are only asked to formulate the statements.
-/

/-!
### 1. Difference of squares — difficulty 1/5

The difference-of-squares identity does not depend on working over the real numbers. State it for
two elements of an arbitrary commutative ring.
-/

/- `CommRing` supplies the algebraic operations and laws; the usual notation is overloaded. -/
-- In Mathlib: `sq_sub_sq`, with the two sides exchanged.
example {R : Type*} [CommRing R] (a b : R) :
    (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  exact (sq_sub_sq a b).symm
  done

/-!
### 2. Images and unions — difficulty 1/5

Let `f : X → Y` be a function and let `A` and `B` be subsets of `X`. State that the image of
`A ∪ B` under `f` is the union of the images of `A` and `B`.
-/

/- Mathlib writes the direct image of a set as `f '' A`; unions are still written `∪`. -/
-- In Mathlib: `Set.image_union`.
example {X Y : Type*} (f : X → Y) (A B : Set X) :
    f '' (A ∪ B) = f '' A ∪ f '' B := by
  exact Set.image_union f A B
  done

/-!
### 3. Composition of injections — difficulty 1/5

Let `f : X → Y` and `g : Y → Z` be injective functions. State that `g ∘ f` is injective.
-/

/- Injectivity is a predicate on functions, and `∘` is function composition. -/
-- In Mathlib: `Function.Injective.comp`, used as `hg.comp hf`.
example {X Y Z : Type*} (f : X → Y) (g : Y → Z)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  exact hg.comp hf
  done

/-!
### 4. Units modulo an integer — difficulty 2/5

For natural numbers `a` and `n`, state that the residue class of `a` modulo `n` is invertible if
and only if `a` and `n` are coprime.
-/

/- `ZMod n` is the ring of residues; `IsUnit` means invertible and `Nat.Coprime` means
coprime. -/
-- In Mathlib: `ZMod.isUnit_iff_coprime`.
example (a n : ℕ) : IsUnit (a : ZMod n) ↔ a.Coprime n := by
  exact ZMod.isUnit_iff_coprime a n
  done

/-!
### 5. Monotone functions and intervals — difficulty 2/5

Let `f` be a monotone (nondecreasing) function between ordered sets. State that `f` maps the closed
`[a, b]` into the closed interval `[f(a), f(b)]`.
-/

/- `Set.MapsTo f A B` says that `f` maps `A` into `B`; `Set.Icc` is a closed interval. -/
-- In Mathlib: `Monotone.mapsTo_Icc`.
example {X Y : Type*} [Preorder X] [Preorder Y] (f : X → Y)
    (hf : Monotone f) (a b : X) :
    Set.MapsTo f (Set.Icc a b) (Set.Icc (f a) (f b)) := by
  exact hf.mapsTo_Icc
  done

/-!
### 6. Disjoint metric balls — difficulty 2/5

In a metric space, let `x` and `y` be points and let `r` and `s` be real radii. State that if
`r + s ≤ d(x, y)`, then the open balls with centers `x`, `y` and radii `r`, `s` are disjoint.
-/

/- A `PseudoMetricSpace` is sufficient. Balls are sets, so their disjointness uses the
general predicate `Disjoint`. -/
-- In Mathlib: `Metric.ball_disjoint_ball`.
example {X : Type*} [PseudoMetricSpace X] (x y : X) (r s : ℝ)
    (h : r + s ≤ dist x y) : Disjoint (Metric.ball x r) (Metric.ball y s) := by
  exact Metric.ball_disjoint_ball h
  done

/-!
### 7. A zero between opposite signs — difficulty 2/5

Let a real-valued function be continuous on `[a, b]`, where `a < b`. If `f(a) < 0 < f(b)`, state
that `f` has a zero strictly between `a` and `b`.
-/

/- Continuity restricted to a set is `ContinuousOn`; `Icc` and `Ioo` denote closed and
open intervals. -/
-- In Mathlib: `intermediate_value_Ioo`, stated as `Set.Ioo (f a) (f b) ⊆ f '' Set.Ioo a b`.
example (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    (ha : f a < 0) (hb : 0 < f b) : ∃ c ∈ Set.Ioo a b, f c = 0 := by
  exact intermediate_value_Ioo hab.le hf ⟨ha, hb⟩
  done

/-!
### 8. Counting subsets — difficulty 3/5

Let `X` be a finite set and let `k` be a natural number. State that the number of `k`-element
subsets of `X` is the binomial coefficient “`|X|` choose `k`”.
-/

/- Finite subsets are `Finset`s. The objects being counted form a subtype, whose cardinality
is obtained with `Fintype.card`. -/
-- In Mathlib: `Fintype.card_finset_len`.
example {α : Type*} [Fintype α] [DecidableEq α] (k : ℕ) :
    Fintype.card {s : Finset α // s.card = k} = (Fintype.card α).choose k := by
  exact Fintype.card_finset_len k
  done

/-!
### 9. The handshake lemma — difficulty 3/5

State the handshake lemma for a finite undirected graph without loops or multiple edges: the sum
of the vertex degrees equals twice the number of edges.
-/

/- A loopless undirected graph is `SimpleGraph`. Computing degrees and the edge finset
requires decidable adjacency. -/
-- In Mathlib: `SimpleGraph.sum_degrees_eq_twice_card_edges`.
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : ∑ v, G.degree v = 2 * G.edgeFinset.card := by
  exact G.sum_degrees_eq_twice_card_edges
  done

/-!
### 10. Cauchy's theorem — difficulty 3/5

Let `G` be a finite group and let `p` be a prime dividing the order of `G`. State Cauchy's theorem:
`G` contains an element of order `p`.
-/

/- `Nat.card G` is the cardinality of a finite type, and primality can be supplied as a
`Fact` typeclass. -/
-- In Mathlib: `exists_prime_orderOf_dvd_card'`.
example {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact (Nat.Prime p)]
    (hp : p ∣ Nat.card G) : ∃ g : G, orderOf g = p := by
  exact exists_prime_orderOf_dvd_card' p hp
  done

/-!
### 11. Rank–nullity — difficulty 3/5

Let `V` and `W` be real vector spaces, with `V` finite-dimensional, and let `f : V → W` be linear.
State the rank–nullity formula

`dim(ker f) + dim(im f) = dim V`.
-/

/- Vector spaces are expressed by `AddCommGroup` and `Module`. A linear map's kernel and
range are submodules, and `Module.finrank` is finite dimension. -/
-- In Mathlib: `LinearMap.finrank_range_add_finrank_ker`, with the two summands exchanged.
example {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ V] (f : V →ₗ[ℝ] W) :
    Module.finrank ℝ ↑(LinearMap.ker f) + Module.finrank ℝ ↑(LinearMap.range f) =
      Module.finrank ℝ V := by
  rw [Nat.add_comm]
  exact f.finrank_range_add_finrank_ker
  done

/-!
### 12. The fundamental theorem of algebra — difficulty 3/5

State that every nonconstant polynomial with complex coefficients has a complex root.
-/

/- Polynomial degree takes values in `WithBot ℕ`, and `p.IsRoot z` abbreviates
`p.eval z = 0`. -/
-- In Mathlib: `Complex.exists_root`.
example (p : Polynomial ℂ) (hp : 0 < p.degree) : ∃ z : ℂ, p.IsRoot z := by
  exact Complex.exists_root hp
  done

/-!
### 13. A compact-to-Hausdorff bijection — difficulty 3/5

Let `X` be a compact topological space and `Y` a Hausdorff topological space. State that every
continuous bijection from `X` to `Y` is a homeomorphism.
-/

/- Compactness and the Hausdorff property are typeclasses. The conclusion is the predicate
`IsHomeomorph f`, not the bundled type `Homeomorph X Y`. -/
-- In Mathlib: `isHomeomorph_iff_continuous_bijective`.
example {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
    [T2Space Y] (f : X → Y) (hf : Continuous f) (hbij : Function.Bijective f) :
    IsHomeomorph f := by
  exact isHomeomorph_iff_continuous_bijective.mpr ⟨hf, hbij⟩
  done

/-!
### 14. The contraction mapping theorem — difficulty 3/5

Let `X` be a nonempty complete metric space and let `f : X → X` be a contraction whose contraction
constant is strictly less than one. State that `f` has a unique fixed point.
-/

/- A contraction constant is a nonnegative real. `ContractingWith` includes the strict
bound by one, while `Function.IsFixedPt` expresses the fixed-point equation. -/
-- In Mathlib: the fixed point is `ContractingWith.fixedPoint`, and
-- `ContractingWith.fixedPoint_isFixedPt` and `ContractingWith.fixedPoint_unique` give existence
-- and uniqueness.
example {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (K : NNReal) (f : X → X) (hf : ContractingWith K f) :
    ∃! x, Function.IsFixedPt f x := by
  refine ⟨ContractingWith.fixedPoint f hf, hf.fixedPoint_isFixedPt, ?_⟩
  intro x hx
  exact hf.fixedPoint_unique hx
  done

/-!
### 15. Continuity of measure from below — difficulty 3/5

Let `(Aₙ)` be an increasing sequence of measurable sets in a measure space. State that the
measures of the `Aₙ` tend to the measure of their union.
-/

/- An increasing sequence of sets is simply a `Monotone` function. Convergence is stated
with filters, and a countable union is written `⋃ n, A n`. -/
-- In Mathlib: `MeasureTheory.tendsto_measure_iUnion_atTop`, which does not even need measurability.
example {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A) :
    Filter.Tendsto (μ ∘ A) Filter.atTop (nhds (μ (⋃ n, A n))) := by
  exact MeasureTheory.tendsto_measure_iUnion_atTop hmono
  done

/-!
### 16. The Chinese remainder theorem — difficulty 4/5

Let `I` and `J` be comaximal ideals of a commutative ring `R`. State the two-ideal Chinese
remainder theorem: `R / (I ∩ J)` is isomorphic as a ring to `(R / I) × (R / J)`.
-/

/- Ideals form a lattice, so their intersection is `I ⊓ J`. Quotient rings and ring
isomorphisms are written `R ⧸ I` and `≃+*`; `Nonempty` asserts existence. -/
-- In Mathlib: `Ideal.quotientInfEquivQuotientProd`.
example {R : Type*} [CommRing R] (I J : Ideal R) (h : IsCoprime I J) :
    Nonempty ((R ⧸ (I ⊓ J)) ≃+* (R ⧸ I) × (R ⧸ J)) := by
  exact ⟨Ideal.quotientInfEquivQuotientProd I J h⟩
  done

/-!
### 17. The Cayley–Hamilton theorem — difficulty 4/5

Let `A` be a square matrix whose rows and columns are indexed by a finite set and whose entries lie
in a commutative ring. State that substituting `A` into its characteristic polynomial gives the
zero matrix.
-/

/- A square matrix uses the same finite index type twice. `Polynomial.aeval A` evaluates a
polynomial at the matrix `A`, in the matrix algebra over `R`. -/
-- In Mathlib: `Matrix.aeval_self_charpoly`.
example {R ι : Type*} [CommRing R] [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι R) : Polynomial.aeval A A.charpoly = 0 := by
  exact Matrix.aeval_self_charpoly A
  done

/-!
### 18. A finite form of Carathéodory's theorem — difficulty 4/5

Let `S` be a subset of a real vector space and let `x` belong to the convex hull of `S`. State that
`x` lies in the convex hull of some finite affinely independent subset of `S`.
-/

/- The coercions turn a `Finset` into a set and its elements into vectors.
`AffineIndependent` is applied to the inclusion of the finite subtype. -/
-- In Mathlib: `convexHull_eq_union`.
example {E : Type*} [AddCommGroup E] [Module ℝ E] (s : Set E) (x : E)
    (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset E, ↑t ⊆ s ∧ AffineIndependent ℝ ((↑) : t → E) ∧
      x ∈ convexHull ℝ (t : Set E) := by
  rw [convexHull_eq_union] at hx
  simpa only [Set.mem_iUnion, exists_prop] using hx
  done

/-!
### 19. Liouville's theorem — difficulty 4/5

State Liouville's theorem: a complex-differentiable function from `ℂ` to `ℂ` whose range is
bounded is constant.
-/

/- Complex differentiability is `Differentiable ℂ f`. Boundedness is phrased in the
bornology of the range, and a constant function is `Function.const`. -/
-- In Mathlib: `Differentiable.exists_eq_const_of_bounded`.
example (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hb : Bornology.IsBounded (Set.range f)) :
    ∃ c : ℂ, f = Function.const ℂ c := by
  exact hf.exists_eq_const_of_bounded hb
  done

/-!
### 20. Chebyshev's inequality — difficulty 4/5

Let `X` be a square-integrable real random variable on a probability space and let `c > 0`. State
that the probability that `|X - E[X]|` is at least `c` is at most `Var(X) / c²`.
-/

/- The probability-space assumption is a typeclass. `MemLp X 2 μ` expresses square
integrability; expectation is an integral, while measures take values in `ℝ≥0∞`. -/
-- In Mathlib: `ProbabilityTheory.meas_ge_le_variance_div_sq`.
example {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MeasureTheory.MemLp X 2 μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ |X ω - ∫ x, X x ∂μ|} ≤
      ENNReal.ofReal (ProbabilityTheory.variance X μ / c ^ 2) := by
  exact ProbabilityTheory.meas_ge_le_variance_div_sq hX hc
  done
