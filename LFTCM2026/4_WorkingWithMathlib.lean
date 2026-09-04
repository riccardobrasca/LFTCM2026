/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import Mathlib
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

Here the error is intentional: the statement is false when `s` is empty. The error message suggests
trying `apply?`. In general, a failed search does *not* mean that the statement is false. -/
example {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  exact?
  done

/- `apply?` also lists the lemmas that close the goal *up to* some hypotheses. The list is long,
but it contains `refine IsCompact.exists_isMinOn hs ?_ hf`, with `s.Nonempty` as the remaining
goal: the assumption our statement was missing. A search that fails is informative too.

Here `apply?` admits the goal with `sorry` after printing its partial suggestions. This is not a
completed proof: choose a suggestion and prove its remaining goals. -/
example {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  apply?
  done

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
grind
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
  sorry
  done

theorem mathlib_ex2 (x : ℝ) : Real.cos x ^ 2 + Real.sin x ^ 2 = 1 := by
  sorry
  done

theorem mathlib_ex3 (s t : Finset ℕ) : (s ∪ t).card + (s ∩ t).card = s.card + t.card := by
  sorry
  done

theorem mathlib_ex4 (n k : ℕ) (h : k ≤ n) :
    n.choose k * k.factorial * (n - k).factorial = n.factorial := by
  sorry
  done

/- There are infinitely many primes: for every `n` there is a prime at least as large as `n`. -/
theorem mathlib_ex5 (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime := by
  sorry
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

theorem mathlib_ex6 {X : Type*} (A : Set X) : A ∩ Set.univ = A := by
  sorry
  done

theorem mathlib_ex7 {X : Type*} (A : Set X) : A ∩ ∅ = ∅ := by
  sorry
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
-/

/-!
### 1. Difference of squares — difficulty 1/5

The difference-of-squares identity does not depend on working over the real numbers. State it for
two elements of an arbitrary commutative ring.
-/

-- Write your Lean statement here. (Exercise 1)

/-!
### 2. Images and unions — difficulty 1/5

Let `f : X → Y` be a function and let `A` and `B` be subsets of `X`. State that the image of
`A ∪ B` under `f` is the union of the images of `A` and `B`.
-/

-- Write your Lean statement here. (Exercise 2)

/-!
### 3. Composition of injections — difficulty 1/5

Let `f : X → Y` and `g : Y → Z` be injective functions. State that `g ∘ f` is injective.
-/

-- Write your Lean statement here. (Exercise 3)

/-!
### 4. Units modulo an integer — difficulty 2/5

For natural numbers `a` and `n`, state that the residue class of `a` modulo `n` is invertible if
and only if `a` and `n` are coprime.
-/

-- Write your Lean statement here. (Exercise 4)

/-!
### 5. Monotone functions and intervals — difficulty 2/5

Let `f` be a monotone (nondecreasing) function between ordered sets. State that `f` maps the closed
`[a, b]` into the closed interval `[f(a), f(b)]`.
-/

-- Write your Lean statement here. (Exercise 5)

/-!
### 6. Disjoint metric balls — difficulty 2/5

In a metric space, let `x` and `y` be points and let `r` and `s` be real radii. State that if
`r + s ≤ d(x, y)`, then the open balls with centers `x`, `y` and radii `r`, `s` are disjoint.
-/

-- Write your Lean statement here. (Exercise 6)

/-!
### 7. A zero between opposite signs — difficulty 2/5

Let a real-valued function be continuous on `[a, b]`, where `a < b`. If `f(a) < 0 < f(b)`, state
that `f` has a zero strictly between `a` and `b`.
-/

-- Write your Lean statement here. (Exercise 7)

/-!
### 8. Counting subsets — difficulty 3/5

Let `X` be a finite set and let `k` be a natural number. State that the number of `k`-element
subsets of `X` is the binomial coefficient “`|X|` choose `k`”.
-/

-- Write your Lean statement here. (Exercise 8)

/-!
### 9. The handshake lemma — difficulty 3/5

State the handshake lemma for a finite undirected graph without loops or multiple edges: the sum
of the vertex degrees equals twice the number of edges.
-/

-- Write your Lean statement here. (Exercise 9)

/-!
### 10. Cauchy's theorem — difficulty 3/5

Let `G` be a finite group and let `p` be a prime dividing the order of `G`. State Cauchy's theorem:
`G` contains an element of order `p`.
-/

-- Write your Lean statement here. (Exercise 10)

/-!
### 11. Rank–nullity — difficulty 3/5

Let `V` and `W` be real vector spaces, with `V` finite-dimensional, and let `f : V → W` be linear.
State the rank–nullity formula

`dim(ker f) + dim(im f) = dim V`.
-/

-- Write your Lean statement here. (Exercise 11)

/-!
### 12. The fundamental theorem of algebra — difficulty 3/5

State that every nonconstant polynomial with complex coefficients has a complex root.
-/

-- Write your Lean statement here. (Exercise 12)

/-!
### 13. A compact-to-Hausdorff bijection — difficulty 3/5

Let `X` be a compact topological space and `Y` a Hausdorff topological space. State that every
continuous bijection from `X` to `Y` is a homeomorphism.
-/

-- Write your Lean statement here. (Exercise 13)

/-!
### 14. The contraction mapping theorem — difficulty 3/5

Let `X` be a nonempty complete metric space and let `f : X → X` be a contraction whose contraction
constant is strictly less than one. State that `f` has a unique fixed point.
-/

-- Write your Lean statement here. (Exercise 14)

/-!
### 15. Continuity of measure from below — difficulty 3/5

Let `(Aₙ)` be an increasing sequence of measurable sets in a measure space. State that the
measures of the `Aₙ` tend to the measure of their union.
-/

-- Write your Lean statement here. (Exercise 15)

/-!
### 16. The Chinese remainder theorem — difficulty 4/5

Let `I` and `J` be comaximal ideals of a commutative ring `R`. State the two-ideal Chinese
remainder theorem: `R / (I ∩ J)` is isomorphic as a ring to `(R / I) × (R / J)`.
-/

-- Write your Lean statement here. (Exercise 16)

/-!
### 17. The Cayley–Hamilton theorem — difficulty 4/5

Let `A` be a square matrix whose rows and columns are indexed by a finite set and whose entries lie
in a commutative ring. State that substituting `A` into its characteristic polynomial gives the
zero matrix.
-/

-- Write your Lean statement here. (Exercise 17)

/-!
### 18. A finite form of Carathéodory's theorem — difficulty 4/5

Let `S` be a subset of a real vector space and let `x` belong to the convex hull of `S`. State that
`x` lies in the convex hull of some finite affinely independent subset of `S`.
-/

-- Write your Lean statement here. (Exercise 18)

/-!
### 19. Liouville's theorem — difficulty 4/5

State Liouville's theorem: a complex-differentiable function from `ℂ` to `ℂ` whose range is
bounded is constant.
-/

-- Write your Lean statement here. (Exercise 19)

/-!
### 20. Chebyshev's inequality — difficulty 4/5

Let `X` be a square-integrable real random variable on a probability space and let `c > 0`. State
that the probability that `|X - E[X]|` is at least `c` is at most `Var(X) / c²`.
-/

-- Write your Lean statement here. (Exercise 20)
