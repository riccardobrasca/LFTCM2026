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

Everything in section 1 and section 2 works offline. The commands of sections 3, 4 and 5 send your
query to a server, so they need an internet connection: they run when Lean elaborates the line, and
the answers appear in the Infoview when you put the cursor on it. Clicking on an answer replaces
the query by it. If one of them shows a red `Could not contact ... server` instead, the server was
just slow to answer: it is not a mistake in the file. Edit the line, or choose `Restart File` in
the `∀` menu, to send the query again.
-/

/-!
### 1. Guessing the name

Names in Mathlib are not chosen at random: they *describe the statement*, read from left to right.
Each ingredient contributes a word:

* operations: `add`, `sub`, `mul`, `div`, `neg`, `inv`, `pow`, `abs`, `sqrt`, ...;
* relations: `eq`, `le`, `lt`, `ne`, `dvd`, `mem`, `subset`, ...;
* qualifiers: `comm`, `assoc`, `left`, `right`, `self`, `cancel`, `zero`, `one`, `nonneg`, `pos`,
  ...

Types and structures are `UpperCamelCase` (`Finset`, `Continuous`, `LinearIndependent`), everything
else is `lower_snake_case`, and results about `Foo` live in the namespace `Foo`, so their full name
is `Foo.bar`. The convention is documented at
<https://leanprover-community.github.io/contribute/naming.html>.

`#check` prints the statement attached to a name.
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

Lean can search its own library. These are search *tools*, not proof steps: they are slow, so once
you have the answer, click on the suggestion in the Infoview to replace the tactic by it.
-/

/- `exact?` looks for a single lemma, applied to the hypotheses, that closes the goal. -/
example (a b c : ℤ) : a - b + c = a + (c - b) := by
  exact?
  done

example (n : ℕ) : 0 < n ! := by
  exact?
  done

/- A continuous function on a compact set attains its minimum. In Mathlib the conclusion is
written with `IsMinOn`: `IsMinOn f s x` says that `f x ≤ f y` for every `y ∈ s`.

Here `exact?` fails, and it is right to: as stated, the statement is false for `s` empty. Note that
the error message suggests trying `apply?`. -/
example {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  exact?
  done

/- `apply?` also lists the lemmas that close the goal *up to* some hypotheses. The list is long,
but it contains `refine IsCompact.exists_isMinOn hs ?_ hf`, with `s.Nonempty` as the remaining
goal: the assumption our statement was missing. A search that fails is informative too.

`apply?` applies nothing itself: after printing the list it closes the goal with `sorry`, which is
why this example carries a warning, and why writing `sorry` after it would be an error. -/
example {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  apply?
  done

/- With the assumption in place, `exact?` closes the goal immediately. -/
example {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ} (hs : IsCompact s)
    (hne : s.Nonempty) (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  exact?
  done

/- `simp?` behaves like `simp` and prints the lemmas it used. It is the fastest way to learn the
names of the elementary simplification lemmas. -/
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

/- The answer to the previous query, used. Mathlib states it for a sum over
`Finset.range n = {0, ..., n - 1}`, so we apply it to `n + 1` and tidy up the result. -/
example (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) / 2 := by
  rw [Finset.sum_range_id]
  grind
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

#leansearch "A linearly independent family is smaller than the dimension of the space."

#loogle LinearIndependent, Module.finrank

/- Both give `LinearIndependent.fintype_card_le_finrank`. -/
#check LinearIndependent.fintype_card_le_finrank

example {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] (v : ι → V) (hv : LinearIndependent K v) :
    Fintype.card ι ≤ Module.finrank K V := by
  exact hv.fintype_card_le_finrank
  done

/-!
### Exercises

Each of the following is in Mathlib. Find its name and replace the `sorry` by it.
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

The fundamental way to write a set is the set-builder notation `{x : X | ...}`: the set of the
elements of `X` satisfying the property written after the `|`.
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

-- `Evens : Set ℕ` and `Reals01 : Set ℝ` have different types, so they cannot interact: their
-- union is not a well-formed expression. Uncomment the line to see the error.
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

The statement looks quite different in Mathlib. A vector of `ℝ³` is a function `Fin 3 → ℝ`, and a
linear subspace is a `Submodule`. The intersection of two subspaces is written `⊓` and their sum
`⊔`. The dimension is the delicate point, and realizing which notion to use is the real difficulty
here: `Module.finrank` takes a *type*, so applying it to a submodule means coercing the
submodule to the type of its elements first. What measures the submodule itself, with no coercion,
is `Submodule.spanFinrank`, the minimal number of generators.
So “the intersection is a line” becomes `(U ⊓ W).spanFinrank = 1`.

The proof is the familiar dimension argument. Grassmann's formula gives
`dim (U ∩ W) ≥ 2 + 2 - 3 = 1`, and since `U ≠ W` the intersection is a proper subspace of `U`, so
`dim (U ∩ W) < 2`. For `ℝ³` itself, a type rather than a submodule, the dimension is again
`Module.finrank`. Every Mathlib lemma used below can be found with the tools of Part 1, and the
natural-number arithmetic is left to `omega`.

Mathlib states those dimension lemmas for `Module.finrank` only, so the `spanFinrank` versions we
need are missing. This is what usually happens when one formalizes something: on the way one runs
into a few trivial lemmas that nobody has written yet. Here they are proved in
`LFTCM2026/Preliminaries/SpanFinrank.lean`.
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
    exact Submodule.eq_of_le_of_spanFinrank_eq hle (by rw [hU, hW])
  -- So `U ⊓ W` is a proper subspace of `U`, and its dimension is smaller.
  have h_lt : U ⊓ W < U := inf_lt_left.mpr h_not_le
  have h_inf : (U ⊓ W).spanFinrank < U.spanFinrank :=
    Submodule.spanFinrank_lt_spanFinrank_of_lt h_lt
  omega
  done

/-!
## Exercises: translating mathematics into Mathlib

For each exercise, write a Lean declaration which expresses the English statement. The aim is
only to formulate the result: finish the declaration with a proof such as `by sorry done` and do
not try to prove it. You may use everything imported by `Mathlib`.

The difficulty rating concerns finding the right Mathlib vocabulary, not proving the theorem.
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

Let `f` be an increasing function between two ordered sets. State that `f` maps the closed interval
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
