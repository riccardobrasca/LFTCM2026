/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

module

import LFTCM2026.Preliminaries

/-!
# Advanced tactics

The tactics introduced in the first two lectures are already sufficient
to prove any (true) theorem in Lean. But there are a few more standard tactics that
will make our lives significantly easier. These are usually tactics performing
well-specified steps automatically. In this lecture, we will learn about:

* `simp`: simplification
* `ring`: proving algebraic identities
* `obtain`, `use`: working with existentials
* `induction`: proof by induction
* `congr`, `gcongr`, `grw`: congruence and generalised rewriting

As before, move the cursor line by line and watch the goal in the Infoview.
-/

/-!
## The `simp` tactic

The tactic `simp` applies simplification lemmas. These are lemmas registered in a global
simplification database. Examples of such simplification lemmas are `x + 0 = x` or
`A ∪ Set.univ = Set.univ`. `simp` repeatedly applies simplification lemmas to the goal by
rewriting with the lemma from left to right or by closing the goal directly. It stops when none
applies any more.
-/

example (x : ℝ) (hx : x = 5) : x + 0 = 5 := by
  simp
  exact hx
  done

/- To see which lemmas were applied by `simp`, use `simp?`: -/
example (x : ℝ) : x + 0 = x := by
  simp?
  done

/- Nothing about `simp` is specific to arithmetic: the simp set covers the whole library. -/
example (l : List ℕ) (hl : l.length = 42) : (l ++ []).length = l.length := by
  simp
  done

/- Here is an example where a simplification lemma closes the goal directly. -/
example {X : Type*} (A B : Set X) : A ∩ B ⊆ A := by
  simp
  done

/- `simp at h` simplifies the hypothesis `h` instead of the goal, and `simp at h ⊢` does both. -/
example (x y : ℝ) (h : x + 0 ≤ y * 1) : x ≤ y := by
  simp at h
  exact h
  done

/- Extra lemmas can be handed to `simp` in a list, and a hypothesis is a lemma like any other:
`simp [h]` also rewrites with `h`. -/
example (f : ℕ → ℕ) (n : ℕ) (h : ∀ m, f m = m + 1) : f (n + 0) = n + 1 := by
  simp [h]
  done

/-!
## `simp?` and `simp only`

`simp` is convenient but opaque: the proof it produces depends on the whole simp set, which grows
with every Mathlib release, so a proof that works today may break tomorrow, and while reading it
you cannot tell what happened.

`simp?` runs `simp` and prints the lemmas it actually used, as a `simp only [...]` call. Click the
suggestion in the Infoview to replace `simp?` by it. `simp only [l₁, ..., lₙ]` behaves like `simp`
but uses only the listed lemmas.
-/

/- The same proof after clicking it. -/
example {X : Type*} (A : Set X) : A ∩ Set.univ = A := by
  simp only [Set.inter_univ]
  done

/- `simp?` works at a hypothesis too. -/
example (x y : ℝ) (h : x + 0 ≤ y * 1) : x ≤ y := by
  simp only [add_zero, mul_one] at h
  exact h
  done

/- Some simplification lemmas are not enabled by default, but are available as named collections
of lemmas (`simp`-sets). Here we use `parity_simps`, a set of `simp` lemmas for parity goals. -/
example (n : ℕ) : Even (n * (n + 1)) := by
  by_cases h : Even n
  · simp [h]
  · simp [parity_simps, h]
  done

/-!
## The `ring` tactic

`simp` is a simplifier, not a prover. To ensure that `simp` terminates, only lemmas
that make the term "simpler" are registered as simplification lemmas. This is
not the case for distributional lemmas, like `(x + y) * z = x * z + y * z`. To
prove algebraic identities valid in any commutative ring, we can use the `ring` tactic
instead. It applies an algorithm to normalise the two sides of an equality in a
deterministic way and closes the goal if these normal forms agree.
-/

example (x y : ℝ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
  done

/- The ring can be any commutative ring, not just `ℝ`. -/
example {R : Type*} [CommRing R] (a b : R) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring
  done

/- `ℕ` is not a ring (there are no negatives) but `ring` also handles identities that hold in
every commutative *semi*ring, which is what `ℕ` is. (Careful with `-` on `ℕ`: it is truncated
subtraction, `3 - 5 = 0`, so `a - b + b = a` is false there and `ring` will not prove it.) -/
example (n : ℕ) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
  ring
  done

/- `ring` does not use hypotheses, so we need to apply them first. -/
example (a b : ℝ) (h : a = 2 * b) : a ^ 2 + b ^ 2 = 5 * b ^ 2 := by
  rw [h]
  ring
  done

/- While `ring` either closes the goal or fails, `ring_nf` ("ring normal form") normalises
algebraic terms, not necessarily closing the goal. It also works `at` a hypothesis. -/
example (x : ℝ) (h : (x + 1) * (x - 1) = 0) : x ^ 2 - 1 = 0 := by
  ring_nf at h ⊢
  exact h
  done

/- A longer example. `simp [h]` replaces every `f n` by `x ^ n` and computes `x ^ 1` and `x ^ 0`,
`ring` proves the identity that is left. -/
example (f : ℕ → ℝ) (x : ℝ) (h : ∀ n, f n = x ^ n) : f 2 + 2 * f 1 + f 0 = (x + 1) ^ 2 := by
  simp [h]
  ring
  done

/-!
## Existential statements: `use` and `obtain`

To prove `∃ x, P x` one exhibits a witness: `use a` replaces the goal by `P a`. To use a
hypothesis `h : ∃ x, P x` one gives the object a name: `obtain ⟨a, ha⟩ := h` puts `a` and
`ha : P a` in the context. The brackets `⟨ ⟩` are typed `\<` and `\>`.

`obtain ⟨a, ha⟩ := h` is the same tactic as `rcases h with ⟨a, ha⟩` from the logic lecture, written
the other way round, and it takes apart conjunctions just as well: `obtain ⟨h1, h2⟩ := h` splits
`h : P ∧ Q` into its two halves.
-/

example (x : ℝ) : ∃ y : ℝ, x + y = 0 := by
  use -x
  ring
  done

/- After `use 7` the goal `7 * 7 = 49` is closed by `use` itself, which tries a few
tactics to finish the goal, here `rfl`. -/
example : ∃ n : ℕ, n * n = 49 := by
  use 7
  done

/- Several witnesses at once, for nested existentials. -/
example : ∃ a b : ℕ, a + b = 10 := by
  use 4, 6
  done

/- Divisibility is an existential statement: `a ∣ b` (type `∣` as `\|`, it is *not* the bar on
your keyboard) means `∃ c, b = a * c`. So we can use `obtain` and `use` as before. -/
example (a b c : ℤ) (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  use k * l
  rw [hl, hk]
  ring
  done

/- `Even n` is `∃ r, n = r + r`, and behaves the same way. -/
example (n m : ℕ) (h : Even n) : Even (n * m) := by
  obtain ⟨k, hk⟩ := h
  use k * m
  rw [hk]
  ring
  done

/-!
## Proofs by induction

Every natural number is either `0` or of the form `n + 1`, and this is what a proof by induction
uses. The tactic is

```
induction n with
| zero => ...
| succ n ih => ...
```

It produces two goals: the statement for `0`, and the statement for `n + 1` given `ih`, the
statement for `n`.
-/

/- Little Gauss: `0 + 1 + ... + n = n * (n + 1) / 2`. We state it multiplied by `2`, to stay inside
`ℕ` where division is not what one wants.

The sum `∑` symbol is typed using `\sum`. `∑ i ∈ Finset.range (n + 1), i` is the sum
`0 + 1 + ... + n`. `Finset.range (n + 1)` is the (finite) set of numbers `{0, ..., n}`.
-/
theorem two_mul_sum_range (n : ℕ) : 2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero =>
    -- Case `n = 0`
    simp
  | succ n ih =>
    -- Case `n + 1`
    -- Split off the last term, distribute the `2`, and the induction hypothesis applies.
    rw [Finset.sum_range_succ, mul_add, ih]
    ring
  done

/- The two lemmas we have used in the above proof are: -/

-- The empty sum is `0`.
#check Finset.sum_range_zero

-- One more term: `∑ i ∈ range (n + 1), f i = ∑ i ∈ range n, f i + f n`.
#check Finset.sum_range_succ

/- The same shape of proof: the sum of the first `n` odd numbers is `n ^ 2`. -/
example (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring
  done

/-!
## `congr`

`congr` applies congruence rules to work backwards from a goal like `f a = f b`: since the two
sides are the same function applied to different arguments, it suffices to prove `a = b`.
`congr n` applies up to `n` congruence steps.
-/

example (f : ℕ → ℕ) (a b : ℕ) : f (a + b) = f (b + a) := by
  congr 1
  ring
  done

/- Here `congr` applies two steps, producing unprovable goals `a = b` and `b = a`. -/
example (f : ℕ → ℕ) (a b : ℕ) : f (a + b) = f (b + a) := by
  congr 2
  -- both goals not provable
  · sorry
  · sorry

/- `congr` closes with `assumption` the goals it can, so it may finish on its own. -/
example {X : Type*} (A B C : Set X) (h : B = C) : A ∪ B = A ∪ C := by
  congr 1
  done

/-!
## `gcongr`

`gcongr` is the same idea for inequalities and more generally for relations. To prove
`a + c ≤ b + d` it is enough to prove `a ≤ b` and `c ≤ d`, because `+` is monotone in both
arguments.
-/

example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  gcongr
  done

/- Here `gcongr` needs `0 ≤ x` to go from `x ≤ y` to `x ^ n ≤ y ^ n`, and finds it in the
context. -/
example (x y : ℝ) (n : ℕ) (hx : 0 ≤ x) (h : x ≤ y) : x ^ n ≤ y ^ n := by
  gcongr
  done

/-!
## `grw`

`grw` ("generalized rewrite") is `rw` for inequalities (more generally relations): given
`h : a ≤ b` it replaces `a` by `b` in the goal, provided the replacement makes the goal
stronger.
-/

example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by
  grw [h]
  done

example (x y : ℝ) (h : x ≤ y) (h3 : y ≤ 3) : x ≤ 3 := by
  grw [h]
  exact h3
  done

/-!
## Rewriting under a binder

`rw` does not rewrite in terms with bound variables. For example, in
`∑ i ∈ Finset.range n, f i * 1` the `i` is bound by the `∑`, so `rw` fails.
-/

example (n : ℕ) (f : ℕ → ℝ) : ∑ i ∈ Finset.range n, f i * 1 = ∑ i ∈ Finset.range n, f i := by
  rw [mul_one]
  done

/- One option is to use `simp` or `simp only`, which rewrite under binders. -/
example (n : ℕ) (f : ℕ → ℝ) : ∑ i ∈ Finset.range n, f i * 1 = ∑ i ∈ Finset.range n, f i := by
  simp only [mul_one]
  done

/- More similar to `rw` is `simp_rw [h₁, ..., hₙ]`, while still rewriting under binders. -/
example (f : ℕ → ℝ) (h : ∀ n, f n = 2 * n) (s : Finset ℕ) :
    ∑ i ∈ s, f i = 2 * ∑ i ∈ s, (i : ℝ) := by
  simp_rw [h]
  rw [Finset.mul_sum]
  done

/- `simp_rw` also differs from `rw` in how often it rewrites. Here `rw [h]` fixes `n := 1` at the
first match and leaves `f 2` alone, while `simp_rw [h]` rewrites both. -/
example (f : ℕ → ℕ) (h : ∀ n, f n = n + 1) : f 1 + f 2 = 5 := by
  simp_rw [h]
  done

/-!
## A longer example

`5 ^ n - 1` is divisible by `4`, by induction on `n`. The proof uses most of this lecture:
`induction` for the structure, `obtain` and `use` for the divisibility, `rw` and `ring` for the
computation. On paper: if `5 ^ n = 4 k + 1`, then `5 ^ (n + 1) = 5 (4 k + 1) = 4 (5 k + 1) + 1`.
-/

example (n : ℕ) : (4 : ℤ) ∣ 5 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih
    -- `eq_add_of_sub_eq : a - b = c → a = c + b`, applied to `hk : 5 ^ n - 1 = 4 * k`.
    have h : (5 : ℤ) ^ n = 4 * k + 1 := eq_add_of_sub_eq hk
    use 5 * k + 1
    rw [pow_succ, h]
    ring
  done

/-!
## Exercises

The tactics of this lecture are `simp`, `simp?`, `simp only`, `ring`, `ring_nf`, `use`, `obtain`,
`induction`, `congr`, `gcongr`, `grw` and `simp_rw`; those of the first two are still available.

As before, replace each `sorry` by a proof.
-/

/- Simplification. -/

theorem adv_ex_1 {X : Type*} (A B : Set X) : (A ∩ B) ∪ A = A := by
  sorry
  done

theorem adv_ex_2 {X : Type*} (A B : Set X) (h : A ⊆ B) : A ∪ B = B := by
  sorry
  done

/- Hint: `pow_two a : a ^ 2 = a * a`. -/
theorem adv_ex_3 (x y : ℝ) (h : x ^ 2 + 0 = 4) (hy : y = x * x) : y = 4 := by
  sorry
  done

theorem adv_ex_4 (n : ℕ) (f : ℕ → ℕ) (h : ∀ m, f m = 2 * m) : f (n * 1) = 2 * n := by
  sorry
  done

theorem adv_ex_5 (x y : ℝ) (h : x * 1 + 0 ≤ y) : x ≤ y := by
  sorry
  done

/- Solve this one with `simp?`, then replace the tactic by the `simp only` it suggests. -/
theorem adv_ex_6 (l : List ℕ) : (l ++ []).length = l.length := by
  sorry
  done

/- Ring identities. -/

theorem adv_ex_7 (x y : ℝ) : (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  sorry
  done

theorem adv_ex_8 {R : Type*} [CommRing R] (a b : R) : (a - b) ^ 2 = (b - a) ^ 2 := by
  sorry
  done

theorem adv_ex_9 (a b : ℝ) (h1 : a + b = 5) (h2 : a - b = 1) : a ^ 2 - b ^ 2 = 5 := by
  sorry
  done

theorem adv_ex_10 (x y : ℝ) (h1 : x + y = 3) (h2 : x * y = 2) : x ^ 3 + y ^ 3 = 9 := by
  sorry
  done

theorem adv_ex_11 (x y : ℝ) (h : x = y + 1) : x ^ 2 = y ^ 2 + 2 * y + 1 := by
  sorry
  done

theorem adv_ex_12 (x : ℝ) (h : x ^ 2 = 2) : x ^ 4 = 4 := by
  sorry
  done

/- Existential statements. -/

theorem adv_ex_13 : ∃ n : ℕ, n ^ 2 = 144 := by
  sorry
  done

theorem adv_ex_14 : ∀ y : ℝ, ∃ x : ℝ, 2 * x + 1 = y := by
  sorry
  done

theorem adv_ex_15 (a b : ℤ) (h : a ∣ b) : a ∣ 3 * b := by
  sorry
  done

theorem adv_ex_16 (h : ∃ x : ℝ, x ^ 2 = 2) : ∃ x : ℝ, 2 * x ^ 2 = 4 := by
  sorry
  done

theorem adv_ex_17 (n m : ℕ) (h : Even n) (h' : Even m) : Even (n + m) := by
  sorry
  done

/- Induction. -/

/- Hint: `add_right_comm a b c : a + b + c = a + c + b` puts the `+ 1` back where the induction
hypothesis expects it. -/
theorem adv_ex_18 (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i + 1 = 2 ^ n := by
  sorry
  done

/- The sum of the first squares, again multiplied by a constant to stay inside `ℕ`. -/
theorem adv_ex_19 (n : ℕ) :
    6 * ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  sorry
  done

/- Nicomachus' theorem: the sum of the first cubes is the square of the sum of the first numbers. -/
theorem adv_ex_20 (n : ℕ) : 4 * ∑ i ∈ Finset.range (n + 1), i ^ 3 = (n * (n + 1)) ^ 2 := by
  sorry
  done

/- The same proof as the longer example above, with different numbers. -/
theorem adv_ex_21 (n : ℕ) : (3 : ℤ) ∣ 4 ^ n - 1 := by
  sorry
  done

/- Congruence and monotonicity. -/

theorem adv_ex_22 (f : ℕ → ℕ) (a b : ℕ) : f (a * b) = f (b * a) := by
  sorry
  done

theorem adv_ex_23 (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : a ≤ b) (h2 : c ≤ d) :
    a * c ≤ b * d := by
  sorry
  done

theorem adv_ex_24 (a b c : ℝ) (hc : 0 ≤ c) (h : a ≤ b) : c * a ≤ c * b := by
  sorry
  done

/- Under a binder. -/

theorem adv_ex_25 (f g : ℕ → ℝ) (h : ∀ n, f n = g n * 1) (s : Finset ℕ) :
    ∑ i ∈ s, f i = ∑ i ∈ s, g i := by
  sorry
  done
