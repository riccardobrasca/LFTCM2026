/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

module

public import LFTCM2026.Preliminaries

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
* `grind`: general purpose automation

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

/- `simp` normalises the goal to `x = 5`. -/
example (x : ℝ) (hx : x = 5) : x * 1 + 0 = 5 := by
  simp
  exact hx
  done

/- To see which lemmas were applied by `simp`, use `simp?`. -/
example (l : List ℕ) (h : l.length = 42) : (l ++ []).length + 0 = 42 := by
  simp?
  exact h
  done

/- `simp at h` simplifies the hypothesis `h` instead of the goal, and `simp at h ⊢` does both.
Here it turns `hx : x ∈ A ∩ B` into a conjunction. -/
example {X : Type*} (A B C : Set X) (h : A ⊆ C) : A ∩ B ⊆ C := by
  intro x hx
  simp at hx
  apply h
  exact hx.left
  done

/- Extra lemmas or hypotheses can be handed to `simp` in a list. With `h` in the list, `simp`
rewrites `f a = f b` into `a = b`. -/
example (f : ℕ → ℕ) (h : ∀ m, f m = m + 1) (a b : ℕ) (hab : f a = f b) : a = b := by
  simp [h] at hab
  exact hab
  done

/-!
## `simp only`

To restrict to specific simplification lemmas, use `simp only [...]`. It works
like `simp`, but only uses the given lemmas. Every `simp` can be turned into a
`simp only` automatically by using `simp?` and clicking on the suggestion.
-/

/- Preimages are monotone. The rewrite we want is `Set.mem_preimage : a ∈ f ⁻¹' s ↔ f a ∈ s`,
whose name `simp?` gives. -/
example {X Y : Type*} (f : X → Y) (A B : Set Y) (h : A ⊆ B) : f ⁻¹' A ⊆ f ⁻¹' B := by
  intro x hx
  simp at hx ⊢
  apply h
  exact hx
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

/- `ring` knows nothing about the hypotheses, so we use them first and call `ring` on what is
left. -/
example {R : Type*} [CommRing R] (a b : R) (h : a + b = 0) : a ^ 3 + b ^ 3 = 0 := by
  -- `eq_neg_of_add_eq_zero_left : a + b = 0 → a = -b`
  have ha : a = -b := eq_neg_of_add_eq_zero_left h
  rw [ha]
  ring
  done

/- `ℕ` is not a ring (there are no negatives) but `ring` also handles identities that hold in
every commutative *semi*ring, which is what `ℕ` is. -/
example (n m : ℕ) (h : n = 2 * m + 1) : n ^ 2 = 4 * (m * (m + 1)) + 1 := by
  rw [h]
  ring
  done

/- Often the hypotheses do not rewrite into the goal directly, and the identity that makes them
applicable is itself proved by `ring`. -/
example (x y : ℝ) (h1 : x + y = 3) (h2 : x * y = 1) : x ^ 3 + y ^ 3 = 18 := by
  have key : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by ring
  rw [key, h1, h2]
  ring
  done

/- While `ring` either closes the goal or fails, `ring_nf` ("ring normal form") normalises
algebraic terms, not necessarily closing the goal. It also works `at` a hypothesis. Here it puts
`h` in a form `simp` can factor. -/
example (x y : ℝ) (h : (x + y) ^ 2 = x ^ 2 + y ^ 2) : x * y = 0 := by
  ring_nf at h
  simp at h
  rcases h with h | h
  · rw [h]
    ring
  · rw [h]
    ring
  done

/- `simp` and `ring` in the same proof: `simp [h]` replaces every `f n` by `x ^ n` and computes
`x ^ 1` and `x ^ 0`, `ring` proves the identity that is left. -/
example (f : ℕ → ℝ) (x : ℝ) (h : ∀ n, f n = x ^ n) : f 2 + 2 * f 1 + f 0 = (x + 1) ^ 2 := by
  simp [h]
  ring
  done

/-!
## Existential statements: `use` and `obtain`

To prove `∃ x, P x` one exhibits a witness: `use a` replaces the goal by `P a`, and tries to
close what is left by `rfl`. To use a hypothesis `h : ∃ x, P x` one gives the object a name:
`obtain ⟨a, ha⟩ := h` puts `a` and `ha : P a` in the context. The brackets `⟨ ⟩` are typed `\<`
and `\>`.

`obtain ⟨a, ha⟩ := h` is the same tactic as `rcases h with ⟨a, ha⟩` from the logic lecture, written
the other way round, and it takes apart conjunctions just as well: `obtain ⟨h1, h2⟩ := h` splits
`h : P ∧ Q` into its two halves.
-/

example (x : ℝ) : ∃ y : ℝ, x + y = 0 := by
  use -x
  ring
  done

/- There is no largest natural number. -/
example : ∀ n : ℕ, ∃ m : ℕ, n < m := by
  intro n
  use n + 1
  simp
  done

/- Several witnesses at once, for nested existentials: every real number is the sum of two equal
halves. -/
example (x : ℝ) : ∃ a b : ℝ, a + b = x ∧ a - b = 0 := by
  use x / 2, x / 2
  constructor
  · ring
  · ring
  done

/- Divisibility is an existential statement: `a ∣ b` (type `∣` as `\|`, it is *not* plain `|`)
means `∃ c, b = a * c`. So `obtain` opens a divisibility hypothesis and `use` proves a
divisibility goal. -/
example (a b c : ℤ) (hb : a ∣ b) (hc : a ∣ c) : a ∣ b + c := by
  obtain ⟨k, hk⟩ := hb
  obtain ⟨l, hl⟩ := hc
  use k + l
  rw [hk, hl]
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

/- A longer example: `5 ^ n - 1` is divisible by `4`, by induction on `n`. The proof uses most of
this lecture: `induction` for the structure, `obtain` and `use` for the divisibility, `rw` and
`ring` for the computation. On paper: if `5 ^ n = 4 k + 1`, then
`5 ^ (n + 1) = 5 (4 k + 1) = 4 (5 k + 1) + 1`. -/
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

/- Two finite sets with the same elements have the same cardinality. `congr 1` reduces the goal
about the cardinalities to `s = t`; `Finset.ext` is the extensionality principle for finite sets.
`congr` closes with `assumption` the goals it can, so it sometimes finishes on its own. -/
example (s t : Finset ℕ) (h : ∀ x, x ∈ s ↔ x ∈ t) : s.card = t.card := by
  congr 1
  apply Finset.ext
  exact h
  done

/-!
## `gcongr`

`gcongr` is the same idea for inequalities and more generally for relations. To prove
`a + c ≤ b + d` it is enough to prove `a ≤ b` and `c ≤ d`, because `+` is monotone in both
arguments. Side conditions such as `0 ≤ x` it discharges itself, using the context.
-/

example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d := by
  gcongr
  done

/- The typical use is an estimate where only one part of a large expression is compared.
`gcongr with i hi` names the bound variable and the assumption `i ∈ Finset.range n` of the goal
that is left. -/
example (f : ℕ → ℝ) (n : ℕ) (h : ∀ i, f i ≤ 1) : ∑ i ∈ Finset.range n, f i ≤ n := by
  have key : ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range n, (1 : ℝ) := by
    gcongr with i hi
    exact h i
  simp at key
  exact key
  done

/-!
## `grw`

`grw` ("generalized rewrite") is `rw` for inequalities (more generally relations): given
`h : a ≤ b` it replaces `a` by `b` in the goal, provided the replacement makes the goal
stronger.
-/

/- Replacing `a` by the larger `b` turns the goal into the hypothesis `h`. The side condition
`0 ≤ c` is again found in the context. -/
example (a b c : ℝ) (hab : a ≤ b) (hc : 0 ≤ c) (h : b * c ≤ 1) : a * c ≤ 1 := by
  grw [hab]
  exact h
  done

/- The typical `ε` estimate: bound the quantity by `ε` first, then bound `ε`. -/
example (x y ε : ℝ) (h : |x - y| ≤ ε) (hε : ε ≤ 1) : |x - y| ≤ 1 := by
  grw [h]
  exact hε
  done

/-!
## Rewriting under a binder

`rw` does not rewrite in terms with bound variables. For example, in
`∑ i ∈ Finset.range n, f i * 1` the `i` is bound by the `∑`, so `rw` fails.
-/

example (n : ℕ) (f : ℕ → ℝ) : ∑ i ∈ Finset.range n, f i * 1 = ∑ i ∈ Finset.range n, f i := by
  rw [mul_one]
  done

/- One option is to use `simp` or `simp only`, which rewrite under binders. Once the `* 1` is
gone, `Finset.sum_nonneg` applies. -/
example (n : ℕ) (f : ℕ → ℝ) (h : ∀ i, 0 ≤ f i) : 0 ≤ ∑ i ∈ Finset.range n, f i * 1 := by
  simp only [mul_one]
  apply Finset.sum_nonneg
  intro i hi
  exact h i
  done

/- More similar to `rw` is `simp_rw [h₁, ..., hₙ]`, while still rewriting under binders. Here it
pulls the `2 *` inside the sum, and `Finset.mul_sum` pulls it back out. -/
example (f : ℕ → ℝ) (h : ∀ n, f n = 2 * n) (s : Finset ℕ) :
    ∑ i ∈ s, f i = 2 * ∑ i ∈ s, (i : ℝ) := by
  simp_rw [h]
  rw [Finset.mul_sum]
  done

/- `simp_rw` also differs from `rw` in how often it rewrites: `rw [h]` fixes `n := 1` at the first
match and leaves `f 2` alone, while `simp_rw [h]` rewrites both. -/
example (f : ℕ → ℕ) (h : ∀ n, f n = n + 1) : f 1 + f 2 = 5 := by
  simp_rw [h]
  done

/-!
## `grind`

`grind` is a general purpose automation tactic. It combines the simplifier with congruence
closure, linear arithmetic, the ring normalisation of `ring` and case splitting on the
hypotheses. It either closes the goal or fails.
-/

/- `grind` splits into cases by itself, and knows how to compute in a ring. -/
example (x : ℝ) (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  grind
  done

/- See the end of the logic lecture for a hands-on proof. -/
example {X : Type*} (A B C : Set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  grind
  done

/- `grind` does not look for an induction, so on its own it fails here. Set the proof up and it
closes both cases, the second one from the induction hypothesis. -/
example (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => grind
  | succ n ih => grind
  done

/-!
## Exercises

The tactics of this lecture are `simp`, `simp?`, `simp only`, `ring`, `ring_nf`, `use`, `obtain`,
`induction`, `congr`, `gcongr`, `grw`, `simp_rw` and `grind`; those of the first two are still
available.

As before, replace each `sorry` by a proof. None of them is a one-liner.
-/

/- Simplification. -/

theorem adv_ex_1 {X Y : Type*} (f : X → Y) (A B : Set Y) : f ⁻¹' (A ∩ B) ⊆ f ⁻¹' A := by
  sorry
  done

/- Hint: `simp at h` first, and remember that `h` is a statement about *every* `n`. -/
theorem adv_ex_2 (f : ℕ → ℕ) (h : ∀ n, f (n + 0) = n * 1) : ∀ n, f (f n) = n := by
  sorry
  done

theorem adv_ex_3 {X : Type*} (A B C : Set X) (h : A ⊆ B) : A ∩ C ⊆ B ∩ C := by
  sorry
  done

/- Use `simp?` here, and replace the `simp` by the `simp only` it suggests. -/
theorem adv_ex_4 (l : List ℕ) (h : l.length = 10) : (l.reverse ++ []).length + 0 = 10 := by
  sorry
  done

/- Ring identities. -/

/- Hint: `x ^ 2 + y ^ 2` is `(x + y) ^ 2 - 2 * (x * y)`. Prove that with `ring` in a `have`. -/
theorem adv_ex_5 (x y : ℝ) (h1 : x + y = 5) (h2 : x * y = 3) : x ^ 2 + y ^ 2 = 19 := by
  sorry
  done

/- Hint: two `have`s, one for `x ^ 2 + y ^ 2` and one for `x ^ 4 + y ^ 4`. -/
theorem adv_ex_6 (x y : ℝ) (h1 : x + y = 3) (h2 : x * y = 2) : x ^ 4 + y ^ 4 = 17 := by
  sorry
  done

theorem adv_ex_7 {R : Type*} [CommRing R] (a b : R) (h : a = b + 1) :
    a ^ 3 - b ^ 3 = 3 * b ^ 2 + 3 * b + 1 := by
  sorry
  done

/- Hint: `x ^ 4 = (x ^ 2) ^ 2`, so `h` can be used twice. -/
theorem adv_ex_8 (x : ℝ) (h : x ^ 2 = x + 1) : x ^ 4 = 3 * x + 2 := by
  sorry
  done

theorem adv_ex_9 (a b : ℝ) (h1 : a + b = 5) (h2 : a - b = 1) : a ^ 2 - b ^ 2 = 5 := by
  sorry
  done

/- Existential statements. -/

theorem adv_ex_10 (a b c : ℤ) (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ 2 * b - 3 * c := by
  sorry
  done

/- `Odd n` is `∃ k, n = 2 * k + 1`. -/
theorem adv_ex_11 (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  sorry
  done

theorem adv_ex_12 (f : ℝ → ℝ) (hf : ∀ x, f x = 2 * x + 1) : ∀ y : ℝ, ∃ x : ℝ, f x = y := by
  sorry
  done

theorem adv_ex_13 (h : ∃ x : ℝ, x ^ 2 = 2) : ∃ x : ℝ, x ^ 4 = 4 := by
  sorry
  done

/- Induction. -/

/- Hint: `add_right_comm a b c : a + b + c = a + c + b` puts the `+ 1` back where the induction
hypothesis expects it. -/
theorem adv_ex_14 (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i + 1 = 2 ^ n := by
  sorry
  done

/- The sum of the first squares, again multiplied by a constant to stay inside `ℕ`. -/
theorem adv_ex_15 (n : ℕ) :
    6 * ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  sorry
  done

/- Nicomachus' theorem: the sum of the first cubes is the square of the sum of the first numbers. -/
theorem adv_ex_16 (n : ℕ) : 4 * ∑ i ∈ Finset.range (n + 1), i ^ 3 = (n * (n + 1)) ^ 2 := by
  sorry
  done

/- The same proof as the longer example above, with different numbers. -/
theorem adv_ex_17 (n : ℕ) : (3 : ℤ) ∣ 4 ^ n - 1 := by
  sorry
  done

/- The geometric sum. Over `ℝ` this time, so that `-` is genuine subtraction. -/
theorem adv_ex_18 (x : ℝ) (n : ℕ) : (x - 1) * ∑ i ∈ Finset.range n, x ^ i = x ^ n - 1 := by
  sorry
  done

/- Congruence and monotonicity. -/

theorem adv_ex_19 (x y : ℝ) (h : x = y + 1) : Real.sqrt (x ^ 2) = Real.sqrt ((y + 1) ^ 2) := by
  sorry
  done

theorem adv_ex_20 (f g : ℕ → ℝ) (n : ℕ) (h : ∀ i, f i ≤ g i) (hf : ∀ i, 0 ≤ f i) :
    ∑ i ∈ Finset.range n, f i ^ 2 ≤ ∑ i ∈ Finset.range n, g i ^ 2 := by
  sorry
  done

theorem adv_ex_21 (a b c d : ℝ) (hb : 0 ≤ b) (hc : 0 ≤ c) (h1 : a ≤ b) (h2 : c ≤ d)
    (h : b * d ≤ 5) : a * c ≤ 5 := by
  sorry
  done

/- Under a binder. -/

/- Hint: after `simp_rw [h]`, split the sum with `Finset.sum_add_distrib`. -/
theorem adv_ex_22 (f g : ℕ → ℝ) (h : ∀ n, f n = g n + 1) (s : Finset ℕ) :
    ∑ i ∈ s, f i = (∑ i ∈ s, g i) + s.card := by
  sorry
  done

/- Automation. The first two are exercises of the logic lecture, proved there by hand. -/

theorem adv_ex_23 (P Q R : Prop) (h : P ∨ (Q ∧ R)) : (P ∨ Q) ∧ (P ∨ R) := by
  sorry
  done

theorem adv_ex_24 {X : Type*} (A B C : Set X) : A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  sorry
  done

/- In the last two, `grind` on its own fails: it does not look for an induction and it does not
take an existential apart. Set the proof up first, then let `grind` close what is left. -/

theorem adv_ex_25 (f : ℕ → ℕ) (h : ∀ n, f (n + 1) = f n + 2) (n : ℕ) : f n = f 0 + 2 * n := by
  sorry
  done

theorem adv_ex_26 (n : ℕ) : 2 ∣ n ^ 2 + n := by
  sorry
  done
