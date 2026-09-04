/-
Copyright (c) 2026 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

module

import Mathlib
import LFTCM2026.Preliminaries

/-!
# Logic

In this lecture we learn how to prove and use statements built with "and", "or" and "not". We
also meet three tactics for working with negation and contradiction: `exfalso`, `by_contra` and
`push Not`.

As in the first lecture, move through the proofs one line at a time and watch the goal and the
hypotheses in the Infoview. The symbols used below are:

* `P ∧ Q` — "`P` and `Q`" (`∧` is typed `\and`);
* `P ∨ Q` — "`P` or `Q`" (`∨` is typed `\or`);
* `¬ P` — "not `P`" (`¬` is typed `\not`);
* `False` — the proposition which has no proof.

Here `P`, `Q` and `R` are arbitrary propositions.
-/

/-!
## Conjunction: `P ∧ Q`

To prove `P ∧ Q` we must prove both parts. The tactic `constructor` separates the goal into the
two goals `P` and `Q`.
-/

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  -- Recall that the focusing dot `·` is typed `\.`. It works on one goal at a time.
  · exact hP
  · exact hQ
  done

/- A proof of `P ∧ Q` contains a proof of each part. They are called `h.left` (or `h.1`) and
`h.right` (or `h.2`). -/
example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left
  done

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right
  done

/- We can therefore exchange the two parts of a conjunction. -/
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  constructor
  · exact h.2
  · exact h.1
  done

/- Of course, there is an alternative way to do this: `rw [and_comm]` where `and_comm` is the
theorem that states `P ∧ Q ↔ Q ∧ P`. -/
example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  rw [and_comm]
  exact h
  done

/- Conjunctions can be nested. Since `∧` associates to the right, `P ∧ Q ∧ R` means
`P ∧ (Q ∧ R)`. -/
example (P Q R : Prop) (hP : P) (hQ : Q) (hR : R) : P ∧ Q ∧ R := by
  constructor
  · exact hP
  · constructor
    · exact hQ
    · exact hR
  done

/- The same pattern works for mathematical statements. -/
example (x : ℝ) (h : 0 < x ∧ x < 1) : x < 1 := by
  exact h.2
  done

/-!
## Disjunction: `P ∨ Q`

To prove `P ∨ Q`, it is enough to prove one side. Use `left` if you will prove `P`, and `right` if
you will prove `Q`.
-/

example (P Q : Prop) (hP : P) : P ∨ Q := by
  left
  exact hP
  done

example (P Q : Prop) (hQ : Q) : P ∨ Q := by
  right
  exact hQ
  done

/- A hypothesis `h : P ∨ Q` does not tell us which side is true. The tactic `cases h` creates one
goal for the case `P` and another for the case `Q`.
-/
example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  · -- In the first case we have a proof of `P`.
    right
    assumption
  · -- In the second case we have a proof of `Q`.
    left
    assumption
  done

/- `cases h` is convenient when `assumption` can find the unnamed hypotheses. When we want to
name them, we write `rcases h with hP | hQ`. -/
example (P Q R : Prop) (h : P ∨ Q) (hPR : P → R) (hQR : Q → R) : R := by
  rcases h with hP | hQ
  · apply hPR
    exact hP
  · apply hQR
    exact hQ
  done

example (x y : ℝ) (h : x = 0 ∨ y = 0) : x * y = 0 := by
  rcases h with hx | hy
  · rw [hx, zero_mul]
  · rw [hy, mul_zero]
  done

/- We can combine `constructor` and `rcases`. -/
example (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  rcases h.2 with hQ | hR
  · left
    constructor
    · exact h.1
    · exact hQ
  · right
    constructor
    · exact h.1
    · exact hR
  done

/-!
## Negation, `False` and `exfalso`

The proposition `¬ P` is defined to mean `P → False`. Thus, to prove `¬ P`, we assume `P` and
derive `False`.
-/

example (P Q : Prop) (hPQ : P → Q) (hnQ : ¬ Q) : ¬ P := by
  intro hP
  have hQ : Q := hPQ hP
  exact hnQ hQ
  done

/- A hypothesis `h : ¬ P` can be applied to a proof `hP : P`; the result `h hP` is a proof of
`False`. -/
example (P : Prop) : ¬ (P ∧ ¬ P) := by
  intro h
  exact h.2 h.1
  done

/- If the current hypotheses are impossible, then any goal follows. The tactic `exfalso` replaces
the current goal by `False`, allowing us to concentrate on the contradiction. -/
example (P : Prop) (hP : P) (hnP : ¬ P) : 0 = 1 := by
  exfalso
  exact hnP hP
  done

/- Unlike `contradiction`, which searches for an immediate contradictory pair, `exfalso` only
changes the goal. We must still construct the proof of `False` ourselves. -/
example (P Q : Prop) (hPQ : P → Q) (hP : P) (hnQ : ¬ Q) : 1 + 1 = 3 := by
  exfalso
  -- Here `contradiction` does not work.
  have hQ : Q := hPQ hP
  exact hnQ hQ
  done

/-!
## Proof by contradiction: `by_contra`

The tactic `by_contra h` proves a goal `P` by assuming its negation `h : ¬ P`. The new goal is
`False`: we now have to show that the assumption leads to a contradiction.
-/

example (P : Prop) (h : ¬ ¬ P) : P := by
  by_contra hnP
  -- ` ¬ ¬ P` is the same as `(P → False) → False`. Thus `h hnP` is a proof of `False`.
  exact h hnP
  done

example (P Q : Prop) (h₁ : ¬ P → Q) (h₂ : ¬ P → ¬ Q) : P := by
  by_contra hnP
  have hQ : Q := h₁ hnP -- type the index 1 as `\_1`.
  have hnQ : ¬ Q := h₂ hnP
  exact hnQ hQ
  done

/- If a real number is not nonzero, it is zero. -/
example (x : ℝ) (h : ¬ x ≠ 0) : x = 0 := by
  by_contra hx
  exact h hx
  done

/-!
## Pushing negations: `push Not`

The tactic `push Not` moves negations inwards using the usual logical rules. Among others:

* `¬ (P ∨ Q)` becomes `¬ P ∧ ¬ Q`;
* `¬ (P ∧ Q)` becomes `P → ¬ Q`;
* `¬ (P → Q)` becomes `P ∧ ¬ Q`;
* `¬ ∀ x, P x` becomes `∃ x, ¬ P x`;
* `¬ ∃ x, P x` becomes `∀ x, ¬ P x`.
-/

example (P Q : Prop) (h : ¬ P ∧ ¬ Q) : ¬ (P ∨ Q) := by
  push Not
  exact h
  done

example (P Q : Prop) (h : P → ¬ Q) : ¬ (P ∧ Q) := by
  push Not
  exact h
  done

example (P Q : Prop) (h : ¬ (P → Q)) : P ∧ ¬ Q := by
  push Not at h
  exact h
  done

example {X : Type*} (P : X → Prop) (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  push Not at h
  exact h
  done

example {X : Type*} (P : X → Prop) (h : ¬ ∃ x, P x) : ∀ x, ¬ P x := by
  push Not at h
  exact h
  done

/- `push Not` also knows how negated equalities and inequalities behave. -/
example (x : ℝ) (h : ¬ x ≤ 3) : 3 < x := by
  push Not at h
  exact h
  done

example (S : Set ℝ) (x : ℝ) (h : ¬ ∀ y ∈ S, y ≤ x) : ∃ y ∈ S, x < y := by
  push Not at h
  exact h
  done

/- A longer example: here `push Not` only gets us started. Once `h` says `0 ≤ x ∧ x ≤ 1`, we
still have to do some real work, using `pow_two : x ^ 2 = x * x` and
`mul_le_of_le_one_right : 0 ≤ a → b ≤ 1 → a * b ≤ a`. -/
example (x : ℝ) (h : ¬ (x < 0 ∨ 1 < x)) : x ^ 2 ≤ x := by
  push Not at h
  rw [pow_two]
  exact mul_le_of_le_one_right h.1 h.2
  done

/-!
## Splitting into cases: `by_cases`

The tactic `by_cases hP : P` divides the proof into two cases. In the first case the context
contains `hP : P`; in the second it contains `hP : ¬ P`. The focusing dots keep the two cases
separate.

Unlike `cases`, which splits an existing disjunction hypothesis, `by_cases` creates the two
possibilities using the law of excluded middle. It is therefore another classical tactic.
-/

/- For every proposition `P`, either `P` or its negation holds. -/
example (P : Prop) : P ∨ ¬ P := by
  by_cases hP : P
  · left
    exact hP
  · right
    exact hP
  done

/- Here the conclusion depends on which of `P` and `¬ P` holds. -/
example (P Q R : Prop) (hPQ : P → Q) (hnPR : ¬ P → R) : Q ∨ R := by
  by_cases hP : P
  · left
    apply hPQ
    exact hP
  · right
    apply hnPR
    exact hP
  done

/- A real number is either zero or has positive square. In the second case,
`sq_pos_of_ne_zero` turns `hx : x ≠ 0` into `0 < x ^ 2`. -/
example (x : ℝ) : x = 0 ∨ 0 < x ^ 2 := by
  by_cases hx : x = 0
  · left
    exact hx
  · right
    exact sq_pos_of_ne_zero hx
  done

/- A more substantial application in which the two cases are not visible in the goal.
Suppose we only know
`mul_nonneg`: `∀ a b, 0 ≤ a → 0 ≤ b → 0 ≤ a * b` and
`mul_nonneg_of_nonpos_of_nonpos`: `∀ a b, a ≤ 0 → b ≤ 0 → 0 ≤ a * b`.
 -/
example (x : ℝ) : 0 ≤ x * x := by
  by_cases hx : 0 ≤ x
  · apply mul_nonneg
    · exact hx
    · exact hx
  · push Not at hx
    apply mul_nonneg_of_nonpos_of_nonpos
    · exact le_of_lt hx
    · exact le_of_lt hx
  done

/-!
## A longer mathematical example

We finish the tutorial by proving that intersection distributes over union. The notation `A ∩ B`
means intersection (`∩` is typed `\inter` or `\cap`), and `A ∪ B` means union (`∪` is typed
`\union` or `\cup`).

The lemma `Set.ext` says that two sets are equal if they have exactly the same elements. After
applying it and introducing an arbitrary `x`, the goal is an `↔`: we must prove membership in one
set from membership in the other, in both directions. The tactic `constructor` separates these
two implications, just as it separates the two parts of a conjunction.

After that, membership in an intersection behaves like `∧`, and membership in a union behaves
like `∨`. Thus the proof is precisely the logical distributive law from this lecture.
-/

example {X : Type*} (A B C : Set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx.2 with hxB | hxC
    · left
      constructor
      · exact hx.1
      · exact hxB
    · right
      constructor
      · exact hx.1
      · exact hxC
  · intro hx
    rcases hx with hxAB | hxAC
    · constructor
      · exact hxAB.1
      · left
        exact hxAB.2
    · constructor
      · exact hxAC.1
      · right
        exact hxAC.2
  done

/-!
## Exercises

Every exercise can be solved with the tactics from the first lecture and this one. In particular,
remember:

* use `constructor` to prove a conjunction and `.1`, `.2` to use one;
* use `left` or `right` to prove a disjunction, and `cases` or `rcases` to use one;
* use `intro` to prove a negation;
* use `exfalso` or `by_contra` when you want the goal to become `False`;
* use `push Not (at h)` to push negations (inside `h`);
* use `by_cases hP : P` to consider separately the cases `P` and `¬ P`;
* use `apply Set.ext` and `intro x` to turn a set equality into a membership `↔` for an
  arbitrary `x`.

Replace each `sorry` with a proof. If you leave an exercise unfinished, put `sorry` back so that
the rest of the file remains usable.
-/

/- Conjunctions and disjunctions. -/

theorem logic_ex_1 (P Q R : Prop) (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) := by
  sorry
  done

theorem logic_ex_2 (P Q R : Prop) (h : (P ∧ Q) ∨ (P ∧ R)) : P ∧ (Q ∨ R) := by
  sorry
  done

theorem logic_ex_3 (P Q R : Prop) (h : P ∨ (Q ∧ R)) : (P ∨ Q) ∧ (P ∨ R) := by
  sorry
  done

theorem logic_ex_4 (P Q R S : Prop) (h : P ∨ Q) (hPR : P → R) (hQS : Q → S) : R ∨ S := by
  sorry
  done

/- Negation and `exfalso`. -/

theorem logic_ex_5 (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hnR : ¬ R) : ¬ P := by
  sorry
  done

theorem logic_ex_6 (P Q : Prop) : ¬ (P ∧ Q ∧ ¬ P) := by
  sorry
  done

theorem logic_ex_7 (P Q : Prop) (h : (P ∨ Q) ∧ ¬ P) : Q := by
  sorry
  done

theorem logic_ex_8 (P Q R : Prop) (h : P ∨ Q) (hnP : ¬ P) (hnQ : ¬ Q) : R := by
  sorry
  done

/- Proof by contradiction. -/

theorem logic_ex_9 (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  sorry
  done

/- Hint: assume `¬ P`, then try to show that `P → Q`. -/
theorem logic_ex_10 (P Q : Prop) (h : (P → Q) → P) : P := by
  sorry
  done

/- Specialize `h` at `1` (use `have h1 := h 1`) and rewrite with `mul_one`. -/
theorem logic_ex_11 (x : ℝ) (h : ∀ y : ℝ, x * y = 0) : x = 0 := by
  sorry
  done

/- Pushing negations. -/

/- Start by applying `push Not` to the goal. -/
theorem logic_ex_12 (P Q R : Prop) (hnP : ¬ P) (hQR : Q → ¬ R) :
    ¬ (P ∨ (Q ∧ R)) := by
  sorry
  done

theorem logic_ex_13 (P Q R : Prop) (h : ¬ (P ∨ (Q ∧ R))) (hQ : Q) : ¬ P ∧ ¬ R := by
  sorry
  done

theorem logic_ex_14 {X : Type*} (P Q : X → Prop) (h : ¬ ∃ x, P x ∧ Q x)
    (hP : ∀ x, P x) : ∀ x, ¬ Q x := by
  sorry
  done

/- After pushing the negation, use `mul_pos` and
`sub_pos : 0 < a - b ↔ b < a`. -/
theorem logic_ex_15 (x y z w : ℝ) (h : ¬ (x ≤ y ∨ z ≤ w)) :
    0 < (x - y) * (z - w) := by
  sorry
  done

/- Splitting with `by_cases`. -/

theorem logic_ex_16 (P Q : Prop) (h : ¬ P → Q) : P ∨ Q := by
  sorry
  done

/- Here the proposition used for the case split does not occur in the goal. -/
theorem logic_ex_17 (P Q : Prop) (hP : P → Q) (hnP : ¬ P → Q) : Q := by
  sorry
  done

/- If `A` and `C` agree both inside `B` and outside `B`, then they are equal. Start with
`apply Set.ext`. In each direction, split into the cases `x ∈ B` and `x ∉ B`, construct
membership in the appropriate intersection or set difference, and rewrite it using `hinside` or
`houtside`.
-/
theorem logic_ex_18 {X : Type*} (A B C : Set X)
    (hinside : A ∩ B = C ∩ B) (houtside : A \ B = C \ B) : A = C := by
  sorry
  done

/- Set-theoretic challenges. As in the longer example, start with `apply Set.ext`, introduce an
arbitrary element, and use `constructor` for the two directions. -/

theorem logic_ex_19 {X : Type*} (A B C : Set X) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry
  done

/- `A \ B` is the set difference: its elements belong to `A` but not to `B`. -/
theorem logic_ex_20 {X : Type*} (A B C : Set X) :
    A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  sorry
  done

/- In the reverse direction, use `by_cases hxB : x ∈ B`. -/
theorem logic_ex_21 {X : Type*} (A B : Set X) : (A ∩ B) ∪ (A \ B) = A := by
  sorry
  done
