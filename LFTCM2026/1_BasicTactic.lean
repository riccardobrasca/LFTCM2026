/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import Mathlib
import LFTCM2026.Preliminaries

/-!

If you want to go further than what we can cover here, the Lean community keeps a list of books,
tutorials and courses at <https://leanprover-community.github.io/learn.html>: that page is the
right place to look for extra material, both during the workshop and after it.

# Basic tactics

This is our first real Lean file. We will prove that the composition of two continuous functions
is continuous, in the obvious way. Mathlib of course already knows this lemma, and in real work you
would simply invoke it; but the point here is not the result. The point is to meet the basic
**tactics**, which are the commands you use to tell Lean how to build a proof.

A word on how to read a Lean file. Put your cursor anywhere inside a proof and look at the
*Lean Infoview* panel on the right (if you do not see it, click the `∀` menu in the top right and
choose `Infoview: Toggle Infoview`). It shows you the **goal**: what you still have to prove, and
which hypotheses you may use. Watching the goal change as you move the cursor line by line is by
far the fastest way to learn what a tactic does. Do that constantly.

One warning before we start: Lean is *whitespace sensitive*. Indentation is part of the syntax, not
decoration, so we suggest following closely the indentation conventions used in our files.
-/

/-
An `example` is a theorem without a name: we prove it, Lean checks it, and it is discarded.

Read the statement as follows. Everything before the colon `:` is the list of *assumptions*, and
what comes after is the *statement*. So the two lines below say:

  "let `X`, `Y` and `Z` be topological spaces, let `f : X → Y` and `g : Y → Z` be functions, and
  assume that `f` is continuous and that `g` is continuous; then `g ∘ f` is continuous."

You will have noticed that the assumptions come in three different kinds of brackets, curly `{ }`,
square `[ ]` and round `( )`. The difference is real and we will come back to it, but it changes
nothing about *what* the statement says, so for now simply ignore it and read every bracket as
"let ... be ...", exactly as in the sentence above.

Two things in that sentence do deserve a comment now:

* `(hf : Continuous f)` is the fact that `f` is continuous, and `hf` is the name of that
  assumption. In pen-and-paper mathematics we usually only name objects; in Lean we also name
  assumptions.
* The symbol `∘` in the conclusion is composition; you can type it as `\comp` or `\circ`. In
  general you can hover the cursor over a symbol and VS Code will tell you how to type it. The
  LaTeX command is a good guess.

The keywords `by` and `done` are the delimiters of the proof: they just tell Lean that you plan to insert the proof between the line following by and the line preceding done. They are analogous to LaTeX
\begin{proof} and \end{proof}. In particular, the fact that you write done at the end is not telling Lean that you are really "done", just explaining that what comes after done will have nothing to do with this theorem (you will see an error if the proof is not complete).
-/
example {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) : Continuous (g ∘ f) := by
  -- `continuous_def` is the lemma `Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s)`: it says that
  -- `Continuous` means what we expect it to mean. The tactic `rw` ("rewrite") replaces one side
  -- of an equality, or of an iff, as here, by the other, and `at hf hg ⊢` tells it to do so in
  -- our two hypotheses *and* in the goal `⊢`. After this line the word `Continuous` has
  -- disappeared: we are looking at open sets and preimages, just as we would on paper.
  rw [continuous_def] at hf hg ⊢
  -- The goal now begins with `∀ U, IsOpen U → ...`, that is, "for any open set `U` of `Z`...".
  -- On paper you would write "let `U` be open"; in Lean the tactic that does it is `intro`.
  -- It names the two things we are handed: the set `U`, and `hU`, the *assumption* that `U` is
  -- open. Note that the assumption gets a name of its own, like any other object.
  intro U hU
  -- Continuity of `g`, now that it is unfolded, behaves like a function: feed it a set and the
  -- fact that the set is open, and it gives you back the fact that the preimage is open. So
  -- `hg U hU` says exactly that `g ⁻¹' U` is open, and `have` records it in the context under the
  -- name `hgU`.
  have hgU : IsOpen (g ⁻¹' U) := hg U hU
  -- Since `f` is continuous and `g ⁻¹' U` is open, the preimage of `g ⁻¹' U` under `f` is open.
  have hfgU : IsOpen (f ⁻¹' (g ⁻¹' U)) := hf (g ⁻¹' U) hgU
  -- We are done, up to writing the preimage under `g ∘ f` as an iterated preimage. That is what
  -- `Set.preimage_comp : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s)` says, so rewriting with it turns the
  -- goal into precisely the statement of `hfgU`.
  rw [Set.preimage_comp]
  -- `exact e` means "the goal is proved by `e`, take it". The proof is finished, and the Infoview
  -- now says `No goals`.
  exact hfgU
  done

/-!
## The `exact` and `assumption` tactics

`exact e` finishes the proof when `e` is exactly what one needs to prove. `assumption` does the same
job, but looks for the proof itself among the hypotheses, so you do not have to name it.
-/

/- The hypothesis `h` is literally the goal. -/
example (x y : ℝ) (h : x < y) : x < y := by
  exact h
  done

/- Any expression proving the goal will do, not just a hypothesis: here a lemma from Mathlib,
`le_of_lt : a < b → a ≤ b`, applied to our hypothesis. -/
example (x y : ℝ) (h : x < y) : x ≤ y := by
  exact le_of_lt h
  done

/- `assumption` finds `hy` on its own. Useful when there are many hypotheses around. -/
example (x y : ℝ) (hx : x = 3) (hy : y = 4) : y = 4 := by
  assumption
  done

/-!
## The `rw` tactic

`rw` ("rewrite") is the one of the most basic Lean tactic.
Given an equality, it replaces, in the goal, the left-hand side by the right-hand side.

An assumption such as `hx : x + 4 = 7` is an equality, and so is a lemma from Mathlib. `rw` does
not distinguish between the two.
-/

/- One rewrite per line. Move the cursor from one line to the next and watch the goal. -/
example (x y : ℝ) (hx : x + 4 = 7) (hy : 7 + y = 5) : x + 4 + y = 5 := by
  rw [hx]
  rw [hy]
  done

/- Several rewrites, performed in the order given, can go in a single `rw`. Note that the last one
leaves the goal `5 = 5`: `rw` closes such a goal by itself. -/
example (x y : ℝ) (hx : x + 4 = 7) (hy : 7 + y = 5) : x + 4 + y = 5 := by
  rw [hx, hy]
  done

/- `rw` acts on the goal unless you tell it otherwise; `rw [...] at h` acts on the assumption `h`.
Here `h` becomes `7 + y = 5`, which is precisely the goal. -/
example (x y : ℝ) (hx : x + 4 = 7) (h : x + 4 + y = 5) : 7 + y = 5 := by
  rw [hx] at h
  exact h
  done

/- With `←` (type it as `\l`) the equality is used from right to left, so here every `7` in the
goal becomes an `x + 4`. -/
example (x y : ℝ) (hx : x + 4 = 7) (hy : x + 4 + y = 5) : 7 + y = 5 := by
  rw [← hx]
  exact hy
  done

/- Now a lemma from the library instead of a local assumption: `mul_one` says `a * 1 = a`, for
every `a`. That `a` is an argument, and you may supply it yourself to choose which occurrence is
rewritten — below, `y * 1` first. -/
example (x y : ℝ) : x * 1 + y * 1 = x + y := by
  rw [mul_one y, mul_one x]
  done

/- Writing `_` instead means "work this one out for me": Lean finds the value of `a` by looking at
the goal, and takes the first thing it can, so here `mul_one _` deals with `x * 1` and the second
one with `y * 1`. You may also leave the argument out altogether. The point of `_` is that in a
lemma with several arguments you can pin down the ones you care about and leave the rest to Lean. -/
example (x y : ℝ) : x * 1 + y * 1 = x + y := by
  rw [mul_one _, mul_one]
  done

/-!
## The `rfl` tactic

`rfl` ("reflexivity") proves a goal `a = b` when the two sides are *the same thing* as far as Lean
is concerned: written identically, or identical after unfolding definitions and computing.
-/

/- The most basic property of equality. -/
example (n : ℕ) : n = n := by
  rfl
  done

/- Lean computes both sides and finds the same natural number. -/
example : 2 + 2 = 4 := by
  rfl
  done

/- The two sides are not written the same way, but `g ∘ f` is *defined* as the function sending
`x` to `g (f x)`, so unfolding that definition makes them identical. -/
example {X Y Z : Type*} (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl
  done

/-!
## The `apply` tactic

`apply e` is `exact e` with the missing arguments left behind: if `e` proves the goal once it is
fed some hypotheses, `apply` accepts it and turns those hypotheses into new goals.
-/

/- `le_of_lt` produces `x ≤ y` out of a proof of `x < y`, so that is what is left to prove. -/
example (x y : ℝ) (h : x < y) : x ≤ y := by
  apply le_of_lt
  exact h
  done

/- `mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b` takes two arguments, so we get two goals. The focusing
dots `·` (type `\.`) work on one goal at a time; they are optional, but they keep a proof readable
and are strongly recommended. -/
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by
  apply mul_nonneg
  · exact hx
  · exact hy
  done

/- Nothing stops you from giving some of the arguments yourself and leaving the others to `apply`:
here `lt_trans : a < b → b < c → a < c` gets the first one. -/
example (x y z : ℝ) (h1 : x < y) (h2 : y < z) : x < z := by
  apply lt_trans h1
  exact h2
  done

/-!
## The `have` tactic

`have h : P := ...` proves the intermediate statement `P` and adds it to the context under the name
`h`, exactly like "we first show that ..." on paper. This is what keeps long proofs readable.
-/

/- After the `:=` comes a proof of `P`: a tactic proof of its own, opened by `by` and indented
under the `have`. -/
example (x y : ℝ) (hx : 0 ≤ x) (h : x < y) : 0 ≤ y := by
  have hxy : x ≤ y := by
    exact le_of_lt h
    done
  exact le_trans hx hxy
  done

/- The intermediate statement is up to you: here it rewrites the `7` of the goal as `x + 4`,
which is what makes `h` usable. -/
example (x y : ℝ) (hx : x + 4 = 7) (h : x + 4 + y = 5) : 7 + y = 5 := by
  have h7 : 7 + y = x + 4 + y := by
    rw [hx]
    done
  rw [h7]
  exact h
  done

/-!
## The `contradiction` tactic

`contradiction` closes *any* goal by finding an impossible hypothesis in the context: a proof of
`False`, a hypothesis together with its negation, or something of the form `h : a ≠ a`.
-/

/- `h` and `h'` cannot both hold, so we do not have to worry about the goal at all. -/
example (x : ℝ) (h : x < 0) (h' : ¬ x < 0) : x = 42 := by
  contradiction
  done

/- The extreme case: from `False`, anything follows. -/
example (P : Prop) (h : False) : P := by
  contradiction
  done

/- `contradiction` does no mathematics: it only spots hypotheses that are incompatible on the nose.
Here too `h` and `h'` cannot both hold, but seeing that needs a lemma relating `≤` and `<`, so the
tactic gives up. The error below is deliberate: read it in the Infoview. -/
example (x : ℝ) (h : x ≤ 3) (h' : x > 3) : x = 42 := by
  contradiction
  done

/- Put the two hypotheses in the same shape first, and it works again: `not_lt : ¬a < b ↔ b ≤ a`
turns `h` into `¬ 3 < x`, which is the negation of `h'`. -/
example (x : ℝ) (h : x ≤ 3) (h' : x > 3) : x = 42 := by
  rw [← not_lt] at h
  contradiction
  done

/-!
## The `intro` tactic

`intro` deals with goals that start with `→` or `∀`. It moves what is being assumed, or given, into
the context under the name you choose, and leaves the rest of the statement as the new goal. It is
the tactic behind "assume that ..." and "let `x` be ...".
-/

/- The goal `P → Q` says "if `P`, then `Q`", so `intro h` assumes `P`, calling it `h`. -/
example (x y : ℝ) : x < y → x ≤ y := by
  intro h
  exact le_of_lt h
  done

/- Several assumptions can be introduced at once, in the order in which they appear. -/
example (x y z : ℝ) : x < y → y < z → x < z := by
  intro h1 h2
  exact lt_trans h1 h2
  done

/- With `∀` what you introduce is an object rather than an assumption: this is "let `x` be a real
number". -/
example : ∀ x : ℝ, x ≤ x := by
  intro x
  exact le_refl x
  done

/-!
## Exercises

Every exercise below can be done with the tactics of this file — `exact`, `assumption`, `rw`,
`rfl`, `apply`, `have`, `intro`, `contradiction` and they get harder as you go down.

Each proof is `sorry` for the moment. `sorry` is the tactic that closes any goal by asking Lean to
take your word for it: the statement is accepted, but Lean marks it with the yellow warning
`declaration uses 'sorry'`. Replacing every `sorry` by a real proof is the exercise, and one is
done when its warning has gone and nothing is red.

We strongly suggest never leaving an error behind. If you want to skip an exercise, or to give up
in the middle of one, put `sorry` back: a `sorry` is only a warning, whereas a half-written proof
is an error, and a file full of red is unpleasant to work in.

Apart from the hypotheses of each statement, here is everything from Mathlib you may need. The
letters `a`, `b`, `c` stand for arbitrary numbers.

Order:

* `le_of_lt : a < b → a ≤ b`
* `le_refl a : a ≤ a`
* `le_trans : a ≤ b → b ≤ c → a ≤ c`
* `lt_trans : a < b → b < c → a < c`
* `lt_of_le_of_lt : a ≤ b → b < c → a < c`
* `le_antisymm : a ≤ b → b ≤ a → a = b`
* `not_lt : ¬ a < b ↔ b ≤ a`

Algebra:

* `add_zero a : a + 0 = a` and `zero_add a : 0 + a = a`
* `mul_one a : a * 1 = a` and `one_mul a : 1 * a = a`
* `add_pos : 0 < a → 0 < b → 0 < a + b` and `mul_pos : 0 < a → 0 < b → 0 < a * b`
* `add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b` and `mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b`
* `zero_ne_one : 0 ≠ 1`

Topology:

* `continuous_def : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s)`
-/

theorem ex_1 (x y : ℝ) (hx : 0 < x) (h : x < y) : x < y := by
  sorry
  done

theorem ex_2 (x y : ℝ) (h : x < y) : x ≤ y := by
  sorry
  done

theorem ex_3 (a b : ℕ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  sorry
  done

theorem ex_4 (x y z : ℝ) (h1 : x ≤ y) (h2 : y ≤ z) (h3 : z ≤ x) : y ≤ z := by
  sorry
  done

theorem ex_5 (a b : ℕ) (h : a = b) : b = a := by
  sorry
  done

theorem ex_6 (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  sorry
  done

theorem ex_7 (x : ℝ) : x * 1 + 0 = x := by
  sorry
  done

theorem ex_8 (x y : ℝ) (h : x = y) : x + 0 = y := by
  sorry
  done

theorem ex_9 (x y : ℝ) (h : y = x) (h' : y ≤ 0) : x ≤ 0 := by
  sorry
  done

theorem ex_10 (x y : ℝ) (h : x = y) (h' : x ≤ 3) : y ≤ 3 := by
  sorry
  done

theorem ex_11 : 5 * 5 = 25 := by
  sorry
  done

theorem ex_12 {X : Type*} (x : X) : id x = x := by
  sorry
  done

theorem ex_13 {X Y Z W : Type*} (f : X → Y) (g : Y → Z) (h : Z → W) (x : X) :
    (h ∘ g ∘ f) x = h (g (f x)) := by
  sorry
  done

theorem ex_14 (x y : ℝ) (h : x < y) : x ≤ y := by
  sorry
  done

theorem ex_15 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x + y := by
  sorry
  done

theorem ex_16 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x * y := by
  sorry
  done

theorem ex_17 (a b : ℕ) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  sorry
  done

theorem ex_18 (x y z : ℝ) (h1 : x ≤ y) (h2 : y < z) : x < z := by
  sorry
  done

theorem ex_19 (x y z : ℝ) (h1 : x < y) (h2 : y < z) : x ≤ z := by
  sorry
  done

theorem ex_20 (x y z w : ℝ) (h1 : x < y) (h2 : y < z) (h3 : z < w) : x < w := by
  sorry
  done

theorem ex_21 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y + x := by
  sorry
  done

theorem ex_22 (x y : ℝ) (h : x = y) (h' : y + 0 ≤ 3) : x ≤ 3 := by
  sorry
  done

theorem ex_23 (x : ℝ) (h : x < 0) (h' : ¬ x < 0) : x = 7 := by
  sorry
  done

theorem ex_24 (n : ℕ) (h : n ≠ n) : n = 0 := by
  sorry
  done

/- `Prop` is the type of mathematical statements, true or false: `P Q : Prop` reads "let `P` and
`Q` be statements". So `h : P` means "let us assume that `P` holds, and let us call this assumption `h`". -/
theorem ex_25 (P Q : Prop) (h : P) (h' : ¬ P) : Q := by
  sorry
  done

theorem ex_26 (x y : ℝ) (h : x = y) (h' : x ≠ y) : x = 0 := by
  sorry
  done

theorem ex_27 (x y : ℝ) : x = y → y ≤ x := by
  sorry
  done

theorem ex_28 : ∀ x : ℝ, 0 ≤ x → 0 ≤ x + 0 := by
  sorry
  done

theorem ex_29 (P : Prop) (hP : P) : ¬ (¬ P) := by
  sorry
  done

/- Hint: Rewriting with `continuous_def` turns `Continuous f` into the statement about preimages of
open sets, as in the very first example of this file. -/
theorem ex_30 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
    (hf : Continuous f) (s : Set Y) (hs : IsOpen s) : IsOpen (f ⁻¹' s) := by
  sorry
  done

theorem ex_31 (f g : ℝ → ℝ) (hf : ∀ x y : ℝ, x ≤ y → f x ≤ f y)
    (hg : ∀ x y : ℝ, x ≤ y → g x ≤ g y) : ∀ x y : ℝ, x ≤ y → (g ∘ f) x ≤ (g ∘ f) y := by
  sorry
