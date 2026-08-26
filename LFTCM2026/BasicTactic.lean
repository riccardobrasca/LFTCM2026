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
-/

/-
Here is the statement.

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

The keyword `by` starts the proof, and `done` ends it (it's technically not needed, but when you
are starting out it is a good idea to use it).
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
