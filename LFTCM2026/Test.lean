/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import Mathlib.Tactic
import Norwich.Talk

/- This is a test file. Lean is configured correctly if you see the output "32" when
  mousing over or clicking on the next line, and you see no other errors in this file. -/
#eval 2 ^ 5

example (x : ℝ) : x - x = 0 := by simp
