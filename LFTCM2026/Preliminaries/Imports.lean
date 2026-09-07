/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

-- Every tactic Mathlib has, plus `exact?`, `apply?`, `#leansearch` and `#loogle`. It also drags in
-- most of the elementary library the sessions use: `ℕ`, `ℤ`, `ℚ`, `ℝ`, sets, groups, rings,
-- `ZMod`, metric spaces, `Nat.fib`, and so on.
public import Mathlib.Tactic
-- Fundamental theorem of algebra, and Liouville's theorem in its import cone (session 4,
-- statements 12 and 19). This is also what brings in `ℂ`, polynomials and differentiability.
public import Mathlib.Analysis.Complex.Polynomial.Basic
-- Carathéodory's theorem, and convexity in general (session 4, statement 18).
public import Mathlib.Analysis.Convex.Caratheodory
-- Numerical bounds on `π` (`Exercises.lean`, exercise 8).
public import Mathlib.Analysis.Real.Pi.Bounds
-- Integrals of the elementary functions, and the differential calculus behind them
-- (`Exercises.lean`, exercises 7 and 9).
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
-- Harmonic series divergence (`SubtleStatement.lean`).
public import Mathlib.Analysis.PSeries
-- `SimpleGraph` and the handshake lemma (session 4, statement 9).
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
-- `Int.quotientSpanEquivZMod`, the isomorphism between `ℤ ⧸ (n)` and `ZMod n` (session 6).
public import Mathlib.Data.ZMod.QuotientRing
-- Burnside's normal complement theorem (`Exercises.lean`, exercise 10), and Sylow theory with it.
public import Mathlib.GroupTheory.Transfer
-- Chebyshev's inequality (session 4, statement 20), and measure theory and integration with it.
public import Mathlib.Probability.Moments.Variance
