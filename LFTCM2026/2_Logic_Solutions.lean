/-
Copyright (c) 2026 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

module

import Mathlib
import LFTCM2026.Preliminaries

/-!
# Logic: solutions

Solutions to the exercises in `2_Logic.lean`.
-/

/- Conjunctions and disjunctions. -/

theorem logic_ex_1 (P Q R : Prop) (h : (P ∧ Q) ∧ R) : P ∧ (Q ∧ R) := by
  constructor
  · exact h.1.1
  · constructor
    · exact h.1.2
    · exact h.2
  done

theorem logic_ex_2 (P Q R : Prop) (h : (P ∧ Q) ∨ (P ∧ R)) : P ∧ (Q ∨ R) := by
  rcases h with hPQ | hPR
  · constructor
    · exact hPQ.1
    · left
      exact hPQ.2
  · constructor
    · exact hPR.1
    · right
      exact hPR.2
  done

theorem logic_ex_3 (P Q R : Prop) (h : P ∨ (Q ∧ R)) : (P ∨ Q) ∧ (P ∨ R) := by
  rcases h with hP | hQR
  · constructor
    · left
      exact hP
    · left
      exact hP
  · constructor
    · right
      exact hQR.1
    · right
      exact hQR.2
  done

theorem logic_ex_4 (P Q R S : Prop) (h : P ∨ Q) (hPR : P → R) (hQS : Q → S) : R ∨ S := by
  rcases h with hP | hQ
  · left
    exact hPR hP
  · right
    exact hQS hQ
  done

/- Negation and `exfalso`. -/

theorem logic_ex_5 (P Q R : Prop) (hPQ : P → Q) (hQR : Q → R) (hnR : ¬ R) : ¬ P := by
  intro hP
  have hQ : Q := hPQ hP
  have hR : R := hQR hQ
  exact hnR hR
  done

theorem logic_ex_6 (P Q : Prop) : ¬ (P ∧ Q ∧ ¬ P) := by
  intro h
  exact h.2.2 h.1
  done

theorem logic_ex_7 (P Q : Prop) (h : (P ∨ Q) ∧ ¬ P) : Q := by
  rcases h.1 with hP | hQ
  · exfalso
    exact h.2 hP
  · exact hQ
  done

theorem logic_ex_8 (P Q R : Prop) (h : P ∨ Q) (hnP : ¬ P) (hnQ : ¬ Q) : R := by
  rcases h with hP | hQ
  · exfalso
    exact hnP hP
  · exfalso
    exact hnQ hQ
  done

/- Proof by contradiction. -/

theorem logic_ex_9 (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q := by
  intro hP
  by_contra hnQ
  have hnP : ¬ P := h hnQ
  exact hnP hP
  done

theorem logic_ex_10 (P Q : Prop) (h : (P → Q) → P) : P := by
  by_contra hnP
  have hPQ : P → Q := by
    intro hP
    contradiction
  have hP : P := h hPQ
  contradiction
  done

theorem logic_ex_11 (x : ℝ) (h : ∀ y : ℝ, x * y = 0) : x = 0 := by
  by_contra hx
  have h1 : x * 1 = 0 := h 1
  rw [mul_one] at h1
  contradiction
  done

/- Pushing negations. -/

theorem logic_ex_12 (P Q R : Prop) (hnP : ¬ P) (hQR : Q → ¬ R) :
    ¬ (P ∨ (Q ∧ R)) := by
  push Not
  constructor
  · exact hnP
  · exact hQR
  done

theorem logic_ex_13 (P Q R : Prop) (h : ¬ (P ∨ (Q ∧ R))) (hQ : Q) : ¬ P ∧ ¬ R := by
  push Not at h
  constructor
  · exact h.1
  · exact h.2 hQ
  done

theorem logic_ex_14 {X : Type*} (P Q : X → Prop) (h : ¬ ∃ x, P x ∧ Q x)
    (hP : ∀ x, P x) : ∀ x, ¬ Q x := by
  push Not at h
  intro x
  exact h x (hP x)
  done

theorem logic_ex_15 (x y z w : ℝ) (h : ¬ (x ≤ y ∨ z ≤ w)) :
    0 < (x - y) * (z - w) := by
  push Not at h
  apply mul_pos
  · rw [sub_pos]
    exact h.1
  · rw [sub_pos]
    exact h.2
  done

/- Splitting with `by_cases`. -/

theorem logic_ex_16 (P Q : Prop) (h : ¬ P → Q) : P ∨ Q := by
  by_cases hP : P
  · left
    exact hP
  · right
    exact h hP
  done

theorem logic_ex_17 (P Q : Prop) (hP : P → Q) (hnP : ¬ P → Q) : Q := by
  by_cases h : P
  · exact hP h
  · exact hnP h
  done

theorem logic_ex_18 {X : Type*} (A B C : Set X)
    (hinside : A ∩ B = C ∩ B) (houtside : A \ B = C \ B) : A = C := by
  apply Set.ext
  intro x
  constructor
  · intro hxA
    by_cases hxB : x ∈ B
    · have hx : x ∈ A ∩ B := by
        constructor
        · exact hxA
        · exact hxB
        done
      rw [hinside] at hx
      exact hx.1
    · have hx : x ∈ A \ B := by
        constructor
        · exact hxA
        · exact hxB
        done
      rw [houtside] at hx
      exact hx.1
  · intro hxC
    by_cases hxB : x ∈ B
    · have hx : x ∈ C ∩ B := by
        constructor
        · exact hxC
        · exact hxB
        done
      rw [← hinside] at hx
      exact hx.1
    · have hx : x ∈ C \ B := by
        constructor
        · exact hxC
        · exact hxB
        done
      rw [← houtside] at hx
      exact hx.1
  done

/- Set-theoretic challenges. -/

theorem logic_ex_19 {X : Type*} (A B C : Set X) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with hxA | hxBC
    · constructor
      · left
        exact hxA
      · left
        exact hxA
    · constructor
      · right
        exact hxBC.1
      · right
        exact hxBC.2
  · intro hx
    rcases hx.1 with hxA | hxB
    · left
      exact hxA
    · rcases hx.2 with hxA | hxC
      · left
        exact hxA
      · right
        constructor
        · exact hxB
        · exact hxC
  done

theorem logic_ex_20 {X : Type*} (A B C : Set X) :
    A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    constructor
    · constructor
      · exact hx.1
      · intro hxB
        apply hx.2
        left
        exact hxB
    · constructor
      · exact hx.1
      · intro hxC
        apply hx.2
        right
        exact hxC
  · intro hx
    constructor
    · exact hx.1.1
    · intro hxBC
      rcases hxBC with hxB | hxC
      · exact hx.1.2 hxB
      · exact hx.2.2 hxC
  done

theorem logic_ex_21 {X : Type*} (A B : Set X) : (A ∩ B) ∪ (A \ B) = A := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    rcases hx with hxAB | hxAB
    · exact hxAB.1
    · exact hxAB.1
  · intro hxA
    by_cases hxB : x ∈ B
    · left
      constructor
      · exact hxA
      · exact hxB
    · right
      constructor
      · exact hxA
      · exact hxB
  done
