/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib

/- # Structures and Classes:
Before embarking on today's class, let's see how things might *go wrong*, so that the design
choices will hopefully become clearer. -/

section Examples

-- ### Some crazy stuff


example {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) := by
  constructor --we'll see later why it appears here
  intro a b
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective N b
  rw [← ha', ← hb'/- , QuotientGroup.mk'_apply, QuotientGroup.mk'_apply-/]
  simp only [QuotientGroup.mk'_apply]
  apply CommGroup.mul_comm
  -- exact QuotientGroup.Quotient.commGroup N
  done

/- `Lean` is not so stupid after all, it understands that metric spaces have a topology...
but how is this possible? -/
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Group Y] [IsTopologicalGroup Y]
    (f g h : X → Y) : Continuous f → Continuous g → Continuous h → Continuous (f * g / h) := by
  intro hf hg hh
  apply Continuous.div'
  · apply Continuous.mul
    · exact hf
    exact hg
  · exact hh
  -- fun_prop
  done

/- Can you understand the error message (I'm not asking whether you understand *why* you get
the error: just what it says). -/
lemma quotComm_lemma {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by
  sorry
  done

-- This is false, but at least it compiles
def quotComm_def {G : Type*} [Group G] (N : Subgroup G) : Group (G ⧸ N) := by
  sorry
  done

-- And what goes on here?!?
#print continuous_fst
example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace (X × Y)] :
    Continuous (fun p : X × Y ↦ p.1) := by
  exact continuous_fst
  done


end Examples

section Structures

-- # A wrong way to define mathematical structures
/- The leitmotiv here is that in "informal" mathematics, the way we aggregate data and conditions
on these data is somewhat irrelevant. We can equally well say that
* A group is a set `G` with a preferred element `e` and a binary operation such that...
* A group law on a non-empty set `G` is the datum of a choice of some `e : G` and an operation ...
* In any of the above, we can require that `e * g = g` **and** `g * e = g` for every `g`; or just
one of the two, since one can prove that every right inverse is also a left inverse...
All these are considered *the same mathematical structure*: the choice is almost "typographical".

In a similar vein, we typically denote by `*` or `+` the operation, and in the first case we
sometimes write `e = 1`, in the second `e = 0`: but it is "clear" that the choice of the symbol
plays no role, and using `◆` and `e = §` would be good.

In Lean we need to do things differently.
-/

structure WrongGroup where
  carrier : Type*
  one : carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  mul_one : ∀ (x : carrier), mul x one = x
  one_mul : ∀ (x : carrier), mul one x = x
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)
  inv_mul_cancel : ∀ (x : carrier), mul (inv x) x = one

-- If this is how we play with products and inverses, we'd rather give up with `Lean` altogether...
lemma WrongGroup.inv_eq_of_mul {α : WrongGroup} (x y : α.carrier) :
    α.mul x y = α.one → α.inv x = y := by
  intro h
  apply_fun (fun z ↦ α.mul (α.inv x) z) at h
      -- use the `apply_fun` tactic to apply a function to both sides of a hypothesis
  rw [α.mul_one, ← α.mul_assoc, α.inv_mul_cancel, α.one_mul] at h
  exact h.symm
  done

structure WrongSemigroup where
  carrier : Type*
  mul : carrier → carrier → carrier
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)

-- A `lemma` saying that `a * ((b * c) * d = (a * b) * (c * d)`
lemma assoc_mul (X : WrongSemigroup) (a b c d : X.carrier) :
    X.mul a (X.mul (X.mul b c) d) = X.mul (X.mul a b) (X.mul c d) := by
  rw [X.mul_assoc]
  rw [X.mul_assoc]
  done

/- If something is true in a Semigroup, it will stay so in a group; so the above `lemma` should
still hold; yet...-/
lemma assoc_mul' (G : WrongGroup) (a b c d : G.carrier) :
    G.mul a (G.mul (G.mul b c) d) = G.mul (G.mul a b) (G.mul c d) := by
  -- apply assoc_mul -- it does not work!
  simp [G.mul_assoc]
  done

/- Just to finish convincing ourselves that this `WrongXXX` approach is *wrong*, let's try to
check that the usual addition makes `ℕ` into a `(Wrong)Semigroup`. -/
def Nplus : WrongSemigroup where
  carrier := ℕ
  mul := (· + ·) -- or fun x y ↦ x + y
  mul_assoc := add_assoc

example : Nplus.mul 1 1 = 2 := rfl
example : Nplus.mul (1 : Nplus) (1 : Nplus) = (2 : Nplus) := rfl
example : Nplus.mul (1 : ℕ) (1 : ℕ) = (2 : ℕ) := rfl


-- ## A right way to define mathematical structures

/- We'll focus on Groups in what follows, but just for the sake of an example: their true theory
will be discussed in the lecture about Algebra. -/
#print Group
-- and right-clicking on it yields (the `_in_Cortona` avoids Lean complaining this already exists)
structure Group_in_Cortona (G : Type*) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

#print DivInvMonoid


-- ## Our old friends ∧ and ↔ are also structures
#print And
#print Iff

example (P Q : Prop) : P ∧ Q → ((P → Q) ↔ (Q → P)) := by
  -- tauto
  · rintro ⟨hP, hQ⟩
    constructor
    · --tauto
      intro hPQ hQ'
      exact hP
    · exact fun _ _ ↦ hQ
  done

/- But how to *remember* the names and list of all fields in a structure? Of course
one can have a look in the file where it is defined, but it's painful and might be very long...
-/
def DiscreteMetric (M : Type*) : MetricSpace M where
  dist := sorry
  dist_self := sorry
  dist_comm := sorry
  dist_triangle := sorry
  edist_dist := sorry
  uniformity_dist := sorry
  cobounded_sets := sorry
  eq_of_dist_eq_zero := sorry

/- Actually, try typing just

def DiscreteMetric (M : Type*) : MetricSpace M :=
_

and follow the bulb...💡️
-/

end Structures

noncomputable section Classes
open Classical

-- ### Some magic happens!

example (G : Type*) [Group G] (x y z : G) : x * y * z * 1 = x * (y * z) * 1 := by simp [mul_assoc]

-- actually `mul_assoc` does not only work for groups, yet `Lean` was happy using it! *Why?*
#check mul_assoc

-- Similarly...
lemma OneOne_Cortona {A : Type*} [Monoid A] (a : A) : a * 1 * 1 = a := by simp

example {F : Type*} [NormedField F] (x : F) : x * 1 * 1 = x := by
  exact OneOne_Cortona x
  done

/-`Classes` are special `structures`, for which certain terms are stored in a database.

Each `class` type cointains a *preferred* or a *canonical* term, declared using the keyword
`instance` rather than `def`; and this term gets registered in the database to be accessible
whenever needed. For example, we want that the terms of type `Field ℝ` or `TopologicalSpace ℂ`,
representing respecitvely *a* field structure on `ℝ` and *a* topological structure on `ℂ`, are
found automatically, and are always what we expect them to be.

*Warning*: often, `Classes` have parameters, so if `G` and `H` are types, `Group G` and `Group H`
are different types! In particular, you don't expect the "type" `TopologicalSpace` to have an
instance (indeed, `TopologicalSpace` is not a type, it's a collection of types!): rather, you
expect the type `TopologicalSpace ℝ`, that contains all possible topologies on the set `ℝ` to
have an instance, and likely you want it to be the Euclidean topology.

Classes also enable **class type inference**, constructing a term of a certain class given a term
of a "parent" one. -/


#synth Group ℤ
#synth AddGroup ℤ
#synth AddGroup (ℤ × ℤ)
#synth TopologicalSpace ℂ

def ℂ_Cortona := ℂ
#synth TopologicalSpace ℂ_Cortona

#print One
#synth One ℤ

example : AddGroup (ℤ × ℚ) := inferInstance

-- Since finding instances is "automatic", the search can be used to create new ones:
variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] in
#synth TopologicalSpace (X × Y)

variable (X Y : Type) [MetricSpace X] [MetricSpace Y] in
#synth TopologicalSpace (X × Y) -- Lean went from `MetricSpace` to `TopologicalSpace` automatically.

variable (X : Type) [MetricSpace X] in
#synth MetricSpace (X × ℕ)
#synth MetricSpace ℕ

/- ...but not all the time, expecially if we don't have a canonical candidate: in the following,
you can think at `((i : ι) → X i) = Π (i : ι), X_i` and `(i : ι) → MetricSpace (X i)` as a metric
structure on each of the `X_i`'s.
-/
variable (ι : Type*) (X : ι → Type*) [(i : ι) → MetricSpace (X i)]
#synth MetricSpace ((i : ι) → X i) -- indeed, `Lp` spaces exist for all `p`!

variable (ι : Type*) (X : ι → Type*) [(i : ι) → Group (X i)]
#synth Group ((i : ι) → X i)

instance CortonaMetric (ι : Type*) (X : ι → Type*) [(i : ι) → MetricSpace (X i)] :
    (MetricSpace ((i : ι) → X i)) where
      dist x y := if x = y then 0 else 1
      dist_self x := by grind
      dist_comm x y := by grind
      dist_triangle x y z := by grind
      edist_dist x y := by split_ifs <;> simp_all
      eq_of_dist_eq_zero {x} {y} := by grind

variable (ι : Type*) (X : ι → Type*) [(i : ι) → MetricSpace (X i)]
#synth MetricSpace ((i : ι) → X i)


example {A : Type*} [AddGroup A] (x y : A) : x + y + 0 = x + y := by
  simp only [add_zero] -- when does `add_zero` hold?
  done

#print HAdd
-- @[inherit_doc] infixl:65 " + "   => HAdd.hAdd


-- What's going on here?
example (G : Type*) [Group G] [CommGroup G] (g : G) : 1 * g = g := by
  rw [one_mul]
  done

instance : Add Bool where
  add b₁ b₂ := b₁ && b₂

example : true + false = false := by rfl

end Classes

-- # Exercises

section Exercises

-- **Exercise**
-- Do you understand why the first of the next two lines compiles while the second
-- throws an error?
example (M : Type*) (α : Monoid M) : (1 : M) = (1 : M) := rfl
example (α : Type*) (M : Monoid α) : (1 : M) = (1 : M) := rfl
/- **Sol.:** The second equality does not make sense because `M` is a structure, so a collection of
many fields, not a type that can/cannot contain a term like `1`. -/

open Function

/- **¶ Exercise**
Re-experience the pain of playing with *wrongly-defined* groups. -/
lemma WrongGroup.mul_inv_cancel {α : WrongGroup} (x : α.carrier) :
    α.mul x (α.inv x) = α.one := by
  rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]
  done

/- **¶ Exercise**
Prove that in every additive group, the intersection of two normal subgroups is normal:
even if you find a one-line proof, try to produce the whole term. For reasons to be explained later,
the intersection is written `⊓` and types as `\inf`.

Since we haven't discussed yet
what a subgroup is, let alone a normal one, it can be useful to -/
#print Subgroup.Normal --it's a class, so in particular a structure!

example (A : Type*) [AddGroup A] (H K : AddSubgroup A) :
    H.Normal → K.Normal → (H ⊓ K).Normal := by
  -- apply AddSubgroup.normal_inf_normal
  intro hH hK
  constructor
  rintro n ⟨hnH, hnK⟩ g
  exact ⟨hH.conj_mem n hnH g, hK.conj_mem n hnK g⟩
  done

/- **¶ Exercise**
You'll soon see how `Mathlib` defines topological spaces. For this exercise, we're implementing
a toy model: a structure that I call *Cortological* spaces, where we just ask for the datum of a
collection of "opens", satisfying no intersection/union property but just obeying the requirement
that the empty set and the universal set belong to the collection. -/

-- **1** Define the structure of a Cortological space on a type `X`: should this be a class?
/- *Sol.:* : Yes, it should be a class, and here it is. -/
class CortologicalSpace (X : Type) where
  opens : Set (Set X)
  univ : Set.univ ∈ opens
  empty : ∅ ∈ opens

/- **2** Put a Cortological structure on `ℕ`, declaring that a non-empty set is "open" if it
contains arbitrarily large elements, and then prove that the intersection of two opens is open:-/
/- *Sol.:* -/
def contains_arbitrarily_large (S : Set ℕ) : Prop := ∃ N, ∀ a, N ≤ a → a ∈ S

instance : CortologicalSpace ℕ where
  opens := {∅} ∪ Set.ofPred contains_arbitrarily_large
  univ := by simp [contains_arbitrarily_large]
  empty := by simp

open CortologicalSpace in
example (X Y : Set ℕ) : X ∈ opens → Y ∈ opens → X ∩ Y ∈ opens := by
  intro hX hY
  -- rcases (Set.mem_union _ _ _).mpr hX with _ | ⟨N, hN⟩
  -- · simp_all
  -- rcases (Set.mem_union _ _ _).mpr hY with _ | ⟨M, hM⟩
  -- · simp_all
  -- right
  -- use max M N
  -- intro a ha
  -- exact ⟨hN a (by grind), hM a (by grind)⟩
  rcases (Set.mem_union _ _ _).mpr hX, (Set.mem_union _ _ _).mpr hY with
    ⟨_ | ⟨N, hN⟩, _ | ⟨M, hM⟩⟩ <;> try simp_all
  right
  use max M N
  grind
  done


open CortologicalSpace
/- **3** Make sure that if `X` and `Y` are both `CortologicalSpaces`, Lean automatically puts a
structure of `CortologicalSpace` on `X × Y`: I'm not asking any relation among this structure
and the starting structures whatsoever... (remember that this is a *toy model*!): -/

instance (X Y : Type) [CortologicalSpace X] [CortologicalSpace Y] : CortologicalSpace (X × Y) where
  opens := {.univ } ∪ {∅}
  univ := by simp
  empty := by simp

/- **4** Define the structure of punctured cortological spaces and discuss advantages and
disadvantages of making it a class (think at the product of two punctured Cortological spaces). -/
/- *Sol.:* -/
class PuncturedCortologicalSpace (X : Type) extends CortologicalSpace X where
  pt : X

/- Against the choice of making it a class, there is the remark that many Cortological Spaces can be
"punctured" in several ways, and we don't want Lean to automatically pick up a point; on the other
hand, if we make it a class, we can automatically deduce a structure of
  `PuncturedCortologicalSpace X × Y` by -/
open PuncturedCortologicalSpace in
instance (X Y : Type) [PuncturedCortologicalSpace X] [PuncturedCortologicalSpace Y] :
  PuncturedCortologicalSpace (X × Y) where
    pt := (pt, pt)

/- **¶ Exercise**
Given a multiplicative group `G` and an additive group `A`, what is the right way of putting a
multiplicative structure on `G × A` where `(g, a) * (h, b) = (g * h, a + b)`?
**HINTS:** This might be hard: a sugggestion is to do it in steps, first defining the multiplication
just as a function, then definining a `Mul` instance, then providing a trivial lemma saying
how this multiplication behaves, and then providing the final instance (where you actually don't
need to provide *all* fields, as some can be deduced automatically: try to comment them to see when
`Lean` complains).
-/

/- *Sol.:* -/
def AddMul_mul {G A : Type*} [Group G] [AddGroup A] : (G × A) → (G × A) → (G × A) :=
  fun ⟨g, a⟩ ⟨h, b⟩ ↦ ⟨g * h, a + b⟩

instance {G A : Type*} [Group G] [AddGroup A] : Mul (G × A) where
  mul := AddMul_mul

lemma AddMul_mul_def {G A : Type*} [Group G] [AddGroup A] (g h : G) (a b : A) :
    (⟨g, a⟩ : G × A) * ⟨h, b⟩ = ⟨g * h, a + b⟩ := rfl

instance {G A : Type*} [Group G] [AddGroup A] : Group (G × A) where
  mul := AddMul_mul
  mul_assoc := by
    rintro ⟨g, a⟩ ⟨h, b⟩ ⟨k, c⟩
    grind [AddMul_mul_def]
    done
  one := ⟨1, 0⟩
  one_mul := by
    rintro ⟨g, a⟩
    rw [AddMul_mul_def]
    simp only [Prod.mk.injEq, mul_eq_right, add_eq_right]
    constructor <;> rfl
    done
  mul_one a := by
    rw [AddMul_mul_def]
    ext <;> simp <;> rfl
    done
  inv := fun ⟨g, a⟩ ↦ ⟨g⁻¹, -a⟩
  inv_mul_cancel := by
    rintro ⟨g, a⟩
    rw [AddMul_mul_def]
    simp only [inv_mul_cancel, neg_add_cancel]
    rfl
    done


end Exercises
