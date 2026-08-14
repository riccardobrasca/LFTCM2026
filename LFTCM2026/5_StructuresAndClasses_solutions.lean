import Mathlib

section Examples

-- # Two painful computations

example {G : Type*} [Group G] (g e : G) (h : g * e = g) : e = 1 := by
  calc e = 1 * e := by rw [one_mul]
      _ = g⁻¹ * g * e := by rw [← inv_mul_cancel]
      _ = g⁻¹ * (g * e) := by rw [mul_assoc]
      _ = g⁻¹ * g := by rw [h]
      _ = 1 := by rw [inv_mul_cancel]
  -- rw [← left_eq_mul, h]


example {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) := by
  constructor --we'll see later why it appears here
  intro a b
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective N b
  rw [← ha', ← hb'/- , QuotientGroup.mk'_apply, QuotientGroup.mk'_apply-/]
  simp only [QuotientGroup.mk'_apply]
  apply CommGroup.mul_comm
  -- exact QuotientGroup.Quotient.commGroup N

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

-- # Some crazy errors

/- Can you understand the error message (I'm not asking whether you understand *why* you get
the error: just what it says). -/
lemma quotComm_lemma {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

-- This is false, but at least it compiles
def quotComm_def {G : Type*} [Group G] (N : Subgroup G) : Group (G ⧸ N) := by sorry

-- And what goes on here?!?
#print continuous_fst
example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace (X × Y)] :
    Continuous (fun p : X × Y ↦ p.1) := by
  exact continuous_fst


end Examples

section Structures

-- # A wrong way to define mathematical structures

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

structure WrongSemigroup where
  carrier : Type*
  mul : carrier → carrier → carrier
  mul_assoc : ∀ (x y z : carrier), mul (mul x y) z = mul x (mul y z)

-- A `lemma` saying that `a * ((b * c) * d = (a * b) * (c * d)`
lemma assoc_mul (X : WrongSemigroup) (a b c d : X.carrier) :
    X.mul a (X.mul (X.mul b c) d) = X.mul (X.mul a b) (X.mul c d) := by
  rw [X.mul_assoc]
  rw [X.mul_assoc]

/- If something is true in a Semigroup, it will stay so in a group; so the above `lemma` should
still hold; yet...-/
lemma assoc_mul' (G : WrongGroup) (a b c d : G.carrier) :
    G.mul a (G.mul (G.mul b c) d) = G.mul (G.mul a b) (G.mul c d) := by
  -- apply assoc_mul -- it does not work!
  simp [G.mul_assoc]

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

#print Group
-- and right-clicking on it yields (the `_in_Cortona` avoids Lean complaining this already exists)
structure Group_in_Cortona (G : Type*) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

#print DivInvMonoid

-- -- whatsnew in
-- @[to_additive] -- to be uncommented later, in the `Classes` section
lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
  rw [pow_two, ← mul_assoc, h]
  simp

-- actually `mul_assoc` does not only work for groups, yet `Lean` was happy using it! *Why?*
#check mul_assoc

-- Similarly...
lemma OneOne_Cortona {A : Type*} [Monoid A] (a : A) : a * 1 * 1 = a := by simp

example {F : Type*} [NormedField F] (x : F) : x * 1 * 1 = x := by
  exact OneOne_Cortona x

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

end Structures

noncomputable section Classes
open Classical

/-
`Classes` are special `structures`, for which certain terms are stored in a database.

Each `class` type cointains a *preferred* or a *canonical* term, declared using the keyword
`instance` rather than `def`; and this term has been registered in the database to be accessible
whenever needed. For example, we want that the terms of type `Field ℝ` or `TopologicalSpace ℂ`,
representing respecitvely *a* field structure on `ℝ` and *a* topological structure on `ℂ`, are
found automatically, and are always what we expect them to be.

*Warning*: often, `Classes` have parameters, so if `G` and `H` are types, `Group G` and `Group H`
are different types!

They also enable **class type inference**, constructing a term of a certain class given a term of a
"parent" one. -/


#synth Group ℤ
#synth AddGroup ℤ
#synth AddGroup (ℤ × ℤ)
#synth TopologicalSpace ℂ

def ℂ_Cortona := ℂ
#synth TopologicalSpace ℂ_Cortona

#print One
#synth One ℤ

example : AddGroup (ℤ × ℚ) := inferInstance

-- Since finding instances is "automatic", it can be used to create new ones:
variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] in
#synth TopologicalSpace (X × Y)

variable (X Y : Type) [MetricSpace X] [MetricSpace Y] in
#synth TopologicalSpace (X × Y)

variable (X : Type) [MetricSpace X] in
#synth MetricSpace (X × ℕ)
#synth MetricSpace ℕ

/- ...but not all the time, expecially if we don't have a canonical candidate: in the following,
you can think at `((i : ι) → X i) = Π (i : ι), X_i` and `(i : ι) → MetricSpace (X i)` as a metric
structure on each of the `X_i`'s.
-/
variable (ι : Type*) (X : ι → Type*) [(i : ι) → MetricSpace (X i)]
#synth MetricSpace ((i : ι) → X i)

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

#print HAdd
-- @[inherit_doc] infixl:65 " + "   => HAdd.hAdd

/- Recall that we proved the
lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
  rw [pow_two, ← mul_assoc, h]
  rw [h]
-/
example {A : Type*} [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := by
  -- exact add_even h -- uncomment @[to_additive]
  rw [two_nsmul, ← add_assoc, h]
  simp

-- What's going on here?
example (G : Type*) [Group G] [CommGroup G] (g : G) : 1 * g = g := by
  rw [one_mul]


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

/- **¶ Exercise**
Why is the following example broken? Fix its statement, then prove it. -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (H₁ ∩ H₂) := sorry
/- **Sol.:** The error comes come the fact that "being a subgroup" is not a proposition. It is the
definition of some term! A solution would be -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (G) where
  carrier := H₁ ∩ H₂

/- **¶ Exercise**
State and prove that in every additive group, the intersection of two normal subgroups is normal:
even if you find a one-line proof, try to produce the whole term. For reasons to be explained later,
the intersection is written `⊓` and types as `\inf`. -/
example (A : Type*) [AddGroup A] (H K : AddSubgroup A) :
    H.Normal → K.Normal → (H ⊓ K).Normal := by
  -- apply AddSubgroup.normal_inf_normal
  intro hH hK
  constructor
  rintro n ⟨hnH, hnK⟩ g
  exact ⟨hH.conj_mem n hnH g, hK.conj_mem n hnK g⟩

/- **¶ Exercise**


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
  one := ⟨1, 0⟩
  one_mul := by
    rintro ⟨g, a⟩
    rw [AddMul_mul_def]
    simp only [Prod.mk.injEq, mul_eq_right, add_eq_right]
    constructor <;> rfl
  mul_one a := by
    rw [AddMul_mul_def]
    ext <;> simp <;> rfl
  inv := fun ⟨g, a⟩ ↦ ⟨g⁻¹, -a⟩
  inv_mul_cancel := by
    rintro ⟨g, a⟩
    rw [AddMul_mul_def]
    simp only [inv_mul_cancel, neg_add_cancel]
    rfl


end Exercises
