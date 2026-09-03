/-
Copyright (c) 2026 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import Mathlib

/- # Algebra (and Number Theory)
The goal of today's lecture is to discuss some algebraic structures: (Sub)Groups, Rings and Vector
Spaces. If time permits (and it won't) we might discuss a bit of modular arithmetic.
-/

section Groups

/- ## Groups
We've already seen in the last lecture how to *define* groups. Let's see how to play with them.
-/

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  sorry
  done


example {G : Type*} [CommGroup G] (x y : G) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  sorry
  done

example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
  sorry
  done

/- All this is very nice, but are we *duplicating* the whole library for both additive and
multiplicative groups?. -/

-- `⌘`
lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
  sorry
  done

example {A : Type*} [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := by
  sorry
  done

/- ### Subgroups
Given all the stress I put in saying **we must use structures**, you might imagine how we
begin to define what a subgroup is...
-/
#print Subgroup
/-
structure Subgroup.{u_3} (G : Type u_3) [Group G] : Type u_3
number of parameters: 2
parents:
  Subgroup.toSubmonoid : Submonoid G
fields:
  Subsemigroup.carrier : Set G
  Subsemigroup.mul_mem' : ∀ {a b : G}, a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
  Submonoid.one_mem' : 1 ∈ self.carrier
  Subgroup.inv_mem' : ∀ {x : G}, x ∈ self.carrier → x⁻¹ ∈ self.carrier
constructor:
  Subgroup.mk.{u_3} {G : Type u_3} [Group G] (toSubmonoid : Submonoid G)
    (inv_mem' : ∀ {x : G}, x ∈ toSubmonoid.carrier → x⁻¹ ∈ toSubmonoid.carrier) : Subgroup G
field notation resolution order:
  Subgroup, Submonoid, Subsemigroup

Concretely, there are *four* fields: a `carrier` (which is a set in `G`) and three proofs that
this `carrier` is stable with respect to the operations. So **a subgroup is a quadruple**:
-/
variable (G : Type*) [Group G] (H : Subgroup G)
#check H.carrier
#check H.mul_mem'
#check H.one_mem'
#check H.inv_mem'

-- And, hopefully, a subgroup is *also* a group:
example (H : Subgroup G) : Group H := sorry

variable (H : Subgroup G) in
#synth Group H

-- The following two examples seem to say something stupid, but for Lean it's an effort!
example (H : Subgroup G) (x : H) (hx : x = 1) : (x : G) = 1 := by -- are the two `1`'s the same?
  sorry
  done

example (H : Subgroup G) : 1 ∈ H := H.one_mem

-- Let's define `2ℤ` as a term of `Subgroup ℤ`... (almost doable!)
example : AddSubgroup ℤ := sorry

/- In the example below, note two things:
1. What happens if we remove `Comm`;
2. What happens to the `G` and `Group G` that are globally defined in this section;
-/
example (G : Type*) [CommGroup G] (H₁ H₂ : Subgroup G) {x y : G} (hx : x ∈ H₁) (hy : y ∈ H₂) :
    x * y ∈ H₁ ⊔ H₂ := by
  sorry
  done


---Let's discuss **dot notation**.
example : (Subgroup.center G).Normal := by
  sorry
  done

/- ### Homomorphisms
Once again, a homomorphism is a collection of things: a bare function, together with the properties
that it must satisfy to be a group homomorphism. So, the *collection* of all these homomorphisms
is a `structure`, denoted `G →* H`! Note that actually we define `monoid` homomorphisms, because a
multiplicative map sending `1` to `1` automatically preserves the inverse. -/

structure MonoidHom_Cortona (M N : Type*) [Monoid M] [Monoid N] where
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)


/- Two examples of things we can say about a morphism: -/
example (G₁ : Type) [CommGroup G₁] (f : G →* G₁) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by
  sorry
  done

-- `⌘`
example (A : Type*) [AddGroup A] (f : G →* A) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by
  sorry
  done


end Groups

section Rings

/- ## Rings
The situation is very similar to the one for `Group`s: they're a class, and they have a dedicated
tactic, `ring`: it closes every goal that holds in a *free commutative ring*. There is also `grind`
that, on top of `ring` , is capable of performing (some) logical reasoning and arithmetic,
including inequalities. -/

#synth Ring ℤ
#synth CommRing ℤ
#synth Monoid ℤ
#synth AddMonoid ℤ
#check CommRing.toCommMonoid
#check CommRing.toAddCommGroupWithOne

example (a b c : ℚ) : a * (b + c * 1) = b * a + a * c := by
  sorry
  done


#check mul_one
#check add_assoc
#print AddMonoid
#print Field
#print IsDomain
#print CommMonoid


example (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  sorry
  done

lemma sixth_pow (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 6 =
    x ^ 6 + 6 * x ^ 5 * y +  15 * x ^ 4 * y ^ 2 + 20 * x ^ 3 * y ^ 3 +
      15 * x ^ 2 * y ^ 4 + 6 * x * y ^ 5 + y ^ 6 := by
  sorry
  done


example (R : Type*) [CommRing R] (x y : R) (H : x ^ 2 ≠ y ^ 2) : x ≠ y := by
  sorry
  done

variable {R S : Type*} [CommRing R] [CommRing S]

example (f : R →+* S) (r : R) : IsUnit r → IsUnit (f r) := by
  sorry
  done

end Rings

section VectorSpaces

/- We all agree that, at the end of the day, a vector space `V` over a field `K` is just a
`K`-module, but it is much better to call it a *`K`-vector space* rather than *`K`-module`...

Except that we **don't agree**.
-/

#check VectorSpace
#check vectorSpace
#check Vectorspace
#check Module

variable (K : Type*) [Field K]
#print Module --it's a class

variable (V : Type*) /- [AddCommGroup V]  -/[Module K V]
--it *requires* that `V` be a(n additive, commutative) group:


example (T : Submodule K V) (x y : V) (c : K) : x ∈ T → y ∈ T →
  c * x + y ∈ T := sorry -- **why this does not work?**
  done


example (f : K →ₗ[K] K) : ∃ c, f = (fun x ↦ c • x) := by --what is going on?
  sorry
  done

/- Let's try to state that "the collection of linear maps from `V` to `W` that vanish on a
subspace `T ≤ V` form a linear/vector subspace of all linear maps.
-/
variable (W : Type*) [AddCommGroup W] [Module K W] in
theorem Annihilator_Submodule (T : Subspace K V) :
  Submodule K {f : V →ₗ[K] W | ∀ x ∈ T, f x = 0} := sorry


end VectorSpaces


section ZModn

/- ##ZMod
We don't have time in this class to discuss how *quotients* are defined, but you can easily imagine
that everything exists (and probably will have something to do with `structure`s and `class`es...)
Just to get a feeling, here are three small examples of results in `ℤ/nℤ`. -/

lemma exists_b_mul_zero (a n : ℕ) (H : ¬ Nat.Coprime a n) : ∃ b : ℕ, (a * b : (ZMod n)) = 0 := by
  sorry
  done

example (a n : ℕ) (H : ¬ Nat.Coprime a n) : ∃ b, (a * b : ℤ ⧸ (Ideal.span {(n : ℤ)})) = 0 := by
  sorry
  done

example (a n : ℕ) (H : ¬ Nat.Coprime a n) : ∃ b : ℕ,
    ((a * b) : ℤ ⧸ (Ideal.span {(n : ℤ)})) = 0 := by
  sorry
  done


end ZModn


noncomputable section Exercises
open Function


/- **¶ Exercise**
Why is the following example broken? Fix its statement, then prove it. -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (H₁ ∩ H₂) := sorry


-- **¶ Exercise**
open Function in
example (A : Type*) [AddGroup A] (f : A →+ ℤ) (hf : 1 ∈ f.range) : Surjective f := by
  sorry
  done


/- **¶ Exercise**
Prove the claim made in class that a monoid homomorphism between groups respects the inverse. -/
example (G H : Type*) [Group G] [Group H] (f : MonoidHom G H) (x : G) : f x⁻¹ = (f x)⁻¹ := by
  sorry
  done

-- **¶ Exercise**
/- The kernel of a ring homomorphism is an ideal: what is an ideal is part of the exercise... -/
def kernel (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S) : Ideal R := sorry

/- **¶ Exercise**
State and that a group is commutative if and only if the map `x ↦ x⁻¹` is a group homomorphism:
even if you find a one-line proof, try to produce the whole term. To get `⁻¹`, type `\-1`. It can
be easier to split this `if and only if` statement in two declarations: are they both lemmas, both
definitions, a lemma and a definition?. -/


/- **¶ Exercise**
Prove that the homomorphisms between commutative monoids have a structure of commutative monoid. -/
example (M N : Type*) [CommMonoid M] [CommMonoid N] : CommMonoid (M →* N) := sorry


/- **¶ Exercise**
Prove that an injective and surjective group homomorphism is an isomorphism:
but what's an isomorphism? -/
def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
    (h_surj : Surjective f) (h_inj : Injective f) : G ≃* H := sorry


/- **¶ Exercise**
State and prove that the image of an ideal through a surjective ring homomorphism is an ideal. -/


/- **¶ Exercise**
This is the standard fact that an ideal containing a unit is the whole ring. -/
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (r : R) :
    r ∈ I → IsUnit r → I = ⊤ := by
  sorry
  done


/- **¶ Exercise**
**State** and **show** that a linear map is injective if and only if it has trivial kernel: try
first to do the whole proof by hand, and then to find it in Mathlib. -/

-- **¶ Exercise**
variable (K V W : Type*) [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W] in
/- Ok, this exists in the library: can we understand it in detail? In other words: write it
down by hand after understanding what all this is about. -/
example : SMul K (V →ₗ[K] W) := by
  sorry
  done



-- **¶ Exercise**
/- For the following exercise, you might need `erw` which is a stronger version of `rw`, in
case you **really really* think that `rw` should work, but it's not working. Similarly, consider
the tactic `rw_mod_cast` when you want to rewrite something but some `↑` is preventing you. All in
all, the exercise is a bit of a fight around the problem that `ℕ` and `ℤ` differ. -/
example (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    IsUnit (p : (ℤ ⧸ Ideal.span {(q : ℤ)})) := by
  sorry
  done


end Exercises
