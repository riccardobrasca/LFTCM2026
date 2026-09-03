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
  group -- this works for **free groups**
  done


example {G : Type*} [CommGroup G] (x y : G) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  -- group -- the group is commutative!
  rw [mul_inv_rev, mul_comm]
  -- rw [mul_inv]
  done

example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
  abel
  done

/- All this is very nice, but are we *duplicating* the whole library for both additive and
multiplicative groups? -/
-- -- whatsnew in
-- @[to_additive]
lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
  rw [pow_two, ← mul_assoc, h]
  simp
  done

example {A : Type*} [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := by
  -- exact add_even h -- uncomment @[to_additive]
  rw [two_nsmul, ← add_assoc, h]
  simp
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
example (H : Subgroup G) : Group H := inferInstance

variable (H : Subgroup G) in
#synth Group H

-- The following two examples seem to say something stupid, but for Lean it's an effort!
example (H : Subgroup G) (x : H) (hx : x = 1) : (x : G) = 1 := by -- are the two `1`'s the same?
  simp [hx]
  done

example (H : Subgroup G) : 1 ∈ H := H.one_mem

-- Let's define `2ℤ` as a term of `Subgroup ℤ`... (almost doable!)
example : AddSubgroup ℤ where
  carrier := {n : ℤ | Even n}
  add_mem' := by
    intro a b ha hb
    -- simp at ha hb --not needed, actually
    simp only [Even] at ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    rw [hn, hm]
    use n + m
    abel
    -- grind
    done
  zero_mem' := ⟨0, by abel⟩
  neg_mem' {x} hx := by
    obtain ⟨r, _⟩ := hx
    exact ⟨-r, by simp_all⟩
    done

/- In the example below, note two things:
1. What happens if we remove `Comm`;
2. What happens to the `G` and `Group G` that are globally defined in this section;
-/
example (G : Type*) [CommGroup G] (H₁ H₂ : Subgroup G) {x y : G} (hx : x ∈ H₁) (hy : y ∈ H₂) :
    x * y ∈ H₁ ⊔ H₂ := by
  rw [Subgroup.mem_sup]
  use x, hx, y, hy
  done


---Let's discuss **dot notation**.
example : (Subgroup.center G).Normal := by
-- #print Subgroup.Normal
  apply Subgroup.Normal.mk
  intro z hz g
  let hz' := hz
  rw [Subgroup.mem_center_iff] at hz --this looses hz
  specialize hz g
  rw [← mul_inv_eq_iff_eq_mul] at hz
  rwa [hz]
  -- exact Subgroup.instNormalCenter
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
-- whatsnew in
-- @[to_additive __]
example (G₁ : Type) [CommGroup G₁] (f : G →* G₁) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by
  intro x y h
  rw [← map_mul, h, map_one]
  done

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
  -- rw [mul_one]
  -- rw [← add_assoc]
  ring
  done


#check mul_one
#check add_assoc
#print AddMonoid
#print Field
#print IsDomain
#print CommMonoid


example (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
  -- exact? ==> exact add_pow_two x y
  done

lemma sixth_pow (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 6 =
    x ^ 6 + 6 * x ^ 5 * y +  15 * x ^ 4 * y ^ 2 + 20 * x ^ 3 * y ^ 3 +
      15 * x ^ 2 * y ^ 4 + 6 * x * y ^ 5 + y ^ 6 := by
  -- exact?
  -- grind
  ring
  done


example (R : Type*) [CommRing R] (x y : R) (H : x ^ 2 ≠ y ^ 2) : x ≠ y := by
  -- ring
  grind
  done

variable {R S : Type*} [CommRing R] [CommRing S]

example (f : R →+* S) (r : R) : IsUnit r → IsUnit (f r) := by
  unfold IsUnit
  -- use r -- the arrow `↑u` is there for a reason...
  intro h
  -- obtain ⟨v, hv⟩ := h -- probably not enough: what does it mean `v : Rˣ`? Let's hover on it...
  obtain ⟨⟨v, u, hvu, huv⟩, H⟩ := h
  -- simp only at H
  fconstructor
  · use f r
    · use (f u)
    · rw [← map_mul, ← H, hvu, map_one]
    · rw [← map_mul, ← H, huv, map_one]
  · simp
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
  -- c * x + y ∈ T := sorry -- **why this does not work?** The `*` should be a `•`
    c • x + y ∈ T := by
  intro hx hy
  -- exact T.add_mem (T.smul_mem c hx) hy
  apply Submodule.add_mem
  apply Submodule.smul_mem
  assumption
  assumption
  done


example (f : K →ₗ[K] K) : ∃ c, f = (fun x ↦ c • x) := by --what is going on?
-- example (f : K →ₗ[K] K) : ∃ c, f = .mulLeft K c := by
--what happens without the `.` in `mulLeft`? Why?
  use f 1
  ext
  simp
  done

/- Let's try to state that "the collection of linear maps from `V` to `W` that vanish on a
subspace `T ≤ V` form a linear/vector subspace of all linear maps.
-/
variable (W : Type*) [AddCommGroup W] [Module K W] in
-- theorem Annihilator_Submodule (T : Subspace K V) :
--   Submodule K {f : V →ₗ[K] W | ∀ x ∈ T, f x = 0} := sorry
/- **Indeed**: it must be a `def`: note, in passing, that Lean accepts that `(V →ₗ[K] W)`
  is a module. -/
def AnnihilatorSubmodule (T : Subspace K V) : Submodule K (V →ₗ[K] W) where
  carrier := {f : V →ₗ[K] W | ∀ x ∈ T, f x = 0}
  add_mem' {f g} hf hg x hx := by
    simp at hf hg ⊢
    grind
    done
  zero_mem' := by simp
  smul_mem' c {f} hf := by
    simp_all
    done


end VectorSpaces


section ZModn

/- ##ZMod
We don't have time in this class to discuss how *quotients* are defined, but you can easily imagine
that everything exists (and probably will have something to do with `structure`s and `class`es...)
Just to get a feeling, here are three small examples of results in `ℤ/nℤ`. -/

lemma exists_b_mul_zero (a n : ℕ) (H : ¬ Nat.Coprime a n) : ∃ b : ℕ, (a * b : (ZMod n)) = 0 := by
  rw [Nat.Coprime, Nat.gcd_eq_one_iff] at H
  push Not at H
  -- obtain ⟨c, hc₁, hc₂, hc₃⟩ := H
  obtain ⟨c, ⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, hc₁⟩ := H
  rw [hb₁]
  use b₂
  rw_mod_cast [mul_assoc, mul_comm b₁, ← mul_assoc, ← hb₂]
  rw [ZMod.natCast_eq_zero_iff]
  use b₁
  done

example (a n : ℕ) (H : ¬ Nat.Coprime a n) : ∃ b, (a * b : ℤ ⧸ (Ideal.span {(n : ℤ)})) = 0 := by
  obtain ⟨b, hb⟩ := exists_b_mul_zero a n H
  use b
  -- exact hb
  let φ := Int.quotientSpanEquivZMod n
  apply_fun φ
  simpa
  done

example (a n : ℕ) (H : ¬ Nat.Coprime a n) : ∃ b : ℕ,
    ((a * b) : ℤ ⧸ (Ideal.span {(n : ℤ)})) = 0 := by
  suffices h : ∃ b : ℕ, Ideal.Quotient.mk (Ideal.span {(n : ℤ)}) ((a * b) : ℤ) = 0 by
    obtain ⟨b, hb⟩ := h
    use b
    exact hb
  simp_rw [Ideal.Quotient.eq_zero_iff_dvd]
  rw [Nat.Coprime, Nat.gcd_eq_one_iff] at H
  push Not at H
  obtain ⟨c, ⟨b₁, hb₁⟩, ⟨b₂, hb₂⟩, hc₁⟩ := H
  rw [hb₂, hb₁]
  exact ⟨b₂, b₁, by grind⟩
  done


end ZModn


noncomputable section Exercises
open Function


/- **¶ Exercise**
Why is the following example broken? Fix its statement, then prove it. -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (H₁ ∩ H₂) := sorry
/- **Sol.:** The error comes come the fact that "being a subgroup" is not a proposition. It is the
definition of some term! A solution would be -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (G) where
  carrier := H₁ ∩ H₂


-- **¶ Exercise**
open Function in
example (A : Type*) [AddGroup A] (f : A →+ ℤ) (hf : 1 ∈ f.range) : Surjective f := by
  rcases hf with ⟨b, hb⟩
  intro m
  use m • b
  simp [map_zsmul, hb]
  done


/- **¶ Exercise**
Prove the claim made in class that a monoid homomorphism between groups respects the inverse. -/
example (G H : Type*) [Group G] [Group H] (f : MonoidHom G H) (x : G) : f x⁻¹ = (f x)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← f.map_mul, inv_mul_cancel, f.map_one]
  done

-- **¶ Exercise**
/- The kernel of a ring homomorphism is an ideal: what is an ideal is part of the exercise... -/
def kernel (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S) : Ideal R where
  carrier := {r : R | f r = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add]
    rw [hb, ha, zero_add]
    done
  zero_mem' := by
    apply map_zero
    done
  smul_mem' := by
    intro c x hx
    simp only [smul_eq_mul, Set.mem_ofPred_eq, map_mul]
    rw [hx, mul_zero]
    done

/- **¶ Exercise**
State and that a group is commutative if and only if the map `x ↦ x⁻¹` is a group homomorphism:
even if you find a one-line proof, try to produce the whole term. To get `⁻¹`, type `\-1`. It can
be easier to split this `if and only if` statement in two declarations: are they both lemmas, both
definitions, a lemma and a definition?. -/
def inv_hom_of_comm (G : Type*) [CommGroup G] : G →* G where
  toFun := (·)⁻¹
  map_one' := by simp
  map_mul' x y := by
    simp [← mul_inv_rev, mul_comm]
    done

def comm_of_inv_hom (G : Type*) [Group G] (f : G →* G) (hf : ∀ x, f x = x⁻¹) :
    CommGroup G where
  mul_comm g h := by
    have h1 := hf (g * h)
    rwa [mul_inv_rev, map_mul, hf, hf, inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq,
      eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul] at h1
    done

/- **¶ Exercise**
Prove that the homomorphisms between commutative monoids have a structure of commutative monoid. -/
example (M N : Type*) [CommMonoid M] [CommMonoid N] : CommMonoid (M →* N) where
  npow_zero := by simp
  npow_succ := by
    intros
    rw [Monoid.npow_succ]
    done
  mul := by
    intro f g
    fconstructor
    · use fun x ↦ f x * g x
      simp
    · intro x y
      simp [map_mul, mul_assoc _ (f y) _, mul_comm (f y) _, ← mul_assoc]
    done
  mul_assoc := by
    intro f g h
    ext x
    simp only [MonoidHom.mul_apply]
    exact mul_assoc ..
    done
  one := by
    fconstructor
    · use fun _ ↦ 1
    · intro x y
      simp
    done
  one_mul := by simp
  mul_one := by simp
  mul_comm := by
    intro f g
    ext x
    simp only [MonoidHom.mul_apply]
    exact mul_comm ..
    done


/- **¶ Exercise**
Prove that an injective and surjective group homomorphism is an isomorphism:
but what's an isomorphism? -/
def IsoOfBijective (G H : Type*) [Group G] [Group H] (f : G →* H)
    (h_surj : Surjective f) (h_inj : Injective f) : G ≃* H := by
  set g : G ≃ H := by
    apply Equiv.ofBijective f
    simp [Bijective, h_inj, h_surj] with hg
  use g
  intro x y
  simp only [hg, Equiv.toFun_as_coe]
  grind
  done

/- **¶ Exercise**
State and prove that the image of an ideal through a surjective ring homomorphism is an ideal. -/
def image_ideal {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R)
    (hf : Surjective f) : Ideal S where
  carrier := f.1 '' I
  add_mem' := by
    intro x y hx hy
    obtain ⟨a, ha_mem, hax⟩ := hx
    obtain ⟨b, hb_mem, hby⟩ := hy
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Set.mem_image, SetLike.mem_coe]
    use a + b
    constructor
    · apply I.add_mem
      · exact ha_mem
      · exact hb_mem
    · rw [map_add, ← hax, ← hby]
      simp
    done
  zero_mem' := by
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Set.mem_image, SetLike.mem_coe]
    use 0
    constructor
    · apply I.zero_mem
    apply map_zero
    done
  smul_mem' := by
    intro s x hx
    obtain ⟨a, ha_mem, hax⟩ := hx
    obtain ⟨r, hr⟩ := hf s
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, smul_eq_mul, Set.mem_image,
      SetLike.mem_coe]
    use r * a
    constructor
    · apply I.mul_mem_left
      exact ha_mem
    · rw [map_mul, hr, ← hax]
      rfl
    done

/- **¶ Exercise**
This is the standard fact that an ideal containing a unit is the whole ring. -/
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (r : R) :
    r ∈ I → IsUnit r → I = ⊤ := by
  intro h_mem h
  obtain ⟨⟨u, v, huv, hvu⟩, H⟩ := h
  simp only at H
  ext x
  constructor
  · intro hx
    simp only [Submodule.mem_top]
  · intro hx
    set y := r * x with hy
    have : y ∈ I := by
      rw [hy]
      rw [mul_comm]
      apply I.mul_mem_left
      exact h_mem
    apply_fun (fun t ↦ v • t) at hy
    rw [← H] at hy
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc _ u, hvu, one_mul] at hy
    rw [← hy]
    -- rw [← smul_eq_mul]
    -- apply I.smul_mem
    apply I.mul_mem_left
    exact this
  done


/- **¶ Exercise**
**State** and **show** that a linear map is injective if and only if it has trivial kernel: try
first to do the whole proof by hand, and then to find it in Mathlib. -/
example (K V W : Type*) [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]
    (f : V →ₗ[K] W) : Injective f ↔ f.ker = ⊥ := by
    -- (f.ker_eq_bot_iff).symm
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext x
    -- simp [Submodule.mem_bot]
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · apply h
      rw [map_zero]
      apply hx
    · rw [hx]
      apply zero_mem
  · intro x y H
    rwa [← sub_eq_zero, ← map_sub, ← f.mem_ker, h, Submodule.mem_bot, sub_eq_zero] at H


-- **¶ Exercise**
variable (K V W : Type*) [Field K] [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W] in
/- Ok, this exists in the library: can we understand it in detail? In other words: write it
down by hand after understanding what all this is about. -/
example : SMul K (V →ₗ[K] W) := by
  constructor
  intro c f
  exact {
  toFun := fun v ↦ c • f v
  map_add' v w := by simp
  map_smul' x v := by rw [map_smul, RingHom.id_apply, smul_comm]}
  done


-- **¶ Exercise**
/- For the following exercise, you might need `erw` which is a stronger version of `rw`, in
case you **really really* think that `rw` should work, but it's not working. Similarly, consider
the tactic `rw_mod_cast` when you want to rewrite something but some `↑` is preventing you. All in
all, the exercise is a bit of a fight around the problem that `ℕ` and `ℤ` differ. -/
example (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    IsUnit (p : (ℤ ⧸ Ideal.span {(q : ℤ)})) := by
  have : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [← Nat.isCoprime_iff_coprime, IsCoprime] at this
  obtain ⟨a, b, H⟩ := this
  apply IsUnit.of_mul_eq_one ↑a
  apply_fun (Ideal.Quotient.mk (Ideal.span {(q : ℤ)})) at H
  simp only [eq_intCast, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one] at H
  erw [mul_comm, ← H, left_eq_add, Ideal.Quotient.eq_zero_iff_dvd]
  simp
  done


end Exercises
