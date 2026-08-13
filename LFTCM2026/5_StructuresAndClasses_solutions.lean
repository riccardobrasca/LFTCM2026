import Mathlib

set_option linter.unusedVariables false
set_option linter.overlappingInstances false
set_option warn.classDefReducibility false

section examples

-- # Examples to start with

-- ## Two painful computations

example {G : Type*} [Group G] (g e : G) (h : g * e = g) : e = 1 := by
  calc e = 1 * e := by rw [one_mul]
      _ = g⁻¹ * g * e := by rw [← inv_mul_cancel]
      _ = g⁻¹ * (g * e) := by rw [mul_assoc]
      _ = g⁻¹ * g := by rw [h]
      _ = 1 := by rw [inv_mul_cancel]
  -- rw [← left_eq_mul, h]


example {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) := by
  constructor
  intro a b
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective N b
  rw [← ha', ← hb'/- , QuotientGroup.mk'_apply, QuotientGroup.mk'_apply-/]
  simp only [QuotientGroup.mk'_apply]
  apply CommGroup.mul_comm
  -- exact QuotientGroup.Quotient.commGroup N

-- ## `Lean` is not so stupid after all... but how?

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Group Y] [IsTopologicalGroup Y]
    (f g h : X → Y) : Continuous f → Continuous g → Continuous h → Continuous (f * g / h) := by
  intro hf hg hh
  apply Continuous.div'
  · apply Continuous.mul
    · exact hf
    exact hg
  · exact hh
  -- fun_prop

-- ## Some crazy errors


/- Can you understand the error message (I'm not asking whether you understand *why* you get
the error: just what it says). -/
lemma quotComm_lemma {G : Type*} [Group G] (N : Subgroup G) : CommGroup (G ⧸ N) := by sorry

-- This is false, but at least it compiles
def quotComm_def {G : Type*} [Group G] (N : Subgroup G) : Group (G ⧸ N) := by sorry


#print continuous_fst

example (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace (X × Y)] :
    Continuous (fun p : X × Y ↦ p.1) := by
  exact continuous_fst


-- `⌘`
end examples

section Groups

-- ## A wrong way to define mathematical structures

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

-- If something is true in a Semigroup, it will stay so in a group; yet...
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

-- `⌘`

-- ## A right way to define mathematical structures

#print Group
-- and right-clicking on it yields (the `_in_Cortona` avoids Lean complaining this already exists)
structure Group_in_Cortona (G : Type*) extends DivInvMonoid G where
  protected inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1

#print DivInvMonoid

-- -- whatsnew in
-- -- @[to_additive] -- to be uncommented later, in the `Classes` section
-- lemma mul_square {G : Type*} [Group G] {x y : G} (h : x * y = 1) : x * y ^ 2 = y := by
--   rw [pow_two]
--   rw [← mul_assoc]
--   rw [h]
--   group


-- actually `mul_assoc` does not only work for groups.
#check mul_assoc

/- **FAE** : Add a couple of examples showing this `Group` behaves nicely (eg with inheritance
from `Monoid` or  something) and look at `Iff` and `And` as `structures.
-/

-- example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
--   group
--
-- #print CommGroup
-- -- and right-clicking on it yields
-- structure CommGroup_in_Cortona (G : Type*) extends Group G, CommMonoid G
--
-- example {G : Type*} [CommGroup G] (x y : G) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
--   -- group
--   rw [mul_inv_rev, mul_comm]
--   -- rw [mul_inv]
--
-- example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
--   abel
--
--

-- `⌘`

-- ## Classes
/- **FAE** Add topological examples for classes, like `DiscreteTopology` or the product on `X × Y`
or the topology induced from a metric space. Perhaps observe that there is no Metric structure
on a product, and discuss why. -/

example {A : Type*} [AddGroup A] (x y : A) : x + y + 0 = x + y := by
  -- group
  simp only [add_zero] -- when does `add_zero` hold?

#print HAdd
-- @[inherit_doc] infixl:65 " + "   => HAdd.hAdd

#synth Group ℤ
#synth AddGroup ℤ
#synth AddGroup (ℤ × ℤ)

#print One
#synth One ℤ

example : AddGroup (ℤ × ℚ) := inferInstance

example {A : Type*} [AddGroup A] {a b : A} (h : a + b = 0) : a + 2 • b = b := by
  -- exact add_even h -- uncomment @[to_additive]
  rw [two_nsmul, ← add_assoc, h]
  simp

-- What's going on here?
example (G : Type*) [Group G] [CommGroup G] (g : G) : 1 * g = g := by
  rw [one_mul]

-- -- #### The `Coe` class
-- #check Complex.exp_add_pi_mul_I (3/2 : ℚ)
-- #print RatCast
-- #synth RatCast ℂ
--
-- -- Anonymous function def!
-- instance : Coe WrongGroup Type where
--   coe := (·.carrier)

-- instance : CoeSort WrongGroup Type where
--  coe := (·.carrier)


-- example {α : WrongGroup} (x : α) :
--     α.mul x (α.inv x) = α.one := by
--   rw [← α.inv_mul_cancel (α.inv x), α.inv_eq_of_mul _ _ (α.inv_mul_cancel x)]

instance : Add Bool where
  add b₁ b₂ := b₁ && b₂

example : true + false = false := by rfl

-- `⌘`
--
-- -- ### More about groups
--
-- variable (G : Type*) [Group G]
--
-- -- #### Subgroups
-- example (H : Subgroup G) : Group H := inferInstance
--
-- variable (H : Subgroup G) in
-- #synth Group H
--
-- /- We have an automatic coercion from sets to types (more about this in the next class),
-- so we get a coercion from subgroups to types: -/
-- example (H : Subgroup G) (x : H) (hx : x = 1) : (x : G) = 1 := by
--   simp [hx]
--
-- example (H : Subgroup G) : 1 ∈ H := H.one_mem
--
-- /- Observe what happens if one writes
--
--   `AddSubgroup ℤ :=`
--   `_`
--
-- -/
-- example : AddSubgroup ℤ where
--   carrier := {n : ℤ | Even n}
--   add_mem' := by
--     intro a b ha hb
--     -- simp at ha hb --not needed, actually
--     simp only [Even] at ha hb
--     obtain ⟨m, hm⟩ := ha
--     obtain ⟨n, hn⟩ := hb
--     rw [hn, hm]
--     use n + m
--     abel
--     -- grind
--   zero_mem' := ⟨0, by abel⟩
--   neg_mem' {x} hx := by
--     obtain ⟨r, _⟩ := hx
--     exact ⟨-r, by simp_all⟩
--
-- /- In the example below, note two things:
-- 1. What happens if we remove `Comm`;
-- 2. What happens to the `G` and `Group G` that are globally defined in this section;
-- -/
-- example (G : Type*) [CommGroup G] (H₁ H₂ : Subgroup G) {x y : G} (hx : x ∈ H₁) (hy : y ∈ H₂) :
--     x * y ∈ H₁ ⊔ H₂ := by
--   rw [Subgroup.mem_sup]
--   use x, hx, y, hy
--
-- example (x : G) (hx : x ∈ (⊥ : Subgroup G)) : x = 1 := Subgroup.mem_bot.mp hx
--
--
-- ---Let's discuss **dot notation**.
-- example : (Subgroup.center G).Normal := by
-- -- #print Subgroup.Normal
--   apply Subgroup.Normal.mk
--   intro z hz g
--   let hz' := hz
--   rw [Subgroup.mem_center_iff] at hz --this looses hz
--   specialize hz g
--   rw [← mul_inv_eq_iff_eq_mul] at hz
--   rwa [hz]
--   -- exact Subgroup.instNormalCenter
--
-- -- `⌘`


-- ## Exercises

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

end Exercises
