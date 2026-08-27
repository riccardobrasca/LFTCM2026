import Mathlib

/- # Algebra
The goal of today's lecture is to discuss some algebraic structures: Groups, Rings and Vector
Spaces. If time permits (and it won't) we might discuss a bit of modular arithmetic.
-/
section Groups
/- ## Groups

-/

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group


example {G : Type*} [CommGroup G] (x y : G) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  -- group
  rw [mul_inv_rev, mul_comm]
  -- rw [mul_inv]

example {A : Type*} [AddCommGroup A] (x y : A) : x + y + 0 = x + y := by
  abel


end Groups

section More


-- ### More about groups

variable (G : Type*) [Group G]

-- #### Subgroups
/- **FAE** Add the definition of subgroup + some discussion about it not being automatically a group
Also check in file 5 that they're not used already.-/

example (H : Subgroup G) : Group H := inferInstance

variable (H : Subgroup G) in
#synth Group H

-- We have an automatic coercion from sets to types, so we get a coercion from subgroups to types:
example (H : Subgroup G) (x : H) (hx : x = 1) : (x : G) = 1 := by
  simp [hx]

example (H : Subgroup G) : 1 ∈ H := H.one_mem

-- **FAE** This is important and must come up in **File 5**!!!
/- Observe what happens if one writes

  `AddSubgroup ℤ :=`
  `_`

-/
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
  zero_mem' := ⟨0, by abel⟩
  neg_mem' {x} hx := by
    obtain ⟨r, _⟩ := hx
    exact ⟨-r, by simp_all⟩

/- In the example below, note two things:
1. What happens if we remove `Comm`;
2. What happens to the `G` and `Group G` that are globally defined in this section;
-/
example (G : Type*) [CommGroup G] (H₁ H₂ : Subgroup G) {x y : G} (hx : x ∈ H₁) (hy : y ∈ H₂) :
    x * y ∈ H₁ ⊔ H₂ := by
  rw [Subgroup.mem_sup]
  use x, hx, y, hy

example (x : G) (hx : x ∈ (⊥ : Subgroup G)) : x = 1 := Subgroup.mem_bot.mp hx


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

-- `⌘`

-- #### Homomorphisms

-- @[ext]
structure MonoidHom_Cortona (M N : Type*) [Monoid M] [Monoid N] where
  toFun : M → N
  map_one : toFun 1 = 1
  map_mul : ∀ (x y : M), toFun (x * y) = (toFun x) * (toFun y)


-- Note the @[ext] tag.
example (G H : Type*) [Group G] [Group H] (f g : MonoidHom_Cortona G H)
    (H : ∀ x, f.toFun x = g.1 x) : f = g := by -- the `f.toFun` and `g.1` are horrible!
  cases f
  cases g
  simp only [MonoidHom_Cortona.mk.injEq]
-- #print MonoidHom_Cortona.mk.injEq
  ext -- x
  apply H

#check MonoidHom.ext

def f : MonoidHom_Cortona (ℕ × ℕ) ℕ where
  toFun p := p.1 * p.2
  map_one := by simp only [Prod.fst_one, Prod.snd_one, mul_one]
  map_mul _ _ := by simp only [Prod.fst_mul, Prod.snd_mul]; group

-- **FAE** This is perhaps too much
#check f ⟨2,3⟩ -- we can't apply a `MonoidHom₁` to an element, which is annoying


#check f.toFun ⟨2,3⟩
#eval f.toFun ⟨2,3⟩

/- We would like to able to write `f ⟨2,3⟩` instead of `f.toFun ⟨2,3⟩`. We do this
using the `CoeFun` class, which is a class for objects that can be coerced into
functions.-/

#print CoeFun


instance {G H : Type*} [Monoid G] [Monoid H] :
    CoeFun (MonoidHom_Cortona G H) (fun _ ↦ G → H) where
  coe := MonoidHom_Cortona.toFun

-- attribute [coe] MonoidHom_Cortona.toFun
#check f ⟨2,3⟩

-- whatsnew in
-- @[to_additive __]
example (G₁ : Type) [CommGroup G₁] (f : G →* G₁) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by
  intro x y h
  rw [← map_mul, h, map_one]

example (A : Type*) [AddGroup A] (f : G →* A) : ∀ x y : G, x * y = 1 → (f x) * (f y) = 1 := by sorry

open Function in
example (A : Type*) [AddGroup A] (f : A →+ ℤ) (hf : 1 ∈ f.range) : Surjective f := by
  rcases hf with ⟨b, hb⟩
  intro m
  use m • b
  simp [map_zsmul, hb]

-- `⌘`

-- -- #### Quotients
--
-- #print Setoid
-- #print Equivalence
-- #print Quotient
--
-- variable (H : Subgroup G)
--
-- #print QuotientGroup.leftRel
-- #check QuotientGroup.leftRel H
-- #check (QuotientGroup.mk' _ : [_? : H.Normal] → G →* G ⧸ H)
--
-- -- `simpa` & `refine` for `↔`
-- example (N : Subgroup G) [N.Normal] (x y : G) : (x : G ⧸ N) = (y : G ⧸ N) ↔ x * y⁻¹ ∈ N := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · rw [QuotientGroup.eq] at h
--     rw [← inv_inv x, ← mul_inv_rev]
--     apply Subgroup.inv_mem
--     rwa [Subgroup.Normal.mem_comm_iff]
--     assumption
--   · rw [QuotientGroup.eq, ← inv_inv y, ← mul_inv_rev]
--     apply Subgroup.inv_mem
--     simpa [Subgroup.Normal.mem_comm_iff]
--
--
-- /- Class type inference makes Lean understand that since `H` is
-- commutative, `N` is normal and thus `H ⧸ N` is a group. -/
-- example (H : Type*) [CommGroup H] (f : H →* G) (N : Subgroup H) (hN : N ≤ f.ker) :
--     {g : H ⧸ N →* G // ∀ h : H, f h = g h } := by
--   set g := QuotientGroup.lift N f hN with hg -- `set ... with`!
--   use g
--   intro h
--   rw [hg]
--   simp only [QuotientGroup.lift_mk]
--
-- example [H.Normal] (K : Subgroup G) : Subgroup (G ⧸ H) where
--   carrier := QuotientGroup.mk '' K
--   one_mem' := by
--     simp only [Set.mem_image, SetLike.mem_coe, QuotientGroup.eq_one_iff]
--     use 1
--     constructor-- <;>
--     · exact K.one_mem
--     · exact H.one_mem
--     -- apply one_mem
--   mul_mem' := by
--     rintro a b ⟨x, hxa, rfl⟩ ⟨y, hyb, rfl⟩
--     exact ⟨x * y, K.mul_mem hxa hyb, rfl⟩
--   inv_mem' /- {g} -/ := by
--     rintro g ⟨x, ⟨hx, rfl⟩⟩
--     -- simp only [Set.mem_image, SetLike.mem_coe]
--     use x⁻¹
--     exact ⟨K.inv_mem hx, rfl⟩
--
-- example [H.Normal] (K : Subgroup G) : Subgroup (G ⧸ H) := K.map (QuotientGroup.mk' H)
-- example [H.Normal] (K : Subgroup G) : Subgroup (G ⧸ H) := K.map (QuotientGroup.mk H)

-- `⌘`

end Groups

section Rings

#synth Ring ℤ
#synth CommRing ℤ
#synth Monoid ℤ
#synth AddMonoid ℤ
#check CommRing.toCommMonoid
#check CommRing.toAddCommGroupWithOne

example (a b c : ℚ) : a + (b + c * 1) = a + b + c := by
  -- rw [mul_one]
  -- rw [← add_assoc]
  ring

#check mul_one
#check add_assoc
#print AddMonoid
#print Field
#print IsDomain
#print CommMonoid


example (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring
  -- exact? ==> exact add_pow_two x y

lemma sixth_pow (R : Type*) [CommRing R] (x y : R) : (x + y) ^ 6 =
    x ^ 6 + 6 * x ^ 5 * y +  15 * x ^ 4 * y ^ 2 + 20 * x ^ 3 * y ^ 3 +
      15 * x ^ 2 * y ^ 4 + 6 * x * y ^ 5 + y ^ 6 := by
  ring
  -- grind
  -- exact?

#print axioms sixth_pow

example (R : Type*) [CommRing R] (x y : R) (H : x ^ 2 ≠ y ^ 2) : x ≠ y := by
  -- ring
  grind

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

/- The kernel of a ring homomorphism is an ideal: -/
def kernel (f : R →+* S) : Ideal R where
  carrier := {r : R | f r = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add]
    rw [hb, ha, zero_add]
  zero_mem' := by
    apply map_zero
  smul_mem' := by
    intro c x hx
    simp only [smul_eq_mul, Set.mem_setOf_eq, map_mul]
    rw [hx, mul_zero]

variable (I : Ideal R) in
#check Quotient.mk (Submodule.quotientRel I)
variable (I : Ideal R) in
#check Ideal.Quotient.mk I

example (I : Ideal R) (x : R) : ⟦x⟧ = Ideal.Quotient.mk I x := by
  rfl


open RingHom Ideal.Quotient in
lemma span_equotient {I : Ideal R} (S : Set (R ⧸ I)) (x : R) (hx : ⟦x⟧ ∈ Ideal.span S) :
    x ∈ I + Ideal.span (Quotient.out '' S) := by
  rw [Ideal.span] at hx
  obtain ⟨n, ι', g', hιx⟩ := (Submodule.mem_span_set' (M := R ⧸ I)).mp hx
  -- obtain ⟨n, ι', g', hιx⟩ := (@Submodule.mem_span_set' _ (R ⧸ I) _ _ _ _ _).mp hx
  set ι : Fin n → R := fun i ↦ Quotient.out (ι' i) with hι
  set g : Fin n → Quotient.out '' S := fun i ↦ ⟨Quotient.out (g' i).val, by simp⟩ with hg
  set y : Ideal.span (Quotient.out '' S) := by
    use ∑ i, ι i • (g i)
    exact Submodule.mem_span_set'.mpr ⟨n, ι, g, rfl⟩ with hy
  replace hιx : ∑ i, ι' i * (g' i) = (mk I) x := by
    exact hιx
  have hxy : x - y ∈ I := by --restate with `mk I x` instead of `⟦x⟧`
    simp [← mk_eq_mk_iff_sub_mem, hy, ← hιx, hι, hg]
  rw [Submodule.add_eq_sup, Submodule.mem_sup]
  exact ⟨x - y, hxy, y, SetLike.coe_mem .., by abel⟩


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


end VectorSpaces
-- **FAE** Add something about `ℤ/nℤ` just for fun and to justify the "Number Theory"?

end More

section Exercises



/- **FAE**: Not sure this is the right place, perhaps put in 7?
**¶ Exercise**
Why is the following example broken? Fix its statement, then prove it. -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (H₁ ∩ H₂) := sorry
/- **Sol.:** The error comes come the fact that "being a subgroup" is not a proposition. It is the
definition of some term! A solution would be -/
example (G : Type*) [Group G] (H₁ H₂ : Subgroup G) : Subgroup (G) where
  carrier := H₁ ∩ H₂


end Exercises
