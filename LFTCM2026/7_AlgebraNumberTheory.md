
### More about groups

#### Subgroups
The definition of subgroups is slightly different from that of a group, it relies on `Sets`:
```
structure Subgroup (G : Type*) [Group G] extends Submonoid G : Type* where
    carrier : Set G
    mul_mem' {a b : G} : a ∈ self.carrier → b ∈ self.carrier → a * b ∈ self.carrier
    one_mem' : 1 ∈ self.carrier
    inv_mem' {x : G} : x ∈ self.carrier → x⁻¹ ∈ self.carrier
```
We'll discuss what "sets" are in the next class, but for now just record that given any type `G : Type*`, 
and any set `S : Set G`, we obtain for every `g : G` the type (of kind `Prop`) `g ∈ S`, that can be either inhabited (the proposition is true) or empty (the proposition is false).

Exactly as we've discussed for monoids, that of "being a subgroup" is not a `Prop`-like
notion: rather, to each group `G` we attach a new *type* `Subgroup G` whose terms
represent the different subgroups of `G`, each seen as an underlying set and a collection of proofs that
the set is multiplicatively closed (a "mixin").

Finally, the type `Subgroup G` is ordered, and `{1} : Subgroup G` is actually `⊥` (the bottom element, written `\bot`) whereas `G : Subgroup G` is `⊤` (the top element, written `\top`).

`⌘`

#### Homomorphisms
Given *monoids* `M` and `N`, a *monoid* homomorphism is a function `f : M → N` that respects the operations and the units. There could be (at least) two ways to define this: 

1. Declare the property `MonHom : (M → N) → Prop` as

        def MonHom : (M → N) → Prop := f ↦ ( ∀ a b, f (a * b) = (f a) * (f b) ) ∧ (f 1 = 1)
    
and let `MonoidHom` be the subtype

    MonoidHom = {f : M → N // MonHom f}
This would mean that a monoid homomorphism is a pair `⟨f, hf : MonHom f⟩`.

2. Define a new type `MonoidHom M N`, as a structure

        structure MonoidHom M N where
        | toFun : M → N
        | map_mul : ∀ a b, toFun (a * b) = (toFun a) * (toFun b)
        | map_one : toFun 1 = 1

so that terms of `MonoidHom M N` would be *triples* `⟨f, map_mul f, map_one f⟩`.

These approaches are not *very* different, the problem with the first is that to access the proofs one has to destructure `hf` to `hf.1` and `hf.2`. Imagine if there were 20 properties...


* A **group homomorphism** is just a monoid homomorphism: the property `f (x⁻¹) = (f x)⁻¹` can be proven. But this relies on class type inference...
  
  +++ Why does it rely on class type inference?
  Because if we only define monoid homomorphisms, then when `G` and `H` are groups and we write `f : G →* H` Lean would complain that `G` and `H` are not monoids. By class type inference, it understands that they are *also* monoids.
  +++

* **Take-home message**: homomorphisms between algebraic structures are structures on their own, "bundling" together the underline function and all its properties.

It will be another story for continuous/differentiable/smooth functions...

`⌘`
#### Quotients
To define quotients, we clearly need equivalence relations:
```
class Setoid (α : Sort u) where
  r : α → α → Prop
  iseqv : Equivalence r
```

Observe that `α` is a parameter, so a term in `Setoid α` is an equivalence relation on `α`. This comes with a notation `a ≈ b` (typed as `\~~`) meaning that `r a b`, *i. e.* `a,b : α` are equivalent.

+++ Why a class instead of a structure? Isn't this an obsession?
It would not change much, and in many *explicit* occurrences terms of `Setoid α` are actually named and in parenthesis, as in `(s : Setoid α)`. But we want automation, for example in order to find the *canonical* equivalence relation on `G ⧸ H` under the assumption that `H` is normal, and not having Lean asking us to choose one relation each time.
+++

Given `s : Setoid α` we can construct `Quotient s`: it is a type whose terms correspond to equivalence classes of `s`, yet **I cannot define it because it is a Lean primitive**.

But the important things are not definitions, **it is the API**:
* `Quotient.mk s : α → Quotient s` is the quotient map (and `Quotient.mk _ x` is denoted `⟦x⟧`, with `\[[` and `\]]`);
* `Quotient.out : Quotient s → α` sends `x : Quotient s` to a lift
of `x`, **using the axiom of choice**;
* `Quotient.lift` : given a term `f : α → β` satisfying `a ≈ b → f a = f b`, the term `Quotient.lift f : Quotient s → β` satisfies `(Quotient.lift f) ∘ Quotient.mk s = f`;

+++ And two more esoteric ones:
* `Quotient.rep [Encodable α] : Quotient s → α` without using the axiom of choice, provided that `α` is **encodable**, *i. e.* it is endowed with a (chosen) bijection into a subset of `ℕ` (we also need `s.r` to be decidable: for all `a, b`, either `a ≈ b` or `¬ a ≈ b`).
* `axiom Quotient.sound {a b : α} : a ≈ b → ⟦a⟧ = ⟦b⟧`: it is (almost) an axiom.
+++

In the special case of `{G : Type*}  [Group G] (H : Subgroup G)` there are two relations: `x y ↦ x * y⁻¹ ∈ H` and `x y ↦ x⁻¹ * y ∈ H` (can you understand their *signature*?), giving rise to
* the corresponding `Quotient (QuotientGroup.leftRel H) : Type*`, denoted `G ⧸ H` (where `⧸` is `\/`, or `\quot` and not `/`);
* the corresponding `Quotient (QuotientGroup.rightRel H) : Type*`;
* the corresponding bare function `Quotient.mk (QuotientGroup.leftRel H) : G → G ⧸ H`;
* the *much more interesting* `Quotient.mk' _ : [_ : H.Normal] → G →* G ⧸ H`.

`⌘`
## Rings

From the theoretical point of view, all algebraic structures look alike: so I'll present a (slightly long) summary of what we need about rings, and then there will be plenty of examples.

### Definition and basic tactics

As for groups, the way to say that `R` is a ring is to type

    (R : Type*) [Ring R]

The library is particularly rich insofar as *commutative* rings are concerned, and we're going to stick to those in our course.

* The tactic `ring` solves claim about basic relations in commutative rings, namely those that hold in *free* rings.
* The tactic `grind` is much more powerful (but it oten calls the axiom of choice for no good reason: we won't care): beyond what `ring` can do, it also treats inequalities, logical connectives, local assumptions, etc.

Given what we know about groups and monoids, we can expect a commutative ring to have several "weaker" structures: typically these can be accessed through a `.toWeakStructure` projection.


### Morphisms, Ideals and Quotients.

* Morphisms work as for groups: they are functions respecting both structures on a ring, that of a multiplicative monoid and of an additive group: so, they're respecting both monoid structures, hence the notation `R →+* S` for a ring homomorphism. Of course, `≃+*` denotes ring isomorphism, so `R ≃+* S` is the type of all ring homomorphisms from `R` to `S`.

* In the usual spirit of working in the greatest possible generality, `I : Ideal R` means `I : Submodule R R`.

Concretely, a term `I : Ideal R` is such that

        | I.carrier : Set R
        | I.zero_mem : (0 : R) ∈ I
        | I.add_mem (x y : R) : x ∈ I → y ∈ I → x + y ∈ I
        | I.smul_mem (x y : R) : x ∈ I → x • y ∈ I

The `smul_mem` field is part of the definition, but it is sometimes handier to use either of

        I.mul_mem_left (a b : R) : b ∈ I → a * b ∈ I

or

        I.mul_mem_right (a b : R) : a ∈ I → a * b ∈ I

As for subgroups, the type `Ideal R` is ordered, with `⊥ = {0} : Ideal R` and `⊤ = R : Ideal R`.

* The discussion about quotient rings is analogous to the one for quotient groups, through the *same* setoid structure (called `Submodule.quotientRel`)
```
@[to_additive]
def leftRel (s : Subgroup α) : Setoid α := MulAction.orbitRel s.op α
```
where `to_additive` fires, becoming `fun x y ↦ x - y ∈ I.toAddSubgroup`.

As for groups, it is often better to replace `Quotient.mk (Submodule.quotientRel I)` by 
`Ideal.Quotient.mk I : R →+* R ⧸ I`.

`⌘`