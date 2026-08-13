  # Structures and Classes

Recall that we finished our last class speaking about inductive types, and among those we mentioned
```
structure Iff (P Q : Prop) : Prop
    number of parameters: 2
    fields:
        Iff.mp : P → Q
        Iff.mpr : Q → P
    constructor: Iff.intro {P Q : Prop} (mp : P → Q) (mpr : Q → P) : P ↔ Q
```

Why did `#print Iff` begin with `structure` rather than with `inductive`?
Because it is a *structure* (with two fields):

> **Definition**
    A structure is an inductive type with a unique constructor.

Indeed, among inductive types (*i. e.* all types...), some are remarkably useful for formalising mathematical objects: those that *bundle* objects and properties together. So, we give them a different name.

As an example, let's see what a Monoid is:
```
structure Monoid (M : Type*) where
    | mul : M → M → M                        -- denoted *
    | one : M                                -- denoted 1
    | mul_assoc (a b c : M) : a * b * c = a * (b * c)
    | one_mul (a : M) : 1 * a = a
    | mul_one (a : M) : a * 1 = a
```
* Two of these fields are terms in types of kind `Type *`;
* three of them are terms in types of kind `Prop`;
* we often call a structure having constructor fields both in `Type *` and in `Prop` a *mixin*.

So, 
* a *monoid structure* on `M` is a collection `⟨*, 1, mul_assoc, one_mul, mul_one⟩`
* a term of a monoid is just a term of it! The monoid is a type, so it comes with its terms even if it has more structure, which is encoded in a term `str : Monoid M`.

`⌘`

# Structures

Let's begin with three *painful* examples and three *crazy* errors: `⌘`

They show that basic manipulations "from first principles" are doable, but certainly the *wrong* way to go. The last example also showed that `Lean` is capable of understanding that every metric space comes with a "natural" topology, so it will automatically infer that it is a topological space (to which the lemma `Continuous.mul` applies:

  ```lean
  #check Continuous.mul

  theorem Continuous.mul : ∀ {M X : Type u} [TopologicalSpace M] [Mul M] [ContinuousMul M]
  [TopologicalSpace X] {f g : X → M} (hf : Continuous f) (hg : Continuous g) : Continuous (f * g)
  ```

## Groups
In this section we're going to see 
1. A bad definition of (the right notion of) group;
1. A complicated one of the same notion, adapted for formalisation — and its advantages; 
1. How to benefit from Mathlib, a huge library where all this has already been defined.

`⌘`

The problems with `WrongGroup` and `WrongSemigroup` are (among others...)
* We're carrying around `mul`, `one` and `inv`, together with the type: `α.one` or `X.mul` or `G.inv`...
* Math is full of hierarchies, and these are not respected (the associativity example...): but we don't want to re-prove a theorem on additive commutative groups for rings, then for commutative rings, then for integral domains, then for fields...
* Although we can create 
```
def Nplus : WrongSemigroup where
  carrier := ℕ
  mul := (· + ·) -- or fun x y ↦ x + y
  mul_assoc := add_assoc
```
it is unhandy to connect `Nplus` with `ℕ` *as types*.

### Extends

The right approach relies on the idea of *extending* structures. 

Suppose we've already defined a structure `PoorStructure` with fields `firstfield,...,nth_field` and  we want a new *richer* structure `RichStructure` that also contains the fields
`(n+1)st_field,...,rth_field`. We can either

* forget that we had `PoorStructure` and declare
  ```  
  structure RichStructure where
    firstfield : firstType
    secondfield : secondType
    ...
    rth_field : rth_Type
  ```

* declare that `RichStructure` **extends** `PoorStructure` inheriting terms from the latter:

  ```
  structure RichStructure extends PoorStructure where
      (n+1)st_field : (n+1)st_Type
      ...
      rth_field : rth_Type
  ```

+++ In details (*probably skipped during lecture*)
* The process can be iterated, yielding a structure extending several ones:

        VeryRichStructure extends Structure₁, Structure₂, Structure₃ where
            ...

* If the parent structures have overlapping field names, then all overlapping field names 
must have the **same type**. 
* If the overlapping fields have different default values, then the default value 
from the **last** parent structure that includes the field is used. New default values in the child
(= richer) structure take precedence over default values from the parent (= poorer) structures.

* The `with` (and `__`) syntax are able to "read through" the extension of structures.
+++

`⌘`

### Classes and Class Inference
+++ Some automation we’ve just witnessed
1. Lean was able to "automatically" decide to use `1` and `*` for `G : Group` or `G : CommGroup`,
and to use `0` and `+` for `A : AddGroup` or `A : AddCommGroup`.
1. If we inspect `mul_assoc` we see
    ```
    mul_assoc {G : Type*} [Semigroup G] (a b c : G) : a * b * c = a * (b * c)
    ```
but we used it for a group: Lean understood that every group is a semigroup.

3. The use of `extend` to define `Group`, yielding an "enriched" `DivInvMonoid`.
4. Some redundancy in the definition of `Group` (of `Monoid`, actually) concerning `npow : ℕ → M → M`.

+++
Most of the above points are related to *classes* and *class type inference*.

Classes are special structures, for which certain terms are stored in a database. They enable **class type inference**, constructing a term of a certain class given a term of a "parent" one.

The idea is that each `class` type cointains a *preferred* or a *canonical* term, declared using the keyword `instance` rather than `def`; and this term has been registered in the database to be accessible whenever needed.
```quote
Warning: often, Classes have parameters, so if `G` and `H` are types, `Group G` and `Group H` are different types!
```
To introduce a class assumption in a lemma (*i. e.* to add a term to the local context), in a definition, or in a new class, we use `[` and `]` and typically *we don't name it*: because this should be useless.

To check what is the canonical term of a certain class type, use the command `#synth`, and to recall it use `inferInstance` (in term mode) or `infer_instance` (in tactic mode).

`⌘`
