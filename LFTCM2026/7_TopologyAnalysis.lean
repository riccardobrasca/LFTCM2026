/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

module
public import LFTCM2026.Preliminaries

/- # Topology & Analysis
The goal of today's lecture is to discuss some algebraic structures: (Sub)Groups, Rings and Vector
Spaces. If time permits (and it won't) we might discuss a bit of modular arithmetic.
-/

open Set Function Real Interval ENNReal
open Filter Topology TopologicalSpace
open MeasureTheory intervalIntegral

noncomputable section

section Filters










/- # Limits -/

/-
In topology, one of basic concepts is that of a limit.
Say `f : ℝ → ℝ`. There are many variants of limits.
* the limit of `f(x)` as `x` tends to `x₀`
* the limit of `f(x)` as `x` tends to `∞` or `-∞`
* the limit of `f(x)` as `x` tends to `x₀⁻` or `x₀⁺`
* variations of the above with the additional assumption that `x ≠ x₀`.

This gives 8 different notions of behavior of `x`.
Similarly, the value `f(x)` can have the same behavior:
`f(x)` tends to `∞`, `-∞`, `x₀`, `x₀⁺`, ...

This gives `64` notions of limits.

When we prove that two limits compose: if
`f x` tends to `y₀` when `x` tends to `x₀` and
`g y` tends to `z₀` when `y` tends to `y₀` then
`(g ∘ f) x` tends to `z₀` when `x` tends to `x₀`.
This lemma has 512 variants.

Obviously we don't want to prove this 512 times.
Solution: use filters.










If `X` is a type, a filter `F : Filter X` is a
collection of sets `F.sets : Set (Set X)` satisfying the following:
-/
section Filter

variable {X Y : Type*} (F : Filter X)

#check (F.sets : Set (Set X))
#check (F.univ_sets : univ ∈ F.sets)
-- A filter is closed under taking supersets.
#check (F.sets_of_superset : ∀ {U V},
  U ∈ F.sets → U ⊆ V → V ∈ F.sets)
-- A filter is closed under finite intersections.
#check (F.inter_sets : ∀ {U V},
  U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets)
end Filter






/-
Examples of filters:
-/

/- `(atTop : Filter ℕ)` is made of sets of `ℕ` containing
`{n | n ≥ N}` for some `N` -/
#check (atTop : Filter ℕ)

example {s : Set ℝ} : s ∈ atTop ↔
    ∃ N, ∀ n ≥ N, n ∈ s := by exact mem_atTop_sets

/- `𝓝 x`, made of neighborhoods of `x` in a topological space -/
#check (𝓝 3 : Filter ℝ)

/- `μ.ae` is made of sets whose complement has zero measure
with respect to a measure `μ`. -/
#check (ae volume : Filter (ℝ × ℝ × ℝ))

/-
It may be useful to think of a filter on a type `X`
as a generalized element of `Set X`.
* `atTop` is the "set of very large numbers"
* `𝓝 x₀` is the "set of points very close to `x₀`."
* For each `s : Set X` we have the so-called *principal filter*
  `𝓟 s` consisting of all sets that contain `s`.
-/

example {s t : Set ℝ} : t ∈ 𝓟 s ↔ s ⊆ t :=
  by exact mem_principal





/- Operations on filters -/

/- the *pushforward* of filters generalizes images of sets. -/
example {X Y : Type*} (f : X → Y) : Filter X → Filter Y :=
  Filter.map f

example {X Y : Type*} (f : X → Y) (F : Filter X) (V : Set Y) :
    V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F := by
  rfl


/- `Filter X` has an order that turns it into a complete lattice.
The order is **reverse** inclusion: -/
example {X : Type*} (F F' : Filter X) :
    F ≤ F' ↔ ∀ V : Set X, V ∈ F' → V ∈ F := by
  rfl

/- The principal filter `𝓟 : Set X → Filter X` monotone. -/
example {X : Type*} : Monotone (𝓟 : Set X → Filter X) := by
  exact monotone_principal



/- Using these operations, we can define the limit. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G


lemma MyTendsto_iff {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :
    MyTendsto f F G ↔ ∀ S : Set Y, S ∈ G → f ⁻¹' S ∈ F := by
  -- This is true by unfolding definitions
  rfl

/- A sequence `u` converges to `x` -/
example (u : ℕ → ℝ) (x : ℝ) : Prop :=
  Tendsto u atTop (𝓝 x)

/- `\lim_{x → x₀} f(x) = y₀` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝 x₀) (𝓝 y₀)

/- `\lim_{x → x₀⁻, x ≠ x₀} f(x) = -∞` -/
example (f : ℝ → ℝ) (x₀ y₀ : ℝ) : Prop :=
  Tendsto f (𝓝[<] x₀) atBot


/- Now the following states all possible composition lemmas all at
once! -/
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z}
    {f : X → Y} {g : Y → Z}
    (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := by
  rw [Tendsto] at hf hg ⊢
  calc
    map (g ∘ f) F
    _ = map g (map f F) := by rw [map_map]
    _ ≤ map g G := by gcongr
    _ ≤ H := hg





/-
Filters also allow us to reason about things that are
"eventually true". If `F : Filter X` and `P : X → Prop` then
`∀ᶠ n in F, P n` means that `P n` is eventually true for `n` in `F`.
It is defined to be `{ x | P x } ∈ F`.

The following example shows that if `P n` and `Q n` hold for
sufficiently large `n`, then so does `P n ∧ Q n`.
-/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ

-- The `filter_upwards` tactic is good for reasoning with
-- `∀ᶠ x, P x`.
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  -- `filter_upwards [hP, hQ]` converts your goal to
  -- `∀ n, P n → Q n → P n ∧ Q n`
  filter_upwards [hP, hQ]
  intro n hpn hqn
  tauto -- does basic logical reasoning

end Filters


section Topology

/- Let's look at the definition of topological space. -/

universe u v w
variable {X : Type u} [TopologicalSpace X]
  {Y : Type v} [TopologicalSpace Y]
  {Z : Type w} [TopologicalSpace Z]

#eval Lean.versionString
example {ι : Type*} (s : ι → Set X) :
    interior (⋂ i, s i) ⊆ ⋂ i, interior (s i) := by
  sorry


/- A map between topological spaces is continuous if the
preimages of open sets are open. -/
example {f : X → Y} :
    Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def

/- It is equivalent to saying that for any `x₀` the function
value `f x` tends to `f x₀` whenever `x` tends to `x₀`. -/
example {f : X → Y} :
    Continuous f ↔ ∀ x₀, Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  exact?

/- By definition, the right-hand side states that `f` is
continuous at `x₀`. -/
example {f : X → Y} {x₀ : X} :
    ContinuousAt f x₀ ↔ Tendsto f (𝓝 x₀) (𝓝 (f x₀)) := by
  rfl



/- ## Proving "boring" continuity goals

If we want to prove that the composition of two complicated continuous functions is continuous,
we can use lemmas of composition, addition, multiplication etc. of continuous functions.
-/

example : Continuous (fun x ↦ 2 + x * Real.sin x) := by
  apply Continuous.add
  · apply continuous_const
  · apply Continuous.mul
    · exact continuous_id
    · exact continuous_sin
  done

/- The `fun_prop` tactic automates these boring proofs. -/

example : Continuous (fun x ↦ 2 + x * Real.sin x) := by
  fun_prop

example {f : ℝ → ℝ} (hf : Continuous f) :
    ContinuousAt (fun x ↦ 2 + f x * Real.sin x) 2 := by
  fun_prop

/- `fun_prop` knows about measurability, differentiability etc.
and knows the relations between them
(e.g., differentiable functions are continuous,
continuous functions are measurable, etc.) -/



/- `X ≃ₜ Y` is the type of homeomorphisms between topological spaces.  -/
#check X ≃ₜ Y



/- We can state that a topological space satisfies
separatedness axioms. -/

example : T0Space X ↔ Injective (𝓝 : X → Filter X) := by
  exact?

example : T1Space X ↔ ∀ x, IsClosed ({ x } : Set X) :=
  ⟨by exact?, by exact?⟩

example : T2Space X ↔
    ∀ x y : X, x ≠ y → Disjoint (𝓝 x) (𝓝 y) :=
  t2Space_iff_disjoint_nhds

example : RegularSpace X ↔ ∀ (s : Set X) (a : X),
    IsClosed s → a ∉ s → Disjoint (𝓝ˢ s) (𝓝 a) := by
  exact?


/- A set is compact if every open cover has a finite subcover. -/

example {K : Set X} : IsCompact K ↔ ∀ {ι : Type u}
    (U : ι → Set X), (∀ i, IsOpen (U i)) → (K ⊆ ⋃ i, U i) →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, U i := by
  exact?

/- We use `CompactSpace` to say that a whole space is compact. -/

#check CompactSpace

end Topology

section Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/- A metric space is a type `X` equipped with a distance function
`dist : X → X → ℝ` with the following properties. -/

#check (dist : X → X → ℝ)
#check (dist_nonneg : ∀ {a b : X}, 0 ≤ dist a b)
#check (dist_eq_zero : ∀ {a b : X}, dist a b = 0 ↔ a = b)
#check (dist_comm : ∀ (a b : X), dist a b = dist b a)
#check (dist_triangle : ∀ (a b c : X), dist a c ≤ dist a b + dist b c)

/- In metric spaces, all topological notions are also
characterized by the distance function. -/

example (f : X → Y) (x₀ : X) : ContinuousAt f x₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ {x},
    dist x x₀ < δ → dist (f x) (f x₀) < ε :=
  Metric.continuousAt_iff

example (x : X) (ε : ℝ) :
    Metric.ball x ε = { y | dist y x < ε } := by
  rfl

example (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

/- Lean already knows that many types are naturally metric spaces. -/
#synth MetricSpace ℝ


end Metric








/- # Differential Calculus -/

/- We write `deriv` to compute the derivative of a function.
`simp` can compute the derivatives of standard functions. -/

example (x : ℝ) : deriv sin x = cos x := by simp

example (x : ℝ) :
    deriv (fun y ↦ sin (y + 3)) x = cos (x + 3) := by simp

/- Not every function has a derivative.
In Mathlib we just define the derivative
of a non-differentiable function to be `0`. -/

example (f : ℝ → ℝ) (x : ℝ) (h : ¬ DifferentiableAt ℝ f x) :
    deriv f x = 0 := by
  exact?



/- So proving that `deriv f x = y` doesn't
necessarily mean that `f` is differentiable.
Often it is nicer to use the predicate `HasDerivAt f y x`,
which states that `f` is differentiable and `f'(x) = y`. -/

example (x : ℝ) : HasDerivAt sin (cos x) x :=
  hasDerivAt_sin x


/- We can also specify that a function has a derivative
without specifying its derivative. -/

example (x : ℝ) : DifferentiableAt ℝ sin x :=
  differentiableAt_sin



/- Mathlib contains lemmas stating that common operations satisfy
`HasDerivAt` and `DifferentiableAt` and to compute `deriv`. -/

#check HasDerivAt.add
#check deriv_add
#check DifferentiableAt.add


example (x : ℝ) :
    HasDerivAt (fun x ↦ cos x + sin x)
    (cos x - sin x) x := by
  rw [sub_eq_neg_add]
  apply HasDerivAt.add
  · exact?
  · exact?
  done


/- There are various variations of derivatives/being differentiable -/

/- A function is differentiable everywhere. -/
#check Differentiable

/- A function is differentiable on a subset. -/
#check DifferentiableOn

/- A function is differentiable at a point, considered only within the subset -/
#check DifferentiableWithinAt

/- We can also consider the derivative only within a subset. -/
#check HasDerivWithinAt
#check derivWithin




/-
Lean has the following names for intervals
("c" = closed, "o" = open, "i" = infinity)
Icc a b = [a, b]
Ico a b = [a, b)
Ioc a b = (a, b]
Ioo a b = (a, b)
Ici a   = [a, ∞)
Ioi a   = (a, ∞)
Iic b   = (-∞, b]
Iio b   = (-∞, b)

The **intermediate value theorem** states that if `f` is continuous and
`f a ≤ y ≤ f b`, then there is an `x ∈ [a, b]` with `f(x) = y`.
-/

example {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  intermediate_value_Icc hab hf

/-
The **mean value theorem** states that if `f` is continous on `[a, b]`
and differentiable on `(a, b)`,
then there is a `c ∈ (a, b)` where `f'(c)`
is the average slope of `f` on `[a, b]`
-/
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'



/- We can more generally talk about the derivative of functions between normed spaces. -/

-- This states that E is a normed vector space over `ℝ`.
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℝ E]
-- add `[CompleteSpace E]` to make `E` a Banach space.

/- If the codomain is a normed vector space,
everything works the same as before.

`fun_prop` can prove a lot of differentiability goals
(but it cannot prove `HasDerivAt` or `deriv ... = ...`) -/
example {x : ℝ} :
    DifferentiableAt ℝ
      (fun x ↦ (Real.cos x ^ 2, Real.sin x ^ 2)) x := by
  fun_prop



/- If the domain is a normed space we can define the
total derivative, which will be a continuous linear map. -/

/- Morphisms between normed spaces are continuous linear maps `E →L[𝕜] F`. -/
section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

#check E →L[𝕜] F

/- We define the *Fréchet derivative* of any function
between normed spaces. -/

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔
    Tendsto (fun x ↦ ‖f x - f x₀ - f' (x - x₀)‖ / ‖x - x₀‖)
      (𝓝 x₀) (𝓝 0) := by
  simp_rw [div_eq_inv_mul, hasFDerivAt_iff_tendsto]

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E)
    (hf : HasFDerivAt f f' x₀) :
    fderiv 𝕜 f x₀ = f' :=
  hf.fderiv

/- Careful: in higher dimensions,
a function can have several derivatives within a set,
if that set is sufficiently "bad".
However, on "nice" sets, it is unique.
This includes open sets and convex sets with non-empty interior.
-/
#check UniqueDiffOn

example {s : Set E} (hs : IsOpen s) :
  UniqueDiffOn 𝕜 s := IsOpen.uniqueDiffOn hs

#check uniqueDiffOn_convex

#click_suggestions
example (f : E → F) (f₁' f₂' : E →L[𝕜] F) (s : Set E) (x₀ : E)
    (hf₁ : HasFDerivWithinAt f f₁' s x₀)
    (hf₂ : HasFDerivWithinAt f f₂' s x₀)
    (h : UniqueDiffOn 𝕜 s) (hx : x₀ ∈ s) :
    f₁' = f₂' :=
  h.eq _ hf₁ hf₂






/- We write `ContDiff 𝕜 n f` to say that `f` is `C^n`,
i.e. it is `n`-times continuously differentiable.
Here `n` lives in `WithTop ℕ∞`:
`ℕ∞` is `ℕ` with an extra top element `∞` added ("∞"),
and `WithTop ℕ∞` adds another element `⊤` ("ω").
-/
variable {f g : E → F} {m : ℕ∞} {r : 𝕜}

open scoped ContDiff -- for the notation "∞"

#check ContDiff 𝕜 42 f
#check ContDiff 𝕜 ∞ f -- f is smooth



example : ContDiff 𝕜 0 f ↔ Continuous f := contDiff_zero

example {n : ℕ} : ContDiff 𝕜 (n+1) f ↔
    Differentiable 𝕜 f ∧ ContDiff 𝕜 n (fderiv 𝕜 f) := by
  simp [contDiff_succ_iff_fderiv]


example : ContDiff 𝕜 ∞ f ↔ ∀ n : ℕ, ContDiff 𝕜 n f :=
  contDiff_infty



/- The element ω denotes analytic functions: those which have a Taylor series which converges
to the function -/
#check ContDiff 𝕜 ω f -- f is analytic

#check AnalyticAt

example [CompleteSpace F] : ContDiff 𝕜 ω f ↔ ∀ x, AnalyticAt 𝕜 f x :=
  sorry

#check iteratedFDeriv

end NormedSpace


/-! ## Integration -/

/- We start with some basic integration results in Mathlib.
The integral of a function `f` on the interval `[a, b)`
is written as `∫ x in a..b, f x`. -/

example (a b : ℝ) : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example : ∫ x in 0..1, x = 1/2 := by
  simp

example (a b : ℝ) : ∫ x in a..b, exp x = exp b - exp a :=
  integral_exp


/- We can use this to define an specific antiderivative
of a function. -/

example (f : ℝ → ℝ) (hf : LocallyIntegrable f) : ℝ → ℝ :=
  fun x ↦ ∫ t in 0..x, f t

/- the notation `[[a, b]]` (in namespace `Interval`) means
`uIcc a b`, i.e. the interval from `min a b` to `max a b` -/
example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, 1 / x = log (b / a) :=
  integral_one_div h

/- In very simple cases `simp` can solve an abstract integral.
In this case, it uses translation invariance of integrals. -/
example (a b : ℝ) :
    ∫ x in a..b, exp (x + 3) = exp (b + 3) - exp (a + 3) := by
  simp

/- If we swap `a` and `b`, the sign flips. -/
example {f : ℝ → ℝ} {a b : ℝ} :
    ∫ x in b..a, f x = - ∫ x in a..b, f x :=
  intervalIntegral.integral_symm a b




/- We have the fundamental theorem of calculus in Lean. -/

/- FTC-1: the derivative of the integral is the original function. -/
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) :
    deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (hf.integral_hasStrictDerivAt a b).hasDerivAt.deriv

/- FTC-2: the integral of a derivative can be computed by
evaluation at the endpoints. -/
example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ}
    (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt h h'

/- We can use this to compute integrals
if we know the antiderivative. -/
example (a b : ℝ) : ∫ x in a..b, exp (x / 2) =
    2 * (exp (b / 2) - exp (a / 2)) := by
  -- sorry
  rw [mul_sub]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    apply HasDerivAt.congr_deriv
    -- note: apply? doesn't work nicely now
    apply HasDerivAt.const_mul
    apply HasDerivAt.exp
    apply HasDerivAt.div_const
    apply hasDerivAt_id
    ring
  · apply Continuous.intervalIntegrable
    fun_prop
  -- sorry
  done

/-
In the example above we computed the derivative using
`apply HasDerivAt.congr_deriv`, which will caused a *metavariable*
to appear in the goal.
Some tactics (like `apply?`) don't work well in such cases,
but sometimes it's convenient.
-/




/-
## Measure Theory

Mathlib has an extensive library of measure theory.
Outer measures on `X` are defined as a structure containing
a function `μ : 𝒫(X) → [0, ∞]` satisfying:
* `μ(∅) = 0`
* *Countable subadditivity*: if `(Aᵢ)ᵢ` is
  a countable family of sets, then
  `μ(⋃ᵢ Aᵢ) ≤ ∑ᵢ μ(Aᵢ)`
* *Monotonicity*: if `A ⊆ B` then `μ(A) ≤ μ(B)`.
-/

/- In Mathlib, we denote `[0, ∞]` by `ℝ≥0∞` or `ENNReal`. -/

#check ℝ≥0∞
example : ℝ≥0∞ = WithTop {x : ℝ // 0 ≤ x} := rfl
example : ∞ + 5 = ∞ := by simp
example : ∞ * 0 = 0 := by simp
example : ∞ - ∞ = 0 := by simp


/-
`OuterMeasure X` is the type of outer measures on `X`
-/
section OuterMeasure

variable {X : Type*} {μ : OuterMeasure X}

#check (μ : Set X → ℝ≥0∞)

example : μ ∅ = 0 :=
  measure_empty

example {s t : Set X} (h : s ⊆ t) : μ s ≤ μ t :=
  measure_mono h

example {s : ℕ → Set X} : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

end OuterMeasure

/- We write `MeasurableSpace X` to say that `X` has a notion
of measurable sets that form a σ-algebra. -/

variable {X : Type*} [MeasurableSpace X]

example : MeasurableSet (∅ : Set X) :=
  MeasurableSet.empty

example {s : Set X} (hs : MeasurableSet s) : MeasurableSet sᶜ :=
  hs.compl

example {f : ℕ → Set X} (h : ∀ b, MeasurableSet (f b)) :
    MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

/-
A measure `μ` on `X` comes together with its associated outer measure.
This means that we can apply `μ` to any subset of `X`, but
many lemmas (e.g. additivity) require that the sets are measurable.
-/

variable {μ : Measure X}

example : μ ∅ = 0 :=
  measure_empty

example {s : ℕ → Set X} (hmeas : ∀ i, MeasurableSet (s i))
    (hdis : Pairwise (Disjoint on s)) :
    μ (⋃ i, s i) = ∑' i, μ (s i) :=
  measure_iUnion hdis hmeas

example (s : Set X) : μ s = ⨅ (t ⊇ s) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ℕ → Set X) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s




/- If you know that the measure of a set is finite, you can get
the measure as a real number with `μ.real`.

The function `ENNReal.toReal` sends `∞` to `0`. -/
example (s : Set X) : μ.real s = (μ s).toReal := rfl



/- The collection of measurable sets on `ℝ`
is the smallest σ-algebra containing the open sets.
These are called the *Borel-measurable* sets. -/
example (s : Set ℝ) : MeasurableSet s ↔
    MeasurableSpace.GenerateMeasurable { t : Set ℝ | IsOpen t } s := by rfl

example : BorelSpace ℝ := by infer_instance


/- The *Lebesgue-measurable* sets are the sets
that are Borel measurable up to a null set. -/
#check NullMeasurableSet
example {s : Set ℝ} (hs : volume s = 0) : NullMeasurableSet s := by
  exact?

/- Various spaces have a canonical measure associated to them,
called `volume`. This is given by the class `MeasureSpace`.

On the real numbers, this is the measure on the Borel measurable sets
that is translation invariant and has `μ([0, 1]) = 1` -/
example : MeasureSpace ℝ := by infer_instance
#check (volume : Measure ℝ)
#check (volume : Measure (Fin 3 → ℝ))


example (a b : ℝ) (h : a ≤ b) :
    volume.real (Icc a b) = b - a := by
  simp [h]

example (x : ℝ) (s : Set ℝ) :
    volume ((· + x) '' s) = volume s := by
  simp?





/- Filters are also useful in measure theory.

We say that a property `P` holds **almost everywhere**
if the set of elements where it doesn't hold has measure 0. -/
example {P : X → Prop} :
    (∀ᶠ x in ae μ, P x) ↔ μ {x | ¬ P x} = 0 := by
  rfl

/- This also has the specific notation `∀ᵐ (x : X) ∂μ, P x`.
We write `f =ᵐ[μ] g` to state that two functions are a.e. equal. -/
variable (P : X → Prop) in
#check ∀ᶠ x in ae μ, P x

variable (P : X → Prop) in
#check ∀ᵐ x ∂μ, P x


example : ({0} : Set ℝ).indicator 1 =ᵐ[volume] (0 : ℝ → ℝ) := by
  simp [Filter.EventuallyEq, ae_iff]
  done

/- `∀ᵐ x, P x` means `∀ᵐ x ∂volume, P x`. -/
example : ∀ᵐ x : ℝ, Irrational x := by
  -- sorry
  unfold Irrational
  refine Countable.ae_notMem ?h volume -- apply?
  exact countable_range Rat.cast -- apply?
  -- sorry
  done



/- A map is (Borel-)measurable if preimages of measurable sets
under that map are measurable.
Note the similarity to the definition of continuity.
In particular, continuous functions are measurable. -/
#print Measurable
#check Continuous.measurable






/- A map `f` into a normed group is integrable
when it is measurable and the map
`x ↦ ‖f x‖` has a finite integral. -/
#print Integrable

example : ¬ Integrable (fun _ ↦ 1 : ℝ → ℝ) := by
  -- sorry
  -- strategy: use rw??
  rw [integrable_const_iff]
  rw [isFiniteMeasure_iff volume]
  simp
  -- sorry
  done




/- We can take the integrals for functions intro a Banach space.
This version of the integral is called the *Bochner integral*.
The integral is denoted `∫ a, f x ∂μ` -/
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {f : X → E}

example {f g : X → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ x, f x + g x ∂μ = ∫ x, f x ∂μ + ∫ x, g x ∂μ :=
  integral_add hf hg


/-
* We can write `∫ x in s, f x ∂μ` for the integral restricted to a set.
* We can abbreviate `∫ x, f x ∂volume` to `∫ x, f x`
* We write `∫ x in a..b, f x ∂μ` for the integral on an interval.
-/
example {s : Set X} (c : E) :
    ∫ x in s, c ∂μ = μ.real s • c :=
  setIntegral_const c

example {f : ℝ → E} {a b c : ℝ} :
    ∫ x in a..b, c • f x = c • ∫ x in a..b, f x :=
  intervalIntegral.integral_smul c f

example {f : ℝ → E} {a b : ℝ} (h : a ≤ b) :
    ∫ x in a..b, f x = ∫ x in Ioc a b, f x :=
  integral_of_le h

example {f : ℝ → E} {a b : ℝ} (h : b ≤ a) :
    ∫ x in a..b, f x = -∫ x in Ioc b a, f x :=
  integral_of_ge h



/- Here is a version of the dominated convergence theorem. -/
example {F : ℕ → X → E} {f : X → E} (bound : X → ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n : ℕ ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim

/- Here is the statement of Fubini's theorem. -/
variable {X Y : Type*} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    [MeasurableSpace Y] {ν : Measure Y} [SigmaFinite ν] in
example (f : X × Y → E) (hf : Integrable f (μ.prod ν)) :
    ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf

/-
There are various versions of the change of variables theorem.
Here is one for functions in only 1 variable.
-/
example {s : Set ℝ} {f f' : ℝ → ℝ}
    (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : ℝ → E) :
    ∫ x in f '' s, g x = ∫ x in s, |f' x| • g (f x) :=
  integral_image_eq_integral_abs_deriv_smul hs hf' hf g

/-
Note that this has weaker assumptions versions you often see:
- `s` is not required to be open;
- `f` is not required to be continuously differentiable;
  because the integral of non-integrable functions has junk value 0,
- `g` is not required to be integrable.
-/

/- Here is a version of the change of variables formula for interval integrals. -/
#check integral_comp_smul_deriv''

end MeasureTheory


/-
# Filter Exercises
-/

/- If `P n` holds for sufficiently large `n`, then clearly does `P n ∨ Q n`:
we can use `Filter.Eventually.mono` to express this: `P n` implies `P n ∨ Q n` -/
example (P Q : ℕ → Prop)
    (hP : ∀ᶠ n in atTop, P n) :
    ∀ᶠ n in atTop, P n ∨ Q n := by
  sorry

/- Let's make that a bit more complicated: assume if `P n` implies `Q n` for n sufficiently large
and `P n` holds for sufficiently large `n` --- then so does `Q n`. -/
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hPQ : ∀ᶠ n in atTop, P n → Q n) :
    ∀ᶠ n in atTop, Q n := by
  sorry

/-
# Topology Exercises
-/

/- Prove this from the charaterization of neighborhood filters `mem_nhds_iff`. -/
example [TopologicalSpace X] {x : X} {s : Set X} (h : s ∈ 𝓝 x) :
    x ∈ s := by
  sorry
  done

-- Practice exercise: prove that the intersection of all open neighborhoods
-- of `x` in a metric space is `{x}`.
example [MetricSpace X] {x : X} :
    ⋂ i ∈ {s : Set X | IsOpen s ∧ x ∈ s }, i = {x} := by
  sorry
  done



/- The goal of these exercises is to prove that
the regular open sets in a topological space form a complete boolean algebra.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/

variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

instance : PartialOrder (RegularOpens X) := PartialOrder.ofSetLike ..

theorem le_def {U V : RegularOpens X} :
    U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp

@[simp] theorem regular {U : RegularOpens X} :
    interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course Mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X :=
  ⟨closure U, sorry⟩

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/
@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X :=
  ⟨interior C, sorry, sorry⟩

/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by sorry

@[simp] lemma cl_int : U.cl.int = U := by sorry

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi

@[simp] lemma coe_inf {U V : RegularOpens X} : ↑(U ⊓ V) = (U : Set X) ∩ V := by
  have : U ⊓ V = (U.cl ⊓ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_sup {U V : RegularOpens X} : ↑(U ⊔ V) = interior (closure ((U : Set X) ∪ V)) := by
  have : U ⊔ V = (U.cl ⊔ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_top : ((⊤ : RegularOpens X) : Set X) = univ := by
  have : (⊤ : RegularOpens X) = (⊤ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := by
  have : (⊥ : RegularOpens X) = (⊥ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_sInf {U : Set (RegularOpens X)} :
    ((sInf U : RegularOpens X) : Set X) =
    interior (⋂₀ ((fun u : RegularOpens X ↦ closure u) '' U)) := by
  have : sInf U = (sInf (cl '' U)).int := rfl
  simp [this]

@[simp] lemma Closeds.coe_sSup {C : Set (Closeds X)} : ((sSup C : Closeds X) : Set X) =
    closure (⋃₀ ((↑) '' C)) := by
  have : sSup C = Closeds.closure (sSup ((↑) '' C)) := rfl
  simp [this]

@[simp] lemma coe_sSup {U : Set (RegularOpens X)} :
    ((sSup U : RegularOpens X) : Set X) =
    interior (closure (⋃₀ ((fun u : RegularOpens X ↦ closure u) '' U))) := by
  have : sSup U = (sSup (cl '' U)).int := rfl
  simp [this]

/- We still have to prove that this gives a distributive lattice.
Note: these are hard; you might want to do the next exercises first. -/
instance completeDistribLattice : CompleteDistribLattice (RegularOpens X) :=
  CompleteDistribLattice.ofMinimalAxioms
  { completeLattice (X := X) with
    inf_sSup_le_iSup_inf := by sorry
    iInf_sup_le_sup_sInf := by sorry
    }


instance : Compl (RegularOpens X) := sorry


@[simp]
lemma coe_compl (U : RegularOpens X) : ↑Uᶜ = interior (U : Set X)ᶜ := by sorry


instance : CompleteBooleanAlgebra (RegularOpens X) :=
  { completeLattice (X := X) with
    inf_compl_le_bot := by sorry
    top_le_sup_compl := by sorry
    le_sup_inf := by sorry
    sdiff_eq := by sorry
    himp_eq := by sorry }

end RegularOpens

/-
# Differentiation Exercises
-/

/- Currently, derivatives still have to be computed by hand.
`HasDerivAt.deriv` is a useful first step.
After that, try to find relevant lemmas from Mathlib.
-/
#check HasDerivAt.deriv
example (x : ℝ) : deriv (fun x ↦ ((Real.cos x) ^ 2, (Real.sin x) ^ 2)) x =
    (- 2 * Real.cos x * Real.sin x, 2 * Real.sin x * Real.cos x) := by
  sorry
  done


/- We can take the directional derivative or partial derivative
by applying the Fréchet derivative to an argument -/
example (x y : ℝ) :
    let f := fun ((x,y) : ℝ × ℝ) ↦ x^2 + x * y
    fderiv ℝ f (x, y) (1, 0) = 2 * x + y := by
  intro f
  sorry




/-
# Integration Exercises
-/


/- simp can deal with a translations and scaling inside integrals. -/
example (a b : ℝ) : ∫ x in a..b, 4 * cos (2 * x + 3) =
    2 * (sin (2 * b + 3) - sin (2 * a + 3)) := by
  sorry
  done

example : ∫ x in 0..2, exp x + x ^ 3 = exp 2 + 3 := by
  sorry
  done

/- Do this *without* using the fundamental theorem of calculus. -/
example (a b : ℝ) : ∫ x in a..b, sin x * cos x =
    (cos (2 * a) - cos (2 * b)) / 4 := by
  sorry
  done

/- Use the fundamental theorem of calculus. -/
example (a b : ℝ) (n : ℕ) : ∫ x in a..b, x ^ n * sin (x ^ (n + 1)) =
    (cos (a ^ (n + 1)) - cos (b ^ (n + 1))) / (n + 1) := by
  sorry
  done

/- This one is tricky. Find appropriate lemmas using `rw??` or loogle. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, 1 / x + 1 / x ^ 2 =
    log b + 1 / a - log a - 1 / b := by
  have : 0 ∉ [[a, b]] := by sorry
  sorry
  done
