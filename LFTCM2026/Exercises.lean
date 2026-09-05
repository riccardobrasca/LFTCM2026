/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import LFTCM2026.Preliminaries

/-!
# Fifteen exercises

Statements and proofs of the fifteen exercises of `Exercises.md`, which is also where each one
carries its "stating" and "proving" difficulty. Nothing here is fancy: the point is that a formal
statement should be readable by someone who knows the informal one, and that the proof should
follow the proof one would write on paper.
-/

/-!
## Exercise 1

`gcd (Fₘ, Fₙ) = F_gcd(m, n)`, where `Fₙ` is the `n`-th Fibonacci number.

This one is in Mathlib already, as `Nat.fib_gcd`, with the two sides exchanged: `Nat.fib` is
Mathlib's Fibonacci sequence, `Nat.gcd` its gcd. Finding the library lemma *is* the exercise here;
proving it from scratch is a serious induction.
-/

theorem exercise_1 (m n : ℕ) : Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) := by
  exact (Nat.fib_gcd m n).symm
  done

/- A concrete instance, to see the statement in action: `F₁₂ = 144`, `F₁₈ = 2584`, their gcd is
`8 = F₆`, and indeed `gcd (12, 18) = 6`. -/
example : Nat.gcd (Nat.fib 12) (Nat.fib 18) = Nat.fib 6 := by
  decide
  done

/-!
## Exercise 2

There is no `f : ℕ → ℕ` with `f (f n) = n + 2027` for every `n`.

The proof on paper: `f` shifts by `2027`, so it descends to a map on the `2027` residue classes,
and there it is an involution. An involution of a set with an odd number of elements has a fixed
point, so `f a ≡ a` for some `a`, that is `f a = a + 2027 * t`. Applying `f` once more gives
`a + 2027 = a + 2 * 2027 * t`, which is absurd. Note where `2027` odd is used: for an even shift
the statement is false, `f n = n + 1` solves `f (f n) = n + 2`.
-/

theorem exercise_2 : ¬ ∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 2027 := by
  intro hex
  obtain ⟨f, hf⟩ := hex
  -- Applying `f` to `hf n` turns `f (f n) = n + 2027` into a shift rule for `f` itself.
  have hstep : ∀ n, f (n + 2027) = f n + 2027 := by
    intro n
    rw [← hf n]
    exact hf (f n)
    done
  -- Iterating the shift rule: this is the induction that says `f` respects `2027`-periodicity.
  have hmul : ∀ m n, f (n + m * 2027) = f n + m * 2027 := by
    intro m
    induction m with
    | zero =>
      intro n
      simp
      done
    | succ k ih =>
      intro n
      have hassoc : n + (k + 1) * 2027 = (n + k * 2027) + 2027 := by ring
      rw [hassoc, hstep, ih]
      ring
      done
    done
  -- Hence `f n` mod `2027` only depends on `n` mod `2027`.
  have hmod : ∀ n, f (n % 2027) % 2027 = f n % 2027 := by
    intro n
    have hdiv : n % 2027 + (n / 2027) * 2027 = n := by
      rw [Nat.mul_comm]
      exact Nat.mod_add_div n 2027
    have hn := hmul (n / 2027) (n % 2027)
    rw [hdiv] at hn
    rw [hn, Nat.add_mul_mod_self_right]
    done
  -- `ZMod 2027` is the ring of integers mod `2027`, and `x.val` is the representative of `x`
  -- among `0, ..., 2026`. Read modulo `2027`, `f` is well defined on residues:
  have hcast : ∀ n : ℕ, ((f (n % 2027) : ℕ) : ZMod 2027) = ((f n : ℕ) : ZMod 2027) := by
    intro n
    rw [← ZMod.natCast_mod (f (n % 2027)), hmod, ZMod.natCast_mod]
    done
  -- so it induces a map on the residues.
  set s : ZMod 2027 → ZMod 2027 := fun x => ((f x.val : ℕ) : ZMod 2027)
  -- That map is an involution, because `f (f n) = n + 2027` and `2027 = 0` in `ZMod 2027`.
  have hinv : Function.Involutive s := by
    intro x
    show ((f ((f x.val : ℕ) : ZMod 2027).val : ℕ) : ZMod 2027) = x
    rw [ZMod.val_natCast, hcast, hf, Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_val,
      ZMod.cast_id]
    done
  -- An involution is a permutation with `σ ^ 2 = 1`, and `ZMod 2027` has an odd number of
  -- elements, so the permutation fixes some residue `x`.
  have hcard : ¬ (2 ∣ Fintype.card (ZMod 2027)) := by
    rw [ZMod.card]
    decide
    done
  have hpow : hinv.toPerm s ^ 2 ^ 1 = 1 := by
    ext x
    simp [pow_succ, hinv x]
    done
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hpow
  -- `hx` says exactly that `f x.val` and `x.val` have the same remainder mod `2027`.
  have hfix : f x.val % 2027 = x.val := by
    have hx' : ((f x.val : ℕ) : ZMod 2027) = x := hx
    have hval := congrArg ZMod.val hx'
    rwa [ZMod.val_natCast] at hval
    done
  -- So `f x.val = x.val + t * 2027` for some `t`, and applying `f` once more is a contradiction.
  obtain ⟨t, ht⟩ : ∃ t, f x.val = x.val + t * 2027 := ⟨f x.val / 2027, by omega⟩
  have hcontr := hmul t x.val
  rw [← ht, hf, ht] at hcontr
  omega
  done

/- The parity really is the point: with an even shift such an `f` does exist, and the proof above
breaks exactly at `hcard`. For `2026 = 2 * 1013`, adding `1013` twice does the job. -/
example : ∃ f : ℕ → ℕ, ∀ n, f (f n) = n + 2026 := by
  refine ⟨fun n => n + 1013, ?_⟩
  intro n
  show n + 1013 + 1013 = n + 2026
  omega
  done

/-!
## Exercise 3

`f 1, ..., f k, g` are linear functionals on a vector space `V`; then `g` is a linear combination
of the `f j` if and only if every vector killed by all the `f j` is killed by `g`.

Two remarks on the statement. First, "`g` is a linear combination of the `f j`" is
`g ∈ span {f j}`, and a finite family `f 1, ..., f k` is a function `Fin k → V →ₗ[K] K`. Second,
the hypothesis is about the *intersection* of the `ker (f j)`, spelled out here as "if all the
`f j` vanish at `v`, so does `g`". Asking instead that `ker (f j) ⊆ ker g` *for every `j`* would
make the statement false: with `k = 2` and `g = f 1 + f 2` the left-hand side holds while
`ker (f 1) ⊆ ker g` fails.
-/

theorem exercise_3 {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {k : ℕ}
    (f : Fin k → (V →ₗ[K] K)) (g : V →ₗ[K] K) :
    g ∈ Submodule.span K (Set.range f) ↔ ∀ v : V, (∀ j, f j v = 0) → g v = 0 := by
  constructor
  -- If `g = ∑ c j • f j` and every `f j` vanishes at `v`, then so does `g`.
  · intro hg v hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hg
    rw [← hc]
    simp [hv]
    done
  -- The other direction is the Mathlib lemma `mem_span_of_iInf_ker_le_ker`; all we have to do is
  -- to phrase our hypothesis as the inclusion `⨅ j, ker (f j) ≤ ker g` that it expects.
  · intro h
    apply mem_span_of_iInf_ker_le_ker
    intro v hv
    simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hv
    exact LinearMap.mem_ker.2 (h v hv)
    done


/-!
## Exercise 4 (analysis: subsequences of a convergent sequence)

`a n → L` and `φ : ℕ → ℕ` strictly increasing; then the subsequence `a (φ n)` converges to `L`.

Convergence is spelled out with `ε` and `N`, as in a first analysis course. The whole content of
the proof is that a strictly increasing `φ : ℕ → ℕ` satisfies `n ≤ φ n`, so the `N` that works for
the sequence works for the subsequence as well.
-/

theorem exercise_4 (a : ℕ → ℝ) (L : ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ha : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, |a (φ n) - L| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, ?_⟩
  intro n hn
  apply hN
  -- `N ≤ n` by assumption, and `n ≤ φ n` because `φ` is strictly increasing.
  exact le_trans hn hφ.le_apply
  done

/- Mathlib says "converges to `L`" with filters, as `Tendsto a atTop (nhds L)`. In that language
the exercise is a one-liner: a strictly increasing `φ : ℕ → ℕ` tends to infinity, and a limit
composed with a limit is a limit. -/
example (a : ℕ → ℝ) (L : ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (ha : Filter.Tendsto a Filter.atTop (nhds L)) :
    Filter.Tendsto (a ∘ φ) Filter.atTop (nhds L) := by
  exact ha.comp hφ.tendsto_atTop
  done

/-!
## Exercise 5 (linear algebra: idempotent linear maps)

`P : V → V` linear with `P ∘ P = P`; then `V = ker P ⊕ im P`.

`IsCompl A B` is how Mathlib says that two subspaces are in direct sum and together span
everything, which is exactly what `V = A ⊕ B` means; the image of `P` is `LinearMap.range P`.
-/

theorem exercise_5 {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (P : V →ₗ[K] V)
    (hP : P ∘ₗ P = P) : IsCompl (LinearMap.ker P) (LinearMap.range P) := by
  constructor
  -- The two subspaces meet only in `0`: if `x = P y` and `P x = 0` then `x = P (P y) = P x = 0`.
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [LinearMap.mem_ker] at hx
    obtain ⟨y, hy⟩ := hx'
    calc x = P y := hy.symm
      _ = P (P y) := by rw [← LinearMap.comp_apply, hP]
      _ = P x := by rw [hy]
      _ = 0 := hx
    done
  -- Together they span `V`, because `x = (x - P x) + P x` with `x - P x` in the kernel.
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hker : x - P x ∈ LinearMap.ker P := by
      rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply, hP, sub_self]
      done
    rw [Submodule.mem_sup]
    exact ⟨x - P x, hker, P x, ⟨x, rfl⟩, by abel⟩
    done

/-!
## Exercise 6 (algebra: subgroups of a cyclic group)

A subgroup of a cyclic group is cyclic.

`IsCyclic G` says that `G` is generated by a single element, and a subgroup `H` is regarded as a
group of its own. As in Exercise 1, Mathlib knows the result: `Subgroup.isCyclic`.
-/

theorem exercise_6 {G : Type*} [Group G] [IsCyclic G] (H : Subgroup G) : IsCyclic H := by
  exact Subgroup.isCyclic H
  done

/- Unfolding `IsCyclic`: some element of `H` generates it. -/
example {G : Type*} [Group G] [IsCyclic G] (H : Subgroup G) :
    ∃ g : H, ∀ h : H, h ∈ Subgroup.zpowers g := by
  exact (Subgroup.isCyclic H).exists_generator
  done

/-!
## Exercise 7 (two points where the derivatives are in harmony)

`f : [a, b] → [a, b]` continuous, differentiable on `(a, b)`, with `f a = a` and `f b = b`; then
there are two distinct `x, y ∈ (a, b)` with `1 / f' x + 1 / f' y = 2`.

The first hint, formalised. The intermediate value theorem gives `c ∈ (a, b)` with
`f c = (a + b) / 2`, and Lagrange's theorem on `[a, c]` and on `[c, b]` gives `x` and `y` with
`f' x = ((b - a) / 2) / (c - a)` and `f' y = ((b - a) / 2) / (b - c)`. The two reciprocals then add
up to `2 (c - a) / (b - a) + 2 (b - c) / (b - a) = 2`, and `x < c < y` keeps them distinct. Note
that the hypothesis that `f` maps `[a, b]` into itself is never used.
-/

theorem exercise_7 (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Set.Icc a b)) (hdiff : DifferentiableOn ℝ f (Set.Ioo a b))
    (hfa : f a = a) (hfb : f b = b) :
    ∃ x ∈ Set.Ioo a b, ∃ y ∈ Set.Ioo a b, x ≠ y ∧ 1 / deriv f x + 1 / deriv f y = 2 := by
  have hmid : (a + b) / 2 ∈ Set.Ioo (f a) (f b) := by
    rw [hfa, hfb]
    constructor <;> linarith
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo hab.le hcont hmid
  obtain ⟨x, hx, hdx⟩ := exists_deriv_eq_slope f hc.1
    (hcont.mono (Set.Icc_subset_Icc le_rfl hc.2.le))
    (hdiff.mono (Set.Ioo_subset_Ioo le_rfl hc.2.le))
  obtain ⟨y, hy, hdy⟩ := exists_deriv_eq_slope f hc.2
    (hcont.mono (Set.Icc_subset_Icc hc.1.le le_rfl))
    (hdiff.mono (Set.Ioo_subset_Ioo hc.1.le le_rfl))
  refine ⟨x, Set.Ioo_subset_Ioo le_rfl hc.2.le hx, y, Set.Ioo_subset_Ioo hc.1.le le_rfl hy,
    ne_of_lt (hx.2.trans hy.1), ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.2 hab.ne'
  have e1 : (a + b) / 2 - a = (b - a) / 2 := by ring
  have e2 : b - (a + b) / 2 = (b - a) / 2 := by ring
  rw [hdx, hdy, hfa, hfb, hfc, one_div_div, one_div_div, e1, e2]
  field_simp
  ring
  done

/-!
## Exercise 8 (the partial sums of `sin k` are bounded)

Rather than passing to the complex exponential, one can telescope with the product formula
`cos x - cos y = -2 sin ((x + y) / 2) sin ((x - y) / 2)`, which gives
`2 sin (1/2) * ∑_{k=1}^n sin k = cos (1/2) - cos (n + 1/2)`. The right-hand side is at most `2` in
absolute value, so `1 / sin (1/2)` bounds every partial sum.
-/

theorem exercise_8 : ∃ C : ℝ, ∀ n : ℕ, |∑ k ∈ Finset.Icc 1 n, Real.sin k| ≤ C := by
  have hs : 0 < Real.sin (1/2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · norm_num
    · linarith [Real.pi_gt_three]
  have key : ∀ n : ℕ, 2 * Real.sin (1/2) * (∑ k ∈ Finset.Icc 1 n, Real.sin k)
      = Real.cos (1/2) - Real.cos ((n : ℝ) + 1/2) := by
    intro n
    induction n with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), mul_add, ih]
      have hstep : Real.cos ((m : ℝ) + 1/2) - Real.cos ((m : ℝ) + 1 + 1/2)
          = 2 * Real.sin (1/2) * Real.sin ((m : ℝ) + 1) := by
        rw [Real.cos_sub_cos]
        have e1 : ((m : ℝ) + 1/2 + ((m : ℝ) + 1 + 1/2)) / 2 = (m : ℝ) + 1 := by ring
        have e2 : ((m : ℝ) + 1/2 - ((m : ℝ) + 1 + 1/2)) / 2 = -(1/2 : ℝ) := by ring
        rw [e1, e2, Real.sin_neg]
        ring
      push_cast
      linarith [hstep]
  refine ⟨1 / Real.sin (1/2), fun n => ?_⟩
  have hb : |2 * Real.sin (1/2) * (∑ k ∈ Finset.Icc 1 n, Real.sin k)| ≤ 2 := by
    rw [key n, abs_le]
    constructor
    · linarith [Real.neg_one_le_cos (1/2 : ℝ), Real.cos_le_one ((n : ℝ) + 1/2)]
    · linarith [Real.cos_le_one (1/2 : ℝ), Real.neg_one_le_cos ((n : ℝ) + 1/2)]
  rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 2 * Real.sin (1/2))] at hb
  rw [le_div_iff₀ hs]
  linarith
  done

/-!
## Exercise 9 (`∫_a^{2a} f(t)/t dt → L log 2`)

`f` continuous on `[0, ∞)` with limit `L` at `+∞`; then `∫_a^{2a} f t / t dt → L log 2`.

Since `∫_a^{2a} L / t dt = L log 2` for every `a > 0`, the difference is the integral of
`(f t - L) / t`. Once `a` is large enough that `|f t - L| ≤ ε'` from `a` on, that integral is
bounded by `∫_a^{2a} ε' / t dt = ε' log 2`, which is the whole proof: choose `ε'` with
`ε' log 2 < ε`.
-/

theorem exercise_9 (f : ℝ → ℝ) (L : ℝ) (hf : ContinuousOn f (Set.Ici 0))
    (hlim : Filter.Tendsto f Filter.atTop (nhds L)) :
    Filter.Tendsto (fun a => ∫ t in a..(2 * a), f t / t) Filter.atTop
      (nhds (L * Real.log 2)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlog0 : Real.log 2 ≠ 0 := hlog.ne'
  obtain ⟨ε', hε'pos, hε'lt⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' * Real.log 2 < ε := by
    refine ⟨ε / (2 * Real.log 2), by positivity, ?_⟩
    have h : ε / (2 * Real.log 2) * Real.log 2 = ε / 2 := by
      field_simp
    rw [h]
    linarith
  obtain ⟨A₀, hA₀⟩ := Metric.tendsto_atTop.1 hlim ε' hε'pos
  refine ⟨max A₀ 1, fun a ha => ?_⟩
  have ha1 : (1 : ℝ) ≤ a := le_trans (le_max_right _ _) ha
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha1
  have hA₀a : A₀ ≤ a := le_trans (le_max_left _ _) ha
  have hle : a ≤ 2 * a := by linarith
  -- On `[a, 2a]` everything in sight is continuous, hence integrable.
  have huIcc : Set.uIcc a (2 * a) = Set.Icc a (2 * a) := Set.uIcc_of_le hle
  have hpos : ∀ t ∈ Set.Icc a (2 * a), 0 < t := fun t ht => lt_of_lt_of_le ha0 ht.1
  have hcont : ContinuousOn (fun t : ℝ => f t / t) (Set.uIcc a (2 * a)) := by
    rw [huIcc]
    exact (hf.mono (fun t ht => le_of_lt (hpos t ht))).div continuousOn_id
      (fun t ht => (hpos t ht).ne')
  have hint1 : IntervalIntegrable (fun t : ℝ => f t / t) MeasureTheory.volume a (2 * a) :=
    hcont.intervalIntegrable
  have hcont2 : ∀ c : ℝ, ContinuousOn (fun t : ℝ => c / t) (Set.uIcc a (2 * a)) := by
    intro c
    rw [huIcc]
    exact continuousOn_const.div continuousOn_id (fun t ht => (hpos t ht).ne')
  have hint2 : ∀ c : ℝ, IntervalIntegrable (fun t : ℝ => c / t) MeasureTheory.volume a (2 * a) :=
    fun c => (hcont2 c).intervalIntegrable
  -- `∫ c / t` over `[a, 2a]` is `c * log 2`.
  have hconst : ∀ c : ℝ, (∫ t in a..(2 * a), c / t) = c * Real.log 2 := by
    intro c
    have h0 : (0 : ℝ) ∉ Set.uIcc a (2 * a) := by
      rw [huIcc]
      exact fun h => absurd h.1 (not_le.2 ha0)
    calc (∫ t in a..(2 * a), c / t) = ∫ t in a..(2 * a), c * (1 / t) := by
          simp only [mul_one_div]
      _ = c * ∫ t in a..(2 * a), 1 / t := intervalIntegral.integral_const_mul _ _
      _ = c * Real.log (2 * a / a) := by rw [integral_one_div h0]
      _ = c * Real.log 2 := by rw [mul_div_assoc, div_self ha0.ne', mul_one]
  -- The difference is an integral of something bounded by `ε' / t`.
  have hbound : ∀ t ∈ Set.Icc a (2 * a), |f t / t - L / t| ≤ ε' / t := by
    intro t ht
    have h0 : 0 < t := hpos t ht
    have hft : |f t - L| ≤ ε' := le_of_lt (by
      have := hA₀ t (le_trans hA₀a ht.1)
      rwa [Real.dist_eq] at this)
    rw [div_sub_div_same, abs_div, abs_of_pos h0]
    gcongr
  have key : |(∫ t in a..(2 * a), f t / t) - L * Real.log 2| ≤ ε' * Real.log 2 := by
    rw [← hconst L, ← intervalIntegral.integral_sub hint1 (hint2 L), ← hconst ε']
    calc |∫ t in a..(2 * a), (f t / t - L / t)|
        ≤ ∫ t in a..(2 * a), |f t / t - L / t| :=
          intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ t in a..(2 * a), ε' / t :=
          intervalIntegral.integral_mono_on hle ((hint1.sub (hint2 L)).abs) (hint2 ε') hbound
  rw [Real.dist_eq]
  exact lt_of_le_of_lt key hε'lt
  done

/-!
## Exercise 10 (a group of order `2d` with `d` odd has a subgroup of order `d`)

The road suggested on the sheet: Burnside's normal complement theorem, which Mathlib knows as
`MonoidHom.ker_transferSylow_isComplement'`. Because `d` is odd, a Sylow `2`-subgroup `P` has
exactly two elements; conjugation by an element of the normaliser of `P` sends the non-trivial
element of `P` to a non-trivial element of `P`, that is to itself, so the normaliser of `P`
centralises `P`. Burnside then produces a normal complement of `P`, whose order must be `d`. The
elementary proof, Cayley's embedding plus the sign of a permutation, is also possible but longer.
-/

theorem exercise_10 {G : Type*} [Group G] [Finite G] {d : ℕ} (hd : Odd d)
    (hG : Nat.card G = 2 * d) : ∃ H : Subgroup G, Nat.card H = d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp [Nat.odd_iff] at hd
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := inferInstance
  -- The Sylow 2-subgroup has exactly two elements, because `d` is odd.
  have hPcard : Nat.card P = 2 := by
    have hnd : ¬ (2 ∣ d) := by simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using hd
    have h2 : Nat.factorization (Nat.card G) 2 = 1 := by
      rw [hG, Nat.factorization_mul two_ne_zero hd0]
      simp [Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hnd]
    rw [P.card_eq_multiplicity, h2, pow_one]
  -- A subgroup with two elements is centralised by its normaliser.
  have hPc : Subgroup.normalizer (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨t, -, ht⟩ := (Nat.card_eq_two_iff' (1 : P)).1 hPcard
    by_cases hx1 : x = 1
    · simp [hx1]
    · have hy : n * x * n⁻¹ ∈ (P : Subgroup G) := (Subgroup.mem_normalizer_iff.1 hn x).1 hx
      have h1 : (⟨x, hx⟩ : P) = t := ht _ (by simpa [Subtype.ext_iff] using hx1)
      have h2 : (⟨n * x * n⁻¹, hy⟩ : P) = t := by
        refine ht _ ?_
        simp only [ne_eq, Subtype.ext_iff, OneMemClass.coe_one]
        intro hcon
        exact hx1 (by group at hcon ⊢; simpa using hcon)
      have : x = n * x * n⁻¹ := by
        have := h1.trans h2.symm
        simpa [Subtype.ext_iff] using this
      conv_lhs => rw [this]
      group
  -- Burnside's normal complement theorem gives a subgroup of order `d`.
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hPc
  refine ⟨(MonoidHom.transferSylow P hPc).ker, ?_⟩
  have := hcomp.card_mul_card
  rw [hPcard, hG] at this
  omega
  done

/-!
## Exercise 11 (a group is never the union of two proper subgroups)

"Union" is spelled out as the hypothesis that every element lies in `H` or in `K`; the conclusion
is that one of the two is the whole group. Pick `x ∉ K` and `y ∉ H`, so that `x ∈ H` and `y ∈ K`.
Then `x * y` lies in neither: in `H` it would force `y ∈ H`, in `K` it would force `x ∈ K`.
-/

theorem exercise_11 {G : Type*} [Group G] (H K : Subgroup G) (hcover : ∀ g : G, g ∈ H ∨ g ∈ K) :
    H = ⊤ ∨ K = ⊤ := by
  by_contra hcon
  have hH : H ≠ ⊤ := fun h => hcon (Or.inl h)
  have hK : K ≠ ⊤ := fun h => hcon (Or.inr h)
  obtain ⟨y, hy⟩ := SetLike.exists_not_mem_of_ne_top H hH
  obtain ⟨x, hx⟩ := SetLike.exists_not_mem_of_ne_top K hK
  have hxH : x ∈ H := (hcover x).resolve_right hx
  have hyK : y ∈ K := (hcover y).resolve_left hy
  rcases hcover (x * y) with hxy | hxy
  · exact hy (by simpa using H.mul_mem (H.inv_mem hxH) hxy)
  · exact hx (by simpa using K.mul_mem hxy (K.inv_mem hyK))
  done

/-!
## Exercise 12 (`(g h) ^ n = g ^ n * h ^ n` for `n = 3, 5` forces commutativity)

Cancelling on both sides of the cube identity gives `(h g) ^ 2 = g ^ 2 h ^ 2`. Combined with the
fifth-power identity it shows that squares commute with cubes and with fifth powers, hence with
`h = h ^ 3 (h ^ 2)⁻¹` — squares are central. Feeding that back into `(h g) ^ 2 = g ^ 2 h ^ 2` and
cancelling once more gives `g h = h g`.
-/

theorem exercise_12 {G : Type*} [Group G] (h3 : ∀ g h : G, (g * h) ^ 3 = g ^ 3 * h ^ 3)
    (h5 : ∀ g h : G, (g * h) ^ 5 = g ^ 5 * h ^ 5) (g h : G) : g * h = h * g := by
  -- Cancelling `g` on the left and `h` on the right in `(g * h) ^ 3 = g ^ 3 * h ^ 3`.
  have hA : ∀ g h : G, (h * g) ^ 2 = g ^ 2 * h ^ 2 := by
    intro g h
    have key := h3 g h
    have e1 : (g * h) ^ 3 = g * ((h * g) ^ 2 * h) := by simp [pow_succ, mul_assoc]
    have e2 : g ^ 3 * h ^ 3 = g * (g ^ 2 * h ^ 2 * h) := by group
    rw [e1, e2] at key
    exact mul_right_cancel (mul_left_cancel key)
  -- Squares commute with cubes.
  have hE : ∀ g h : G, g ^ 2 * h ^ 3 = h ^ 3 * g ^ 2 := by
    intro g h
    have key : g * (g ^ 2 * h ^ 3) = g * (h ^ 3 * g ^ 2) := by
      have e1 : g * (g ^ 2 * h ^ 3) = g ^ 3 * h ^ 3 := by group
      have e2 : (g * h) ^ 3 = (g * h) * (g * h) ^ 2 := by group
      rw [e1, ← h3 g h, e2, hA h g]
      group
    exact mul_left_cancel key
  -- Squares commute with fifth powers.
  have hD : ∀ g h : G, g ^ 5 * h ^ 2 = h ^ 2 * g ^ 5 := by
    intro g h
    have key : g ^ 5 * h ^ 2 * h ^ 3 = h ^ 2 * g ^ 5 * h ^ 3 := by
      have e1 : g ^ 5 * h ^ 2 * h ^ 3 = g ^ 5 * h ^ 5 := by group
      have e2 : (g * h) ^ 5 = (g * h) ^ 2 * (g * h) ^ 3 := by group
      rw [e1, ← h5 g h, e2, hA h g, h3 g h]
      group
    exact mul_right_cancel key
  -- Hence squares are central: `g ^ 2` commutes with `h ^ 3` and with `h ^ 5`, so with
  -- `h ^ 2 = h ^ 5 * (h ^ 3)⁻¹` and finally with `h = h ^ 3 * (h ^ 2)⁻¹`.
  have hsq : ∀ g h : G, g ^ 2 * h = h * g ^ 2 := by
    intro g h
    have c3 : Commute (g ^ 2) (h ^ 3) := hE g h
    have c5 : Commute (g ^ 2) (h ^ 5) := (hD h g).symm
    have c2 : Commute (g ^ 2) (h ^ 2) := by
      have e : h ^ 2 = h ^ 5 * (h ^ 3)⁻¹ := by group
      rw [e]
      exact c5.mul_right c3.inv_right
    have e : h = h ^ 3 * (h ^ 2)⁻¹ := by group
    rw [e]
    exact c3.mul_right c2.inv_right
  -- Now `(h * g) ^ 2 = g ^ 2 * h ^ 2 = h ^ 2 * g ^ 2` gives the result after two cancellations.
  have key : h * (g * h) * g = h * (h * g) * g := by
    have e1 : h * (g * h) * g = (h * g) ^ 2 := by simp [pow_succ, mul_assoc]
    have e2 : h * (h * g) * g = h ^ 2 * g ^ 2 := by simp [pow_succ, mul_assoc]
    rw [e1, e2, hA g h]
    exact hsq g (h ^ 2)
  exact mul_left_cancel (mul_right_cancel key)
  done

/-!
## Exercise 13 (symmetric plus antisymmetric matrices)

"The space of `n × n` matrices is the direct sum of the symmetric and the antisymmetric matrices"
is stated here as: every `A` is a sum `S + K` with `S` symmetric and `K` antisymmetric in exactly
one way, which is what `∃!` says. The two pieces are `(A + Aᵀ) / 2` and `(A - Aᵀ) / 2`; uniqueness
comes from transposing `A = S + K`, which gives `Aᵀ = S - K` and hence `2 S = A + Aᵀ`.
-/

open Matrix in
theorem exercise_13 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃! p : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ,
      p.1ᵀ = p.1 ∧ p.2ᵀ = -p.2 ∧ p.1 + p.2 = A := by
  refine ⟨((1/2 : ℝ) • (A + Aᵀ), (1/2 : ℝ) • (A - Aᵀ)), ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  · rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_transpose, ← smul_neg,
      neg_sub]
  · module
  · rintro ⟨S, K⟩ ⟨hS, hK, hSK⟩
    have hAT : Aᵀ = S - K := by
      rw [← hSK, Matrix.transpose_add, hS, hK, sub_eq_add_neg]
    ext i j <;> simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul,
      Matrix.transpose_apply] <;>
      · have h1 := congrFun (congrFun hSK i) j
        have h2 := congrFun (congrFun hAT i) j
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply] at h1 h2
        linarith
  done

/-!
## Exercise 14 (the parallelogram law)

Mathlib has it: `parallelogram_law_with_norm`, for an inner product space over `ℝ` or `ℂ`.
-/

theorem exercise_14 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v w : V) :
    ‖v + w‖ ^ 2 + ‖v - w‖ ^ 2 = 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  exact parallelogram_law_with_norm ℝ v w
  done

/-!
## Exercise 15 (antisymmetric matrices are not invertible)

As the sheet warns, the statement is false for `n` even: for `n = 2` the matrix `!![0, 1; -1, 0]`
is antisymmetric and invertible, as the second declaration below records. The odd case is proved
here: `det H = det Hᵀ = det (-H) = (-1) ^ n det H = -det H`, so `det H = 0`.
-/

open Matrix in
theorem exercise_15 {n : ℕ} (hn : Odd n) (H : Matrix (Fin n) (Fin n) ℝ) (hH : Hᵀ = -H) :
    ¬ IsUnit H := by
  have hdet : H.det = 0 := by
    have h1 : H.det = (-1 : ℝ) ^ n * H.det := by
      conv_lhs => rw [← Matrix.det_transpose H, hH, Matrix.det_neg, Fintype.card_fin]
    rw [hn.neg_one_pow] at h1
    linarith
  rw [Matrix.isUnit_iff_isUnit_det, hdet]
  simp
  done

/- The even case, refuted: this matrix is antisymmetric and invertible. -/
open Matrix in
example : ∃ A : Matrix (Fin 2) (Fin 2) ℝ, Aᵀ = -A ∧ IsUnit A := by
  refine ⟨!![0, 1; -1, 0], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]
    norm_num
  done
