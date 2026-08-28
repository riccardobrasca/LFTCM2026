# Exercises

Choose some of the following exercises, with the goal of proving them in Lean **by the end of the
week**. Don't worry if right now you don't even know how to *state* them: deciding what the formal
statement should look like is a large part of the work, and it is the part you will soon get better
at.

Each exercise carries two numbers, from 1 to 10:

- **Stating**: how hard it is to write the statement in Lean: finding the right definitions, the
  right way to say "the union of two subgroups", "converges to `L`", "direct sum".
- **Proving**: how hard it is to prove it once the statement is there.

The two are independent. Some exercises are painful to state and then proved by a single lemma
from Mathlib; others are one line to state and take an afternoon to prove. A low *proving* score
often means "Mathlib already knows this", in which case the exercise is really about searching
the library, which is a skill worth practising. Of course, you are also welcome to try to find
the proof yourself!

---

## 1. gcd of Fibonacci numbers

Let `F_n` be the `n`-th Fibonacci number. Prove that

> `gcd(F_m, F_n) = F_gcd(m, n)`.

**Stating: 2. Proving: 1.** Mathlib has this one, so the whole exercise is to find it. (Proving it
from scratch instead is a 9.)

## 2. A functional equation with no solution

Prove that there is no function `f : ℕ → ℕ` such that

> `f(f(n)) = n + 2027` for every `n ∈ ℕ`.

Bonus: prove that the analogue statement with `2026` is false.

**Stating: 2. Proving: 8.** The statement is a one-liner; the proof is not.

## 3. Functionals and their kernels

Let `f₁, ..., f_k, g` be linear functionals on a vector space `V`. Prove that `g` is a linear
combination of the `f_j` if and only if every vector annihilated by all the `f_j` is annihilated
by `g`.

**Stating: 7. Proving: 4.** "Linear combination of the `f_j`" is membership in a span, and a
finite family is a function out of `Fin k`.

## 4. Subsequences of a convergent sequence

Let `(a_n)` be a real sequence converging to `L`, and let `φ : ℕ → ℕ` be strictly increasing.
Prove that the subsequence `(a_φ(n))` converges to `L` as well.

**Stating: 4. Proving: 2.** You can spell convergence out with `ε` and `N`, or use Mathlib's
`Filter.Tendsto`. Do it both ways: the first is the definition you know, the second is the one the
library speaks, and seeing the same proof in both languages is the point of the exercise.

## 5. Idempotent linear maps

Let `P : V → V` be a linear map with `P ∘ P = P`. Prove that

> `V = ker P ⊕ im P`.

**Stating: 6. Proving: 4.** The interesting question is how to say "`⊕`" for two subspaces of a
given space. Mind also that `P ∘ P` has to be the composition of *linear maps*: write it as plain
function composition and `ker` no longer makes sense.

## 6. Subgroups of cyclic groups

Prove that a subgroup of a cyclic group is cyclic.

**Stating: 3. Proving: 1.** Mathlib knows it. The work is to say "a subgroup, regarded as a group
in its own right, is cyclic".

## 7. Two points where the derivatives are in harmony

Let `a < b` be real numbers and let `f : [a, b] → [a, b]` be continuous, differentiable on
`(a, b)`, with `f(a) = a` and `f(b) = b`. Prove that there are two distinct points
`x, y ∈ (a, b)` with

> `1/f'(x) + 1/f'(y) = 2`.

**Stating: 4. Proving: 7.**

## 8. The partial sums of `sin k` are bounded

Prove that the sequence

> `s_n = sin 1 + sin 2 + ... + sin n`,  `n ≥ 1`

is bounded.

**Stating: 3. Proving: 6.**

## 9. A limit of integrals

Let `f : [0, ∞) → ℝ` be continuous with a finite limit `L` at `+∞`. Prove that

> `lim_{a → +∞} ∫_a^{2a} f(t)/t dt = L log 2`.

**Stating: 7. Proving: 9.** The hardest of the sheet. Both the integral and the limit have to be
said in Mathlib's language, and the proof needs the integrals to exist before it can compare them.

## 10. A group of order `2d`

Let `d` be an odd positive integer and let `G` be a group of cardinality `2d`. Prove that `G` has a
subgroup `H` of cardinality `d`.

**Stating: 4. Proving: 9.** Mathlib offers a road through Burnside's normal complement theorem.

## 11. A group is not the union of two proper subgroups

Prove that a group is never the union of two proper subgroups.

**Stating: 4. Proving: 2.** Think about how to phrase "is the union of" — probably as a hypothesis
that every element lies in one of the two, with the conclusion that one of them is everything.
The proof is three lines and uses no theory at all.

## 12. Cubes and fifth powers force commutativity

Let `G` be a group such that

> `(gh)^n = g^n h^n` for all `g, h ∈ G` and all `n ∈ {3, 5}`.

Prove that `G` is abelian.

**Stating: 2. Proving: 7.** Nothing but cancellation, but you have to find the right chain of
cancellations.

## 13. Symmetric and antisymmetric matrices

Prove that the space of `n × n` matrices decomposes as the direct sum of the subspace of symmetric
matrices and the subspace of antisymmetric ones.

**Stating: 6. Proving: 5.** As in exercise 5, the question is how to say "direct sum" — either
with two subspaces, or by saying that every matrix splits as a sum of a symmetric and an
antisymmetric one in exactly one way.

## 14. The parallelogram law

Prove that for all `v, w` in a real vector space with a positive definite inner product,

> `‖v + w‖² + ‖v - w‖² = 2(‖v‖² + ‖w‖²)`.

**Stating: 2. Proving: 1.** In Mathlib already. The exercise is to set up the right space with the
right hypotheses and then find the lemma.

## 15. Antisymmetric matrices are singular

Let `n` be a positive integer and let `H` be an antisymmetric `n × n` matrix. Prove that `H` is not
invertible.

**Stating: 3. Proving: 3.** Careful: as stated this is *false* for `n` even — find a `2 × 2`
counterexample first, then prove the odd case. Formalising a counterexample is itself a useful
exercise: it is how you check that a statement you are about to spend an afternoon on is actually
true.
