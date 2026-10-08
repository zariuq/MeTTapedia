# Information Theory (Lean 4)

## What this is about

When you learn the outcome of a coin flip, you gain *information* — and a loaded
coin tells you less than a fair one, because you could already guess how it would
land. **Information theory** makes that intuition exact. The central quantity is
**Shannon entropy**

```
H(p) = -Σ pᵢ log pᵢ
```

the average "surprise" of a distribution `p`: it is largest when `p` is uniform
(maximal uncertainty) and zero when `p` is a point mass (no uncertainty at all).
From entropy you build **Kullback–Leibler divergence** `KL(p ‖ q)` — extra
description length when coding for `q` while the truth is `p` — and **mutual information**,
the entropy shared between two variables. This directory formalizes these finite
discrete measures and the bridges to Mathlib's measure-theoretic versions.

A second, deeper theme runs through the `ShannonEntropy/` subdirectory: *why* is
`-Σ pᵢ log pᵢ` the right formula and not some other function? The answer is an
**axiomatic characterization**. If you write down a handful of properties any
sensible "uncertainty measure" must have — symmetry, a grouping/chain rule, a
normalization, and some continuity — then those properties *force* the function to
be Shannon entropy (up to a constant). Three classical axiom systems do this, and
this directory proves they all pin down the same function:

- **Faddeev (1956)** — four clauses (binary continuity,
  symmetry, recursivity, normalization). It *derives* full continuity,
  monotonicity, maximality, and expansibility.
- **Shannon (1948)** — four structural clauses (relabeling, full continuity,
  monotonicity on uniforms and grouping). Normalization is separate, so its
  uniqueness theorem is up to a constant scale.
- **Shannon–Khinchin (1957)** — five named clauses, plus explicit relabeling,
  that *assume* full continuity, maximality and expansibility.

Within these hypotheses the entropy formula is forced. Presentation counts
alone do not prove axiom independence or absolute minimality. Natural-log entropy
is measured in nats; dividing by `log 2` gives the normalized entropy in bits.

## Components

| File | Contents |
|------|----------|
| `Basic.lean` | core types: `ProbVec n` (distributions over `Fin n`), `shannonEntropy` `H(p) = -Σ pᵢ log pᵢ`, `uniformDist` |
| `EntropyKL.lean` | curated single-import interface tying entropy/KL together across the axiomatic, Knuth–Skilling, and measure-theoretic routes; bridge glue (`probVecEquivProbDist`, `shannonEntropy_eq_ks_shannonEntropy`, `klDivergenceVec`) |
| `MutualInformation.lean` | pointwise log-ratio information gain (the scalar in `posterior = prior · 2^score`) vs. Shannon mutual information of a joint distribution |
| `BinomialEntropy.lean` | exact natural-number entropy bounds on binomial coefficients `2^{n·H(k/n)}/(n+1) ≤ C(n,k) ≤ 2^{n·H(k/n)}`, stated without real logs — workhorse counting estimates |
| `Main.lean` | aggregate entry point (finite entropy, mutual information, K&S bridge) |
| `ShannonEntropy/` (8 files) | the axiomatic-characterization development — see below |

### `ShannonEntropy/` — the axiomatic-characterization lane

| File | Contents |
|------|----------|
| `Shannon1948.lean` | four-clause `Shannon1948Entropy`, its concrete model and uniqueness up to scale; normalization is separate |
| `ShannonKhinchin.lean` | five named clauses plus relabeling (`ShannonKhinchinEntropy`); entropy satisfies them; full ⇒ binary continuity |
| `Faddeev.lean` | four-clause `FaddeevEntropy`; axiom-preserving adapter to the canonical coefficient proof; `F(n) = log₂(n)` and full entropy uniqueness |
| `Equivalence.lean` | entropy-preserving bridges between Faddeev and Shannon–Khinchin; a separate inhabitedness corollary |
| `Interface.lean` | derived axiom transfers, presentation-count comparisons and the `ProbVec ≃ ProbDist` bridge |
| `Properties.lean` | fundamental facts: `H ≥ 0`, `H ≤ log n` (uniform-maximal), `H = 0 ⇔` point mass, continuity, permutation invariance |
| `MeasureTheoreticBridge.lean` | embeds finite distributions into Mathlib `Measure (Fin n)` over counting measure; connects to `klDiv` |
| `Main.lean` | reviewer-friendly shipping entry point for the entropy axiomatizations |

## Proof qualification

Faddeev's prime-coefficient equality is transported from the canonical standalone
`InformationTheory.ShannonEntropy.Faddeev` module. The
`FaddeevEntropy.toStandalone` adapter preserves the entropy function and all four
axioms; no full-continuity, monotonicity or nonnegativity assumption is added.

The resulting chain proves the uniform formula, uniqueness on all finite
probability vectors, full continuity, maximality and expansibility. The
Shannon–Khinchin bridges preserve the entropy function; their inhabitedness
corollary is separate from these function-preservation theorems.

A repeatable qualification check audits transitive axioms of all kernel
declarations in the finite entropy-characterization modules, including the
canonical proof. Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
It includes fair-coin normalization, exclusion of zero ternary-uniform entropy,
and a negative control checking that `sorryAx` is rejected.

Run from the Lean project root:

```bash
lake build Mettapedia.InformationTheory.ShannonEntropy.Main
lake env lean scripts/check_faddeev_axioms.lean
```

This audit qualifies the named entropy chain, not the whole Mettapedia library.
The adapter's types and transport lemmas also ensure that incompatible changes
to the canonical axioms or coefficient definitions are caught at compilation.

## References

- Claude E. Shannon, [*A Mathematical Theory of Communication*](https://onlinelibrary.wiley.com/doi/abs/10.1002/j.1538-7305.1948.tb01338.x), Bell System Technical Journal 27 (1948), 379–423 and 623–656 ([archive scan](https://ia803209.us.archive.org/27/items/bstj27-3-379/bstj27-3-379_text.pdf)) — the origin of entropy (`Shannon1948.lean`).
- D. K. Faddeev, "On the concept of entropy of a finite probabilistic scheme" (Russian), Uspekhi Mat. Nauk 11 (1956), no. 1(67), 227–231 — the binary-continuity characterization (`Faddeev.lean`); see this [English translation](https://arrowtheory.com/pub/notes/025-faddeev-entropy.html) and the discussion in John Baez's [*Entropy as a functor*](https://ncatlab.org/johnbaez/show/Entropy+as+a+functor).
- A. Ya. Khinchin, [*Mathematical Foundations of Information Theory*](https://archive.org/details/mathematicalfoun0000khin) (Dover, 1957) — the Shannon–Khinchin axioms (`ShannonKhinchin.lean`).
- Tom Leinster, [*An Operadic Introduction to Entropy*](https://golem.ph.utexas.edu/category/2011/05/an_operadic_introduction_to_en.html) (The n-Category Café, 2011) — cited in `Faddeev.lean` for the operadic/uniqueness viewpoint.
