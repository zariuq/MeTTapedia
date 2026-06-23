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
From entropy you build **Kullback–Leibler divergence** `KL(p ‖ q)` — how many extra
bits you waste by coding for `q` when the truth is `p` — and **mutual information**,
the entropy shared between two variables. This directory formalizes these finite
discrete measures and the bridges to Mathlib's measure-theoretic versions.

A second, deeper theme runs through the `ShannonEntropy/` subdirectory: *why* is
`-Σ pᵢ log pᵢ` the right formula and not some other function? The answer is an
**axiomatic characterization**. If you write down a handful of properties any
sensible "uncertainty measure" must have — symmetry, a grouping/chain rule, a
normalization, and some continuity — then those properties *force* the function to
be Shannon entropy (up to a constant). Three classical axiom systems do this, and
this directory proves they all pin down the same function:

- **Faddeev (1956)** — the *minimal* system: only 4 axioms (binary continuity,
  symmetry, recursivity, normalization). It *derives* full continuity,
  monotonicity, maximality, and expansibility.
- **Shannon (1948)** — the original 5-axiom system (relabeling, full continuity,
  monotonicity on uniforms, grouping, normalization).
- **Shannon–Khinchin (1957)** — 5 axioms that *assume* full continuity, maximality,
  and expansibility (exactly what Faddeev proves).

The payoff is that all three are equivalent, so "entropy" is not an arbitrary
choice but a forced one.

## Components

| File | Contents |
|------|----------|
| `Basic.lean` | core types: `ProbVec n` (distributions over `Fin n`), `shannonEntropy` `H(p) = -Σ pᵢ log pᵢ`, `uniformDist` |
| `EntropyKL.lean` | curated single-import surface tying entropy/KL together across the axiomatic, Knuth–Skilling, and measure-theoretic routes; bridge glue (`probVecEquivProbDist`, `shannonEntropy_eq_ks_shannonEntropy`, `klDivergenceVec`) |
| `MutualInformation.lean` | pointwise log-ratio information gain (the scalar in `posterior = prior · 2^score`) vs. Shannon mutual information of a joint distribution |
| `BinomialEntropy.lean` | exact natural-number entropy bounds on binomial coefficients `2^{n·H(k/n)}/(n+1) ≤ C(n,k) ≤ 2^{n·H(k/n)}`, stated without real logs — workhorse counting estimates |
| `Main.lean` | aggregate entry point (finite entropy, mutual information, K&S bridge) |
| `ShannonEntropy/` (8 files) | the axiomatic-characterization development — see below |

### `ShannonEntropy/` — the axiomatic-characterization lane

| File | Contents |
|------|----------|
| `Shannon1948.lean` | Shannon's original 5-axiom `ShannonEntropy` structure; proof that `Σ negMulLog(pᵢ)` satisfies it |
| `ShannonKhinchin.lean` | the Shannon–Khinchin 5-axiom system (`ShannonKhinchinEntropy`); entropy satisfies it; full ⇒ binary continuity |
| `Faddeev.lean` | Faddeev's minimal 4-axiom system (`FaddeevEntropy`); the uniqueness route `F(n) = log₂(n)` and derived monotonicity (**has the one open `sorry`**, see below) |
| `Equivalence.lean` | glue theorems: `faddeev_iff_shannonKhinchin` (the two systems characterize the same function) |
| `Interface.lean` | unified view of all three axiomatizations + the `ProbVec ≃ ProbDist` bridge; the explicit minimality statements |
| `Properties.lean` | fundamental facts: `H ≥ 0`, `H ≤ log n` (uniform-maximal), `H = 0 ⇔` point mass, continuity, permutation invariance |
| `MeasureTheoreticBridge.lean` | embeds finite distributions into Mathlib `Measure (Fin n)` over counting measure; connects to `klDiv` |
| `Main.lean` | reviewer-friendly shipping entry point for the entropy axiomatizations |

## Formalization status

No source-level `axiom` declarations appear in this directory — a source grep, *not*
a per-theorem `#print axioms` audit (a theorem can still inherit a Mathlib axiom
transitively). Proof state:

- **`sorry`-free:** everything except the one gap below — `Basic`, `EntropyKL`,
  `MutualInformation`, `BinomialEntropy`, `Main`, and within `ShannonEntropy/` the
  `Shannon1948`, `ShannonKhinchin`, `Properties`, `Equivalence`, `Interface`,
  `MeasureTheoreticBridge`, and `Main` files.
- **One open `sorry`** (in `ShannonEntropy/Faddeev.lean`, see footer): the lemma
  `faddeev_c_prime_all_equal` — Faddeev's Lemma 9, asserting that the per-prime
  constants `c_p := F(p)/log(p)` are all equal (`c_p = c_q` for all primes `p, q`).
  This is the keystone of the Faddeev uniqueness route: once it holds, `F(n) =
  log₂(n)` follows (`faddeev_F_eq_log2`), and from there the derived monotonicity,
  full continuity, and maximality. The surrounding development (the structure, the
  λ → 0 increment machinery in the lemmas leading up to it, and the downstream
  consequences) is in place; only this combinatorial identity is unproved, and a
  forensic non-building proof attempt is retained in a comment block beneath it.

**Trusted base.** There is no `native_decide` anywhere in this directory, so nothing
here compile-evaluates in place of kernel checking; the trusted base is Lean's
kernel plus whatever Mathlib axioms the imported lemmas carry.

Reproduce from this directory — the `sorry`/`admit` regex is a *raw* scan that can
also match prose in comments/strings, so the per-file count in the footer below is
the authoritative comment-stripped figure:

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Claude E. Shannon, [*A Mathematical Theory of Communication*](https://onlinelibrary.wiley.com/doi/abs/10.1002/j.1538-7305.1948.tb01338.x), Bell System Technical Journal 27 (1948), 379–423 and 623–656 ([archive scan](https://ia803209.us.archive.org/27/items/bstj27-3-379/bstj27-3-379_text.pdf)) — the origin of entropy and the original 5-axiom characterization (`Shannon1948.lean`).
- D. K. Faddeev, "On the concept of entropy of a finite probabilistic scheme" (Russian), Uspekhi Mat. Nauk 11 (1956), no. 1(67), 227–231 — the minimal 4-axiom system (`Faddeev.lean`); see this [English translation](https://arrowtheory.com/pub/notes/025-faddeev-entropy.html) and the discussion in John Baez's [*Entropy as a functor*](https://ncatlab.org/johnbaez/show/Entropy+as+a+functor).
- A. Ya. Khinchin, [*Mathematical Foundations of Information Theory*](https://archive.org/details/mathematicalfoun0000khin) (Dover, 1957) — the Shannon–Khinchin axioms (`ShannonKhinchin.lean`).
- Tom Leinster, [*An Operadic Introduction to Entropy*](https://golem.ph.utexas.edu/category/2011/05/an_operadic_introduction_to_en.html) (The n-Category Café, 2011) — cited in `Faddeev.lean` for the operadic/uniqueness viewpoint.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 13 .lean files, 1 with sorries.*
- `ShannonEntropy/Faddeev.lean` — 1 sorry
