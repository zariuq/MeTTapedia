# Higher-Order Probability (Lean 4)

## What this is about

Ordinary probability asks "how likely is rain tomorrow?" *Higher-order* probability
asks a stranger question: "how confident am I in my own confidence?" — a probability
*about* a probability. If you are unsure whether a coin is fair, you might hold a
distribution over its bias `θ`, and then a distribution over `θ` on top of that.
This shows up everywhere uncertainty is layered: hierarchical Bayesian models,
second-order (credence-about-credence) uncertainty, and imprecise probability.

The natural worry is that this could regress forever — distributions over
distributions over distributions. **Kyburg's flattening theorem** (1988) settles
it: a higher-order probability can always be *flattened* into an ordinary one by
taking the marginal of a joint distribution, and you lose nothing decision-relevant
in doing so. Concretely, if `κ : Θ → Measure X` is a family of distributions indexed
by a parameter `θ`, and `μ` is your distribution over `θ`, then the flattened
distribution

```
flatten = ∫ κ(θ) dμ(θ)     (the marginal of the joint  μ ⊗ κ  on  Θ × X)
```

makes the same predictions and supports the same optimal decisions as reasoning with
the two-level object. There is "no advantage" to keeping the levels separate.

The clean way to see *why* flattening is canonical rather than ad hoc is category
theory: `flatten` is exactly the **monadic bind / join of the Giry monad** (the monad
of probability measures). The monad laws — left/right identity and associativity —
are precisely the consistency properties Kyburg's reduction needs, so flattening is
mathematically forced, not a modelling convenience. This directory formalizes the
flattening theorem, its Giry-monad characterization, and the bridge showing the
de Finetti mixture models elsewhere in Mettapedia are themselves Kyburg flattenings.

## Components

| File | Contents |
|------|----------|
| `Basic.lean` | the core object `ParametrizedDistribution` (a Markov kernel `κ : Θ → Measure X` plus a mixing measure `μ` over parameters); `flatten` (the marginal `κ ∘ₘ μ`); `kyburgJoint` (`μ ⊗ₘ κ` on `Θ × X`); the probability-measure instances and the marginal/sum/deterministic basic lemmas |
| `KyburgFlattening.lean` | the flattening results: `kyburg_flattening` (marginalizing the joint recovers the mixture), `flatten_is_marginal`, `expectation_consistency` (`E[U] = E[E[U∣θ]]`), `kyburg_no_advantage` (decision-theoretic equivalence), and `flatten_is_monad_multiplication` |
| `GiryMonad.lean` | the categorical identification: `flatten_is_bind`, `flatten_is_join`, and the monad laws `flatten_left_identity`, `flatten_right_identity`, `flatten_associativity` (plus a kernel-level associativity and a monad-route `kyburg_no_advantage_via_monad`) |
| `DeFinettiConnection.lean` | packages the Bernoulli-mixture model from `Mettapedia.Logic.DeFinetti` as a `ParametrizedDistribution`; the singleton bridge `flatten(pd M n) {xs} = ENNReal.ofReal (M.prob xs)` — "de Finetti is Kyburg" for binary observations |
| `CategoricalConnection.lean` | the same bridge generalized from binary (Bool) to k-ary (`Fin k`) observations, built on `Mettapedia.Logic.CategoricalMixture`: `catKernel`, `catPMF`, `sum_catWeight_eq_one`, `flatten_apply_singleton` |
| `ProbabilityMeasureBorelBridge.lean` | supporting measurability infrastructure: derives `BorelSpace (ProbabilityMeasure Ω)` from `BorelSpace (FiniteMeasure Ω)` via `ProbabilityMeasure.toFiniteMeasure` (needed so mixing measures over the parameter space are well-typed) |

### Connection to PLN (developed elsewhere)

The motivation for this directory is the higher-order PLN story: PLN's evidence
counts `(n⁺, n⁻)` are the sufficient statistic for a Beta–Bernoulli Kyburg
flattening, so PLN's compact strength/confidence pair *is* a flattened second-order
belief. That reduction is formalized in the **sibling** directory
`Mettapedia/Logic/HigherOrder/` (`PLNKyburgReduction.lean`), which builds on the
flattening API here together with `Mettapedia/Logic/EvidenceQuantale.lean`. It is
out of scope for this directory and not counted in the file totals below.

## Formalization status

No source-level `axiom` declarations appear in this directory — a source grep, *not*
a per-theorem `#print axioms` audit (a theorem can still inherit a Mathlib axiom
transitively, e.g. through the Giry-monad and measure-theory development it builds
on). All six `.lean` files are **`sorry`-free**.

**Trusted base.** There is no `native_decide` anywhere in this directory, so nothing
here compile-evaluates in place of kernel checking; the trusted base is Lean's
kernel plus whatever Mathlib axioms the imported measure-theory lemmas carry.

Reproduce from this directory — the `sorry`/`admit` regex is a *raw* scan that can
also match prose in comments/strings, so the per-file count in the footer below is
the authoritative comment-stripped figure:

```bash
# sorry/admit occurrences (prints nothing):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Henry E. Kyburg, Jr., [*Higher Order Probabilities*](https://arxiv.org/pdf/1304.2714), in Uncertainty in Artificial Intelligence 3 (1987/88) — the flattening theorem this directory formalizes ("higher-order probabilities can always be replaced by marginal distributions of joint probability distributions").
- Michèle Giry, [*A categorical approach to probability theory*](https://doi.org/10.1007/BFb0092872), Lecture Notes in Mathematics 915 (Springer, 1982), 68–85 — the Giry monad that makes `flatten` a monadic bind/join.
- F. William Lawvere, [*The category of probabilistic mappings*](https://ncatlab.org/nlab/files/lawvereprobability1962.pdf) (seminar notes, 1962; [Lawvere Archives scan](https://lawverearchives.com/wp-content/uploads/2025/07/1962.probmap.pdf)) — the origin of the categorical view of probabilistic maps, cited in `GiryMonad.lean`.
- de Finetti's exchangeability/mixture theory, as formalized in `Mettapedia/Logic/DeFinetti.lean` and `Mettapedia/Logic/CategoricalMixture.lean` — the source of the mixture models the `*Connection.lean` files identify as Kyburg flattenings.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 6 .lean files, 0 with sorries.*
