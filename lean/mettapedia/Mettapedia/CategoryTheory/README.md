# Category Theory foundations for OSLF, PLN & de Finetti (Lean 4)

## What this is about

A lot of mathematics is easier to *do* once you notice that two very different
objects share the same shape. **Category theory** is the language for spotting
and exploiting that shared shape: instead of studying things one at a time, you
study them together with the structure-preserving maps between them, and many
"deep" facts turn out to be the statement that some map is *universal* — the
single best one of its kind. This directory supplies the categorical scaffolding
that the rest of Mettapedia stands on, organized around two payoffs.

- **Logic can be read off from a programming language, mechanically.** Given a
  language presented as a *theory*, one can form the category of presheaves over
  it and use the *internal language* of the resulting topos as a type system that
  talks about both the structure and the runtime behaviour of programs. This is
  the **OSLF / native-type-theory** idea (Meredith-Stay-Williams), and the
  lambda-theory strand here builds the pieces — subobject fibrations, the
  Grothendieck construction `∫ Sub`, Kripke-Joyal semantics, modal comprehension
  types — that PLN's truth-value logic plugs into.
- **"Order doesn't matter" is a universal property, not a coincidence.** A
  sequence of observations is *exchangeable* when any reshuffling has the same
  law. **de Finetti's theorem** says such a sequence is secretly a *mixture* of
  i.i.d. sequences: there is a hidden parameter, and conditioning on it makes the
  observations independent. Phrased categorically, the exchangeable law is the
  apex of a **limit cone** over the diagram of finite permutations, and the
  mixing measure is the unique mediating map. The de Finetti strand makes that
  precise and then carries it across the Giry / Markov-category machinery to the
  Markov-chain and hidden-Markov settings.

A recurring engineering theme: these objects live at the boundary of what
Mathlib's measure theory states comfortably, so the bridges deliberately stop at
an *honest* level (prefix laws, fixed emission kernels) and flag where a full
measurable kernel on a parameter space would be future work, rather than
overclaiming.

## Architecture

Three strands, 29 files in total:

- **Lambda theory / native type theory** (7 files) — the OSLF/PLN categorical
  logic core.
- **Categorical de Finetti** (the `DeFinetti*` files plus
  `FiniteHiddenMarkovDeFinettiBridge`) — exchangeability as a limit-cone
  universal property, plus Giry / Markov-category / Borel bridges, export
  surfaces, a smoke test, and an explicit counterexample.
- **Supporting structure** — the unit-interval fuzzy frame for PLN truth values,
  Meredith's theory of graphs, generalized open maps (bisimulation), and the
  Kripke-Joyal internal-language file.

### Lambda theory and native type theory strand

- `LambdaTheory.lean`
  - LambdaTheory.lean defines SubobjectFibration and LambdaTheory with finite limits and Heyting fibers

- `NativeTypeTheory.lean`
  - NativeTypeTheory.lean defines NativeTypeBundle as a Grothendieck construction

- `PLNInstance.lean`
  - PLNInstance.lean defines PLN as a frame-fiber instance with modal composition

- `PLNTerms.lean`
  - PLNTerms.lean defines PLN term syntax and reduction relation

- `ModalTypes.lean`
  - ModalTypes.lean defines modal types via comprehension and rely-possibly semantics

- `Hypercube.lean`
  - Hypercube.lean defines the H_Sigma endofunctor for modal type generation

- `PLNSemiringQuantale.lean`
  - PLNSemiringQuantale.lean defines a semiring quantale on Evidence with tensor and plus

### Categorical de Finetti strand

- `DeFinettiCategoricalInterface.lean`
  - DeFinettiCategoricalInterface.lean defines a qualitative factorization interface

- `DeFinettiPermutationCone.lean`
  - DeFinettiPermutationCone.lean proves permutation commutation of finite-prefix laws

- `DeFinettiKernelInterface.lean`
  - DeFinettiKernelInterface.lean defines kernel-level categorical de Finetti interfaces

- `DeFinettiSequenceKernelCone.lean`
  - DeFinettiSequenceKernelCone.lean defines sequence-kernel permutation cones on Bool power N

- `DeFinettiHausdorffBridge.lean`
  - DeFinettiHausdorffBridge.lean proves Hausdorff moment uniqueness links

- `DeFinettiPerNDiagram.lean`
  - DeFinettiPerNDiagram.lean defines per-n permutation diagram surfaces

- `DeFinettiGlobalFinitaryDiagram.lean`
  - DeFinettiGlobalFinitaryDiagram.lean defines global finitary-permutation indexing

- `DeFinettiLimitConePackage.lean`
  - DeFinettiLimitConePackage.lean packages the universal-property layer

- `DeFinettiKleisliGirySkeleton.lean`
  - DeFinettiKleisliGirySkeleton.lean defines Kleisli Giry global diagrams and IID cones

- `DeFinettiMarkovCategoryBridge.lean`
  - DeFinettiMarkovCategoryBridge.lean provides a MarkovCategoryCore viewpoint

- `DeFinettiMarkovGiryBridge.lean`
  - Packages the proved measure-theoretic `MarkovMixture` interface as a Kleisli(Giry) mediator `1 ⟶ G(MarkovParam k)` and the induced sequence-level cylinder factorization (stops short of a full measurable kernel `MarkovParam k ⟶ G((Fin k)^ℕ)`)

- `DeFinettiHigherOrderGiryBridge.lean`
  - Lifts the higher-order raw-cylinder theorem into the Borel `ProbMarkov` bridge by reducing order-`m` chains to first-order chains on encoded finite context states

- `FiniteHiddenMarkovDeFinettiBridge.lean`
  - Finite-state / finitely-emitting hidden Markov models at the de Finetti boundary: latent law as a Borel measure on `MarkovParam`, fixed emission kernel, observed finite-word law via `observedWordProb`

- `DeFinettiSmokeTest.lean`
  - `#check`s that the headline aliases and key API theorems (positive results and the negative `not_allSourcesKleisli_unrestricted`) resolve correctly

- `DeFinettiUnrestrictedCounterexample.lean`
  - Proves the unrestricted all-sources Kleisli mediator property is FALSE: counting measure on `ℕ → Bool` is finitary-permutation invariant yet admits no mixing mediator (interior `iid(θ)` puts mass 0 on every singleton, but `count({ω₀}) = 1`)

- `DeFinettiExternalBridge.lean`
  - DeFinettiExternalBridge.lean provides bridges to vendored exchangeability formalization

- `DeFinettiStableExports.lean`
  - DeFinettiStableExports.lean provides stable alias exports

- `DeFinettiExports.lean`
  - DeFinettiExports.lean provides the recommended import surface

### Other

- `FuzzyFrame.lean`
  - FuzzyFrame.lean formalizes the unit interval frame for PLN truth values

- `GeneralizedOpenMaps.lean`
  - GeneralizedOpenMaps.lean defines the minimal generalized-open-map core:
    `BisimulationKit`, `GOpen`, `PathBisim`, `StrongPathBisim`, and `(E,S)`-style
    span witness equivalence (`pathBisim_iff_esBisimilar`)

- `TOGL.lean`
  - TOGL.lean formalizes Greg Meredith's theory of graphs

- `Topos/InternalLanguage.lean`
  - Topos/InternalLanguage.lean formalizes Kripke-Joyal semantics for OSLF

## Open-map bridge map

- `GeneralizedOpenMaps.lean`
  - Core theorem: `pathBisim_iff_esBisimilar`
- `../Languages/ProcessCalculi/PiCalculus/WeakBisimOpenMapBridge.lean`
  - Core theorem: `weakRestrictedBisim_iff_pathBisim`
- `../Languages/ProcessCalculi/PiCalculus/BranchingBisim.lean`
  - Core theorem: `branching_implies_weak`
- `../Logic/WeightedOpenMaps.lean`
  - Core theorem: `weightedBisim_iff_gopen_span`
- `../Logic/OSLFOpenMapBridge.lean`
  - Core theorem: `fullOpenWitness_implies_obsEq`

## Formalization status

Every `.lean` file in this directory (29 files) is `sorry`-free and `admit`-free.
There are **no source-level `axiom` declarations** here — a source grep, *not* a
per-theorem `#print axioms` audit, so a theorem can still inherit a Mathlib axiom
(e.g. `propext`, choice, `Quot.sound`) transitively.

**Trusted base.** There is **no `native_decide` anywhere in this directory**, so
nothing here compile-evaluates in place of kernel checking; nothing in this lane
enlarges the trusted base beyond Mathlib's own.

Reproduce from this directory — the `sorry`/`admit` regex below is a *raw* scan
that also matches prose in comments and docstrings (e.g. "exchangeable processes
admit a factorization", and the literal "(0 sorry)" note in `TOGL.lean`), so the
authoritative figures are the comment-stripped footer counts:

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*(noncomputable\s+)?axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## Dependency flow

The dependency flow is the following architecture diagram.

```
LambdaTheory -> PLNInstance -> NativeTypeTheory
                    |
              PLNTerms -> ModalTypes -> Hypercube

DeFinettiCategoricalInterface -> PermutationCone -> KernelInterface
  -> SequenceKernelCone -> HausdorffBridge -> PerNDiagram
  -> GlobalFinitaryDiagram -> KleisliGirySkeleton -> StableExports -> Exports
```

## References

- L. Gregory Meredith, Mike Stay & Christian Williams — *Operational Semantics
  in Logical Form* (OSLF), the algorithm `NativeTypeTheory.lean` and
  `Topos/InternalLanguage.lean` formalize (the `∫ Sub` Grothendieck construction
  and Kripke-Joyal semantics for the modal comprehension types).
- Christian Williams & Mike Stay, [*Native Type Theory*](https://arxiv.org/abs/2102.04672)
  (arXiv:2102.04672, 2021) — the published companion: model a language as a
  theory, take presheaves, and reason in the internal language of the topos.
- L. Gregory Meredith, *A formal theory of graphs* — the notes formalized in
  `TOGL.lean` (the `G[X, V]` theory-of-graphs construction).
- Bruno de Finetti, *La prévision: ses lois logiques, ses sources subjectives*,
  Annales de l'Institut Henri Poincaré 7 (1937) — the exchangeability / mixture
  representation that the `DeFinetti*` strand renders as a limit-cone universal
  property. Modern reference: Olav Kallenberg,
  [*Probabilistic Symmetries and Invariance Principles*](https://link.springer.com/book/10.1007/0-387-28861-9)
  (Springer, 2005).

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 29 .lean files, 0 with sorries.*
