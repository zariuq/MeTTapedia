# GSLT — Graph-Structured Lambda Theories (Lean 4)

## The idea

A programming language, at heart, is two things: a set of *terms* (programs) and a
notion of when two terms *mean the same thing*. In the λ-calculus, for instance,
`(λx. x) y` and `y` compute to the same value, so any sensible theory should equate
them. A **lambda theory** is exactly such an "equality theory": a congruence on
terms that extends β-equality. Different theories make different choices about the
hard cases — most famously, *what to do with non-terminating programs* like
`Ω = (λx.xx)(λx.xx)`. A theory is **sensible** if it lumps all such "meaningless"
terms together, and the beautiful classical result (Bucciarelli–Salibra) is that
there is a *unique maximal sensible* theory, captured by **Böhm trees**: the
possibly-infinite tree of "what a program eventually does."

A **Graph-Structured Lambda Theory (GSLT)** generalizes this from λ-calculus to *any*
computational system. It is a triple `S = (T, E, R)`:

- `T` — a grammar of terms (could be λ-terms, π-calculus processes, ρ-calculus,
  a tiny ML, a machine-state language…),
- `E` — equations saying which terms are structurally equal,
- `R` — small-step **rewrite rules** saying how terms evolve.

That single shape is enough to do a surprising amount of work. Because every system
is "just" terms-with-equations-and-rewrites, you get, *uniformly*:

- a **labeled transition system** and a notion of **bisimilarity** ("these two terms
  are indistinguishable to any observer"), with **Hennessy–Milner logic** to describe
  what an observer can see;
- a **causal structure** — traces record history, and reversing every step gives a
  *reversible envelope* `S†`, the computational analogue of CPT symmetry, where the
  arrow of time lives entirely in the boundary condition (the empty trace);
- a **categorical / topos semantics** — lambda theories become objects of a category
  with cartesian-closed structure and a subobject classifier, which is the direct
  infrastructure for *Native Type Theory*;
- a **path-integral / quantum layer** — assigning complex amplitudes to rewrite paths
  and summing over them, in the style of physics, with a resource-accounting
  conservation law.

This unification follows two lines of work: Bucciarelli & Salibra, *Graph Lambda
Theories* (2008) for the graph-model / Böhm-tree core, and G. Meredith,
*Computation, Causality, and Consciousness* (2026) for the causal, modal, and
path-integral superstructure. **Within Mettapedia, GSLT is also the formal contract
that the OSLF type-synthesis framework consumes** (see "OSLF interface" below): you
describe a language as a GSLT, and OSLF builds its modal/Galois type theory for you.

## Layout

| Subdir | Files | What it formalizes |
|--------|-------|--------------------|
| `Core/` | 4 | the abstract GSLT triple `(T,E,R)`, morphisms, rewrite paths, bisimilarity (`GSLT.lean`); lambda-theories as categorical objects with CCC + finite limits + a subobject fibration (`LambdaTheoryCategory.lean`); change-of-base / quantifier adjunctions (`ChangeOfBase.lean`); webs, coding functions, graph models (`Web.lean`) |
| `GraphTheory/` | 6 | graph lambda theories, interpretations, sensible/semisensible theories (`Basic.lean`); **Böhm trees** and the Böhm theory `B` (`BohmTree.lean`); finite approximants and weak products |
| `Causality/` | 2 | traces and the **reversible envelope** `S†` with embedding/projection (`Trace.lean`); closed vs open **synchronization trees** and causal partial orders (`SyncTree.lean`) |
| `Logic/` | 3 | context-decorated **Hennessy–Milner logic** and its satisfaction relation; minimal-context machinery |
| `Dynamics/` | 3 | weight/cost annotations and finite-support **path integrals** — amplitude-weighted GSLTs and transition amplitudes (`PathIntegral.lean`) |
| `Synthesis/` | 1 | Construction 10.1 — the **main conservation kernel**: reversible debit/credit ledger invariant under quantum-resource steps (`MainConservation.lean`) |
| `Topos/` | 3 | subobject classifier, the **predicate fibration** `πΩ` over presheaf categories, Beck–Chevalley |
| `Meredith/` | 11 | the interactive/cost/bisimulation bridges and modal (`Diamond`, `RewriteModality`) layer, with ρ-calculus examples |
| `Life/` | 2 | an assembly-theory experiment over the GSLT substrate |

## OSLF interface (how the rest of Mettapedia uses GSLT)

GSLT supplies the *spec* that OSLF turns into an executable modal type theory. The
operational front-end is `LanguageDef` (in the OSLF MeTTaIL modules): you declare
**sorts** (with one designated *process* sort), **constructor terms** for syntax and
state, **equations** for structural equality/normalization, **small-step rewrite
rules**, and any **premise** constraints (freshness, congruence, `relationQuery`).
A `RelationEnv` is optional — needed only if you use `relationQuery` premises.

From a `LanguageDef` you get the type-synthesis entry points
`langRewriteSystem`, `langDiamond`, `langBox`, `langGalois`, and `langOSLF`
(each with a `…Using` variant that threads an explicit `RelationEnv`):

```lean
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.MeTTaIL.Engine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Engine

def myLang : LanguageDef := { /- sorts, terms, equations, rewrites, premises -/ }
def myRelEnv : RelationEnv := RelationEnv.empty

def myOSLF    := langOSLF myLang "Proc"
def myDiamond := langDiamondUsing myRelEnv myLang
def myBox     := langBoxUsing myRelEnv myLang
```

Any language that can be written as small-step rewrites over structured states fits:
functional languages via term-reduction rules, imperative languages as rewrites over
machine states, concurrent languages as rewrites over process/message networks.
Worked examples to copy: `OSLF/Framework/TinyMLInstance.lean`,
`MeTTaMinimalInstance.lean`, `MeTTaFullInstance.lean`,
`OSLF/MeTTaIL/DeclReducesWithPremises.lean`,
`OSLF/Tools/ExportTinyMLSmokeRoundTrip.lean`.

`LanguageDef` is the *executable* ingestion layer; the `Topos/` modules give the
matching **categorical semantics**, and the presheaf/predicate-fibration layer is the
infrastructure used by the Native Type Theory formalization. Paper-parity and strict
claim counts are tracked in `OSLF/Framework/NTTClaimTracker.lean`,
`PaperClaimTracker.lean`, and `FULLStatus.lean` (those trackers are authoritative —
prefer them over prose here for exact status).

## Formalization status

GSLT mixes settled classical theory with active research, so the proof state is
mixed and honest about it:

- The abstract core, causal/trace layer, HML logic, topos/predicate-fibration layer,
  and the conservation kernel are largely complete. `Synthesis/MainConservation.lean`
  deliberately makes its global hypotheses (probability normalization, the CPT
  automorphism) **explicit interfaces** rather than pretending they are already
  earned — the resource part of Theorem 10.1 is proved; the probability/CPT parts are
  stated as the assumptions they currently require.
- The **graph-theory lane carries the open work.** Five files still contain `sorry`s
  (see the footer): the Böhm-tree development (`BohmTree.lean`) and graph-model
  basics (`Basic.lean`, `Approximants.lean`, `WeakProduct.lean`, `Core/Web.lean`).
  These are genuine proof gaps in the classical Bucciarelli–Salibra results, not
  hidden axioms.

There are no source-level `axiom` declarations in this directory (a source grep, *not* a
per-theorem `#print axioms` audit, so a theorem can still inherit a standard Mathlib axiom
transitively), and nothing here uses `native_decide`.

Reproduce from this directory — the `sorry`/`admit` regex is a *raw* scan that also matches
prose in comments/strings, so the footer's per-file figures are the authoritative
comment-stripped counts:

```bash
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .   # prints nothing
rg -n --glob '*.lean' 'native_decide' .                 # prints nothing
```

## References

- Antonio Bucciarelli & Antonino Salibra, [*Graph lambda theories*](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/graph-lambda-theories/6AA6D923589379EA6B3EC57C91FEEEC0), Mathematical Structures in Computer Science 18(5):975–1004 (2008) — the graph-model / Böhm-tree core ([open-access HAL copy](https://hal.science/hal-00149556)).
- Antonio Bucciarelli & Antonino Salibra, [*The Minimal Graph Model of Lambda Calculus*](https://doi.org/10.1007/978-3-540-45138-9_24), MFCS 2003 — minimal/maximal sensible graph theories.
- Henk Barendregt, [*The Lambda Calculus: Its Syntax and Semantics*](https://www.elsevier.com/books/the-lambda-calculus/barendregt/978-0-444-87508-2) (North-Holland, rev. ed. 1984) — Böhm trees and sensible λ-theories.
- L. G. Meredith (2026). *Computation, Causality, and Consciousness* — the causal, modal, and path-integral superstructure (manuscript; no public URL located).
- Christian Williams & Michael Stay, [*Native Type Theory*](https://arxiv.org/abs/2102.04672), arXiv:2102.04672 — the categorical/topos infrastructure GSLT feeds into OSLF.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 35 .lean files, 5 with sorries.*
- `Core/Web.lean` — 3 sorries
- `GraphTheory/Approximants.lean` — 2 sorries
- `GraphTheory/Basic.lean` — 3 sorries
- `GraphTheory/BohmTree.lean` — 8 sorries
- `GraphTheory/WeakProduct.lean` — 5 sorries
