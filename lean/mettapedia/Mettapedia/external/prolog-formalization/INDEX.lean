/-!
# Prolog Formalization Reference Collection

Materials gathered for formalizing a clean Prolog fragment (compatible with
SWI-Prolog) in Lean 4.  Organized to support the two-layer architecture from
the ChatGPT deep-research document:

  (A) proof-relevant specification layer (unification, SLD steps, model theory)
  (B) executable interpreter layer with refinement theorems

Source roadmap:
  `~/claude/literature/AI Deep Research/
    Do deep research on formalizing a clean Prolog fragment compatible with SWI-Prolog in Lean 4.pdf`

Existing Datalog formalization (pattern to follow):
  `Mettapedia/Logic/Datalog/` — Core, Substitution, Semantics, Evaluation, Provenance, bridges

## Papers (24 gathered, 2 ungathered)

### foundations/ (8 papers)
- van Emden & Kowalski 1976 — Semantics of predicate logic as a programming language (T_P operator, fixpoints)
- Kowalski & Kuehner 1971 — Linear resolution with selection function (SL-resolution origin)
- Apt & van Emden 1982 — Contributions to theory of logic programming (SLD completeness)
- Tarski 1955 — Lattice-theoretical fixpoint theorem (mathematical foundation for T_P)
- Robinson 1965 — Machine-oriented logic and the resolution principle (unification origin)
- Kowalski 1974 — Predicate logic as programming language (definite clauses)
- Kowalski (history) — History of logic programming
- Lloyd 1987 — Foundations of logic programming (canonical textbook, 2nd ed)

### unification/ (4 papers)
- Martelli & Montanari 1982 — Efficient unification algorithm (equation-system style)
- McBride 2003 — First-order unification by structural recursion (dependent types, no termination proof needed)
- Bove & Capretta 2005 — Modelling general recursion in type theory (Bove-Capretta method)
- Paulson 1985 — Verifying the unification algorithm in LCF

### SLD-resolution/ (2 papers)
- Kriener, King & Blazy 2013 — Proofs you can believe in: Prolog in Coq (full SLD-resolution formalization)
- Gallier — SLD resolution notes (lecture notes, clear exposition)

### cut-and-NAF/ (3 papers)
- Clark 1978 — Negation as failure (CWA, completion semantics)
- de Bruin & de Vink 1989 — Continuation semantics for Prolog with cut
- Rozplokhas et al. 2020 — Certified semantics for relational programming (miniKanren/SLD with cut, Coq)

### verified-implementations/ (4 papers)
- Kokke & Swierstra 2015 — Auto in Agda: Prolog-style resolution (proof search as program)
- Tantow et al. 2025 — Verifying Datalog reasoning in Lean (CertifyingDatalog paper)
- Ramos et al. 2025 — Metatheory: Lean 4 rewriting framework
- Schlichtkrull 2026 — Stratified Datalog program analysis in Isabelle

### standards-and-manuals/ (3 papers)
- Borger & Rosenzweig 1995 — Mathematical definition of full Prolog (ASM-based)
- Stroder et al. 2011 — Prolog semantics report (linear, local)
- ISO/IEC 13211-1:1995 — Prolog standard (preview)

## Ungathered Papers

- **Kunen 1987** — "Negation in Logic Programming", J. Logic Programming 4:289-308
  Behind ScienceDirect paywall. URL: https://doi.org/10.1016/0743-1066(87)90007-0

- **Jaume 1999** — "A formalisation of the SLD resolution schema in Coq"
  Behind Springer paywall. URL: https://link.springer.com/chapter/10.1007/3-540-48167-2_36

## Repos (10 gathered)

### Lean 4
- `CertifyingDatalog/` — knowsys/CertifyingDatalog. Verified Datalog checker in Lean 4.
  Directly relevant as existing infrastructure pattern.

### Coq
- `Coq-unif/` — mattam82/Coq-unif. First-order unification formalized in Coq (ssreflect).
  Key reference for unification layer.
- `unification-Coq/` — rodrigogribeiro/unification. Type unification in Coq with
  termination, soundness, completeness. Clean textbook-style formalization.
- `certified-semantics-miniKanren-SLD/` — dboulytchev/miniKanren-coq.
  Certified miniKanren/SLD semantics with cut in Coq. Extracts Haskell interpreters.
- `coalgebraic-logic-programming-Coq/` — coalp/Coq. Coalgebraic logic programming in Coq.

### Agda
- `AutoInAgda/` — wenkokke/AutoInAgda. Prolog-style proof search in Agda.
  Direct implementation of resolution-based search.
- `FirstOrderUnificationInAgda-Agda/` — wenkokke/FirstOrderUnificationInAgda.
  McBride's structural-recursion unification in Agda. Best candidate for porting to Lean 4.
- `mgu-agda/` — gergoerdi/mgu-agda. Another Agda MGU implementation (McBride style).
- `miller-Agda/` — Saizan/miller. Miller/pattern unification in Agda.

### Prolog
- `swi-prolog-bench/` — SWI-Prolog van Roy benchmark set.
  Test programs for validating interpreter behavior.

## Notable repos NOT gathered (available online, not cloned)

- `IsaFoL/IsaFoL` — Isabelle Formalization of Logic (resolution calculus, unification)
- `logic-tools/unification` — Isabelle first-order unification
- `logic-tools/simpro` — Isabelle verified FOL prover
- `FormalizedFormalLogic/Foundation` — Lean 4 formal logic (FOL, modal, no LP content)
- `LPCIC/elpi` — Embeddable Lambda Prolog Interpreter (OCaml, used in Coq-ELPI)
- `Orange-OpenSource/octant-proof` — Certified Datalog optimizations (Coq/MathComp)
- `rocq-community/semantics` — Coq semantics survey (operational, denotational, axiomatic)

## Key finding

**No existing Lean 4 project formalizes Prolog semantics, SLD resolution, or a
Prolog interpreter.** This formalization would be genuinely novel.

## Formalization Architecture (from PDF roadmap)

Target Lean 4 module: `Mettapedia/Logic/Prolog/`

Planned files (following Datalog pattern):
- `Core.lean` — Signature, Term, Atom, Clause, Program, Goal
- `Substitution.lean` — Subst, apply, compose, ground, idempotent
- `Unification.lean` — UnifEq, unify, soundness, MGU, occurs-check
- `SLDResolution.lean` — SLDStep, SLDDerivation, refutation
- `Semantics.lean` — T_P, Herbrand model, least model (lfp)
- `Soundness.lean` — SLD refutation → correct answer in least model
- `Completeness.lean` — correct answer → computed answer (lifting lemma)
- `Interpreter.lean` — executable DFS search, refinement to SLD spec
- Optional extensions:
  - `Cut.lean` — cut as choice-point pruning
  - `NAF.lean` — negation as failure via `\+/1`

Key SWI-Prolog compatibility decisions:
- occurs-check OFF by default (match SWI), proved sound WITH occurs-check
- `unify_with_occurs_check/2` as the verified path
- left-to-right goal selection (Prolog standard)
- depth-first search (matching SWI's default strategy)
-/

-- This file is a manifest only; no Lean definitions.
