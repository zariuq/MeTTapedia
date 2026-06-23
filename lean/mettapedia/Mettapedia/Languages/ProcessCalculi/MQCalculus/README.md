# MQ-Calculus

## What this is about

A **process calculus** describes concurrent systems as processes that talk to each
other; the basic event is two processes meeting on a channel and exchanging a
message (a "rendezvous", or COMM). The **MQ-calculus** (Stay & Meredith 2026)
takes that idea and makes the rendezvous *quantum*: when two processes
synchronize, the event behaves like a **quantum measurement**. Instead of one
deterministic continuation, a COMM produces a **binary outcome** (0 or 1), and
*which* outcome occurs is governed by the **Born rule** — the squared-amplitude
probabilities of quantum mechanics.

The key design move is to make that branching visible right in the syntax. A
receiver `MQIn n P Q` listens on wire `n` and carries **two** continuations:
`P` runs if the measurement yields `0`, `Q` if it yields `1`. Channels are
**wires**, addressed by **De Bruijn indices** (`MQNu` allocates a fresh wire at
index 0 and shifts every existing index up by one), so there are no name-capture
headaches — wire identity is positional. The upshot is a small, executable model
in which quantum non-determinism is a first-class operational phenomenon rather
than an annotation.

A deliberate separation runs through the formalization: the **branching structure**
is a plain structural inductive (which outcomes are reachable), while the
**probabilities** are a *separate* numeric field constrained to sum to one. This
keeps the theorem-level invariants clean and decouples "what can happen" from
"with what amplitude".

Part of `../../../../../../papers/process-calculi.tex` (Section 4).

## Key Idea

COMM is quantum measurement: a rendezvous event produces a binary outcome
governed by Born-rule probabilities. Each `MQIn` carries two continuations — one
for outcome zero, one for outcome one — making branching explicit in the syntax.

## Syntax

Six process constructors with De Bruijn-style wire indices:

```
Process ::= MQNil | MQPar P Q | MQNu P | MQGate spec P | MQOut n | MQIn n P Q
```

`MQIn n P Q` listens on wire `n`; `P` is the zero-outcome continuation, `Q` the
one-outcome continuation. `MQNu` introduces a fresh wire at index 0.

## Modules

| File | Contents |
|------|----------|
| `Syntax.lean` | Process grammar (`GateOp`, `GateSpec`, `Process`), De Bruijn wire indices |
| `StructuralCongruence.lean` | `SC` relation: par-comm, par-assoc, nu-nil, scope-extrusion |
| `Reduction.lean` | One-step `Reduces` and reflexive-transitive `MultiStep`; OSLF `HasPar`/`HasNil`/`HasNu`/`HasSC` instances |
| `CommRule.lean` | COMM with binary `Outcome` type; `comm_both_outcomes` witness |
| `Shift.lean` | Wire-index shifting with equational law proofs |
| `Denotational.lean` | Denotational semantics (Stay & Meredith 2026, Section 6.3) |
| `Backend.lean` | `MQSemanticsBackend` interface: gate application, wire allocation, Born-rule probabilities, post-measurement collapse |
| `Interoperability.lean` | `comm_nondeterminism_iff_mork_binary`: MQ COMM ↔ MORK binary-fold |
| `PaperMap.lean` | Theorem index from the MQ-calculus paper clauses to Lean names |
| `MQCalculus.lean` | Facade module, integration tests, canary theorems |

## Key Results

- **`comm_both_outcomes`** (`CommRule.lean`): constructive witness that both COMM
  outcomes are simultaneously derivable.
- **`collapseByOutcome_norm_eq_one_of_raw_pos`** (`Backend.lean`): post-collapse
  state normalization — the collapsed state vector has norm one (physical
  consistency).
- **`comm_nondeterminism_iff_mork_binary`** (`Interoperability.lean`): MQ's two
  `CommReduction` outcomes biject with MORK's two `FoldPicksSubResult` choices
  (`subResult0`/`subResult1`).
- MQ `Process` is wired into the OSLF common-infrastructure typeclasses
  `HasPar`, `HasNil`, `HasNu`, and `HasSC` (`Reduction.lean`).

## Backend Interface

The denotational semantics is parameterized by `MQSemanticsBackend` (`Backend.lean`),
a structure providing the fields `branchProb`, `applyGate`, `allocFresh`, and
`collapse`, together with the proof obligations `branchProb_nonneg` and
`branchProb_sum_one`. The `statevectorBackend` instantiation gives executable
semantics (state-vector amplitudes) while keeping the theorem-level invariants
clean. Born probabilities and branch relations are decoupled: the branch inductive
is structural; probabilities are a separate field subject to `branchProb_sum_one`.

## Formalization status

All 10 `.lean` files in this directory are **`sorry`-free**.

**Trusted base.** No source-level `axiom` declarations appear in this directory (a
source grep over `*.lean`, *not* a per-theorem `#print axioms` audit — a theorem
can still inherit a Mathlib axiom transitively). There is **no `native_decide`**
anywhere in this directory, so nothing here compile-evaluates in place of a kernel
check; nothing in this lane enlarges the trusted base.

Reproduce from this directory — note the `sorry` regex is a *raw* scan that also
matches prose such as the comment "all sorry-free" in `Shift.lean`, so the
comment-stripped figure in the footer below is the authoritative one:

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Mike Stay & L. Greg Meredith, *MQ-Calculus* (2026) — the quantum-rendezvous
  process calculus formalized here (Born-rule COMM, De Bruijn wires, gate
  application). Manuscript in preparation; tracked locally as `mq-calculus.pdf`.
  Author page: [Mike Stay](https://math.ucr.edu/~mike/).
- Simon J. Gay & Rajagopal Nagarajan, [*Communicating Quantum Processes*](https://eprints.gla.ac.uk/3475/1/gay23475.pdf), POPL 2005, DOI [10.1145/1040305.1040318](https://doi.org/10.1145/1040305.1040318) (also [arXiv:quant-ph/0409052](https://arxiv.org/abs/quant-ph/0409052)) — CQP, the qubit-passing quantum extension of the π-calculus; the closest prior quantum process calculus.

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 10 .lean files, 0 with sorries.*
