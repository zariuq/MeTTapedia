# π-Calculus

## What this is about

The **π-calculus** (Milner, Parrow & Walker 1992) is the textbook model of
*concurrency as message-passing*. Computation is processes running side by side
that synchronize by sending and receiving on named **channels** — and the twist
that makes it "mobile" is that the messages sent are themselves channel names. A
process can hand out a private name and thereby reconfigure who can talk to whom
*while the system runs*. That single idea ("names are data") is enough to encode
the λ-calculus, objects, and most concurrency patterns, which is why the
π-calculus is the lingua franca for reasoning about concurrent systems.

This directory formalizes one specific dialect: the **asynchronous, choice-free**
π-calculus (sends do not block; there is no `+` summation operator), following
the presentation Lybech uses in his rho-vs-pi encoding work (2022). On top of the
calculus itself it builds two things:

- **A verified π → ρ encoding.** The ρ-calculus (Meredith & Radestock 2005) is a
  *reflective* relative of the π-calculus in which names are quoted processes
  rather than atoms. Translating π into ρ is delicate — Lybech showed the original
  Meredith–Radestock encoding had two bugs — so the payoff of a machine-checked
  **forward simulation** (every π reduction is matched by the encoded ρ process)
  is high. This lane proves that simulation for the restriction-free fragment and
  assembles a weak-correspondence statement combining the forward and backward
  directions.
- **Open-map bisimulation bridges.** The same behavioural equivalence (weak
  barbed bisimilarity) is re-expressed categorically, as a bisimulation over the
  paths picked out by *open maps* — connecting the operational equivalence to the
  open-map / presheaf account of bisimulation.

A recurring engineering choice: the structural-congruence and reduction relations
are **`Type`-valued inductives** (not `Prop`), so that a derivation is a piece of
data the encoding lemmas can recurse over and extract from, rather than an opaque
proof.

Part of `../../../../../../papers/process-calculi.tex` (Section 3).

## Syntax

Six process constructors (`Syntax.lean`): `nil` (`0`), `par` (`P | Q`), `input`
(`x(y).P`), `output` (`x<z>`, asynchronous — no continuation), `nu` (`(νx)P`,
restriction), and `replicate` (`!x(y).P`, input-guarded replication). Names are
strings; the file also defines free/bound names and (capture-avoiding)
substitution and alpha-equivalence.

## Core Semantics

| File | Contents |
|------|----------|
| `Syntax.lean` | `Process` type, alpha-equivalence, free/bound names |
| `StructuralCongruence.lean` | SC relation (`Type`-valued): par-comm, par-assoc, scope extrusion |
| `Reduction.lean` | `comm` reduction rule, substitution lemmas |
| `MultiStep.lean` | `P =>* Q` reflexive-transitive closure |

## π → ρ Encoding (Lybech 2022)

Full encoding into the ρ-calculus via a name-server approach.

| File | Contents |
|------|----------|
| `RhoEncoding.lean` | Encoding function with Lybech-style name server |
| `ForwardSimulation.lean` | Forward simulation for the restriction-free fragment (`forward_comm_rf`, `forward_single_step_rf`, `forward_multi_step_rf`) |
| `EncodingMorphism.lean` | Encoding as a structured `LanguageMorphism` |
| `RhoEncodingCorrectness.lean` | Clean restriction-free forward-correctness surface |
| `NameServerLemmas.lean` | Name-server operational lemmas |
| `WeakBisim.lean` | Weak N-restricted barbed bisimilarity (`WeakRestrictedBisim`) |
| `WeakBisimDerived.lean` | Weak bisimilarity with derived reductions |
| `BackwardNormalization.lean` | Normalization helpers for the backward direction |
| `BackwardAdminReflection.lean` | `EncodedSC` predicate; admin-trace reflection (2,743 lines) |
| `RhoParTactic.lean` | Custom tactic for `rhoPar`/`rhoSubstitute` commutativity |

## Open-Map Bridges

| File | Contents |
|------|----------|
| `BranchingBisim.lean` | Branching bisimilarity via generalized open maps |
| `WeakBisimOpenMapBridge.lean` | Weak bisim ↔ generalized open-map path bisimulation |
| `OpenMapBridgeRegression.lean` | Regression checks for the bridge |

## Integration

| File | Contents |
|------|----------|
| `Main.lean` | Facade: re-exports the core + bridges; home of `calculus_weak_correspondence_full_encode` |
| `PiCalcInstance.lean` | π-calculus as an OSLF pipeline instance (single sort `Proc`, six constructors, COMM + ParCong) |

## Key Results

- **Forward simulation** for the restriction-free π → ρ encoding (Lybech 2022,
  Prop. 4): `forward_comm_rf` (single COMM step), lifted to
  `forward_single_step_rf` and `forward_multi_step_rf`.
- **Backward admin reflection** with a three-branch decomposition of
  administrative ν/seed/replicate traces (`BackwardAdminReflection.lean`).
- **`calculus_weak_correspondence_full_encode`** (`Main.lean`) — weak
  correspondence assembled from the forward and backward directions.
- **Weak bisim ↔ open-map path bisimulation** bridge
  (`WeakBisimOpenMapBridge.lean`).

## Formalization status

All 19 `.lean` files in this directory are **`sorry`-free**.

**Trusted base.** No source-level `axiom` declarations appear in this directory (a
source grep over `*.lean`, *not* a per-theorem `#print axioms` audit — a theorem
can still inherit a Mathlib axiom transitively). There is **no `native_decide`**
anywhere in this directory, so nothing here compile-evaluates in place of a
kernel check; nothing in this lane enlarges the trusted base.

Reproduce from this directory — note the `sorry`/`admit` regex is a *raw* scan
that also matches the phrase "sorry-free" and similar prose in comments, so the
per-file figure in the footer below (comment-stripped) is the authoritative one:

```bash
# sorry/admit occurrences (raw — also matches comment/string mentions):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## References

- Robin Milner, Joachim Parrow & David Walker, "A Calculus of Mobile Processes, [I](https://www.sciencedirect.com/science/article/pii/0890540192900084) / [II](https://www.sciencedirect.com/science/article/pii/0890540192900095)", *Information and Computation* 100(1):1–40, 41–77 (1992) — the original π-calculus.
- Stian Lybech, [*Encodability and Separation for a Reflective Higher-Order Calculus*](https://arxiv.org/abs/2209.02356), EXPRESS/SOS 2022 (EPTCS 368) — the corrected π → ρ encoding (fixing two errors in Meredith–Radestock) and the ρ-cannot-encode-π separation result; the source this lane follows for the encoding.
- L. Greg Meredith & Matthias Radestock, [*A Reflective Higher-Order Calculus*](https://www.sciencedirect.com/science/article/pii/S1571066105051893), *Electronic Notes in Theoretical Computer Science* 141(5):49–67 (2005), DOI [10.1016/j.entcs.2005.05.016](https://doi.org/10.1016/j.entcs.2005.05.016) — the ρ-calculus (the encoding target).

---
*Status (drafted 2026-06-22 by Claude Code, Opus 4.8): 19 .lean files, 0 with sorries.*
