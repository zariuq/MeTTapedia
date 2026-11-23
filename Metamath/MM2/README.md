# Metamath on MM2

This directory separates a reusable Metamath verifier from its input data.
The verifier is ordinary MM2 executed directly by MORK. The native translator
prepares passive data from a `.mm` database. Lean supplies an offline semantic
reference and supporting proofs; it is not part of the runtime path.

```text
.mm bytes -- B: native translation --> data.mm2
                                      + A: fixed verifier.mm2
                                      -- MORK --> outcome
```

## Organization

| Directory | Responsibility |
| --- | --- |
| `verifier/` | Canonical MM2 source fragments and their assembly manifest |
| `frontend/` | Native parsing, include expansion, declaration preparation, and data encoding |
| `tools/` | Assembly, direct execution, and qualification |
| `tests/` | Positive and negative regression controls |

The initial fragments retain the established load order: runtime support,
dispatch, declarations, compressed support, and admission continuations.
These are full top-level MM2 forms, not a new macro language. Assembly only
concatenates them and validates the manifest. Editing a fragment requires
updating its manifest checks and rerunning the corresponding gates.

## Runtime

Build B with the pinned native parser dependency:

```sh
make -C Metamath/MM2/frontend
```

An existing CeTTa checkout can supply the dependency objects through
`CETTA_SOURCE`; it is cloned at the locked revision into the ignored build
directory. It is not modified. The resulting `mm2-translate` executable has
no runtime dependency on the source checkout or on Lean.

Translate data and assemble A separately:

```sh
Metamath/MM2/frontend/build/mm2-translate input.mm --output data.mm2 --profile zar
python3 Metamath/MM2/tools/assemble.py --output verifier.mm2
```

Run the composition directly:

```sh
python3 Metamath/MM2/tools/run.py --mork "$MORK" \
  --translator Metamath/MM2/frontend/build/mm2-translate \
  --input input.mm --work-dir Metamath/MM2/.build/run
```

The initial profile is Zar/book. Other mm-lean4 modes are not implied by the
mode support of the offline Lean scanner. Includes resolve relative to their
parent file, with canonical file identity for repeat and cycle handling.

## The A and B boundary

B retains statement chronology, original proof labels, and compressed
header/body words. It also prepares mandatory frames, occurrence indexes,
disjoint-variable pair plans, and proof-gated declaration deltas. These are
structural computations, not proof verification. In particular, B does not
resolve a normal proof label, execute a proof stack, decode compressed actions,
or substitute a dummy successful proof result.

An assertion preview in B is not an admitted runtime assertion. A checks
proofs in source order and owns theorem admission. Input supplies no executable
rules, executable continuations, or pre-approved theorem verdicts. Explicit
occurrence identities preserve order and repeated values in MORK's set store.
The structural guard on passive data is `validate_passive_data` in
[tools/protocol.py](tools/protocol.py).

The native translator is part of the implementation being qualified. The
public runner's data guard checks syntax, ownership, and prohibited carriers;
it does not recompute all preparation from the source. A pretranslated
`--data` artifact must therefore come from B or an independently checked
encoder. Schema validity alone is not a semantic admission theorem.

## A small execution

`examples/simple.mm` declares the floating hypothesis `wph` and the axiom `ax`.
The proof `wph ax` pushes `wff ph`, then applies `ax`: its floating hypothesis
consumes that stack entry and the substitution produces `|- ph`. The final
stack is a singleton with the claimed formula; only then may A publish `ok`.

```sh
python3 Metamath/MM2/tools/run.py --mork "$MORK" \
  --translator Metamath/MM2/frontend/build/mm2-translate \
  --input Metamath/MM2/examples/simple.mm --work-dir Metamath/MM2/.build/example
```

`examples/undefined-label.mm` has the same declarations but cites `missing`.
B preserves that label without deciding its proof meaning; A must reject it.
This separates a successfully translated input from a successfully checked
proof.

## Implementation and theory map

| Boundary | Native implementation | Offline semantic reference |
| --- | --- | --- |
| Source occurrences and include chronology | `frontend/reader.c` | `SourceGSLTRawSourceComposition` |
| Active declaration state and mandatory frames | `frontend/model.c` | `SourceGSLTState`, `MM2SourceAssertionPlan` |
| Located passive rows and proof-gated deltas | `frontend/emit_source.c`, `frontend/emit.c` | `MM2SourceEventTransformation`, `MM2SourceActionPlan` |
| Normal proof stack, substitutions, essential hypotheses, DV checks | A's normal dispatch inventory | `MM2NormalProofCorrespondence` |
| Compressed headers, indices, save/recall, stack handoff | A's compressed dispatch inventory | `MM2CompressedProofData`, `MM2CompressedProofExecution` |
| Sequential publication and final outcomes | A's source/admission continuations; `tools/protocol.py` | `MM2TwoTransformProgram`, `MM2TwoTransformLineageClosure` |

This map identifies related theory, not an unproved equality of the native
implementation with every reference module. In particular, the authored
source fold's permanent variable-type history is stricter than released Zar:
the native model follows the released active-frame rule for floating types.

## Qualification and evidence

Run the parser, manifest, passive-boundary, model, encoding, and outcome tests:

```sh
make -C Metamath/MM2 test
```

Run the supplied specification suite and released mm-lean4 oracle explicitly:

```sh
python3 Metamath/MM2/tools/qualify.py --suite "$METAMATH_TEST" \
  --oracle "$MM_LEAN4" --mork "$MORK" \
  --translator Metamath/MM2/frontend/build/mm2-translate \
  --work-dir Metamath/MM2/.build/qualification
```

The suite is [zariuq/metamath-test](https://github.com/zariuq/metamath-test),
branch `unit-tests`. Reports distinguish skipped and failed cases from passed
ones. A time limit or exhausted step budget is an execution failure, never a
semantic rejection. Genuine incomplete proofs are distinct from proved
theorem admission.

Each qualification freezes its verifier and native executables before the
first case. Separate case directories and exact source/proof observations
prevent prior results or concurrent source edits from supplying evidence.

For incremental corpus tests, a lightweight preflight sizes the current
successor tables without constructing them:

```sh
python3 Metamath/MM2/tools/measure_source.py input.mm
```

It assumes structurally valid Zar source and reports encoding bounds, not
proof correctness or MORK memory use. It does not expand includes or execute
the native mandatory-frame model; those limitations appear in its report.
Large successor-table expansion is an encoding cost, not evidence that MM2
is intrinsically unable to verify the database.

`tools/check_reference.py` is an optional offline gate comparing native B
against the Lean data encoder. It is separate from the production path.
Initial data-row order can differ: the gate compares exact parsed atom sets,
including every occurrence index and source span.

The supporting theory remains in
`lean/mettapedia/Mettapedia/Languages/Metamath/`. Useful entry points are
`MM2TwoTransformProgram`, `MM2SourceActionPlan`, `MM2NormalProofCorrespondence`,
`MM2CompressedProofData`, and `MM2TwoTransformLineageClosure`.
Their entry-boundary and local correspondence theorems do not establish a
whole-run verdict theorem for this native implementation. Runtime qualification
and finite reference comparisons are tests, not substitutes for that theorem.

## Reading the modular execution theory

The Lean execution material separates reusable results from concrete examples:

| Module | What to read it for |
| --- | --- |
| `MM2Transformation` | The admitted source scope, emitted normal-verifier slice, and rule-inventory invariants |
| `SourceInferenceProjectionValidation` | The source projection gates and validity of the generated inference language |
| `MM2AssembledNormalExecutionCore` | Bounded acceptance, compositional reachability, invariant-to-adequacy construction, and transport to OSLF native types |
| `MM2TransformationCanary` | Small admitted source scopes, positive and negative inputs, and ordinary MM2 renderers |
| `MM2AssembledNormalExecution` | Seven kernel-checked example runs, including missing-authorization and premature-admission controls |

Import `Mettapedia.Languages.Metamath.MM2AssembledNormalExecutionCore` to use
the generic execution results without checking the example runs. The declarations
remain in the `Mettapedia.Languages.Metamath.MM2AssembledNormalExecution`
namespace. Importing the example module still exposes both theory and examples.

The Metamath umbrella exposes the reusable theory, not the concrete fixtures.
From `lean/mettapedia`, the examples have an explicit, non-default audit target:

```sh
lake build MetamathProofRegression
```

These examples prove properties of finite runs in the Lean scheduler model.
They are neither the native MORK qualification gate nor a whole-verifier
correctness theorem. Future work can compose the generic reachability and
adequacy results while keeping that model-to-runtime boundary explicit.
