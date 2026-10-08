# PeTTa Evaluation Layer

Upstream: https://github.com/trueagi-io/PeTTa

## What this is about

MeTTa, the meta-language of OpenCog Hyperon, runs programs by
*pattern-matching rewriting* over a space of atoms. **PeTTa** ("Prolog-based
MeTTa") is one way to actually execute that: it compiles each MeTTa expression
into Prolog-style goals and resolves them against a logic-programming (LP)
kernel — so MeTTa's pattern matching becomes Prolog unification, and MeTTa's
nondeterministic results become the answer set of an LP query. If you know
Prolog, the mental picture is "MeTTa equations compile to clauses; evaluating an
expression is running a goal."

This directory contains several formalized fragments and execution profiles.
The pattern-level core has pure, stateful and operational relations with named
agreement theorems. A `PeTTaEval.ruleApp` derivation selects one rewrite and
returns its instantiated right-hand side; it does not recursively execute that
body or collect every matching equation. Its LP soundness theorem connects rule application to the
least Herbrand model of the compiled clauses. These results do not establish
correctness of every PeTTa feature or of CeTTa's C implementation.

The executable fragment in `SpaceSemantics`, `Effects`, `StdLib`,
`DeclarativeSpec` and `Eval`
gives meaning to retained program text without first losing
the distinction between a symbol, a nullary expression and a grounded value.
It covers saturated calls, ordered cases with constructor/list-view
patterns, containers, state cells and stream operations used by the MM0
service, together with literal `superpose`, `empty` and quotation. Independent
syntax-directed rules in `DeclarativeSpec` define its transitions and finite
whole-program observations. `Eval` proves that the executable machine computes
exactly those observations, including ordered answers, the store and I/O. Computations inside patterns are outside this selector's contract:
native PeTTa computes such patterns, so the restriction must be checked on the
program being proved. `RaiseFree` separately accounts for callable occurrences
in patterns; absence of raising is not absence of computation. The typed and
open-program profiles have their own carriers and contracts.

The routine umbrella is `Mettapedia.Languages.MeTTa.PeTTa`
([PeTTa.lean](../PeTTa.lean)). The executable fragment now belongs to the
existing semantic layers. Import `Eval` when proving execution of a retained
program and `ProgramQuotation` when retaining its pinned text.

## Build

```bash
# from the repository root
lake build Mettapedia.Languages.MeTTa.PeTTa
```

## Modules

### Pattern-level presentations

The selected-rewrite view has three related presentations:

1. **Pure declarative core**: `PeTTaEval` / `PureDecl`.
2. **Stateful declarative core**: `PeTTaCmd` / `CoreDecl`.
3. **Operational minimal-step layer**: `MeTTaStep`.

Presentation and fragment theorem anchors:
- `pureDecl_iff_pettaEval` ([PatternRewrite/DeclarativeSpec.lean](PatternRewrite/DeclarativeSpec.lean))
- `coreDecl_iff_pettaCmd` ([PatternRewrite/DeclarativeSpec.lean](PatternRewrite/DeclarativeSpec.lean))
- `evalStep_implies_pettaEval` ([MinimalInstructions.lean](MinimalInstructions.lean))
- `translatePredicate_query_to_pettaEval_match` ([PatternRewrite/DeclarativeSpec.lean](PatternRewrite/DeclarativeSpec.lean))
- `catch_fallback_to_pettaEval` ([PatternRewrite/DeclarativeSpec.lean](PatternRewrite/DeclarativeSpec.lean))

The pure and stateful equivalences translate between inductive presentations
with corresponding constructors. They establish presentation agreement, rather
than adequacy of an independently specified executable evaluator.
`evalStep_implies_pettaEval` takes the components of a selected rewrite;
`catch_fallback_to_pettaEval` constructs a control derivation using an already
supplied fallback derivation.

### Core evaluation

| Module | What it does |
|--------|-------------|
| [DeclarativeSpec.lean](DeclarativeSpec.lean) | Independent operational rules and finite whole-program judgments over Atom |
| [Eval.lean](Eval.lean) | Executable Atom evaluation, adequacy, fuel and composition laws |
| [MeTTaEval.lean](MeTTaEval.lean) | Selected-rewrite relation with bindings, types, and error propagation |
| [Answers.lean](Answers.lean) | Ordered Atom answer lists, retaining duplicate occurrences |
| [PatternRewrite/Answers.lean](PatternRewrite/Answers.lean) | `RewriteResults`, the Pattern list algebra of the selected-rewrite view |
| [SpaceSemantics.lean](SpaceSemantics.lean) | Source reading, ordered equations, the literal-`Atom` argument policy, constructor matching and ordered queries over `OSLFCore.Atom` |
| [Effects.lean](Effects.lean) | Atom storage, private spaces, cells and primitive outcomes |
| [PatternRewrite/Space.lean](PatternRewrite/Space.lean) | The selected-rewrite view over `Pattern`: `PeTTaSpace`, `spaceMatch`, `PeTTaEval` |
| [PatternRewrite/Commands.lean](PatternRewrite/Commands.lean) | The `&self` command view over `Pattern`: `EvalState`, `PeTTaCmd`, and the `Pattern` specialization of the named-space store |
| [PatternRewrite/OperationalGSLT.lean](PatternRewrite/OperationalGSLT.lean) | The GSLT and OSLF built from the `CoreDecl` request relation over `Pattern` |
| [UpstreamAgreement.lean](UpstreamAgreement.lean) | Kernel-checked runs of the machine that reproduce upstream SWI-PeTTa answers on small programs, and the upstream answers for forms the machine does not yet cover |

### Closed source execution

| Module | What it does |
|--------|-------------|
| [NamedSpaces.lean](NamedSpaces.lean) | Shared allocation, read, update and frame laws for private spaces and state cells |
| [SpaceSemantics.lean](SpaceSemantics.lean) | Shared OSLFCore.Atom carrier, ordered equations, grounded pattern selection and ordered queries |
| [Effects.lean](Effects.lean) | Shared storage specialization and faults separate from completed answers |
| [StdLib.lean](StdLib.lean) | Mathematical integer operations and one ground primitive table |
| [DeclarativeSpec.lean](DeclarativeSpec.lean) | Syntax-directed transition rules and finite completed/fault judgments |
| [Eval.lean](Eval.lean) | Control-and-continuation machine, judgment adequacy, finite path correspondence, fuel and caller-frame composition |
| [OperationalGSLT.lean](OperationalGSLT.lean) | OSLF generated from the judgment, executable correspondence and preservation of printed history |
| [ProgramQuotation.lean](ProgramQuotation.lean) | Retained source text, digest and constructor data for program proofs |
| [Main.lean](Main.lean) | `pettaRun`, the generic executable for the closed fragment |

The machine's definitions and execution laws belong to the layers above.
`Eval.completed_run_iff_derivation` and `Eval.fault_run_iff_derivation`
prove adequacy against the independent `DeclarativeSpec.Runs` judgment.
`Eval.completed_derivation_iff_path` relates a completed judgment to the single
GSLT generated from its transition rules. These results do not establish
agreement with the selected Pattern relations; that fragment simulation is a
separate obligation. Loading a program adds every non-request form,
equations included, to `&self` in source order (`Effects.loaded`,
`SpaceSemantics.loadedAtoms_collect`), so `match` and `get-atoms` see them as
upstream does. The equations that apply are fixed at load time: adding or
removing an equation atom at run time does not change them, whereas upstream
redefines the function. Open caller-variable binding, partial application,
`once`, `progn` and run-time equation redefinition remain outside this
executable profile.

`Effects.loaded_finite_cells`, `DeclarativeSpec.completed_finite_cells` and
`OperationalGSLT.finite_cells_preserved` derive finite support of state cells
from loading, primitive operations and the actual transition graph. The
corresponding empty-tail laws preserve the values of every unallocated space
slot. `NamedSpaces.Store.reconstruct_exact` reconstructs the existing store
from its core, ordered allocated-space prefix and a supplied cell support;
`DeclarativeSpec.completed_from_loaded_finite_representation` derives the
existence of such a representation after completed execution from a loaded
program. A present cell cannot be represented by an empty support.

[`OSLFCore.Bridge.GroundData`](../OSLFCore/Bridge.lean) provides an injective
Atom-to-Pattern data codec, with decoding and canonical-image theorems. It
preserves grounded values, symbol versus nullary expression, source-variable
spellings, expression order and duplicate occurrences. Its `dataLanguage`
declares the corresponding LangDef carrier with ordered vector payloads;
`encode_has_type` and `encode_checked` prove that every encoded Atom is sorted
and accepted by the carrier checker. Malformed tags and noncanonical integer
spellings are rejected by decoding. Structural sorting can still admit a
noncanonical spelling, so it does not replace the decoder's image check.
[`ConfigurationEncoding`](ConfigurationEncoding.lean) encodes entire existing
configurations, including recursive controls, continuation frames, substitutions,
ordered case rows, allocated spaces, finitely supported cells and I/O. Its decoder
reconstructs the existing configuration exactly under the derived store support
and empty-tail premises. `cellSupportAfter` maintains support constructively at
each actual transition; loaded paths retain exact, ground, carrier-checked
representations. Omitting a present cell's support loses that cell and is
explicitly rejected by the round-trip claim. Faults, empty answers, `False`,
symbols and nullary expressions stay distinct. The full Pattern LanguageDef
transition simulation remains a separate obligation.

The retained MM0 program connects to this same judgment in
[`MM0.MeTTa.Proof`](../../MM0/MeTTa/Kernel/Proof.lean):
`certificate_accepted_iff_petta_judgment` and
`certificate_accepted_iff_gslt_path` relate acceptance of a translated
`formMM0` certificate to the actual PeTTa proof call.
`certificate_accepted_iff_petta_accepts` and
`certificate_accepted_iff_check_gslt_path` give the corresponding results for
the Boolean `mm0:check-proof` entry point. Their premises retain
the concrete term, definition and theorem tables and the call's `Ready`
invariant. Declaration admission and establishment of those premises by the
session driver are proved separately in the same MM0 source layer. Its files
are grouped by layer of the program under `MM0/MeTTa/`: `Data`, `Kernel`,
`Formation`, `Admission`, `Session` and `Formats`; the names below are
namespaces, which do not carry the folder:

- `MM0.MeTTa.SessionInitialization` derives six fresh spaces, three owned
  cells and empty native tables from the actual `mm0:start` equation.
- `MM0.MeTTa.AdmissionChecks`, `AdmissionStep` and `SpecificationStep`
  check formation, supplied proofs, publication and ordered public/local
  specification consumption in the preceding theory.
- `MM0.MeTTa.SessionDriver` derives cache readiness from each actual submit
  reset and preserves table ownership between declarations. Its complete
  resolved ordinary protocol accepts exactly when the independent
  specification verifier does; accepted execution derives a checked history,
  the exact specification axiom basis and the specified source extension.
- `MM0.MeTTa.SharedService` and `SharedSessionDriver` retain every submitted
  saved initializer, optional expected conclusion and root. Logical cut is
  used only after that fixed sharing check to obtain ordinary history evidence.
- `MM0.MeTTa.SessionProtocol` composes ordinary and shared submissions with
  startup and finish. Accepted receipts preserve the original command payloads,
  consume the specification and justify shared proofs in their preceding history.
- `MM0.MeTTa.FrontendBindings` proves finite child-before-parent constructor
  plans materialize captured values through the actual `let*` wrappers. Equal
  captures enter the retained callees, preserving their whole state and answers.
- `MM0.MeTTa.StreamProtocol` composes those wrappers with the pinned
  `mm0:stream` initializer. It consumes the parsed requests in order, prints
  exactly one response per submission plus startup and finish, and returns
  `MM0:End`. All-true printed responses earn specification consumption, its
  exact axiom basis and the specified source extension. EOF alone supplies
  no acceptance evidence. The results are paths and derivations in this same
  operational GSLT and whole-program judgment.

The four-field cache reset
in `MM0.MeTTa.InferenceCache.reset_scope_returns` establishes an empty coherent
scope for a subsequent signature without assuming coherence of the old rows.
Between submissions, the driver retains the physical row shape rather than
asserting that values checked against an earlier theory remain coherent.
These theorems concern resolved inputs, certified finite constructor plans and
parsed-request execution in the actual PeTTa operational GSLT. The readers
that turn `.mm0`, `.mmu` and `.mmb` bytes into those requests are MeTTa
programs of the same library (`textual.metta`, `mmu.metta`, `mmb.metta`).
`MM0/MeTTa/Formats` holds what is proved about them; the rest of their
behaviour, raw line reading and native rendering remain explicit interfaces. A whole-configuration MeTTaIL `LanguageDef`
transition simulation is a further obligation, beyond the injective data codec.

Source reading, native arithmetic and native runtime agreement are separate
boundaries. Signed `%` follows the divisor-sign remainder convention. Plain
`//` is unregistered in upstream PeTTa and CeTTa's PeTTa profile and remains
data unless defined by the program; it is not a ground division primitive.
Private `new-space` allocation belongs to the CeTTa extension profile, rather
than the shared SWI-PeTTa fragment. Execution uses captured values without reinterpreting them as code.
Zero-fuel exhaustion, primitive faults, an empty answer bag and Boolean `False`
have distinct meanings. Open cyclic unification and partial applications are
outside this profile.

The ordered sequencing rule `Eval.sequence_cons_answers` adapts
`PLeaTTa.PeTTaSpec.PrologCore.OpenOrdered.RunsMany.cons` from
[godelclaw/LeaTTa at 64a6ae3](https://github.com/godelclaw/LeaTTa/tree/64a6ae39d6e437c79d429d33340340df197c0b10).
It uses this evaluator's paths and shared store. `BindingForms` connects
captured-value inertness to those paths through
`captured_value_binding_returns`. Neither result imports PLeaTTa's SLD
machine or asserts agreement of the open-unification profiles.

`ValueOccurrences.executable_variable_derivation` connects variable lookup in
the existing value-occurrence view to the whole-program judgment. A captured
expression is returned as a value; it is not evaluated as code by lookup.
`CallGuardOptimization.executable_raw_argument_iff` connects the actual typed
argument lookup to the shared literal-Atom demand policy.

`MainlineGroundProvider.ExecutableInteger.completed_iff` connects the existing
independent integer/addition judgment to completed machine execution. It
preserves the exact answer list and store and proves there are no input or
output effects. For example, `(+ (+ 2 3) 4)` produces the single integer `9`;
two answer occurrences are impossible for one expression in this fragment.
The Horn-to-Atom embedding is a structural encoding for that fragment, not a
text reader or an arbitrary Boolean/string codec. This result concerns
mathematical integers; native arithmetic representation is a separate boundary.

### Types and standard library

| Module | What it does |
|--------|-------------|
| [TypeSystem.lean](TypeSystem.lean) | Type annotations, arrow types and special type atoms over `Pattern` |
| [TypedEval.lean](TypedEval.lean) | Type-directed evaluation pass-through |
| [StdLib.lean](StdLib.lean) | Ground primitive table with explicit outcomes |
| [MinimalInstructions.lean](MinimalInstructions.lean) | MeTTaIL instructions and their derived library forms |

### Bridges

| Module | What it does |
|--------|-------------|
| [LPSoundness.lean](LPSoundness.lean) | LP soundness: `PeTTaEval` rule application implies least-Herbrand-model membership |
| [PrologBridge.lean](PrologBridge.lean) | Wires `EvalOracle` to concrete PeTTa semantics |
| [TranslateExpr.lean](TranslateExpr.lean) | `compileExpr`: MeTTa expressions to Prolog goals, with correctness theorems against `PeTTaEval` |
| [GroundedOracle.lean](GroundedOracle.lean) | Grounded oracle interface for built-in operations |

`PrologBridge.meTTaPrologOracle` supplies `PeTTaEval` as the meaning of a
`reduceCall`. The translation theorems using that oracle describe this abstract
interface; they do not prove that native Prolog execution implements PeTTa
evaluation. The function-free least-Herbrand-model results have their separate,
explicit fragment hypotheses.

## Qualification

Build and axiom qualification belong to a named module set and source revision.
A source scan alone is insufficient: an imported theorem can inherit axioms or
an unfilled proof. The pattern-level bridge anchors above establish agreement
for their stated relations. The whole-program adequacy theorems connect the independent judgment,
executable machine and its operational graph. Agreement with a guest kernel
still needs an additional program-correctness theorem; finite differential
controls do not prove universal agreement with a native implementation.

`TypeSystem` records annotations. Its annotation lookup predicates are not a
proof of subject reduction or of a cached checker's semantic correctness.

These scans identify candidates for review; prose matches are not proof holes:

```bash
# sorry/admit occurrences (raw):
rg -n --glob '*.lean' '\b(sorry|admit)\b' .
# axiom declarations (prints nothing):
rg -n --glob '*.lean' '^\s*(@\[[^]]*\]\s*)*axiom\s' .
# native_decide occurrences (prints nothing):
rg -n --glob '*.lean' 'native_decide' .
```

## Related

- [LP kernel](../../../Logic/LP) — unification, SLD resolution, Herbrand semantics
- [Prolog layer](../../../Languages/Prolog) — goal language, cut semantics, ISO conformance fixtures (proven against the Lean evaluator)
- [Conformance harness](../../../../scripts/prolog) — SWI parity checks and ISO coverage

## References

- Lucius Gregory Meredith, Ben Goertzel, Jonathan Warrell, Adam Vandervorst, [*Meta-MeTTa: an operational semantics for MeTTa*](https://arxiv.org/abs/2305.17218) (arXiv:2305.17218, 2023) — the MeTTa operational semantics this evaluation layer formalizes.
- Ben Goertzel et al., [*OpenCog Hyperon: A Framework for AGI at the Human Level and Beyond*](https://arxiv.org/abs/2310.18318) (arXiv:2310.18318, 2023) — the Hyperon system MeTTa and PeTTa serve.
- [PeTTa (trueagi-io/PeTTa)](https://github.com/trueagi-io/PeTTa) — the upstream Prolog-based MeTTa interpreter this directory formalizes.

## Retired on 2026-10-05

`lean/mettapedia/_archive/petta-retirement-2026-10-05` holds the March 2026
stage-indexed OSLF and artifact-export route (`OSLFInstance`, `GSLTVertex`,
`StageIndex`, `OSLFPackage`, `StageFiber`, `SemanticBundle`, `ArtifactBundle`,
`ContractCatalog`, `ContractExport`, `BoundaryContract`, `ExecutableBoundary`,
`ExecutionContract`, `Artifacts`, `Unit`, `LookupPlan`,
`Conformance/PeTTaArtifactBridge` and five export scripts) and the earlier
fuel-indexed evaluator `Algorithms/MeTTa/Eval`. Their content that remains in use:

- the rule-only OSLF is `langOSLF (pettaSpaceToLangDef s) "Expr"` from the framework;
- its LP soundness theorem is `petta_safe_space_ruleApp_lp_sound` in `LPSoundness`;
- its modal laws are the framework's generic ones;
- the lookup plan is `Algorithms.MeTTa.LookupPlans`;
- the shared-variable `spaceMatch` checks are kernel-checked examples in `PatternRewrite/Space`;
- the earlier evaluator's test programs, with upstream answers, are `UpstreamAgreement`.
