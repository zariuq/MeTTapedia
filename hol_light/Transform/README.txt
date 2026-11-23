Transform in HOL Light
======================

The four source modules form an independent HOL formulation of transform's
relational core, indexed frames, prepared effects and finite labelled runs.
They use conservative definitions and derived HOL proofs. They do not add an
axiom or implement a theorem checker.

  core.ml       admission, soundness and optional coverage
  frames.ml     typed fibres, morphism action and store transport
  prepared.ml   old/information/result states and occurrence effects
  runs.ml       paths, pullbacks, simulations, observers and footprint diamonds

Open transform.html for a searchable, folding view of the definitions and
theorems in ordinary HOL notation. transform.pretty.txt contains the same
printed statements without the interface. These views are generated from
HOL theorem objects; transform.holr contains the replay evidence.

The additional refinement package uses:

  constraints.ml          local preservation and constraint morphisms
  constraint_frames.ml    the indexed frame construction and exact admission
  constraint_controls.ml  compatible/conflicting commitments in one model
  witnesses.ml            preparation packing, path refinement and observers

Its readable view is refinements.html, with refinements.pretty.txt and the
self-contained refinements.holr certificate. The earlier transform bundle
remains unchanged for its existing consumers.

semantic_effects.ml separates semantic knowledge refinement from the stronger
transported-equation profile. The latter implies semantic refinement and
optional exactness. Equality of its HOL equation predicates preserves equation
membership; it does not recover list order or duplicate counts. Its seven
exported roots are retained in semantic-effects.holr and its readable views.

The Lean source presentation has intrinsic binding-term readback and physical
schema-opening correspondence. Versioned prepared-view bundles retain the
rule, ordered selected views and scope reservation. Admission and publication
recipes remain separate. EventAccount identifies ordered monoid accounts with
the unique interpretation of the free event category.

HOLFrameEncoding represents indexed terms and morphisms in inhabited raw
carriers, with invalid sentinels outside every valid fibre. The nine tc_*
definitions in the semantic-effect export now have checked operational
interpretations in one constructed model: models, solvability, store typing,
transport, frame laws, occurrence updates, semantic effects, optional exactness
and the stronger transported-equation profile. Independent typed bodies are
read against the actual received defining equations.

admission.ml adds general prepared and admitted events with explicit permission
profiles. The earlier history remains a checked prefix of a history with 24
definitions. The loaded prepared/admitted-event predicates agree with indexed
preparation packets and the shared EffectCore.Event interface. Empty candidate
fibres remain empty, and equal endpoints do not identify different firings.
The authored Execute rule preserves and reflects the loaded predicate for its
selected candidate. The scalar source route additionally retains actual parse,
routing and lowering evidence; backward source realization requires the parse
policy's stated canonical coverage.

admission.holr replays 21 roots, including the seven semantic-effect roots;
admission.html and admission.pretty.txt display their source statements.
The solution/guard/profile-inclusion constructors remain explicit
specializations. Their loaded Lean interpretations now agree with readiness,
solution existence, entailment over all future morphisms, and inclusion on
the preparation domain. Restriction preserves candidate and witness data.

run_interpretation.ml provides closed list-constructor, path and pullback laws.
The source list carrier is identified with finite lists from its actual
separation, injectivity and full induction theorems. RunSourceReadback checks
the exact received formulas. CachedDefinitionHistory transfers all 24 earlier
defining theorems into the same mixed-history model at every source type
instance. HOLRunAdmissionJoin then connects the loaded tc_path using the loaded
tc_admitted_event to complete native event words, in both directions.

runs-admission.holr retains the full 28-root semantic/admission/run bundle.
run-model.holr retains the defining equations and seven list/run laws needed
by the model interpretation. interpretation_definitions.ml exports those
actual equations; its aliases are declaration inventory, not additional
correctness theorems. Both certificates have independent replay and tampering
controls. The model receiver additionally checks the original 24 theorem
identities and rejects altered origins, types, root addresses and inventories.
ExportReceiptHistory proves that carrying the accepted history incrementally
returns the same receiver states, avoiding a second traversal of the commands.

PresentationHOLRuns connects the scalar occurrence-source profile to the
loaded run interpretation. Backward realization requires the parse policy's
canonical coverage. PresentationQuotedSource separately connects typed scalar
trees to the existing contextual beta/activation program, including lexical
captures and inert quotation under that profile's active-context policy.
ProgramBindersInterface instantiates the shared effect/admission contract with
that program's actual declaration frames, equation stores and occurrence
updates. PresentationQuotedEvents retains its complete event paths, and
PresentationQuotedHOL connects those paths to the same loaded HOL definitions.
The final-answer observation remains distinct from the retained event word.

Step/Origins retains a rule key beside the complete candidate. The native
instance checks catalogue agreement and authority over the whole firing,
including publication recipes, while retaining the base step's admission.
Parsed quoted-rule references do not grant permission by themselves. Origin
records commute with reference erasure and lift uniquely; actual native
aliases demonstrate that they need not survive erasure of the origin key.
The authored native-origin Execute theorem uses RepresentedEffects: represented
states and candidates interpret into the unrestricted native semantics and
retain a represented result for every prepared candidate, including refusals.
Exact codecs apply only to those represented carriers. Reflection at a fixed
represented endpoint additionally requires injective state interpretation;
existence of a represented endpoint does not. Coverage of an intended native
program's offered candidates is a separate obligation, not surjectivity onto
all mathematical native firings. A real conditional-template publication
protocol exercises this interface and retains the refused alternative's
prepared output. Its finite code set is a control fixture, not a runtime limit.
RepresentedPaths proves finite-path reflection under the declared candidate
coverage law and unique lifting under faithful candidate interpretation.
PresentationRepresentedRuns composes those laws with the actual source
execution equivalence, and PresentationRepresentedHOL connects the resulting
complete words to the loaded HOL path predicate. The counted-store consumer
supplies unbounded state codes, executable decisions and coverage for every
finite run. Its missing-candidate control retains the same state effects but
fails to cover a distinguished event.
The loaded preparation, admission and finite-run correspondences apply at the
profiles described above. Final consolidation qualification and native
implementation refinement remain separate claims.

The calculus has no evaluation default. Admission, soundness, answer coverage,
branch coverage and the existence of prepared results are separate predicates.
Commitment is compatible with soundness. Coverage is needed only when an
interpretation promises to preserve the entire answer family. No trace or
global reversibility is required by these definitions.
EventFeedbackControls exercises the operational-state boundary for records:
two actual first events reach the same store with different histories, and
the next permission differs. No store-only permission predicate represents
that controller. Refused candidates still have their prepared effects.

recording.ml states forward record updates using the continuation instance
of the existing tc_pullback. Its nine roots cover composition, valid indexed
fibres, erasure, unique final records and ordered-word/empty-fibre controls.
recording.holr and its readable views have independent replay and three
tampering controls. This is a supplement to the earlier certificates.
RecordingInterpretation connects the loaded pullback to forward updates;
HOLObserverEncoding retains native state indices and rejects refused packets.
HOLObserverModel constructs the continuation carrier and proves agreement
with the dependent event observer. HOLObserverAdmission uses the actual
loaded admitted-event predicate and path operation in that same model.
The concrete controls distinguish two ordered words that change the store,
reject a record at the wrong state and preserve an empty valid record fibre.
HOLPublications applies the loaded recording interpretation to actual prepared
publications and success receipts. Prior names move along the event's frame
morphism before new names are appended. The constrained-admission control
retains its inherited payload and fresh receipt, while the loaded base
prepared-event predicate succeeds and its admitted-event predicate refuses.

Representation
--------------

parallel.ml adds total configuration coexistence, common-solution and
transport laws, the exact resource-enable condition under a context, and
the resource frame law. Shared reads, occurrence aliases, allocation
collisions and destructive interference have concrete controls. Its fifteen
roots are replayed in parallel.holr; parallel.html and parallel.pretty.txt
display the actual source statements. parallel-example.metta consumes the
replayed proof handles.

The two exported parallel definitions also pass the registered Lean receiver.
HOLParallelAgreement constructs a common model and proves that these loaded
operations agree with native indexed configuration coexistence. Equation
lists are observed by membership; their layout and duplicate counts remain
separate observations. Empty valid fibres remain empty. The newer contextual
run-composition and interchange contracts require their separate HOL bridge.

parallel_domains.ml checks complete prepared-event words at each computed
prefix. Its nine roots characterize the exact execution domain, sequential
composition and the existing admitted-event specialization. Refused prepared
targets remain data, noncommuting events retain order, and distinct words can
have equal endpoints. parallel-domains.holr and its readable views retain those
nine correctness roots together with seven list/run laws, four word-recursion
laws and fifteen defining-equation inventory roots. The inventory roots alias
the actual defining equations; they are not additional correctness results.

HOLPreparedWordModel connects the loaded target and domain operations to the
same constructed model as the earlier preparation, admission and path
operations. The domain holds exactly when a native path with that complete
event/preparation word exists. Concatenation checks the second word at the
first word's computed target. This target is independent of permission.
HOLPreparedWordControls provides a separate repeated-tell profile admitting
every finite Boolean word and refusing every nonempty word under false
permission. It does not change the earlier source profile's guards.

The combined source export has independent replay and three certificate
tampering controls. Its Lean receiver checks all eleven exact list/run/word
roots, the retained twenty-four defining theorems and eighteen separating
readback controls. The certificate records the source and receiver hashes.
The trace package below supplies a separate native-interchange interpretation.
The word interpretation does not establish C implementation refinement.

parallel_trace.ml defines the equivalence generated by explicitly selected
exchange and transport equations. Its observation definition quantifies over
all Boolean predicates respecting those equations. The source proves
generation, equivalence, leastness and observer descent. An empty generating
relation retains distinct events even when their endpoints are equal.

parallel-traces.holr retains the earlier thirty-five word/model roots and
nine trace roots; parallel-traces.html and parallel-traces.pretty.txt display
the source statements. TC_TRACE_MEANING supplies the exact formula consumed
by the Lean receiver. HOLTraceModel interprets it in the same received model
as preparation, admission and complete words. The selected generators are
actual native residual interchanges and transport similarities. Their loaded
equivalence agrees with the existing native trace relation in both directions.
The invalid raw run remains outside every valid run class.

HOLTraceControls exercises native helpers whose declaration frames change.
Different four-block schedules have one loaded trace and keep different raw
histories. A separate control proves that canonical interchange alone omits
identifications made by transport similarity. Dropping all generators fails
to identify the higher-order schedules. The original contextual source/native
join and the HOL interpretation of the placement-dependent composition grade
remain separate obligations.

Frames, terms and morphisms have polymorphic HOL carrier types. The terms
and hom predicates delimit their valid fibres; an object fibre may be empty.
The theory does not require a dependent HOL type constructor. Morphism action
and equivalence are parameters. Theorems state the action and typing laws they
use rather than assuming category laws on raw morphism representations.

Equation stores are predicates on pairs of terms. This is their semantic
representation, not a claim that every predicate has a finite executable
presentation. Occurrence sets distinguish occurrence identity from payload
equality. tc_enabled models the positive take/read/make footprint; semantic
queries belong in the guard. Its frame theorem does not license framing an
arbitrary absence query.

The tc_admits solution/guard profile requires readiness, at least one solution, and a guard holding at
every solution. tc_prepares requires a preparation for ready solvable firings
without consulting that guard. tc_move retains the preparation witness used
to compute the result; no uniqueness of that witness is silently assumed.

tc_sound says that every result solution reads back to a source solution.
tc_covers is the stronger, optional property that each source answer can be
recovered through a faithful common-frame extension. tc_same_target_covers
is sufficient but strictly stronger, as the fresh-target controls demonstrate.
A covering family must account for every branch result as well as every source
solution; an unrelated extra branch is refused by its negative control.

The prepared-effect contract supplies both frame morphisms, the transported
old knowledge, the information at the intermediate frame, the settled result
knowledge and the exact occurrence update. TC_PREPARED_MODELS_ALONG derives
solution pullback from those structural laws. TC_PREPARED_PATH_MODELS_START
lifts it to any finite labelled path of interpreted prepared effects.

Paths retain their event word as mathematical evidence. This representation
does not impose logging on an executor. The event carrier may include full
firing and preparation data. The current bisimulation is strong and labelled;
using labels alone does not establish history-preserving bisimulation.
TC_POSITIVE_FOOTPRINT_DIAMOND covers positive occurrence effects. It does not
commute arbitrary guards: TC_ABSENCE_NOT_FRAMED is the negative control.

Local constraints and witnessed firings
--------------------------------------

Global reflection preserves every valid inequality context. A particular
prepared effect instead needs to preserve the context it actually carries.
TC_REFLECTION_IFF_ALL_CONTEXTS states this quantifier difference exactly.
TC_LOCAL_PRESERVATION_EXACT characterizes validity of the transported context.

TC_CONSTRAINT_FRAME_LIFT constructs a new instance of the same frame laws.
Its objects pair a base frame with a valid inequality context. Its morphisms
require every future respecting the target context to pull back to a future
respecting the source context. TC_CONSTRAINT_SOLVABLE_EXACT and
TC_CONSTRAINT_ENTAILS_EXACT identify solutions and guards with the separating
solutions of the base model. TC_LOCAL_ADMISSION_EXACT lifts and reflects the
whole prepared-effect admission contract.

The inequalities are carried into the result. Local preservation does not
permit forgetting them after a firing. The two-bit observation controls admit
X := false with Y != true, refuse that commitment with X != false, and keep
the latter input problem solvable. A second control shows two commitments
compatible separately with X != Y but incompatible together: the second must
be checked against the transported context.

Witness packing retains each preparation as part of the firing data. A fixed
complete event then has one result, while different witnesses remain different
events. Every finite coarse execution has a witnessed refinement and every
witnessed execution projects back. After the declared label projection, the
systems are strongly bisimilar. TC_WITNESS_OBSERVER_DESCENT gives the exact
condition for erasing witnesses from a pointwise event observation: agreement
on all valid witnesses of the same firing.

These are representation laws, not procedures for finding or enumerating
witnesses. They do not license moving a dynamic choice to installation time
or sharing one choice across separate calls. Ordinary LTS bisimulation does
not preserve parallel-edge counts or
probability mass. The controls retain two distinct preparations even when they
produce the same result. Store predicates describe constraint meaning; a
representation exposing order, duplicates or textual provenance needs that
additional data and its own observation contract.

Coverage and preservation of solvability remain separate capabilities. A
committing branch may eliminate all models; a live-result profile additionally
needs joint consistency of its result equations and inequalities.

Checking
--------

From the workspace containing the Mettapedia and hyperon repositories:

  python3 Mettapedia/hol_light/check_theory.py \
    Mettapedia/hol_light/Transform/core.ml \
    Mettapedia/hol_light/Transform/frames.ml \
    Mettapedia/hol_light/Transform/prepared.ml \
    Mettapedia/hol_light/Transform/runs.ml \
    --library-through lists.ml --output scratch/transform-hol-check

The runner uses the existing pinned HOL Light ProofTrace producer and HOLR
adapter. It checks every exported root for undischarged hypotheses, then asks
CeTTa's standard-policy HOL kernel to replay the primitive derivations and
compare every proposed sequent. An ordinary MeTTa consumer also retrieves
checked theorem handles. The gate requires refusal of a changed root claim,
an additional nonstandard axiom and a truncated stream.

Producer paths and the CeTTa binary may be supplied by command-line options.
The producer's source inventory uses read-only version-control queries.
Qualification records the theory, producer, checker and certificate hashes.

The retained certificate can also be checked directly:

  hyperon/CeTTa/cetta --lang hol-light --profile standard \
    Mettapedia/hol_light/Transform/transform.holr

To retrieve checked theorem handles from an ordinary MeTTa program:

  hyperon/CeTTa/cetta --lang he --quiet \
    Mettapedia/hol_light/Transform/transform-example.metta

transform.certificate.json identifies the sources and certificate. The exact
kernel syntax is retained in transform.checked-sequents.txt. The earlier
core-only bundle remains independently checkable via core.holr.

The refinement package can be reproduced from the workspace in Bash:

  python3 Mettapedia/hol_light/check_theory.py \
    Mettapedia/hol_light/Transform/{core,frames,prepared,runs,constraints,constraint_frames,constraint_controls,witnesses}.ml \
    --export-from Mettapedia/hol_light/Transform/constraints.ml \
    --export-from Mettapedia/hol_light/Transform/constraint_frames.ml \
    --export-from Mettapedia/hol_light/Transform/constraint_controls.ml \
    --export-from Mettapedia/hol_light/Transform/witnesses.ml \
    --library-through lists.ml --output scratch/transform-hol-refinements

--export-from selects the new theorem roots. Every input module remains
source-pinned, and all primitive proof dependencies are included in the
certificate. The generated HTML includes imported definitions for context.
--reuse-export reuses a completed export in the same output directory only
after checking the source helper, HOL library, producer and artifact hashes.
Native proof replay and the refusal controls still run. The two corrupted
controls are emitted from one decoding of the same proof graph.

  hyperon/CeTTa/cetta --lang he --quiet \
    Mettapedia/hol_light/Transform/refinements-example.metta

General preparation and admission can be reproduced with:

  python3 Mettapedia/hol_light/check_theory.py \
    Mettapedia/hol_light/Transform/{core,frames,prepared,semantic_effects,admission}.ml \
    --export-from Mettapedia/hol_light/Transform/semantic_effects.ml \
    --export-from Mettapedia/hol_light/Transform/admission.ml \
    --library-through lists.ml --output scratch/transform-hol-admission

The qualified library boundary keeps shared defining records identical across
these exports. The receiver checks the extension and preserves the earlier
cache. The ordinary proof-handle consumer is:

  hyperon/CeTTa/cetta --lang he --quiet \
    Mettapedia/hol_light/Transform/admission-example.metta

The paired run and interpretation artifacts can be regenerated with:

  python3 Mettapedia/hol_light/check_theory.py \
    Mettapedia/hol_light/Transform/{core,frames,prepared,semantic_effects,admission,runs,run_interpretation}.ml \
    --export-from Mettapedia/hol_light/Transform/semantic_effects.ml \
    --export-from Mettapedia/hol_light/Transform/admission.ml \
    --export-from Mettapedia/hol_light/Transform/run_interpretation.ml \
    --library-through lists.ml --output scratch/transform-hol-runs

  python3 Mettapedia/hol_light/check_theory.py \
    Mettapedia/hol_light/Transform/{core,frames,prepared,semantic_effects,admission,runs,run_interpretation,interpretation_definitions}.ml \
    --export-from Mettapedia/hol_light/Transform/run_interpretation.ml \
    --export-from Mettapedia/hol_light/Transform/interpretation_definitions.ml \
    --library-through lists.ml --output scratch/transform-hol-model

Build HOLRunAdmissionJoin and ExportReceiptHistory with Lake in the Lean
project before running the typed source receiver. From the workspace:

  python3 Mettapedia/hol_light/check_interpretation.py \
    scratch/transform-hol-model --output scratch/transform-model-receiver

The adapter selects source addresses and groups the existing type-definition
pairs. The typed receiver checks the commands, formulas and theorem identities;
the adapter is not a proof checker. --prepare-only emits input data without
claiming qualification. Execution of this receiver is distinguished from a
closed kernel reduction of the entire concrete history and from a native
implementation-refinement proof.

  hyperon/CeTTa/cetta --lang he --quiet \
    Mettapedia/hol_light/Transform/runs-admission-example.metta

Trust and scope
---------------

The Lean companion is in CMR Step/DisequalityLocal.lean, with concrete controls
in Step/DisequalityLocalControls.lean. withLocalDisequations constructs a Step
without a global reflection hypothesis. The compatible and conflicting
commitments are checked there too. For globally reflecting steps, admission,
results and settlement agree with the existing construction; inverse maps of
runs preserve firing words and endpoints. No existing core file was replaced.
This local disequation integration is a separate refinement consumer. Its
equivalence to every declaration in the older refinement bundle is not asserted
by the semantic-effect, admission and run interpretations described above.

The OCaml tactic engine is a producer. The native HOL kernel checks its
primitive derivations; running OCaml tactics inside CeTTa is unnecessary.
The native kernel remains a trusted implementation, independently exercised
against the source derivations. No refinement proof of that C implementation
is supplied by this package.

The source interpretation uses the frame solution semantics in CMR
Step/Interface, preparation and explicit permission in Step/EffectCore, and
the admitted-event paths. Optional answer coverage remains a separate property
in Step/SettlementCoverage. The HOL definitions are independently authored;
their agreement is proved against the loaded definitions, not inferred from
common generation. Step/Consolidation is the Lean import boundary for the
contracts, consumers, source profiles and controls. These results are not a
compiler-correctness theorem, a CeTTa transform implementation, a solution of
dependent unification, or an x86 proof.

Additional causal/history-preserving and weak execution contracts, and native
realization, retain their own qualification obligations.
A native realization must preserve the observations promised by its particular
execution policy; a forward simulation alone permits extra target behavior.

The ordinary native HOL API is hyperon/CeTTa/lib/holkernel.metta. The retained
MeTTa sources at Mettapedia/metta/hol_light/derived.metta contain derived
proof-command generators for the quoted guest kernel. They are distinct from
an interactive tactic system over native theorem handles. The OCaml source
files here contain the current proof automation.

Consolidation qualification
---------------------------

consolidation-qualification.json records the checked source snapshot,
original requirement evidence and the separately qualified HOL bundles.
The internal dependency closure has 3323 source modules,
including 1055 affected modules. Each has a current successful
warning-as-error check; external libraries were reused.
The 43 requirement rows select 241 declarations,
whose only axioms are propext, Classical.choice and Quot.sound.
The grammar, represented-state and GSOS correspondences retain their
stated coverage, binding and observation hypotheses. Complete native
implementation refinement and full rho/PeTTa factorization are separate.
The qualification file records build evidence; mathematical guarantees
are the propositions proved by the selected declarations.
