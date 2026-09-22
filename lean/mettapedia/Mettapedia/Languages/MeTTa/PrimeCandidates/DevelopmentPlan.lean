import Mettapedia.Languages.MeTTa.PrimeCandidates.Specification

/-!
# Broad candidate-specification obligations

This is a development ledger, not an adopted language or a semantic
qualification record. A proved row stores its exact theorem. A partial row
retains supporting claims without discharging its stated acceptance condition.
Mechanical rows close only when the status runner supplies a fresh result for
their named source gate; a build or import count is not a mathematical proof.

Dependencies describe the order of integration work, not hidden hypotheses of
the stored theorems. Stable IDs are not reused when an obligation is replaced.
Changing scope or the denominator requires a new plan version. Completion of
this checklist is not a percentage of all future cognitive-language research.

This broad inventory is not the critical path or a readiness denominator for
integrated higher-order MeTTa experimentation. In particular, closing every
public observation, binding, evaluation, or final handoff row is not a premise
of an already qualified HOL/DTT/NIK fragment. Experiments must pin the rules
and observations they use; they need not settle every Prime convention.
The metatheory paper states that integration scope; working notes are maintained
separately. This inventory retains its original row meanings and theorem evidence;
it neither blocks those experiments nor supplies a replacement completion score.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DevelopmentPlan

open Specification
open Mettapedia.TypeTheory

def version : String := "2026-09-13.1"

inductive Milestone where
  | isolation | justification | contextualAbstraction | decisionFamilies
  | jointAssembly | handoff
  deriving DecidableEq, Repr

def milestones : List Milestone :=
  [.isolation, .justification, .contextualAbstraction, .decisionFamilies,
    .jointAssembly, .handoff]

inductive Progress where
  | proved (claim : CheckedClaim)
  | sourceGate (id : String)
  | partialEvidence (claims : List CheckedClaim) (gap : String)
  | unresolved (gap : String)

structure Obligation where
  id : String
  milestone : Milestone
  acceptance : String
  requirementIds : List String
  dependsOn : List String
  progress : Progress
  decisionFamily : Option Decision := none

/-- The complete denominator for this plan version. Source isolation is
bounded by explicitly declared roots and the reviewed cross-boundary
inventory. Neither a classification nor a build asserts universal theory
independence for arbitrary future additions. -/
def obligations : List Obligation := [
  { id := "ISO-001", milestone := .isolation
    acceptance := "The independent requirement and semantic-support roots have no candidate/current dependency."
    requirementIds := ["INV-TT-001"], dependsOn := []
    progress := .sourceGate "isolation.requirement-interface" },
  { id := "ISO-002", milestone := .isolation
    acceptance := "Staged-reflective presentation, revisioned occurrence flow, returned-fibre and first-class route theory are independent of selected candidates."
    requirementIds := ["INV-TT-001", "INV-TT-004"], dependsOn := ["ISO-001"]
    progress := .sourceGate "isolation.staged-reflective" },
  { id := "ISO-003", milestone := .isolation
    acceptance := "Dialect gluing and structural morphism laws are independent of quotation/choice instances."
    requirementIds := ["INV-TT-001"], dependsOn := ["ISO-001"]
    progress := .sourceGate "isolation.dialect-gluing" },
  { id := "ISO-004", milestone := .isolation
    acceptance := "Candidate/current branches are independent; retired foundation namespaces and object declarations do not remain active."
    requirementIds := ["INV-TT-001"], dependsOn := []
    progress := .sourceGate "isolation.integration-direction-and-names" },
  { id := "ISO-005", milestone := .isolation
    acceptance := "Every remaining cross-boundary module has a justified classification; no unclassified candidate instance is advertised as reusable theory."
    requirementIds := ["INV-TT-001"], dependsOn := ["ISO-002", "ISO-003", "ISO-004"]
    progress := .sourceGate "isolation.classified-crossings" },
  { id := "TRACE-001", milestone := .justification
    acceptance := "Completing scoped predicate evidence establishes satisfaction for the very same candidate."
    requirementIds := ["INV-TT-001"], dependsOn := ["ISO-001"]
    progress := .proved (checked "TRACE-C-001" "same-candidate evidence completion"
      (@DesignStudy.Specification.Evidence.complete.{0, 0})) },
  { id := "TRACE-002", milestone := .justification
    acceptance := "Necessity under an added requirement retains explicit inhabitance of the extended class."
    requirementIds := ["INV-TT-001"], dependsOn := ["TRACE-001"]
    progress := .proved (checked "TRACE-C-002" "consistent extension of nonvacuous determination"
      (@DesignStudy.Specification.determination_of_extension.{0, 0})) },
  { id := "TRACE-003", milestone := .justification
    acceptance := "Combining requirement namespaces preserves one shared assembly index, rather than combining unrelated existential models."
    requirementIds := ["INV-TT-001"], dependsOn := ["TRACE-001"]
    progress := .proved (checked "TRACE-C-003" "conjunction at one candidate index"
      (@DesignStudy.Specification.satisfies_conjoin_iff.{0, 0, 0})) },
  { id := "TRACE-004", milestone := .justification
    acceptance := "All six families' draft-critical requirements have semantic predicates on the proposed shared assembly, with versioned normative provenance."
    requirementIds := ["INV-TT-001", "REQ-VIEWS-001", "REQ-UNIFORM-001", "REQ-NIK-001"]
    dependsOn := ["TRACE-002", "TRACE-003"]
    progress := .partialEvidence [sharedJudgmentEvidence, operationalServiceEvidence,
      nativeHOLMeaningEvidence, nativeMatchingMeaningEvidence, nestedServiceEvidence, retainedSemanticEvidence]
      "SharedJudgmentSemanticRequirements collects 31 native and four declaration predicates plus source and required-service predicates on one shared record, with resolved normative references. The same quotient proves 28 native component predicates, three declaration clauses and the original required four-face contract. SEM-ID-004 is refuted for the canonical family-only-frame/exact-quotient attachment; merely scoping the operation cannot restore the lost motive function. A separate retained-function profile now jointly satisfies all 33 native clauses on one quotient with the actual source assembly, original four-face service contract and required wire/HOL declarations. TRACE-004 still needs the complete six-family/public-consumer predicates; compatible constructor and operational/host joint qualification belong to ASM-005." },
  { id := "VIEW-001", milestone := .contextualAbstraction
    acceptance := "A supplied heterogeneous policy-coordinate closure derives congruence for the actual operation."
    requirementIds := ["REQ-VIEWS-001"], dependsOn := ["TRACE-001"]
    progress := .proved (checked "VIEW-C-001" "operation closure derives scoped congruence"
      (@Mettapedia.GSLT.Core.PolicyFamily.OperationReindex.preserves_policyEquivalent.{0, 0, 0, 0, 0, 0})) },
  { id := "VIEW-002", milestone := .contextualAbstraction
    acceptance := "Restricting a closed policy family commutes with the executable vector action, including dependent result transports."
    requirementIds := ["REQ-VIEWS-001"], dependsOn := ["VIEW-001"]
    progress := .proved (checked "VIEW-C-002" "closed restriction square"
      (@Mettapedia.GSLT.Core.PolicyFamily.OperationReindex.vectorMap_reindex.{0, 0, 0, 0, 0, 0, 0, 0})) },
  { id := "VIEW-003", milestone := .contextualAbstraction
    acceptance := "The selected object-language substitution and admitted dependent families descend through the same declared contextual views."
    requirementIds := ["REQ-VIEWS-001", "INV-TT-007"], dependsOn := ["VIEW-002"]
    progress := .proved contextualDescentEvidence },
  { id := "VIEW-004", milestone := .contextualAbstraction
    acceptance := "One object-HOL induction principle proves map-length, with a countermodel excluding that theorem from the displayed equations alone."
    requirementIds := ["REQ-UNIFORM-001"], dependsOn := ["TRACE-001"]
    progress := .proved (checked "VIEW-C-004" "uniform proof and strict equation-only boundary"
      (And.intro (Mettapedia.Logic.HOL.UniformListInduction.mapLength_derivation (Γ := []))
        Mettapedia.Logic.HOL.UniformListInduction.equations_do_not_derive_mapLength)) },
  { id := "VIEW-005", milestone := .contextualAbstraction
    acceptance := "Eligible specialized proof obligations are recognized, transported and reconstructed into the retained HO representation, with stated limitations and costs."
    requirementIds := ["REQ-UNIFORM-001"], dependsOn := ["VIEW-004"]
    progress := .proved specializedChartEvidence },
  { id := "VIEW-006", milestone := .contextualAbstraction
    acceptance := "Hiding, reversible specialization, erasure and bounded approximation have distinct contracts indexed by context and revision."
    requirementIds := ["REQ-VIEWS-001", "INV-TT-002"], dependsOn := ["VIEW-001"]
    progress := .proved revisionViewsEvidence },
  { id := "FORK-OBS", milestone := .decisionFamilies
    decisionFamily := some .observation
    acceptance := "Public operations identify their view families and the consumer-specific alternatives that remain."
    requirementIds := (study .observation).requirementIds, dependsOn := ["VIEW-002", "VIEW-003", "VIEW-006"]
    progress := .partialEvidence (study .observation).constraints
      "Context closure determines the greatest safe collision relation; actual native resumption has a least answer/state readout. Complete worlds are congruent under actual source substitution, two sequencing forms and choice, with exact backend completion. Code inspection distinguishes an administrative detour; a later admitted state-sensitive continuation distinguishes equal present answers. Scoped reference changes commute with actual native substitution/effects and preserve typed results. Retained origin inspection coexists with live evaluation between executions. Resolved reference-value capture obeys no-redirection; surface bindings may instead pass delayed computations. Ground refinement computes categorical common extensions, but a rejected extension does not force silence or one failure handler. Finite zero observation and loss of coverage/faults through value-only collection are separately checked. Qualify within-execution named-table reads, the source-level binding interface, and the remaining public completion and mixed-result interfaces. First answer remains any accepted answer; stronger strategy/effect promises are separate. This inventory does not select a global observer or cover arbitrary reflection and resampling." },
  { id := "FORK-ID", milestone := .decisionFamilies
    decisionFamily := some .identity
    acceptance := "Motive, J/K/UIP, code and route identity alternatives have exact scope and discriminators in the admitted fragment."
    requirementIds := (study .identity).requirementIds, dependsOn := ["VIEW-003"]
    progress := .proved scopedIdentityEvidence },
  { id := "FORK-ADM", milestone := .decisionFamilies
    decisionFamily := some .admission
    acceptance := "Formation, conversion, evidence checking and search have separately specified roles and compatible interfaces."
    requirementIds := (study .admission).requirementIds, dependsOn := ["TRACE-003"]
    progress := .partialEvidence (study .admission).constraints
      "Opaque signatures extend List/J/relator admission with preservation and the unchanged exact checker. Authored conversion between admitted endpoints has a formed completed path, preserved by refined substitution. The shared semantic interface now uses independently formed contexts, and its actual quotient interpretation covers native judgments, substitutions and converted annotations. Raw service requests retain unformed contexts without receiving native admission; a successful typed substitution into a formed target cannot supply missing source formation. Scoped proposition branching distinguishes accepted support, actual refutation and incomplete search; empty samples and rejected proofs do not refute a proposition. The retained native constructor component and original four-face service contract are now jointly qualified on that interpretation. Host/public-consumer comparisons remain; these laws do not prove consistency, normalization or universal service success." },
  { id := "FORK-EVAL", milestone := .decisionFamilies
    decisionFamily := some .evaluation
    acceptance := "CBPV structure, sharing, effects, resampling and choice have observation-indexed equations and independent alternatives."
    requirementIds := (study .evaluation).requirementIds, dependsOn := ["VIEW-002", "VIEW-006"]
    progress := .partialEvidence (study .evaluation).constraints
      "The shared handler/world pair qualifies admitted scoped programs and finite repeated requests with exact state, branches, intents and replies. Actual matching/HOL services satisfy active thunk/function/continuation equations in the native-indexed polarized machine, with real captured and higher-order arguments and independently admitted dependent results. Their qualified callbacks also cross target scopes; a formed open variable distinguishes exact inspection from native admission. Stored producer origins separate active equations from heap/code observations. Evidence-conditioned branching invokes neither body for incomplete evidence. General captured-heap, sharing/resampling and receipt-consumer contracts still need qualification on the same package; these scoped laws do not force Need, call-time choice or one empty/search policy." },
  { id := "FORK-HOST", milestone := .decisionFamilies
    decisionFamily := some .mathematicalHost
    acceptance := "Shared STT/DTT and set-theory routes state formation, proof dependencies, universes, recoverability and comparison criteria."
    requirementIds := (study .mathematicalHost).requirementIds, dependsOn := ["VIEW-004"]
    progress := .partialEvidence (study .mathematicalHost).constraints
      "The same formed syntactic CwF qualifies Pi/Sigma, Id/reflexivity, native motive frames/boundaries, universes, installed declarations and the required four-face specimen. The canonical family-only J attachment to this exact quotient is refuted; the separate retained-function interface now jointly qualifies all 33 native clauses with the source, fixed four-face services and actual required declarations. Indexed-environment and operational-presheaf/host comparisons remain open. A coarser semantic equality can lose conversion reflection without losing independently required native admission. Finite-list union does not make an abstract-set host; no full HOTG or optimal host is selected." },
  { id := "FORK-HO", milestone := .decisionFamilies
    decisionFamily := some .reasoning
    acceptance := "GSLT/OSLF interfaces and all four NIK faces state the actual supported judgments, residuals and trust boundaries."
    requirementIds := (study .reasoning).requirementIds, dependsOn := ["TRACE-003"]
    progress := .partialEvidence (study .reasoning).constraints
      "The HOL workload connects model discrimination, submitted proofs and revision reuse. Its structural producer now retains the actual submitted proof; theorem application and strategy inspection have distinct qualified views. Actual assembly callbacks feed the native-proof and submitted-receipt services. A sound proof producer can ignore submitted history, so faithful replay is a separate consumer contract. A required four-face registry fixes the caller's interfaces and native surfaces and rejects vacuous source substitution. Finite repeated matching/HOL calls have exact typed backends and generated complete-run OSLF meaning. Ordinary rewrite changes may alter conditional equation premises even when equation text is retained. The full public-judgment/native/model integration, raw proof-byte validation and unrestricted OSLF completeness remain open." },
  { id := "ASM-001", milestone := .jointAssembly
    acceptance := "In one query-first model, the authored request enumerates exactly its semantic answer bag with value-level causal receipts under a supplied revision encoding."
    requirementIds := ["INV-TT-001", "INV-TT-008"], dependsOn := ["ISO-002", "TRACE-003"]
    progress := .proved queryFirstAssemblyEvidence },
  { id := "ASM-002", milestone := .jointAssembly
    acceptance := "Dependent transport, matching and logical admission interoperate on one specified syntax and semantic state, with a rejecting control."
    requirementIds := ["INV-TT-001", "INV-TT-003", "INV-TT-004", "INV-TT-007"]
    dependsOn := ["FORK-ID", "FORK-ADM"]
    progress := .proved matchedTransportEvidence },
  { id := "ASM-003", milestone := .jointAssembly
    acceptance := "Uniform HO mathematics and specialized obligations run through the same retained syntax, theory assumptions and reconstruction boundary."
    requirementIds := ["REQ-UNIFORM-001"], dependsOn := ["VIEW-005", "FORK-HOST"]
    progress := .proved uniformHostServiceEvidence },
  { id := "ASM-004", milestone := .jointAssembly
    acceptance := "One claim connects hypothesis generation, model discrimination, imported proof use and revision-sensitive reuse with distinct outcomes."
    requirementIds := ["REQ-NIK-001", "INV-TT-002", "INV-TT-003"]
    dependsOn := ["FORK-HO", "FORK-ADM"]
    progress := .proved cognitiveWorkloadEvidence },
  { id := "ASM-005", milestone := .jointAssembly
    acceptance := "The candidate contract jointly satisfies its draft-critical predicates on explicit shared data and translations, with genuine remaining choices parameterized lawfully."
    requirementIds := ["INV-TT-001", "REQ-VIEWS-001", "REQ-UNIFORM-001", "REQ-NIK-001"]
    dependsOn := ["ISO-005", "TRACE-004", "FORK-OBS", "FORK-EVAL", "ASM-001", "ASM-002", "ASM-003", "ASM-004"]
    progress := .partialEvidence [sharedJudgmentEvidence, operationalServiceEvidence,
      nativeHOLMeaningEvidence, nativeMatchingMeaningEvidence, nestedServiceEvidence, retainedSemanticEvidence]
      "Actual matching/HOL requests compose in one scoped source and typed backend. The shared quotient has 28/31 proved native component predicates, three declaration clauses and the unchanged required four-face specimen. Native J meaning/beta hold on every submitted tuple, but SEM-ID-004 refutes factoring their exact outputs through canonical family-only inputs. This is a failed attachment, not three missing proofs; SEM-ID-005/007 are not independently refuted. The separately named retained profile now qualifies all 33 native clauses, seven source clauses, six fixed service clauses and four declaration clauses on one common record. The old 31-clause profile is unchanged. Complete operational-presheaf, host and public-consumer comparisons; this is a closed native component, not yet the whole six-family model. Normalization is not claimed." },
  { id := "HAND-001", milestone := .handoff
    acceptance := "Current CeTTa comparisons cover the selected contract surfaces, with inspection, testing and proven refinement distinguished."
    requirementIds := ["INV-TT-001", "REQ-NIK-001"], dependsOn := ["ASM-005"]
    progress := .unresolved "All six decision families have pinned source observations and explicit open correspondences. Five experimental-draft probe topics retain five historical runs with 74 literal outputs. A later snapshot separately records eight source observations and one isolated existing-binary probe with five outputs: a raw theorem record is accepted at use while explicit proof replay remains inert. No C rebuild or full gate is claimed for this probe. Exact-name ownership and retained proof fields improve the draft, while qualification of raw records and conversion fallback remains open. Align these distinct observations with the jointly qualified candidate contract; failed proof search supplies no negation. Other proposed experiments remain unexecuted. C need not be complete before a draft." },
  { id := "HAND-002", milestone := .handoff
    acceptance := "Executable non-Horn experiments and extension contracts distinguish the remaining choices without assuming a Lean emitter."
    requirementIds := ["REQ-UNIFORM-001", "REQ-NIK-001"], dependsOn := ["ASM-002", "ASM-003", "ASM-004"]
    progress := .partialEvidence [matchedTransportEvidence, uniformHostServiceEvidence,
      cognitiveWorkloadEvidence, sharedJudgmentEvidence, operationalServiceEvidence,
      nativeHOLMeaningEvidence, nativeMatchingMeaningEvidence, nestedServiceEvidence, retainedSemanticEvidence]
      "The joint runner exercises accepted and declined two-call sources, retaining replies and effectful worlds; retained proof strategies and the fixed-input four-face registry supply further executable controls. Native admission, independently authored backend laws and generated complete-run OSLF meaning cover arbitrary finite scoped compositions. Complete the remaining public-operation, common four-face and host-extension contracts before treating this as the full handoff; no Lean emitter or C completion is required." },
  { id := "HAND-003", milestone := .handoff
    acceptance := "Stable obligations have unique IDs, resolving normative references and earlier dependencies; status exposes denominators, blockers and source-gate scope."
    requirementIds := [], dependsOn := []
    progress := .sourceGate "ledger.structure" },
  { id := "HAND-004", milestone := .handoff
    acceptance := "The live specification and paper agree with the qualified candidate, with final source/build/axiom checks and an immutable handoff report."
    requirementIds := ["INV-TT-001"], dependsOn := ["HAND-001", "HAND-002", "HAND-003"]
    progress := .unresolved "Intermediate successful builds are recorded separately; final qualification and paper claims must track the completed contract." }]

def ids : List String := obligations.map (·.id)

def find? (id : String) : Option Obligation :=
  obligations.find? (fun row => row.id == id)

def Progress.isClosed (passedGates : List String) : Progress → Bool
  | .proved _ => true
  | .sourceGate id => passedGates.contains id
  | .partialEvidence _ _ | .unresolved _ => false

def Obligation.isClosed (passedGates : List String) (row : Obligation) : Bool :=
  row.progress.isClosed passedGates

def closedIds (passedGates : List String) : List String :=
  (obligations.filter (·.isClosed passedGates)).map (·.id)

/-- Policy readout only: selecting a direction does not change `isClosed`. -/
def Obligation.hasSelectedDirection (row : Obligation) : Bool :=
  row.decisionFamily.any (fun family => (study family).selection.isSome)

/-- A separate planning measure: proved/gated rows together with rows whose
development direction is selected. Never use this to report proof closure. -/
def developmentResolvedIds (passedGates : List String) : List String :=
  (obligations.filter fun row => row.isClosed passedGates || row.hasSelectedDirection).map (·.id)

def selectedPendingIds (passedGates : List String) : List String :=
  (obligations.filter fun row => !row.isClosed passedGates && row.hasSelectedDirection).map (·.id)

def outstanding (passedGates : List String) : List Obligation :=
  obligations.filter (! ·.isClosed passedGates)

def availableNext (passedGates : List String) : List Obligation :=
  (outstanding passedGates).filter fun row =>
    row.dependsOn.all ((closedIds passedGates).contains ·)

/-- Counts use this version's explicit denominator. Supporting a row is not
closing it, and uninspected source gates are not silently counted as passed. -/
def counts (passedGates : List String) (milestone : Milestone) : Nat × Nat :=
  let rows := obligations.filter (·.milestone == milestone)
  ((rows.filter (·.isClosed passedGates)).length, rows.length)

/-- Supporting evidence remains visible without receiving completion credit. -/
def partialCount (milestone : Milestone) : Nat :=
  (obligations.filter fun row => row.milestone == milestone &&
    match row.progress with
    | .partialEvidence _ _ => true
    | _ => false).length

def dependenciesEarlier : List String → List Obligation → Bool
  | _, [] => true
  | seen, row :: rest =>
      row.dependsOn.all seen.contains && dependenciesEarlier (row.id :: seen) rest

def structurallyValid (rows : List Obligation) : Bool :=
  decide (rows.map (·.id)).Nodup &&
    dependenciesEarlier [] rows &&
    rows.all (fun row => row.requirementIds.all
      ((requirementReferences.map (·.id)).contains ·))

theorem obligation_ids_unique : ids.Nodup := by decide

theorem plan_structure_valid : structurallyValid obligations = true := by decide

/-- An actual negative control for the registry gate: duplicated obligations
do not become valid just because their stored theorems are valid. -/
theorem duplicate_rows_rejected :
    structurallyValid (obligations ++ obligations) = false := by decide

theorem unresolved_rows_not_closed (gates : List String) (gap : String) :
    Progress.isClosed gates (.unresolved gap) = false := rfl

/-- Partial evidence never gains closure from the planning selection. -/
theorem partial_evidence_is_not_closure (gates : List String)
    (claims : List CheckedClaim) (gap : String) :
    Progress.isClosed gates (.partialEvidence claims gap) = false := rfl

/-- Registry readout after the independent fixed-fragment qualification;
this readout is not the semantic proof stored in the row. -/
theorem selected_identity_qualification_closed (gates : List String) :
    (find? "FORK-ID").map (fun row => (row.hasSelectedDirection, row.isClosed gates)) =
      some (true, true) := by
  rfl

#print axioms obligation_ids_unique
#print axioms plan_structure_valid
#print axioms duplicate_rows_rejected

end Mettapedia.Languages.MeTTa.PrimeCandidates.DevelopmentPlan
