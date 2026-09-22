import Mettapedia.Languages.MeTTa.PrimeCandidates.Specification
import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent
import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedJudgmentDraft
import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedJudgmentDraftSecondPass
import Mettapedia.Languages.MeTTa.PrimeCeTTaCurrent.ScopedIdentityRetainedPresentationAudit

/-!
# Candidate studies compared with inspected CeTTa surfaces

This is the integration layer: neither the mathematical specification nor
the as-built snapshot imports the other. A comparison records what the native
API exposes, the precise Lean result relevant to it, and the still-unproved
correspondence. There is no implicit runtime-refinement edge.

The receipt model already relates accepted, decoded events to a cell-causal
invariant. That theorem is useful when testing a producer, but is not a proof
that every C execution produces such events. Likewise, canonicalization is not
formation, and an artifact digest is not executable semantics. Parallel C
development does not require a Lean emitter; any claimed qualification still
requires its stated correspondence evidence.

The earlier dated comparisons contain proposed experiments. The separately
pinned scoped-judgment draft review adds literal results from five recorded
runs, without replacing either earlier source snapshot. Neither observations
nor coverage of every decision completes the jointly qualified candidate
contract or its native handoff.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.Logic.MetaInterpretiveLearning.CumulativeTheory
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.Languages.MeTTa.PrimeComparisons

open PrimeCandidates.Specification
open PrimeCeTTaCurrent

/-- An open comparison, not a weakened conformance certificate. The remaining
relation is stated as a research task rather than a proposition with a missing
proof. A completed conformance claim must be added with its actual typed law. -/
structure OpenComparison (snapshot : InspectedSourceSnapshot) where
  decision : Decision
  observed : List (SourceObservation snapshot)
  modelEvidence : List CheckedClaim
  correspondenceToEstablish : String
  experiment : String
  recordedRuns : List ScopedJudgmentDraft.RecordedRun := []
  recordedIdentityProbes : List ScopedIdentityRetainedPresentationAudit.ObservedProbe := []

def receipts20260909 : OpenComparison inspected20260909 where
  decision := .observation
  observed := [needAPI20260909]
  modelEvidence := [
    checked "CMP-RCP-001" "accepted decoded receipts select at most one outcome per cell"
      (PrimeCandidates.CellCausalNativeRefinement.accepted_decodedProducerState_functional
        (Obs := Nat) (Eff := Nat)),
    checked "CMP-RCP-002" "subscriber event identities survive equal payloads"
      (@PrimeCandidates.NativeReceiptCorrespondence.equal_payload_distinct_ids_decode_distinct
        Nat Nat)]
  correspondenceToEstablish := "Relate native emitted receipts and their decoder to the abstract receipt model, including demand subscriptions and publication steps; the producer is not qualified by the checker theorem alone."
  experiment := "Decode observed receipts from shared and fresh demands; retain occurrence IDs. Mutate an ID, cell outcome, causal dependency and premise revision independently."

def admission20260909 : OpenComparison inspected20260909 where
  decision := .admission
  observed := [conversionAPI20260909]
  modelEvidence := (study .admission).constraints
  correspondenceToEstablish := "Identify the actual native admission relation independently, then compare it with the chosen formed fragment. Do not identify raw canonicalization with typing or assume the current runtime chooses the fragment."
  experiment := "Distinguish canonical but unformed input, formed indexed elimination, invalid conversion and incomplete checking."

def evaluation20260909 : OpenComparison inspected20260909 where
  decision := .evaluation
  observed := [needAPI20260909]
  modelEvidence := [queryFirstAssemblyEvidence,
    checked "CMP-EVAL-001" "the selected provider observation distinguishes sharing"
      PrimeCandidates.DecisionSurface.Sharing.same_value_support_different_observations]
  correspondenceToEstablish := "Compare an explicit native execution observation with the selected reference machine. The query-first bag theorem and the provider machine are different scoped models, not jointly certified native semantics."
  experiment := "Run demand, sharing, resampling and sibling-world fixtures at a declared observer before comparing cost. Keep the raw native record for finer observers."

def openComparisons20260909 : List (OpenComparison inspected20260909) :=
  [receipts20260909, admission20260909, evaluation20260909]

def identity20260910 : OpenComparison inspected20260910 where
  decision := .identity
  observed := [computedConversion20260910, mathematicalFormation20260910]
  modelEvidence := (study .identity).constraints
  correspondenceToEstablish := "Relate native telescope canonicalization and the restricted computed-conversion judgment to an explicitly selected syntax/equation interpretation. Keep native J, code equality and K/UIP policies distinct. The C replay routine validates a certificate-internal claim without a separately supplied expected claim or premise revision; these bindings require their own correspondence."
  experiment := "Proposed, unexecuted: reuse tests/prime/conformance/canonical_binders.metta and tests/support/test_prime_package_validation.c. Compare alpha-renamed telescopes, corrupted normal forms and a marked user equation. Submit a valid certificate for a different Original pair to distinguish internal replay from external claim binding. A declared equality-substitution rule or a replayed wire must not be reported as native J."

def mathematicalHost20260910 : OpenComparison inspected20260910 where
  decision := .mathematicalHost
  observed := [mathematicalFormation20260910, dependentProfiles20260910]
  modelEvidence := (study .mathematicalHost).constraints
  correspondenceToEstablish := "Give an explicit interpretation of the inspected named-telescope/declared-type surface into the qualified common host, preserving its assumptions, contexts and substitutions. Bare Type formation and canonical Pi/idx syntax do not supply the candidate's cumulative universes, native J, HOL induction or set-theory model; levelled Type expressions are currently deferred in this dispatcher."
  experiment := "Proposed, unexecuted: compare Form Type, Form (Type 1), a formed dependent telescope, an escaped binder and a canonicalizable telescope with a grounded non-type domain. Existing canonical_binders.metta and prime_02_completion_resources.metta provide source fixtures. Keep the uniform-list HOL proof and its missing-induction model control as the target meaning to relate, not as evidence already implemented by C."

def reasoning20260910 : OpenComparison inspected20260910 where
  decision := .reasoning
  observed := [judgmentOperations20260910, dependentProfiles20260910,
    inhabitantRechecking20260910, importedATPLibrary20260910,
    unitSuperposition20260910]
  modelEvidence := (study .reasoning).constraints
  correspondenceToEstablish := "Bind the actual submitted request, declared theory and revision to rechecked inhabitants or imported unit-superposition results, then qualify any native proof/operation/decision/certificate role against the same service contract. Neither these entry points nor the value-type May/Must verdicts implement all four candidate interfaces or the generated service OSLF meaning by their presence."
  experiment := "Proposed, unexecuted: reuse tests/prime/practical/atp_superposition_replay.metta for its non-ground substitution, orientation, position, cyclic-binding and forged-child controls. Recheck an imported equality-substitution proof with its actual declarations, then change a premise or requested conclusion. Contrast a producer-authored Complete bag with evaluator-certified completion and an explicit-budget incomplete result; no finite miss is a proof of uninhabitability."

def openComparisons20260910 : List (OpenComparison inspected20260910) :=
  [identity20260910, mathematicalHost20260910, reasoning20260910]

/-! ## Recorded experimental draft probes, not runtime qualification -/

private def evidenceFor (ids : List String) : List CheckedClaim :=
  claims.filter (fun claim => ids.contains claim.id)

def draftPublication : OpenComparison ScopedJudgmentDraft.experimentalSource where
  decision := .reasoning
  observed := [ScopedJudgmentDraft.publicationSource, ScopedJudgmentDraft.publicationDispatchSource]
  modelEvidence := evidenceFor ["HO-009", "HO-040", "HO-041", "HO-042", "HO-043", "OBS-030"]
  correspondenceToEstablish := "Relate a published theorem to its retained request, proof, assumptions and environment. Historical proof validity and current authorization are different consumers. The recorded loss of this data is not repaired by naming the resulting atom a theorem or attaching an unqualified revision hash."
  experiment := "Recorded: removed used premise, directly inserted known proposition and shadowed seeded name. Next compare an inspectable historical proof with a fresh-use request after each change; a coarse theorem-application view may hide the proof but must not invent its missing provenance."
  recordedRuns := ScopedJudgmentDraft.publication.runs

def draftHigherOrderBinding : OpenComparison ScopedJudgmentDraft.experimentalSource where
  decision := .mathematicalHost
  observed := [ScopedJudgmentDraft.higherOrderSource]
  modelEvidence := evidenceFor ["HOST-053", "HO-040", "HO-042", "HO-044", "HO-046"]
  correspondenceToEstablish := "Bind the actual requested quantifier instance, open witness, theory and proof grammar. Formation of a proposition is not a proof of it, and an incomplete guest proof grammar is not an impossibility theorem for a shared simple/dependent host. Native product types and a hosted proof family need their separately qualified semantic interpretations."
  experiment := "Recorded: higher-order proposition formation and submitted universal-proof controls diverge. Extend the exact admitted witness interface and compare the same uniform theorem under different qualified host routes; do not infer an impredicative-sort or kernel selection from this draft's rejection."
  recordedRuns := ScopedJudgmentDraft.higherOrderBinding.runs

def draftPrefixOwnership : OpenComparison ScopedJudgmentDraft.experimentalSource where
  decision := .evaluation
  observed := [ScopedJudgmentDraft.prefixSource]
  modelEvidence := evidenceFor ["HO-049", "HO-050", "HO-051", "HO-047"]
  correspondenceToEstablish := "Keep ordinary user definitions available independently of namespace spelling, while separately qualifying their mathematical use. Bind service ownership to the requested operation and environment, not the entire prefix. Retaining equation text alone is insufficient when its premises consult the changing rewrite relation; premise agreement and grammar preservation give an explicit sufficient contract."
  experiment := "Recorded: an ordinary unprefixed definition rewrites in both binaries; equivalent set:/lang: definitions become inert only in the overlay. Preserve ordinary and deliberately nonstandard definitions while testing mathematical meaning and old theorem reuse separately. Compare a premise-free equation with a conditional equation enabled by a new rewrite."
  recordedRuns := ScopedJudgmentDraft.prefixOwnership.runs

def baseConversionRouting : OpenComparison ScopedJudgmentDraft.optBaseSource where
  decision := .admission
  observed := [ScopedJudgmentDraft.conversionSource, ScopedJudgmentDraft.conversionKernelSource,
    ScopedJudgmentDraft.conversionRoutingSource]
  modelEvidence := evidenceFor ["ADM-001", "ADM-002", "ID-019", "HO-047"]
  correspondenceToEstablish := "Bind the service's admitted surface and expected equality judgment before interpreting a False result. The actual supported beta/eta controls pass; the annotation-bearing lambda is out of class for the inspected elaborator and reaches another equality fallback. This does not establish failure of native beta."
  experiment := "Recorded on both binaries: supported intrinsic/scoped beta and eta, a genuinely different pair, and the unsupported annotated spelling. Preserve the positive controls while separating unowned input, rejection of evidence, checked inequality and exhaustion."
  recordedRuns := ScopedJudgmentDraft.conversionRouting.runs

def baseDependentRoundtrip : OpenComparison ScopedJudgmentDraft.optBaseSource where
  decision := .mathematicalHost
  observed := [ScopedJudgmentDraft.roundtripSource]
  modelEvidence := evidenceFor ["HOST-047", "HOST-049", "ID-020"]
  correspondenceToEstablish := "Relate scope-indexed quoting and elaboration to the same admitted context and type, retaining the full level-polymorphic schema where promised. The anonymous-index dependent instance already round-trips in both binaries; that observation is not a proof for every schema or substitution."
  experiment := "Recorded: query the polymorphic declaration's instantiated type, form and check its idx-bearing quotation, compare it with the named spelling, then feed it back into formation and checking. Next vary the context and level substitution independently."
  recordedRuns := ScopedJudgmentDraft.dependentRoundtrip.runs

def experimentalComparisons20260910 :
    List (OpenComparison ScopedJudgmentDraft.experimentalSource) :=
  [draftPublication, draftHigherOrderBinding, draftPrefixOwnership]

def optProbeComparisons20260910 :
    List (OpenComparison ScopedJudgmentDraft.optBaseSource) :=
  [baseConversionRouting, baseDependentRoundtrip]

/-! ## Later source observations preserve, rather than rewrite, earlier runs -/

def draftSecondPassReuse : OpenComparison ScopedJudgmentDraftSecondPass.source where
  decision := .reasoning
  observed := [ScopedJudgmentDraftSecondPass.retainedProofs,
    ScopedJudgmentDraftSecondPass.currentDependencies, ScopedJudgmentDraftSecondPass.rawRecordUse]
  modelEvidence := evidenceFor ["HO-040", "HO-041", "HO-043", "HO-058", "HO-059"]
  correspondenceToEstablish := "Relate fresh theorem use to the actual stored proof, selected assumption scope and complete dependencies. The draft now retains those fields and rejects several stale dependencies, but pf:known and set:recheck do different work. Neither a raw theorem-shaped record nor valid proof of the same conclusion establishes the recorded derivation history."
  experiment := "Recorded on the existing binary: valid proof True, mismatched proof False, raw theorem-record use True, explicit recheck inert, stored proof empty. Next, unexecuted: vary a malformed dependency and compare duplicate names with different origins/proofs. Keep ordinary data insertion legal, and distinguish unchecked assumption use from fresh theorem replay."
  recordedRuns := ScopedJudgmentDraftSecondPass.recordedRuns

def draftSecondPassOwnership : OpenComparison ScopedJudgmentDraftSecondPass.source where
  decision := .admission
  observed := [ScopedJudgmentDraftSecondPass.operationOwnership,
    ScopedJudgmentDraftSecondPass.kernelFirstConversion, ScopedJudgmentDraftSecondPass.legacyOwnershipRepair]
  modelEvidence := evidenceFor ["HO-046", "HO-047", "HO-049", "ADM-035"]
  correspondenceToEstablish := "The draft's exact operation-name ownership and legacy binder decline remove two source-level conflations. Qualify the remaining fallback's inputs and equality meaning independently; kernel-first is not kernel-exclusive. A new namespace definition may execute without being admitted as a mathematical conversion."
  experiment := "Proposed, unexecuted: add an overlay declaration absent from the fixed proof-kernel context, then independently exhaust kernel and structural budgets. Distinguish admitted inequality, declined syntax, rejected proof and unfinished work; do not repin a changed verdict before identifying the intended judgment."

def draftLiveProgramming : OpenComparison ScopedJudgmentDraftSecondPass.source where
  decision := .evaluation
  observed := [ScopedJudgmentDraftSecondPass.livePropositionProgram,
    ScopedJudgmentDraftSecondPass.nativeMay]
  modelEvidence := evidenceFor ["ADM-020", "ADM-037", "ADM-038", "ADM-039", "ADM-040",
    "EVAL-016", "EVAL-017", "EVAL-018", "EVAL-019", "EVAL-020", "HO-054", "HO-057",
    "HO-059", "HO-061", "HOST-063", "HOST-067", "HOST-068", "HOST-069"]
  correspondenceToEstablish := "A program can construct claims and propose evidence without selecting where propositions live in every host. Branching needs evidence for the exact proposition or its scoped negation, or a qualified complete decision; a rejected submitted proof and an empty incomplete search do not justify else. A represented finite-set operation can be related by a theorem to abstract set meaning without extending kernel conversion."
  experiment := "Proposed, unexecuted: branch on a checked positive claim, a checked negation, a bad proof of a true claim, and an incomplete empty search. Give the branches distinct effects and verify that undecided cases execute neither. Compare a correct list-backed set operation with the deliberately nonstandard executable union under an explicitly stated representation relation."

def secondPassComparisons20260910 :
    List (OpenComparison ScopedJudgmentDraftSecondPass.source) :=
  [draftSecondPassReuse, draftSecondPassOwnership, draftLiveProgramming]

/-! ## Scoped proofs, retained originals and separately measured reuse -/

def scopedIdentityNamedApplication :
    OpenComparison ScopedIdentityRetainedPresentationAudit.source where
  decision := .identity
  observed := [ScopedIdentityRetainedPresentationAudit.diagnosticRouting]
  modelEvidence := evidenceFor ["ID-066", "ID-067", "ID-068", "ID-070", "ID-071", "ID-072", "ID-073"]
  correspondenceToEstablish := "Relate the same public named context, proof, motive and expected type to native conditional J application. The constructive C probe checks a conditional proof and its explicitly assumed instance while leaving direct and nested conversion unchanged. The try wrapper loses the explicit-space request; this is a routing defect, not a refutation of the native theorem or a reason to reopen scoped identity. Opaque Nat plus a local uniqueness assumption is not datatype-specific Hedberg evidence."
  experiment := "Recorded independently of expected outputs: conditional export without the premise, typed use with the premise in a separate named space, outside-context diagnostic query, and direct/nested conversion controls. Preserve the original context through optional diagnostics and keep the failure distinct from logical non-derivability."
  recordedIdentityProbes := [ScopedIdentityRetainedPresentationAudit.conditionalScope]

def scopedIdentityOriginalInspection :
    OpenComparison ScopedIdentityRetainedPresentationAudit.source where
  decision := .observation
  observed := [ScopedIdentityRetainedPresentationAudit.retainedAndLiveProofViews,
    ScopedIdentityRetainedPresentationAudit.admittedRecordCost]
  modelEvidence := evidenceFor ["ID-062", "ID-063", "ID-064", "ID-065", "ID-070", "ID-071", "ID-072"]
  correspondenceToEstablish := "Bind optional original references to the retained proof presentation and source scope, separately from live name lookup and current application. The actual HOL workload preserves an explicitly stored original while its publication name changes to a different accepted proof. This is not yet a native stable-handle or reconstruction implementation. Source-path costs and process timings do not prove allocation freedom or constant-time reuse."
  experiment := "Recorded: publish an actual implication proof, retain it in ordinary data, remove the live publication, publish a different checked proof of the same claim, inspect both and use the live theorem. Separately measure shallow/deeper retained proof sizes and plain/try requests; do not count the pinned build's zero runtime counters as zero work."
  recordedIdentityProbes := [ScopedIdentityRetainedPresentationAudit.originalInspection]

def scopedIdentityPublicationBoundary :
    OpenComparison ScopedIdentityRetainedPresentationAudit.source where
  decision := .admission
  observed := [ScopedIdentityRetainedPresentationAudit.signatureTagBypass,
    ScopedIdentityRetainedPresentationAudit.diagnosticRouting,
    ScopedIdentityRetainedPresentationAudit.admittedRecordCost]
  modelEvidence := evidenceFor ["ADM-030", "ADM-031", "ADM-032", "HO-058", "HO-059", "ID-065", "ID-070"]
  correspondenceToEstablish := "An ordinary origin tag or publicly obtainable digest must not turn inserted data into seeded authority. A diagnostic operation promised not to publish must not silently register admission either. These two failed controls do not require mandatory proof replay or a particular registry representation: the actual admission and current-use relation must be justified before choosing its optimized realization."
  experiment := "Recorded with independent controls: fresh raw theorem and axiom tags abstain; a forged signature tag establishes Falsum; a wrong digest abstains. A nonpublishing try silently grants admission to its returned assumption record before raw insertion; explicit assumption publication succeeds as intended. Keep the failed expectations, do not repin them as intended behavior."
  recordedIdentityProbes := [ScopedIdentityRetainedPresentationAudit.authorityTags,
    ScopedIdentityRetainedPresentationAudit.tryAdmission]

def scopedIdentityComparisons20260912 :
    List (OpenComparison ScopedIdentityRetainedPresentationAudit.source) :=
  [scopedIdentityNamedApplication, scopedIdentityOriginalInspection, scopedIdentityPublicationBoundary]

/-- An entry with no inspected native surface stays visible; no missing entry
is interpreted as conformance, nonimplementation or a failed requirement. -/
def decisionsWithoutInspectedComparison : List Decision :=
  decisions.filter (fun decision =>
    decision ∉ (openComparisons20260909.map OpenComparison.decision ++
      openComparisons20260910.map OpenComparison.decision))

def remainingCorrespondences : List (Decision × String) :=
  openComparisons20260909.map (fun comparison =>
    (comparison.decision, comparison.correspondenceToEstablish)) ++
  openComparisons20260910.map (fun comparison =>
    (comparison.decision, comparison.correspondenceToEstablish)) ++
  experimentalComparisons20260910.map (fun comparison =>
    (comparison.decision, comparison.correspondenceToEstablish)) ++
  optProbeComparisons20260910.map (fun comparison =>
    (comparison.decision, comparison.correspondenceToEstablish)) ++
  secondPassComparisons20260910.map (fun comparison =>
    (comparison.decision, comparison.correspondenceToEstablish)) ++
  scopedIdentityComparisons20260912.map (fun comparison =>
    (comparison.decision, comparison.correspondenceToEstablish))

#print axioms receipts20260909

end Mettapedia.Languages.MeTTa.PrimeComparisons
