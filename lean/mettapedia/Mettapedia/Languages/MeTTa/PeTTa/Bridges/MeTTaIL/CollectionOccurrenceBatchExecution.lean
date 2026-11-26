import Mettapedia.Languages.MeTTa.PeTTa.EquationEquality
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.RecursiveCollectionContinuationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionContextExecution
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch
import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceReadout

/-!
# Native chronological batches of prepared collection occurrences

The native batch retains each full occurrence and recursive allocation. Its
per-frame suffix drain realizes the proved receipt-permutation account.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax CollectionOccurrenceBatch
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval BridgeKit WireKit
open scoped ProgramQuotation

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def source : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../metta/gslt/lib/gslt_collection_occurrences.metta"
    sha256 "1a1cfbef65f6a0320ea0fa2e1a067665f14b950ea2f6fedcdc6e573839b2d352"

def library : BridgeKit.Library :=
  CollectionOccurrenceSearchExecution.SelectedNativeSource.library

theorem checked : library.check = true := CollectionOccurrenceSearchExecution.SelectedNativeSource.checked

section ProofMetadata

private local instance batchEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

/-- Direct outward calls derived from the actual batch-operation bodies. -/
def batchProofInheritedHeads : List String := ["gslt:collection-continuation:begin", "gslt:collection-continuation:run", "gslt:collection-continuation:publication",  "gslt:automata:length", "gslt:complete:drop", "gslt:automata:append"]

theorem batchProofInheritedHeads_derived :
    ((source.program.equations.flatMap (fun row => CompleteExecution.sourceLiteralHeads row.body)).filter
      (fun head => head.startsWith "gslt:" && !(source.program.equations.map (·.head)).contains head)).eraseDups =
        batchProofInheritedHeads := by decide +kernel

private def batchMetadataBase : SpaceSemantics.Program where
  equations := [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.equations[12]'(by decide +kernel),
    CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program.equations[0]'(by decide +kernel),
    CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program.equations[1]'(by decide +kernel),
    CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program.equations[3]'(by decide +kernel)]
  declarations := [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.declarations[12]'(by decide +kernel),
    CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program.declarations[0]'(by decide +kernel),
    CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program.declarations[1]'(by decide +kernel),
    CollectionOccurrenceSearchExecution.SelectedNativeSource.continuationSource.program.declarations[3]'(by decide +kernel)]

/-- Bounded source metadata; all operational conclusions retain the shared runtime. -/
def batchProofLibrary : Library := ⟨batchMetadataBase, source.program, ["gslt:occurrence-batch:"]⟩

def batchProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || batchProofLibrary.owns head || batchProofInheritedHeads.contains head

theorem batchProof_checked : batchProofLibrary.check = true := by decide +kernel

theorem batchProof_agreement :
    ProgramAgreementOn batchProofHeads batchProofLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

#print axioms batchProofInheritedHeads_derived
#print axioms batchProof_checked
#print axioms batchProof_agreement

/-- Body metadata for composition with a separately interpreted continuation source. -/
def batchBodyLibrary : Library :=
  ⟨{equations := [], declarations := []}, source.program, ["gslt:occurrence-batch:"]⟩

def batchBodyHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || head.startsWith "gslt:occurrence-batch:"

theorem batchBody_checked : batchBodyLibrary.check = true := by decide +kernel

theorem batchBody_agreement :
    ProgramAgreementOn batchBodyHeads batchBodyLibrary.runtime library.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

/-- List primitives are unchanged by the selected continuation bodies. -/
def batchPrimitiveHeads (head : String) : Bool :=
  !head.startsWith "gslt:" ||
    ["gslt:automata:length", "gslt:complete:drop", "gslt:automata:append"].contains head

theorem batchPrimitive_agreement :
    ProgramAgreementOn batchPrimitiveHeads batchProofLibrary.runtime
      RuleExecutionProgram.interpretedPremiseProgram := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

#print axioms batchBody_checked
#print axioms batchBody_agreement
#print axioms batchPrimitive_agreement

end ProofMetadata

syntax "occurrence_batch_from_lower% " "[" str,* "] " term:max : term
macro_rules
  | `(occurrence_batch_from_lower% [$names,*] $fact) =>
    `(BridgeKit.transport_call
      CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
      CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement
      (by decide +kernel) (by decide)
      (by rw [← batchPrimitive_agreement.dispatch _ (by decide +kernel)]; decide +kernel)
      (by decide) [$names,*] (by decide) (by rfl)
      (by
        intro index bounded
        simp only [List.length_cons, List.length_nil] at bounded
        rw [← batchPrimitive_agreement.demand _ index (by decide +kernel)]
        interval_cases index <;> decide +kernel)
      $fact)

def originTerm (job : CollectionOccurrenceHandoff.Job)
    (answer : RecursiveCollectionMachine.Answer) : Term :=
  .application "RecursiveCollectionOrigin"
    [ScopedRuleJobReadoutExecution.jobTerm job.origin,
      CollectionContextExecution.variantTerm job.variant,
      RecursiveCollectionExecution.answerTerm answer]

def frameTerm (frame : Frame plan bound expected sourcePattern) : Term :=
  .application "RecursiveOccurrenceFrame"
    [originTerm frame.allocation.job frame.allocation.answer,
      RecursiveCollectionContinuationExecution.frameTerm frame.allocation.request frame.state]

/-- Retain the original allocation beside the declared matching continuation. -/
def frameTermWith {matcher : GeneralPremise.MatchingExecution}
    (codec : RetainedMatchingWire.MatchingCodec matcher)
    (frame : Frame plan bound expected sourcePattern matcher) : Term :=
  .application "RecursiveOccurrenceFrame"
    [originTerm frame.allocation.job frame.allocation.answer,
      .application "RecursiveCollectionContinuation"
        [RecursiveCollectionHandoffExecution.preparedTerm frame.allocation.request.prepared,
          RetainedMatchingWire.Scheduled.stateTerm codec frame.state]]

theorem frameTermWith_ordinary (frame : Frame plan bound expected sourcePattern) :
    frameTermWith RetainedMatchingWire.ordinaryCodec frame = frameTerm frame := by
  simp only [frameTermWith, frameTerm, RecursiveCollectionContinuationExecution.frameTerm,
    RetainedMatchingWire.Scheduled.ordinary_state]

def publicationTerm (packet : Publication) : Term :=
  .application "RecursiveOccurrencePublication"
    [originTerm packet.job packet.answer,
      .application "RecursiveCollectionContinued"
        [RecursiveCollectionHandoffExecution.preparedTerm packet.prepared,
          CompleteExecution.firingTerm packet.outcome]]

/-- The selected choice carrier is retained in the complete occurrence packet. -/
def publicationTermWith {Choice : Type} (choiceTerm : Choice → Term)
    (packet : Publication Choice) : Term :=
  .application "RecursiveOccurrencePublication"
    [originTerm packet.job packet.answer,
      .application "RecursiveCollectionContinued"
        [RecursiveCollectionHandoffExecution.preparedTerm packet.prepared,
          CompleteExecution.firingTermWith choiceTerm packet.outcome]]

theorem publicationTermWith_ordinary (packet : Publication) :
    publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm packet = publicationTerm packet := by
  unfold publicationTermWith publicationTerm
  rw [CompleteExecution.firingTermWith_ordinary]

def stateTerm (batch : State plan bound expected sourcePattern) : Term :=
  .application "RecursiveOccurrenceBatch"
    [encodeList frameTerm batch.frames, encodeList publicationTerm batch.log]

private def decodeRecursiveAnswer? : Term → Option RecursiveCollectionMachine.Answer
  | .application "RecursiveCollectionAnswer" [assignment, trace] => do
      pure ⟨← ScopedRuleJobReadoutExecution.decodeAssignment? assignment,
        ← decodeList RecursiveCollectionExecution.decodeEvent? trace⟩
  | _ => none

private theorem decodeRecursiveAnswer?_answerTerm (answer : RecursiveCollectionMachine.Answer) :
    decodeRecursiveAnswer? (RecursiveCollectionExecution.answerTerm answer) = some answer := by
  rcases answer with ⟨assignment, trace⟩
  simp [RecursiveCollectionExecution.answerTerm, decodeRecursiveAnswer?, decodeList_encodeList,
    RecursiveCollectionExecution.decodeEvent?_eventTerm,
    ScopedRuleJobReadoutExecution.decodeAssignment?_assignmentTerm]

private def decodeOrdinaryAnswer? : Term → Option GeneralScopedMatchMachine.Answer
  | .application "ScopedMatcherAnswer" [assignment, trace] => do
      pure ⟨← ScopedRuleJobReadoutExecution.decodeAssignment? assignment,
        ← ScopedRuleJobReadoutExecution.decodeTrace? trace⟩
  | _ => none

private theorem decodeOrdinaryAnswer?_matcherAnswerTerm (answer : GeneralScopedMatchMachine.Answer) :
    decodeOrdinaryAnswer? (RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm answer) =
      some answer := by
  rcases answer with ⟨assignment, trace⟩
  have decodedTrace : ScopedRuleJobReadoutExecution.decodeTrace?
      (RuleInstantiationExecution.GeneralExecution.traceTerm trace) = some trace :=
    ScopedRuleJobReadoutExecution.decodeTrace?_traceTerm trace
  simp [RuleInstantiationExecution.GeneralExecution.matcherAnswerTerm, decodeOrdinaryAnswer?,
    ScopedRuleJobReadoutExecution.decodeAssignment?_assignmentTerm, decodedTrace]

private def decodePrepared? : Term → Option RecursiveCollectionHandoff.Prepared
  | .application "PreparedCollectionMatch" [source, ordinary, history] => do
      pure ⟨← InferenceCettaWire.decodePattern source, ← decodeOrdinaryAnswer? ordinary,
        ← decodeList RecursiveCollectionExecution.decodeEvent? history⟩
  | _ => none

private theorem decodePrepared?_preparedTerm (prepared : RecursiveCollectionHandoff.Prepared) :
    decodePrepared? (RecursiveCollectionHandoffExecution.preparedTerm prepared) = some prepared := by
  rcases prepared with ⟨source, ordinary, history⟩
  simp [RecursiveCollectionHandoffExecution.preparedTerm, decodePrepared?,
    decodeOrdinaryAnswer?_matcherAnswerTerm, decodeList_encodeList,
    RecursiveCollectionExecution.decodeEvent?_eventTerm]

private def decodeSiteVariant? : Term → Option CollectionSelection.SiteVariant
  | .application "CollectionSiteVariant" [original, site] => do
      pure ⟨← ScopedRuleJobReadoutExecution.decodeSite? original,
        ← ScopedRuleJobReadoutExecution.decodeSite? site⟩
  | _ => none

private theorem decodeSiteVariant?_variantTerm (variant : CollectionSelection.SiteVariant) :
    decodeSiteVariant? (CollectionContextExecution.variantTerm variant) = some variant := by
  cases variant
  simp [CollectionContextExecution.variantTerm, decodeSiteVariant?]

private def decodeOccurrenceOrigin? : Term →
    Option (CollectionOccurrenceHandoff.Job × RecursiveCollectionMachine.Answer)
  | .application "RecursiveCollectionOrigin" [original, variant, answer] => do
      let job ← ScopedRuleJobReadoutExecution.decodeJob? original
      let selected ← decodeSiteVariant? variant
      let matched ← decodeRecursiveAnswer? answer
      pure (⟨job, selected⟩, matched)
  | _ => none

private theorem decodeOccurrenceOrigin?_originTerm (job : CollectionOccurrenceHandoff.Job)
    (answer : RecursiveCollectionMachine.Answer) :
    decodeOccurrenceOrigin? (originTerm job answer) = some (job, answer) := by
  cases job
  simp [originTerm, decodeOccurrenceOrigin?, decodeSiteVariant?_variantTerm,
    decodeRecursiveAnswer?_answerTerm]

/-- Decode all retained packet fields, including both occurrence sites and allocation choices. -/
def decodePublication? : Term → Option Publication
  | .application "RecursiveOccurrencePublication"
      [origin, .application "RecursiveCollectionContinued" [prepared, outcome]] => do
      let (job, answer) ← decodeOccurrenceOrigin? origin
      pure ⟨job, answer, ← decodePrepared? prepared, ← CompleteExecution.decodeFiring? outcome⟩
  | _ => none

@[simp] theorem decodePublication?_publicationTerm (packet : Publication) :
    decodePublication? (publicationTerm packet) = some packet := by
  rcases packet with ⟨job, answer, prepared, outcome⟩
  simp [publicationTerm, decodePublication?, decodeOccurrenceOrigin?_originTerm,
    decodePrepared?_preparedTerm, CompleteExecution.decodeFiring?_firingTerm]

theorem publicationTerm_injective : Function.Injective publicationTerm := by
  intro first second same
  have decoded := congrArg decodePublication? same
  simpa only [decodePublication?_publicationTerm, Option.some.injEq] using decoded

theorem publicationList_encoding_injective : Function.Injective (encodeList publicationTerm) := by
  intro first second same
  have decode : ∀ packet, decodePublication? (publicationTerm packet) = some packet :=
    decodePublication?_publicationTerm
  have readback := congrArg (decodeList decodePublication?) same
  simpa only [decodeList_encodeList decodePublication? publicationTerm decode,
    Option.some.injEq] using readback

theorem publicationTerm_distinguishes_source_addresses (first second : Publication)
    (different : first.job.origin.site.address ≠ second.job.origin.site.address) :
    publicationTerm first ≠ publicationTerm second := by
  intro equal
  exact different (congrArg (fun packet : Publication => packet.job.origin.site.address)
    (publicationTerm_injective equal))

theorem decodePublication?_wrong_constructor : decodePublication? (.application "RuleReceipt" []) = none := rfl


/-- Read the original occurrence, allocation, prepared match and full conditional outcome. -/
def decodePublicationWith? {Choice : Type} (decodeChoice : Term → Option Choice) :
    Term → Option (Publication Choice)
  | .application "RecursiveOccurrencePublication"
      [origin, .application "RecursiveCollectionContinued" [prepared, outcome]] => do
      let (job, answer) ← decodeOccurrenceOrigin? origin
      pure ⟨job, answer, ← decodePrepared? prepared,
        ← CompleteExecution.decodeFiringWith? decodeChoice outcome⟩
  | _ => none

@[simp] theorem decodePublicationWith?_publicationTermWith {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (packet : Publication Choice) :
    decodePublicationWith? decodeChoice (publicationTermWith choiceTerm packet) = some packet := by
  rcases packet with ⟨job, answer, prepared, outcome⟩
  simp [publicationTermWith, decodePublicationWith?, decodeOccurrenceOrigin?_originTerm,
    decodePrepared?_preparedTerm,
    CompleteExecution.decodeFiringWith?_firingTermWith choiceTerm decodeChoice inverse]

theorem publicationTermWith_injective {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice) :
    Function.Injective (publicationTermWith choiceTerm) := by
  intro first second same
  have decoded := congrArg (decodePublicationWith? decodeChoice) same
  simpa only [decodePublicationWith?_publicationTermWith choiceTerm decodeChoice inverse,
    Option.some.injEq] using decoded

theorem publicationListWith_encoding_injective {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice) :
    Function.Injective (encodeList (publicationTermWith choiceTerm)) := by
  intro first second same
  have decoded := congrArg (decodeList (decodePublicationWith? decodeChoice)) same
  simpa only [decodeList_encodeList (decodePublicationWith? decodeChoice)
    (publicationTermWith choiceTerm) (decodePublicationWith?_publicationTermWith choiceTerm decodeChoice inverse),
    Option.some.injEq] using decoded

theorem publicationTermWith_distinguishes_source_addresses {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (first second : Publication Choice)
    (different : first.job.origin.site.address ≠ second.job.origin.site.address) :
    publicationTermWith choiceTerm first ≠ publicationTermWith choiceTerm second := by
  intro same
  exact different (congrArg (fun packet : Publication Choice => packet.job.origin.site.address)
    (publicationTermWith_injective choiceTerm decodeChoice inverse same))

theorem decodePublicationWith?_wrong_constructor {Choice : Type} (decodeChoice : Term → Option Choice) :
    decodePublicationWith? decodeChoice (.application "RuleReceipt" []) = none := rfl

#print axioms publicationTermWith_ordinary
#print axioms decodePublicationWith?_publicationTermWith
#print axioms publicationTermWith_injective
#print axioms publicationListWith_encoding_injective
#print axioms publicationTermWith_distinguishes_source_addresses
#print axioms decodePublicationWith?_wrong_constructor

/-- Wire readback preserves the full publication and its associated receipt. -/
def committedTermWith {Choice : Type} (choiceTerm : Choice → Term)
    (committed : CollectionCommittedObservation.Committed Choice) : Term :=
  .application "CommittedOccurrence"
    [publicationTermWith choiceTerm committed.1,
      ScopedRuleJobReadoutExecution.receiptTermWith choiceTerm committed.2]

def decodeCommittedWith? {Choice : Type} (decodeChoice : Term → Option Choice) :
    Term → Option (CollectionCommittedObservation.Committed Choice)
  | .application "CommittedOccurrence" [publication, receipt] => do
      pure (← decodePublicationWith? decodeChoice publication,
        ← ScopedRuleJobReadoutExecution.decodeReceiptWith? decodeChoice receipt)
  | _ => none

@[simp] theorem decodeCommittedWith?_committedTermWith {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice)
    (committed : CollectionCommittedObservation.Committed Choice) :
    decodeCommittedWith? decodeChoice (committedTermWith choiceTerm committed) = some committed := by
  rcases committed with ⟨publication, receipt⟩
  simp [committedTermWith, decodeCommittedWith?,
    decodePublicationWith?_publicationTermWith choiceTerm decodeChoice inverse,
    ScopedRuleJobReadoutExecution.decodeReceiptWith?_receiptTermWith choiceTerm decodeChoice inverse]

theorem committedTermWith_injective {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice) :
    Function.Injective (committedTermWith choiceTerm) := by
  intro first second same
  have decoded := congrArg (decodeCommittedWith? decodeChoice) same
  simpa only [decodeCommittedWith?_committedTermWith choiceTerm decodeChoice inverse,
    Option.some.injEq] using decoded

theorem committedListWith_encoding_injective {Choice : Type}
    (choiceTerm : Choice → Term) (decodeChoice : Term → Option Choice)
    (inverse : ∀ choice, decodeChoice (choiceTerm choice) = some choice) :
    Function.Injective (encodeList (committedTermWith choiceTerm)) := by
  intro first second same
  have decoded := congrArg (decodeList (decodeCommittedWith? decodeChoice)) same
  simpa only [decodeList_encodeList (decodeCommittedWith? decodeChoice)
    (committedTermWith choiceTerm) (decodeCommittedWith?_committedTermWith choiceTerm decodeChoice inverse),
    Option.some.injEq] using decoded

theorem decodeCommittedWith?_wrong_constructor {Choice : Type} (decodeChoice : Term → Option Choice) :
    decodeCommittedWith? decodeChoice (.application "RecursiveOccurrencePublication" []) = none := rfl

#print axioms decodeCommittedWith?_committedTermWith
#print axioms committedTermWith_injective
#print axioms committedListWith_encoding_injective
#print axioms decodeCommittedWith?_wrong_constructor


syntax "occurrence_batch_eval" (" [" term,* "]")?
    (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| occurrence_batch_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in batchProof_checked using batchProof_agreement; metta_eval [$facts,*] with batchProof_checked in batchProof_agreement
      unfolding [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        frameTerm, publicationTerm, stateTerm, CettaWireAtom.encode, CettaWireAtom.encodeMany,
        $extra,*]))

/-- The existing initializer wraps the actual seeded continuation. It preserves the
original allocation and accepts no completed premise outcome. -/
theorem frame_begin_with_returns {matcher : GeneralPremise.MatchingExecution}
    (program : SpaceSemantics.Program)
    (agreement : ProgramAgreementOn batchBodyHeads batchBodyLibrary.runtime program)
    (host : Effects.State) (environmentWire : Term)
    (codec : RetainedMatchingWire.MatchingCodec matcher)
    (profile : SeedProfile matcher plan bound expected sourcePattern)
    (allocation : Allocation plan bound expected sourcePattern)
    (dispatch : (ioHead "gslt:collection-continuation:begin" ||
      StdLib.known "gslt:collection-continuation:begin" ||
      program.equations.any (·.head == "gslt:collection-continuation:begin")) = true)
    (raw : ∀ index < 8, argumentIsRaw program "gslt:collection-continuation:begin" index = true)
    (begun : PureReturns program [] host
      (apply "gslt:collection-continuation:begin"
        [encoded environmentWire, number allocation.request.depth,
          encoded (CompleteExecution.DescentCodec.typesTerm allocation.request.bound),
          encoded (CompleteExecution.DescentCodec.typeTerm allocation.request.type),
          number allocation.request.index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm allocation.request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm allocation.request.spec),
          encoded (RecursiveCollectionHandoffExecution.preparedTerm allocation.request.prepared)])
      host (encoded (.application "RecursiveCollectionContinuation"
        [RecursiveCollectionHandoffExecution.preparedTerm allocation.request.prepared,
          RetainedMatchingWire.Scheduled.stateTerm codec (Frame.initialWith profile allocation).state]))) :
    PureReturns program [] host
      (apply "gslt:occurrence-batch:frame-begin"
        [encoded (originTerm allocation.job allocation.answer), encoded environmentWire,
          number allocation.request.depth,
          encoded (CompleteExecution.DescentCodec.typesTerm allocation.request.bound),
          encoded (CompleteExecution.DescentCodec.typeTerm allocation.request.type),
          number allocation.request.index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm allocation.request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm allocation.request.spec),
          encoded (RecursiveCollectionHandoffExecution.preparedTerm allocation.request.prepared)])
      host (encoded (frameTermWith codec (Frame.initialWith profile allocation))) := by
  metta_call_in batchBody_checked using agreement
  apply pure_let_returns _ _ _ _ _ _ _ _ (by rfl)
  · refine PureData.raw_capture_returns program [] _ host host
      "gslt:collection-continuation:begin" _ _ _ dispatch ?_ (by decide) ?_ begun
    · intro index bounded
      exact raw index (by simpa only [List.length_cons, List.length_nil] using bounded)
    · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind,
        CettaWireAtom.applySubst_encode, encoded, number, List.find?]
  · metta_eval with batchBody_checked in agreement unfolding
      [frameTermWith, Frame.initialWith, Library.bind,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        CettaWireAtom.encode, CettaWireAtom.encodeMany]

private theorem continuation_begin_dispatch :
    (ioHead "gslt:collection-continuation:begin" ||
      StdLib.known "gslt:collection-continuation:begin" ||
      library.runtime.equations.any (·.head == "gslt:collection-continuation:begin")) = true := by
  rw [← batchProof_agreement.dispatch "gslt:collection-continuation:begin" (by decide +kernel)]
  decide +kernel

private theorem continuation_begin_raw :
    ∀ index < 8, argumentIsRaw library.runtime "gslt:collection-continuation:begin" index = true := by
  intro index bounded
  rw [← batchProof_agreement.demand "gslt:collection-continuation:begin" index (by decide +kernel)]
  interval_cases index <;> decide +kernel

#print axioms frame_begin_with_returns
#print axioms continuation_begin_dispatch
#print axioms continuation_begin_raw

def FrameReady (footprint : List String) (frame : Frame plan bound expected sourcePattern) : Prop :=
  StructuralDescent.Scheduled.stateFreeWithin footprint frame.allocation.request.environment
    frame.allocation.request.goal frame.state

theorem run_ready (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (frame : Frame plan bound expected sourcePattern) (work : Nat)
    (covered : FrameReady footprint frame) : FrameReady footprint (Frame.run work frame) := by
  have same := frame.allocation.request_origin.1
  have rows := GeneralPremise.provider_coverage_mono _ footprint
    frame.allocation.request.environment.provider (by simpa only [same] using provider)
    (GeneralPremise.provider_covered_by_own_names frame.allocation.request.environment.provider)
  have dynamic := GeneralPremise.Query.DynamicOutputsFreeWithin.of_unregistered footprint
    frame.allocation.request.environment (by simpa only [same] using finite)
  exact StructuralDescent.Scheduled.run_free_within Mettapedia.OSLF.MeTTaIL.GeneralPremise.MatchingExecution.ordinary_preservesFreeNames footprint frame.allocation.request.environment
    _ rows dynamic work frame.state covered

@[metta_head "gslt:occurrence-batch:frame-begin"]
theorem frame_begin_returns (host : Effects.State)
    (allocation : Allocation plan bound expected sourcePattern) (footprint : List String)
    (inside : ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ footprint) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:frame-begin"
        [encoded (originTerm allocation.job allocation.answer),
          CompleteExecution.environmentValue allocation.request.environment
            (allocation.request.environment.free.entriesOn footprint),
          number allocation.request.depth,
          encoded (CompleteExecution.DescentCodec.typesTerm allocation.request.bound),
          encoded (CompleteExecution.DescentCodec.typeTerm allocation.request.type),
          number allocation.request.index,
          encoded (InferenceCettaWire.AuthoredRule.rewriteTerm allocation.request.rule),
          encoded (InferenceCettaWire.AuthoredRule.bindingSpecTerm allocation.request.spec),
          encoded (RecursiveCollectionHandoffExecution.preparedTerm allocation.request.prepared)])
      host (encoded (frameTerm (Frame.initial allocation))) := by
  have begun := RecursiveCollectionContinuationExecution.begin_returns host allocation.request footprint inside
  have initialized := frame_begin_with_returns library.runtime batchBody_agreement host
    (PremiseOperationsExecution.GeneralExecution.environmentTerm allocation.request.environment
      (allocation.request.environment.free.entriesOn footprint))
    RetainedMatchingWire.ordinaryCodec (ordinarySeedProfile plan bound expected sourcePattern)
    allocation continuation_begin_dispatch continuation_begin_raw (by
      simpa only [Frame.initialWith_ordinary, Frame.initial,
        RetainedMatchingWire.Scheduled.ordinary_state, RecursiveCollectionContinuationExecution.frameTerm,
        library, RecursiveCollectionContinuationExecution.library,
        RetainedMatchingWire.interpreted_runtime, CompleteExecution.environmentValue] using begun)
  rw [Frame.initialWith_ordinary, frameTermWith_ordinary] at initialized
  exact initialized

@[metta_head "gslt:occurrence-batch:frame-run"]
theorem frame_run_returns (host : Effects.State) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (frame : Frame plan bound expected sourcePattern) (work : Nat)
    (covered : FrameReady footprint frame) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:frame-run"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (frameTerm frame)])
      host (encoded (frameTerm (Frame.run work frame))) := by
  have same := frame.allocation.request_origin.1
  have native := RecursiveCollectionContinuationExecution.run_returns host frame.allocation.request
    footprint (by simpa only [same] using finite) (by simpa only [same] using provider)
    frame.state work covered
  have advanced := native
  simp only [same] at advanced
  occurrence_batch_eval [advanced] unfolding [Frame.run]

@[metta_head "gslt:occurrence-batch:tag"]
theorem tag_returns (host : Effects.State) (allocation : Allocation plan bound expected sourcePattern) :
    ∀ packets : List Complete.DeepRoot.Firing,
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:tag"
        [encoded (originTerm allocation.job allocation.answer),
          encoded (encodeList (RecursiveCollectionContinuationExecution.publicationTerm allocation.request) packets)])
      host (encoded (encodeList publicationTerm (packets.map (tag allocation))))
  | [] => by occurrence_batch_eval
  | packet :: packets => by
    have later := tag_returns host allocation packets
    have same := allocation.request_origin.2
    occurrence_batch_eval [later] unfolding
      [tag, RecursiveCollectionContinuationExecution.publicationTerm, same]

@[metta_head "gslt:occurrence-batch:frame-publication"]
theorem frame_publication_returns (host : Effects.State)
    (frame : Frame plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:frame-publication" [encoded (frameTerm frame)])
      host (encoded (encodeList publicationTerm frame.publication)) := by
  have native := RecursiveCollectionContinuationExecution.publication_returns host
    frame.allocation.request frame.state
  have published := native
  have tagged := tag_returns host frame.allocation
    (RecursiveCollectionContinuation.publication frame.allocation.request frame.state)
  simp only [Frame.publication, RecursiveCollectionContinuation.publicationIn_ordinary]
  occurrence_batch_eval [published, tagged]

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State) (left right : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:append" [encoded (encodeList encoder left), encoded (encodeList encoder right)]) host (encoded (encodeList encoder (left ++ right))) := by
  exact occurrence_batch_from_lower% ["left", "right"]
    (CollectionSelectionExecution.scoped_append_returns encoder host left right)

private theorem length_returns {α : Type} (encoder : α → Term) (host : Effects.State) (items : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:automata:length" [encoded (encodeList encoder items)]) host (number items.length) := by
  exact occurrence_batch_from_lower% ["items"]
    (CollectionSelectionExecution.scoped_length_returns encoder host items)

private theorem drop_returns {α : Type} (encoder : α → Term) (host : Effects.State) (count : Nat) (items : List α) :
    PureReturns library.runtime [] host
      (apply "gslt:complete:drop" [number count, encoded (encodeList encoder items)]) host (encoded (encodeList encoder (items.drop count))) := by
  have mapped (values : List α) : encoded (encodeList encoder values) =
      CompleteExecution.terms (values.map encoder) := by
    simp only [CompleteExecution.terms, CettaWire.encodeList_map, Function.id_comp]
  rw [mapped, mapped, List.map_drop]
  exact occurrence_batch_from_lower% ["count", "items"]
    (CompleteExecution.drop_returns host count (items.map encoder))

def advancedFramesTerm (frames : List (Frame plan bound expected sourcePattern)) : Term :=
  .application "RecursiveOccurrenceAdvanced"
    [encodeList frameTerm (frames.map (Frame.run 1)),
      encodeList publicationTerm (frames.flatMap Frame.fresh)]

@[metta_head "gslt:occurrence-batch:advance-frames"]
theorem advance_frames_returns (host : Effects.State) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) :
    ∀ frames : List (Frame plan bound expected sourcePattern),
    (∀ frame ∈ frames, FrameReady footprint frame) →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:advance-frames"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          encoded (encodeList frameTerm frames)])
      host (encoded (advancedFramesTerm frames))
  | [], _ => by occurrence_batch_eval unfolding [advancedFramesTerm]
  | frame :: frames, covered => by
    have previous := frame_publication_returns host frame
    have count := length_returns publicationTerm host frame.publication
    have advanced := frame_run_returns host footprint finite provider frame 1
      (covered frame List.mem_cons_self)
    have published := frame_publication_returns host (Frame.run 1 frame)
    have fresh := drop_returns publicationTerm host frame.publication.length
      (Frame.run 1 frame).publication
    have later := advance_frames_returns host footprint finite provider frames
      (fun child member => covered child (List.mem_cons_of_mem _ member))
    have joined := append_returns publicationTerm host frame.fresh (frames.flatMap Frame.fresh)
    simp only [advancedFramesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at later
    occurrence_batch_eval [previous, count, advanced, published, fresh, later, joined]
      unfolding [advancedFramesTerm, Frame.fresh, List.flatMap_cons]

@[metta_head "gslt:occurrence-batch:begin"]
theorem begin_returns (host : Effects.State)
    (allocations : List (Allocation plan bound expected sourcePattern)) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:begin" [encoded (encodeList frameTerm (allocations.map Frame.initial))])
      host (encoded (stateTerm (State.begin allocations))) := by
  occurrence_batch_eval unfolding [State.begin]

def StateReady (footprint : List String) (batch : State plan bound expected sourcePattern) : Prop :=
  ∀ frame ∈ batch.frames, FrameReady footprint frame

theorem round_ready (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (batch : State plan bound expected sourcePattern)
    (covered : StateReady footprint batch) : StateReady footprint batch.round := by
  intro frame member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact run_ready footprint finite provider original 1 (covered original present)

@[metta_head "gslt:occurrence-batch:resume"]
theorem resume_returns (host : Effects.State) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) :
    ∀ (work : Nat) (batch : State plan bound expected sourcePattern), StateReady footprint batch →
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:resume"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (encodeList frameTerm batch.frames), encoded (encodeList publicationTerm batch.log)])
      host (encoded (stateTerm (State.run work batch)))
  | 0, batch, _ => by occurrence_batch_eval unfolding [State.run]
  | work + 1, batch, covered => by
    have advanced := advance_frames_returns host footprint finite provider batch.frames covered
    have joined := append_returns publicationTerm host batch.log (batch.frames.flatMap Frame.fresh)
    have later := resume_returns host footprint finite provider work batch.round
      (round_ready footprint finite provider batch covered)
    simp only [advancedFramesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at advanced
    occurrence_batch_eval [advanced, joined, later] unfolding [State.run, State.round]

@[metta_head "gslt:occurrence-batch:run"]
theorem run_returns (host : Effects.State) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ GeneralPremise.providerFreeNames (GeneralPlanEnvironment.environment plan).provider,
      name ∈ footprint) (work : Nat) (batch : State plan bound expected sourcePattern)
    (covered : StateReady footprint batch) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:run"
        [CompleteExecution.environmentValue (GeneralPlanEnvironment.environment plan)
          ((GeneralPlanEnvironment.environment plan).free.entriesOn footprint),
          number work, encoded (stateTerm batch)])
      host (encoded (stateTerm (State.run work batch))) := by
  have native := resume_returns host footprint finite provider work batch covered
  occurrence_batch_eval [native]

@[metta_head "gslt:occurrence-batch:publication"]
theorem publication_returns (host : Effects.State) (batch : State plan bound expected sourcePattern) :
    PureReturns library.runtime [] host
      (apply "gslt:occurrence-batch:publication" [encoded (stateTerm batch)])
      host (encoded (encodeList publicationTerm batch.log)) := by
  occurrence_batch_eval

#print axioms decodePublication?_publicationTerm
#print axioms publicationTerm_injective
#print axioms publicationList_encoding_injective
#print axioms publicationTerm_distinguishes_source_addresses
#print axioms decodePublication?_wrong_constructor


#print axioms frameTermWith_ordinary
#print axioms frame_begin_returns
#print axioms frame_run_returns
#print axioms tag_returns
#print axioms frame_publication_returns
#print axioms append_returns
#print axioms length_returns
#print axioms drop_returns
#print axioms advance_frames_returns
#print axioms begin_returns
#print axioms round_ready
#print axioms resume_returns
#print axioms run_returns
#print axioms publication_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution.Canonical
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise CollectionOccurrenceBatch RecursiveCollectionHandoff CanonicalCompare
open CanonicalCompare.AllNameSupport
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics Eval BridgeKit WireKit

private local instance loopEquationEq : DecidableEq SpaceSemantics.Equation :=
  SpaceSemantics.Equation.decideEq

def loopHeads (head : String) : Bool := !head.startsWith "gslt:" || head.startsWith "gslt:occurrence-batch:" ||
  ["gslt:collection-continuation:run", "gslt:collection-continuation:publication",
    "gslt:automata:length", "gslt:complete:drop", "gslt:automata:append"].contains head

theorem loop_agreement : ProgramAgreementOn loopHeads CollectionOccurrenceBatchExecution.batchProofLibrary.runtime
    CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime := by
  apply programAgreementOn_of_retained_rows
  · decide +kernel
  · decide +kernel

/-- Finite wire-name requirements, all constructed from the declared environment and input. -/
structure Config (plan : GeneralExecutionAdmission.Plan) where
  names : List String
  footprint : List String
  ordered : NameOrdered names
  declarations : ∀ rule ∈ (GeneralPlanEnvironment.environment plan).language.terms, rule.label ∈ names
  included : ∀ name ∈ footprint, name ∈ names
  provider : ∀ name ∈ providerFreeNames (GeneralPlanEnvironment.environment plan).provider, name ∈ footprint
  unregistered : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []
  templates : ∀ rule ∈ (GeneralPlanEnvironment.environment plan).language.rewrites, ∀ premise ∈ rule.premises,
    StructuralDescent.Scheduled.NameSupport.PremiseCovered names premise
  specifications : ∀ entry ∈ (GeneralPlanEnvironment.environment plan).specifications,
    SpecificationCovered names entry.2

/-- The name table covers the explicit free projection, environment templates and additional source names. -/
def Config.forFootprint (plan : GeneralExecutionAdmission.Plan) (footprint : List String)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = [])
    (provider : ∀ name ∈ providerFreeNames (GeneralPlanEnvironment.environment plan).provider, name ∈ footprint)
    (extraNames : List String := []) : Config plan :=
  let environment := GeneralPlanEnvironment.environment plan
  let alphabet := extraNames ++ footprint
  { names := StructuralDescent.Scheduled.NameSupport.environmentNameTable environment alphabet,
    footprint,
    ordered := StructuralDescent.Scheduled.NameSupport.environment_table_ordered environment alphabet,
    declarations := StructuralDescent.Scheduled.NameSupport.environment_table_declarations environment alphabet,
    included := fun name member => StructuralDescent.Scheduled.NameSupport.environment_table_footprint
      environment alphabet name (List.mem_append_right _ member),
    provider,
    unregistered := finite,
    templates := StructuralDescent.Scheduled.NameSupport.environment_table_templates environment alphabet,
    specifications := StructuralDescent.Scheduled.NameSupport.environment_table_specifications environment alphabet }

def Config.forSource (plan : GeneralExecutionAdmission.Plan) (source : Pattern)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []) : Config plan :=
  Config.forFootprint plan
    (source.freeFvarNames ++ providerFreeNames (GeneralPlanEnvironment.environment plan).provider)
    finite (fun _ member => List.mem_append_right _ member)

theorem Config.forSource_eq_forFootprint (plan : GeneralExecutionAdmission.Plan) (source : Pattern)
    (finite : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []) :
    Config.forSource plan source finite = Config.forFootprint plan
      (source.freeFvarNames ++ providerFreeNames (GeneralPlanEnvironment.environment plan).provider)
      finite (fun _ member => List.mem_append_right _ member) := rfl


variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr} {expected : TypeExpr} {sourcePattern : Pattern}
local notation "CFrame" => Frame plan bound expected sourcePattern canonicalMatchingExecution
local notation "CState" => State plan bound expected sourcePattern canonicalMatchingExecution

def environmentTerm (config : Config plan) : Term :=
  RetainedMatchingWire.interpretedEnvironmentTerm config.names
    (PremiseOperationsExecution.GeneralExecution.environmentTerm (GeneralPlanEnvironment.environment plan)
      ((GeneralPlanEnvironment.environment plan).free.entriesOn config.footprint))

def frameTerm (frame : CFrame) : Term := frameTermWith RetainedMatchingWire.canonicalCodec frame
def publicationTerm (packet : Publication canonicalMatchingExecution.Choice) : Term :=
  publicationTermWith RecursiveCollectionExecution.eventTerm packet

def stateTerm (batch : CState) : Term :=
  .application "RecursiveOccurrenceBatch" [encodeList frameTerm batch.frames, encodeList publicationTerm batch.log]

def FrameReady (config : Config plan) (frame : CFrame) : Prop :=
  StructuralDescent.Scheduled.stateFreeWithin config.footprint frame.allocation.request.environment
    frame.allocation.request.goal frame.state ∧
  StructuralDescent.Scheduled.NameSupport.StateCovered (table := config.names)
    frame.allocation.request.environment frame.allocation.request.goal frame.state

theorem initial_ready (config : Config plan)
    (allocation : Allocation plan bound expected (CanonicalBags.canon sourcePattern))
    (inside : ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ config.footprint) :
    FrameReady config (Frame.initialCanonical allocation) := by
  have same := allocation.request_origin.1
  constructor
  · exact RecursiveCollectionContinuation.Canonical.start_free_within _ allocation.canonical_seed config.footprint inside
  · apply RecursiveCollectionContinuation.Canonical.start_names_covered _ allocation.canonical_seed config.names config.footprint
    · simpa only [same] using config.declarations
    · exact config.included
    · simpa only [same] using config.templates
    · simpa only [same] using config.specifications
    · exact inside

theorem run_ready (config : Config plan) (frame : CFrame) (work : Nat) (ready : FrameReady config frame) :
    FrameReady config (Frame.run work frame) := by
  have same := frame.allocation.request_origin.1
  have provider : ∀ name ∈ providerFreeNames frame.allocation.request.environment.provider, name ∈ config.footprint := by
    simpa only [same] using config.provider
  have rows := provider_coverage_mono _ config.footprint frame.allocation.request.environment.provider provider
    (provider_covered_by_own_names frame.allocation.request.environment.provider)
  have dynamic := Query.DynamicOutputsFreeWithin.of_unregistered config.footprint frame.allocation.request.environment
    (by simpa only [same] using config.unregistered)
  constructor
  · exact StructuralDescent.Scheduled.run_free_within canonical_preservesFreeNames _ _ _ rows dynamic work frame.state ready.1
  · exact StructuralDescent.Scheduled.NameSupport.run_covered MatchingExecution.canonical_preservesNames
      canonical_preservesFreeNames _ _ (by simpa only [same] using config.declarations) config.included rows dynamic
      (by simpa only [same] using config.templates) (by simpa only [same] using config.specifications)
      work frame.state ready.1 ready.2

private theorem matchValue_variable (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (name : String) (value : Atom) :
    matchValue bindings (.var name) value =
      Mettapedia.Languages.ProcessCalculi.MORK.matchAtom bindings (.var name) value := by
  cases value <;> simp only [matchValue]

syntax "canonical_batch_eval" (" [" term,* "]")? (" unfolding" " [" term,* "]")? : tactic
macro_rules
  | `(tactic| canonical_batch_eval $[[$facts,*]]? $[unfolding [$extra,*]]?) => do
    let facts := (facts.map (·.getElems)).getD #[]
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (metta_call_in CollectionOccurrenceBatchExecution.batchProof_checked using loop_agreement; metta_eval [$facts,*] with CollectionOccurrenceBatchExecution.batchProof_checked in loop_agreement unfolding
      [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
        Mettapedia.Languages.ProcessCalculi.MORK.applySubst.applySubstList,
        Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, List.find?,
        frameTerm, frameTermWith, publicationTerm, publicationTermWith, stateTerm,
        CettaWireAtom.encode, CettaWireAtom.encodeMany, matchValue_variable, $extra,*]))

theorem frame_run_returns (host : Effects.State) (config : Config plan)
    (frame : CFrame) (work : Nat) (ready : FrameReady config frame) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:frame-run" [encoded (environmentTerm config), number work, encoded (frameTerm frame)])
      host (encoded (frameTerm (Frame.run work frame))) := by
  have same := frame.allocation.request_origin.1
  have native := RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.run_returns host
    frame.allocation.request config.names config.ordered config.footprint
    (by simpa only [same] using config.declarations) config.included
    (by simpa only [same] using config.provider) (by simpa only [same] using config.unregistered)
    (by simpa only [same] using config.templates) (by simpa only [same] using config.specifications)
    frame.state work ready.1 ready.2
  simp only [RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.frameTermWith,
    RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.environmentTerm, same] at native
  canonical_batch_eval [native] unfolding [Frame.run, RecursiveCollectionContinuation.Canonical.run, environmentTerm]

theorem tag_returns (host : Effects.State) (allocation : Allocation plan bound expected sourcePattern) :
    ∀ packets : List RecursiveCollectionContinuation.Canonical.Firing,
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:tag" [encoded (originTerm allocation.job allocation.answer),
        encoded (encodeList (RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.publicationTermWith
          RetainedMatchingWire.canonicalCodec allocation.request) packets)]) host
      (encoded (encodeList publicationTerm (packets.map (tag allocation))))
  | [] => by canonical_batch_eval
  | packet :: packets => by
    have later := tag_returns host allocation packets
    have same := allocation.request_origin.2
    canonical_batch_eval [later] unfolding
      [CollectionOccurrenceBatch.tag,
        RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.publicationTermWith,
        RetainedMatchingWire.canonicalCodec, same]

theorem frame_publication_returns (host : Effects.State) (frame : CFrame) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:frame-publication" [encoded (frameTerm frame)]) host
      (encoded (encodeList publicationTerm frame.publication)) := by
  have native := RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.publication_returns host
    frame.allocation.request RetainedMatchingWire.canonicalCodec frame.state
  simp only [RecursiveCollectionContinuationExecution.Canonical.SelectedPostmatch.frameTermWith] at native
  have tagged := tag_returns host frame.allocation (RecursiveCollectionContinuation.Canonical.publication frame.allocation.request frame.state)
  simp only [Frame.publication, RecursiveCollectionContinuation.Canonical.publicationIn_canonical]
  canonical_batch_eval [native,tagged]

private theorem raw_metadata_agreement : ProgramAgreementOn batchPrimitiveHeads batchProofLibrary.runtime
    RuleExecutionProgram.interpretedPremiseProgram := by
  exact batchPrimitive_agreement

private theorem append_returns {α : Type} (encoder : α → Term) (host : Effects.State) (left right : List α) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:automata:append" [encoded (encodeList encoder left), encoded (encodeList encoder right)]) host
      (encoded (encodeList encoder (left ++ right))) := by
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← raw_metadata_agreement.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["left", "right"] (by decide) (by rfl)
    (by intro index bounded; have small : index < 2 := by simpa using bounded
        rw [← raw_metadata_agreement.demand _ index (by decide +kernel)]; interval_cases index <;> decide +kernel)
  simpa only [CollectionSelectionExecution.scopedLibrary, RetainedMatchingWire.interpreted_runtime] using
    CollectionSelectionExecution.scoped_append_returns encoder host left right

private theorem length_returns {α : Type} (encoder : α → Term) (host : Effects.State) (items : List α) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:automata:length" [encoded (encodeList encoder items)]) host (number items.length) := by
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← raw_metadata_agreement.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["items"] (by decide) (by rfl)
    (by intro index bounded; have small : index = 0 := by simpa using bounded
        subst index; rw [← raw_metadata_agreement.demand _ 0 (by decide +kernel)]; decide +kernel)
  simpa only [CollectionSelectionExecution.scopedLibrary, RetainedMatchingWire.interpreted_runtime] using
    CollectionSelectionExecution.scoped_length_returns encoder host items

private theorem drop_returns {α : Type} (encoder : α → Term) (host : Effects.State) (count : Nat) (items : List α) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:complete:drop" [number count, encoded (encodeList encoder items)]) host
      (encoded (encodeList encoder (items.drop count))) := by
  have mapped (values : List α) : encoded (encodeList encoder values) = CompleteExecution.terms (values.map encoder) := by
    simp only [CompleteExecution.terms, CettaWire.encodeList_map, Function.id_comp]
  rw [mapped, mapped, List.map_drop]
  apply transport_call CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_closed
    CollectionOccurrenceSearchExecution.SelectedNativeSource.lower_agreement (by decide +kernel) (by decide)
    (by rw [← raw_metadata_agreement.dispatch _ (by decide +kernel)]; decide +kernel) (by decide)
    ["count", "items"] (by decide) (by rfl)
    (by intro index bounded; have small : index < 2 := by simpa using bounded
        rw [← raw_metadata_agreement.demand _ index (by decide +kernel)]; interval_cases index <;> decide +kernel)
  simpa only [CompleteExecution.runtime, CompleteExecution.completeLibrary, RetainedMatchingWire.interpreted_runtime] using
    CompleteExecution.drop_returns host count (items.map encoder)

def advancedFramesTerm (frames : List CFrame) : Term :=
  .application "RecursiveOccurrenceAdvanced" [encodeList frameTerm (frames.map (Frame.run 1)),
    encodeList publicationTerm (frames.flatMap Frame.fresh)]

theorem advance_frames_returns (host : Effects.State) (config : Config plan) :
    ∀ frames : List CFrame, (∀ frame ∈ frames, FrameReady config frame) →
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:advance-frames" [encoded (environmentTerm config), encoded (encodeList frameTerm frames)]) host
      (encoded (advancedFramesTerm frames))
  | [], _ => by canonical_batch_eval unfolding [advancedFramesTerm]
  | frame :: frames, ready => by
    have previous := frame_publication_returns host frame
    have count := length_returns publicationTerm host frame.publication
    have advanced := frame_run_returns host config frame 1 (ready frame List.mem_cons_self)
    have published := frame_publication_returns host (Frame.run 1 frame)
    have fresh := drop_returns publicationTerm host frame.publication.length (Frame.run 1 frame).publication
    have later := advance_frames_returns host config frames (fun child member => ready child (List.mem_cons_of_mem _ member))
    have joined := append_returns publicationTerm host frame.fresh (frames.flatMap Frame.fresh)
    simp only [advancedFramesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at later
    canonical_batch_eval [previous,count,advanced,published,fresh,later,joined]
      unfolding [advancedFramesTerm,Frame.fresh,List.flatMap_cons]

def StateReady (config : Config plan) (batch : CState) : Prop := ∀ frame ∈ batch.frames, FrameReady config frame

/-- Every retained request uses the focus of its original typed source occurrence. -/
theorem allocation_source_within (allocation : Allocation plan bound expected sourcePattern)
    (footprint : List String)
    (inside : ∀ name ∈ sourcePattern.freeFvarNames, name ∈ footprint) :
    ∀ name ∈ allocation.request.source.freeFvarNames, name ∈ footprint := by
  have focus : allocation.job.variant.site.focus = allocation.job.origin.site.focus := by
    obtain ⟨context, member, equal⟩ := List.mem_map.mp allocation.licensed.2
    exact congrArg (fun variant : CollectionSelection.SiteVariant => variant.site.focus) equal.symm
  rw [allocation.request_fields.2.2.2.1, focus]
  intro name occurs
  apply inside name
  rw [← allocation.licensed.1.2.source_eq]
  exact (GeneralEquationContexts.fill_contains_source allocation.job.origin.site.context
    allocation.job.origin.site.focus).2.1 name occurs

theorem begin_ready (allocations : List (Allocation plan bound expected (CanonicalBags.canon sourcePattern)))
    (unregistered : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []) :
    StateReady (Config.forSource plan (CanonicalBags.canon sourcePattern) unregistered)
      (State.beginCanonical allocations) := by
  intro frame member
  obtain ⟨allocation, present, rfl⟩ := List.mem_map.mp member
  apply initial_ready
  exact allocation_source_within allocation _ (fun _ occurs => List.mem_append_left _ occurs)

theorem round_ready (config : Config plan) (batch : CState) (ready : StateReady config batch) :
    StateReady config batch.round := by
  intro frame member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact run_ready config original 1 (ready original present)

theorem run_state_ready (config : Config plan) (batch : CState) (work : Nat)
    (ready : StateReady config batch) : StateReady config (State.run work batch) := by
  induction work generalizing batch with
  | zero => exact ready
  | succ work ih => exact ih batch.round (round_ready config batch ready)

theorem resume_returns (host : Effects.State) (config : Config plan) :
    ∀ (work : Nat) (batch : CState), StateReady config batch →
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:resume" [encoded (environmentTerm config),number work,
        encoded (encodeList frameTerm batch.frames), encoded (encodeList publicationTerm batch.log)]) host
      (encoded (stateTerm (State.run work batch)))
  | 0, batch, _ => by canonical_batch_eval unfolding [State.run]
  | work + 1, batch, ready => by
    have advanced := advance_frames_returns host config batch.frames ready
    have joined := append_returns publicationTerm host batch.log (batch.frames.flatMap Frame.fresh)
    have later := resume_returns host config work batch.round (round_ready config batch ready)
    simp only [advancedFramesTerm, encoded, CettaWireAtom.encode, CettaWireAtom.encodeMany] at advanced
    canonical_batch_eval [advanced,joined,later] unfolding [State.run,State.round]

theorem run_returns (host : Effects.State) (config : Config plan) (work : Nat) (batch : CState)
    (ready : StateReady config batch) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:run" [encoded (environmentTerm config),number work,encoded (stateTerm batch)]) host
      (encoded (stateTerm (State.run work batch))) := by
  have native := resume_returns host config work batch ready
  canonical_batch_eval [native]

/-- Resume retains the entire chronological packet account, with its original histories. -/
theorem resumed_returns (host : Effects.State) (config : Config plan) (first extra : Nat)
    (batch : CState) (ready : StateReady config batch) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:run" [encoded (environmentTerm config),number extra,
        encoded (stateTerm (State.run first batch))]) host
      (encoded (stateTerm (State.run (first + extra) batch))) := by
  have native := run_returns host config extra (State.run first batch)
    (run_state_ready config batch first ready)
  rw [← State.run_add] at native
  exact native

/-- The source and declared finite provider discharge all initial batch representation obligations. -/
theorem seeded_run_returns (host : Effects.State)
    (allocations : List (Allocation plan bound expected (CanonicalBags.canon sourcePattern)))
    (unregistered : (GeneralPlanEnvironment.environment plan).provider.dynamicRelations = []) (work : Nat) :
    let config := Config.forSource plan (CanonicalBags.canon sourcePattern) unregistered
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:run" [encoded (environmentTerm config),number work,
        encoded (stateTerm (State.beginCanonical allocations))]) host
      (encoded (stateTerm (State.run work (State.beginCanonical allocations)))) :=
  run_returns host _ work (State.beginCanonical allocations) (begin_ready allocations unregistered)

theorem publication_returns (host : Effects.State) (batch : CState) :
    PureReturns CollectionOccurrenceSearchExecution.SelectedNativeSource.runtime [] host
      (apply "gslt:occurrence-batch:publication" [encoded (stateTerm batch)]) host
      (encoded (encodeList publicationTerm batch.log)) := by canonical_batch_eval

#print axioms loop_agreement
#print axioms initial_ready
#print axioms run_ready
#print axioms frame_run_returns
#print axioms tag_returns
#print axioms frame_publication_returns
#print axioms append_returns
#print axioms length_returns
#print axioms drop_returns
#print axioms advance_frames_returns
#print axioms allocation_source_within
#print axioms begin_ready
#print axioms round_ready
#print axioms run_state_ready
#print axioms resume_returns
#print axioms run_returns
#print axioms resumed_returns
#print axioms seeded_run_returns
#print axioms publication_returns
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution.Canonical


namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceBatch
open Mettapedia.GSLT.LanguageDef CettaWire

variable {plan : GeneralExecutionAdmission.Plan} {bound : List TypeExpr}
    {expected : TypeExpr} {sourcePattern : Pattern}

def stateTermWith {matcher : GeneralPremise.MatchingExecution}
    (codec : RetainedMatchingWire.MatchingCodec matcher)
    (batch : State plan bound expected sourcePattern matcher) : Term :=
  .application "RecursiveOccurrenceBatch"
    [encodeList (frameTermWith codec) batch.frames,
      encodeList (publicationTermWith codec.choiceTerm) batch.log]

theorem stateTermWith_ordinary (batch : State plan bound expected sourcePattern) :
    stateTermWith RetainedMatchingWire.ordinaryCodec batch = stateTerm batch := by
  have frames : (frameTermWith RetainedMatchingWire.ordinaryCodec :
      Frame plan bound expected sourcePattern → Term) = frameTerm := funext frameTermWith_ordinary
  have packets : publicationTermWith RetainedMatchingWire.ordinaryCodec.choiceTerm = publicationTerm :=
    funext publicationTermWith_ordinary
  simp only [stateTermWith, stateTerm, frames, packets]

theorem stateTermWith_canonical
    (batch : State plan bound expected sourcePattern RecursiveCollectionHandoff.canonicalMatchingExecution) :
    stateTermWith RetainedMatchingWire.canonicalCodec batch = Canonical.stateTerm batch := rfl

#print axioms stateTermWith_ordinary
#print axioms stateTermWith_canonical
end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CollectionOccurrenceBatchExecution
