import Mettapedia.GSLT.Core.LinkedInventoryLoader
import Mettapedia.Languages.Metamath.MM2CompressedProofHeaderExecution
import Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
import Mettapedia.Languages.Metamath.MM2SourceActionExecution
import Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
import Mettapedia.Languages.Metamath.MM2Transformation
import Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

/-!
# Ordered activation of the compressed MM2 verifier

Source transformation emits compact header and body rows but grants them no
authority.  This module withholds the initial header cursor until the ordered
theorem request arrives, then reinstalls the fixed verifier inventory from
verifier-owned, occurrence-indexed opaque rule values before releasing that
cursor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeaderExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.Metamath.MM2SourceActionKindDispatch
open Mettapedia.Languages.Metamath.MM2SourceActionRuleInventory
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface

def sinkSurface : Sink → Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom =>
      .expression [.symbol "head", natAtom count, atom]
  | .tail count atom =>
      .expression [.symbol "tail", natAtom count, atom]

def inputSurface (patterns : List Atom) : Atom :=
  .expression (.symbol "," :: patterns)

def outputSurface (sinks : List Sink) : Atom :=
  .expression (.symbol "O" :: sinks.map sinkSurface)

private def activationLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-source-compressed-proof-activate"]

def loadLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-source-compressed-rule-load"]

private def finishLocation : Atom :=
  .expression [.symbol "05", .symbol "mm-source-compressed-rule-finish"]

def sourceProofOwnerTemplate : Atom :=
  .expression
    [.symbol "mm-source-proof-owner", .var "source", .var "position"]

private def sourceTheoremStatementTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem", .var "theorem-site",
      .var "theorem-label", .var "theorem-typecode",
      .var "theorem-body", .var "theorem-proof",
      .var "theorem-separator", .var "theorem-terminator"]

private def proofRequestTemplate : Atom :=
  .expression
    [.symbol "mm-source-theorem-proof-request", .var "source",
      .var "position", .var "next-position",
      sourceTheoremStatementTemplate]

def headerControlTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-header-control", .var "source",
      sourceProofOwnerTemplate, natAtom 0]

/-- Owner-bound administrative request used to reinstall the finite compact
verifier family after one volatile MM2 rule has been selected. -/
def compressedDispatchReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-compressed-dispatch", .var "scope-owner",
      .var "proof-owner"]

private def sourceCompressedDispatchReloadTemplate : Atom :=
  .expression
    [.symbol "mm-reload-compressed-dispatch", .var "source",
      sourceProofOwnerTemplate]

/-- Verifier-owned opaque continuation used to arm a compact dispatch round.
The source rows can request a reload, but only this static row can release the
ordinary MM2 `exec` that implements it. -/
private def compressedDispatchReloadCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-compressed-dispatch-reload",
    .var "compressed-dispatch-reload-rule"]

private def compressedDispatchReloadCaptureVariable : Atom :=
  .var "compressed-dispatch-reload-rule"

private def preparedHeaderControlTemplate : Atom :=
  .expression
    [.symbol "mm-source-proof-control-prepared", .var "source",
      sourceProofOwnerTemplate, headerControlTemplate]

/-- Withhold the source-derived compressed header cursor until its exact
ordered theorem occurrence requests proof execution. -/
def deferCompressedHeaderControlRow : Atom → Atom
  | row@(.expression
      [.symbol "mm-compressed-header-control", scopeOwner, proofOwner,
        _position]) =>
      .expression
        [.symbol "mm-source-proof-control-prepared", scopeOwner,
          proofOwner, row]
  | row => row

def deferCompressedHeaderControls (rows : List Atom) : List Atom :=
  rows.map deferCompressedHeaderControlRow

def compressedRuleLoadingTemplate : Atom :=
  .expression
    [.symbol "mm-source-compressed-rule-loading", .var "source",
      .var "position", sourceProofOwnerTemplate, headerControlTemplate,
      .var "rule-position"]

private def initialLoadingTemplate : Atom :=
  .expression
    [.symbol "mm-source-compressed-rule-loading", .var "source",
      .var "position", sourceProofOwnerTemplate, headerControlTemplate,
      natAtom 0]

private def activationSelf : Atom :=
  .expression
    [.symbol "exec", activationLocation,
      .var "activation-input", .var "activation-output"]

private def activationPatterns : List Atom :=
  [activationSelf, proofRequestTemplate, preparedHeaderControlTemplate]

private def activationSinks : List Sink :=
  [.add activationSelf,
   .remove proofRequestTemplate,
   .remove preparedHeaderControlTemplate,
   .add initialLoadingTemplate]

def sourceCompressedProofActivateRule : Atom :=
  .expression
    [.symbol "exec", activationLocation, inputSurface activationPatterns,
      outputSurface activationSinks]

def sourceCompressedProofActivateDirective : SourceExecFact where
  atom := sourceCompressedProofActivateRule
  loc := activationLocation
  rule :=
    { priority := 3
      name := "mm-source-compressed-proof-activate"
      input := .compat (mkPattern activationPatterns)
      guards := []
      tmpl := mkTemplate activationSinks }

theorem extract_sourceCompressedProofActivateRule_exact :
    extractSupportedSourceExecFact sourceCompressedProofActivateRule =
      some sourceCompressedProofActivateDirective := by
  rfl

def compressedVerifierRuleOwner : Atom :=
  .symbol "mm-compressed-verifier-rule-inventory"

/-- A finite, inspectable target-rule presentation. The lowering retains rule
order explicitly and treats each target rule as opaque data. Behavioral
hosting remains a separate obligation of the surrounding transformation. -/
structure FiniteVerifierRulePresentation where
  family : String
  owner : Atom
  endTag : String
  rules : List Atom
deriving DecidableEq

namespace FiniteVerifierRulePresentation

open Mettapedia.GSLT.FiniteInventoryLoader

def rows (presentation : FiniteVerifierRulePresentation) : List Atom :=
  linkedRows presentation.family presentation.owner id presentation.rules

def endRow (presentation : FiniteVerifierRulePresentation) : Atom :=
  .expression
    [.symbol presentation.endTag, natAtom presentation.rules.length]

/-- Reify the exact authored verifier-rule inventory through the generic
occurrence-indexed GSLT-data transform.  This is separate from MM2 surface
rendering: it retains typed positions and values for the generic loader
correctness argument. -/
def reifiedRuleArtifact (presentation : FiniteVerifierRulePresentation) :
    Mettapedia.GSLT.LinkedInventoryLoader.ReifiedArtifact Atom :=
  Mettapedia.GSLT.LinkedInventoryLoader.reify presentation.rules

@[simp] theorem reifiedRuleArtifact_source
    (presentation : FiniteVerifierRulePresentation) :
    presentation.reifiedRuleArtifact.source = presentation.rules := by
  rfl

/-- The generic linked-row decoder recovers every supplied verifier rule,
including duplicate rule occurrences, from the reified transform artifact. -/
@[simp] theorem reifiedRuleArtifact_decodes
    (presentation : FiniteVerifierRulePresentation) :
    Mettapedia.GSLT.LinkedInventoryLoader.decodeInventory?
      presentation.reifiedRuleArtifact.target = some presentation.rules := by
  exact Mettapedia.GSLT.LinkedInventoryLoader.decodeInventory?_reify
    presentation.rules

@[simp] theorem reifiedRuleArtifact_target_length
    (presentation : FiniteVerifierRulePresentation) :
    presentation.reifiedRuleArtifact.target.length =
      presentation.rules.length := by
  exact Mettapedia.GSLT.LinkedInventoryLoader.encodeInventory_length
    presentation.rules

@[simp] theorem rows_length (presentation : FiniteVerifierRulePresentation) :
    presentation.rows.length = presentation.rules.length := by
  simp [rows]

theorem mem_rows_iff (presentation : FiniteVerifierRulePresentation)
    (row : Atom) :
    row ∈ presentation.rows ↔
      ∃ (position : Nat) (inBounds : position < presentation.rules.length),
        linkedRow presentation.family presentation.owner position
          (position + 1) presentation.rules[position] = row := by
  exact mem_linkedRows_iff presentation.family presentation.owner id
    presentation.rules row

/-- The abstract loader starts from the exact ordered opaque-rule inventory
carried by this presentation. -/
def loaderInitial (presentation : FiniteVerifierRulePresentation) :
    State Atom :=
  initial presentation.rules

/-- Successful loading exposes exactly the same ordered rule occurrences. -/
def loaderTerminal (presentation : FiniteVerifierRulePresentation) :
    State Atom :=
  terminal presentation.rules

/-- Abstract state named by a concrete occurrence cursor. -/
def loaderAtCursor (presentation : FiniteVerifierRulePresentation)
    (position : Nat) : State Atom :=
  atCursor presentation.rules position

/-- Every finite verifier presentation has an exact proof-relevant loading
path, independent of the internal syntax of its rules. -/
def loaderPath (presentation : FiniteVerifierRulePresentation) :
    (gslt Atom).RewritePath presentation.loaderInitial
      presentation.loaderTerminal :=
  complete presentation.reifiedRuleArtifact.source

/-- The second transformation stage lowers the abstract occurrence inventory
to an exact linked-row operational state. -/
def linkedLoaderInitial (presentation : FiniteVerifierRulePresentation) :
    Mettapedia.GSLT.LinkedInventoryLoader.State Atom :=
  Mettapedia.GSLT.LinkedInventoryLoader.lowerState
    presentation.loaderInitial

/-- Exact linked-row terminal state for the same opaque rule inventory. -/
def linkedLoaderTerminal (presentation : FiniteVerifierRulePresentation) :
    Mettapedia.GSLT.LinkedInventoryLoader.State Atom :=
  Mettapedia.GSLT.LinkedInventoryLoader.lowerState
    presentation.loaderTerminal

/-- The abstract loader-to-linked-loader arrow is an existing covered GSLT
translation: it preserves every occurrence step and reflects every target
step leaving a lowered state. -/
def linkedLowering (_presentation : FiniteVerifierRulePresentation) :
    Mettapedia.GSLT.IndexedOperational.CoveredTranslation
      (gslt Atom) (Mettapedia.GSLT.LinkedInventoryLoader.gslt Atom) :=
  Mettapedia.GSLT.LinkedInventoryLoader.lowering

/-- The linked-row stage retains the complete proof-relevant path rather than
only the terminal support set. -/
def linkedLoaderPath (presentation : FiniteVerifierRulePresentation) :
    (Mettapedia.GSLT.LinkedInventoryLoader.gslt Atom).RewritePath
      presentation.linkedLoaderInitial
      presentation.linkedLoaderTerminal :=
  Mettapedia.GSLT.LinkedInventoryLoader.lowerPath presentation.loaderPath

@[simp] theorem linkedLoaderPath_length
    (presentation : FiniteVerifierRulePresentation) :
    presentation.linkedLoaderPath.length = presentation.loaderPath.length :=
  Mettapedia.GSLT.LinkedInventoryLoader.lowerPath_length
    presentation.loaderPath

@[simp] theorem loaderTerminal_loaded
    (presentation : FiniteVerifierRulePresentation) :
    presentation.loaderTerminal.loaded = presentation.rules := by
  rfl

/-- Mutating the ordered rule inventory mutates the loader's terminal
observation; presentation data is therefore behaviorally load-bearing. -/
theorem loaderTerminal_ne_of_rules_ne
    {left right : FiniteVerifierRulePresentation}
    (different : left.rules ≠ right.rules) :
    left.loaderTerminal ≠ right.loaderTerminal := by
  intro equal
  apply different
  exact congrArg State.loaded equal

/-- Every emitted linked row is a witness for the corresponding in-bounds
step of the abstract occurrence-preserving loader. -/
theorem row_witnesses_abstract_step
    (presentation : FiniteVerifierRulePresentation) (position : Nat)
    (inBounds : position < presentation.rules.length) :
    linkedRow presentation.family presentation.owner position (position + 1)
        presentation.rules[position] ∈ presentation.rows ∧
      Step (presentation.loaderAtCursor position)
        (presentation.loaderAtCursor (position + 1)) := by
  constructor
  · apply (presentation.mem_rows_iff _).2
    exact ⟨position, inBounds, rfl⟩
  · exact atCursor_step presentation.rules position inBounds

/-- The same emitted row also witnesses the corresponding step after the
generic GSLT-to-GSLT linked-row lowering. -/
theorem row_witnesses_linked_step
    (presentation : FiniteVerifierRulePresentation) (position : Nat)
    (inBounds : position < presentation.rules.length) :
    linkedRow presentation.family presentation.owner position (position + 1)
        presentation.rules[position] ∈ presentation.rows ∧
      Mettapedia.GSLT.LinkedInventoryLoader.Step
        (Mettapedia.GSLT.LinkedInventoryLoader.lowerState
          (presentation.loaderAtCursor position))
        (Mettapedia.GSLT.LinkedInventoryLoader.lowerState
          (presentation.loaderAtCursor (position + 1))) := by
  obtain ⟨rowMember, abstractStep⟩ :=
    presentation.row_witnesses_abstract_step position inBounds
  exact ⟨rowMember,
    Mettapedia.GSLT.LinkedInventoryLoader.lower_step abstractStep⟩

/-- The explicit end marker names exactly the abstract terminal cursor. -/
theorem endRow_marks_terminal_cursor
    (presentation : FiniteVerifierRulePresentation) :
    presentation.loaderAtCursor presentation.rules.length =
      presentation.loaderTerminal := by
  exact atCursor_length presentation.rules

/-- Lowering preserves the exact terminal cursor named by the explicit end
marker. -/
theorem endRow_marks_linked_terminal_cursor
    (presentation : FiniteVerifierRulePresentation) :
    Mettapedia.GSLT.LinkedInventoryLoader.lowerState
        (presentation.loaderAtCursor presentation.rules.length) =
      presentation.linkedLoaderTerminal := by
  exact congrArg Mettapedia.GSLT.LinkedInventoryLoader.lowerState
    presentation.endRow_marks_terminal_cursor

end FiniteVerifierRulePresentation

/-- The header is the first compact verifier stage.  Its rules are transformed
through the strict reusable rearming pass.  A rule can therefore request and
release the next dispatch round only after it has actually matched; no raw
reloader exists before the owner-bound request. -/
private theorem compressedHeaderRules_rearmable :
    (buildRearm? compressedDispatchReloadTemplate
      compressedDispatchReloadCaptureTemplate
      compressedDispatchReloadCaptureVariable compressedHeaderRules).isSome =
      true := by
  decide +kernel

/-- The header profile records the actual authored finite rule surface and its
strict rearmed target surface.  The loader below remains a separate target
realization rather than being hidden inside this transformation artifact. -/
def compressedHeaderRearmArtifact : RearmArtifact :=
  (buildRearm? compressedDispatchReloadTemplate
    compressedDispatchReloadCaptureTemplate
    compressedDispatchReloadCaptureVariable compressedHeaderRules).get
      (by simpa using compressedHeaderRules_rearmable)

private theorem compressedHeaderRearmArtifact_built :
    buildRearm? compressedDispatchReloadTemplate
      compressedDispatchReloadCaptureTemplate
      compressedDispatchReloadCaptureVariable compressedHeaderRules =
        some compressedHeaderRearmArtifact := by
  simp [compressedHeaderRearmArtifact]

/-- The header artifact carries the exact finite header presentation supplied
to the generic transform, rather than an independently selected rule list. -/
theorem compressedHeaderRearmArtifact_sourceRules :
    compressedHeaderRearmArtifact.sourceRules = compressedHeaderRules := by
  exact buildRearm?_sourceRules compressedDispatchReloadTemplate
    compressedDispatchReloadCaptureTemplate
    compressedDispatchReloadCaptureVariable compressedHeaderRules
    compressedHeaderRearmArtifact compressedHeaderRearmArtifact_built

def compressedHeaderRulesWithReload : List Atom :=
  compressedHeaderRearmArtifact.targetRules

/-- The rearming transform changes each header rule's surface but preserves
the finite rule-occurrence inventory recorded by its actual artifact. -/
theorem compressedHeaderRearmArtifact_preserves_occurrences :
    compressedHeaderRearmArtifact.targetRules.length =
      compressedHeaderRearmArtifact.sourceRules.length := by
  exact rearmAll?_target_length compressedDispatchReloadTemplate
    compressedDispatchReloadCaptureTemplate
    compressedDispatchReloadCaptureVariable
    compressedHeaderRearmArtifact.exact

theorem compressedHeaderRulesWithReload_length :
    compressedHeaderRulesWithReload.length = compressedHeaderRules.length := by
  rw [compressedHeaderRulesWithReload,
    compressedHeaderRearmArtifact_preserves_occurrences,
    compressedHeaderRearmArtifact_sourceRules]

/-- Header faults retain their compact-machine origin but capture the same
owner-bound source rejection continuation as body faults. -/
private theorem compressedHeaderRules_source_fault_captureable :
    (captureRulesAddingOutputHead? "mm-proof-fault"
      compressedProofFaultSourceTheoremRejectCaptureTemplate
      (.var "compressed-source-theorem-fault-reject-rule")
      compressedHeaderRulesWithReload).isSome = true := by
  decide +kernel

def compressedHeaderRulesWithReloadAndSourceFaultReject : List Atom :=
  (captureRulesAddingOutputHead? "mm-proof-fault"
    compressedProofFaultSourceTheoremRejectCaptureTemplate
    (.var "compressed-source-theorem-fault-reject-rule")
    compressedHeaderRulesWithReload).get
      (by simpa using compressedHeaderRules_source_fault_captureable)

/-! ### Compact-to-normal assertion handoff -/

/-- The normal assertion result is the unique target-owned boundary at which
the compact assertion continuation becomes eligible again.  The strict surface
transform adds an opaque rejoin-code capture to that result rule; it neither
inspects the compressed proof nor reconstructs a normal-label trace. -/
private theorem normalAssertionResultComplete_rejoinable :
    (appendCapturedRuleSink? compressedAssertionRejoinRuleCaptureTemplate
      (.var "compressed-assertion-rejoin-rule")
      normalAssertionResultCompleteRule).isSome = true := by
  decide +kernel

def normalAssertionResultCompleteRuleWithCompressedRejoin : Atom :=
  (appendCapturedRuleSink? compressedAssertionRejoinRuleCaptureTemplate
    (.var "compressed-assertion-rejoin-rule")
    normalAssertionResultCompleteRule).get
      (by simpa using normalAssertionResultComplete_rejoinable)

def normalFloatingTypecodePrepareCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-normal-floating-typecode-prepare",
    .var "normal-floating-typecode-prepare-rule"]

private def compressedNormalConsumedStackTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-stack-cell", .var "proof",
      .var "stack-position", .var "compressed-child-node"]

private def compressedNormalFloatingChildNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof",
      .var "compressed-child-node",
      .expression
        [.symbol "mm-formula", .var "actual-typecode", .var "body"],
      .var "child-occurrence"]

private theorem normalFloatingTypecodePrepareRule_compact_consumable :
    (appendPositivePremisesAndRemoveSink?
      [compressedNormalConsumedStackTemplate,
        compressedNormalFloatingChildNodeTemplate]
      compressedNormalConsumedStackTemplate
      normalFloatingTypecodePrepareRule).isSome = true := by
  decide +kernel

/-- The compressed assertion handoff checks the ordinary stack formula and
its compact node identity together, then consumes the exact compact stack
mirror before the assertion may shrink and later reuse that position. -/
def normalFloatingTypecodePrepareRuleWithCompactStackConsumption : Atom :=
  (appendPositivePremisesAndRemoveSink?
    [compressedNormalConsumedStackTemplate,
      compressedNormalFloatingChildNodeTemplate]
    compressedNormalConsumedStackTemplate
    normalFloatingTypecodePrepareRule).get
      (by simpa using normalFloatingTypecodePrepareRule_compact_consumable)

def normalFloatingTypecodePrepareCaptureRow : Atom :=
  .expression [.symbol "mm-internal-normal-floating-typecode-prepare",
    normalFloatingTypecodePrepareRuleWithCompactStackConsumption]

private def compressedNormalEssentialChildNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof",
      .var "compressed-child-node",
      .expression
        [.symbol "mm-formula", .var "typecode", .var "actual-body"],
      .var "child-occurrence"]

private theorem normalAssertionEssentialRule_compact_consumable :
    (appendPositivePremisesAndRemoveSink?
      [compressedNormalConsumedStackTemplate,
        compressedNormalEssentialChildNodeTemplate]
      compressedNormalConsumedStackTemplate
      normalAssertionEssentialRule).isSome = true := by
  decide +kernel

/-- Essential-hypothesis matching consumes the same compact stack mirror as
floating-hypothesis matching while retaining the original normal rule's body
comparison and continuation. -/
def normalAssertionEssentialRuleWithCompactStackConsumption : Atom :=
  (appendPositivePremisesAndRemoveSink?
    [compressedNormalConsumedStackTemplate,
      compressedNormalEssentialChildNodeTemplate]
    compressedNormalConsumedStackTemplate
    normalAssertionEssentialRule).get
      (by simpa using normalAssertionEssentialRule_compact_consumable)

private theorem normalAssertionBeginRule_prepare_capturable :
    (appendCapturedRuleSink? normalFloatingTypecodePrepareCaptureTemplate
      (.var "normal-floating-typecode-prepare-rule")
      normalAssertionBeginRule).isSome = true := by
  decide +kernel

/-- Creating the first assertion bind releases the exact verifier-owned
typecode checker that is authorized to consume it. -/
def normalAssertionBeginRuleWithTypecodePrepare : Atom :=
  (appendCapturedRuleSink? normalFloatingTypecodePrepareCaptureTemplate
    (.var "normal-floating-typecode-prepare-rule")
    normalAssertionBeginRule).get
      (by simpa using normalAssertionBeginRule_prepare_capturable)

private theorem normalFloatingTypecodeEqualRule_prepare_capturable :
    (appendCapturedRuleSink? normalFloatingTypecodePrepareCaptureTemplate
      (.var "normal-floating-typecode-prepare-rule")
      normalFloatingTypecodeEqualRule).isSome = true := by
  decide +kernel

/-- A successful floating bind releases the same checker for the next
hypothesis occurrence. -/
def normalFloatingTypecodeEqualRuleWithTypecodePrepare : Atom :=
  (appendCapturedRuleSink? normalFloatingTypecodePrepareCaptureTemplate
    (.var "normal-floating-typecode-prepare-rule")
    normalFloatingTypecodeEqualRule).get
      (by simpa using normalFloatingTypecodeEqualRule_prepare_capturable)

private theorem compressedNormalVerdictRules_prepare_replaceable :
    (replaceMatching? normalFloatingTypecodePrepareRule
      normalFloatingTypecodePrepareRuleWithCompactStackConsumption
      (sourceVerdictRules normalProofMachineRuleInventory)).isSome = true := by
  decide +kernel

private def compressedNormalMirrorVerdictRules : List Atom :=
  (replaceMatching? normalFloatingTypecodePrepareRule
    normalFloatingTypecodePrepareRuleWithCompactStackConsumption
    (sourceVerdictRules normalProofMachineRuleInventory)).get
      (by simpa using compressedNormalVerdictRules_prepare_replaceable)

private theorem compressedNormalVerdictRules_equal_replaceable :
    (replaceMatching? normalFloatingTypecodeEqualRule
      normalFloatingTypecodeEqualRuleWithTypecodePrepare
      compressedNormalMirrorVerdictRules).isSome = true := by
  decide +kernel

def compressedNormalVerdictRules : List Atom :=
  (replaceMatching? normalFloatingTypecodeEqualRule
    normalFloatingTypecodeEqualRuleWithTypecodePrepare
    compressedNormalMirrorVerdictRules).get
      (by simpa using compressedNormalVerdictRules_equal_replaceable)

private theorem normalProofMachineRules_rejoin_replaceable :
    (replaceMatching? normalAssertionResultCompleteRule
      normalAssertionResultCompleteRuleWithCompressedRejoin
      normalProofMachineRules).isSome = true := by
  decide +kernel

/-- The handoff retains the complete normal machine byte-for-byte except for
its one assertion-result publication rule, which releases the captured compact
continuation precisely when its result state exists. -/
def normalProofMachineRulesWithCompressedRejoin : List Atom :=
  (replaceMatching? normalAssertionResultCompleteRule
    normalAssertionResultCompleteRuleWithCompressedRejoin
    normalProofMachineRules).get
      (by simpa using normalProofMachineRules_rejoin_replaceable)

private theorem normalProofMachineRules_begin_replaceable :
    (replaceMatching? normalAssertionBeginRule
      normalAssertionBeginRuleWithTypecodePrepare
      normalProofMachineRulesWithCompressedRejoin).isSome = true := by
  decide +kernel

private def normalProofMachineRulesWithCompressedRejoinAndPreparedTypecode :
    List Atom :=
  (replaceMatching? normalAssertionBeginRule
    normalAssertionBeginRuleWithTypecodePrepare
    normalProofMachineRulesWithCompressedRejoin).get
      (by simpa using normalProofMachineRules_begin_replaceable)

private theorem normalProofMachineRules_essential_replaceable :
    (replaceMatching? normalAssertionEssentialRule
      normalAssertionEssentialRuleWithCompactStackConsumption
      normalProofMachineRulesWithCompressedRejoinAndPreparedTypecode).isSome =
        true := by
  decide +kernel

def normalProofMachineRulesWithCompressedRejoinAndTypecodePrepare : List Atom :=
  (replaceMatching? normalAssertionEssentialRule
    normalAssertionEssentialRuleWithCompactStackConsumption
    normalProofMachineRulesWithCompressedRejoinAndPreparedTypecode).get
      (by simpa using normalProofMachineRules_essential_replaceable)

private theorem normalProofMachineRules_source_verdict_replaceable :
    (replaceNormalAcceptWithSourceTheoremSuccess?
      normalProofMachineRulesWithCompressedRejoinAndTypecodePrepare).isSome = true := by
  decide +kernel

/-- The normal terminal rule is replaced by an exact captured continuation
into source theorem success.  This keeps the source verdict path dormant until
the normal machine has actually emitted its acceptance observation. -/
def normalProofMachineRulesWithCompressedRejoinAndSourceVerdict : List Atom :=
  (replaceNormalAcceptWithSourceTheoremSuccess?
    normalProofMachineRulesWithCompressedRejoinAndTypecodePrepare).get
      (by simpa using normalProofMachineRules_source_verdict_replaceable)

/-- Owner-bound request which re-arms one normal assertion transition after a
compact proof has crossed into the normal submachine.  It is distinct from the
bridge request that initially loads the finite normal inventory. -/
private def compressedNormalRearmTriggerTemplate : Atom :=
  .expression [.symbol "mm-reload-compressed-normal-rearm",
    .var "proof-owner"]

/-- Opaque verifier-owned code row for the low-priority normal rearming
dispatcher.  Normal rules capture this value as code rather than copying an
`exec` shell across their expression-local substitution boundary. -/
private def compressedNormalRearmCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-rearm",
    .var "compressed-normal-rearm-rule"]

private def compressedNormalRearmCaptureVariable : Atom :=
  .var "compressed-normal-rearm-rule"

private def compressedNormalHandoffSourceRules : List Atom :=
  normalProofMachineRulesWithCompressedRejoinAndSourceVerdict ++
    compressedNormalVerdictRules

private theorem compressedNormalHandoffSourceRules_reload_removable :
    (removeAddedOutputHeadFromRules? "mm-reload-normal-dispatch"
      compressedNormalHandoffSourceRules).isSome = true := by
  decide +kernel

/-- The compact handoff has a distinct owner-bound rearm protocol.  Its
source rules therefore shed the ordinary normal-dispatch request before the
generic rearm transformation is applied. -/
def compressedNormalHandoffSourceRulesWithoutOrdinaryReload : List Atom :=
  (removeAddedOutputHeadFromRules? "mm-reload-normal-dispatch"
    compressedNormalHandoffSourceRules).get
      (by simpa using compressedNormalHandoffSourceRules_reload_removable)

/-- Capability separation is visible in the transformed syntax: no compact
handoff rule can request the ordinary normal dispatcher. -/
theorem compressedNormalHandoffSourceRules_no_ordinary_reload :
    ∀ rule ∈ compressedNormalHandoffSourceRulesWithoutOrdinaryReload,
      outputAddsHead? "mm-reload-normal-dispatch" rule = some false := by
  decide +kernel

theorem compressedNormalHandoffSourceRulesWithoutOrdinaryReload_length :
    compressedNormalHandoffSourceRulesWithoutOrdinaryReload.length =
      compressedNormalHandoffSourceRules.length := by
  decide +kernel

private theorem compressedNormalHandoffSourceRules_rearmable :
    (buildRearm? compressedNormalRearmTriggerTemplate
      compressedNormalRearmCaptureTemplate
      compressedNormalRearmCaptureVariable
      compressedNormalHandoffSourceRulesWithoutOrdinaryReload).isSome = true := by
  decide +kernel

/-- The normal submachine is made reactive by the same finite rule
transformation used for compact header rules.  It remains a transformation of
the supplied presentation; no normal proof labels are inspected. -/
def compressedNormalRearmArtifact : RearmArtifact :=
  (buildRearm? compressedNormalRearmTriggerTemplate
    compressedNormalRearmCaptureTemplate
    compressedNormalRearmCaptureVariable
    compressedNormalHandoffSourceRulesWithoutOrdinaryReload).get
      (by simpa using compressedNormalHandoffSourceRules_rearmable)

private theorem compressedNormalRearmArtifact_built :
    buildRearm? compressedNormalRearmTriggerTemplate
      compressedNormalRearmCaptureTemplate
      compressedNormalRearmCaptureVariable
      compressedNormalHandoffSourceRulesWithoutOrdinaryReload =
        some compressedNormalRearmArtifact := by
  simp [compressedNormalRearmArtifact]

/-- The normal-profile artifact retains precisely the input rule presentation
that the compact handoff passes to the generic rearming transform. -/
theorem compressedNormalRearmArtifact_sourceRules :
    compressedNormalRearmArtifact.sourceRules =
      compressedNormalHandoffSourceRulesWithoutOrdinaryReload := by
  exact buildRearm?_sourceRules compressedNormalRearmTriggerTemplate
    compressedNormalRearmCaptureTemplate
    compressedNormalRearmCaptureVariable
    compressedNormalHandoffSourceRulesWithoutOrdinaryReload
    compressedNormalRearmArtifact compressedNormalRearmArtifact_built

/-- The reactive normal-profile transform preserves the exact number of
rule occurrences recorded by its actual finite presentation. -/
theorem compressedNormalRearmArtifact_preserves_occurrences :
    compressedNormalRearmArtifact.targetRules.length =
      compressedNormalRearmArtifact.sourceRules.length := by
  exact rearmAll?_target_length compressedNormalRearmTriggerTemplate
    compressedNormalRearmCaptureTemplate
    compressedNormalRearmCaptureVariable
    compressedNormalRearmArtifact.exact

/-- The complete normal-profile inventory needed after a compact assertion
code is resolved.  Values remain opaque to the compact proof source: this is
verifier-owned target code, loaded occurrence by occurrence before the normal
machine is released. -/
def compressedNormalHandoffRules : List Atom :=
  compressedNormalRearmArtifact.targetRules

theorem compressedNormalHandoffRules_length :
    compressedNormalHandoffRules.length =
      normalProofMachineRulesWithCompressedRejoinAndSourceVerdict.length +
        compressedNormalVerdictRules.length := by
  rw [compressedNormalHandoffRules,
    compressedNormalRearmArtifact_preserves_occurrences,
    compressedNormalRearmArtifact_sourceRules,
    compressedNormalHandoffSourceRulesWithoutOrdinaryReload_length]
  simp [compressedNormalHandoffSourceRules]

/-- The strict selected-rule transform changes the handoff inventory at its
real normal result-completion occurrence and leaves the original raw rule out.
This is a target-surface invariant, not a claim about arbitrary authored MM2
input. -/
theorem normalProofMachineRulesWithCompressedRejoin_exact :
    normalAssertionResultCompleteRule ∉ normalProofMachineRulesWithCompressedRejoin ∧
      normalAssertionResultCompleteRuleWithCompressedRejoin ∈
      normalProofMachineRulesWithCompressedRejoin := by
  decide +kernel

/-- The handoff removes the raw normal acceptance rule and replaces it with
the source-verdict continuation. -/
theorem normalProofMachineRulesWithCompressedRejoinAndSourceVerdict_exact :
    normalAcceptRule ∉ normalProofMachineRulesWithCompressedRejoinAndSourceVerdict ∧
      normalAcceptRuleWithSourceTheoremSuccess ∈
        normalProofMachineRulesWithCompressedRejoinAndSourceVerdict := by
  decide +kernel

private def compressedNormalHandoffRuleOwner : Atom :=
  .symbol "mm-compressed-normal-handoff-rule-inventory"

/-- A second concrete use of the generic finite rule presentation: compact
assertion resolution loads the normal submachine through linked occurrences,
not through a host-side expansion or an arbitrary single-rule choice. -/
def compressedNormalHandoffRulePresentation : FiniteVerifierRulePresentation where
  family := "compressed-normal-handoff-rule"
  owner := compressedNormalHandoffRuleOwner
  endTag := "mm-compressed-normal-handoff-rule-end"
  rules := compressedNormalHandoffRules

def compressedNormalHandoffRuleRows : List Atom :=
  compressedNormalHandoffRulePresentation.rows

def compressedNormalHandoffRuleEnd : Atom :=
  compressedNormalHandoffRulePresentation.endRow

private def compressedNormalHandoffLoadLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-compressed-normal-handoff-load"]

private def compressedNormalHandoffFinishLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-compressed-normal-handoff-z-finish"]

private def compressedNormalHandoffLoadingTemplate : Atom :=
  .expression [.symbol "mm-compressed-normal-handoff-loading",
    .var "proof-owner", .var "normal-rule-position"]

/-- Initial cursor emitted when a compressed assertion enters the finite
normal-profile loader. -/
def compressedNormalHandoffInitialLoadingTemplate : Atom :=
  .expression [.symbol "mm-compressed-normal-handoff-loading",
    .var "proof-owner", natAtom 0]

private def compressedNormalHandoffNextLoadingTemplate : Atom :=
  .expression [.symbol "mm-compressed-normal-handoff-loading",
    .var "proof-owner", .var "next-normal-rule-position"]

private def compressedNormalHandoffRuleRowTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row",
      stringAtom compressedNormalHandoffRulePresentation.family,
      compressedNormalHandoffRulePresentation.owner,
      .var "normal-rule-position", .var "next-normal-rule-position",
      .var "normal-handoff-rule"]

private def compressedNormalHandoffLoadSelf : Atom :=
  .expression
    [.symbol "exec", compressedNormalHandoffLoadLocation,
      .var "normal-handoff-load-input", .var "normal-handoff-load-output"]

private def compressedNormalHandoffLoadPatterns : List Atom :=
  [compressedNormalHandoffLoadSelf, compressedNormalHandoffLoadingTemplate,
   compressedNormalHandoffRuleRowTemplate]

private def compressedNormalHandoffLoadSinks : List Sink :=
  [.add compressedNormalHandoffLoadSelf,
   .remove compressedNormalHandoffLoadingTemplate,
   .add (.var "normal-handoff-rule"),
   .add compressedNormalHandoffNextLoadingTemplate]

/-- Load one opaque normal-profile rule at the current linked occurrence.
The `00` scheduler position keeps the finite loader ahead of every released
normal rule until its end marker is reached. -/
def compressedNormalHandoffLoadRule : Atom :=
  .expression
    [.symbol "exec", compressedNormalHandoffLoadLocation,
      inputSurface compressedNormalHandoffLoadPatterns,
      outputSurface compressedNormalHandoffLoadSinks]

private def compressedNormalHandoffFinishSelf : Atom :=
  .expression
    [.symbol "exec", compressedNormalHandoffFinishLocation,
      .var "normal-handoff-finish-input",
      .var "normal-handoff-finish-output"]

private def compressedNormalHandoffEndTemplate : Atom :=
  .expression [.symbol compressedNormalHandoffRulePresentation.endTag,
    .var "normal-rule-position"]

private def compressedNormalHandoffFinishPatterns : List Atom :=
  [compressedNormalHandoffFinishSelf, compressedNormalHandoffLoadingTemplate,
   compressedNormalHandoffEndTemplate]

private def compressedNormalHandoffFinishSinks : List Sink :=
  [.remove compressedNormalHandoffLoadingTemplate]

/-- The raw terminal loader step releases the already-loaded normal profile.
It does not synthesize or inspect a normal proof label. -/
private def compressedNormalHandoffFinishRuleRaw : Atom :=
  .expression
    [.symbol "exec", compressedNormalHandoffFinishLocation,
      inputSurface compressedNormalHandoffFinishPatterns,
      outputSurface compressedNormalHandoffFinishSinks]

private theorem compressedNormalHandoffFinishRule_rearmable :
    (appendRearmSinks? compressedNormalRearmTriggerTemplate
      compressedNormalRearmCaptureTemplate
      compressedNormalRearmCaptureVariable
      compressedNormalHandoffFinishRuleRaw).isSome = true := by
  decide +kernel

/-- The terminal loader step makes the first normal dispatch continuation
available only after the finite normal profile has completely loaded. -/
def compressedNormalHandoffFinishRule : Atom :=
  (appendRearmSinks? compressedNormalRearmTriggerTemplate
    compressedNormalRearmCaptureTemplate
    compressedNormalRearmCaptureVariable
    compressedNormalHandoffFinishRuleRaw).get
      (by simpa using compressedNormalHandoffFinishRule_rearmable)

private def compressedNormalDispatchBridgeLocation : Atom :=
  .expression [.symbol "31", .symbol "mm-compressed-normal-dispatch-bridge"]

private def compressedNormalDispatchBridgeSelf : Atom :=
  .expression
    [.symbol "exec", compressedNormalDispatchBridgeLocation,
      .var "normal-bridge-input", .var "normal-bridge-output"]

/-- Pattern that recovers the compiler-owned finite-loader rule. -/
def compressedNormalHandoffLoaderCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-handoff-loader",
    .var "normal-handoff-loader-rule"]

/-- Pattern that recovers the compiler-owned terminal loader rule. -/
def compressedNormalHandoffFinishCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-handoff-finish",
    .var "normal-handoff-finish-rule"]

/-- Complete input pattern of the compressed-to-normal bridge. -/
def compressedNormalDispatchBridgePatterns : List Atom :=
  [compressedNormalDispatchBridgeSelf,
   compressedAssertionNormalReloadRequest,
   compressedNormalHandoffLoaderCaptureTemplate,
   compressedNormalHandoffFinishCaptureTemplate]

/-- Complete output transaction of the compressed-to-normal bridge. -/
def compressedNormalDispatchBridgeSinks : List Sink :=
  [.remove compressedAssertionNormalReloadRequest,
   .add (.var "normal-handoff-loader-rule"),
   .add (.var "normal-handoff-finish-rule"),
   .add compressedNormalHandoffInitialLoadingTemplate]

/-- A compact assertion index delegates to the already-authored normal
assertion machine by activating its verifier-owned finite loader at the
owner-bound handoff.  The bridge itself is emitted by the transformed compact
assertion rule, never by source proof data. -/
def compressedNormalDispatchBridgeRule : Atom :=
  .expression
    [.symbol "exec", compressedNormalDispatchBridgeLocation,
      inputSurface compressedNormalDispatchBridgePatterns,
      outputSurface compressedNormalDispatchBridgeSinks]

theorem compressedNormalDispatchBridgeRule_exec_shape :
    ∃ input output,
      compressedNormalDispatchBridgeRule =
        .expression
          [.symbol "exec",
           .expression
             [.symbol "31", .symbol "mm-compressed-normal-dispatch-bridge"],
           input, output] := by
  exact ⟨_, _, rfl⟩

theorem compressedNormalDispatchBridgeRule_head_shape :
    ∃ tail,
      compressedNormalDispatchBridgeRule =
        .expression (.symbol "exec" :: tail) := by
  exact ⟨_, rfl⟩

def compressedNormalDispatchBridgeDirective : SourceExecFact where
  atom := compressedNormalDispatchBridgeRule
  loc := compressedNormalDispatchBridgeLocation
  rule :=
    { priority := 31
      name := "mm-compressed-normal-dispatch-bridge"
      input := .compat (mkPattern compressedNormalDispatchBridgePatterns)
      guards := []
      tmpl := mkTemplate compressedNormalDispatchBridgeSinks }

theorem extract_compressedNormalDispatchBridgeRule_exact :
    extractSupportedSourceExecFact compressedNormalDispatchBridgeRule =
      some compressedNormalDispatchBridgeDirective := by
  rfl

/-- The handoff must run before the dormant assertion rejoin.  Rule-scoped
execution selects resident directives before matching their data premises, so
the opposite order would consume the rejoin before the normal submachine could
produce its result. -/
theorem compressedNormalDispatchBridge_before_assertionRejoin :
    compressedNormalDispatchBridgeDirective.rule.priority <
      compressedAssertionRejoinDirective.rule.priority := by
  decide

/-! ### Trigger-created normal rearming dispatcher -/

private def compressedNormalRearmLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-compressed-normal-rearm"]

private def compressedNormalRearmSelf : Atom :=
  .expression
    [.symbol "exec", compressedNormalRearmLocation,
      .var "compressed-normal-rearm-input",
      .var "compressed-normal-rearm-output"]

private def compressedNormalRearmRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-rearm-rule", rule]

private def compressedNormalRearmRuleRowTemplate : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-rearm-rule",
    .var "compressed-normal-rearm-target-rule"]

private def compressedNormalRearmPatterns : List Atom :=
  [compressedNormalRearmSelf, compressedNormalRearmTriggerTemplate,
   compressedNormalRearmRuleRowTemplate]

private def compressedNormalRearmSinks : List Sink :=
  [.remove compressedNormalRearmTriggerTemplate,
   .add (.var "compressed-normal-rearm-target-rule")]

/-- Reinstall one opaque rearmed normal rule only after its owner-bound
request exists.  The rule deliberately does not reinstall itself: the next
normal transition releases a fresh copy, which prevents an unmatched reloader
from being consumed before a request arrives. -/
def compressedNormalRearmRule : Atom :=
  .expression
    [.symbol "exec", compressedNormalRearmLocation,
      inputSurface compressedNormalRearmPatterns,
      outputSurface compressedNormalRearmSinks]

def compressedNormalRearmDirective : SourceExecFact where
  atom := compressedNormalRearmRule
  loc := compressedNormalRearmLocation
  rule :=
    { priority := 0
      name := "mm-compressed-normal-rearm"
      input := .compat (mkPattern compressedNormalRearmPatterns)
      guards := []
      tmpl := mkTemplate compressedNormalRearmSinks }

theorem extract_compressedNormalRearmRule_exact :
    extractSupportedSourceExecFact compressedNormalRearmRule =
      some compressedNormalRearmDirective := by
  rfl

private def compressedNormalRearmCaptureRow : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-rearm",
    compressedNormalRearmRule]

private def compressedNormalRearmRuleRows : List Atom :=
  compressedNormalHandoffRules.map compressedNormalRearmRuleRow

private def compressedNormalDispatchBridgeCaptureTemplate : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-dispatch-bridge",
    .var "normal-bridge-rule"]

/-- Compiler-owned carrier for the finite normal-profile loader. -/
def compressedNormalHandoffLoaderCaptureRow : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-handoff-loader",
    compressedNormalHandoffLoadRule]

/-- Compiler-owned carrier for the terminal normal-profile loader step. -/
def compressedNormalHandoffFinishCaptureRow : Atom :=
  .expression [.symbol "mm-internal-compressed-normal-handoff-finish",
    compressedNormalHandoffFinishRule]

/-- Opaque verifier-owned code used at the compact-to-normal boundary.  The
assertion launcher captures the bridge as a whole, and the bridge in turn
captures the normal finite-loader rules as whole values; neither nested rule
crosses an expression-local substitution boundary as source data. -/
def compressedNormalDispatchBridgeRows : List Atom :=
  [.expression [.symbol "mm-internal-compressed-normal-dispatch-bridge",
      compressedNormalDispatchBridgeRule],
   compressedNormalHandoffLoaderCaptureRow,
   compressedNormalHandoffFinishCaptureRow,
   compressedNormalRearmCaptureRow,
   normalFloatingTypecodePrepareCaptureRow] ++
    compressedNormalRearmRuleRows ++ sourceActionKindDispatchStaticRows

private theorem compressedAssertionLaunchRule_bridgeable :
    (appendCapturedRuleSink? compressedNormalDispatchBridgeCaptureTemplate
      (.var "normal-bridge-rule")
      compressedAssertionLaunchRule).isSome = true := by
  decide +kernel

def compressedAssertionLaunchRuleWithNormalBridge : Atom :=
  (appendCapturedRuleSink? compressedNormalDispatchBridgeCaptureTemplate
    (.var "normal-bridge-rule")
    compressedAssertionLaunchRule).get
      (by simpa using compressedAssertionLaunchRule_bridgeable)

theorem compressedAssertionLaunchRuleWithNormalBridge_build_exact :
    appendCapturedRuleSink? compressedNormalDispatchBridgeCaptureTemplate
        (.var "normal-bridge-rule") compressedAssertionLaunchRule =
      some compressedAssertionLaunchRuleWithNormalBridge := by
  unfold compressedAssertionLaunchRuleWithNormalBridge
  exact (Option.some_get
    (by simpa using compressedAssertionLaunchRule_bridgeable)).symm

/-- Adding the captured normal bridge changes only the assertion launcher's
input and output rows; its executable location remains exact. -/
theorem compressedAssertionLaunchRuleWithNormalBridge_exec_shape :
    ∃ input output,
      compressedAssertionLaunchRuleWithNormalBridge =
        .expression
          [.symbol "exec",
           .expression
             [.symbol "08", .symbol "mm-compressed-proof-step-assertion"],
           input, output] := by
  obtain ⟨inputs, sinks, sourceExact⟩ :
      ∃ inputs sinks,
        compressedAssertionLaunchRule =
          .expression
            [.symbol "exec", compressedAssertionLaunchDirective.loc,
             .expression (.symbol "," :: inputs),
             .expression (.symbol "O" :: sinks)] := by
    exact ⟨_, _, rfl⟩
  obtain ⟨input, output, targetExact⟩ :=
    appendCapturedRuleSink?_preserves_comma_exec_location sourceExact
      compressedAssertionLaunchRuleWithNormalBridge_build_exact
  have locationExact : compressedAssertionLaunchDirective.loc =
      .expression
        [.symbol "08", .symbol "mm-compressed-proof-step-assertion"] := by
    rfl
  rw [locationExact] at targetExact
  exact ⟨input, output, targetExact⟩

private theorem compressedBodyRules_normal_bridgeable :
    (replaceMatching? compressedAssertionLaunchRule
      compressedAssertionLaunchRuleWithNormalBridge
      compressedVerifierRules).isSome = true := by
  decide +kernel

/-- The body-stage inventory differs from the authored compact inventory only
at assertion launch: that one rule emits the finite normal-machine handoff.
The strict selected-rule transform rejects an absent or malformed launch rule. -/
def compressedBodyRulesWithNormalBridge : List Atom :=
  (replaceMatching? compressedAssertionLaunchRule
    compressedAssertionLaunchRuleWithNormalBridge
    compressedVerifierRules).get
      (by simpa using compressedBodyRules_normal_bridgeable)

private theorem compressedBodyRules_source_verdict_replaceable :
    (replaceCompressedAcceptWithSourceTheoremSuccess?
      compressedBodyRulesWithNormalBridge).isSome = true := by
  decide +kernel

/-- The compact terminal observation releases its source-verdict continuation
only after the compressed machine has accepted its owner-bound proof. -/
def compressedBodyRulesWithNormalBridgeAndSourceVerdict : List Atom :=
  (replaceCompressedAcceptWithSourceTheoremSuccess?
    compressedBodyRulesWithNormalBridge).get
      (by simpa using compressedBodyRules_source_verdict_replaceable)

private def compressedProofFaultCaptureVariable : Atom :=
  .var "compressed-source-theorem-fault-reject-rule"

/-- One compact rule is transformed only through the strict observation
surface: it must be an ordinary executable and its output head determines
whether the owner-bound fault continuation is captured. -/
def captureCompressedProofFaultRule? (rule : Atom) : Option Atom :=
  captureRuleAddingOutputHead? "mm-proof-fault"
    compressedProofFaultSourceTheoremRejectCaptureTemplate
    compressedProofFaultCaptureVariable rule

private theorem compressedBodyRules_source_fault_captureable :
    (captureRulesAddingOutputHead? "mm-proof-fault"
      compressedProofFaultSourceTheoremRejectCaptureTemplate
      compressedProofFaultCaptureVariable
      compressedBodyRulesWithNormalBridgeAndSourceVerdict).isSome = true := by
  decide +kernel

/-- The finite compact rule presentation is transformed by the exact output
observation it produces.  This attaches no source data and does not alter a
rule whose output lacks `mm-proof-fault`. -/
def compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject :
    List Atom :=
  (captureRulesAddingOutputHead? "mm-proof-fault"
    compressedProofFaultSourceTheoremRejectCaptureTemplate
    compressedProofFaultCaptureVariable
    compressedBodyRulesWithNormalBridgeAndSourceVerdict).get
      (by simpa using compressedBodyRules_source_fault_captureable)

/-- The occurrence selected as the opaque assertion handler remains the
normal-bridge-decorated assertion launcher through the later verdict and
fault-observation passes. -/
theorem compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject_assertion_at :
    compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject[7]? =
      some compressedAssertionLaunchRuleWithNormalBridge := by
  decide +kernel

private theorem compressedHeapLookupFaultRule_is_fault_observation :
    execAddsOutputHead? "mm-proof-fault" compressedHeapLookupFaultRule =
      some true := by
  rfl

private theorem compressedHeapLookupFaultRule_fault_captureable :
    (captureCompressedProofFaultRule? compressedHeapLookupFaultRule).isSome =
      true := by
  decide +kernel

private def compressedHeapLookupFaultRuleWithSourceTheoremFaultReject : Atom :=
  (captureCompressedProofFaultRule? compressedHeapLookupFaultRule).get
    (by simpa using compressedHeapLookupFaultRule_fault_captureable)

private theorem compressedInvalidByteRule_fault_captureable :
    (captureCompressedProofFaultRule? compressedInvalidByteRule).isSome =
      true := by
  decide +kernel

private def compressedInvalidByteRuleWithSourceTheoremFaultReject : Atom :=
  (captureCompressedProofFaultRule? compressedInvalidByteRule).get
    (by simpa using compressedInvalidByteRule_fault_captureable)

private theorem compressedQuestionOpenFaultRule_fault_captureable :
    (captureCompressedProofFaultRule? compressedQuestionOpenFaultRule).isSome =
      true := by
  decide +kernel

private def compressedQuestionOpenFaultRuleWithSourceTheoremFaultReject : Atom :=
  (captureCompressedProofFaultRule? compressedQuestionOpenFaultRule).get
    (by simpa using compressedQuestionOpenFaultRule_fault_captureable)

private theorem compressedSaveFaultRule_fault_captureable :
    (captureCompressedProofFaultRule? compressedSaveFaultRule).isSome = true := by
  decide +kernel

private def compressedSaveFaultRuleWithSourceTheoremFaultReject : Atom :=
  (captureCompressedProofFaultRule? compressedSaveFaultRule).get
    (by simpa using compressedSaveFaultRule_fault_captureable)

private theorem compressedIncompleteRule_fault_captureable :
    (captureCompressedProofFaultRule? compressedIncompleteRule).isSome = true := by
  decide +kernel

private def compressedIncompleteRuleWithSourceTheoremFaultReject : Atom :=
  (captureCompressedProofFaultRule? compressedIncompleteRule).get
    (by simpa using compressedIncompleteRule_fault_captureable)

private def compressedAssertionLaunchCaptureRow : Atom :=
  compressedOwnedRuntimeRuleRow "assertion-launch" compressedAssertionLaunchRule

private def compressedAssertionLaunchCaptureRowWithNormalBridge : Atom :=
  compressedOwnedRuntimeRuleRow "assertion-launch"
    compressedAssertionLaunchRuleWithNormalBridge

private theorem compressedAssertionLaunchCapture_replaceable :
    (replaceMatching? compressedAssertionLaunchCaptureRow
      compressedAssertionLaunchCaptureRowWithNormalBridge
      compressedScannerRuleCaptureRows).isSome = true := by
  decide +kernel

/-- Scanner-owned capture rows are target code, so the compact-to-normal
handoff replaces the one captured assertion launcher through a strict exact
surface transform.  All other scanner rules retain their authored bytes. -/
def compressedScannerRuleCaptureRowsWithNormalBridge : List Atom :=
  (replaceMatching? compressedAssertionLaunchCaptureRow
    compressedAssertionLaunchCaptureRowWithNormalBridge
    compressedScannerRuleCaptureRows).get
      (by simpa using compressedAssertionLaunchCapture_replaceable)

private def compressedAcceptCaptureRow : Atom :=
  compressedOwnedRuntimeRuleRow "accept" compressedAcceptRule

private def compressedAcceptCaptureRowWithSourceVerdict : Atom :=
  compressedOwnedRuntimeRuleRow "accept"
    compressedAcceptRuleWithSourceTheoremSuccess

private theorem compressedAcceptCapture_replaceable :
    (replaceMatching? compressedAcceptCaptureRow
      compressedAcceptCaptureRowWithSourceVerdict
      compressedScannerRuleCaptureRowsWithNormalBridge).isSome = true := by
  decide +kernel

/-- Every scanner-owned route back to compact acceptance retains the normal
handoff replacement and carries the source-verdict continuation at its actual
terminal code value. -/
def compressedScannerRuleCaptureRowsWithNormalBridgeAndSourceVerdict :
    List Atom :=
  (replaceMatching? compressedAcceptCaptureRow
    compressedAcceptCaptureRowWithSourceVerdict
    compressedScannerRuleCaptureRowsWithNormalBridge).get
      (by simpa using compressedAcceptCapture_replaceable)

/-- Exact opaque-row adapter for a verifier-owned scanner reload entry.  It
does not inspect source rows: both the selected and replacement rule values
are supplied by the compact verifier transformation. -/
private def replaceCompressedScannerCapture? (tag : String)
    (source replacement : Atom) (rows : List Atom) : Option (List Atom) :=
  replaceMatching? (compressedOwnedRuntimeRuleRow tag source)
    (compressedOwnedRuntimeRuleRow tag replacement) rows

private theorem compressedScannerLookupFaultCapture_replaceable :
    (replaceCompressedScannerCapture? "lookup-fault"
      compressedHeapLookupFaultRule
      compressedHeapLookupFaultRuleWithSourceTheoremFaultReject
      compressedScannerRuleCaptureRowsWithNormalBridgeAndSourceVerdict).isSome =
        true := by
  decide +kernel

private def compressedScannerRowsWithLookupFaultSourceReject : List Atom :=
  (replaceCompressedScannerCapture? "lookup-fault"
    compressedHeapLookupFaultRule
    compressedHeapLookupFaultRuleWithSourceTheoremFaultReject
    compressedScannerRuleCaptureRowsWithNormalBridgeAndSourceVerdict).get
      (by simpa using compressedScannerLookupFaultCapture_replaceable)

private theorem compressedScannerInvalidByteCapture_replaceable :
    (replaceCompressedScannerCapture? "invalid-byte" compressedInvalidByteRule
      compressedInvalidByteRuleWithSourceTheoremFaultReject
      compressedScannerRowsWithLookupFaultSourceReject).isSome = true := by
  decide +kernel

private def compressedScannerRowsWithInvalidByteSourceReject : List Atom :=
  (replaceCompressedScannerCapture? "invalid-byte" compressedInvalidByteRule
    compressedInvalidByteRuleWithSourceTheoremFaultReject
    compressedScannerRowsWithLookupFaultSourceReject).get
      (by simpa using compressedScannerInvalidByteCapture_replaceable)

private theorem compressedScannerQuestionOpenFaultCapture_replaceable :
    (replaceCompressedScannerCapture? "question-open-fault"
      compressedQuestionOpenFaultRule
      compressedQuestionOpenFaultRuleWithSourceTheoremFaultReject
      compressedScannerRowsWithInvalidByteSourceReject).isSome = true := by
  decide +kernel

private def compressedScannerRowsWithQuestionOpenFaultSourceReject :
    List Atom :=
  (replaceCompressedScannerCapture? "question-open-fault"
    compressedQuestionOpenFaultRule
    compressedQuestionOpenFaultRuleWithSourceTheoremFaultReject
    compressedScannerRowsWithInvalidByteSourceReject).get
      (by simpa using compressedScannerQuestionOpenFaultCapture_replaceable)

private theorem compressedScannerSaveFaultCapture_replaceable :
    (replaceCompressedScannerCapture? "save-fault" compressedSaveFaultRule
      compressedSaveFaultRuleWithSourceTheoremFaultReject
      compressedScannerRowsWithQuestionOpenFaultSourceReject).isSome = true := by
  decide +kernel

private def compressedScannerRowsWithSaveFaultSourceReject : List Atom :=
  (replaceCompressedScannerCapture? "save-fault" compressedSaveFaultRule
    compressedSaveFaultRuleWithSourceTheoremFaultReject
    compressedScannerRowsWithQuestionOpenFaultSourceReject).get
      (by simpa using compressedScannerSaveFaultCapture_replaceable)

private theorem compressedScannerIncompleteCapture_replaceable :
    (replaceCompressedScannerCapture? "incomplete" compressedIncompleteRule
      compressedIncompleteRuleWithSourceTheoremFaultReject
      compressedScannerRowsWithSaveFaultSourceReject).isSome = true := by
  decide +kernel

/-- Every static scanner route which can reintroduce a compact proof-fault
rule carries the same source-bound rejection continuation as the live finite
inventory. -/
def compressedScannerRuleCaptureRowsWithSourceFaultReject : List Atom :=
  (replaceCompressedScannerCapture? "incomplete" compressedIncompleteRule
    compressedIncompleteRuleWithSourceTheoremFaultReject
    compressedScannerRowsWithSaveFaultSourceReject).get
      (by simpa using compressedScannerIncompleteCapture_replaceable)

/-- The lookup service owns a second opaque route to the assertion launcher.
It is transformed through the same exact target-surface pass as the scanner
capture row, so the compact assertion boundary cannot reinstall the raw
launcher through a different verifier-owned continuation. -/
private def compressedAssertionLookupHandlerRow : Atom :=
  .expression
    [.symbol "mm-compressed-owned-lookup-handler", .symbol "assertion",
      compressedAssertionLaunchRule]

private def compressedAssertionLookupHandlerRowWithNormalBridge : Atom :=
  .expression
    [.symbol "mm-compressed-owned-lookup-handler", .symbol "assertion",
      compressedAssertionLaunchRuleWithNormalBridge]

private def compressedStaticRowsBeforeNormalBridge : List Atom :=
  compressedVerifierStaticRowsWithScannerCaptureRows
    compressedScannerRuleCaptureRowsWithNormalBridgeAndSourceVerdict

private theorem compressedAssertionLookupHandler_replaceable :
    (replaceMatching? compressedAssertionLookupHandlerRow
      compressedAssertionLookupHandlerRowWithNormalBridge
      compressedStaticRowsBeforeNormalBridge).isSome = true := by
  decide +kernel

/-- Static verifier data for the compact pipeline, with its assertion-launch
capture and lookup-handler routes both bound to the transformed handoff rule
rather than an unscoped raw execution shell. -/
def compressedVerifierStaticRowsWithNormalBridge : List Atom :=
  (replaceMatching? compressedAssertionLookupHandlerRow
    compressedAssertionLookupHandlerRowWithNormalBridge
    compressedStaticRowsBeforeNormalBridge).get
      (by simpa using compressedAssertionLookupHandler_replaceable)

private def compressedHeapLookupFaultHandlerRow : Atom :=
  .expression
    [.symbol "mm-compressed-owned-lookup-handler", .symbol "fault",
      compressedHeapLookupFaultRule]

private def compressedHeapLookupFaultHandlerRowWithSourceTheoremFaultReject :
    Atom :=
  .expression
    [.symbol "mm-compressed-owned-lookup-handler", .symbol "fault",
      compressedHeapLookupFaultRuleWithSourceTheoremFaultReject]

private theorem compressedHeapLookupFaultHandler_replaceable :
    (replaceMatching? compressedHeapLookupFaultHandlerRow
      compressedHeapLookupFaultHandlerRowWithSourceTheoremFaultReject
      compressedHeapLookupReloadRows).isSome = true := by
  decide +kernel

private def compressedHeapLookupReloadRowsWithSourceFaultReject : List Atom :=
  (replaceMatching? compressedHeapLookupFaultHandlerRow
    compressedHeapLookupFaultHandlerRowWithSourceTheoremFaultReject
    compressedHeapLookupReloadRows).get
      (by simpa using compressedHeapLookupFaultHandler_replaceable)

private theorem compressedHeapLookupAssertionHandler_replaceable :
    (replaceMatching? compressedAssertionLookupHandlerRow
      compressedAssertionLookupHandlerRowWithNormalBridge
      compressedHeapLookupReloadRowsWithSourceFaultReject).isSome = true := by
  decide +kernel

private def compressedHeapLookupReloadRowsWithNormalBridgeAndSourceFaultReject :
    List Atom :=
  (replaceMatching? compressedAssertionLookupHandlerRow
    compressedAssertionLookupHandlerRowWithNormalBridge
    compressedHeapLookupReloadRowsWithSourceFaultReject).get
      (by simpa using compressedHeapLookupAssertionHandler_replaceable)

/-- The compact static inventory is assembled from verifier-owned finite
families only.  Its two reload surfaces carry the same normal handoff and
fault-rejection transformations as the active rule presentation. -/
def compressedVerifierStaticRowsWithNormalBridgeAndSourceFaultReject :
    List Atom :=
  compressedVerifierStaticRowsWithReloadRows
    compressedHeapLookupReloadRowsWithNormalBridgeAndSourceFaultReject
    compressedScannerRuleCaptureRowsWithSourceFaultReject

/-- The narrow lookup-handler replacement is observable directly in the
transformed static inventory.  This says nothing about arbitrary hostile
MM2 input; it records only the verifier-generated presentation. -/
theorem compressedVerifierStaticRowsWithNormalBridge_lookup_handler_exact :
    compressedAssertionLookupHandlerRow ∉ compressedVerifierStaticRowsWithNormalBridge ∧
      compressedAssertionLookupHandlerRowWithNormalBridge ∈
        compressedVerifierStaticRowsWithNormalBridge := by
  decide +kernel

/-- One verifier-owned opaque row for a rule in the compact dispatch family. -/
def compressedDispatchRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-compressed-dispatch-rule", rule]

def compressedVerifierRulePresentation : FiniteVerifierRulePresentation where
  family := "compressed-verifier-rule"
  owner := compressedVerifierRuleOwner
  endTag := "mm-compressed-verifier-rule-end"
  rules := compressedHeaderRulesWithReloadAndSourceFaultReject ++
    compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject

def compressedVerifierRuleRows : List Atom :=
  compressedVerifierRulePresentation.rows

def compressedVerifierRuleEnd : Atom :=
  compressedVerifierRulePresentation.endRow

def compressedVerifierRuleRowTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row",
      stringAtom compressedVerifierRulePresentation.family,
      compressedVerifierRulePresentation.owner, .var "rule-position",
      .var "next-rule-position", .var "compressed-verifier-rule"]

private def compressedDispatchRuleRowTemplate : Atom :=
  .expression
    [.symbol "mm-internal-compressed-dispatch-rule",
      .var "compressed-verifier-rule"]

def compressedRuleNextLoadingTemplate : Atom :=
  .expression
    [.symbol "mm-source-compressed-rule-loading", .var "source",
      .var "position", sourceProofOwnerTemplate, headerControlTemplate,
      .var "next-rule-position"]

def compressedRuleLoadSelf : Atom :=
  .expression
    [.symbol "exec", loadLocation,
      .var "load-input", .var "load-output"]

def compressedRuleLoadPatterns : List Atom :=
  [compressedRuleLoadSelf, compressedRuleLoadingTemplate,
   compressedVerifierRuleRowTemplate]

def compressedRuleLoadSinks : List Sink :=
  [.add compressedRuleLoadSelf,
   .remove compressedRuleLoadingTemplate,
   .add compressedDispatchRuleRowTemplate,
   .add compressedRuleNextLoadingTemplate]

def sourceCompressedRuleLoadRule : Atom :=
  .expression
    [.symbol "exec", loadLocation, inputSurface compressedRuleLoadPatterns,
      outputSurface compressedRuleLoadSinks]

def sourceCompressedRuleLoadDirective : SourceExecFact where
  atom := sourceCompressedRuleLoadRule
  loc := loadLocation
  rule :=
    { priority := 4
      name := "mm-source-compressed-rule-load"
      input := .compat (mkPattern compressedRuleLoadPatterns)
      guards := []
      tmpl := mkTemplate compressedRuleLoadSinks }

theorem extract_sourceCompressedRuleLoadRule_exact :
    extractSupportedSourceExecFact sourceCompressedRuleLoadRule =
      some sourceCompressedRuleLoadDirective := by
  rfl

private def ruleEndTemplate : Atom :=
  .expression
    [.symbol compressedVerifierRulePresentation.endTag,
      .var "rule-position"]

private def finishSelf : Atom :=
  .expression
    [.symbol "exec", finishLocation,
      .var "finish-input", .var "finish-output"]

private def finishPatterns : List Atom :=
  [finishSelf, compressedRuleLoadingTemplate, ruleEndTemplate]

private def finishSinks : List Sink :=
  [.add finishSelf,
   .remove compressedRuleLoadingTemplate,
   .add headerControlTemplate,
   .add sourceCompressedDispatchReloadTemplate]

def sourceCompressedRuleFinishRule : Atom :=
  .expression
    [.symbol "exec", finishLocation, inputSurface finishPatterns,
      outputSurface finishSinks]

private theorem sourceCompressedRuleFinishRule_rearmable :
    (appendCapturedRuleSink? compressedDispatchReloadCaptureTemplate
      compressedDispatchReloadCaptureVariable
      sourceCompressedRuleFinishRule).isSome = true := by
  decide +kernel

/-- Releasing the initial compact header cursor also releases exactly one
low-priority dispatch continuation.  The continuation is opaque verifier code,
not source proof data, and so cannot be consumed before this transition. -/
def sourceCompressedRuleFinishRuleWithDispatchReload : Atom :=
  (appendCapturedRuleSink? compressedDispatchReloadCaptureTemplate
    compressedDispatchReloadCaptureVariable
    sourceCompressedRuleFinishRule).get
      (by simpa using sourceCompressedRuleFinishRule_rearmable)

def sourceCompressedRuleFinishDirective : SourceExecFact where
  atom := sourceCompressedRuleFinishRuleWithDispatchReload
  loc := finishLocation
  rule :=
    { priority := 5
      name := "mm-source-compressed-rule-finish"
      input := .compat (mkPattern
        (finishPatterns ++ [compressedDispatchReloadCaptureTemplate]))
      guards := []
      tmpl := mkTemplate
        (finishSinks ++ [.add compressedDispatchReloadCaptureVariable]) }

theorem extract_sourceCompressedRuleFinishRule_exact :
    extractSupportedSourceExecFact sourceCompressedRuleFinishRuleWithDispatchReload =
      some sourceCompressedRuleFinishDirective := by
  rfl

/-! ### Volatile compact-rule reinstallation -/

/-- Location of the bootstrap dispatcher that consumes an owner-bound reload
request and reinstalls one verifier-owned compact rule. -/
private def compressedDispatchReloadLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-compressed-dispatch-reload"]

private def compressedDispatchReloadSelf : Atom :=
  .expression
    [.symbol "exec", compressedDispatchReloadLocation,
      .var "compressed-reload-input", .var "compressed-reload-output"]

private def compressedDispatchReloadPatterns : List Atom :=
  [compressedDispatchReloadSelf, compressedDispatchReloadTemplate,
   compressedDispatchRuleRowTemplate]

private def compressedDispatchReloadSinks : List Sink :=
  [.remove compressedDispatchReloadTemplate,
   .add (.var "compressed-verifier-rule")]

/-- Reinstall one verifier-owned compact rule after a decorated rule reports
its owner-bound reload request.  The source data contains only the opaque row;
it never constructs an executable rule shell. -/
def compressedDispatchReloadRule : Atom :=
  .expression
    [.symbol "exec", compressedDispatchReloadLocation,
      inputSurface compressedDispatchReloadPatterns,
      outputSurface compressedDispatchReloadSinks]

def compressedDispatchReloadDirective : SourceExecFact where
  atom := compressedDispatchReloadRule
  loc := compressedDispatchReloadLocation
  rule :=
    { priority := 0
      name := "mm-compressed-dispatch-reload"
      input := .compat (mkPattern compressedDispatchReloadPatterns)
      guards := []
      tmpl := mkTemplate compressedDispatchReloadSinks }

theorem extract_compressedDispatchReloadRule_exact :
    extractSupportedSourceExecFact compressedDispatchReloadRule =
      some compressedDispatchReloadDirective := by
  rfl

/-- Passive verifier-owned code row for the dynamic compact dispatcher.  The
row alone is inert; a transformed compact transition must capture it before an
ordinary MM2 `exec` is made available. -/
def compressedDispatchReloadCaptureRow : Atom :=
  .expression [.symbol "mm-internal-compressed-dispatch-reload",
    compressedDispatchReloadRule]

def compressedOrderedActivationRules : List Atom :=
  [sourceCompressedProofActivateRule, sourceCompressedRuleLoadRule,
   sourceCompressedRuleFinishRuleWithDispatchReload]

def compressedOrderedActivationDirectives : List SourceExecFact :=
  [sourceCompressedProofActivateDirective,
   sourceCompressedRuleLoadDirective,
   sourceCompressedRuleFinishDirective]

theorem compressedOrderedActivationRules_extract_exact :
    compressedOrderedActivationRules.filterMap extractSupportedSourceExecFact =
      compressedOrderedActivationDirectives := by
  rfl

/-- Complete generated-input extension. Rule values and static classifier
rows are verifier-owned; source data supplies only the wrapped header cursor. -/
def compressedOrderedVerifierExtensionProgram : List Atom :=
  compressedOrderedActivationRules ++ compressedVerifierRuleRows ++
    [compressedVerifierRuleEnd] ++
      compressedVerifierStaticRowsWithNormalBridgeAndSourceFaultReject ++
      compressedNormalHandoffRuleRows ++ [compressedNormalHandoffRuleEnd] ++
        compressedNormalDispatchBridgeRows ++ [compressedDispatchReloadCaptureRow]

#print axioms extract_sourceCompressedProofActivateRule_exact
#print axioms extract_sourceCompressedRuleLoadRule_exact
#print axioms extract_sourceCompressedRuleFinishRule_exact
#print axioms extract_compressedDispatchReloadRule_exact
#print axioms compressedOrderedActivationRules_extract_exact
#print axioms extract_compressedNormalDispatchBridgeRule_exact
#print axioms compressedNormalDispatchBridgeRule_exec_shape
#print axioms compressedNormalDispatchBridgeRule_head_shape
#print axioms compressedNormalDispatchBridge_before_assertionRejoin
#print axioms compressedAssertionLaunchRuleWithNormalBridge_build_exact
#print axioms compressedAssertionLaunchRuleWithNormalBridge_exec_shape
#print axioms compressedBodyRulesWithNormalBridgeAndSourceVerdictAndFaultReject_assertion_at
#print axioms compressedVerifierStaticRowsWithNormalBridge_lookup_handler_exact
#print axioms compressedHeaderRearmArtifact_sourceRules
#print axioms compressedHeaderRulesWithReload_length
#print axioms compressedNormalRearmArtifact_sourceRules
#print axioms compressedNormalHandoffSourceRules_no_ordinary_reload
#print axioms compressedNormalHandoffSourceRulesWithoutOrdinaryReload_length
#print axioms compressedNormalHandoffRules_length
#print axioms FiniteVerifierRulePresentation.rows_length
#print axioms FiniteVerifierRulePresentation.mem_rows_iff
#print axioms FiniteVerifierRulePresentation.reifiedRuleArtifact_source
#print axioms FiniteVerifierRulePresentation.reifiedRuleArtifact_decodes
#print axioms FiniteVerifierRulePresentation.reifiedRuleArtifact_target_length
#print axioms FiniteVerifierRulePresentation.loaderTerminal_loaded
#print axioms FiniteVerifierRulePresentation.loaderTerminal_ne_of_rules_ne
#print axioms FiniteVerifierRulePresentation.linkedLowering
#print axioms FiniteVerifierRulePresentation.linkedLoaderPath_length
#print axioms FiniteVerifierRulePresentation.row_witnesses_abstract_step
#print axioms FiniteVerifierRulePresentation.row_witnesses_linked_step
#print axioms FiniteVerifierRulePresentation.endRow_marks_terminal_cursor
#print axioms FiniteVerifierRulePresentation.endRow_marks_linked_terminal_cursor

end Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
