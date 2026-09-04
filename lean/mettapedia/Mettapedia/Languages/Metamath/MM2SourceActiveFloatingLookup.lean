import Mettapedia.Languages.Metamath.MM2SourceDVPairValidation

/-!
# Active floating-hypothesis lookup in ordinary MM2

The scoped active-hypothesis ledger already retains each exact proof-runtime
row so scope exit can retract it.  This module walks that same linked ledger by
variable name.  It does not introduce a second active-frame authority.

Lookup controls and observations are verifier-owned.  The candidate retains
its source occurrence, while equality is decided by the encoded variable name
inside an exact floating-hypothesis runtime row.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceActiveFloatingLookup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2OrderedEventVerifier
open Mettapedia.Languages.Metamath.MM2SourceEventTransformation
open Mettapedia.Languages.Metamath.MM2SourceObjectLookup
open Mettapedia.Languages.Metamath.MM2SourceScopeExecution
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

/-! ## Owner-bound controls -/

def activeFloatingLookupAtom (owner request : Atom)
    (candidate : LocatedName) (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-lookup", owner, request,
      locatedNameAtom candidate, cursor, frontier]

def activeFloatingFoundAtom (owner request : Atom)
    (candidate : LocatedName) (runtimeRow : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-found", owner, request,
      locatedNameAtom candidate, runtimeRow]

def activeFloatingMissingAtom (owner request : Atom)
    (candidate : LocatedName) : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-missing", owner, request,
      locatedNameAtom candidate]

@[simp] theorem activeFloatingLookupAtom_not_proofNeutral
    (owner request : Atom) (candidate : LocatedName) (cursor frontier : Atom) :
    isProofNeutralInitialAtom
      (activeFloatingLookupAtom owner request candidate cursor frontier) =
        false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-active-floating-lookup"
    [owner, request, locatedNameAtom candidate, cursor, frontier] (by decide)

@[simp] theorem activeFloatingFoundAtom_not_proofNeutral
    (owner request : Atom) (candidate : LocatedName) (runtimeRow : Atom) :
    isProofNeutralInitialAtom
      (activeFloatingFoundAtom owner request candidate runtimeRow) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-active-floating-found"
    [owner, request, locatedNameAtom candidate, runtimeRow] (by decide)

/-! ## Linked scan -/

private def hitLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-source-active-floating-hit"]
private def missingLocation : Atom :=
  .expression [.symbol "01", .symbol "mm-source-active-floating-missing"]
private def advanceLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-source-active-floating-advance"]
private def reloadLocation : Atom :=
  .expression [.symbol "35", .symbol "mm-source-active-floating-reload"]

private def candidateTemplate : Atom :=
  .expression
    [.symbol "mm-source-name", .var "candidate-span",
      .var "candidate-name"]

private def lookupTemplate (cursor frontier : Atom) : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-lookup", .var "source",
      .var "request", candidateTemplate, cursor, frontier]

private def lookupAtCursorTemplate : Atom :=
  lookupTemplate (.var "cursor") (.var "frontier")

private def lookupAtFrontierTemplate : Atom :=
  lookupTemplate (.var "frontier") (.var "frontier")

private def activeOwnerTemplate : Atom :=
  .expression [.symbol "mm-source-active-hypothesis-ledger", .var "source"]

private def floatingRuntimeTemplate : Atom :=
  .expression
    [.symbol "mm-hypothesis-lookup", .var "source",
      .var "floating-label",
      .expression
        [.symbol "mm-formula", .var "floating-typecode",
          .expression
            [.symbol "mm-cons",
              .expression
                [.symbol "mm-variable", .var "candidate-name"],
              .expression [.symbol "mm-nil"]]]]

private def floatingHypothesisTemplate : Atom :=
  .expression
    [.symbol "mm-floating", .var "floating-label",
      .var "floating-typecode", .var "candidate-name"]

private def matchingLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-active-hypothesis-link", activeOwnerTemplate,
      .var "cursor", .var "next-cursor", floatingHypothesisTemplate,
      floatingRuntimeTemplate]

private def anyLinkTemplate : Atom :=
  .expression
    [.symbol "mm-source-active-hypothesis-link", activeOwnerTemplate,
      .var "cursor", .var "next-cursor", .var "encoded-hypothesis",
      .var "hypothesis-runtime-row"]

private def frontierTemplate : Atom :=
  .expression
    [.symbol "mm-source-activity-frontier", activeOwnerTemplate,
      .var "frontier"]

private def foundTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-found", .var "source",
      .var "request", candidateTemplate, floatingRuntimeTemplate]

private def missingTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-missing", .var "source",
      .var "request", candidateTemplate]

private def nextLookupTemplate : Atom :=
  lookupTemplate (.var "next-cursor") (.var "frontier")

private def reloadTriggerTemplate : Atom :=
  .expression [.symbol "mm-reload-source-active-floating", .var "source"]

def activeFloatingReloadTriggerAtom (owner : Atom) : Atom :=
  .expression [.symbol "mm-reload-source-active-floating", owner]

private def selfTemplate (loc : Atom) (stem : String) : Atom :=
  .expression
    [.symbol "exec", loc, .var (stem ++ "-input"),
      .var (stem ++ "-output")]

private def sinkAtom : Sink → Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom => .expression [.symbol "head", natAtom count, atom]
  | .tail count atom => .expression [.symbol "tail", natAtom count, atom]

private def mkRule (loc : Atom) (patterns : List Atom)
    (sinks : List Sink) : Atom :=
  .expression
    [.symbol "exec", loc, .expression (.symbol "," :: patterns),
      .expression (.symbol "O" :: sinks.map sinkAtom)]

private def mkCompatDirective (atom loc : Atom) (priority : Nat)
    (name : String) (patterns : List Atom) (sinks : List Sink) :
    SourceExecFact :=
  { atom
    loc
    rule :=
      { priority
        name
        input := .compat (mkPattern patterns)
        guards := []
        tmpl := mkTemplate sinks } }

private def hitSelf : Atom := selfTemplate hitLocation "active-floating-hit"
private def hitPatterns : List Atom :=
  [hitSelf, lookupAtCursorTemplate, matchingLinkTemplate]
private def hitSinks : List Sink :=
  [.add hitSelf, .remove lookupAtCursorTemplate, .add foundTemplate]

def activeFloatingHitRule : Atom := mkRule hitLocation hitPatterns hitSinks
def activeFloatingHitDirective : SourceExecFact :=
  mkCompatDirective activeFloatingHitRule hitLocation 0
    "mm-source-active-floating-hit" hitPatterns hitSinks

private def missingSelf : Atom :=
  selfTemplate missingLocation "active-floating-missing"
private def missingPatterns : List Atom :=
  [missingSelf, lookupAtFrontierTemplate, frontierTemplate]
private def missingSinks : List Sink :=
  [.add missingSelf, .remove lookupAtFrontierTemplate,
    .add missingTemplate]

def activeFloatingMissingRule : Atom :=
  mkRule missingLocation missingPatterns missingSinks
def activeFloatingMissingDirective : SourceExecFact :=
  mkCompatDirective activeFloatingMissingRule missingLocation 1
    "mm-source-active-floating-missing" missingPatterns missingSinks

private def advanceSelf : Atom :=
  selfTemplate advanceLocation "active-floating-advance"
private def advancePatterns : List Atom :=
  [advanceSelf, lookupAtCursorTemplate, anyLinkTemplate]
private def advanceSinks : List Sink :=
  [.remove lookupAtCursorTemplate, .add nextLookupTemplate,
    .add reloadTriggerTemplate]

def activeFloatingAdvanceRule : Atom :=
  mkRule advanceLocation advancePatterns advanceSinks
def activeFloatingAdvanceDirective : SourceExecFact :=
  mkCompatDirective activeFloatingAdvanceRule advanceLocation 2
    "mm-source-active-floating-advance" advancePatterns advanceSinks

theorem extract_activeFloatingHitRule_exact :
    extractSupportedSourceExecFact activeFloatingHitRule =
      some activeFloatingHitDirective := by rfl
theorem extract_activeFloatingMissingRule_exact :
    extractSupportedSourceExecFact activeFloatingMissingRule =
      some activeFloatingMissingDirective := by rfl
theorem extract_activeFloatingAdvanceRule_exact :
    extractSupportedSourceExecFact activeFloatingAdvanceRule =
      some activeFloatingAdvanceDirective := by rfl

def activeFloatingScanRules : List Atom :=
  [activeFloatingHitRule, activeFloatingMissingRule,
    activeFloatingAdvanceRule]
def activeFloatingScanDirectives : List SourceExecFact :=
  [activeFloatingHitDirective, activeFloatingMissingDirective,
    activeFloatingAdvanceDirective]

def activeFloatingRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-source-active-floating-rule", rule]

@[simp] theorem activeFloatingRuleRow_not_proofNeutral (rule : Atom) :
    isProofNeutralInitialAtom (activeFloatingRuleRow rule) = false := by
  exact verifier_owned_internal_prefix_not_proofNeutral
    "mm-internal-source-active-floating-rule" [rule] (by decide)

def activeFloatingStaticRows : List Atom :=
  activeFloatingScanRules.map activeFloatingRuleRow

private def reloadSelf : Atom :=
  selfTemplate reloadLocation "active-floating-reload"
private def reloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-source-active-floating-rule",
      .var "active-floating-rule"]
private def reloadPatterns : List Atom :=
  [reloadSelf, reloadTriggerTemplate, reloadRuleTemplate]
private def reloadSinks : List Sink :=
  [.add reloadSelf, .remove reloadTriggerTemplate,
    .add (.var "active-floating-rule")]

def activeFloatingReloadRule : Atom :=
  mkRule reloadLocation reloadPatterns reloadSinks
def activeFloatingReloadDirective : SourceExecFact :=
  mkCompatDirective activeFloatingReloadRule reloadLocation 35
    "mm-source-active-floating-reload" reloadPatterns reloadSinks

theorem extract_activeFloatingReloadRule_exact :
    extractSupportedSourceExecFact activeFloatingReloadRule =
      some activeFloatingReloadDirective := by rfl

def activeFloatingRules : List Atom :=
  activeFloatingScanRules ++ [activeFloatingReloadRule]
def activeFloatingDirectives : List SourceExecFact :=
  activeFloatingScanDirectives ++ [activeFloatingReloadDirective]

theorem activeFloatingRules_extract_exact :
    activeFloatingRules.filterMap extractSupportedSourceExecFact =
      activeFloatingDirectives := by rfl

/-! ## Bounded positive and negative controls -/

private def fixtureOwner : Atom := .symbol "active-floating-source"
private def fixtureRequest : Atom := .symbol "endpoint-request"
private def fixtureSpan (start stop : Nat) : LocatedByteSpan :=
  { fileId := "active-floating.mm", start, stop }
private def xName : LocatedName :=
  { span := fixtureSpan 10 11, name := "x" }
private def yName : LocatedName :=
  { span := fixtureSpan 12 13, name := "y" }
private def floating : HypothesisView := .floating "wx" "wff" "x"
private def runtimeRow : Atom := hypothesisLookupRow fixtureOwner floating
private def nextCursor : Atom :=
  .expression [.symbol "source-hypothesis-occurrence", natAtom 4]

private def hitCanaryAtoms : List Atom :=
  [activeFloatingHitRule,
    activeFloatingLookupAtom fixtureOwner fixtureRequest xName objectRootKey
      nextCursor,
    activeHypothesisLinkAtom fixtureOwner objectRootKey nextCursor floating]
private def hitCanarySpace : Space := hitCanaryAtoms.toFinset
private theorem hitCanaryAtoms_nodup : hitCanaryAtoms.Nodup := by
  decide +kernel
private theorem hitCanaryAtoms_supported :
    cSupportedSourceExecFacts hitCanaryAtoms =
      [activeFloatingHitDirective] := by rfl
theorem hitCanary_selects_directive :
    selectNextScheduled (supportedSourceExecFactsOfSpace hitCanarySpace) =
      some activeFloatingHitDirective := by
  exact reflective_selects_of_computable_supported_singleton
    hitCanaryAtoms activeFloatingHitDirective hitCanaryAtoms_nodup
    hitCanaryAtoms_supported
private theorem hitCanary_fire_agreement :
    (cFireReflectiveSourceExecFact hitCanaryAtoms
        activeFloatingHitDirective).toFinset =
      fireReflectiveSourceExecFact hitCanarySpace
        activeFloatingHitDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    hitCanaryAtoms activeFloatingHitDirective hitCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      activeFloatingHitDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      hitCanaryAtoms activeFloatingHitDirective hitCanaryAtoms_nodup)

theorem hitCanary_finds_exact_runtime_row :
    activeFloatingFoundAtom fixtureOwner fixtureRequest xName runtimeRow ∈
      fireReflectiveSourceExecFact hitCanarySpace
        activeFloatingHitDirective := by
  rw [← hitCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

theorem hitCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies hitCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact hitCanarySpace
          activeFloatingHitDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected hitCanary_selects_directive)

private def missingCanaryAtoms : List Atom :=
  [activeFloatingMissingRule,
    activeFloatingLookupAtom fixtureOwner fixtureRequest yName nextCursor
      nextCursor,
    sourceActivityFrontierAtom (activeHypothesisLedgerOwner fixtureOwner)
      nextCursor]
private def missingCanarySpace : Space := missingCanaryAtoms.toFinset
private theorem missingCanaryAtoms_nodup : missingCanaryAtoms.Nodup := by
  decide +kernel
private theorem missingCanaryAtoms_supported :
    cSupportedSourceExecFacts missingCanaryAtoms =
      [activeFloatingMissingDirective] := by rfl
private theorem missingCanary_fire_agreement :
    (cFireReflectiveSourceExecFact missingCanaryAtoms
        activeFloatingMissingDirective).toFinset =
      fireReflectiveSourceExecFact missingCanarySpace
        activeFloatingMissingDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    missingCanaryAtoms activeFloatingMissingDirective missingCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      activeFloatingMissingDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      missingCanaryAtoms activeFloatingMissingDirective
      missingCanaryAtoms_nodup)

theorem missingCanary_emits_exact_missing_observation :
    activeFloatingMissingAtom fixtureOwner fixtureRequest yName ∈
      fireReflectiveSourceExecFact missingCanarySpace
        activeFloatingMissingDirective := by
  rw [← missingCanary_fire_agreement]
  exact List.mem_toFinset.mpr (by decide +kernel)

private def wrongVariableCanaryAtoms : List Atom :=
  [activeFloatingHitRule,
    activeFloatingLookupAtom fixtureOwner fixtureRequest yName
      objectRootKey nextCursor,
    activeHypothesisLinkAtom fixtureOwner objectRootKey nextCursor floating]
private def wrongVariableCanarySpace : Space :=
  wrongVariableCanaryAtoms.toFinset
private theorem wrongVariableCanaryAtoms_nodup :
    wrongVariableCanaryAtoms.Nodup := by decide +kernel
private theorem wrongVariableCanary_fire_agreement :
    (cFireReflectiveSourceExecFact wrongVariableCanaryAtoms
        activeFloatingHitDirective).toFinset =
      fireReflectiveSourceExecFact wrongVariableCanarySpace
        activeFloatingHitDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    wrongVariableCanaryAtoms activeFloatingHitDirective
    wrongVariableCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      activeFloatingHitDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      wrongVariableCanaryAtoms activeFloatingHitDirective
      wrongVariableCanaryAtoms_nodup)

theorem hitRule_cannot_masquerade_different_variable :
    activeFloatingFoundAtom fixtureOwner fixtureRequest yName runtimeRow ∉
      fireReflectiveSourceExecFact wrongVariableCanarySpace
        activeFloatingHitDirective := by
  rw [← wrongVariableCanary_fire_agreement]
  simpa using (show
    activeFloatingFoundAtom fixtureOwner fixtureRequest yName runtimeRow ∉
      (cFireReflectiveSourceExecFact wrongVariableCanaryAtoms
        activeFloatingHitDirective).toFinset by decide +kernel)

/-! An essential hypothesis may project to the same runtime formula row as a
floating hypothesis.  The semantic hypothesis retained in the active ledger
prevents that lossy projection from manufacturing floating-variable evidence. -/

private def sameRuntimeEssential : HypothesisView :=
  .essential "wx" { typecode := "wff", body := [.var "x"] }

private theorem sameRuntimeEssential_runtimeRow_eq :
    hypothesisLookupRow fixtureOwner sameRuntimeEssential = runtimeRow := by
  rfl

private def essentialMasqueradeCanaryAtoms : List Atom :=
  [activeFloatingHitRule,
    activeFloatingLookupAtom fixtureOwner fixtureRequest xName objectRootKey
      nextCursor,
    activeHypothesisLinkAtom fixtureOwner objectRootKey nextCursor
      sameRuntimeEssential]

private def essentialMasqueradeCanarySpace : Space :=
  essentialMasqueradeCanaryAtoms.toFinset

private theorem essentialMasqueradeCanaryAtoms_nodup :
    essentialMasqueradeCanaryAtoms.Nodup := by
  decide +kernel

private theorem essentialMasqueradeCanary_fire_agreement :
    (cFireReflectiveSourceExecFact essentialMasqueradeCanaryAtoms
        activeFloatingHitDirective).toFinset =
      fireReflectiveSourceExecFact essentialMasqueradeCanarySpace
        activeFloatingHitDirective := by
  exact reflectiveSourceFiringAgreement_of_supportAlignment
    essentialMasqueradeCanaryAtoms activeFloatingHitDirective
    essentialMasqueradeCanaryAtoms_nodup
    ((all_reflectiveSupportSetSinkB_eq_true_iff
      activeFloatingHitDirective.rule.tmpl).1 (by decide +kernel))
    (reflectiveSourceRowSupportAlignment_of_nodup
      essentialMasqueradeCanaryAtoms activeFloatingHitDirective
      essentialMasqueradeCanaryAtoms_nodup)

theorem hitRule_cannot_masquerade_essential_with_same_runtime_row :
    activeFloatingFoundAtom fixtureOwner fixtureRequest xName runtimeRow ∉
      fireReflectiveSourceExecFact essentialMasqueradeCanarySpace
        activeFloatingHitDirective := by
  rw [← essentialMasqueradeCanary_fire_agreement]
  simpa [sameRuntimeEssential_runtimeRow_eq] using (show
    activeFloatingFoundAtom fixtureOwner fixtureRequest xName runtimeRow ∉
      (cFireReflectiveSourceExecFact essentialMasqueradeCanaryAtoms
        activeFloatingHitDirective).toFinset by decide +kernel)

section AxiomAudit

#print axioms activeFloatingLookupAtom_not_proofNeutral
#print axioms activeFloatingFoundAtom_not_proofNeutral
#print axioms extract_activeFloatingHitRule_exact
#print axioms extract_activeFloatingMissingRule_exact
#print axioms extract_activeFloatingAdvanceRule_exact
#print axioms extract_activeFloatingReloadRule_exact
#print axioms activeFloatingRules_extract_exact
#print axioms activeFloatingRuleRow_not_proofNeutral
#print axioms hitCanary_selects_directive
#print axioms hitCanary_finds_exact_runtime_row
#print axioms hitCanary_inhabits_target_native_type
#print axioms missingCanary_emits_exact_missing_observation
#print axioms hitRule_cannot_masquerade_different_variable
#print axioms hitRule_cannot_masquerade_essential_with_same_runtime_row

end AxiomAudit

end Mettapedia.Languages.Metamath.MM2SourceActiveFloatingLookup
