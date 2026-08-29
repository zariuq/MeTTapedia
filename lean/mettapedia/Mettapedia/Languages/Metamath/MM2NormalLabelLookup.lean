import Mettapedia.Languages.Metamath.MM2NormalLabelInventory
import Mettapedia.Languages.Metamath.MM2SourceActionExecution

/-!
# Finite normal-label lookup in ordinary MM2

The normal verifier first tries its positive active-hypothesis and assertion
rules.  If neither applies, this extension scans the exact finite label
inventory emitted for the theorem occurrence.  Equality is handled by an
earlier exact-match rule; the later advance rule therefore needs no negative
oracle.  Reaching the explicit frontier produces `undefined-label` rather
than leaving a silent residual control state.

The inventory and its termination theorem come from
`FiniteOccurrenceLookup`; this file supplies only the ordinary-MM2
realization and its extraction boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2NormalLabelLookup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2NormalLabelInventory
open Mettapedia.Languages.Metamath.MM2SourceActionExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private def normalLabelLookupStartLocation : Atom :=
  .expression [.symbol "34", .symbol "mm-normal-label-lookup-start"]

private def normalLabelLookupHitLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-normal-label-lookup-hit"]

private def normalLabelLookupMissingLocation : Atom :=
  .expression [.symbol "01", .symbol "mm-normal-label-lookup-missing"]

private def normalLabelLookupAdvanceLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-normal-label-lookup-advance"]

private def normalLabelLookupReloadLocation : Atom :=
  .expression [.symbol "35", .symbol "mm-normal-label-lookup-reload"]

private def normalControlTemplate : Atom :=
  .expression
    [.symbol "mm-normal-control", .var "scope", .var "proof",
      .var "pc", .var "top"]

private def normalProofLabelTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-proof-label",
      .var "proof", .var "pc", .var "next-pc", .var "label"]

private def normalLabelFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-normal-label-frontier", .var "proof", .var "frontier"]

private def normalLabelLookupTemplate : Atom :=
  .expression
    [.symbol "mm-normal-label-lookup", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "top", .var "label",
      .var "cursor", .var "frontier"]

private def normalLabelLookupInitialTemplate : Atom :=
  .expression
    [.symbol "mm-normal-label-lookup", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "top", .var "label",
      natAtom 0, .var "frontier"]

private def normalLabelLookupReloadTriggerTemplate : Atom :=
  .expression
    [.symbol "mm-reload-normal-label-lookup", .var "proof"]

private def normalLabelCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-label-candidate",
      .var "proof", .var "cursor", .var "next-cursor",
      .expression
        [.symbol "mm-normal-label-entry", .var "candidate-label",
          .var "candidate-kind"]]

private def normalLabelMatchingCandidateTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "normal-label-candidate",
      .var "proof", .var "cursor", .var "next-cursor",
      .expression
        [.symbol "mm-normal-label-entry", .var "label",
          .var "candidate-kind"]]

private def normalLabelLookupNextTemplate : Atom :=
  .expression
    [.symbol "mm-normal-label-lookup", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "top", .var "label",
      .var "next-cursor", .var "frontier"]

/-! ## Fallback activation -/

private def normalLabelLookupStartPatternAtoms : List Atom :=
  [normalControlTemplate, normalProofLabelTemplate, normalLabelFrontierTemplate]

private def normalLabelLookupStartInput : Atom :=
  .expression (.symbol "," :: normalLabelLookupStartPatternAtoms)

private def normalLabelLookupStartSinks : List Sink :=
  [.remove normalControlTemplate,
   .add normalLabelLookupInitialTemplate,
   .add normalLabelLookupReloadTriggerTemplate]

private def normalLabelLookupStartOutput : Atom :=
  .expression
    [.symbol "O",
      .expression [.symbol "-", normalControlTemplate],
      .expression [.symbol "+", normalLabelLookupInitialTemplate],
      .expression [.symbol "+", normalLabelLookupReloadTriggerTemplate]]

/-- Enter finite lookup only after the ordinary positive dispatch rules and
terminal observer have failed to match the current normal token. -/
def normalLabelLookupStartRule : Atom :=
  .expression
    [.symbol "exec", normalLabelLookupStartLocation,
      normalLabelLookupStartInput, normalLabelLookupStartOutput]

def normalLabelLookupStartDirective : SourceExecFact where
  atom := normalLabelLookupStartRule
  loc := normalLabelLookupStartLocation
  rule :=
    { priority := 34
      name := "mm-normal-label-lookup-start"
      input := .compat (mkPattern normalLabelLookupStartPatternAtoms)
      guards := []
      tmpl := mkTemplate normalLabelLookupStartSinks }

theorem extract_normalLabelLookupStartRule_exact :
    extractSupportedSourceExecFact normalLabelLookupStartRule =
      some normalLabelLookupStartDirective := by
  rfl

/-! ## Exact hit and explicit missing observations -/

private def normalLabelLookupHitPatternAtoms : List Atom :=
  [normalLabelLookupTemplate, normalLabelMatchingCandidateTemplate]

private def normalLabelLookupHitFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope", .var "proof", .var "pc",
      .symbol "normal-label-catalog-dispatch-mismatch", .var "label",
      .var "label", .var "candidate-kind"]

private def normalLabelLookupHitSinks : List Sink :=
  [.remove normalLabelLookupTemplate,
   .add normalLabelLookupHitFaultTemplate]

/-- A catalog hit after positive dispatch failed is an internal
source/realization mismatch, never evidence that the submitted token is
undefined. -/
def normalLabelLookupHitRule : Atom :=
  .expression
    [.symbol "exec", normalLabelLookupHitLocation,
      .expression (.symbol "," :: normalLabelLookupHitPatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "-", normalLabelLookupTemplate],
          .expression [.symbol "+", normalLabelLookupHitFaultTemplate]]]

def normalLabelLookupHitDirective : SourceExecFact where
  atom := normalLabelLookupHitRule
  loc := normalLabelLookupHitLocation
  rule :=
    { priority := 0
      name := "mm-normal-label-lookup-hit"
      input := .compat (mkPattern normalLabelLookupHitPatternAtoms)
      guards := []
      tmpl := mkTemplate normalLabelLookupHitSinks }

theorem extract_normalLabelLookupHitRule_exact :
    extractSupportedSourceExecFact normalLabelLookupHitRule =
      some normalLabelLookupHitDirective := by
  rfl

private def normalLabelLookupAtFrontierTemplate : Atom :=
  .expression
    [.symbol "mm-normal-label-lookup", .var "scope", .var "proof",
      .var "pc", .var "next-pc", .var "top", .var "label",
      .var "frontier", .var "frontier"]

private def normalLabelLookupMissingFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope", .var "proof", .var "pc",
      .symbol "undefined-label", .var "label", .var "label",
      .var "frontier"]

private def normalLabelLookupMissingPatternAtoms : List Atom :=
  [normalLabelLookupAtFrontierTemplate]

private def normalLabelLookupMissingSinks : List Sink :=
  [.remove normalLabelLookupAtFrontierTemplate,
   .add normalLabelLookupMissingFaultTemplate]

/-- Absence is observed only when the cursor equals the explicit finite
frontier supplied by the source-derived inventory. -/
def normalLabelLookupMissingRule : Atom :=
  .expression
    [.symbol "exec", normalLabelLookupMissingLocation,
      .expression (.symbol "," :: normalLabelLookupMissingPatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "-", normalLabelLookupAtFrontierTemplate],
          .expression [.symbol "+", normalLabelLookupMissingFaultTemplate]]]

def normalLabelLookupMissingDirective : SourceExecFact where
  atom := normalLabelLookupMissingRule
  loc := normalLabelLookupMissingLocation
  rule :=
    { priority := 1
      name := "mm-normal-label-lookup-missing"
      input := .compat (mkPattern normalLabelLookupMissingPatternAtoms)
      guards := []
      tmpl := mkTemplate normalLabelLookupMissingSinks }

theorem extract_normalLabelLookupMissingRule_exact :
    extractSupportedSourceExecFact normalLabelLookupMissingRule =
      some normalLabelLookupMissingDirective := by
  rfl

/-! ## Cursor advance and finite rule reinstallation -/

private def normalLabelLookupAdvancePatternAtoms : List Atom :=
  [normalLabelLookupTemplate, normalLabelCandidateTemplate]

private def normalLabelLookupAdvanceSinks : List Sink :=
  [.remove normalLabelLookupTemplate,
   .add normalLabelLookupNextTemplate,
   .add normalLabelLookupReloadTriggerTemplate]

/-- Advance follows only the explicit successor in the current linked source
occurrence.  The earlier exact-hit rule wins whenever the labels agree. -/
def normalLabelLookupAdvanceRule : Atom :=
  .expression
    [.symbol "exec", normalLabelLookupAdvanceLocation,
      .expression (.symbol "," :: normalLabelLookupAdvancePatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "-", normalLabelLookupTemplate],
          .expression [.symbol "+", normalLabelLookupNextTemplate],
          .expression [.symbol "+", normalLabelLookupReloadTriggerTemplate]]]

def normalLabelLookupAdvanceDirective : SourceExecFact where
  atom := normalLabelLookupAdvanceRule
  loc := normalLabelLookupAdvanceLocation
  rule :=
    { priority := 2
      name := "mm-normal-label-lookup-advance"
      input := .compat (mkPattern normalLabelLookupAdvancePatternAtoms)
      guards := []
      tmpl := mkTemplate normalLabelLookupAdvanceSinks }

theorem extract_normalLabelLookupAdvanceRule_exact :
    extractSupportedSourceExecFact normalLabelLookupAdvanceRule =
      some normalLabelLookupAdvanceDirective := by
  rfl

def normalLabelLookupRuleRow (rule : Atom) : Atom :=
  .expression [.symbol "mm-internal-normal-label-lookup-rule", rule]

private def normalLabelLookupReloadSelfTemplate : Atom :=
  .expression
    [.symbol "exec", normalLabelLookupReloadLocation,
      .var "lookup-reload-input", .var "lookup-reload-output"]

private def normalLabelLookupReloadRuleTemplate : Atom :=
  .expression
    [.symbol "mm-internal-normal-label-lookup-rule",
      .var "lookup-rule"]

private def normalLabelLookupReloadPatternAtoms : List Atom :=
  [normalLabelLookupReloadSelfTemplate,
   normalLabelLookupReloadTriggerTemplate,
   normalLabelLookupReloadRuleTemplate]

private def normalLabelLookupReloadSinks : List Sink :=
  [.add normalLabelLookupReloadSelfTemplate,
   .remove normalLabelLookupReloadTriggerTemplate,
   .add (.var "lookup-rule")]

/-- Reload the finite lookup micro-machine after one cursor advance. -/
def normalLabelLookupReloadRule : Atom :=
  .expression
    [.symbol "exec", normalLabelLookupReloadLocation,
      .expression (.symbol "," :: normalLabelLookupReloadPatternAtoms),
      .expression
        [.symbol "O",
          .expression [.symbol "+", normalLabelLookupReloadSelfTemplate],
          .expression [.symbol "-", normalLabelLookupReloadTriggerTemplate],
          .expression [.symbol "+", .var "lookup-rule"]]]

def normalLabelLookupReloadDirective : SourceExecFact where
  atom := normalLabelLookupReloadRule
  loc := normalLabelLookupReloadLocation
  rule :=
    { priority := 35
      name := "mm-normal-label-lookup-reload"
      input := .compat (mkPattern normalLabelLookupReloadPatternAtoms)
      guards := []
      tmpl := mkTemplate normalLabelLookupReloadSinks }

theorem extract_normalLabelLookupReloadRule_exact :
    extractSupportedSourceExecFact normalLabelLookupReloadRule =
      some normalLabelLookupReloadDirective := by
  rfl

/-- Source-level rules that must be reinstalled at each ordered theorem
activation. -/
def normalLabelLookupSourceRules : List Atom :=
  [normalLabelLookupStartRule, normalLabelLookupReloadRule]

/-- Passive verifier-owned relation loaded after fallback activation.  The
fault reflector is included because unsuccessful scan iterations may have
caused the scheduler to consume its earlier copy. -/
def normalLabelLookupStaticRows : List Atom :=
  [normalLabelLookupRuleRow normalLabelLookupHitRule,
   normalLabelLookupRuleRow normalLabelLookupMissingRule,
   normalLabelLookupRuleRow normalLabelLookupAdvanceRule,
   normalLabelLookupRuleRow sourceTheoremFaultRejectRule]

/-- Parsing the actual emitted lookup rules loses none of the four authored
transitions. -/
theorem normalLabelLookupRules_extract_exact :
    (normalLabelLookupSourceRules ++
      [normalLabelLookupHitRule, normalLabelLookupMissingRule,
       normalLabelLookupAdvanceRule]).filterMap
        extractSupportedSourceExecFact =
      [normalLabelLookupStartDirective, normalLabelLookupReloadDirective,
       normalLabelLookupHitDirective, normalLabelLookupMissingDirective,
       normalLabelLookupAdvanceDirective] := by
  rfl

/-! ## Bounded positive and negative realization controls -/

private def missingCanaryState : Atom :=
  .expression
    [.symbol "mm-normal-label-lookup", .symbol "scope", .symbol "proof",
      natAtom 0, natAtom 1, natAtom 0, stringAtom "absent", natAtom 2,
      natAtom 2]

private def missingCanaryFault : Atom :=
  .expression
    [.symbol "mm-proof-fault", .symbol "scope", .symbol "proof", natAtom 0,
      .symbol "undefined-label", stringAtom "absent", stringAtom "absent",
      natAtom 2]

private def missingCanaryAtoms : List Atom :=
  [normalLabelLookupMissingRule, missingCanaryState]

private def missingCanarySpace : Space := missingCanaryAtoms.toFinset

private theorem missingCanaryAtoms_nodup : missingCanaryAtoms.Nodup := by
  decide +kernel

private theorem missingCanaryAtoms_supported :
    cSupportedSourceExecFacts missingCanaryAtoms =
      [normalLabelLookupMissingDirective] := by
  rfl

theorem missingCanary_selects_directive :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace missingCanarySpace) =
      some normalLabelLookupMissingDirective := by
  exact reflective_selects_of_computable_supported_singleton
    missingCanaryAtoms normalLabelLookupMissingDirective
    missingCanaryAtoms_nodup missingCanaryAtoms_supported

theorem missingCanary_fires_fault :
    missingCanaryFault ∈
      fireReflectiveSourceExecFact missingCanarySpace
        normalLabelLookupMissingDirective := by
  have agreement :=
    reflectiveSourceFiringAgreement_of_supportAlignment
      missingCanaryAtoms normalLabelLookupMissingDirective
      missingCanaryAtoms_nodup
      ((all_reflectiveSupportSetSinkB_eq_true_iff
        normalLabelLookupMissingDirective.rule.tmpl).1 (by decide +kernel))
      (reflectiveSourceRowSupportAlignment_of_nodup
        missingCanaryAtoms normalLabelLookupMissingDirective
        missingCanaryAtoms_nodup)
  have computableMember : missingCanaryFault ∈
      (cFireReflectiveSourceExecFact missingCanaryAtoms
        normalLabelLookupMissingDirective).toFinset :=
    List.mem_toFinset.mpr (by decide +kernel)
  rw [agreement] at computableMember
  simpa [missingCanarySpace] using computableMember

/-- The real MM2 missing transition is one OSLF-observed step of the emitted
target machine, not a host-side verdict postprocessor. -/
theorem missingCanary_inhabits_target_native_type :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
        (reflectiveSourceExecGSLT .leaveInert)).satisfies missingCanarySpace
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact missingCanarySpace
          normalLabelLookupMissingDirective)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected missingCanary_selects_directive)

private def notAtFrontierCanaryState : Atom :=
  .expression
    [.symbol "mm-normal-label-lookup", .symbol "scope", .symbol "proof",
      natAtom 0, natAtom 1, natAtom 0, stringAtom "absent", natAtom 1,
      natAtom 2]

theorem missingRule_rejects_nonfrontier_canary :
    (cmatchInputSpec []
        [normalLabelLookupMissingRule, notAtFrontierCanaryState]
        normalLabelLookupMissingDirective.rule.input).isEmpty = true := by
  decide +kernel

#print axioms extract_normalLabelLookupStartRule_exact
#print axioms extract_normalLabelLookupHitRule_exact
#print axioms extract_normalLabelLookupMissingRule_exact
#print axioms extract_normalLabelLookupAdvanceRule_exact
#print axioms extract_normalLabelLookupReloadRule_exact
#print axioms normalLabelLookupRules_extract_exact
#print axioms missingCanary_fires_fault
#print axioms missingCanary_inhabits_target_native_type
#print axioms missingRule_rejects_nonfrontier_canary

end Mettapedia.Languages.Metamath.MM2NormalLabelLookup
