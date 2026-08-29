import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
import Mettapedia.Languages.TPTP.StatusSemantics

/-!
# Official TPTP useful-information projection

TSTP places semantic status, assumption, introduced-symbol, refutation, and
tool-specific metadata in the `useful_info` general-term list.  This module
decodes the list structure once, recognizes the standardized top-level item
names, and preserves every original item pattern for later calculus services.

Recognition is deliberately not verification.  In particular, a derivation
service must decide whether a status is supported, whether assumptions are
properly propagated or discharged, and whether introduced symbols are fresh.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.Languages.TPTP.StatusSemantics

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def decodeCommaGeneralTerms? : Pattern -> Option (List Pattern)
  | .apply "tptp92-ast:list:tptp92ast-comma-general-term:nil" [] => some []
  | .apply "tptp92-ast:list:tptp92ast-comma-general-term:cons" [
      .apply "tptp92-ast:comma-general-term:alt-1" [term], rest] => do
      let decodedRest <- decodeCommaGeneralTerms? rest
      some (term :: decodedRest)
  | _ => none

def decodeGeneralTerms? : Pattern -> Option (List Pattern)
  | .apply "tptp92-ast:general-terms:alt-1" [first, rest] => do
      let decodedRest <- decodeCommaGeneralTerms? rest
      some (first :: decodedRest)
  | _ => none

def decodeGeneralList? : Pattern -> Option (List Pattern)
  | .apply "tptp92-ast:general-list:alt-1" [] => some []
  | .apply "tptp92-ast:general-list:alt-2" [terms] =>
      decodeGeneralTerms? terms
  | _ => none

structure GeneralFunctionView where
  name : String
  arguments : List Pattern
  raw : Pattern
  deriving DecidableEq, Repr

def decodeGeneralFunctionTerm? (term : Pattern) : Option GeneralFunctionView :=
  match term with
  | .apply "tptp92-ast:general-term:alt-1" [
      .apply "tptp92-ast:general-data:alt-2" [
        .apply "tptp92-ast:general-function:alt-1" [name, arguments]]] => do
      let decodedName <- decodeAtomicWord? name
      let decodedArguments <- decodeGeneralTerms? arguments
      some { name := decodedName, arguments := decodedArguments, raw := term }
  | _ => none

def decodeAtomicGeneralTerm? : Pattern -> Option String
  | .apply "tptp92-ast:general-term:alt-1" [
      .apply "tptp92-ast:general-data:alt-1" [word]] =>
      decodeAtomicWord? word
  | _ => none

def decodeVariableGeneralTerm? : Pattern -> Option String
  | .apply "tptp92-ast:general-term:alt-1" [
      .apply "tptp92-ast:general-data:alt-3" [
        .apply "tptp92-ast:variable:alt-1" [token]]] =>
      decodeLexeme? token
  | _ => none

def decodeIntegerGeneralTerm? : Pattern -> Option String
  | .apply "tptp92-ast:general-term:alt-1" [
      .apply "tptp92-ast:general-data:alt-4" [
        .apply "tptp92-ast:number:alt-1" [token]]] =>
      decodeLexeme? token
  | _ => none

/-- Formula names in an assumptions record have the official `<name>` shape:
an atomic word or an integer.  This decoder acts on their representation as
general terms rather than inventing a second name syntax. -/
def decodeReferenceNameGeneralTerm? (term : Pattern) : Option String :=
  decodeAtomicGeneralTerm? term <|> decodeIntegerGeneralTerm? term

def decodeBracketGeneralTerm? : Pattern -> Option (List Pattern)
  | .apply "tptp92-ast:general-term:alt-3" [generalList] =>
      decodeGeneralList? generalList
  | _ => none

inductive InfoItemKind where
  | status
  | assumptions
  | newSymbols
  | refutation
  | other
  deriving DecidableEq, Repr

structure InfoItemView where
  raw : Pattern
  kind : InfoItemKind
  functionName : Option String
  arguments : List Pattern
  deriving DecidableEq, Repr

def classifyFunctionName : String -> InfoItemKind
  | "status" => .status
  | "assumptions" => .assumptions
  | "new_symbols" => .newSymbols
  | "refutation" => .refutation
  | _ => .other

def decodeInfoItem (term : Pattern) : InfoItemView :=
  match decodeGeneralFunctionTerm? term with
  | none => {
      raw := term
      kind := .other
      functionName := none
      arguments := []
    }
  | some function => {
      raw := term
      kind := classifyFunctionName function.name
      functionName := some function.name
      arguments := function.arguments
    }

structure UsefulInfoView where
  raw : Pattern
  items : List InfoItemView
  deriving DecidableEq, Repr

def decodeUsefulInfo? (usefulInfo : Pattern) : Option UsefulInfoView :=
  match usefulInfo with
  | .apply "tptp92-ast:useful-info:alt-1" [generalList] => do
      let terms <- decodeGeneralList? generalList
      some { raw := usefulInfo, items := terms.map decodeInfoItem }
  | _ => none

def InfoItemView.decodeStatus? (item : InfoItemView) : Option Status := do
  if item.kind != .status then none else
  match item.arguments with
  | [argument] =>
      Status.parse? (← decodeAtomicGeneralTerm? argument)
  | _ => none

def statusValues? : List InfoItemView -> Option (List Status)
  | [] => some []
  | item :: items => do
      let rest <- statusValues? items
      if item.kind == .status then
        some ((← item.decodeStatus?) :: rest)
      else
        some rest

/-- A semantically checked inference requires exactly one recognized status.
Missing, malformed, unknown, and duplicate statuses are all distinguished
from the successful singleton case by returning `none`. -/
def uniqueStatus? (view : UsefulInfoView) : Option Status :=
  do
    match ← statusValues? view.items with
    | [status] => some status
    | _ => none

def decodeUniqueStatus? (usefulInfo : Pattern) : Option Status := do
  let view <- decodeUsefulInfo? usefulInfo
  uniqueStatus? view

/-! ## Exact assumption and introduced-symbol records -/

structure AssumptionsRecord where
  names : List String
  rawNames : List Pattern
  raw : Pattern
  deriving DecidableEq, Repr

def InfoItemView.decodeAssumptions? (item : InfoItemView) : Option AssumptionsRecord := do
  if item.kind != .assumptions then none else
  match item.arguments with
  | [argument] =>
      let rawNames <- decodeBracketGeneralTerm? argument
      let names <- rawNames.mapM decodeReferenceNameGeneralTerm?
      some { names, rawNames, raw := item.raw }
  | _ => none

inductive PrincipalSymbolKind where
  | functor
  | variable
  deriving DecidableEq, Repr

structure PrincipalSymbol where
  kind : PrincipalSymbolKind
  name : String
  raw : Pattern
  deriving DecidableEq, Repr

/-- A `principal_symbol` is exactly an official functor or variable.  Bare
atomic general terms encode functors; upper-word general terms encode
variables.  Numbers and arbitrary general functions are deliberately not
accepted as symbol declarations. -/
def decodePrincipalSymbol? (term : Pattern) : Option PrincipalSymbol :=
  match decodeAtomicGeneralTerm? term with
  | some name => some { kind := .functor, name, raw := term }
  | none => match decodeVariableGeneralTerm? term with
    | some name => some { kind := .variable, name, raw := term }
    | none => none

structure NewSymbolsRecord where
  introductionKind : String
  symbols : List PrincipalSymbol
  rawSymbols : List Pattern
  raw : Pattern
  deriving DecidableEq, Repr

def InfoItemView.decodeNewSymbols? (item : InfoItemView) : Option NewSymbolsRecord := do
  if item.kind != .newSymbols then none else
  match item.arguments with
  | [kindTerm, symbolsTerm] =>
      let introductionKind <- decodeAtomicGeneralTerm? kindTerm
      let rawSymbols <- decodeBracketGeneralTerm? symbolsTerm
      let symbols <- rawSymbols.mapM decodePrincipalSymbol?
      some { introductionKind, symbols, rawSymbols, raw := item.raw }
  | _ => none

/-- Decode every assumptions record while ignoring unrelated useful-info
items.  A syntactically recognized but malformed assumptions record rejects
the projection instead of being silently downgraded to tool-specific data. -/
def assumptionRecords? : List InfoItemView -> Option (List AssumptionsRecord)
  | [] => some []
  | item :: items => do
      let rest <- assumptionRecords? items
      if item.kind == .assumptions then
        some ((← item.decodeAssumptions?) :: rest)
      else
        some rest

/-- Decode every introduced-symbol record with the same fail-closed rule. -/
def newSymbolsRecords? : List InfoItemView -> Option (List NewSymbolsRecord)
  | [] => some []
  | item :: items => do
      let rest <- newSymbolsRecords? items
      if item.kind == .newSymbols then
        some ((← item.decodeNewSymbols?) :: rest)
      else
        some rest

def decodeAssumptionRecords? (usefulInfo : Pattern) : Option (List AssumptionsRecord) := do
  assumptionRecords? (← decodeUsefulInfo? usefulInfo).items

def decodeNewSymbolsRecords? (usefulInfo : Pattern) : Option (List NewSymbolsRecord) := do
  newSymbolsRecords? (← decodeUsefulInfo? usefulInfo).items

/-! ## Rule-indexed inference information -/

/-- Official `<inference_info>` is not wrapped in an `inference` function.
Its function name is the inference rule itself, followed by an information
kind and a general list.  Decoding therefore requires the surrounding rule
name; classifying these records from the function name alone is impossible. -/
structure RuleInfoRecord where
  ruleName : String
  informationKind : String
  details : List Pattern
  raw : Pattern
  deriving DecidableEq, Repr

def InfoItemView.decodeRuleInfoFor? (ruleName : String)
    (item : InfoItemView) : Option RuleInfoRecord := do
  if item.kind != .other then none else
  if item.functionName != some ruleName then none else
  match item.arguments with
  | [kindTerm, detailsTerm] =>
      let informationKind <- decodeAtomicGeneralTerm? kindTerm
      let details <- decodeBracketGeneralTerm? detailsTerm
      some { ruleName, informationKind, details, raw := item.raw }
  | _ => none

/-- Decode all information records belonging to the surrounding rule.  A
matching but malformed record rejects the list; unrelated tool-specific
functions remain available through `InferenceMetadata.rawItems`. -/
def ruleInfoRecords? (ruleName : String) :
    List InfoItemView -> Option (List RuleInfoRecord)
  | [] => some []
  | item :: items => do
      let rest <- ruleInfoRecords? ruleName items
      if item.kind == .other && item.functionName == some ruleName then
        some ((← item.decodeRuleInfoFor? ruleName) :: rest)
      else
        some rest

def decodeRuleInfoRecords? (ruleName : String) (usefulInfo : Pattern) :
    Option (List RuleInfoRecord) := do
  ruleInfoRecords? ruleName (← decodeUsefulInfo? usefulInfo).items

/-- The semantic metadata carried by one official inference record.  All
recognized fields are decoded atomically: one malformed status, assumptions,
or introduced-symbol record rejects the whole view instead of being erased
while another field is accepted.  Tool-specific information remains in
`rawItems` for separately validated consumers. -/
structure InferenceMetadata where
  status : Status
  assumptions : List AssumptionsRecord
  newSymbols : List NewSymbolsRecord
  rawItems : List InfoItemView
  deriving DecidableEq, Repr

def decodeInferenceMetadata? (usefulInfo : Pattern) : Option InferenceMetadata := do
  let view <- decodeUsefulInfo? usefulInfo
  let status <- uniqueStatus? view
  let assumptions <- assumptionRecords? view.items
  let newSymbols <- newSymbolsRecords? view.items
  some { status, assumptions, newSymbols, rawItems := view.items }

structure RuleMetadata extends InferenceMetadata where
  ruleInfo : List RuleInfoRecord
  deriving DecidableEq, Repr

def decodeRuleMetadata? (ruleName : String) (usefulInfo : Pattern) :
    Option RuleMetadata := do
  let metadata <- decodeInferenceMetadata? usefulInfo
  let ruleInfo <- ruleInfoRecords? ruleName metadata.rawItems
  some { toInferenceMetadata := metadata, ruleInfo }

/-! ## Controls -/

namespace Canary

def word (value : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-1" [
    a "tptp92-ast:token:lower-word" [a value]]

def atomicTerm (value : String) : Pattern :=
  a "tptp92-ast:general-term:alt-1" [
    a "tptp92-ast:general-data:alt-1" [word value]]

def integerTerm (value : String) : Pattern :=
  a "tptp92-ast:general-term:alt-1" [
    a "tptp92-ast:general-data:alt-4" [
      a "tptp92-ast:number:alt-1" [
        a "tptp92-ast:token:integer" [a value]]]]

def variableTerm (value : String) : Pattern :=
  a "tptp92-ast:general-term:alt-1" [
    a "tptp92-ast:general-data:alt-3" [
      a "tptp92-ast:variable:alt-1" [
        a "tptp92-ast:token:upper-word" [a value]]]]

def commaTerms : List Pattern -> Pattern
  | [] => a "tptp92-ast:list:tptp92ast-comma-general-term:nil"
  | term :: terms =>
      a "tptp92-ast:list:tptp92ast-comma-general-term:cons" [
        a "tptp92-ast:comma-general-term:alt-1" [term],
        commaTerms terms]

def terms : List Pattern -> Pattern
  | [] => a "malformed-empty-general-terms"
  | first :: rest =>
      a "tptp92-ast:general-terms:alt-1" [first, commaTerms rest]

def functionTerm (name : String) (arguments : List Pattern) : Pattern :=
  a "tptp92-ast:general-term:alt-1" [
    a "tptp92-ast:general-data:alt-2" [
      a "tptp92-ast:general-function:alt-1" [word name, terms arguments]]]

def usefulInfo (items : List Pattern) : Pattern :=
  match items with
  | [] => a "tptp92-ast:useful-info:alt-1" [
      a "tptp92-ast:general-list:alt-1"]
  | _ => a "tptp92-ast:useful-info:alt-1" [
      a "tptp92-ast:general-list:alt-2" [terms items]]

def listTerm (items : List Pattern) : Pattern :=
  match items with
  | [] => a "tptp92-ast:general-term:alt-3" [
      a "tptp92-ast:general-list:alt-1"]
  | _ => a "tptp92-ast:general-term:alt-3" [
      a "tptp92-ast:general-list:alt-2" [terms items]]

def statusThm : Pattern := usefulInfo [functionTerm "status" [atomicTerm "thm"]]

theorem status_thm_exact : decodeUniqueStatus? statusThm = some .thm := by
  rfl

def statusWithOther : Pattern := usefulInfo [
  functionTerm "proof" [atomicTerm "recorded"],
  functionTerm "status" [atomicTerm "esa"]]

theorem unrelated_information_is_preserved_and_status_found :
    (decodeUsefulInfo? statusWithOther).map (fun view =>
      (view.items.map InfoItemView.functionName, uniqueStatus? view)) =
        some ([some "proof", some "status"], some .esa) := by
  rfl

def duplicateStatus : Pattern := usefulInfo [
  functionTerm "status" [atomicTerm "thm"],
  functionTerm "status" [atomicTerm "esa"]]

theorem duplicate_status_rejected :
    decodeUniqueStatus? duplicateStatus = none := by
  rfl

def unknownStatus : Pattern :=
  usefulInfo [functionTerm "status" [atomicTerm "zzz"]]

theorem unknown_status_rejected : decodeUniqueStatus? unknownStatus = none := by
  rfl

def validThenUnknownStatus : Pattern := usefulInfo [
  functionTerm "status" [atomicTerm "thm"],
  functionTerm "status" [atomicTerm "zzz"]]

theorem unknown_status_is_not_erased_beside_valid_status :
    decodeUniqueStatus? validThenUnknownStatus = none := by
  rfl

def malformedList : Pattern :=
  a "tptp92-ast:useful-info:alt-1" [
    a "tptp92-ast:general-list:alt-2" [a "bad"]]

theorem malformed_list_rejected : decodeUsefulInfo? malformedList = none := by
  rfl

def assumptionsAndSymbols : Pattern := usefulInfo [
  functionTerm "status" [atomicTerm "thm"],
  functionTerm "assumptions" [listTerm [atomicTerm "hypothesis_a", integerTerm "17"]],
  functionTerm "new_symbols" [
    atomicTerm "skolem",
    listTerm [atomicTerm "skolem_f", variableTerm "X"]]]

theorem assumptions_preserve_exact_names_order_and_multiplicity :
    (decodeAssumptionRecords? assumptionsAndSymbols).map
      (fun records => records.map (fun record => record.names)) =
        some [["hypothesis_a", "17"]] := by
  rfl

theorem introduced_symbols_preserve_kind_order_and_symbol_kinds :
    (decodeNewSymbolsRecords? assumptionsAndSymbols).map
      (fun records => records.map (fun record =>
        (record.introductionKind,
          record.symbols.map (fun symbol => (symbol.kind, symbol.name))))) =
        some [("skolem", [(.functor, "skolem_f"), (.variable, "X")])] := by
  rfl

theorem inference_metadata_is_one_exact_object :
    (decodeInferenceMetadata? assumptionsAndSymbols).map (fun metadata =>
      (metadata.status,
        metadata.assumptions.map (fun record => record.names),
        metadata.newSymbols.map (fun record =>
          (record.introductionKind,
            record.symbols.map (fun symbol => (symbol.kind, symbol.name)))))) =
      some (.thm, [["hypothesis_a", "17"]],
        [("skolem", [(.functor, "skolem_f"), (.variable, "X")])]) := by
  rfl

def repeatedAssumptions : Pattern := usefulInfo [
  functionTerm "assumptions" [listTerm [atomicTerm "h"]],
  functionTerm "assumptions" [listTerm [atomicTerm "h"]]]

theorem repeated_assumption_records_are_preserved_not_conflated :
    (decodeAssumptionRecords? repeatedAssumptions).map
      (fun records => records.map (fun record => record.names)) =
        some [["h"], ["h"]] := by
  rfl

def assumptionsAndDischarge : Pattern := usefulInfo [
  functionTerm "status" [atomicTerm "thm"],
  functionTerm "assumptions" [listTerm [atomicTerm "h"]],
  functionTerm "contra" [atomicTerm "discharge", listTerm [atomicTerm "h"]]]

theorem rule_indexed_discharge_information_is_exact :
    (decodeRuleMetadata? "contra" assumptionsAndDischarge).map
      (fun metadata =>
        (metadata.assumptions.map (fun record => record.names),
          metadata.ruleInfo.map (fun record =>
            (record.ruleName, record.informationKind,
              record.details.map decodeAtomicGeneralTerm?)))) =
      some ([ ["h"] ], [("contra", "discharge", [some "h"])]) := by
  rfl

def malformedDischarge : Pattern := usefulInfo [
  functionTerm "status" [atomicTerm "thm"],
  functionTerm "contra" [atomicTerm "discharge", atomicTerm "not-a-list"]]

theorem malformed_matching_rule_information_rejected :
    decodeRuleMetadata? "contra" malformedDischarge = none := by
  rfl

def malformedAssumptions : Pattern :=
  usefulInfo [functionTerm "assumptions" [atomicTerm "not-a-list"]]

theorem malformed_recognized_assumptions_rejected :
    decodeAssumptionRecords? malformedAssumptions = none := by
  rfl

def malformedNewSymbols : Pattern := usefulInfo [
  functionTerm "new_symbols" [
    atomicTerm "skolem",
    listTerm [integerTerm "9"]]]

theorem malformed_principal_symbol_rejected :
    decodeNewSymbolsRecords? malformedNewSymbols = none := by
  rfl

end Canary

#print axioms Canary.status_thm_exact
#print axioms Canary.unrelated_information_is_preserved_and_status_found
#print axioms Canary.duplicate_status_rejected
#print axioms Canary.unknown_status_rejected
#print axioms Canary.unknown_status_is_not_erased_beside_valid_status
#print axioms Canary.malformed_list_rejected
#print axioms Canary.assumptions_preserve_exact_names_order_and_multiplicity
#print axioms Canary.introduced_symbols_preserve_kind_order_and_symbol_kinds
#print axioms Canary.inference_metadata_is_one_exact_object
#print axioms Canary.repeated_assumption_records_are_preserved_not_conflated
#print axioms Canary.rule_indexed_discharge_information_is_exact
#print axioms Canary.malformed_matching_rule_information_rejected
#print axioms Canary.malformed_recognized_assumptions_rejected
#print axioms Canary.malformed_principal_symbol_rejected

end Mettapedia.GSLT.LanguageDef.TptpOfficialUsefulInfo
