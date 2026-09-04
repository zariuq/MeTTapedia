import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamily

/-!
# Mutation controls for cold call-guard source authentication

These controls distinguish complete structural decoding from rule-name or
row-count checks.  Every mutation retains a well-formed `LanguageDef` record;
the exact cold decoder is responsible for rejecting the altered schedule or
row structure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamilyCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamily

private def withRewrites (rewrites : List RewriteRule) : LanguageDef :=
  { language with rewrites := rewrites }

/-- A missing row must not silently select a smaller compiler. -/
def omittedLanguage : LanguageDef :=
  withRewrites transitions.tail

/-- A duplicate row must be rejected even though every row is individually
known. -/
def duplicatedLanguage : LanguageDef :=
  withRewrites (finishTransition :: transitions)

/-- Source order is scheduling data, so swapping two known rows is invalid. -/
def reorderedLanguage : LanguageDef :=
  withRewrites
    (skipHeadTransition :: finishTransition :: transitions.drop 2)

/-- Same name and patterns, but an added premise. -/
def changedPremiseTransition : RewriteRule :=
  { finishTransition with
    premises := [.relationQuery "PeTTaCallGuardCanaryPremise" []] }

def changedPremiseLanguage : LanguageDef :=
  withRewrites (changedPremiseTransition :: transitions.tail)

/-- Same name, premises, and patterns, but an added metavariable binding. -/
def changedContextTransition : RewriteRule :=
  { finishTransition with
    typeContext :=
      finishTransition.typeContext ++ [("canary", .base "CGNat")] }

def changedContextLanguage : LanguageDef :=
  withRewrites (changedContextTransition :: transitions.tail)

/-- Same name and metadata, but a changed left pattern. -/
def changedPatternTransition : RewriteRule :=
  { finishTransition with left := finishTransition.right }

def changedPatternLanguage : LanguageDef :=
  withRewrites (changedPatternTransition :: transitions.tail)

/-- A correct rule name alone carries no authority. -/
def nameOnlySpoofTransition : RewriteRule :=
  { finishTransition with right := finishTransition.left }

def nameOnlySpoofLanguage : LanguageDef :=
  withRewrites (nameOnlySpoofTransition :: transitions.tail)

/-- Relation identity is part of the ordered premise structure. -/
def changedRelationTransition : RewriteRule :=
  { skipHeadTransition with
    premises := [.relationQuery "PeTTaCallGuardCanaryNotEqual"
      [.fvar "declarationHead", .fvar "head"]] }

def changedRelationLanguage : LanguageDef :=
  withRewrites
    (finishTransition :: changedRelationTransition :: transitions.drop 2)

/-- An unknown row is rejected even when copied from a supported row. -/
def unknownTransition : RewriteRule :=
  { finishTransition with name := "petta-call-guard-compile-unknown" }

def unknownLanguage : LanguageDef :=
  withRewrites (unknownTransition :: transitions.tail)

theorem live_language_accepted :
    decodeLanguage? language = some orderedFamilies :=
  language_decodes_exactly

theorem omitted_language_rejected :
    decodeLanguage? omittedLanguage = none := by
  apply (decodeLanguage?_eq_none_iff omittedLanguage).2
  intro rowsEqual
  have lengthsEqual := congrArg List.length rowsEqual
  simp [omittedLanguage, withRewrites, transitions] at lengthsEqual

theorem duplicated_language_rejected :
    decodeLanguage? duplicatedLanguage = none := by
  apply (decodeLanguage?_eq_none_iff duplicatedLanguage).2
  intro rowsEqual
  have lengthsEqual := congrArg List.length rowsEqual
  simp [duplicatedLanguage, withRewrites, transitions] at lengthsEqual

theorem reordered_language_rejected :
    decodeLanguage? reorderedLanguage = none := by
  apply (decodeLanguage?_eq_none_iff reorderedLanguage).2
  intro rowsEqual
  have namesEqual := congrArg (List.map RewriteRule.name) rowsEqual
  simp [reorderedLanguage, withRewrites, transitions, finishTransition,
    skipHeadTransition] at namesEqual

theorem changed_premise_rejected :
    decodeLanguage? changedPremiseLanguage = none := by
  apply (decodeLanguage?_eq_none_iff changedPremiseLanguage).2
  intro rowsEqual
  have firstEqual := congrArg List.head? rowsEqual
  have premisesEqual := congrArg (Option.map RewriteRule.premises) firstEqual
  simp [changedPremiseLanguage, changedPremiseTransition, withRewrites,
    transitions, finishTransition] at premisesEqual

theorem changed_context_rejected :
    decodeLanguage? changedContextLanguage = none := by
  apply (decodeLanguage?_eq_none_iff changedContextLanguage).2
  intro rowsEqual
  have firstEqual := congrArg List.head? rowsEqual
  have contextsEqual := congrArg (Option.map RewriteRule.typeContext) firstEqual
  simp [changedContextLanguage, changedContextTransition, withRewrites,
    transitions, finishTransition] at contextsEqual

theorem changed_pattern_rejected :
    decodeLanguage? changedPatternLanguage = none := by
  apply (decodeLanguage?_eq_none_iff changedPatternLanguage).2
  intro rowsEqual
  have firstEqual := congrArg List.head? rowsEqual
  have leftEqual := congrArg (Option.map RewriteRule.left) firstEqual
  simp [changedPatternLanguage, changedPatternTransition, withRewrites,
    transitions, finishTransition, compileRunning, compileHalted,
    declarationsNil, compiledPattern, familyPattern] at leftEqual

theorem name_only_spoof_rejected :
    decodeLanguage? nameOnlySpoofLanguage = none := by
  apply (decodeLanguage?_eq_none_iff nameOnlySpoofLanguage).2
  intro rowsEqual
  have firstEqual := congrArg List.head? rowsEqual
  have rightEqual := congrArg (Option.map RewriteRule.right) firstEqual
  simp [nameOnlySpoofLanguage, nameOnlySpoofTransition, withRewrites,
    transitions, finishTransition, compileRunning, compileHalted,
    declarationsNil, compiledPattern, familyPattern] at rightEqual

theorem changed_relation_rejected :
    decodeLanguage? changedRelationLanguage = none := by
  apply (decodeLanguage?_eq_none_iff changedRelationLanguage).2
  intro rowsEqual
  have secondEqual := congrArg (fun rows => rows[1]?) rowsEqual
  have premisesEqual := congrArg (Option.map RewriteRule.premises) secondEqual
  simp [changedRelationLanguage, changedRelationTransition, withRewrites,
    transitions, skipHeadTransition, notEqualRelation] at premisesEqual

theorem unknown_row_rejected :
    decodeLanguage? unknownLanguage = none := by
  apply (decodeLanguage?_eq_none_iff unknownLanguage).2
  intro rowsEqual
  have firstEqual := congrArg List.head? rowsEqual
  have namesEqual := congrArg (Option.map RewriteRule.name) firstEqual
  simp [unknownLanguage, unknownTransition, withRewrites, transitions,
    finishTransition] at namesEqual

#print axioms live_language_accepted
#print axioms omitted_language_rejected
#print axioms duplicated_language_rejected
#print axioms reordered_language_rejected
#print axioms changed_premise_rejected
#print axioms changed_context_rejected
#print axioms changed_pattern_rejected
#print axioms name_only_spoof_rejected
#print axioms changed_relation_rejected
#print axioms unknown_row_rejected

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileTransitionFamilyCanary
