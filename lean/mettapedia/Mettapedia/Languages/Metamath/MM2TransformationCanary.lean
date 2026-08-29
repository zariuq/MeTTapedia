import Mettapedia.Languages.Metamath.MM2Transformation
import Mettapedia.Languages.Metamath.SourceInferenceProjectionValidation

/-!
# Executable Metamath-to-MM2 hypothesis canary

This module supplies the smallest admitted Metamath scope with one active
floating hypothesis.  The compiler consumes that scope and its generated
calculus language, while the proof label remains dynamic input.  The resulting
ordinary MM2 program is suitable for direct execution by MORK.

The canary is intentionally one proof-machine slice, not a complete verifier.
Its purpose is to keep the source language, target language, surface,
and executor boundaries executable while assertion and compressed-proof
semantics are added.
-/

namespace Mettapedia.Languages.Metamath.MM2TransformationCanary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditions
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.Metamath.SourceInferenceProjectionValidation
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface
open Mettapedia.GSLT.LanguageDef (CalculusLanguageDef)

/-! ## One admitted source scope -/

def hypothesisCanaryState : SourceState :=
  { declaredConstants := ["wff"]
    declaredVariables := ["ph"]
    activeVariables := ["ph"]
    variableTypecodes := [("ph", "wff")]
    usedLabels := ["wph"]
    activeHypotheses := [.floating "wph" "wff" "ph"]
    activeDistinctVariables := []
    assertions := []
    scopes := []
    pendingBlockCompletions := 0 }

theorem hypothesisCanaryState_valid :
    sourceStateValid hypothesisCanaryState = true := by
  decide

theorem hypothesisCanaryState_prefix :
    hypothesisCanaryState.toSourcePrefix = exampleSourcePrefix := by
  rfl

private theorem hypothesisCanaryVocabulary_valid :
    sourceVocabularyValid
        (sourcePrefixVocabulary exampleSourcePrefix) = true := by
  unfold sourceVocabularyValid
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro value member
    have rawMember : value ∈ ["wph", "wph", "wff", "ph"] := by
      unfold sourcePrefixVocabulary at member
      rw [mem_sortStrings_iff, List.mem_eraseDups] at member
      simpa [exampleSourcePrefix, stringsOfSourceFrame,
        stringsOfHypothesis, stringsOfFormula, HypothesisView.label,
        HypothesisView.formula, Metamath.Verify.Sym.value] using member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at rawMember
    rcases rawMember with rfl | rfl | rfl | rfl <;>
      decide
  · apply beq_iff_eq.mpr
    apply eraseDups_length_eq_of_nodup
    have permutation :
        (sortStrings (["wph", "wph", "wff", "ph"].eraseDups)).Perm
          (["wph", "wph", "wff", "ph"].eraseDups) :=
      List.mergeSort_perm _ _
    have erasedNodup :
        (["wph", "wph", "wff", "ph"].eraseDups).Nodup := by
      decide
    have sortedNodup :
        (sortStrings
          (["wph", "wph", "wff", "ph"].eraseDups)).Nodup :=
      permutation.symm.nodup erasedNodup
    simpa [sourcePrefixVocabulary, exampleSourcePrefix,
      stringsOfSourceFrame, stringsOfHypothesis, stringsOfFormula,
      HypothesisView.label, HypothesisView.formula,
      Metamath.Verify.Sym.value] using sortedNodup

def hypothesisCanaryGates : SourceProjectionGates exampleSourcePrefix where
  prefixValid := by decide
  vocabularyValid := hypothesisCanaryVocabulary_valid
  ruleIdsDisjoint := by decide +kernel

def hypothesisCanaryLanguage : CalculusLanguageDef :=
  rawSourceInferenceLanguageDef exampleSourcePrefix

theorem hypothesisCanaryLanguage_generated :
    calculusLanguageDefOfSourcePrefix? hypothesisCanaryState.toSourcePrefix =
      some hypothesisCanaryLanguage := by
  rw [hypothesisCanaryState_prefix]
  exact calculusLanguageDefOfSourcePrefix_eq_some_rawSourceInferenceLanguageDef
    exampleSourcePrefix hypothesisCanaryGates

def hypothesisCanarySource : AdmittedSourceScope where
  state := hypothesisCanaryState
  stateValid := hypothesisCanaryState_valid
  language := hypothesisCanaryLanguage
  languageGenerated := hypothesisCanaryLanguage_generated

def severedGates : SourceProjectionGates initialState.toSourcePrefix where
  prefixValid := by decide
  vocabularyValid := by
    simp [initialState, sourcePrefixVocabulary, SourceState.toSourcePrefix,
      SourceState.callerFrame, SourceState.proofDistinctVariables,
      SourceState.activeFloatingVariables, sourceVocabularyValid, sortStrings,
      stringsOfSourceFrame]
  ruleIdsDisjoint := by decide +kernel

def severedLanguage : CalculusLanguageDef :=
  rawSourceInferenceLanguageDef initialState.toSourcePrefix

theorem severedLanguage_generated :
    calculusLanguageDefOfSourcePrefix? initialState.toSourcePrefix =
      some severedLanguage :=
  calculusLanguageDefOfSourcePrefix_eq_some_rawSourceInferenceLanguageDef
    initialState.toSourcePrefix severedGates

/-- An independently admitted source scope with no active hypothesis.  It is
the source-level severance control for the same dynamic proof input. -/
def severedSource : AdmittedSourceScope where
  state := initialState
  stateValid := by decide
  language := severedLanguage
  languageGenerated := severedLanguage_generated

/-! ## One admitted assertion scope -/

def identityAssertion : SourceAssertion :=
  { label := "ax-ph"
    formula := ⟨"wff", [.var "ph"]⟩
    frame :=
      { distinctVariables := []
        hypothesisLabels := ["wph"] }
    hypotheses := [.floating "wph" "wff" "ph"] }

def assertionCanaryState : SourceState :=
  { hypothesisCanaryState with
    usedLabels := ["wph", "ax-ph"]
    assertions := [identityAssertion] }

theorem assertionCanaryState_valid :
    sourceStateValid assertionCanaryState = true := by
  simp [sourceStateValid, sourceStateProjectionValid, sourceActivityValid,
    assertionCanaryState, hypothesisCanaryState, SourceState.toSourcePrefix,
    SourceState.callerFrame, SourceState.proofDistinctVariables,
    SourceState.activeFloatingVariables, SourceState.objectNames,
    variableTypecodesValid, activeHypothesisValid, sourcePrefixValid,
    sourceFrameValid, sourceFrameDVValid, sourceAssertionValid,
    identityAssertion, sourceRuleLabelsValid, reservedRulePrefix,
    formulaSymbolsRespectFrame, formulaSymbolsRespectDeclarations,
    floatingVariableNames, hasUniqueLabels, hasUniqueFloatingVariables,
    hypothesesPrefixScoped, hypothesesPrefixScopedFrom,
    SourcePrefix.toProjection, SourceAssertion.toProjectionView,
    sourceRuleLabels, HypothesisView.label, HypothesisView.formula,
    symbolRespectsFrame]
  all_goals decide +kernel

private theorem assertionCanaryVocabulary_valid :
    sourceVocabularyValid
        (sourcePrefixVocabulary assertionCanaryState.toSourcePrefix) = true := by
  unfold sourceVocabularyValid
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro value member
    have rawMember :
        value ∈
          ["wph", "wph", "wff", "ph", "ax-ph", "wff", "ph",
            "wph", "wph", "wff", "ph"] := by
      unfold sourcePrefixVocabulary at member
      rw [mem_sortStrings_iff, List.mem_eraseDups] at member
      simpa [assertionCanaryState, hypothesisCanaryState,
        SourceState.toSourcePrefix, SourceState.callerFrame,
        SourceState.proofDistinctVariables, SourceState.activeFloatingVariables,
        identityAssertion, stringsOfSourceFrame, stringsOfSourceAssertion,
        stringsOfHypothesis, stringsOfFormula, HypothesisView.label,
        HypothesisView.formula, Metamath.Verify.Sym.value] using member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at rawMember
    rcases rawMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [reservedRulePrefix, reservedProjectionHeads,
          reservedInternalHeads, reservedDataHeads] <;>
        decide +kernel
  · apply beq_iff_eq.mpr
    apply eraseDups_length_eq_of_nodup
    have permutation :
        (sortStrings
          (["wph", "wph", "wff", "ph", "ax-ph", "wff", "ph",
            "wph", "wph", "wff", "ph"].eraseDups)).Perm
          (["wph", "wph", "wff", "ph", "ax-ph", "wff", "ph",
            "wph", "wph", "wff", "ph"].eraseDups) :=
      List.mergeSort_perm _ _
    have erasedNodup :
        (["wph", "wph", "wff", "ph", "ax-ph", "wff", "ph",
          "wph", "wph", "wff", "ph"].eraseDups).Nodup := by
      decide
    have sortedNodup :
        (sortStrings
          (["wph", "wph", "wff", "ph", "ax-ph", "wff", "ph",
            "wph", "wph", "wff", "ph"].eraseDups)).Nodup :=
      permutation.symm.nodup erasedNodup
    simpa [sourcePrefixVocabulary, assertionCanaryState,
      hypothesisCanaryState, SourceState.toSourcePrefix,
      SourceState.callerFrame, SourceState.proofDistinctVariables,
      SourceState.activeFloatingVariables, identityAssertion,
      stringsOfSourceFrame, stringsOfSourceAssertion,
      stringsOfHypothesis, stringsOfFormula, HypothesisView.label,
      HypothesisView.formula, Metamath.Verify.Sym.value] using sortedNodup

def assertionCanaryGates :
    SourceProjectionGates assertionCanaryState.toSourcePrefix where
  prefixValid := sourcePrefixValid_of_sourceStateValid
    assertionCanaryState assertionCanaryState_valid
  vocabularyValid := assertionCanaryVocabulary_valid
  ruleIdsDisjoint := by decide +kernel

def assertionCanaryLanguage : CalculusLanguageDef :=
  rawSourceInferenceLanguageDef assertionCanaryState.toSourcePrefix

theorem assertionCanaryLanguage_generated :
    calculusLanguageDefOfSourcePrefix? assertionCanaryState.toSourcePrefix =
      some assertionCanaryLanguage :=
  calculusLanguageDefOfSourcePrefix_eq_some_rawSourceInferenceLanguageDef
    assertionCanaryState.toSourcePrefix assertionCanaryGates

def assertionCanarySource : AdmittedSourceScope where
  state := assertionCanaryState
  stateValid := assertionCanaryState_valid
  language := assertionCanaryLanguage
  languageGenerated := assertionCanaryLanguage_generated

/-! ## An essential-hypothesis assertion scope -/

def essentialHypothesis :
    Mettapedia.Languages.Metamath.InferenceEncoding.ConstantHeadedFormula :=
  ⟨"wff", [.var "ph"]⟩

def essentialAssertion : SourceAssertion :=
  { label := "ax-use"
    formula := ⟨"wff", [.var "ps"]⟩
    frame :=
      { distinctVariables := []
        hypothesisLabels := ["wph", "wps", "hph"] }
    hypotheses :=
      [.floating "wph" "wff" "ph",
       .floating "wps" "wff" "ps",
       .essential "hph" essentialHypothesis] }

def essentialCanaryState : SourceState :=
  { declaredConstants := ["wff"]
    declaredVariables := ["ph", "ps"]
    activeVariables := ["ph", "ps"]
    variableTypecodes := [("ph", "wff"), ("ps", "wff")]
    usedLabels := ["wph", "wps", "hph", "ax-use"]
    activeHypotheses :=
      [.floating "wph" "wff" "ph",
       .floating "wps" "wff" "ps",
       .essential "hph" essentialHypothesis]
    activeDistinctVariables := []
    assertions := [essentialAssertion]
    scopes := []
    pendingBlockCompletions := 0 }

theorem essentialCanaryState_valid :
    sourceStateValid essentialCanaryState = true := by
  simp [sourceStateValid, sourceStateProjectionValid, sourceActivityValid,
    essentialCanaryState, SourceState.toSourcePrefix,
    SourceState.callerFrame, SourceState.proofDistinctVariables,
    SourceState.activeFloatingVariables, SourceState.objectNames,
    variableTypecodesValid, activeHypothesisValid, sourcePrefixValid,
    sourceFrameValid, sourceFrameDVValid, sourceAssertionValid,
    essentialAssertion, essentialHypothesis, sourceRuleLabelsValid,
    reservedRulePrefix, formulaSymbolsRespectFrame,
    formulaSymbolsRespectDeclarations, floatingVariableNames,
    hasUniqueLabels, hasUniqueFloatingVariables,
    hypothesesPrefixScoped, hypothesesPrefixScopedFrom,
    SourcePrefix.toProjection, SourceAssertion.toProjectionView,
    sourceRuleLabels, HypothesisView.label, HypothesisView.formula,
    symbolRespectsFrame]
  all_goals decide +kernel

private theorem essentialCanaryVocabulary_valid :
    sourceVocabularyValid
        (sourcePrefixVocabulary essentialCanaryState.toSourcePrefix) = true := by
  unfold sourceVocabularyValid
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro value member
    have rawMember :
        value ∈
          ["wph", "wps", "hph", "wph", "wff", "ph", "wps", "wff",
           "ps", "hph", "wff", "ph", "ax-use", "wff", "ps", "wph",
           "wps", "hph", "wph", "wff", "ph", "wps", "wff", "ps",
           "hph", "wff", "ph"] := by
      unfold sourcePrefixVocabulary at member
      rw [mem_sortStrings_iff, List.mem_eraseDups] at member
      simpa [essentialCanaryState, SourceState.toSourcePrefix,
        SourceState.callerFrame, SourceState.proofDistinctVariables,
        SourceState.activeFloatingVariables, essentialAssertion,
        essentialHypothesis, stringsOfSourceFrame, stringsOfSourceAssertion,
        stringsOfHypothesis, stringsOfFormula, HypothesisView.label,
        HypothesisView.formula, Metamath.Verify.Sym.value] using member
    have distinctMember :
        value ∈ ["wph", "wps", "hph", "wff", "ph", "ps", "ax-use"] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at rawMember ⊢
      aesop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at distinctMember
    rcases distinctMember with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [reservedRulePrefix, reservedProjectionHeads,
          reservedInternalHeads, reservedDataHeads] <;>
        decide +kernel
  · apply beq_iff_eq.mpr
    apply eraseDups_length_eq_of_nodup
    let raw : List String :=
      ["wph", "wps", "hph", "wph", "wff", "ph", "wps", "wff",
       "ps", "hph", "wff", "ph", "ax-use", "wff", "ps", "wph",
       "wps", "hph", "wph", "wff", "ph", "wps", "wff", "ps",
       "hph", "wff", "ph"]
    have permutation : (sortStrings raw.eraseDups).Perm raw.eraseDups :=
      List.mergeSort_perm _ _
    have erasedNodup : raw.eraseDups.Nodup := by
      decide
    have sortedNodup : (sortStrings raw.eraseDups).Nodup :=
      permutation.symm.nodup erasedNodup
    simpa [raw, sourcePrefixVocabulary, essentialCanaryState,
      SourceState.toSourcePrefix, SourceState.callerFrame,
      SourceState.proofDistinctVariables, SourceState.activeFloatingVariables,
      essentialAssertion, essentialHypothesis, stringsOfSourceFrame,
      stringsOfSourceAssertion, stringsOfHypothesis, stringsOfFormula,
      HypothesisView.label, HypothesisView.formula,
      Metamath.Verify.Sym.value] using sortedNodup

def essentialCanaryGates :
    SourceProjectionGates essentialCanaryState.toSourcePrefix where
  prefixValid := sourcePrefixValid_of_sourceStateValid
    essentialCanaryState essentialCanaryState_valid
  vocabularyValid := essentialCanaryVocabulary_valid
  ruleIdsDisjoint := by decide +kernel

def essentialCanaryLanguage : CalculusLanguageDef :=
  rawSourceInferenceLanguageDef essentialCanaryState.toSourcePrefix

theorem essentialCanaryLanguage_generated :
    calculusLanguageDefOfSourcePrefix? essentialCanaryState.toSourcePrefix =
      some essentialCanaryLanguage :=
  calculusLanguageDefOfSourcePrefix_eq_some_rawSourceInferenceLanguageDef
    essentialCanaryState.toSourcePrefix essentialCanaryGates

def essentialCanarySource : AdmittedSourceScope where
  state := essentialCanaryState
  stateValid := essentialCanaryState_valid
  language := essentialCanaryLanguage
  languageGenerated := essentialCanaryLanguage_generated

/-! ## A stored assertion with a live disjoint-variable obligation -/

def dvAssertion : SourceAssertion :=
  { label := "ax-dv"
    formula := ⟨"wff", [.var "ph", .var "ps"]⟩
    frame :=
      { distinctVariables := [("ph", "ps")]
        hypothesisLabels := ["wph", "wps"] }
    hypotheses :=
      [.floating "wph" "wff" "ph",
       .floating "wps" "wff" "ps"] }

/-- The stored assertion has formal DV pair `(ph,ps)`; the current caller
licenses its concrete substitution through the independent pair `(x,y)`. -/
def dvCanaryState : SourceState :=
  { declaredConstants := ["wff"]
    declaredVariables := ["ph", "ps", "x", "y"]
    activeVariables := ["x", "y"]
    variableTypecodes :=
      [("ph", "wff"), ("ps", "wff"), ("x", "wff"), ("y", "wff")]
    usedLabels := ["wph", "wps", "ax-dv", "wx", "wy"]
    activeHypotheses :=
      [.floating "wx" "wff" "x",
       .floating "wy" "wff" "y"]
    activeDistinctVariables := [("x", "y")]
    assertions := [dvAssertion]
    scopes := []
    pendingBlockCompletions := 0 }

/-- Same stored assertion and dynamic hypotheses, but the caller omits the
required concrete DV pair.  The source scope itself remains valid. -/
def dvMissingCallerState : SourceState :=
  { dvCanaryState with activeDistinctVariables := [] }

theorem dvCanaryState_valid :
    sourceStateValid dvCanaryState = true := by
  decide +kernel

theorem dvMissingCallerState_valid :
    sourceStateValid dvMissingCallerState = true := by
  decide +kernel

private theorem sortedErasedVocabularyValid
    (raw : List String)
    (allowed : ∀ value ∈ raw,
      (value != "" &&
        !(value.startsWith reservedRulePrefix) &&
        !(reservedProjectionHeads.contains value)) = true)
    (nodup : (sortStrings raw.eraseDups).Nodup) :
    sourceVocabularyValid (sortStrings raw.eraseDups) = true := by
  unfold sourceVocabularyValid
  rw [Bool.and_eq_true]
  constructor
  · rw [List.all_eq_true]
    intro value member
    apply allowed value
    exact (List.mem_eraseDups.mp
      ((mem_sortStrings_iff value raw.eraseDups).mp member))
  · exact beq_iff_eq.mpr (eraseDups_length_eq_of_nodup _ nodup)

private def dvVocabularyRaw : List String :=
  ["x", "y", "wx", "wy",
   "wx", "wff", "x", "wy", "wff", "y",
   "ax-dv", "wff", "ph", "ps", "ph", "ps", "wph", "wps",
   "wph", "wff", "ph", "wps", "wff", "ps"]

private def dvMissingCallerVocabularyRaw : List String :=
  ["wx", "wy",
   "wx", "wff", "x", "wy", "wff", "y",
   "ax-dv", "wff", "ph", "ps", "ph", "ps", "wph", "wps",
   "wph", "wff", "ph", "wps", "wff", "ps"]

private theorem dvCanaryProofDistinctVariables :
    dvCanaryState.proofDistinctVariables = [("x", "y")] := by
  decide +kernel

private theorem dvMissingCallerProofDistinctVariables :
    dvMissingCallerState.proofDistinctVariables = [] := by
  rfl

private theorem dvCanaryCallerFrame :
    dvCanaryState.callerFrame =
      { distinctVariables := [("x", "y")]
        hypothesisLabels := ["wx", "wy"] } := by
  unfold SourceState.callerFrame
  rw [dvCanaryProofDistinctVariables]
  rfl

private theorem dvMissingCallerFrame :
    dvMissingCallerState.callerFrame =
      { distinctVariables := []
        hypothesisLabels := ["wx", "wy"] } := by
  unfold SourceState.callerFrame
  rw [dvMissingCallerProofDistinctVariables]
  rfl

private theorem dvCanaryVocabulary_valid :
    sourceVocabularyValid
        (sourcePrefixVocabulary dvCanaryState.toSourcePrefix) = true := by
  have allowed : ∀ value ∈ dvVocabularyRaw,
      (value != "" &&
        !(value.startsWith reservedRulePrefix) &&
        !(reservedProjectionHeads.contains value)) = true := by
    intro value member
    simp only [dvVocabularyRaw, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
        simp [reservedRulePrefix, reservedProjectionHeads,
          reservedInternalHeads, reservedDataHeads] <;>
        decide +kernel
  have erasedNodup : dvVocabularyRaw.eraseDups.Nodup := by
    decide +kernel
  have sortedNodup : (sortStrings dvVocabularyRaw.eraseDups).Nodup :=
    (List.mergeSort_perm dvVocabularyRaw.eraseDups _).symm.nodup
      erasedNodup
  unfold sourcePrefixVocabulary
  simp only [SourceState.toSourcePrefix]
  rw [dvCanaryCallerFrame]
  simpa [dvCanaryState,
    dvAssertion, stringsOfSourceFrame, stringsOfSourceAssertion,
    stringsOfHypothesis, stringsOfFormula, HypothesisView.label,
    HypothesisView.formula, Metamath.Verify.Sym.value, dvVocabularyRaw] using
      sortedErasedVocabularyValid dvVocabularyRaw allowed sortedNodup

private theorem dvMissingCallerVocabulary_valid :
    sourceVocabularyValid
        (sourcePrefixVocabulary dvMissingCallerState.toSourcePrefix) = true := by
  have allowed : ∀ value ∈ dvMissingCallerVocabularyRaw,
      (value != "" &&
        !(value.startsWith reservedRulePrefix) &&
        !(reservedProjectionHeads.contains value)) = true := by
    intro value member
    simp only [dvMissingCallerVocabularyRaw, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
        simp [reservedRulePrefix, reservedProjectionHeads,
          reservedInternalHeads, reservedDataHeads] <;>
        decide +kernel
  have erasedNodup : dvMissingCallerVocabularyRaw.eraseDups.Nodup := by
    decide +kernel
  have sortedNodup :
      (sortStrings dvMissingCallerVocabularyRaw.eraseDups).Nodup :=
    (List.mergeSort_perm dvMissingCallerVocabularyRaw.eraseDups _).symm.nodup
      erasedNodup
  unfold sourcePrefixVocabulary
  simp only [SourceState.toSourcePrefix]
  rw [dvMissingCallerFrame]
  simpa [dvMissingCallerState, dvCanaryState,
    dvAssertion, stringsOfSourceFrame, stringsOfSourceAssertion,
    stringsOfHypothesis, stringsOfFormula, HypothesisView.label,
    HypothesisView.formula, Metamath.Verify.Sym.value,
    dvMissingCallerVocabularyRaw] using
      sortedErasedVocabularyValid dvMissingCallerVocabularyRaw allowed
        sortedNodup

def dvCanaryGates :
    SourceProjectionGates dvCanaryState.toSourcePrefix where
  prefixValid := sourcePrefixValid_of_sourceStateValid
    dvCanaryState dvCanaryState_valid
  vocabularyValid := dvCanaryVocabulary_valid
  ruleIdsDisjoint := by decide +kernel

def dvMissingCallerGates :
    SourceProjectionGates dvMissingCallerState.toSourcePrefix where
  prefixValid := sourcePrefixValid_of_sourceStateValid
    dvMissingCallerState dvMissingCallerState_valid
  vocabularyValid := dvMissingCallerVocabulary_valid
  ruleIdsDisjoint := by decide +kernel

def dvCanaryLanguage : CalculusLanguageDef :=
  rawSourceInferenceLanguageDef dvCanaryState.toSourcePrefix

def dvMissingCallerLanguage : CalculusLanguageDef :=
  rawSourceInferenceLanguageDef dvMissingCallerState.toSourcePrefix

theorem dvCanaryLanguage_generated :
    calculusLanguageDefOfSourcePrefix? dvCanaryState.toSourcePrefix =
      some dvCanaryLanguage :=
  calculusLanguageDefOfSourcePrefix_eq_some_rawSourceInferenceLanguageDef
    dvCanaryState.toSourcePrefix dvCanaryGates

theorem dvMissingCallerLanguage_generated :
    calculusLanguageDefOfSourcePrefix? dvMissingCallerState.toSourcePrefix =
      some dvMissingCallerLanguage :=
  calculusLanguageDefOfSourcePrefix_eq_some_rawSourceInferenceLanguageDef
    dvMissingCallerState.toSourcePrefix dvMissingCallerGates

def dvCanarySource : AdmittedSourceScope where
  state := dvCanaryState
  stateValid := dvCanaryState_valid
  language := dvCanaryLanguage
  languageGenerated := dvCanaryLanguage_generated

def dvMissingCallerSource : AdmittedSourceScope where
  state := dvMissingCallerState
  stateValid := dvMissingCallerState_valid
  language := dvMissingCallerLanguage
  languageGenerated := dvMissingCallerLanguage_generated

/-! ## Dynamic proof and emitted program -/

def scopeOwner : Atom := stringAtom "canary-scope"
def proofOwner : Atom := stringAtom "canary-proof"

def hypothesisFormula :
    Mettapedia.Languages.Metamath.InferenceEncoding.ConstantHeadedFormula :=
  { typecode := "wff", body := [Metamath.Verify.Sym.var "ph"] }

def hypothesisProof : ProofInput :=
  .normal "canary-theorem" hypothesisFormula ["wph"]

/-- Abstract MM2 program produced from the admitted source and dynamic proof.
The database and proof are ordinary target data; the separately supplied MM2
profile identifies the semantics for which this compiler core is licensed. -/
def hypothesisCanaryProgram : List Atom :=
  compileNormalScopeProgram hypothesisCanarySource scopeOwner ++
    proofInputRows scopeOwner proofOwner hypothesisProof

/-- Target-owned surface lowering to an ordinary `.mm2` program. -/
def renderHypothesisCanary? : Option String :=
  renderProgram? hypothesisCanaryProgram

theorem hypothesisCanaryProgram_is_selected_target_invocation :
    hypothesisCanaryProgram =
      invocationProgram hypothesisCanarySource ordinaryMM2Target
        scopeOwner proofOwner hypothesisProof := by
  rfl

def acceptedFact : Atom :=
  .expression
    [.symbol "mm-accepted", scopeOwner, proofOwner,
      stringAtom "canary-theorem", formulaAtom hypothesisFormula,
      natAtom 0]

def severedProgram : List Atom :=
  compileNormalScopeProgram severedSource scopeOwner ++
    proofInputRows scopeOwner proofOwner hypothesisProof

def renderSeveredCanary? : Option String :=
  renderProgram? severedProgram

def renderAcceptedFact? : Option String :=
  renderAtom? acceptedFact

/-! ## Dynamic assertion proof -/

def assertionProofOwner : Atom := stringAtom "assertion-canary-proof"

def assertionProof : ProofInput :=
  .normal "assertion-canary-theorem" hypothesisFormula ["wph", "ax-ph"]

def assertionCanaryProgram : List Atom :=
  compileNormalScopeProgram assertionCanarySource scopeOwner ++
    proofInputRows scopeOwner assertionProofOwner assertionProof

def renderAssertionCanary? : Option String :=
  renderProgram? assertionCanaryProgram

/-- Removing the assertion while retaining the active hypothesis tests the
assertion source edge independently of proof ingestion and hypothesis lookup. -/
def assertionSeveredProgram : List Atom :=
  compileNormalScopeProgram hypothesisCanarySource scopeOwner ++
    proofInputRows scopeOwner assertionProofOwner assertionProof

def renderAssertionSeveredCanary? : Option String :=
  renderProgram? assertionSeveredProgram

def assertionOccurrence : Atom :=
  .expression
    [.symbol "mm-assertion-occurrence", natAtom 1, stringAtom "ax-ph"]

def assertionAcceptedFact : Atom :=
  .expression
    [.symbol "mm-accepted", scopeOwner, assertionProofOwner,
      stringAtom "assertion-canary-theorem", formulaAtom hypothesisFormula,
      assertionOccurrence]

def renderAssertionAcceptedFact? : Option String :=
  renderAtom? assertionAcceptedFact

/-- A second occurrence of the same assertion proves that MM2's
remove-before-interpret scheduler is reloaded explicitly between assertion
applications. -/
def repeatedAssertionProofOwner : Atom :=
  stringAtom "repeated-assertion-canary-proof"

def repeatedAssertionProof : ProofInput :=
  .normal "repeated-assertion-canary-theorem" hypothesisFormula
    ["wph", "ax-ph", "ax-ph"]

def repeatedAssertionProgram : List Atom :=
  compileNormalScopeProgram assertionCanarySource scopeOwner ++
    proofInputRows scopeOwner repeatedAssertionProofOwner
      repeatedAssertionProof

def renderRepeatedAssertionCanary? : Option String :=
  renderProgram? repeatedAssertionProgram

def repeatedAssertionAcceptedFact : Atom :=
  .expression
    [.symbol "mm-accepted", scopeOwner, repeatedAssertionProofOwner,
      stringAtom "repeated-assertion-canary-theorem",
      formulaAtom hypothesisFormula,
      .expression
        [.symbol "mm-assertion-occurrence", natAtom 2,
          stringAtom "ax-ph"]]

def renderRepeatedAssertionAcceptedFact? : Option String :=
  renderAtom? repeatedAssertionAcceptedFact

/-! ## Dynamic essential-hypothesis proofs -/

def essentialProofOwner : Atom := stringAtom "essential-canary-proof"
def essentialWrongProofOwner : Atom := stringAtom "essential-wrong-proof"

def secondFormula :
    Mettapedia.Languages.Metamath.InferenceEncoding.ConstantHeadedFormula :=
  { typecode := "wff", body := [Metamath.Verify.Sym.var "ps"] }

/-- `wph`, `wps`, and `wph` supply the two floating actuals and the essential
actual for `ax-use`.  The theorem result is the substitution instance `wps`. -/
def essentialProof : ProofInput :=
  .normal "essential-canary-theorem" secondFormula
    ["wph", "wps", "wph", "ax-use"]

/-- The final `wps` deliberately disagrees with the substitution for `ph`.
The essential-hypothesis rule must therefore abstain rather than accept. -/
def essentialWrongProof : ProofInput :=
  .normal "essential-wrong-theorem" secondFormula
    ["wph", "wps", "wps", "ax-use"]

def essentialCanaryProgram : List Atom :=
  compileNormalScopeProgram essentialCanarySource scopeOwner ++
    proofInputRows scopeOwner essentialProofOwner essentialProof

def renderEssentialCanary? : Option String :=
  renderProgram? essentialCanaryProgram

def essentialWrongProgram : List Atom :=
  compileNormalScopeProgram essentialCanarySource scopeOwner ++
    proofInputRows scopeOwner essentialWrongProofOwner essentialWrongProof

def renderEssentialWrongCanary? : Option String :=
  renderProgram? essentialWrongProgram

def essentialAssertionOccurrence : Atom :=
  .expression
    [.symbol "mm-assertion-occurrence", natAtom 3, stringAtom "ax-use"]

def essentialAcceptedFact : Atom :=
  .expression
    [.symbol "mm-accepted", scopeOwner, essentialProofOwner,
      stringAtom "essential-canary-theorem", formulaAtom secondFormula,
      essentialAssertionOccurrence]

def renderEssentialAcceptedFact? : Option String :=
  renderAtom? essentialAcceptedFact

theorem essential_execution_index_is_source_derived :
    assertionExecutionRows scopeOwner essentialCanarySource.state =
      assertionExecutionRowsFor scopeOwner 0 essentialAssertion := by
  rfl

/-! ## Dynamic proof with a nonempty disjoint-variable check -/

def dvProofOwner : Atom := stringAtom "dv-canary-proof"
def dvMissingCallerProofOwner : Atom := stringAtom "dv-missing-caller-proof"

def dvResultFormula :
    Mettapedia.Languages.Metamath.InferenceEncoding.ConstantHeadedFormula :=
  { typecode := "wff"
    body := [Metamath.Verify.Sym.var "x", Metamath.Verify.Sym.var "y"] }

def dvProof : ProofInput :=
  .normal "dv-canary-theorem" dvResultFormula ["wx", "wy", "ax-dv"]

def dvMissingCallerProof : ProofInput :=
  .normal "dv-missing-caller-theorem" dvResultFormula
    ["wx", "wy", "ax-dv"]

def dvCanaryProgram : List Atom :=
  compileNormalScopeProgram dvCanarySource scopeOwner ++
    proofInputRows scopeOwner dvProofOwner dvProof

def dvMissingCallerProgram : List Atom :=
  compileNormalScopeProgram dvMissingCallerSource scopeOwner ++
    proofInputRows scopeOwner dvMissingCallerProofOwner dvMissingCallerProof

def renderDVCanary? : Option String :=
  renderProgram? dvCanaryProgram

def renderDVMissingCaller? : Option String :=
  renderProgram? dvMissingCallerProgram

def dvAssertionOccurrence : Atom :=
  .expression
    [.symbol "mm-assertion-occurrence", natAtom 2, stringAtom "ax-dv"]

def dvAcceptedFact : Atom :=
  .expression
    [.symbol "mm-accepted", scopeOwner, dvProofOwner,
      stringAtom "dv-canary-theorem", formulaAtom dvResultFormula,
      dvAssertionOccurrence]

def renderDVAcceptedFact? : Option String :=
  renderAtom? dvAcceptedFact

theorem caller_dv_relation_is_source_derived :
    callerDVRows scopeOwner dvCanarySource.state =
      [callerDVRow scopeOwner "x" "y",
       callerDVRow scopeOwner "y" "x"] := by
  simp [callerDVRows, dvCanarySource, dvCanaryProofDistinctVariables,
    callerDVRowsOfPairs, callerDVRowsForPair]

theorem missing_caller_dv_relation_is_empty :
    callerDVRows scopeOwner dvMissingCallerSource.state = [] := by
  simp [callerDVRows, dvMissingCallerSource,
    dvMissingCallerProofDistinctVariables, callerDVRowsOfPairs]

/-- The exact row theorem rejects a permission absent from the admitted
caller frame; a target lookup fact cannot authorize it by sharing one endpoint
with a real pair. -/
theorem unlicensed_caller_dv_row_is_absent :
    callerDVRow scopeOwner "x" "z" ∉
      callerDVRows scopeOwner dvCanarySource.state := by
  intro member
  have licensed :=
    (callerDVRow_mem_callerDVRows_iff scopeOwner dvCanarySource.state
      "x" "z").mp member
  have pairs :
      dvCanarySource.state.proofDistinctVariables = [("x", "y")] := by
    simpa [dvCanarySource] using dvCanaryProofDistinctVariables
  rw [pairs] at licensed
  simp [
    Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics.DVRelation]
    at licensed

/-! ## Independent full-cross-product DV machine -/

def dvCrossProductProofOwner : Atom := stringAtom "dv-cross-product-proof"
def dvCrossProductPc : Atom := natAtom 0
def dvCrossProductLabel : Atom := stringAtom "ax-cross-product"
def dvCrossProductContext : Atom :=
  .expression [.symbol "dv-cross-product-context"]

def dvCrossProductLeftBody : Atom :=
  listAtom runtimeSymAtom [.var "x", .var "z"]

def dvCrossProductRightBody : Atom :=
  listAtom runtimeSymAtom [.var "y", .var "w"]

def dvCrossProductSourceBody : Atom :=
  listAtom runtimeSymAtom []

def dvCrossProductState : Atom :=
  .expression
    [.symbol "mm-dv-next-pair", scopeOwner, dvCrossProductProofOwner,
      dvCrossProductPc, dvCrossProductLabel, natAtom 0, natAtom 1,
      dvCrossProductSourceBody, dvCrossProductContext]

def dvCrossProductData : List Atom :=
  [.expression
      [.symbol "mm-assertion-dv-pair", scopeOwner, dvCrossProductLabel,
        natAtom 0, stringAtom "ph", stringAtom "ps"],
   .expression
      [.symbol "mm-assertion-dv-successor", scopeOwner, dvCrossProductLabel,
        natAtom 0, natAtom 1],
   .expression
      [.symbol "mm-substitution", dvCrossProductProofOwner,
        dvCrossProductPc, stringAtom "ph", dvCrossProductLeftBody],
   .expression
      [.symbol "mm-substitution", dvCrossProductProofOwner,
        dvCrossProductPc, stringAtom "ps", dvCrossProductRightBody]]

/-- The four rows are exactly the Cartesian product
`[x,z] × [y,w]`. -/
def dvCrossProductRelations : List Atom :=
  [callerDVRow scopeOwner "x" "y",
   callerDVRow scopeOwner "x" "w",
   callerDVRow scopeOwner "z" "y",
   callerDVRow scopeOwner "z" "w"]

def dvCrossProductProgram : List Atom :=
  normalDVMachineRules ++ dvCrossProductData ++
    dvCrossProductRelations ++ [dvCrossProductState]

/-- Removing only `(z,w)` checks that the machine did not accept after one
representative pair or one row/column of the Cartesian product. -/
def dvCrossProductMissingLastProgram : List Atom :=
  normalDVMachineRules ++ dvCrossProductData ++
    dvCrossProductRelations.dropLast ++ [dvCrossProductState]

def dvCrossProductExpected : Atom :=
  .expression
    [.symbol "mm-body-build", dvCrossProductProofOwner, dvCrossProductPc,
      dvCrossProductSourceBody, .expression [.symbol "mm-nil"],
      dvCrossProductContext]

def renderDVCrossProduct? : Option String :=
  renderProgram? dvCrossProductProgram

def renderDVCrossProductMissingLast? : Option String :=
  renderProgram? dvCrossProductMissingLastProgram

def renderDVCrossProductExpected? : Option String :=
  renderAtom? dvCrossProductExpected

/-! ## Generic body-substitution machine -/

def bodyMatchProofOwner : Atom := stringAtom "body-match-proof"
def bodyMatchPc : Atom := natAtom 0

def bodyMatchSource : Atom :=
  listAtom runtimeSymAtom
    [.const "(", .var "ph", .const "->", .var "ps", .const ")"]

def bodyMatchActual : Atom :=
  listAtom runtimeSymAtom
    [.const "(", .const "a", .const "b", .const "->", .const ")"]

def bodyMatchWrongActual : Atom :=
  listAtom runtimeSymAtom
    [.const "(", .const "b", .const "a", .const "->", .const ")"]

def bodyMatchSuccess : Atom :=
  .expression [.symbol "mm-body-match-succeeded", bodyMatchProofOwner]

def bodyMatchSubstitutions : List Atom :=
  [.expression
    [.symbol "mm-substitution", bodyMatchProofOwner, bodyMatchPc,
      stringAtom "ph",
      listAtom runtimeSymAtom [.const "a", .const "b"]],
   .expression
    [.symbol "mm-substitution", bodyMatchProofOwner, bodyMatchPc,
      stringAtom "ps", listAtom runtimeSymAtom []]]

def bodyMatchState (actual : Atom) : Atom :=
  .expression
    [.symbol "mm-body-match", bodyMatchProofOwner, bodyMatchPc,
      bodyMatchSource, actual, bodyMatchSuccess]

def bodyMatchPositiveProgram : List Atom :=
  normalBodyMatchMachineRules ++ bodyMatchSubstitutions ++
    [bodyMatchState bodyMatchActual]

def bodyMatchWrongProgram : List Atom :=
  normalBodyMatchMachineRules ++ bodyMatchSubstitutions ++
    [bodyMatchState bodyMatchWrongActual]

def renderBodyMatchPositive? : Option String :=
  renderProgram? bodyMatchPositiveProgram

def renderBodyMatchWrong? : Option String :=
  renderProgram? bodyMatchWrongProgram

def renderBodyMatchSuccess? : Option String :=
  renderAtom? bodyMatchSuccess

/-! ## Generic body-construction machine -/

def bodyBuildContext : Atom :=
  .expression [.symbol "body-build-context", bodyMatchProofOwner]

def bodyBuildExpectedBody : Atom :=
  listAtom runtimeSymAtom
    [.const "(", .const "a", .const "b", .const "->", .const ")"]

def bodyBuildState : Atom :=
  .expression
    [.symbol "mm-body-build", bodyMatchProofOwner, bodyMatchPc,
      bodyMatchSource, .expression [.symbol "mm-nil"], bodyBuildContext]

def bodyBuildExpected : Atom :=
  .expression
    [.symbol "mm-body-built", bodyMatchProofOwner, bodyMatchPc,
      bodyBuildContext, bodyBuildExpectedBody]

def bodyBuildPositiveProgram : List Atom :=
  normalBodyBuildMachineRules ++ bodyMatchSubstitutions ++ [bodyBuildState]

/-- Removing the substitution for `ps` must leave construction unresolved;
the builder may not silently erase an unbound source variable. -/
def bodyBuildSeveredProgram : List Atom :=
  normalBodyBuildMachineRules ++ bodyMatchSubstitutions.take 1 ++
    [bodyBuildState]

def renderBodyBuildPositive? : Option String :=
  renderProgram? bodyBuildPositiveProgram

def renderBodyBuildSevered? : Option String :=
  renderProgram? bodyBuildSeveredProgram

def renderBodyBuildExpected? : Option String :=
  renderAtom? bodyBuildExpected

theorem assertion_execution_index_is_source_derived :
    assertionExecutionRows scopeOwner assertionCanarySource.state =
      assertionExecutionRowsFor scopeOwner 0 identityAssertion := by
  rfl

theorem severed_assertion_index_is_empty :
    assertionExecutionRows scopeOwner hypothesisCanarySource.state = [] := by
  rfl

/-- The source-derived lookup table contains the sole executable hypothesis
row. -/
theorem hypothesis_lookup_is_source_derived :
    hypothesisLookupRows scopeOwner hypothesisCanarySource.state =
      [hypothesisLookupRow scopeOwner
        (.floating "wph" "wff" "ph")] := by
  rfl

/-- Removing the active hypothesis from the source removes the lookup row;
the proof input alone cannot authorize the hypothesis step. -/
theorem empty_source_has_no_canary_lookup :
    hypothesisLookupRows scopeOwner severedSource.state = [] := by
  rfl

#print axioms hypothesisCanaryState_valid
#print axioms hypothesisCanaryLanguage_generated
#print axioms hypothesisCanaryProgram_is_selected_target_invocation
#print axioms hypothesis_lookup_is_source_derived
#print axioms severedLanguage_generated
#print axioms empty_source_has_no_canary_lookup
#print axioms assertionCanaryState_valid
#print axioms assertionCanaryLanguage_generated
#print axioms assertion_execution_index_is_source_derived
#print axioms severed_assertion_index_is_empty
#print axioms essentialCanaryState_valid
#print axioms essentialCanaryLanguage_generated
#print axioms essential_execution_index_is_source_derived
#print axioms dvCanaryState_valid
#print axioms dvMissingCallerState_valid
#print axioms dvCanaryLanguage_generated
#print axioms dvMissingCallerLanguage_generated
#print axioms caller_dv_relation_is_source_derived
#print axioms missing_caller_dv_relation_is_empty
#print axioms unlicensed_caller_dv_row_is_absent

end Mettapedia.Languages.Metamath.MM2TransformationCanary
