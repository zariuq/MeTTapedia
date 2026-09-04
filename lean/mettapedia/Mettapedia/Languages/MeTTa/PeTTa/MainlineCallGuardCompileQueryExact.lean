import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

/-!
# Exact query interfaces for the PeTTa call-guard compiler

The authored compiler language uses seven deterministic classification
relations.  This module proves that each fully-bound query is only a filter on
the rule's existing bindings.  Keeping these reverse-adequacy interfaces out
of the source presentation avoids making ordinary language validation depend
on their proof elaboration.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan

set_option autoImplicit false

theorem checkedArgumentClass_encode_iff (expected : Term) :
    isCheckedArgumentClass (argumentModeClass (encodeTerm expected)) = true ↔
      compileArgMode expected = some (.evalSoftcutType expected) := by
  by_cases atom : expected = atomType
  · subst expected
    simp [argumentModeClass, isCheckedArgumentClass, compileArgMode]
  · by_cases undefined : expected = undefinedType
    · subst expected
      simp [argumentModeClass, isCheckedArgumentClass, compileArgMode, atom]
    · by_cases hole : expected = holeType
      · subst expected
        simp [argumentModeClass, isCheckedArgumentClass, compileArgMode, atom,
          undefined]
      · by_cases closed : termIsClosed expected = true
        · simp [argumentModeClass, isCheckedArgumentClass, compileArgMode,
            atom, undefined, hole, closed]
        · simp [argumentModeClass, isCheckedArgumentClass, compileArgMode,
            atom, undefined, hole, closed]

theorem openArgumentClass_encode_iff (expected : Term) :
    argumentModeClass (encodeTerm expected) = some none ↔
      compileArgMode expected = none := by
  simp [argumentModeClass]

theorem checkedResultClass_encode_iff (expected : Term) :
    isCheckedResultClass (resultModeClass (encodeTerm expected)) = true ↔
      compileResultMode expected = some (.resultSoftcutType expected) := by
  by_cases undefined : expected = undefinedType
  · subst expected
    simp [resultModeClass, isCheckedResultClass, compileResultMode]
  · by_cases hole : expected = holeType
    · subst expected
      simp [resultModeClass, isCheckedResultClass, compileResultMode,
        undefined]
    · by_cases atom : expected = atomType
      · subst expected
        simp [resultModeClass, isCheckedResultClass, compileResultMode,
          undefined, hole]
      · by_cases closed : termIsClosed expected = true
        · simp [resultModeClass, isCheckedResultClass, compileResultMode,
            undefined, hole, atom, closed]
        · simp [resultModeClass, isCheckedResultClass, compileResultMode,
            undefined, hole, atom, closed]

theorem openResultClass_encode_iff (expected : Term) :
    resultModeClass (encodeTerm expected) = some none ↔
      compileResultMode expected = none := by
  simp [resultModeClass]

/-- A fully-bound name-inequality premise only filters its existing rule
bindings. -/
theorem premiseStep_notEqual_bound_eq
    (bindings : Bindings) (leftName rightName left right : String)
    (leftLookup : bindings.lookup leftName = some (encodeName left))
    (rightLookup : bindings.lookup rightName = some (encodeName right)) :
    premiseStepWithEnv relationEnv language bindings
        (.relationQuery notEqualRelation
          [.fvar leftName, .fvar rightName]) =
      if left ≠ right then [bindings] else [] := by
  change relationQueryStep relationEnv language bindings notEqualRelation
      ([leftName, rightName].map Pattern.fvar) = _
  have exactResult := relationQueryStep_boundVariables_echo_eq
      (relEnv := relationEnv) (language := language) (bindings := bindings)
      (relation := notEqualRelation) (names := [leftName, rightName])
      (values := [encodeName left, encodeName right])
      (condition := decide (left ≠ right))
      (.cons leftLookup (.cons rightLookup .nil))
      (by simp [builtinRelationTuples, notEqualRelation])
      (by
        rw [relationEnv_notEqual_encodeName]
        by_cases equal : left = right <;> simp [equal])
  simp only [decide_eq_true_eq] at exactResult
  exact exactResult

/-- A fully-bound arity-match premise only filters its existing rule
bindings. -/
theorem premiseStep_arityMatches_bound_eq
    (bindings : Bindings) (inputs : List Term) (arity : Nat)
    (inputsLookup : bindings.lookup "inputs" = some (encodeTerms inputs))
    (arityLookup : bindings.lookup "arity" = some (encodeNat arity)) :
    premiseStepWithEnv relationEnv language bindings
        (.relationQuery arityMatchesRelation [.fvar "inputs", .fvar "arity"]) =
      if inputs.length = arity then [bindings] else [] := by
  change relationQueryStep relationEnv language bindings arityMatchesRelation
      (["inputs", "arity"].map Pattern.fvar) = _
  have exactResult := relationQueryStep_boundVariables_echo_eq
      (relEnv := relationEnv) (language := language) (bindings := bindings)
      (relation := arityMatchesRelation)
      (names := ["inputs", "arity"])
      (values := [encodeTerms inputs, encodeNat arity])
      (condition := decide (inputs.length = arity))
      (.cons inputsLookup (.cons arityLookup .nil))
      (by simp [builtinRelationTuples, arityMatchesRelation])
      (by simp only [relationEnv_arityMatches_encoded, decide_eq_true_eq])
  simp only [decide_eq_true_eq] at exactResult
  exact exactResult

/-- A fully-bound arity-difference premise only filters its existing rule
bindings. -/
theorem premiseStep_arityDiffers_bound_eq
    (bindings : Bindings) (inputs : List Term) (arity : Nat)
    (inputsLookup : bindings.lookup "inputs" = some (encodeTerms inputs))
    (arityLookup : bindings.lookup "arity" = some (encodeNat arity)) :
    premiseStepWithEnv relationEnv language bindings
        (.relationQuery arityDiffersRelation [.fvar "inputs", .fvar "arity"]) =
      if inputs.length ≠ arity then [bindings] else [] := by
  change relationQueryStep relationEnv language bindings arityDiffersRelation
      (["inputs", "arity"].map Pattern.fvar) = _
  have exactResult := relationQueryStep_boundVariables_echo_eq
      (relEnv := relationEnv) (language := language) (bindings := bindings)
      (relation := arityDiffersRelation)
      (names := ["inputs", "arity"])
      (values := [encodeTerms inputs, encodeNat arity])
      (condition := decide (inputs.length ≠ arity))
      (.cons inputsLookup (.cons arityLookup .nil))
      (by simp [builtinRelationTuples, arityDiffersRelation])
      (by simp only [relationEnv_arityDiffers_encoded, decide_eq_true_eq])
  simp only [decide_eq_true_eq] at exactResult
  exact exactResult

/-- Exact row interface for checked-input classification. -/
theorem relationEnv_checkedInput_encoded_eq (expected : Term) :
    relationEnv.tuples checkedInputRelation [encodeTerm expected] =
      if isCheckedArgumentClass (argumentModeClass (encodeTerm expected)) then
        [[encodeTerm expected]]
      else [] := by
  simp [relationEnv, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation, notEqualRelation,
    arityMatchesRelation, arityDiffersRelation, rowWhen]

/-- A fully-bound checked-input premise only filters its existing rule
bindings. -/
theorem premiseStep_checkedInput_bound_eq
    (bindings : Bindings) (expected : Term)
    (expectedLookup : bindings.lookup "expected" =
      some (encodeTerm expected)) :
    premiseStepWithEnv relationEnv language bindings
        (.relationQuery checkedInputRelation [.fvar "expected"]) =
      if isCheckedArgumentClass (argumentModeClass (encodeTerm expected)) then
        [bindings]
      else [] := by
  change relationQueryStep relationEnv language bindings checkedInputRelation
      (["expected"].map Pattern.fvar) = _
  exact relationQueryStep_boundVariables_echo_eq
    (relEnv := relationEnv) (language := language) (bindings := bindings)
    (relation := checkedInputRelation) (names := ["expected"])
    (values := [encodeTerm expected])
    (condition := isCheckedArgumentClass
      (argumentModeClass (encodeTerm expected)))
    (.cons expectedLookup .nil)
    (by simp [builtinRelationTuples])
    (relationEnv_checkedInput_encoded_eq expected)

/-- Exact row interface for unsupported open-input classification. -/
theorem relationEnv_openInput_encoded_eq (expected : Term) :
    relationEnv.tuples openInputRelation [encodeTerm expected] =
      if argumentModeClass (encodeTerm expected) = some none then
        [[encodeTerm expected]]
      else [] := by
  simp [relationEnv, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation, notEqualRelation,
    arityMatchesRelation, arityDiffersRelation, rowWhen]

/-- A fully-bound open-input premise only filters its existing rule bindings. -/
theorem premiseStep_openInput_bound_eq
    (bindings : Bindings) (expected : Term)
    (expectedLookup : bindings.lookup "expected" =
      some (encodeTerm expected)) :
    premiseStepWithEnv relationEnv language bindings
        (.relationQuery openInputRelation [.fvar "expected"]) =
      if argumentModeClass (encodeTerm expected) = some none then
        [bindings]
      else [] := by
  change relationQueryStep relationEnv language bindings openInputRelation
      (["expected"].map Pattern.fvar) = _
  have exactResult := relationQueryStep_boundVariables_echo_eq
      (relEnv := relationEnv) (language := language) (bindings := bindings)
      (relation := openInputRelation) (names := ["expected"])
      (values := [encodeTerm expected])
      (condition := decide
        (argumentModeClass (encodeTerm expected) = some none))
      (.cons expectedLookup .nil)
      (by simp [builtinRelationTuples])
      (by simp only [relationEnv_openInput_encoded_eq, decide_eq_true_eq])
  simp only [decide_eq_true_eq] at exactResult
  exact exactResult

/-- Exact row interface for checked-result classification. -/
theorem relationEnv_checkedResult_encoded_eq (expected : Term) :
    relationEnv.tuples checkedResultRelation [encodeTerm expected] =
      if isCheckedResultClass (resultModeClass (encodeTerm expected)) then
        [[encodeTerm expected]]
      else [] := by
  simp [relationEnv, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation, notEqualRelation,
    arityMatchesRelation, arityDiffersRelation, rowWhen]

/-- A fully-bound checked-result premise only filters its existing rule
bindings. -/
theorem premiseStep_checkedResult_bound_eq
    (bindings : Bindings) (expected : Term)
    (expectedLookup : bindings.lookup "output" = some (encodeTerm expected)) :
    premiseStepWithEnv relationEnv language bindings
        (.relationQuery checkedResultRelation [.fvar "output"]) =
      if isCheckedResultClass (resultModeClass (encodeTerm expected)) then
        [bindings]
      else [] := by
  change relationQueryStep relationEnv language bindings checkedResultRelation
      (["output"].map Pattern.fvar) = _
  exact relationQueryStep_boundVariables_echo_eq
    (relEnv := relationEnv) (language := language) (bindings := bindings)
    (relation := checkedResultRelation) (names := ["output"])
    (values := [encodeTerm expected])
    (condition := isCheckedResultClass
      (resultModeClass (encodeTerm expected)))
    (.cons expectedLookup .nil)
    (by simp [builtinRelationTuples])
    (relationEnv_checkedResult_encoded_eq expected)

/-- Exact row interface for unsupported open-result classification. -/
theorem relationEnv_openResult_encoded_eq (expected : Term) :
    relationEnv.tuples openResultRelation [encodeTerm expected] =
      if resultModeClass (encodeTerm expected) = some none then
        [[encodeTerm expected]]
      else [] := by
  simp [relationEnv, checkedInputRelation, openInputRelation,
    checkedResultRelation, openResultRelation, notEqualRelation,
    arityMatchesRelation, arityDiffersRelation, rowWhen]

/-- A fully-bound open-result premise only filters its existing rule bindings. -/
theorem premiseStep_openResult_bound_eq
    (bindings : Bindings) (expected : Term)
    (expectedLookup : bindings.lookup "output" = some (encodeTerm expected)) :
    premiseStepWithEnv relationEnv language bindings
        (.relationQuery openResultRelation [.fvar "output"]) =
      if resultModeClass (encodeTerm expected) = some none then
        [bindings]
      else [] := by
  change relationQueryStep relationEnv language bindings openResultRelation
      (["output"].map Pattern.fvar) = _
  have exactResult := relationQueryStep_boundVariables_echo_eq
      (relEnv := relationEnv) (language := language) (bindings := bindings)
      (relation := openResultRelation) (names := ["output"])
      (values := [encodeTerm expected])
      (condition := decide
        (resultModeClass (encodeTerm expected) = some none))
      (.cons expectedLookup .nil)
      (by simp [builtinRelationTuples])
      (by simp only [relationEnv_openResult_encoded_eq, decide_eq_true_eq])
  simp only [decide_eq_true_eq] at exactResult
  exact exactResult

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
