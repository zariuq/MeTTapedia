import Mettapedia.Languages.MeTTa.HE.HumanTypeConformance
import MettaHyperonFull.Proofs.MultipleSignatureSelection
import Std.Data.HashMap.Lemmas

/-!
# Multiple-signature evaluator counterexample

The ordered specification evaluator tries function-type candidates from left
to right and stops at the first applicable candidate.  The repaired runtime
now does the same.  This module retains the removed last-write-wins selection
as a negative canary beside the specification result and repaired selection.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMultipleSignatureCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanMatchMergeSpec
open HumanTypeSpec
open HumanEvalSpec

private def arrowA : Atom :=
  .expression [.symbol "->", .symbol "A", .symbol "RA"]

private def arrowB : Atom :=
  .expression [.symbol "->", .symbol "B", .symbol "RB"]

private def application : Atom :=
  .expression [.symbol "f", .symbol "a"]

private def multiSignatureSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "f", arrowA],
    .expression [.symbol ":", .symbol "f", arrowB],
    .expression [.symbol ":", .symbol "a", .symbol "A"]]

private def leaArrowA : Metta.Atom :=
  .expr [.sym "->", .sym "A", .sym "RA"]

private def leaArrowB : Metta.Atom :=
  .expr [.sym "->", .sym "B", .sym "RB"]

private def leaApplication : Metta.Atom :=
  .expr [.sym "f", .sym "a"]

private def multiSignatureEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", leaArrowA],
    .expr [.sym ":", .sym "f", leaArrowB],
    .expr [.sym ":", .sym "a", .sym "A"]] []

private def noHostDispatch : HumanGroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

private theorem mergeEmptyEmpty :
    MergeRel equalityGroundedSemantic
      Bindings.empty Bindings.empty Bindings.empty :=
  .mk (by simp [constraints, Bindings.empty]) MergeConstraintsRel.nil

private theorem symbolicListMatchEmpty : ∀ names : List String,
    MatchListAccRel equalityGroundedSemantic
      (names.map Atom.symbol) (names.map Atom.symbol)
      Bindings.empty Bindings.empty := by
  intro names
  induction names with
  | nil => exact MatchListAccRel.nil
  | cons name names ih =>
      exact MatchListAccRel.cons
        (MatchRel.symSym name semanticLoopFree_empty)
        mergeEmptyEmpty ih

private theorem arrowATypeMatch :
    TypeMatchRel arrowA arrowA Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural
  · simp [arrowA, Atom.undefinedType]
  · simp [arrowA, Atom.atomType]
  · simp [arrowA, Atom.undefinedType]
  · simp [arrowA, Atom.atomType]
  · apply MatchRel.expression
    · simpa [arrowA] using
        symbolicListMatchEmpty ["->", "A", "RA"]
    · exact semanticLoopFree_empty
  · exact mergeEmptyEmpty

private theorem ATypeMatch :
    TypeMatchRel (.symbol "A") (.symbol "A")
      Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · exact MatchRel.symSym "A" semanticLoopFree_empty
  · exact mergeEmptyEmpty

private theorem RATypeMatch :
    TypeMatchRel (.symbol "RA") (.symbol "RA")
      Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · exact MatchRel.symSym "RA" semanticLoopFree_empty
  · exact mergeEmptyEmpty

private theorem fTypes :
    TypesOfRel multiSignatureSpace (.symbol "f") [arrowA, arrowB] := by
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.hit
      (AnnotationTypesRel.hit
        (AnnotationTypesRel.skip (by simp) AnnotationTypesRel.nil))
  · simp

private theorem aTypes :
    TypesOfRel multiSignatureSpace (.symbol "a") [.symbol "A"] := by
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.skip (by simp)
        (AnnotationTypesRel.hit AnnotationTypesRel.nil))
  · simp

private theorem aType :
    TypeOfRel multiSignatureSpace (.symbol "a") (.symbol "A") :=
  ⟨[.symbol "A"], aTypes, by simp⟩

private theorem firstSignatureApplicable :
    ApplicabilityRel multiSignatureSpace application arrowA
      (.symbol "RA") Bindings.empty (.success Bindings.empty) := by
  apply ApplicabilityRel.success
  apply ApplicationSuccessRel.mk
      (operator := .symbol "f") (arguments := [.symbol "a"])
      (argumentTypes := [.symbol "A"]) (returnType := .symbol "RA")
      (afterArguments := Bindings.empty)
  · rfl
  · rfl
  · exact ArgumentsApplicableRel.cons aType ATypeMatch
      (ArgumentsApplicableRel.nil Bindings.empty)
  · exact RATypeMatch

private theorem firstSignatureSelected :
    FunctionCandidateScanRel ApplicabilityRel multiSignatureSpace
      application (.symbol "RA") Bindings.empty [arrowA, arrowB]
      (.success arrowA (.symbol "RA") Bindings.empty) := by
  apply FunctionCandidateScanRel.functionSuccess
      (argumentTypes := [.symbol "A"])
      (returnType := .symbol "RA")
  · rfl
  · exact firstSignatureApplicable

private theorem fCastToFirstSignature :
    TypeCastRel multiSignatureSpace (.symbol "f") arrowA Bindings.empty
      (.symbol "f", Bindings.empty) := by
  apply TypeCastRel.success
      (types := [arrowA, arrowB]) (earlierTypes := [])
      (laterTypes := [arrowB]) (actualType := arrowA)
  · exact fTypes
  · rfl
  · simp
  · exact arrowATypeMatch

private theorem aCastToA :
    TypeCastRel multiSignatureSpace (.symbol "a") (.symbol "A")
      Bindings.empty (.symbol "a", Bindings.empty) := by
  apply TypeCastRel.success
      (types := [.symbol "A"]) (earlierTypes := [])
      (laterTypes := []) (actualType := .symbol "A")
  · exact aTypes
  · rfl
  · simp
  · exact ATypeMatch

private theorem fRaw :
    HumanEvalAtomRaw multiSignatureSpace noHostDispatch []
      (.symbol "f") arrowA Bindings.empty
      (.symbol "f", Bindings.empty) := by
  apply HumanEvalAtomRaw.cast
      (.symbol "f") arrowA Atom.symbolType Bindings.empty
      (.symbol "f", Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.symbol "f"
  · simp [arrowA, Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨"f", rfl⟩
  · exact fCastToFirstSignature

private theorem aRaw :
    HumanEvalAtomRaw multiSignatureSpace noHostDispatch []
      (.symbol "a") (.symbol "A") Bindings.empty
      (.symbol "a", Bindings.empty) := by
  apply HumanEvalAtomRaw.cast
      (.symbol "a") (.symbol "A") Atom.symbolType Bindings.empty
      (.symbol "a", Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.symbol "a"
  · simp [Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨"a", rfl⟩
  · exact aCastToA

private theorem interpretedArguments :
    HumanInterpretArgs multiSignatureSpace noHostDispatch []
      [.symbol "a"] [.symbol "A"] Bindings.empty
      (.expression [.symbol "a"], Bindings.empty) := by
  apply HumanInterpretArgs.success
      (.symbol "a") [] (.symbol "A") [] Bindings.empty
      (.symbol "a", Bindings.empty) (Atom.unit, Bindings.empty)
  · exact aRaw
  · exact Or.inr rfl
  · exact HumanInterpretArgs.nil Bindings.empty
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, Atom.unit]

private theorem interpretedFunction :
    HumanInterpretFunction multiSignatureSpace noHostDispatch []
      application arrowA (.symbol "RA") Bindings.empty
      (application, Bindings.empty) := by
  apply HumanInterpretFunction.success
      application arrowA (.symbol "RA") (.symbol "f")
      [.symbol "a"] [.symbol "A"] Bindings.empty
      (.symbol "f", Bindings.empty)
      (.expression [.symbol "a"], Bindings.empty)
  · rfl
  · rfl
  · exact fRaw
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact interpretedArguments
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]

private theorem applicationNoEquation :
    HumanCall multiSignatureSpace noHostDispatch []
      application (.symbol "RA") Bindings.empty
      (application, Bindings.empty) := by
  apply HumanCall.noEquation
  · simp [application, IsErrorRel]
  · simp [application, noHostDispatch, NonGroundedCallRel]
  · intro freshPattern freshRhs matched ruleMatch
    obtain ⟨rawLhs, rawRhs, ruleMember, _⟩ := ruleMatch
    simp [multiSignatureSpace, Space.ofList] at ruleMember

private theorem interpretedExpression :
    HumanInterpretExpression multiSignatureSpace noHostDispatch []
      application (.symbol "RA") Bindings.empty
      (application, Bindings.empty) := by
  apply HumanInterpretExpression.functionPath
      application (.symbol "RA") (.symbol "f") [.symbol "a"]
      [arrowA, arrowB] arrowA (.symbol "RA") (.symbol "RA")
      Bindings.empty Bindings.empty
      (application, Bindings.empty) (application, Bindings.empty)
  · rfl
  · exact fTypes
  · exact firstSignatureSelected
  · simp [Atom.expressionType]
  · exact interpretedFunction
  · exact applicationNoEquation

/-- Independent human result: the earlier applicable declaration wins, so
the application is a non-error normal form. -/
theorem human_ordered_scan_accepts_earlier_signature :
    HumanEval multiSignatureSpace noHostDispatch []
      application (.symbol "RA") Bindings.empty
      (application, Bindings.empty) := by
  constructor
  · apply HumanEvalAtomRaw.interpretSuccess
        application (.symbol "RA") Atom.expressionType Bindings.empty
        (application, Bindings.empty)
    · simp [application, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact MetaTypeRel.expression [.symbol "f", .symbol "a"]
    · simp [Atom.atomType,
        Atom.expressionType, Atom.variableType]
    · exact ⟨.symbol "f", [.symbol "a"], rfl⟩
    · exact interpretedExpression
    · simp [application, IsErrorRel]
  · intro resultError
    simp [application, IsErrorRel] at resultError

/-- Concrete historical index defect: the removed evaluator signature table
retains only the last arrow declaration even though `getTypes` retains both. -/
theorem runtime_signature_index_keeps_only_last :
    (Metta.legacySignatureIndex [
      .expr [.sym ":", .sym "f", leaArrowA],
      .expr [.sym ":", .sym "f", leaArrowB],
      .expr [.sym ":", .sym "a", .sym "A"]]).get? "f" =
      some [.sym "B", .sym "RB"] := by
  simp [Metta.legacySignatureIndex, leaArrowA, leaArrowB]

/-- The complete runtime lookup still exposes both declarations in source
order. -/
theorem runtime_getTypes_keeps_both_signatures :
    Metta.Minimal.getTypes multiSignatureEnv (.sym "f") =
      [leaArrowA, leaArrowB] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [multiSignatureEnv, Metta.Minimal.MinEnv.ofAtomsGT,
    leaArrowA, leaArrowB, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity]

/-- Permanent negative canary for the removed selection boundary: feeding only
the historical last cached signature rejects the call that the earlier
signature accepts. -/
theorem runtime_last_signature_rejects_earlier_applicable_call :
    Metta.Minimal.scanFunctionTypeCandidates multiSignatureEnv
        Metta.Minimal.World.empty leaApplication [.sym "a"] false
        [leaArrowB] =
      .exhausted [.badArgument 1 (.sym "B") (.sym "A")] false := by
  have hprep : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "a") = .sym "a" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have htypes : Metta.Minimal.getTypes multiSignatureEnv (.sym "a") =
      [.sym "A"] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [multiSignatureEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hmatch : Metta.Minimal.matchType [] (.sym "B") (.sym "A") = none := by
    rfl
  simp [Metta.Minimal.scanFunctionTypeCandidates, leaArrowB,
    Metta.Minimal.typeCheckArgsOutcome, hprep, htypes,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
    Metta.instantiate, hmatch, Metta.Minimal.FunctionTypeScanOutcome.prependError]

/-- Positive repair canary: the runtime's sole ordered selection boundary now
chooses the earlier applicable declaration.  The fork proof module additionally
pins the resulting `mettaEval` observation. -/
theorem repaired_runtime_selects_earlier_applicable_signature :
    ∃ selected,
      Metta.Minimal.selectFunctionType multiSignatureEnv
          Metta.Minimal.World.empty (.sym "f") [.sym "a"] =
        .selected selected ∧ selected.functionType = leaArrowA := by
  have hprep : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "f") = .sym "f" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hatypes : Metta.Minimal.getTypes multiSignatureEnv (.sym "a") =
      [.sym "A"] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [multiSignatureEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hmatch : Metta.Minimal.matchType [] (.sym "A") (.sym "A") = some [] := by
    rfl
  have hprepArg : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "a") = .sym "a" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hcheck :
      Metta.Minimal.typeCheckArgsOutcome multiSignatureEnv
          Metta.Minimal.World.empty [.sym "A"] 0 [] [.sym "a"] =
        .success [] := by
    simp [Metta.Minimal.typeCheckArgsOutcome, hprepArg, hatypes,
      Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
      Metta.instantiate, hmatch]
  refine ⟨⟨leaArrowA, [.sym "A"], .sym "RA", []⟩, ?_, rfl⟩
  rw [Metta.Minimal.selectFunctionType, hprep,
    runtime_getTypes_keeps_both_signatures]
  simp [Metta.Minimal.scanFunctionTypeCandidates, leaArrowA, hcheck]

end Mettapedia.Languages.MeTTa.HE.LeaTTaMultipleSignatureCounterexample
