import Mettapedia.Languages.MeTTa.HE.HumanEvalSpec
import MettaHyperonFull.Minimal.Interpreter

namespace Scratch.LeaTTaExpectedReturnSelectionCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec
open Mettapedia.Languages.MeTTa.HE.HumanTypeSpec
open Mettapedia.Languages.MeTTa.HE.HumanEvalSpec
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def arrowA : Metta.Atom :=
  .expr [.sym "->", .sym "A", .sym "RA"]

private def arrowB : Metta.Atom :=
  .expr [.sym "->", .sym "A", .sym "RB"]

private def application : Metta.Atom :=
  .expr [.sym "f", .sym "a"]

private def env : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", arrowA],
    .expr [.sym ":", .sym "f", arrowB],
    .expr [.sym ":", .sym "a", .sym "A"]] []

#eval Metta.Minimal.getTypes env application
#eval Metta.Minimal.mettaTypeCast env Metta.Minimal.World.empty []
  application (.sym "RB")
private def selectedFunctionType : Option Metta.Atom :=
  match Metta.Minimal.selectFunctionType env Metta.Minimal.World.empty
      (.sym "f") [.sym "a"] with
  | .selected selected => some selected.functionType
  | .exhausted _ _ => none

#eval selectedFunctionType

theorem applicationTypes :
    Metta.Minimal.getTypes env application = [.sym "RA", .sym "RB"] := by
  have hf : Metta.Minimal.getTypes env (.sym "f") = [arrowA, arrowB] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [env, arrowA, arrowB, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have ha : Metta.Minimal.getTypes env (.sym "a") = [.sym "A"] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [env, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hexpr : env.exprTypes = [] := rfl
  have hatoms : env.atoms = [
      .expr [.sym ":", .sym "f", arrowA],
      .expr [.sym ":", .sym "f", arrowB],
      .expr [.sym ":", .sym "a", .sym "A"]] := rfl
  rw [show application = .expr [.sym "f", .sym "a"] from rfl,
    Metta.Minimal.getTypes.eq_10 _ _ _ (by simp)]
  simp [hf, ha, hexpr, hatoms, arrowA, arrowB,
    Metta.Minimal.typeInferenceAvoid, Metta.Atom.vars,
    Metta.Minimal.freshenArgumentTypes,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
    Metta.Minimal.matchApplicationTypeArguments, Metta.Minimal.matchType,
    Metta.Minimal.matchReduced, Metta.matchAtoms, Metta.matchAtomsWith,
    Metta.instantiate_nil, BEq.beq, Metta.Atom.beq]

private theorem applicationTypePrep :
    Metta.Minimal.typePrep Metta.Minimal.World.empty application = application := by
  simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens,
    Metta.Minimal.wrapStates, Metta.Minimal.World.empty, application]

theorem outerCastAcceptsLaterReturn :
    Metta.Minimal.mettaTypeCast env Metta.Minimal.World.empty []
      application (.sym "RB") = .inr [] := by
  rw [Metta.Minimal.mettaTypeCast, applicationTypePrep, applicationTypes]
  rfl

theorem innerSelectorKeepsEarlierReturn : selectedFunctionType = some arrowA := by
  have hprepF : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "f") = .sym "f" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hf : Metta.Minimal.getTypes env (.sym "f") = [arrowA, arrowB] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [env, arrowA, arrowB, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have ha : Metta.Minimal.getTypes env (.sym "a") = [.sym "A"] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [env, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hprepA : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "a") = .sym "a" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hmatch : Metta.Minimal.matchType [] (.sym "A") (.sym "A") = some [] := by
    rfl
  have hcheck : Metta.Minimal.typeCheckArgsOutcome env
      Metta.Minimal.World.empty [.sym "A"] 0 [] [.sym "a"] = .success [] := by
    simp [Metta.Minimal.typeCheckArgsOutcome, hprepA, ha,
      Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
      Metta.instantiate, hmatch]
  rw [selectedFunctionType, Metta.Minimal.selectFunctionType, hprepF, hf]
  simp [Metta.Minimal.scanFunctionTypeCandidates, arrowA, hcheck]

private def humanArrowA : Atom :=
  .expression [.symbol "->", .symbol "A", .symbol "RA"]

private def humanArrowB : Atom :=
  .expression [.symbol "->", .symbol "A", .symbol "RB"]

private def humanApplication : Atom :=
  .expression [.symbol "f", .symbol "a"]

private def humanSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "f", humanArrowA],
    .expression [.symbol ":", .symbol "f", humanArrowB],
    .expression [.symbol ":", .symbol "a", .symbol "A"]]

private theorem mergeEmptyEmpty :
    MergeRel equalityGroundedSemantic
      Bindings.empty Bindings.empty Bindings.empty :=
  .mk (by simp [constraints, Bindings.empty]) MergeConstraintsRel.nil

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

private theorem RBTypeMatch :
    TypeMatchRel (.symbol "RB") (.symbol "RB")
      Bindings.empty Bindings.empty := by
  apply TypeMatchRel.structural
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · exact MatchRel.symSym "RB" semanticLoopFree_empty
  · exact mergeEmptyEmpty

private theorem RBDoesNotMatchRA (incoming output : Bindings) :
    ¬TypeMatchRel (.symbol "RB") (.symbol "RA") incoming output := by
  intro matched
  obtain ⟨_, atomMatch, _⟩ := TypeMatchRel.structural_of_nonWildcard
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType])
    (by simp [Atom.undefinedType]) (by simp [Atom.atomType]) matched
  exact symbol_mismatch_not_match (by simp) _ atomMatch

private theorem RBDoesNotMatchArrowAReturn
    {argumentTypes : List Atom} {returnType : Atom}
    {incoming output : Bindings}
    (functionShape : FunctionTypeRel humanArrowA argumentTypes returnType) :
    ¬TypeMatchRel (.symbol "RB") returnType incoming output := by
  have lists := Atom.expression.inj functionShape
  have last := congrArg List.getLast? lists
  have returnEq : returnType = .symbol "RA" := by
    have rightLast :
        (.symbol "->" :: (argumentTypes ++ [returnType])).getLast? =
          some returnType := by
      rw [show (.symbol "->" :: (argumentTypes ++ [returnType])) =
        ((.symbol "->" :: argumentTypes) ++ [returnType]) by simp]
      rw [List.getLast?_append_of_ne_nil _ (by simp)]
      rfl
    rw [rightLast] at last
    simp at last
    exact last.symm
  subst returnType
  exact RBDoesNotMatchRA incoming output

private theorem aType :
    TypeOfRel humanSpace (.symbol "a") (.symbol "A") := by
  refine ⟨[.symbol "A"], ?_, by simp⟩
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.skip (by simp)
        (AnnotationTypesRel.hit AnnotationTypesRel.nil))
  · simp

private theorem argumentsApplicable :
    ArgumentsApplicableRel humanSpace [.symbol "a"] [.symbol "A"]
      Bindings.empty Bindings.empty :=
  ArgumentsApplicableRel.cons aType ATypeMatch
    (ArgumentsApplicableRel.nil Bindings.empty)

private theorem firstCandidateCannotSucceed (output : Bindings) :
    ¬ApplicationSuccessRel humanSpace humanApplication humanArrowA
      (.symbol "RB") Bindings.empty output := by
  intro success
  cases success with
  | mk _ functionShape _ returnMatch =>
      exact RBDoesNotMatchArrowAReturn functionShape returnMatch

private theorem firstCandidateFailsReturn :
    PublishedCandidateApplicabilityRel humanSpace humanApplication
      humanArrowA (.symbol "RB") Bindings.empty
      (.error (mkError humanApplication
        (.badType (.symbol "RB") (.symbol "RA")))) := by
  apply PublishedCandidateApplicabilityRel.error
  apply ApplicabilityRel.badReturn
      (operator := .symbol "f") (arguments := [.symbol "a"])
      (argumentTypes := [.symbol "A"])
      (returnType := .symbol "RA") (afterArguments := Bindings.empty)
  · rfl
  · rfl
  · exact argumentsApplicable
  · intro candidate
    exact RBDoesNotMatchRA _ candidate
  · exact firstCandidateCannotSucceed

private theorem secondCandidateSucceeds :
    PublishedCandidateApplicabilityRel humanSpace humanApplication
      humanArrowB (.symbol "RB") Bindings.empty
      (.success
        ⟨humanArrowB, [.symbol "A"], .symbol "RB", rfl⟩
        Bindings.empty) := by
  apply PublishedCandidateApplicabilityRel.success
      (argumentTypes := [.symbol "A"]) (returnType := .symbol "RB") rfl
  apply ApplicabilityRel.success
  apply ApplicationSuccessRel.mk
      (operator := .symbol "f") (arguments := [.symbol "a"])
      (argumentTypes := [.symbol "A"]) (returnType := .symbol "RB")
      (afterArguments := Bindings.empty)
  · rfl
  · rfl
  · exact argumentsApplicable
  · exact RBTypeMatch

theorem publishedScanSelectsLaterExpectedReturn :
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      humanSpace humanApplication (.symbol "RB") Bindings.empty
      [humanArrowA, humanArrowB]
      (.success
        ⟨humanArrowB, [.symbol "A"], .symbol "RB", rfl⟩
        Bindings.empty) := by
  apply FunctionCandidateScanRel.functionFailureThenSuccess
      (argumentTypes := [.symbol "A"])
      (candidateReturn := .symbol "RA")
      (error := mkError humanApplication
        (.badType (.symbol "RB") (.symbol "RA")))
  · rfl
  · intro policy output success
    cases success with
    | success _ applicable =>
        cases applicable with
        | success complete => exact firstCandidateCannotSucceed _ complete
  · exact firstCandidateFailsReturn
  · apply FunctionCandidateScanRel.functionSuccess
        (argumentTypes := [.symbol "A"])
        (returnType := .symbol "RB")
    · rfl
    · exact secondCandidateSucceeds

end Scratch.LeaTTaExpectedReturnSelectionCounterexample
