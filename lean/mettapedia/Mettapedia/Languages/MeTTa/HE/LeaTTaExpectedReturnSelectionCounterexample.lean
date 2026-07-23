import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.Substitution

/-!
# Expected-return selection counterexample

The repaired runtime exposes all argument-applicable return types when it
casts a whole application, but its subsequent function-policy scan selects
the first argument-applicable signature without consulting that accepted
expected return.  With two signatures that share an argument type but return
different types, the two scans can therefore choose different declarations.

The independent published evaluator scans each signature conjunctively over
its arguments and expected return.  The final theorem pins the corresponding
later-signature selection.  This module records the divergence before any
runtime repair is attempted.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedReturnSelectionCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
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

private def selectedFunctionType : Option Metta.Atom :=
  match Metta.Minimal.selectFunctionType env Metta.Minimal.World.empty
      (.sym "f") [.sym "a"] with
  | .selected selected => some selected.functionType
  | .exhausted _ _ => none

/-- The whole-application type lookup retains both argument-applicable return
types in declaration order. -/
theorem application_types :
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

private theorem application_type_prep :
    Metta.Minimal.typePrep Metta.Minimal.World.empty application = application := by
  simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens,
    Metta.Minimal.wrapStates, Metta.Minimal.World.empty, application]

/-- The outer cast accepts the later `RB` return candidate. -/
theorem outer_cast_accepts_later_return :
    Metta.Minimal.mettaTypeCast env Metta.Minimal.World.empty []
      application (.sym "RB") = .inr [] := by
  rw [Metta.Minimal.mettaTypeCast, application_type_prep, application_types]
  rfl

/-- The independent inner policy scan nevertheless selects the earlier `RA`
signature, because it has no expected-return input. -/
theorem inner_selector_keeps_earlier_return :
    selectedFunctionType = some arrowA := by
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

private def specArrowA : Atom :=
  .expression [.symbol "->", .symbol "A", .symbol "RA"]

private def specArrowB : Atom :=
  .expression [.symbol "->", .symbol "A", .symbol "RB"]

private def specPolicyA : SelectedTypePolicy :=
  ⟨specArrowA, [.symbol "A"], .symbol "RA", rfl⟩

private def specPolicyB : SelectedTypePolicy :=
  ⟨specArrowB, [.symbol "A"], .symbol "RB", rfl⟩

private def specApplication : Atom :=
  .expression [.symbol "f", .symbol "a"]

private def specSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "f", specArrowA],
    .expression [.symbol ":", .symbol "f", specArrowB],
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
    (functionShape : FunctionTypeRel specArrowA argumentTypes returnType) :
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
    TypeOfRel specSpace (.symbol "a") (.symbol "A") := by
  refine ⟨[.symbol "A"], ?_, by simp⟩
  apply TypesOfRel.symbolKnown
  · exact AnnotationTypesRel.skip (by simp)
      (AnnotationTypesRel.skip (by simp)
        (AnnotationTypesRel.hit AnnotationTypesRel.nil))
  · simp

private theorem argumentsApplicable :
    ArgumentsApplicableRel specSpace [.symbol "a"] [.symbol "A"]
      Bindings.empty Bindings.empty :=
  ArgumentsApplicableRel.cons aType ATypeMatch
    (ArgumentsApplicableRel.nil Bindings.empty)

private theorem firstCandidateCannotSucceed (output : Bindings) :
    ¬ApplicationSuccessRel specSpace specApplication specArrowA
      (.symbol "RB") Bindings.empty output := by
  intro success
  cases success with
  | mk _ functionShape _ returnMatch =>
      exact RBDoesNotMatchArrowAReturn functionShape returnMatch

private theorem firstCandidateFailsReturn :
    PublishedCandidateApplicabilityRel specSpace specApplication
      specArrowA (.symbol "RB") Bindings.empty
      (.error [mkError specApplication
        (.badType (.symbol "RB") (.symbol "RA"))]) := by
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
    PublishedCandidateApplicabilityRel specSpace specApplication
      specArrowB (.symbol "RB") Bindings.empty
      (.success specPolicyB Bindings.empty) := by
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

/-- The published evaluator rejects the earlier `RA` candidate on its return
check and selects the later `RB` candidate. -/
theorem published_scan_selects_later_expected_return :
    FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      specSpace specApplication (.symbol "RB") Bindings.empty
      [specArrowA, specArrowB]
      (.success specPolicyB Bindings.empty) := by
  apply FunctionCandidateScanRel.functionFailureThenSuccess
      (argumentTypes := [.symbol "A"])
      (candidateReturn := .symbol "RA")
      (candidateErrors := [mkError specApplication
        (.badType (.symbol "RB") (.symbol "RA"))])
  · rfl
  · intro policy output success
    cases success with
    | success _ applicable =>
        cases applicable with
        | success complete => exact firstCandidateCannotSucceed _ complete
  · exact firstCandidateFailsReturn
  · simp
  · apply FunctionCandidateScanRel.functionSuccess
        (argumentTypes := [.symbol "A"])
        (returnType := .symbol "RB")
    · rfl
    · exact secondCandidateSucceeds

/-- The published scan cannot select the earlier `RA` policy when the caller
expects `RB`.  This is the negative half of the selection-boundary canary:
the candidate exists and its argument is applicable, but its return is not. -/
theorem published_scan_rejects_earlier_return_policy
    (output : Bindings) :
    ¬FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      specSpace specApplication (.symbol "RB") Bindings.empty
      [specArrowA, specArrowB] (.success specPolicyA output) := by
  intro scan
  have selected := published_scan_success_selected scan
  cases selected.2 with
  | success applicable =>
      exact firstCandidateCannotSucceed output applicable

/-- Kernel-checked pre-repair selection divergence: the unconstrained selector
chooses the first argument-applicable `RA` declaration, while the published
scan selects the later declaration whose return also satisfies expected
`RB`.  The unconstrained selector remains the ordinary-evaluation compatibility
path; embedded `metta` now uses the expected-aware selector pinned below. -/
theorem expected_return_policy_selection_diverges :
    selectedFunctionType = some arrowA ∧
      FunctionCandidateScanRel PublishedCandidateApplicabilityRel
        specSpace specApplication (.symbol "RB") Bindings.empty
        [specArrowA, specArrowB]
        (.success specPolicyB Bindings.empty) :=
  ⟨inner_selector_keeps_earlier_return,
    published_scan_selects_later_expected_return⟩

private def selectedExpectedFunctionType : Option Metta.Atom :=
  match Metta.Minimal.selectFunctionTypeForExpected env Metta.Minimal.World.empty
      (.sym "f") [.sym "a"] (.sym "RB") with
  | .selected selected => some selected.functionType
  | .exhausted _ _ => none

/-- Repair canary: the expected-aware runtime boundary rejects the earlier
`RA` return and selects the same later `RB` signature as the published scan. -/
theorem repaired_selector_selects_later_expected_return :
    selectedExpectedFunctionType = some arrowB := by
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
  have hmatchA : Metta.Minimal.matchType [] (.sym "A") (.sym "A") = some [] := by
    rfl
  have hreturnA : Metta.Minimal.matchType [] (.sym "RB") (.sym "RA") = none := by
    rfl
  have hreturnB : Metta.Minimal.matchType [] (.sym "RB") (.sym "RB") = some [] := by
    rfl
  have hcheck : Metta.Minimal.typeCheckArgsOutcome env
      Metta.Minimal.World.empty [.sym "A"] 0 [] [.sym "a"] = .success [] := by
    simp [Metta.Minimal.typeCheckArgsOutcome, hprepA, ha,
      Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
      Metta.instantiate, hmatchA]
  rw [selectedExpectedFunctionType, Metta.Minimal.selectFunctionTypeForExpected,
    hprepF, hf]
  simp [Metta.Minimal.scanFunctionTypeCandidatesForExpected, arrowA, arrowB,
    hcheck, hreturnA, hreturnB,
    Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependError]

/-! ## Pre-instantiated-return wildcard counterexample

This witness distinguishes a literal `Atom` return from a type variable that
the argument fold has bound to `Atom`.  The published gate examines the raw
return syntax under the threaded theory, so only the former is a wildcard.
The first repair-#11 implementation instead instantiated the return before
the wildcard test and therefore accepted the latter incorrectly. -/

private def dependentArrow : Metta.Atom :=
  .expr [.sym "->", .expr [.sym "P", .var "t"], .var "t"]

private def dependentArgumentType : Metta.Atom :=
  .expr [.sym "P", .sym "Atom"]

private def dependentEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "dependent-f", dependentArrow],
    .expr [.sym ":", .sym "dependent-a", dependentArgumentType]] []

private def preinstantiatedReturnGate
    (bindings : Metta.Bindings) (expected returnType : Metta.Atom) :
    Option Metta.Bindings :=
  Metta.Minimal.matchType bindings expected
    (Metta.instantiate bindings returnType)

/-- The retired pre-instantiating gate accepts a return variable whose
argument-fold presentation is `t = Atom`, exposing the bound value as a
wildcard.  This theorem permanently pins the buggy capability independently
of the repaired selector. -/
theorem preinstantiated_return_exposes_bound_atom_wildcard :
    preinstantiatedReturnGate [.val "t" (.sym "Atom")]
      (.sym "B") (.var "t") =
        some [.val "t" (.sym "Atom")] := by
  rw [preinstantiatedReturnGate,
    Metta.instantiate_singleton_val_var_of_not_mem
      "t" (.sym "Atom") (by simp [Metta.Atom.vars])]
  rfl

private theorem dependentArgument_match : Metta.Minimal.matchType []
    (.expr [.sym "P", .var "t"])
    (.expr [.sym "P", .sym "Atom"]) =
      some [.val "t" (.sym "Atom")] := by
  have hloop : Metta.Bindings.hasLoop
      ([.val "t" (.sym "Atom")] : Metta.Bindings) = false := by
    simpa using Metta.Bindings.hasLoop_singleton_val_of_not_mem
      "t" (.sym "Atom") (by simp [Metta.Atom.vars])
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.Minimal.matchReducedList, Metta.matchAtoms,
    Metta.matchAtomsWith, Metta.Bindings.merge,
    Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
    Metta.Atom.beq, BEq.beq, hloop]

/-- The repaired raw-return gate rejects the candidate and retains the
instantiated return only in its diagnostic. -/
theorem repaired_selector_rejects_bound_atom_wildcard :
    Metta.Minimal.selectFunctionTypeForExpected dependentEnv
      Metta.Minimal.World.empty (.sym "dependent-f")
      [.sym "dependent-a"] (.sym "B") =
        .exhausted [.badReturn (.sym "B") (.sym "Atom")] false := by
  have hprepF : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "dependent-f") = .sym "dependent-f" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hf : Metta.Minimal.getTypes dependentEnv (.sym "dependent-f") =
      [dependentArrow] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [dependentEnv, dependentArrow, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have ha : Metta.Minimal.getTypes dependentEnv (.sym "dependent-a") =
      [dependentArgumentType] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [dependentEnv, dependentArgumentType,
      Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
      Std.HashMap.getD_emptyWithCapacity]
  have hprepA : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "dependent-a") = .sym "dependent-a" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hcheck : Metta.Minimal.typeCheckArgsOutcome dependentEnv
      Metta.Minimal.World.empty [.expr [.sym "P", .var "t"]] 0 []
        [.sym "dependent-a"] =
          .success [.val "t" (.sym "Atom")] := by
    simp [Metta.Minimal.typeCheckArgsOutcome, hprepA, ha,
      dependentArgumentType, Metta.Minimal.freshenTypeCandidate,
      Metta.Minimal.renameAllVars, Metta.instantiate,
      dependentArgument_match]
  have hreturn : Metta.Minimal.matchType [.val "t" (.sym "Atom")]
      (.sym "B") (.var "t") = none := by
    simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
      Metta.matchAtoms, Metta.matchAtomsWith, Metta.Bindings.merge,
      Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
      Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
      Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
      Metta.Atom.size, Metta.Atom.beq, BEq.beq]
  have hinstantiate : Metta.instantiate [.val "t" (.sym "Atom")]
      (.var "t") = .sym "Atom" := by
    exact Metta.instantiate_singleton_val_var_of_not_mem
      "t" (.sym "Atom") (by simp [Metta.Atom.vars])
  rw [Metta.Minimal.selectFunctionTypeForExpected, hprepF, hf]
  simp [Metta.Minimal.scanFunctionTypeCandidatesForExpected,
    dependentArrow, hcheck, hinstantiate, hreturn,
    Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependError]

/-- The raw-return specification rejects the same candidate: the argument
constraint forces `t = Atom`, while the return constraint forces `t = B`.
The two facts have no common valuation. -/
theorem raw_return_gate_rejects_bound_atom :
    ¬∃ output,
      PresentationArgumentListMatchRel
        [.expression [.symbol "P", .var "t"], .symbol "B"]
        [.expression [.symbol "P", .symbol "Atom"], .var "t"]
        [] output := by
  intro success
  have model := (presentationArgumentList_exists_iff
    [.expression [.symbol "P", .var "t"], .symbol "B"]
    [.expression [.symbol "P", .symbol "Atom"], .var "t"]).mp success
  rcases model with ⟨valuation, consistency⟩
  cases consistency with
  | cons argumentConsistency returnConsistency =>
      cases returnConsistency with
      | cons resultConsistency tailConsistency =>
          simp [CorePlusR2TypeConsistent, ReducedTypeConsistent,
            ReducedTypeListConsistent, applyTypeValuation,
            Atom.undefinedType, Atom.atomType] at argumentConsistency resultConsistency
          rw [argumentConsistency] at resultConsistency
          simp at resultConsistency

end Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedReturnSelectionCounterexample
