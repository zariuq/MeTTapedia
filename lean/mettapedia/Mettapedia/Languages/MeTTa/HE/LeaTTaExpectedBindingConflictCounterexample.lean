import Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeServiceConformance

/-!
# Conflicting applicability bindings

The published applicability algorithm starts from the evaluator's incoming
bindings.  A successful private scan followed by an inconsistent merge is not
equivalent to that algorithm: the private scan commits to a candidate which
the incoming theory rejects, while the later application executor receives no
seed at all.

The canaries below isolate both halves.  The repaired prepared carrier rejects
the inconsistent success because its output must have the model of a normal
finite presentation, while the old post-selection seed merge produces no
branch.  The seeded selector rejects the conflict inside applicability and
retains the return diagnostic before any candidate commits.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingConflictCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Eval
open Spec.Type.Presentation
open Spec.Type.Presentation.Freshness
open Spec.Type.Presentation.Selection
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement
open LeaTTaSpecTypeService
open LeaTTaTypeServiceConformance
open Metta.Minimal

private def identityPreparation : TypePreparationOracle where
  prepare := fun _ atom prepared => prepared = atom

private def conflictExpression : Atom :=
  .expression [.symbol "f"]

private def conflictFunctionType : Atom :=
  .expression [.symbol "->", .symbol "B"]

private def conflictPolicy : SelectedTypePolicy :=
  { functionType := conflictFunctionType
    argumentTypes := []
    returnType := .symbol "B"
    isFunction := rfl }

private def conflictIncoming : Bindings :=
  ⟨[("t", .symbol "A")], []⟩

private def conflictPresentation : TypeSubst :=
  [("t", .symbol "B")]

private def conflictOutput : Bindings :=
  ⟨[("t", .symbol "A"), ("t", .symbol "B")], []⟩

private def conflictSelected : SelectedFunctionType :=
  { functionType := .expr [.sym "->", .sym "B"]
    argumentTypes := []
    returnType := .sym "B"
    typeBindings := [.val "t" (.sym "B")] }

private def conflictRuntimeIncoming : Metta.Bindings :=
  [.val "t" (.sym "A")]

private def conflictEnv : MinEnv :=
  MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", .expr [.sym "->", .sym "B"]]] []

/-- The admitted specification output has no model: it forces `t` to be both
distinct ground type symbols. -/
theorem prepared_candidate_success_output_has_no_model :
    ¬∃ valuation, TypeBindingSatisfied valuation conflictOutput := by
  rintro ⟨valuation, assignments, _equalities⟩
  have tIsA := assignments "t" (.symbol "A") (by
    simp [conflictOutput])
  have tIsB := assignments "t" (.symbol "B") (by
    simp [conflictOutput])
  have impossible : Atom.symbol "A" = Atom.symbol "B" :=
    by simpa [applyTypeValuation] using tIsA.symm.trans tIsB
  simp at impossible

/-- Repair canary: the seeded prepared carrier cannot certify the old
contradictory output, because every successful output is represented by a
normal finite presentation and therefore has a model. -/
theorem prepared_candidate_success_rejects_inconsistent_output :
    ¬PreparedCandidateSuccessRel identityPreparation Space.empty
      conflictExpression conflictFunctionType (.var "t") conflictIncoming
      [("t", .symbol "A")] conflictPolicy conflictOutput := by
  intro success
  rcases success with
    ⟨_operator, _arguments, argumentTypes, _returnType,
      candidateLists, _argumentOutcome, _returnOutcome,
      privatePresentation, _expressionEquation, _functionType, arity,
      prepared, _separated, argumentScan, returnScan, selected,
      _policy, outputPresentation⟩
  have initialNormal : TypeSubst.Normal [("t", .symbol "A")] := by
    simp [TypeSubst.Normal, TypeSubst.keys, TypeSubst.typeVars]
  obtain ⟨argumentPresentation, argumentMember, returnMatch⟩ :=
    returnScan.exists_match_of_selected selected
  have lengthEquation : argumentTypes.length = candidateLists.length := by
    rw [← arity]
    exact prepared.arguments_length.symm
  obtain ⟨_actualTypes, _actualChoices, argumentMatch⟩ :=
    argumentScan.exists_choice_of_mem_success lengthEquation argumentMember
  have argumentNormal : argumentPresentation.Normal :=
    Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
      argumentMatch initialNormal
  have privateNormal : privatePresentation.Normal :=
    returnMatch.output_normal argumentNormal
  let valuation := presentedValuation privatePresentation
  have privateSatisfied : TypeSubstSatisfied valuation privatePresentation :=
    normal_presentedValuation_satisfied privateNormal
  have argumentSatisfied : TypeSubstSatisfied valuation argumentPresentation :=
    (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
      returnMatch argumentNormal valuation).mp privateSatisfied |>.1
  have initialSatisfied : TypeSubstSatisfied valuation [("t", .symbol "A")] :=
    (Spec.Type.Presentation.ApplicationEquivariance.presentationArgumentList_solutions
      argumentMatch initialNormal valuation).mp argumentSatisfied |>.1
  have incomingSatisfied : TypeBindingSatisfied valuation conflictIncoming := by
    simpa [conflictIncoming, TypeSubstSatisfied, TypeBindingSatisfied] using
      initialSatisfied
  have outputSatisfied : TypeBindingSatisfied valuation conflictOutput :=
    (outputPresentation valuation).mpr
      ⟨incomingSatisfied, privateSatisfied⟩
  exact prepared_candidate_success_output_has_no_model
    ⟨valuation, outputSatisfied⟩

private theorem conflictVisibleBindings :
    selectedApplicationVisibleBindings
      (.expr [.sym "f"]) (.var "t") conflictSelected =
        [.val "t" (.sym "B")] := by
  have scope : expectedApplicationVisibleScope
      (.expr [.sym "f"]) (.var "t") = ["t"] := by
    unfold expectedApplicationVisibleScope
    simp only [Metta.Atom.vars, List.map, List.flatten, List.append]
    change ["t"].eraseDups = ["t"]
    rw [List.eraseDups_cons]
    simp
  have resolved : resolveAtom ([.val "t" (.sym "B")] : Metta.Bindings)
      2 (.var "t") = .sym "B" := by
    have instantiated :
        Metta.instantiate ([.val "t" (.sym "B")] : Metta.Bindings)
          (.var "t") = .sym "B" :=
      Metta.instantiate_singleton_val_var_of_not_mem "t" (.sym "B")
        (by simp [Metta.Atom.vars])
    have fixed :
        Metta.instantiate ([.val "t" (.sym "B")] : Metta.Bindings)
          (.sym "B") = .sym "B" :=
      Metta.instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
    have notVariable : ((.sym "B" : Metta.Atom) == .var "t") = false := by
      rfl
    have fixedPoint : ((.sym "B" : Metta.Atom) == .sym "B") = true := by
      rfl
    simp [resolveAtom, instantiated, fixed, notVariable, fixedPoint]
  rw [selectedApplicationVisibleBindings, scope]
  change restrictBnd ["t"] ([.val "t" (.sym "B")] : Metta.Bindings) = _
  unfold restrictBnd
  simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd]
  simp only [List.filterMap_cons, List.filterMap_nil, List.filter_cons,
    List.filter_nil]
  rw [resolved]
  rfl

/-- The runtime half of the same boundary produces no application seed: its
visible `t = B` presentation is incompatible with incoming `t = A`. -/
theorem conflicting_selected_application_has_no_seed :
    selectedApplicationInitialBindings conflictRuntimeIncoming
      (.expr [.sym "f"]) (.var "t") conflictSelected = [] := by
  have values : Metta.Bindings.classValues conflictRuntimeIncoming "t" =
      [.sym "A"] := by
    simp [conflictRuntimeIncoming, Metta.Bindings.classValues,
      Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
      Metta.Bindings.lookupVal]
  have incompatible :
      Metta.Bindings.unifyValues ([.sym "A"] ++ [.sym "B"]) = none := by
    simp [Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq, Metta.Atom.size]
  have rejected : Metta.Bindings.addVarBinding conflictRuntimeIncoming
      "t" (.sym "B") = [] :=
    Metta.Bindings.addVarBinding_conflict
      (by intro name equality; cases equality) values (by simp) incompatible
  rw [selectedApplicationInitialBindings, conflictVisibleBindings]
  simpa [conflictRuntimeIncoming, Metta.Bindings.merge,
    Metta.Bindings.mergeOne] using rejected

private theorem conflictFunctionTypes :
    getTypes conflictEnv (typePrep World.empty (.sym "f")) =
      [.expr [.sym "->", .sym "B"]] := by
  have prepared : typePrep World.empty (.sym "f") = .sym "f" := by
    simp [typePrep, subTokens.eq_1, wrapStates.eq_3, World.empty]
  rw [prepared, getTypes.eq_8]
  simp [conflictEnv, MinEnv.ofAtomsGT, Std.HashMap.getD_emptyWithCapacity]

private theorem conflictFreshenedFunctionTypes :
    freshenFunctionTypeCandidatesAvoiding conflictEnv
      (.expr [.sym "f"]) [] (.var "t") conflictRuntimeIncoming.vars
      [.expr [.sym "->", .sym "B"]] =
        [.expr [.sym "->", .sym "B"]] := by
  simp [freshenFunctionTypeCandidatesAvoiding,
    functionTypeSelectionAvoiding, functionTypeSelectionAvoid,
    applicationTypeInferenceScope, typeInferenceAvoid,
    freshenTypeCandidate, conflictEnv, conflictRuntimeIncoming,
    MinEnv.ofAtomsGT, renameAllVars]

private theorem conflictReturnRejected :
    matchType conflictRuntimeIncoming (.var "t") (.sym "B") = none := by
  have loopFree : Metta.Bindings.hasLoop
      ([.val "t" (.sym "B")] : Metta.Bindings) = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have matched : Metta.matchAtoms (.var "t") (.sym "B") =
      [[.val "t" (.sym "B")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, loopFree]
  have values : Metta.Bindings.classValues conflictRuntimeIncoming "t" =
      [.sym "A"] := by
    simp [conflictRuntimeIncoming, Metta.Bindings.classValues,
      Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
      Metta.Bindings.lookupVal]
  have incompatible :
      Metta.Bindings.unifyValues ([.sym "A"] ++ [.sym "B"]) = none := by
    simp [Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq, Metta.Atom.size]
  have rejected : Metta.Bindings.addVarBinding conflictRuntimeIncoming
      "t" (.sym "B") = [] :=
    Metta.Bindings.addVarBinding_conflict
      (by intro name equality; cases equality) values (by simp) incompatible
  have merged : Metta.Bindings.merge conflictRuntimeIncoming
      [.val "t" (.sym "B")] = [] := by
    simpa [conflictRuntimeIncoming, Metta.Bindings.merge,
      Metta.Bindings.mergeOne] using rejected
  simp [matchType, matchReduced, Metta.Atom.beq, BEq.beq, matched, merged]

/-- Repair canary: seeding applicability with the live evaluator theory turns
the incompatible return gate into an ordinary failed candidate, with its
diagnostic retained, before any selection commit occurs. -/
theorem seeded_selector_rejects_conflicting_candidate :
    selectFunctionTypeForExpectedFrom conflictEnv World.empty
      (.sym "f") [] (.var "t") conflictRuntimeIncoming =
        .exhausted [.badReturn (.var "t") (.sym "B")] false := by
  rw [selectFunctionTypeForExpectedFrom, conflictFunctionTypes,
    conflictFreshenedFunctionTypes]
  have returnInstantiated :
      Metta.instantiate conflictRuntimeIncoming (.sym "B") = .sym "B" :=
    Metta.instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
  simp [scanFunctionTypeCandidatesForExpectedFrom,
    typeCheckArgsBranchesScoped, scanExpectedReturnBranches,
    conflictReturnRejected, returnInstantiated,
    ExpectedFunctionTypeScanOutcome.prependErrors]

end Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingConflictCounterexample
