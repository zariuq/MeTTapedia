import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.BindingLaws
import MettaHyperonFull.Proofs.Substitution

/-!
# Multiple-actual-type failure counterexample

An argument may have several declared actual types.  The published
applicability loop retains one diagnostic for every failed actual type.  This
module pins both sides of repair #13.  The compatibility projection retains
the historical first error, while the authoritative detailed worker and the
function scan retain both failures in declaration order.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMultipleActualTypeCounterexample

private def arrow : Metta.Atom :=
  .expr [.sym "->", .sym "A", .sym "R"]

private def application : Metta.Atom :=
  .expr [.sym "multi-f", .sym "multi-a"]

private def env : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "multi-f", arrow],
    .expr [.sym ":", .sym "multi-a", .sym "B"],
    .expr [.sym ":", .sym "multi-a", .sym "C"]] []

private theorem argumentTypePrep :
    Metta.Minimal.typePrep Metta.Minimal.World.empty (.sym "multi-a") =
      .sym "multi-a" := by
  simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
    Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]

/-- The argument's complete ordered type list contains both declarations. -/
theorem argument_types :
    Metta.Minimal.getTypes env (.sym "multi-a") =
      [.sym "B", .sym "C"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [env, arrow, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem A_does_not_match_B :
    Metta.Minimal.matchType [] (.sym "A") (.sym "B") = none := by
  rfl

private theorem A_does_not_match_C :
    Metta.Minimal.matchType [] (.sym "A") (.sym "C") = none := by
  rfl

private theorem A_matches_A :
    Metta.Minimal.matchType [] (.sym "A") (.sym "A") = some [] := by
  rfl

private theorem A_does_not_match_D :
    Metta.Minimal.matchType [] (.sym "A") (.sym "D") = none := by
  rfl

private theorem B_matches_B :
    Metta.Minimal.matchType [] (.sym "B") (.sym "B") = some [] := by
  rfl

private theorem B_does_not_match_C :
    Metta.Minimal.matchType [] (.sym "B") (.sym "C") = none := by
  rfl

private theorem C_does_not_match_E :
    Metta.Minimal.matchType [] (.sym "C") (.sym "E") = none := by
  rfl

private theorem u_matches_B :
    Metta.Minimal.matchType [] (.var "u") (.sym "B") =
      some [.val "u" (.sym "B")] := by
  have hloop : Metta.Bindings.hasLoop [.val "u" (.sym "B")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hmatch : Metta.matchAtoms (.var "u") (.sym "B") =
      [[.val "u" (.sym "B")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs, hloop]
  have hmerge : Metta.Bindings.merge [] [.val "u" (.sym "B")] =
      [[.val "u" (.sym "B")]] := by
    simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
      Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal]
  have huUndefined : ((.var "u" : Metta.Atom) == .sym "%Undefined%") = false := rfl
  have huAtom : ((.var "u" : Metta.Atom) == .sym "Atom") = false := rfl
  have hBUndefined : ((.sym "B" : Metta.Atom) == .sym "%Undefined%") = false := rfl
  have hBAtom : ((.sym "B" : Metta.Atom) == .sym "Atom") = false := rfl
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    hmatch, hmerge, hloop, huUndefined, huAtom, hBUndefined, hBAtom]

private theorem u_matches_C :
    Metta.Minimal.matchType [] (.var "u") (.sym "C") =
      some [.val "u" (.sym "C")] := by
  have hloop : Metta.Bindings.hasLoop [.val "u" (.sym "C")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hmatch : Metta.matchAtoms (.var "u") (.sym "C") =
      [[.val "u" (.sym "C")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs, hloop]
  have hmerge : Metta.Bindings.merge [] [.val "u" (.sym "C")] =
      [[.val "u" (.sym "C")]] := by
    simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
      Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal]
  have huUndefined : ((.var "u" : Metta.Atom) == .sym "%Undefined%") = false := rfl
  have huAtom : ((.var "u" : Metta.Atom) == .sym "Atom") = false := rfl
  have hCUndefined : ((.sym "C" : Metta.Atom) == .sym "%Undefined%") = false := rfl
  have hCAtom : ((.sym "C" : Metta.Atom) == .sym "Atom") = false := rfl
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    hmatch, hmerge, hloop, huUndefined, huAtom, hCUndefined, hCAtom]

/-- The repaired detailed worker retains both rejected actual types in
declaration order. -/
theorem detailed_argument_failure_keeps_every_actual :
    Metta.Minimal.typeCheckArgsDetailedOutcome env
      Metta.Minimal.World.empty [.sym "A"] 0 [] [.sym "multi-a"] =
        .failure
          { position := 1, expected := .sym "A", actual := .sym "B" }
          [{ position := 1, expected := .sym "A", actual := .sym "C" }] := by
  simp [Metta.Minimal.typeCheckArgsDetailedOutcome,
    Metta.Minimal.scanActualTypes, argumentTypePrep, argument_types,
    Metta.Minimal.typeInferenceAvoid,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
    Metta.instantiate_nil, A_does_not_match_B, A_does_not_match_C]

/-- The old single-error view is now explicitly only a compatibility
projection; it is no longer the boundary used by function selection. -/
theorem compatibility_projection_keeps_only_first_actual :
    Metta.Minimal.typeCheckArgsOutcome env Metta.Minimal.World.empty
      [.sym "A"] 0 [] [.sym "multi-a"] =
        .failure 1 (.sym "A") (.sym "B") := by
  rw [Metta.Minimal.typeCheckArgsOutcome,
    detailed_argument_failure_keeps_every_actual]

/-- The enclosing repaired scan exposes one `BadArgType` for every failed
actual type, in declaration order. -/
theorem selector_emits_every_actual_error :
    Metta.Minimal.selectFunctionType env Metta.Minimal.World.empty
      (.sym "multi-f") [.sym "multi-a"] =
        .exhausted
          [.badArgument 1 (.sym "A") (.sym "B"),
           .badArgument 1 (.sym "A") (.sym "C")] false := by
  have operatorPrep : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "multi-f") = .sym "multi-f" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have functionTypes : Metta.Minimal.getTypes env (.sym "multi-f") =
      [arrow] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [env, arrow, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  rw [Metta.Minimal.selectFunctionType, operatorPrep, functionTypes]
  simp [Metta.Minimal.scanFunctionTypeCandidates, arrow,
    detailed_argument_failure_keeps_every_actual,
    Metta.Minimal.FunctionTypeScanOutcome.prependErrors,
    Metta.Minimal.TypeCheckArgsError.toFunctionTypeError]

/-! ## Cross-argument ordering and multiplicity -/

private theorem symbolTypePrep (name : String) :
    Metta.Minimal.typePrep Metta.Minimal.World.empty (.sym name) =
      .sym name := by
  simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
    Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]

private def mixedEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "mixed", .sym "B"],
    .expr [.sym ":", .sym "mixed", .sym "C"],
    .expr [.sym ":", .sym "bad", .sym "D"]] []

private theorem mixed_types :
    Metta.Minimal.getTypes mixedEnv (.sym "mixed") =
      [.sym "B", .sym "C"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [mixedEnv, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem bad_types :
    Metta.Minimal.getTypes mixedEnv (.sym "bad") = [.sym "D"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [mixedEnv, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

/-- W8: a later total failure is emitted before a latent failed actual from
an earlier successful argument. -/
theorem mixed_latent_errors_are_block_prepended :
    Metta.Minimal.typeCheckArgsDetailedOutcome mixedEnv
      Metta.Minimal.World.empty [.sym "B", .sym "A"] 0 []
        [.sym "mixed", .sym "bad"] =
      .failure
        { position := 2, expected := .sym "A", actual := .sym "D" }
        [{ position := 1, expected := .sym "B", actual := .sym "C" }] := by
  simp [Metta.Minimal.typeCheckArgsDetailedOutcome,
    Metta.Minimal.scanActualTypes, symbolTypePrep, mixed_types, bad_types,
    Metta.Minimal.typeInferenceAvoid, Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, Metta.instantiate_nil,
    B_matches_B, B_does_not_match_C, A_does_not_match_D]

private def threeArgumentEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "first", .sym "B"],
    .expr [.sym ":", .sym "first", .sym "C"],
    .expr [.sym ":", .sym "middle", .sym "A"],
    .expr [.sym ":", .sym "middle", .sym "D"],
    .expr [.sym ":", .sym "last", .sym "E"]] []

private theorem first_types :
    Metta.Minimal.getTypes threeArgumentEnv (.sym "first") =
      [.sym "B", .sym "C"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [threeArgumentEnv, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem middle_types :
    Metta.Minimal.getTypes threeArgumentEnv (.sym "middle") =
      [.sym "A", .sym "D"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [threeArgumentEnv, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem last_types :
    Metta.Minimal.getTypes threeArgumentEnv (.sym "last") = [.sym "E"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [threeArgumentEnv, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

/-- W9: later argument blocks precede earlier blocks across three arguments,
while declaration order inside each block is retained. -/
theorem three_argument_error_blocks_are_reverse_positional :
    Metta.Minimal.typeCheckArgsDetailedOutcome threeArgumentEnv
      Metta.Minimal.World.empty [.sym "B", .sym "A", .sym "C"] 0 []
        [.sym "first", .sym "middle", .sym "last"] =
      .failure
        { position := 3, expected := .sym "C", actual := .sym "E" }
        [{ position := 2, expected := .sym "A", actual := .sym "D" },
         { position := 1, expected := .sym "B", actual := .sym "C" }] := by
  simp [Metta.Minimal.typeCheckArgsDetailedOutcome,
    Metta.Minimal.scanActualTypes, symbolTypePrep, first_types, middle_types,
    last_types, Metta.Minimal.typeInferenceAvoid,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
    Metta.instantiate_nil, B_matches_B, B_does_not_match_C,
    A_matches_A, A_does_not_match_D, C_does_not_match_E]

/-- W10: when several actual types match a type variable, the first match
remains the unique private binding selected by this runtime profile. -/
theorem first_matching_actual_supplies_one_binding :
    Metta.Minimal.typeCheckArgsDetailedOutcome env
      Metta.Minimal.World.empty [.var "u"] 0 [] [.sym "multi-a"] =
      .success [.val "u" (.sym "B")] [] := by
  simp [Metta.Minimal.typeCheckArgsDetailedOutcome,
    Metta.Minimal.scanActualTypes, argumentTypePrep, argument_types,
    Metta.Minimal.typeInferenceAvoid, Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, Metta.instantiate_nil,
    u_matches_B, u_matches_C]

/-! ## Cross-candidate error-block order -/

private def arityFailureArrow : Metta.Atom :=
  .expr [.sym "->", .sym "A", .sym "R0"]

private def argumentFailureArrow : Metta.Atom :=
  .expr [.sym "->", .sym "B", .sym "C", .sym "R1"]

private def candidateBlockEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "block-f", arityFailureArrow],
    .expr [.sym ":", .sym "block-f", argumentFailureArrow],
    .expr [.sym ":", .sym "block-a", .sym "B"],
    .expr [.sym ":", .sym "block-b", .sym "D"]] []

private theorem candidate_block_function_types :
    Metta.Minimal.getTypes candidateBlockEnv (.sym "block-f") =
      [arityFailureArrow, argumentFailureArrow] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [candidateBlockEnv, arityFailureArrow, argumentFailureArrow,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity]

private theorem candidate_block_a_types :
    Metta.Minimal.getTypes candidateBlockEnv (.sym "block-a") =
      [.sym "B"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [candidateBlockEnv, arityFailureArrow, argumentFailureArrow,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity]

private theorem candidate_block_b_types :
    Metta.Minimal.getTypes candidateBlockEnv (.sym "block-b") =
      [.sym "D"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [candidateBlockEnv, arityFailureArrow, argumentFailureArrow,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity]

private theorem C_does_not_match_D :
    Metta.Minimal.matchType [] (.sym "C") (.sym "D") = none := by
  rfl

private theorem candidate_block_second_signature_failure :
    Metta.Minimal.typeCheckArgsDetailedOutcome candidateBlockEnv
      Metta.Minimal.World.empty [.sym "B", .sym "C"] 0 []
        [.sym "block-a", .sym "block-b"] =
      .failure
        { position := 2, expected := .sym "C", actual := .sym "D" } [] := by
  simp [Metta.Minimal.typeCheckArgsDetailedOutcome,
    Metta.Minimal.scanActualTypes, symbolTypePrep,
    candidate_block_a_types, candidate_block_b_types,
    Metta.Minimal.typeInferenceAvoid, Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, Metta.instantiate_nil,
    B_matches_B, C_does_not_match_D]

/-- W16: failed function-candidate blocks are emitted in function-type scan
order and remain contiguous.  The first signature contributes the arity
error; the second contributes its complete argument-error block. -/
theorem selector_preserves_candidate_error_block_order :
    Metta.Minimal.selectFunctionType candidateBlockEnv
      Metta.Minimal.World.empty (.sym "block-f")
        [.sym "block-a", .sym "block-b"] =
      .exhausted
        [.incorrectArity,
          .badArgument 2 (.sym "C") (.sym "D")] false := by
  have notGetType :
      ((.sym "block-f" : Metta.Atom) == .sym "get-type") = false := rfl
  rw [Metta.Minimal.selectFunctionType,
    symbolTypePrep, candidate_block_function_types]
  simp [Metta.Minimal.scanFunctionTypeCandidates,
    arityFailureArrow, argumentFailureArrow,
    candidate_block_second_signature_failure,
    Metta.Minimal.FunctionTypeScanOutcome.prependError,
    Metta.Minimal.FunctionTypeScanOutcome.prependErrors,
    Metta.Minimal.TypeCheckArgsError.toFunctionTypeError, notGetType]

/-! ## Dependent return types expose the discarded successful branch

When the parameter and return share a type variable, the first successful
actual type is no longer observationally interchangeable with later
successes.  The runtime currently keeps only the first private type binding;
the following candidate therefore fails an expected-`C` return check even
though the argument also has a declared `C` type.
-/

private def dependentArrow : Metta.Atom :=
  .expr [.sym "->", .var "u", .var "u"]

private def dependentEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "dependent-f", dependentArrow],
    .expr [.sym ":", .sym "multi-a", .sym "B"],
    .expr [.sym ":", .sym "multi-a", .sym "C"]] []

private theorem dependent_argument_types :
    Metta.Minimal.getTypes dependentEnv (.sym "multi-a") =
      [.sym "B", .sym "C"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [dependentEnv, dependentArrow, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem dependent_function_types :
    Metta.Minimal.getTypes dependentEnv (.sym "dependent-f") =
      [dependentArrow] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [dependentEnv, dependentArrow, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem u_bound_to_B_does_not_match_C :
    Metta.Minimal.matchType [.val "u" (.sym "B")] (.sym "C") (.var "u") =
      none := by
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.matchAtoms, Metta.matchAtomsWith, Metta.Bindings.merge,
    Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
    Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
    Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
    Metta.Atom.size, Metta.Atom.beq, BEq.beq]

private theorem instantiate_u_bound_to_B :
    Metta.instantiate [.val "u" (.sym "B")] (.var "u") = .sym "B" := by
  exact Metta.instantiate_singleton_val_var_of_not_mem
    "u" (.sym "B") (by simp [Metta.Atom.vars])

private theorem u_bound_to_C_matches_C :
    Metta.Minimal.matchType [.val "u" (.sym "C")] (.sym "C") (.var "u") =
      some [.val "u" (.sym "C")] := by
  have hloop : Metta.Bindings.hasLoop [.val "u" (.sym "C")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hmatch : Metta.matchAtoms (.sym "C") (.var "u") =
      [[.val "u" (.sym "C")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs, hloop]
  have hvalues :
      Metta.Bindings.classValues [.val "u" (.sym "C")] "u" =
        [.sym "C"] := by
    simp
  have hunify :
      Metta.Bindings.unifyValues ([.sym "C"] ++ [.sym "C"]) = some [] := by
    simp [Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq, Metta.Atom.size]
  have hadd : Metta.Bindings.addVarBinding [.val "u" (.sym "C")]
      "u" (.sym "C") = [[.val "u" (.sym "C")]] :=
    Metta.Bindings.addVarBinding_nochange
      (by intro name h; cases h) hvalues (by simp) hunify
  have hmerge : Metta.Bindings.merge [.val "u" (.sym "C")]
      [.val "u" (.sym "C")] = [[.val "u" (.sym "C")]] := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using hadd
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.Atom.beq, BEq.beq, hmatch, hmerge, hloop]

private theorem instantiate_u_bound_to_C :
    Metta.instantiate [.val "u" (.sym "C")] (.var "u") = .sym "C" := by
  exact Metta.instantiate_singleton_val_var_of_not_mem
    "u" (.sym "C") (by simp [Metta.Atom.vars])

/-- The detailed argument worker commits to the first successful actual type,
discarding the later successful `C` presentation. -/
theorem dependent_argument_scan_commits_to_first_actual :
    Metta.Minimal.typeCheckArgsDetailedOutcome dependentEnv
      Metta.Minimal.World.empty [.var "u"] 0 [] [.sym "multi-a"] =
      .success [.val "u" (.sym "B")] [] := by
  simp [Metta.Minimal.typeCheckArgsDetailedOutcome,
    Metta.Minimal.scanActualTypes, argumentTypePrep, dependent_argument_types,
    Metta.Minimal.typeInferenceAvoid, Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, Metta.instantiate_nil,
    u_matches_B, u_matches_C]

/-- The retired first-presentation gate fixes the dependent return to `B` and
rejects, even though the argument also admits `u := C`. -/
private def legacyDependentExpectedSelection :
    Metta.Minimal.ExpectedFunctionTypeScanOutcome :=
  match Metta.Minimal.typeCheckArgsDetailedOutcome dependentEnv
      Metta.Minimal.World.empty [.var "u"] 0 [] [.sym "multi-a"] with
  | .success argumentBindings latentErrors =>
      let actualReturn := Metta.instantiate argumentBindings (.var "u")
      match Metta.Minimal.matchType argumentBindings (.sym "C") (.var "u") with
      | some typeBindings => .selected
          ⟨dependentArrow, [.var "u"], .var "u", typeBindings⟩
      | none => .exhausted
          (latentErrors.map (fun error =>
              .ordinary error.toFunctionTypeError) ++
            [.badReturn (.sym "C") actualReturn]) false
  | .failure firstError moreErrors =>
      .exhausted ((firstError :: moreErrors).map (fun error =>
        .ordinary error.toFunctionTypeError)) false

/-- Permanent negative canary for repair #14: the retired first-presentation
gate loses the later viable branch. -/
theorem dependent_candidate_loses_later_viable_presentation :
    legacyDependentExpectedSelection =
      .exhausted [.badReturn (.sym "C") (.sym "B")] false := by
  simp [legacyDependentExpectedSelection,
    dependent_argument_scan_commits_to_first_actual,
    u_bound_to_B_does_not_match_C, instantiate_u_bound_to_B]

/-- The repaired authoritative worker retains both successful presentations
in declaration order. -/
theorem dependent_argument_branches_keep_both_presentations :
    Metta.Minimal.typeCheckArgsBranches dependentEnv
      Metta.Minimal.World.empty [.var "u"] 0 [] [.sym "multi-a"] =
      ⟨[[.val "u" (.sym "B")], [.val "u" (.sym "C")]], []⟩ := by
  simp [Metta.Minimal.typeCheckArgsBranches,
    Metta.Minimal.scanActualTypeBranches, argumentTypePrep,
    dependent_argument_types, Metta.Minimal.typeInferenceAvoid,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
    Metta.instantiate_nil, u_matches_B, u_matches_C]

/-- W11 selection canary: return filtering rejects `u := B`, backtracks
inside applicability, and selects the later `u := C` presentation. -/
theorem repaired_dependent_candidate_selects_later_viable_presentation :
    Metta.Minimal.selectFunctionTypeForExpected dependentEnv
      Metta.Minimal.World.empty (.sym "dependent-f") [.sym "multi-a"]
        (.sym "C") =
      .selected
        ⟨dependentArrow, [.var "u"], .var "u", [.val "u" (.sym "C")]⟩ := by
  have operatorPrep : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "dependent-f") = .sym "dependent-f" :=
    symbolTypePrep "dependent-f"
  rw [Metta.Minimal.selectFunctionTypeForExpected, operatorPrep,
    dependent_function_types]
  simp [Metta.Minimal.scanFunctionTypeCandidatesForExpected, dependentArrow,
    dependent_argument_branches_keep_both_presentations,
    Metta.Minimal.scanExpectedReturnBranches,
    u_bound_to_B_does_not_match_C, u_bound_to_C_matches_C,
    instantiate_u_bound_to_B]

end Mettapedia.Languages.MeTTa.HE.LeaTTaMultipleActualTypeCounterexample
