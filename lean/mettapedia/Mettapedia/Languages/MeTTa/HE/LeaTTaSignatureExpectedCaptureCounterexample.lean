import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Selection
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.Substitution
import MettaHyperonFull.Proofs.TypeSoundness

/-!
# Raw function-signature capture at an expected-type boundary

The repaired argument-candidate freshener protects the complete application
scope, but function signatures are still consumed directly from `getTypes`.
Consequently a signature-private variable can capture an equal-spelled
variable in the caller-supplied expected type.

The reference evaluator at revision `3f76dc46` returns `sigcap-rb` for the
source witness represented below, while the current LeaTTa selector exhausts
with `BadType $t B`.  The independent presentation relation succeeds after
alpha-localizing the signature variable.  These theorems pin the divergence
before any executable repair.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaSignatureExpectedCaptureCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.Selection
open Spec.Type.RuntimeRefinement

private def rawArrow : Metta.Atom :=
  .expr [.sym "->", .var "t", .sym "B"]

private def freshSignatureVariable : String := "####t#1"

private def freshArrow : Metta.Atom :=
  .expr [.sym "->", .var freshSignatureVariable, .sym "B"]

private def repairedTypeBindings : Metta.Bindings :=
  [.val "t" (.sym "B"), .val freshSignatureVariable (.sym "A")]

private def env : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "sigcap-f", rawArrow],
    .expr [.sym ":", .sym "sigcap-a", .sym "A"],
    .expr [.sym ":", .sym "sigcap-rb", .sym "B"]] []

private theorem functionTypes :
    Metta.Minimal.getTypes env (.sym "sigcap-f") = [rawArrow] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [env, rawArrow, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem argumentTypes :
    Metta.Minimal.getTypes env (.sym "sigcap-a") = [.sym "A"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [env, rawArrow, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]

private theorem functionPrep :
    Metta.Minimal.typePrep Metta.Minimal.World.empty (.sym "sigcap-f") =
      .sym "sigcap-f" := by
  simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
    Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]

private theorem argumentPrep :
    Metta.Minimal.typePrep Metta.Minimal.World.empty (.sym "sigcap-a") =
      .sym "sigcap-a" := by
  simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
    Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]

private theorem signatureFreshening :
    Metta.Minimal.freshenFunctionTypeCandidates env
      (.expr [.sym "sigcap-f", .sym "sigcap-a"]) [.sym "sigcap-a"]
      (.var "t") [rawArrow] = [freshArrow] := by
  simp [Metta.Minimal.freshenFunctionTypeCandidates,
    Metta.Minimal.functionTypeSelectionAvoid,
    Metta.Minimal.applicationTypeInferenceScope,
    Metta.Minimal.typeInferenceAvoid,
    Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.captureAvoidingName, Metta.Minimal.avoidancePrefix,
    Metta.Minimal.renameAllVars, env, rawArrow, freshArrow,
    freshSignatureVariable, Metta.Minimal.MinEnv.ofAtomsGT, Metta.Atom.vars]
  decide

private theorem rawFormalMatchesArgument :
    Metta.Minimal.matchType [] (.var "t") (.sym "A") =
      some [.val "t" (.sym "A")] := by
  have loopFree : Metta.Bindings.hasLoop [.val "t" (.sym "A")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have matched : Metta.matchAtoms (.var "t") (.sym "A") =
      [[.val "t" (.sym "A")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, loopFree]
  have merged : Metta.Bindings.merge [] [.val "t" (.sym "A")] =
      [[.val "t" (.sym "A")]] := by
    simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
      Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal]
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    matched, merged, loopFree, Metta.Atom.beq, BEq.beq]

private theorem freshFormalMatchesArgument :
    Metta.Minimal.matchType [] (.var freshSignatureVariable) (.sym "A") =
      some [.val freshSignatureVariable (.sym "A")] := by
  change Metta.Minimal.matchType [] (.var "####t#1") (.sym "A") =
    some [.val "####t#1" (.sym "A")]
  have loopFree : Metta.Bindings.hasLoop
      [.val "####t#1" (.sym "A")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have matched : Metta.matchAtoms (.var "####t#1") (.sym "A") =
      [[.val "####t#1" (.sym "A")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, loopFree]
  have merged : Metta.Bindings.merge []
      [.val "####t#1" (.sym "A")] =
      [[.val "####t#1" (.sym "A")]] := by
    simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
      Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal]
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    matched, merged, loopFree, Metta.Atom.beq, BEq.beq]

private theorem independentExpectedAcceptsReturn :
    Metta.Minimal.matchType
      [.val freshSignatureVariable (.sym "A")] (.var "t") (.sym "B") =
      some repairedTypeBindings := by
  have candidateLoop : Metta.Bindings.hasLoop [.val "t" (.sym "B")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have matched : Metta.matchAtoms (.var "t") (.sym "B") =
      [[.val "t" (.sym "B")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, candidateLoop]
  have namesDiffer : freshSignatureVariable ≠ "t" := by
    simp [freshSignatureVariable]
  have classEmpty : Metta.Bindings.classValues
      [.val freshSignatureVariable (.sym "A")] "t" = [] := by
    simp [Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
      Metta.Bindings.eqVarsInOrder, Metta.Bindings.lookupVal,
      freshSignatureVariable]
  have added : Metta.Bindings.addVarBinding
      [.val freshSignatureVariable (.sym "A")] "t" (.sym "B") =
      [[.val "t" (.sym "B"), .val freshSignatureVariable (.sym "A")]] := by
    have keep : freshSignatureVariable != "t" := by
      simpa only [bne_iff_ne] using namesDiffer
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal, keep] using
      (Metta.Bindings.addVarBinding_fresh classEmpty
        (by intro name h; cases h))
  have merged : Metta.Bindings.merge
      [.val freshSignatureVariable (.sym "A")] [.val "t" (.sym "B")] =
      [[.val "t" (.sym "B"), .val freshSignatureVariable (.sym "A")]] := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using added
  have outputLoop : Metta.Bindings.hasLoop
      [.val "t" (.sym "B"), .val freshSignatureVariable (.sym "A")] = false := by
    simp (config := { maxSteps := 1000000 })
      [Metta.Bindings.hasLoop, Metta.Bindings.vars,
        Metta.Bindings.resolveAtomAux, Metta.Bindings.resolutionFuel,
        Metta.Bindings.relationResolutionFuel, Metta.Atom.vars,
        Metta.Bindings.classValues, Metta.Bindings.lookupVal,
        Metta.Bindings.eqRepresentative, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
        Metta.Atom.size, namesDiffer]
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    matched, merged, outputLoop, repairedTypeBindings,
    Metta.Atom.beq, BEq.beq]

private theorem capturedExpectedRejectsReturn :
    Metta.Minimal.matchType [.val "t" (.sym "A")]
      (.var "t") (.sym "B") = none := by
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.matchAtoms, Metta.matchAtomsWith, Metta.Bindings.merge,
    Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
    Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
    Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
    Metta.Atom.size, Metta.Atom.beq, BEq.beq]

/-- The retired raw-signature scan captures expected `$t` in the
signature-private argument presentation and rejects the otherwise applicable
arrow.  The repaired public selector freshens before entering this unchanged
lower scan, so this theorem permanently pins the old behavior without
reintroducing it as an executable path. -/
theorem raw_signature_scan_rejects_captured_expected_variable :
    Metta.Minimal.scanFunctionTypeCandidatesForExpected env
      Metta.Minimal.World.empty
      (.expr [.sym "sigcap-f", .sym "sigcap-a"])
      [.sym "sigcap-a"] (.var "t") false [rawArrow] =
      .exhausted [.badReturn (.var "t") (.sym "B")] false := by
  have actualScan :
      Metta.Minimal.scanActualTypeBranches [] (.var "t") [.sym "A"] =
        ⟨[[.val "t" (.sym "A")]], []⟩ := by
    simp [Metta.Minimal.scanActualTypeBranches, rawFormalMatchesArgument]
  have returnInert : Metta.instantiate [.val "t" (.sym "A")] (.sym "B") =
      .sym "B" := by
    simp [Metta.instantiate, Metta.Bindings.resolveAtom]
  have returnScan : Metta.Minimal.scanExpectedReturnBranches
      (.var "t") (.sym "B") [[.val "t" (.sym "A")]] =
        ⟨none, [.badReturn (.var "t") (.sym "B")]⟩ := by
    simp [Metta.Minimal.scanExpectedReturnBranches,
      capturedExpectedRejectsReturn, returnInert]
  simp [Metta.Minimal.scanFunctionTypeCandidatesForExpected,
    Metta.Minimal.typeCheckArgsBranchesScoped, argumentPrep, argumentTypes,
    Metta.Minimal.applicationTypeInferenceScope,
    Metta.Minimal.typeInferenceAvoid, Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, rawArrow, actualScan, returnScan,
    Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors]

/-- The repaired selector gives the signature its own private name before
matching.  The argument binds that private name to `A`, while the independent
public expected variable binds to `B`; the candidate therefore succeeds. -/
theorem repaired_selector_accepts_independent_expected_variable :
    Metta.Minimal.selectFunctionTypeForExpected env
      Metta.Minimal.World.empty (.sym "sigcap-f") [.sym "sigcap-a"]
        (.var "t") =
      .selected
        { functionType := freshArrow
          argumentTypes := [.var freshSignatureVariable]
          returnType := .sym "B"
          typeBindings := repairedTypeBindings } := by
  have actualScan : Metta.Minimal.scanActualTypeBranches []
      (.var freshSignatureVariable) [.sym "A"] =
      ⟨[[.val freshSignatureVariable (.sym "A")]], []⟩ := by
    simp [Metta.Minimal.scanActualTypeBranches, freshFormalMatchesArgument]
  have argumentBranches :
      Metta.Minimal.typeCheckArgsBranchesScoped env Metta.Minimal.World.empty
        [.var freshSignatureVariable]
        (Metta.Minimal.applicationTypeInferenceScope (.var "t")
          [.sym "sigcap-a"])
        0 [] [.sym "sigcap-a"] =
      ⟨[[.val freshSignatureVariable (.sym "A")]], []⟩ := by
    simp [Metta.Minimal.typeCheckArgsBranchesScoped,
      Metta.Minimal.applicationTypeInferenceScope, argumentPrep, argumentTypes,
      Metta.Minimal.typeInferenceAvoid, Metta.Minimal.freshenTypeCandidate,
      Metta.Minimal.renameAllVars, actualScan]
  have returnBranches : Metta.Minimal.scanExpectedReturnBranches
      (.var "t") (.sym "B")
        [[.val freshSignatureVariable (.sym "A")]] =
      ⟨some repairedTypeBindings, []⟩ := by
    simp [Metta.Minimal.scanExpectedReturnBranches,
      independentExpectedAcceptsReturn]
  have preparedFunctionTypes : Metta.Minimal.getTypes env
      (Metta.Minimal.typePrep Metta.Minimal.World.empty (.sym "sigcap-f")) =
      [rawArrow] := by
    rw [functionPrep]
    exact functionTypes
  simpa [freshArrow] using
    (Metta.selectFunctionTypeForExpected_singleton_fresh_arrow_selected
      env Metta.Minimal.World.empty "sigcap-f" [.sym "sigcap-a"]
      [.var freshSignatureVariable] rawArrow (.sym "B") (.var "t")
      repairedTypeBindings [[.val freshSignatureVariable (.sym "A")]] [] []
      preparedFunctionTypes signatureFreshening (by simp) argumentBranches
      returnBranches)

private def localizedArrow : Atom :=
  .expression [.symbol "->", .var "u", .symbol "B"]

private def localizedPresentation : TypeSubst :=
  [("t", .symbol "B"), ("u", .symbol "A")]

private theorem localizedFormalMatchesArgument :
    CorePlusR2TypePresentationMatchRel [] (.var "u") (.symbol "A")
      [("u", .symbol "A")] := by
  apply CorePlusR2TypePresentationMatchRel.reduced
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.atomType]
  apply ReducedTypePresentationMatchRel.ordinary
      (resolvedLeft := .var "u") (resolvedRight := .symbol "A")
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [ReducedTypeLeafShape]
  · exact TypeSubst.apply_empty (.var "u")
  · exact TypeSubst.apply_empty (.symbol "A")
  · simpa [TypeSubst.bind, TypeSubst.apply, TypeSubst.lookup,
      TypeSubst.erase] using
      (AppliedReducedTypeMatchRel.bindLeft
        (substitution := []) (name := "u") (right := .symbol "A")
        (by simp [TypeSubst.typeVars]))

private theorem independentExpectedMatchesReturn :
    CorePlusR2TypePresentationMatchRel [("u", .symbol "A")]
      (.var "t") (.symbol "B") localizedPresentation := by
  apply CorePlusR2TypePresentationMatchRel.reduced
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [Atom.atomType]
  · simp [Atom.atomType]
  apply ReducedTypePresentationMatchRel.ordinary
      (resolvedLeft := .var "t") (resolvedRight := .symbol "B")
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [ReducedTypeLeafShape]
  · simp [TypeSubst.apply, TypeSubst.lookup]
  · simp [TypeSubst.apply]
  · simpa [localizedPresentation, TypeSubst.bind, TypeSubst.apply,
      TypeSubst.lookup, TypeSubst.erase, TypeSubst.applyAssignment] using
      (AppliedReducedTypeMatchRel.bindLeft
        (substitution := [("u", .symbol "A")])
        (name := "t") (right := .symbol "B")
        (by simp [TypeSubst.typeVars]))

/-- The executable-independent presentation semantics succeeds when the
signature-private variable is alpha-localized away from the expected type. -/
theorem localized_specification_accepts :
    PresentationArgumentListMatchRel
      [.var "u", .var "t"] [.symbol "A", .symbol "B"]
      [] localizedPresentation := by
  exact .cons localizedFormalMatchesArgument
    (.cons independentExpectedMatchesReturn (.nil localizedPresentation))

/-- The failed proof obligation is mathematically impossible: no
permutation can both fix public `$t` and rename the raw signature to the
localized one. -/
theorem no_public_fixed_signature_localization :
    ¬∃ permutation : Equiv.Perm String,
      permutation "t" = "t" ∧
        localizedArrow = renameTypeVars permutation
          (.expression [.symbol "->", .var "t", .symbol "B"]) := by
  rintro ⟨permutation, fixed, localized⟩
  simp [localizedArrow, renameTypeVars, fixed] at localized

end Mettapedia.Languages.MeTTa.HE.LeaTTaSignatureExpectedCaptureCounterexample
