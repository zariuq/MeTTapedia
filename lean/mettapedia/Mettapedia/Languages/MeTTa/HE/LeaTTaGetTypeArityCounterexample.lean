import Mettapedia.Languages.MeTTa.HE.Spec.Type
import MettaHyperonFull.Minimal.Interpreter

/-!
# Legacy `get-type` arity exemption

Function applicability in the published interpreter requires the call and
arrow to have exactly the same number of arguments.  The runtime scanner has
a legacy Boolean exemption used only by `get-type`; with that flag enabled,
the unary `get-type` arrow accepts a second space argument.

The reference evaluator at revision `3f76dc46` rejects the corresponding
two-argument application with `IncorrectNumberOfArguments`.  The repaired
public selectors now agree with that behavior.  The low-level Boolean worker
can still express the retired compatibility behavior, which is retained here
only as the negative historical canary.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaGetTypeArityCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def unaryArrow : Metta.Atom :=
  .expr [.sym "->", .sym "Atom", .sym "Atom"]

private def env : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [] []

private def selectorEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT
    [.expr [.sym ":", .sym "get-type", unaryArrow]] []

private theorem selectorCandidates :
    Metta.Minimal.getTypes selectorEnv (.sym "get-type") = [unaryArrow] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [selectorEnv, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_emptyWithCapacity]

private theorem selectorTypePrep :
    Metta.Minimal.typePrep Metta.Minimal.World.empty (.sym "get-type") =
      .sym "get-type" := by
  simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
    Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]

private def runtimeExpression : Metta.Atom :=
  .expr [.sym "get-type", .sym "A", .sym "&self"]

private def selected : Metta.Minimal.SelectedFunctionType :=
  { functionType := unaryArrow
    argumentTypes := [.sym "Atom"]
    returnType := .sym "Atom"
    typeBindings := [] }

private theorem freshenedUnaryArrow (avoid : List Metta.VarName)
    (position : Nat) :
    Metta.Minimal.freshenTypeCandidate avoid position unaryArrow = unaryArrow := by
  simp [Metta.Minimal.freshenTypeCandidate, unaryArrow,
    Metta.Minimal.renameAllVars]

private theorem freshenedSelectorCandidates (liveAvoid : List Metta.VarName) :
    Metta.Minimal.freshenFunctionTypeCandidatesAvoiding selectorEnv
      runtimeExpression [.sym "A", .sym "&self"] (.sym "%Undefined%")
      liveAvoid [unaryArrow] = [unaryArrow] := by
  simp only [Metta.Minimal.freshenFunctionTypeCandidatesAvoiding, List.map,
    freshenedUnaryArrow]

private theorem actualTypes :
    Metta.Minimal.getTypes env (.sym "A") = [.sym "%Undefined%"] := by
  rw [Metta.Minimal.getTypes.eq_8]
  simp [env, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_emptyWithCapacity]

private theorem atomMatchesUndefined :
    Metta.Minimal.matchType [] (.sym "Atom") (.sym "%Undefined%") =
      some [] := by
  rfl

private theorem undefinedMatchesAtom :
    Metta.Minimal.matchType [] (.sym "%Undefined%") (.sym "Atom") =
      some [] := by
  rfl

private theorem argumentBranches :
    Metta.Minimal.typeCheckArgsBranchesScoped env Metta.Minimal.World.empty
      [.sym "Atom"]
      (Metta.Minimal.applicationTypeInferenceScope (.sym "%Undefined%")
        [.sym "A", .sym "&self"])
      0 [] [.sym "A", .sym "&self"] = ⟨[[]], []⟩ := by
  simp [Metta.Minimal.typeCheckArgsBranchesScoped,
    Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
    Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty,
    actualTypes, Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, Metta.Minimal.scanActualTypeBranches,
    atomMatchesUndefined]

private theorem returnBranches :
    Metta.Minimal.scanExpectedReturnBranches (.sym "%Undefined%")
      (.sym "Atom") [[]] = ⟨some [], []⟩ := by
  simp [Metta.Minimal.scanExpectedReturnBranches, undefinedMatchesAtom]

/-- The retired low-level flag would admit the extra space argument even
though the selected arrow has only one formal argument.  No public selector
passes this flag after the strict-arity repair. -/
theorem legacy_extra_argument_is_selected :
    Metta.Minimal.scanFunctionTypeCandidatesForExpected env
      Metta.Minimal.World.empty runtimeExpression
      [.sym "A", .sym "&self"] (.sym "%Undefined%") true [unaryArrow] =
        .selected selected := by
  simp [Metta.Minimal.scanFunctionTypeCandidatesForExpected,
    argumentBranches, returnBranches, unaryArrow, selected]

/-- With the exemption disabled, the same runtime scanner reports the
published strict-arity error. -/
theorem strict_arity_rejects_extra_argument :
    Metta.Minimal.scanFunctionTypeCandidatesForExpected env
      Metta.Minimal.World.empty runtimeExpression
      [.sym "A", .sym "&self"] (.sym "%Undefined%") false [unaryArrow] =
        .exhausted [.ordinary .incorrectArity] false := by
  rfl

/-- Ordinary public selection is strict for `get-type`. -/
theorem repaired_ordinary_selector_rejects_extra_argument :
    Metta.Minimal.selectFunctionType selectorEnv Metta.Minimal.World.empty
      (.sym "get-type") [.sym "A", .sym "&self"] =
        .exhausted [.incorrectArity] false := by
  simp [Metta.Minimal.selectFunctionType, selectorTypePrep,
    selectorCandidates, Metta.Minimal.scanFunctionTypeCandidates,
    Metta.Minimal.FunctionTypeScanOutcome.prependError, unaryArrow]

/-- Expected-return-aware public selection is strict for the same call. -/
theorem repaired_expected_selector_rejects_extra_argument :
    Metta.Minimal.selectFunctionTypeForExpected selectorEnv
      Metta.Minimal.World.empty (.sym "get-type") [.sym "A", .sym "&self"]
      (.sym "%Undefined%") =
        .exhausted [.ordinary .incorrectArity] false := by
  simp only [Metta.Minimal.selectFunctionTypeForExpected,
    Metta.Minimal.selectFunctionTypeForExpectedAvoiding]
  rw [selectorTypePrep, selectorCandidates]
  change Metta.Minimal.scanFunctionTypeCandidatesForExpected selectorEnv
    Metta.Minimal.World.empty runtimeExpression [.sym "A", .sym "&self"]
      (.sym "%Undefined%") false
      (Metta.Minimal.freshenFunctionTypeCandidatesAvoiding selectorEnv
        runtimeExpression [.sym "A", .sym "&self"] (.sym "%Undefined%") []
        [unaryArrow]) = _
  rw [freshenedSelectorCandidates]
  rfl

/-- The seeded selector used by evaluation is strict as well.  This is the
load-bearing public path: the compatibility selector above is its empty-live-
scope counterpart, not a substitute for it. -/
theorem repaired_seeded_selector_rejects_extra_argument :
    Metta.Minimal.selectFunctionTypeForExpectedFrom selectorEnv
      Metta.Minimal.World.empty (.sym "get-type") [.sym "A", .sym "&self"]
      (.sym "%Undefined%") [] =
        .exhausted [.ordinary .incorrectArity] false := by
  simp only [Metta.Minimal.selectFunctionTypeForExpectedFrom]
  rw [selectorTypePrep, selectorCandidates]
  change Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom selectorEnv
    Metta.Minimal.World.empty runtimeExpression [.sym "A", .sym "&self"]
      (.sym "%Undefined%") false []
      (Metta.Minimal.freshenFunctionTypeCandidatesAvoiding selectorEnv
        runtimeExpression [.sym "A", .sym "&self"] (.sym "%Undefined%") []
        [unaryArrow]) = _
  rw [freshenedSelectorCandidates]
  rfl

private def specExpression : Atom :=
  .expression [.symbol "get-type", .symbol "A", .symbol "&self"]

private def specArrow : Atom :=
  .expression [.symbol "->", .symbol "Atom", .symbol "Atom"]

/-- The executable-independent applicability relation rejects the same call
because two actual arguments cannot inhabit a unary arrow. -/
theorem published_applicability_rejects_extra_argument :
    ApplicabilityRel Space.empty specExpression specArrow Atom.undefinedType
      Bindings.empty
      (.error (mkError specExpression .incorrectNumberOfArguments)) := by
  apply ApplicabilityRel.wrongArity
      (argumentTypes := [.symbol "Atom"])
      (returnType := .symbol "Atom")
  · rfl
  · rfl
  · decide

end Mettapedia.Languages.MeTTa.HE.LeaTTaGetTypeArityCounterexample
