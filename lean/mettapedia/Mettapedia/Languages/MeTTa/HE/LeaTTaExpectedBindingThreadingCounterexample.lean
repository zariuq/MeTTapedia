import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.Substitution
import MettaHyperonFull.Proofs.TypeInferenceFreshening
import MettaHyperonFull.Proofs.TypeSoundness

/-!
# Expected-return bindings must remain public

The published application relation threads the binding output of function
applicability into function evaluation.  Before repair #19, LeaTTa retained a
successful expected-return match only inside `SelectedFunctionType.typeBindings`.
The selected evaluator then restarted argument evaluation from the incoming
evaluator bindings, making a caller-visible expected-type assignment disappear.

At Hyperon revision `3f76dc46`, the source witness represented below evaluates
to `[B]`; pre-repair LeaTTa returned `[$t]`.  The retained empty-seed executor
theorem isolates that obsolete failure mode.  The repaired seed canaries prove
that the public assignment is retained, a ground expectation remains neutral,
and a private freshening name cannot leak into the seed.  The presentation
theorems show why the return-gate assignment cannot honestly be classified as
private.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement
open Metta
open Metta.Minimal

private theorem visibleScope_eq :
    expectedApplicationVisibleScope
      (.expr [.sym "f", .var "t"]) (.var "t") = ["t"] := by
  unfold expectedApplicationVisibleScope
  simp only [Metta.Atom.vars, List.map, List.flatten, List.append]
  change ["t", "t"].eraseDups = ["t"]
  rw [List.eraseDups_cons]
  simp

private theorem resolve_public :
    resolveAtom ([.val "t" (.sym "B")] : Metta.Bindings) 2 (.var "t") =
      .sym "B" := by
  have hinst :
      instantiate ([.val "t" (.sym "B")] : Metta.Bindings) (.var "t") =
        .sym "B" :=
    instantiate_singleton_val_var_of_not_mem "t" (.sym "B") (by
      simp [Metta.Atom.vars])
  have hfixed :
      instantiate ([.val "t" (.sym "B")] : Metta.Bindings) (.sym "B") =
        .sym "B" :=
    instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
  have hneq : ((.sym "B" : Metta.Atom) == .var "t") = false := by rfl
  have hself : ((.sym "B" : Metta.Atom) == .sym "B") = true := by rfl
  simp [resolveAtom, hinst, hfixed, hneq, hself]

private theorem restrict_public :
    restrictBnd ["t"] ([.val "t" (.sym "B")] : Metta.Bindings) =
      [.val "t" (.sym "B")] := by
  simp [restrictBnd, restrictBndRaw, resolve_public,
    Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
    Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
    Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal]

private theorem merge_public :
    Metta.Bindings.merge [] ([.val "t" (.sym "B")] : Metta.Bindings) =
      [[.val "t" (.sym "B")]] := by
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
    Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
    Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal]

private def selectedWithPublicBinding : SelectedFunctionType :=
  { functionType := .expr [.sym "->", .sym "Atom", .sym "B"]
    argumentTypes := [.sym "Atom"]
    returnType := .sym "B"
    typeBindings := [.val "t" (.sym "B")] }

private def selectedWithPrivateBinding : SelectedFunctionType :=
  { functionType := .expr [.sym "->", .sym "Atom", .sym "B"]
    argumentTypes := [.sym "Atom"]
    returnType := .sym "B"
    typeBindings :=
      [.val "private#19" (.sym "A"), .val "t" (.sym "B")] }

private theorem resolve_public_with_private :
    resolveAtom selectedWithPrivateBinding.typeBindings 3 (.var "t") =
      .sym "B" := by
  have hclosed :
      Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.ClosedValueBindings
        selectedWithPrivateBinding.typeBindings := by
    exact .val (by simp [Metta.Atom.vars])
      (.val (by simp [Metta.Atom.vars]) .nil)
  have hresolve :
      Metta.Bindings.resolve selectedWithPrivateBinding.typeBindings "t" =
        some (.sym "B") := by
    rw [Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.ClosedValueBindings.resolve_eq_lookupVal
      hclosed]
    rfl
  have hinst :
      instantiate selectedWithPrivateBinding.typeBindings (.var "t") =
        .sym "B" := by
    simp [instantiate, Metta.Bindings.resolveAtom, hresolve]
  have hfixed :
      instantiate selectedWithPrivateBinding.typeBindings (.sym "B") =
        .sym "B" :=
    instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
  have hneq : ((.sym "B" : Metta.Atom) == .var "t") = false := by rfl
  have hself : ((.sym "B" : Metta.Atom) == .sym "B") = true := by rfl
  simp [resolveAtom, hinst, hfixed, hneq, hself]

private theorem restrict_public_with_private :
    restrictBnd ["t"] selectedWithPrivateBinding.typeBindings =
      [.val "t" (.sym "B")] := by
  change
    restrictBnd ["t"]
      ([.val "private#19" (.sym "A"), .val "t" (.sym "B")] :
        Metta.Bindings) = [.val "t" (.sym "B")]
  have hresolve :
      resolveAtom
          ([.val "private#19" (.sym "A"), .val "t" (.sym "B")] :
            Metta.Bindings)
          3 (.var "t") = .sym "B" := by
    simpa [selectedWithPrivateBinding] using resolve_public_with_private
  simp [restrictBnd, restrictBndRaw, hresolve,
    Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
    Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
    Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal]

private def echoExpected
    (st : St) (bindings : Metta.Bindings) (atom : Metta.Atom)
    (_expected : Metta.Atom) :
    List (Metta.Atom × Metta.Bindings) × St :=
  ([(atom, bindings)], st)

private def emitUnresolvedT
    (st : St) (_application : Metta.Atom) :
    List (Metta.Atom × Metta.Bindings) × St :=
  ([(.var "t", [])], st)

/-- Structural pre-repair canary: even when the selected policy already
contains the public assignment `t = B`, the application executor initializes
its partial binding at `[]`.  A quoted `$t` therefore reaches both the rule
reducer and the expected-result continuation unresolved.  The whole-program
regression beside this theorem pins the same behavior at the public CLI. -/
theorem selected_public_binding_is_not_seeded_into_evaluation :
    evaluateExpectedApplication echoExpected emitUnresolvedT St.init "f"
      [.var "t"] selectedWithPublicBinding =
      ([(.var "t", [])], St.init) := by
  have instantiateAtom :
      instantiate ([.val "t" (.sym "B")] : Metta.Bindings) (.sym "Atom") =
        .sym "Atom" :=
    instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
  have instantiateB :
      instantiate ([.val "t" (.sym "B")] : Metta.Bindings) (.sym "B") =
        .sym "B" :=
    instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
  have atomNotItself :
      ((.sym "Atom" : Metta.Atom) != .sym "Atom") = false := by
    rfl
  have bNotAtom : ((.sym "B" : Metta.Atom) == .sym "Atom") = false := by
    rfl
  have policies : argumentEvaluationPolicies selectedWithPublicBinding 1 =
      [(false, .sym "Atom")] := by
    simp [argumentEvaluationPolicies, selectedWithPublicBinding,
      instantiateAtom, atomNotItself]
  have returnsNotAtom : returnsAtom selectedWithPublicBinding = false := by
    simp [returnsAtom, selectedWithPublicBinding, instantiateB, bNotAtom]
  have variableNotSelf : ((.var "t" : Metta.Atom) != .var "t") = false := by
    rfl
  have variableNotError : (.var "t" : Metta.Atom).isError = false := by
    rfl
  have variableNotNotReducible :
      ((.var "t" : Metta.Atom) == notReducibleA) = false := by
    rfl
  have variableNotApplication :
      ((.var "t" : Metta.Atom) == .expr [.sym "f", .var "t"]) = false := by
    rfl
  have emptyMerge : Metta.Bindings.merge [] [] = [[]] := by
    rfl
  have variableVars : (.var "t" : Metta.Atom).vars = ["t"] := by
    simp [Metta.Atom.vars]
  have emptyRestriction : restrictBnd ["t"] [] = [] := by
    have resolveEmpty :
        resolveAtom ([] : Metta.Bindings) 1 (.var "t") = .var "t" := by
      simp [resolveAtom, instantiate_nil]
    simp [restrictBnd, restrictBndRaw, resolveEmpty, Metta.Bindings.merge]
  have emptyRetention :
      restrictBnd
          (expectedApplicationRetentionScope [] [(.var "t" : Metta.Atom)])
          [] = [] := by
    simpa [expectedApplicationRetentionScope, variableVars] using
      emptyRestriction
  simp [evaluateExpectedApplication, evaluateExpectedApplicationFrom,
    policies, returnsNotAtom,
    echoExpected, emitUnresolvedT, instantiate_nil, variableNotSelf,
    variableNotError, variableNotNotReducible, variableNotApplication,
    emptyRetention]

/-- POSITIVE repair canary: the expected-return assignment visible in the
post-instantiation expression/expected scope becomes the initial application
binding. -/
theorem selected_public_binding_is_seeded_into_expected_application :
    selectedApplicationInitialBindings []
      (.expr [.sym "f", .var "t"]) (.var "t")
      selectedWithPublicBinding = [[.val "t" (.sym "B")]] := by
  rw [selectedApplicationInitialBindings, selectedApplicationVisibleBindings,
    visibleScope_eq]
  change
    Metta.Bindings.merge []
      (restrictBnd ["t"] ([.val "t" (.sym "B")] : Metta.Bindings)) =
        [[.val "t" (.sym "B")]]
  rw [restrict_public, merge_public]

/-- NEGATIVE repair canary: a selected type-freshening name outside the public
scope cannot appear in the bindings that seed expected application evaluation. -/
theorem selected_private_binding_does_not_leak_into_expected_application :
    .val "private#19" (.sym "A") ∉
      (selectedApplicationInitialBindings []
        (.expr [.sym "f", .var "t"]) (.var "t")
        selectedWithPrivateBinding).flatten := by
  rw [selectedApplicationInitialBindings, selectedApplicationVisibleBindings,
    visibleScope_eq, restrict_public_with_private, merge_public]
  simp

private def selectedWithPublicPrivateAlias : SelectedFunctionType :=
  { functionType := .expr [.sym "->", .var "####u#0"]
    argumentTypes := []
    returnType := .var "####u#0"
    typeBindings := [.eq "t" "####u#0"] }

private def liveCollisionRawArrow : Metta.Atom :=
  .expr [.sym "->", .var "u"]

private def liveCollisionEnv : MinEnv :=
  MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "f", liveCollisionRawArrow]] []

private theorem liveCollisionFunctionTypes :
    getTypes liveCollisionEnv
        (typePrep World.empty (.sym "f")) =
      [liveCollisionRawArrow] := by
  have prepared : typePrep World.empty (.sym "f") = .sym "f" := by
    simp [typePrep, subTokens.eq_1, wrapStates.eq_3, World.empty]
  rw [prepared]
  rw [getTypes.eq_8]
  simp [liveCollisionEnv, liveCollisionRawArrow, MinEnv.ofAtomsGT,
    Std.HashMap.getD_emptyWithCapacity]

private theorem liveCollisionFreshening :
    freshenFunctionTypeCandidates liveCollisionEnv
      (.expr [.sym "f"]) [] (.var "t") [liveCollisionRawArrow] =
      [.expr [.sym "->", .var "####u#0"]] := by
  simp [freshenFunctionTypeCandidates, freshenFunctionTypeCandidatesAvoiding,
    functionTypeSelectionAvoiding, functionTypeSelectionAvoid,
    applicationTypeInferenceScope, typeInferenceAvoid,
    freshenTypeCandidate, captureAvoidingName, avoidancePrefix,
    renameAllVars, liveCollisionEnv, liveCollisionRawArrow,
    MinEnv.ofAtomsGT, Metta.Atom.vars]
  decide

/-- The legacy selector can choose a private signature spelling already live
in the caller bindings because those bindings are absent from its avoid set. -/
theorem selected_signature_can_collide_with_live_binding :
    selectFunctionTypeForExpected liveCollisionEnv World.empty
      (.sym "f") [] (.var "t") =
        .selected selectedWithPublicPrivateAlias ∧
      "####u#0" ∈
        Metta.Bindings.vars
          ([(.val "####u#0" (.sym "B") : BindingRel)] : Metta.Bindings) := by
  constructor
  · simpa [selectedWithPublicPrivateAlias] using
      (Metta.selectFunctionTypeForExpected_singleton_fresh_arrow_selected
        liveCollisionEnv World.empty "f" [] [] liveCollisionRawArrow
        (.var "####u#0") (.var "t")
        ([.eq "t" "####u#0"] : Metta.Bindings)
        ([[]] : List Metta.Bindings) [] []
        liveCollisionFunctionTypes liveCollisionFreshening rfl rfl rfl)
  · simp [Bindings.vars, Metta.Atom.vars]

/-- Repair canary: the evaluator-facing freshener cannot reuse any spelling
already present in the live binding scope. -/
theorem live_aware_signature_cannot_repeat_live_binding :
    ∀ candidate ∈
        freshenFunctionTypeCandidatesAvoiding liveCollisionEnv
          (.expr [.sym "f"]) [] (.var "t") ["####u#0"]
          [liveCollisionRawArrow],
      ∀ name ∈ candidate.vars, name ≠ "####u#0" := by
  intro candidate candidateMember name nameMember nameEq
  have avoidsLive :=
    freshenFunctionTypeCandidatesAvoiding_vars_avoid_live liveCollisionEnv
      (.expr [.sym "f"]) [] (.var "t") ["####u#0"]
      [liveCollisionRawArrow] candidate candidateMember name nameMember
  exact avoidsLive (by simp [nameEq])

private theorem resolve_public_private_alias :
    resolveAtom ([.eq "t" "####u#0"] : Metta.Bindings) 2 (.var "t") =
      .var "####u#0" := by
  let bindings : Metta.Bindings := [.eq "t" "####u#0"]
  have namesDiffer : "t" ≠ "####u#0" := by decide
  have privateDiffers : "####u#0" ≠ "t" := by decide
  have order : Metta.Bindings.eqVarsInOrder bindings =
      ["####u#0", "t"] := by
    simp [bindings, Metta.Bindings.eqVarsInOrder, namesDiffer]
  have tClass : Metta.Bindings.eqClass bindings "t" =
      ["t", "####u#0"] := by
    simp [bindings, Metta.Bindings.eqClass, Metta.Bindings.eqClassAux,
      Metta.Bindings.eqStep, namesDiffer, privateDiffers]
  have privateClass : Metta.Bindings.eqClass bindings "####u#0" =
      ["####u#0", "t"] := by
    simp [bindings, Metta.Bindings.eqClass, Metta.Bindings.eqClassAux,
      Metta.Bindings.eqStep, namesDiffer, privateDiffers]
  have tOrdered : Metta.Bindings.eqClassOrdered bindings "t" =
      ["####u#0", "t"] := by
    simp [Metta.Bindings.eqClassOrdered, order, tClass]
  have privateOrdered :
      Metta.Bindings.eqClassOrdered bindings "####u#0" =
        ["####u#0", "t"] := by
    simp [Metta.Bindings.eqClassOrdered, order, privateClass]
  have tValues : Metta.Bindings.classValues bindings "t" = [] := by
    simp [Metta.Bindings.classValues, bindings,
      Metta.Bindings.lookupVal]
  have privateValues :
      Metta.Bindings.classValues bindings "####u#0" = [] := by
    simp [Metta.Bindings.classValues, bindings,
      Metta.Bindings.lookupVal]
  have tFuel :
      Metta.Bindings.resolutionFuel bindings (.var "t") = 3 := by
    simp [bindings, Metta.Bindings.resolutionFuel,
      Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
  have privateFuel :
      Metta.Bindings.resolutionFuel bindings (.var "####u#0") = 3 := by
    simp [bindings, Metta.Bindings.resolutionFuel,
      Metta.Bindings.relationResolutionFuel, Metta.Atom.size]
  have tAux : Metta.Bindings.resolveAtomAux bindings 3 [] (.var "t") =
      some (.var "####u#0") := by
    simp [Metta.Bindings.resolveAtomAux, tOrdered, tValues,
      Metta.Bindings.eqRepresentative]
  have privateAux :
      Metta.Bindings.resolveAtomAux bindings 3 [] (.var "####u#0") =
        some (.var "####u#0") := by
    simp [Metta.Bindings.resolveAtomAux, privateOrdered, privateValues,
      Metta.Bindings.eqRepresentative]
  have tResolve : Metta.instantiate bindings (.var "t") =
      .var "####u#0" := by
    simp [Metta.instantiate, Metta.Bindings.resolveAtom,
      Metta.Bindings.resolve, tOrdered, tValues, tFuel, tAux]
  have privateResolve : Metta.instantiate bindings (.var "####u#0") =
      .var "####u#0" := by
    simp [Metta.instantiate, Metta.Bindings.resolveAtom,
      Metta.Bindings.resolve, privateOrdered, privateValues,
      privateFuel, privateAux]
  have firstChanges :
      ((.var "####u#0" : Metta.Atom) == .var "t") = false := by rfl
  have thenStable :
      ((.var "####u#0" : Metta.Atom) == .var "####u#0") = true := by rfl
  change resolveAtom bindings 2 (.var "t") = .var "####u#0"
  simp [resolveAtom, tResolve, privateResolve, firstChanges, thenStable]

/-- A private signature variable linked to an observed expected variable is
not an unrelated private assignment: the projection must retain the link so a
later return cast can refine the public variable.  Consequently the selector's
freshening avoid must include live incoming binding names; otherwise this
necessary bridge can collide with an older private name.  The projected link
is an equality relation, preserving the runtime's normalized representation. -/
theorem selected_public_private_alias_is_retained :
    selectedApplicationVisibleBindings
      (.expr [.sym "f", .var "t"]) (.var "t")
      selectedWithPublicPrivateAlias =
        [.eq "t" "####u#0"] := by
  rw [selectedApplicationVisibleBindings, visibleScope_eq]
  change restrictBnd ["t"]
      ([.eq "t" "####u#0"] : Metta.Bindings) =
    [.eq "t" "####u#0"]
  simp [restrictBnd, restrictBndRaw, resolve_public_private_alias,
    Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarEquality, Metta.Bindings.addEqRaw,
    Metta.Bindings.unifyValues, Metta.Bindings.classValues,
    Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
    Metta.Bindings.eqClass, Metta.Bindings.eqClassAux,
    Metta.Bindings.eqStep, Metta.Bindings.lookupVal]

/-- Ground expectations and closed applications expose no caller variable, so
the repaired projection leaves the empty incoming binding unchanged. -/
theorem ground_expected_application_seed_is_neutral :
    selectedApplicationInitialBindings []
      (.expr [.sym "f", .sym "a"]) (.sym "B")
      selectedWithPrivateBinding = [[]] := by
  have hscope :
      expectedApplicationVisibleScope
        (.expr [.sym "f", .sym "a"]) (.sym "B") = [] := by
    simp [expectedApplicationVisibleScope, Metta.Atom.vars]
  rw [selectedApplicationInitialBindings, selectedApplicationVisibleBindings,
    hscope]
  change
    Metta.Bindings.merge []
      (restrictBnd []
        ([.val "private#19" (.sym "A"), .val "t" (.sym "B")] :
          Metta.Bindings)) = [[]]
  have hrestrict :
      restrictBnd []
        ([.val "private#19" (.sym "A"), .val "t" (.sym "B")] :
          Metta.Bindings) = [] := by
    unfold restrictBnd
    rfl
  rw [hrestrict]
  rfl

/-- The independent return-gate presentation records the public equation
`t = B`; it is not an observationally inert private assignment. -/
theorem expected_return_gate_binds_public_variable :
    CorePlusR2TypePresentationMatchRel [] (.var "t") (.symbol "B")
      [("t", .symbol "B")] := by
  apply CorePlusR2TypePresentationMatchRel.reduced
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType]
  · simp [Mettapedia.Languages.MeTTa.OSLFCore.Atom.atomType]
  apply ReducedTypePresentationMatchRel.ordinary
      (resolvedLeft := .var "t") (resolvedRight := .symbol "B")
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [ReducedTypeLeafShape]
  · exact TypeSubst.apply_empty (.var "t")
  · exact TypeSubst.apply_empty (.symbol "B")
  simpa [TypeSubst.bind, TypeSubst.apply, TypeSubst.erase,
    TypeSubst.lookup] using
    (AppliedReducedTypeMatchRel.bindLeft
      (substitution := []) (name := "t") (right := .symbol "B")
      (by simp [TypeSubst.typeVars]))

/-- No private-presentation witness can hide `t = B` at a scope that observes
`t`: the carrier's freshness law excludes the presentation key itself. -/
theorem expected_binding_cannot_be_private
    (output : Mettapedia.Languages.MeTTa.HE.Bindings) :
    ¬PrivatePresentationExtensionRel ["t"]
      Mettapedia.Languages.MeTTa.HE.Bindings.empty
      [("t", .symbol "B")] output := by
  intro extension
  exact extension.scopeFresh "t" (by simp)
    (by simp [TypeSubst.keys])

/-- POSITIVE carrier canary: the public equation `t = B` is a lawful semantic
extension even though it is not private at a scope observing `t`. -/
theorem expected_binding_is_presentation_extension :
    PresentationExtensionRel
      Mettapedia.Languages.MeTTa.HE.Bindings.empty
      [("t", .symbol "B")]
      ⟨[("t", .symbol "B")], []⟩ := by
  simpa [Mettapedia.Languages.MeTTa.HE.Bindings.empty] using
    (presentationExtension_append
      Mettapedia.Languages.MeTTa.HE.Bindings.empty
      [("t", .symbol "B")])

/-- NEGATIVE carrier canary: dropping the public presentation is not a
solution-theory extension of the empty incoming record. -/
theorem expected_binding_cannot_be_dropped :
    ¬PresentationExtensionRel
      Mettapedia.Languages.MeTTa.HE.Bindings.empty
      [("t", .symbol "B")]
      Mettapedia.Languages.MeTTa.HE.Bindings.empty := by
  intro extension
  let valuation : String → Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
    fun name => .var name
  have emptySatisfied : TypeBindingSatisfied valuation
      Mettapedia.Languages.MeTTa.HE.Bindings.empty := by
    constructor
    · intro _ _ member
      cases member
    · intro _ _ member
      cases member
  have presentationSatisfied :
      TypeSubstSatisfied valuation [("t", .symbol "B")] :=
    ((extension valuation).mp emptySatisfied).2
  have forced := presentationSatisfied "t" (.symbol "B") (by simp)
  simp [valuation] at forced

/-- NEGATIVE scope canary: projection forgets a binding whose variable is
not retained.  Consequently no evaluator observation theorem may quantify
over an arbitrary public scope; it must prove that every observed name lies
in the executable retention scope. -/
theorem restrictBnd_drops_unretained_binding :
    restrictBnd ["x"]
      ([.val "x" (.sym "A"), .val "y" (.sym "B")] : Metta.Bindings) =
        [.val "x" (.sym "A")] := by
  let bindings : Metta.Bindings :=
    [.val "x" (.sym "A"), .val "y" (.sym "B")]
  have closed :
      Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.ClosedValueBindings
        bindings := by
    exact .val (by simp [Metta.Atom.vars])
      (.val (by simp [Metta.Atom.vars]) .nil)
  have lookup : Metta.Bindings.resolve bindings "x" = some (.sym "A") := by
    rw [Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.ClosedValueBindings.resolve_eq_lookupVal
      closed]
    rfl
  have instantiated : instantiate bindings (.var "x") = .sym "A" := by
    simp [instantiate, Metta.Bindings.resolveAtom, lookup]
  have fixed : instantiate bindings (.sym "A") = .sym "A" :=
    instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
  have differs : ((.sym "A" : Metta.Atom) == .var "x") = false := by
    rfl
  have stable : ((.sym "A" : Metta.Atom) == .sym "A") = true := by
    rfl
  have resolved : resolveAtom bindings 3 (.var "x") = .sym "A" := by
    simp [resolveAtom, instantiated, fixed, differs, stable]
  change restrictBnd ["x"] bindings = [.val "x" (.sym "A")]
  simp [bindings, restrictBnd, restrictBndRaw, resolved,
    Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
    Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
    Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal]

end Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample
