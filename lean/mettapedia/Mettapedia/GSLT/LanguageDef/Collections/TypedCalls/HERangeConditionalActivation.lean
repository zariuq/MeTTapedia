import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProgram

/-!
# Undefined-demanded conditional selection in recursive range

Superpose emits its recursive child under Undefined. The standard-if range
variable therefore remains unvalued at selection; a second fresh operator
instance merely joins its class. No Number premise is inserted here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeConditionalActivation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation
open HEIfSourceSelection (signature)

/-- A singleton actual type query and its source match earn the operator
cast and reached contextual frame; no operator run is assumed. -/
theorem operator_cast {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (name : String) (expected actual : Atom) (output : Bindings)
    (notEmpty : name ≠ "Empty") (notAtom : expected ≠ Atom.atomType) (notSymbol : expected ≠ Atom.symbolType)
    (queried : environment.lookup (invocationTypeScope scope live (.symbol name) expected before.bindings)
      (environment.view world label) before.bindings (.symbol name) expected [actual])
    (matched : policy.matching.Rel expected actual before.bindings output)
    (model : ∃ valuation, TypeBindingSatisfied valuation output) :
    ∃ after : Frame, after.bindings = output ∧
      Stateful.AtomRel environment label world live scope (.symbol name) expected before
        [(.symbol name, after)] world (policy := policy) := by
  obtain ⟨after, bound, renewed⟩ := Frame.CastRenewRel.of_modelled_source_match
    (policy := policy) before (earlier := []) (later := []) queried rfl (by simp) matched model
  have readSymbol : before.read policy (.symbol name) = .symbol name := by simp [Frame.read, Entry.Value.substitute]
  refine ⟨after, bound, ?_⟩
  apply Stateful.AtomRel.cast (raw := [(.symbol name, after.bindings)])
  · rw [readSymbol]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol name
    · rintro (asAtom | asSymbol | impossible)
      · exact notAtom asAtom
      · exact notSymbol asSymbol
      · exact (by decide : Atom.symbolType ≠ Atom.variableType) impossible
    · exact Or.inl ⟨name, by simp [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [readSymbol]
    simp only [Entry.Value.erase]
    apply TypeCastBatchRel.success (earlierTypes := []) (laterTypes := []) queried rfl (by simp)
    rw [bound]
    exact matched
  · rw [readSymbol]
    exact .cons ⟨by simp [Completed.rawResult, Entry.Value.erase],
      by simpa only [Entry.Value.erase] using renewed, by simp [Entry.Value.erase]⟩ .nil

theorem undefined_selection (space : Space) (policy : Policy) (before : Frame) (live : List Atom)
    (scope : List String) (condition yes no : Atom) (name : String)
    (declared : getAtomTypes space (.symbol "if") = [(signature "t").functionType])
    (conditionUnknown : getAtomTypes space condition = [Atom.undefinedType])
    (yesUnknown : getAtomTypes space yes = [Atom.undefinedType])
    (noUnknown : getAtomTypes space no = [Atom.undefinedType])
    (fresh : name ∉ invocationTypeScope
      (invocationTypeScope scope live (HEIfSourceSelection.call condition yes no) Atom.undefinedType before.bindings)
      [] (.symbol "if") Atom.undefinedType before.bindings) :
    InvocationSelectionRel space scopedLookup policy live scope (HEIfSourceSelection.call condition yes no)
      (.symbol "if") Atom.undefinedType before (.selected (signature name) [before]) := by
  let names := invocationTypeScope scope live (HEIfSourceSelection.call condition yes no) Atom.undefinedType before.bindings
  have first := HEIfSourceSelection.unknown_argument space names policy before (HEIfSourceSelection.call condition yes no)
    condition (.symbol "Bool") 1 conditionUnknown
  have second := HEIfSourceSelection.unknown_argument space names policy before (HEIfSourceSelection.call condition yes no)
    yes Atom.atomType 2 yesUnknown
  have third := HEIfSourceSelection.unknown_argument space names policy before (HEIfSourceSelection.call condition yes no)
    no Atom.atomType 3 noUnknown
  have checked : ApplicationChecksRel space (scopedLookup names space) policy
      (HEIfSourceSelection.call condition yes no) Atom.undefinedType (signature name) before [before] [] := by
    simpa [signature, checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (expression := HEIfSourceSelection.call condition yes no) (expected := Atom.undefinedType)
        (selected := signature name) (before := before)
        (operator := .symbol "if") (arguments := [condition, yes, no]) rfl
        (.cons first (.cons second (.cons third .nil)))
        (.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy (.undefinedLeft _ _)))) .nil))
  exact ⟨[(signature name).functionType], HEIfSourceSelection.signature_lookup space names before _ name declared fresh,
    .selected checked (by simp)⟩

theorem unconstrained_operator_of_query {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (left right : String)
    (queried : environment.lookup
      (invocationTypeScope scope live (.symbol "if") (signature left).functionType before.bindings)
      (environment.view world label) before.bindings (.symbol "if") (signature left).functionType [(signature right).functionType])
    (leftFresh : left ∉ specBindingVars before.bindings)
    (rightFresh : right ∉ HEIfOperatorSource.castScope scope live before left) :
    ∃ after : Frame, after.bindings = before.bindings.addEquality left right ∧
      Stateful.AtomRel environment label world live scope (.symbol "if") (signature left).functionType before
        [(.symbol "if", after)] world (policy := policy) := by
  have fresh : right ∉ specBindingVars before.bindings := by
    intro member
    exact rightFresh (by simp [HEIfOperatorSource.castScope, invocationTypeScope, member])
  have different : left ≠ right := by
    intro same
    subst right
    exact rightFresh (by
      simp [HEIfOperatorSource.castScope, invocationTypeScope, signature, CompletedDelivery.arrowType,
        TypeSubst.typeVars, TypeSubst.typeVarsList, Atom.atomType])
  obtain ⟨matched, model⟩ := HEUnconstrainedRangeAlias.arrow_policy_match before policy
    ["->", "Bool", "Atom", "Atom"] left right leftFresh fresh different
  have matching : policy.matching.Rel (signature left).functionType (signature right).functionType before.bindings
      (before.bindings.addEquality left right) := by
    simpa [signature, CompletedDelivery.arrowType, HEFreshRangeAlias.arrowWith, Atom.atomType] using matched
  apply operator_cast environment policy label world live scope before "if" (signature left).functionType
    (signature right).functionType (before.bindings.addEquality left right) (by decide)
    (by simp [signature, CompletedDelivery.arrowType, Atom.atomType])
    (by simp [signature, CompletedDelivery.arrowType, Atom.symbolType])
  · exact queried
  · exact matching
  · exact model

theorem unconstrained_operator {Context World : Type} (environment : WorldEnvironment Context World)
    (lookup : environment.lookup = scopedLookup) (policy : Policy)
    (label : Context) (world : World) (live : List Atom) (scope : List String)
    (before : Frame) (left right : String)
    (declared : getAtomTypes (environment.view world label) (.symbol "if") = [(signature "t").functionType])
    (leftFresh : left ∉ specBindingVars before.bindings)
    (rightFresh : right ∉ HEIfOperatorSource.castScope scope live before left) :
    ∃ after : Frame, after.bindings = before.bindings.addEquality left right ∧
      Stateful.AtomRel environment label world live scope (.symbol "if") (signature left).functionType before
        [(.symbol "if", after)] world (policy := policy) := by
  apply unconstrained_operator_of_query environment policy label world live scope before left right
  · rw [lookup]
    exact HEIfSourceSelection.signature_lookup _ _ before _ right declared rightFresh
  · exact leftFresh
  · exact rightFresh

open HERangeSourceProgram (space environment)
open HEIfSourceSelection.Range (condition yes no)
open HEFreshEquationFrames.Range (number bodyAt)
open HEIfSourceActivation (operands reachedCall)

theorem arguments (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) :
    Stateful.ArgumentsRel (environment minimal) space () live scope
      [(Entry.Value.ofAtom (condition lower upper), .symbol "Bool"),
       (Entry.Value.ofAtom yes, Atom.atomType), (Entry.Value.ofAtom (no lower upper), Atom.atomType)] before
      [(Entry.Value.argumentPacket [.grounded (.bool (decide (lower ≥ upper))),
        Entry.Value.ofAtom yes, Entry.Value.ofAtom (no lower upper)], before)] () (policy := policy) := by
  apply HEHeldSourceArguments.conditional
  · exact HEHeldSourceArguments.ground_read policy before yes (by rfl)
  · exact HEHeldSourceArguments.ground_read policy before (no lower upper) (by rfl)
  · simpa only [condition, number, Entry.Value.ofAtom, HEBinaryNumericSource.Operation.call,
      HEBinaryNumericSource.greaterEqual, List.map_cons, List.map_nil] using
      HERangeSourceProgram.compare_source minimal policy before
        (argumentScope [(Entry.Value.ofAtom yes, Atom.atomType),
          (Entry.Value.ofAtom (no lower upper), Atom.atomType)] ++ live) scope lower upper

/-- Both demanded entry profiles are earned from their actual source type
queries. Recursive Undefined entries do not inherit a fabricated Number row. -/
theorem source_activation (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ name selected after,
      InvocationSelectionRel space scopedLookup policy live scope (bodyAt (number lower) (number upper))
        (.symbol "if") expected before (.selected (signature name) [selected]) ∧
      Stateful.FunctionRel (environment minimal) space ()
        (invocationReturnType (signature name) :: live) scope expected (signature name)
        (.symbol "if") (operands lower upper) selected [(reachedCall lower upper, after)] () (policy := policy) := by
  let avoid := invocationTypeScope
    (invocationTypeScope scope live (HEIfSourceSelection.call (condition lower upper) yes (no lower upper)) expected before.bindings)
    [] (.symbol "if") expected before.bindings
  let name := instanceName avoid ["t"] 0 "t"
  have fresh : name ∉ avoid := instanceName_not_mem avoid ["t"] 0 "t"
  have bindingFresh : name ∉ specBindingVars before.bindings := by
    intro member
    exact fresh (by simp [avoid, invocationTypeScope, member])
  have conditionUnknown : getAtomTypes space (condition lower upper) = [Atom.undefinedType] := rfl
  have yesUnknown : getAtomTypes space yes = [Atom.undefinedType] := rfl
  have noUnknown : getAtomTypes space (no lower upper) = [Atom.undefinedType] := rfl
  let headLive := (signature name).functionType ::
    (operands lower upper).map Entry.Value.erase ++ invocationReturnType (signature name) :: live
  let headScope := scope ++ expectedApplicationScope
    (.expression ((Entry.Value.symbol "if" :: operands lower upper).map Entry.Value.erase)) expected
  have finish (selected after : Frame)
      (selectedRun : InvocationSelectionRel space scopedLookup policy live scope (bodyAt (number lower) (number upper))
        (.symbol "if") expected before (.selected (signature name) [selected]))
      (headRun : Stateful.AtomRel (environment minimal) space () headLive headScope
        (.symbol "if") (signature name).functionType selected [(.symbol "if", after)] () (policy := policy)) :
      ∃ name selected after,
        InvocationSelectionRel space scopedLookup policy live scope (bodyAt (number lower) (number upper))
          (.symbol "if") expected before (.selected (signature name) [selected]) ∧
        Stateful.FunctionRel (environment minimal) space ()
          (invocationReturnType (signature name) :: live) scope expected (signature name)
          (.symbol "if") (operands lower upper) selected [(reachedCall lower upper, after)] () (policy := policy) := by
    have args := arguments minimal policy after
      ((Entry.Value.symbol "if").erase :: invocationReturnType (signature name) :: live) scope lower upper
    have branches : Stateful.FunctionBranchesRel (environment minimal) space ()
        (invocationReturnType (signature name) :: live) scope ((operands lower upper).zip (signature name).argumentTypes)
        [(.symbol "if", after)] [(reachedCall lower upper, after)] () (policy := policy) := by
      simpa [operands, signature, functionAssemble, reachedCall] using
        (Stateful.FunctionBranchesRel.continuing (head := (Entry.Value.symbol "if", after))
          (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) args Stateful.FunctionBranchesRel.nil)
    exact ⟨name, selected, after, selectedRun, .evaluated rfl headRun branches⟩
  rcases demand with numberDemand | undefinedDemand
  · subst expected
    obtain ⟨selected, selectedRun, bound, _⟩ := HEIfSourceSelection.selection space policy before live scope
      (condition lower upper) yes (no lower upper) name HERangeSourceProgram.if_declared
      conditionUnknown yesUnknown noUnknown fresh
    have facts := HEFreshRangeAlias.extended_private_facts before.bindings name (.symbol "Number") bindingFresh
    rw [← bound] at facts
    let headAvoid := HEIfOperatorSource.castScope headScope headLive selected name
    let right := instanceName headAvoid ["t"] 0 "t"
    obtain ⟨after, headRun, _, _⟩ := HEIfOperatorSource.source (environment minimal) rfl policy space () headLive headScope
      selected name right HERangeSourceProgram.if_declared facts.2 facts.1
      (instanceName_not_mem headAvoid ["t"] 0 "t")
    exact finish selected after selectedRun headRun
  · subst expected
    have selectedRun := undefined_selection space policy before live scope (condition lower upper) yes (no lower upper)
      name HERangeSourceProgram.if_declared conditionUnknown yesUnknown noUnknown fresh
    let headAvoid := HEIfOperatorSource.castScope headScope headLive before name
    let right := instanceName headAvoid ["t"] 0 "t"
    obtain ⟨after, _, headRun⟩ := unconstrained_operator (environment minimal) rfl policy space () headLive headScope
      before name right HERangeSourceProgram.if_declared bindingFresh
      (instanceName_not_mem headAvoid ["t"] 0 "t")
    exact finish before after selectedRun headRun

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeConditionalActivation
