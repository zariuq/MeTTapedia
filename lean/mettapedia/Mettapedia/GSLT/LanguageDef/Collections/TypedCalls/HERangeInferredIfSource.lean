import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredArithmetic
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeConditionalActivation

/-!
# Fresh conditional activation through inferred ports

Selection and operator casting are different read occurrences. Each obtains
its real fresh arrow; the operator cast joins the two private result names.
The actual comparison runs once and both source branches remain held.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredIfSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type
open Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HERangeAdmissionBoundary (environment lookup)
open HERangeSourceProgram (space)
open HEIfSourceSelection (signature)
open HEIfSourceSelection.Range (condition yes no)
open HEFreshEquationFrames.Range (number bodyAt)
open HEIfSourceActivation (operands reachedCall)

theorem selection_from_query (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before after : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom) (name : String)
    (queried : lookup (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world
      (invocationTypeScope scope live (bodyAt (number lower) (number upper)) expected before.bindings)
      space before.bindings (.symbol "if") Atom.undefinedType [(signature name).functionType])
    (renewed : Frame.TypeRenewRel policy expected (.var name) before after) :
    kindArgumentService.selection space
      (lookup (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world)
      policy live scope (bodyAt (number lower) (number upper)) (.symbol "if") expected before
      (.selected (signature name) [after]) := by
  refine ⟨[(signature name).functionType], queried, .selected (errors := []) ?_ (by simp)⟩
  have args := HERangeAdmissionBoundary.conditional_arguments world active primitive unobservedClosure policy before
    (invocationTypeScope scope live (bodyAt (number lower) (number upper)) expected before.bindings)
    lower upper yes (no lower upper)
  simpa [signature, checkedFrames, checkedFailures, HEIfSourceSelection.Range.source_shape, lookup] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
      (expression := bodyAt (number lower) (number upper)) (expected := expected)
      (selected := signature name) (before := before) (operator := .symbol "if")
      (arguments := [condition lower upper, yes, no lower upper]) rfl args
      (List.Forall₂.cons (TypeCheckRel.accepted renewed) List.Forall₂.nil)

theorem arguments (minimal : Minimal.Services)
    (currentOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom) (world : ExternalView)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (lower upper : Int) :
    Stateful.ArgumentsRel (environment minimal currentOps world) space () live scope
      [(Entry.Value.ofAtom (condition lower upper), .symbol "Bool"),
       (Entry.Value.ofAtom yes, Atom.atomType), (Entry.Value.ofAtom (no lower upper), Atom.atomType)] before
      [(Entry.Value.argumentPacket [.grounded (.bool (decide (lower ≥ upper))),
        Entry.Value.ofAtom yes, Entry.Value.ofAtom (no lower upper)], before)] () (policy := policy) := by
  apply HEHeldSourceArguments.conditional
  · exact HEHeldSourceArguments.ground_read policy before yes rfl
  · exact HEHeldSourceArguments.ground_read policy before (no lower upper) rfl
  · simpa only [condition, number, Entry.Value.ofAtom, HEBinaryNumericSource.Operation.call,
      HEBinaryNumericSource.greaterEqual, List.map_cons, List.map_nil] using
      HERangeInferredArithmetic.comparison_source minimal currentOps world policy before
        (argumentScope [(Entry.Value.ofAtom yes, Atom.atomType),
          (Entry.Value.ofAtom (no lower upper), Atom.atomType)] ++ live) scope lower upper

theorem source_activation (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (lower upper : Int)
    (expected : Atom) (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
    ∃ name selected after,
      kindArgumentService.selection space (lookup currentOps world) policy live scope
        (bodyAt (number lower) (number upper)) (.symbol "if") expected before (.selected (signature name) [selected]) ∧
      Stateful.FunctionRel (environment minimal currentOps world) space ()
        (invocationReturnType (signature name) :: live) scope expected (signature name)
        (.symbol "if") (operands lower upper) selected [(reachedCall lower upper, after)] () (policy := policy) := by
  dsimp only
  let currentOps := HERangeTypeReadApplications.ops world active primitive unobservedClosure
  let names := invocationTypeScope scope live (bodyAt (number lower) (number upper)) expected before.bindings
  obtain ⟨name, queried, fresh⟩ := HERangeArgumentQueryTransport.if_read currentOps world names before Atom.undefinedType
  have bindingFresh : name ∉ specBindingVars before.bindings := by
    intro member
    exact fresh (by simp [invocationTypeScope, member])
  let headLive := (signature name).functionType ::
    (operands lower upper).map Entry.Value.erase ++ invocationReturnType (signature name) :: live
  let headScope := scope ++ expectedApplicationScope
    (.expression ((Entry.Value.symbol "if" :: operands lower upper).map Entry.Value.erase)) expected
  have finish (selected after : Frame)
      (selectedRun : kindArgumentService.selection space (lookup currentOps world) policy live scope
        (bodyAt (number lower) (number upper)) (.symbol "if") expected before (.selected (signature name) [selected]))
      (headRun : Stateful.AtomRel (environment minimal currentOps world) space () headLive headScope
        (.symbol "if") (signature name).functionType selected [(.symbol "if", after)] () (policy := policy)) :
      ∃ name selected after,
        kindArgumentService.selection space (lookup currentOps world) policy live scope
          (bodyAt (number lower) (number upper)) (.symbol "if") expected before (.selected (signature name) [selected]) ∧
        Stateful.FunctionRel (environment minimal currentOps world) space ()
          (invocationReturnType (signature name) :: live) scope expected (signature name)
          (.symbol "if") (operands lower upper) selected [(reachedCall lower upper, after)] () (policy := policy) := by
    have args := arguments minimal currentOps world policy after
      ((Entry.Value.symbol "if").erase :: invocationReturnType (signature name) :: live) scope lower upper
    have branches : Stateful.FunctionBranchesRel (environment minimal currentOps world) space ()
        (invocationReturnType (signature name) :: live) scope ((operands lower upper).zip (signature name).argumentTypes)
        [(.symbol "if", after)] [(reachedCall lower upper, after)] () (policy := policy) := by
      simpa [operands, signature, functionAssemble, reachedCall] using
        Stateful.FunctionBranchesRel.continuing (head := (Entry.Value.symbol "if", after))
          (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) args Stateful.FunctionBranchesRel.nil
    exact ⟨name, selected, after, selectedRun, .evaluated rfl headRun branches⟩
  rcases demand with numberDemand | undefinedDemand
  · subst expected
    obtain ⟨selected, bound, renewed, _⟩ := HEFreshRangeFrame.number_range_frame policy before name bindingFresh
    have selectedRun := selection_from_query world active primitive unobservedClosure policy before selected
      live scope lower upper (.symbol "Number") name queried renewed
    have facts := HEFreshRangeAlias.extended_private_facts before.bindings name (.symbol "Number") bindingFresh
    rw [←bound] at facts
    obtain ⟨right, headQuery, headFresh⟩ := HERangeArgumentQueryTransport.if_read currentOps world
      (invocationTypeScope headScope headLive (.symbol "if") (signature name).functionType selected.bindings)
      selected (signature name).functionType
    obtain ⟨after, headRun, _, _⟩ := HEIfOperatorSource.source_of_query
      (environment minimal currentOps world) policy space () headLive headScope selected name right
      headQuery facts.2 facts.1 headFresh
    exact finish selected after selectedRun headRun
  · subst expected
    have renewed : Frame.TypeRenewRel policy Atom.undefinedType (.var name) before before :=
      .unchanged (before.preserved_type_match policy (.undefinedLeft _ _))
    have selectedRun := selection_from_query world active primitive unobservedClosure policy before before
      live scope lower upper Atom.undefinedType name queried renewed
    obtain ⟨right, headQuery, headFresh⟩ := HERangeArgumentQueryTransport.if_read currentOps world
      (invocationTypeScope headScope headLive (.symbol "if") (signature name).functionType before.bindings)
      before (signature name).functionType
    obtain ⟨after, _, headRun⟩ := HERangeConditionalActivation.unconstrained_operator_of_query
      (environment minimal currentOps world) policy space () headLive headScope before name right headQuery bindingFresh headFresh
    exact finish before after selectedRun headRun

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredIfSource
