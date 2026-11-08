import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionArithmetic
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredIfSource

/-! The range conditional's actual inferred selection and argument delivery
in the collection world. Its two operator queries earn separate fresh result
variables; the comparison runs once and the branches remain held syntax. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionIfActivation

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HEIfSourceSelection (signature)
open HEIfSourceSelection.Range (condition yes no)
open HEFreshEquationFrames.Range (number bodyAt)
open HEIfSourceActivation (operands reachedCall)

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem comparison_admission (policy : Policy) (before : Frame) (scope : List String)
    (expression : Atom) (position : Nat) (lower upper : Int) :
    KindArgumentAdmissionRel sourceSpace ((current).lookup scope sourceSpace) policy expression
      (condition lower upper) (.symbol "Bool") position before [before] [] := by
  apply HEArgumentMetatypeRole.singleton_inferred
  · exact fun kind _ => HERangeArgumentQueryTransport.bool_has_no_metatype_cut kind
  · exact HECollectionInferredQueries.comparison_query external active primitive subtypes scope before lower upper _
  · exact .unchanged (before.preserved_type_match policy
      (same_symbol_type_match "Bool" before.bindings (by decide) (by decide)))

theorem selection_from_query (policy : Policy) (before after : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom) (name : String)
    (queried : (current).lookup (invocationTypeScope scope live (bodyAt (number lower) (number upper)) expected before.bindings)
      sourceSpace before.bindings (.symbol "if") Atom.undefinedType [(signature name).functionType])
    (renewed : Frame.TypeRenewRel policy expected (.var name) before after) :
    (current).arguments.selection sourceSpace (current).lookup policy live scope
      (bodyAt (number lower) (number upper)) (.symbol "if") expected before (.selected (signature name) [after]) := by
  let names := invocationTypeScope scope live (bodyAt (number lower) (number upper)) expected before.bindings
  refine ⟨[(signature name).functionType], queried, .selected (errors := []) ?_ (by simp)⟩
  have first := comparison_admission minimal nativePolicy external active primitive subtypes policy before names
    (bodyAt (number lower) (number upper)) 1 lower upper
  have held (subject : Atom) (position : Nat) : KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (bodyAt (number lower) (number upper)) subject Atom.atomType position before [before] [] := by
    cases subject with
    | symbol name => exact .kind (.symbol name) (.atom _)
    | var name => exact .kind (.variable name) (.atom _)
    | grounded value => exact .kind (.grounded value) (.atom _)
    | expression children => exact .kind (.expression children) (.atom _)
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (bodyAt (number lower) (number upper)) 1 [condition lower upper, yes, no lower upper]
      [.symbol "Bool", Atom.atomType, Atom.atomType] [before] [before] [] :=
    .cons (AdmissionFramesRel.single first) (.cons (AdmissionFramesRel.single (held yes 2))
      (.cons (AdmissionFramesRel.single (held (no lower upper) 3)) .nil))
  simpa [signature, checkedFrames, checkedFailures, HEIfSourceSelection.Range.source_shape, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel)
      (expression := bodyAt (number lower) (number upper)) (expected := expected)
      (selected := signature name) (before := before) (operator := .symbol "if")
      (arguments := [condition lower upper, yes, no lower upper]) rfl args
      (List.Forall₂.cons (TypeCheckRel.accepted renewed) List.Forall₂.nil)

theorem arguments (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) :
    Stateful.ArgumentsRel current sourceSpace world live scope
      [(Entry.Value.ofAtom (condition lower upper), .symbol "Bool"),
       (Entry.Value.ofAtom yes, Atom.atomType), (Entry.Value.ofAtom (no lower upper), Atom.atomType)] before
      [(Entry.Value.argumentPacket [.grounded (.bool (decide (lower ≥ upper))),
        Entry.Value.ofAtom yes, Entry.Value.ofAtom (no lower upper)], before)] world (policy := policy) := by
  apply HEHeldSourceArguments.conditional
  · exact HEHeldSourceArguments.ground_read policy before yes rfl
  · exact HEHeldSourceArguments.ground_read policy before (no lower upper) rfl
  · simpa only [condition, number, Entry.Value.ofAtom, HEBinaryNumericSource.Operation.call,
      HEBinaryNumericSource.greaterEqual, List.map_cons, List.map_nil] using
      HECollectionArithmetic.comparison_source minimal nativePolicy external active primitive subtypes world policy before
        (argumentScope [(Entry.Value.ofAtom yes, Atom.atomType),
          (Entry.Value.ofAtom (no lower upper), Atom.atomType)] ++ live) scope lower upper

theorem source_activation (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom) (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ name selected after,
      (current).arguments.selection sourceSpace (current).lookup policy live scope
        (bodyAt (number lower) (number upper)) (.symbol "if") expected before (.selected (signature name) [selected]) ∧
      Stateful.FunctionRel current sourceSpace world (invocationReturnType (signature name) :: live) scope expected
        (signature name) (.symbol "if") (operands lower upper) selected [(reachedCall lower upper, after)] world (policy := policy) := by
  let names := invocationTypeScope scope live (bodyAt (number lower) (number upper)) expected before.bindings
  obtain ⟨name, queried, fresh⟩ := HECollectionInferredQueries.if_query ops external names before Atom.undefinedType
  have bindingFresh : name ∉ specBindingVars before.bindings := by
    intro member
    exact fresh (by simp [invocationTypeScope, member])
  let headLive := (signature name).functionType :: (operands lower upper).map Entry.Value.erase ++ invocationReturnType (signature name) :: live
  let headScope := scope ++ expectedApplicationScope (.expression ((Entry.Value.symbol "if" :: operands lower upper).map Entry.Value.erase)) expected
  have finish (selected after : Frame)
      (selectedRun : (current).arguments.selection sourceSpace (current).lookup policy live scope
        (bodyAt (number lower) (number upper)) (.symbol "if") expected before (.selected (signature name) [selected]))
      (headRun : Stateful.AtomRel current sourceSpace world headLive headScope (.symbol "if") (signature name).functionType selected
        [(.symbol "if", after)] world (policy := policy)) :
      ∃ name selected after,
        (current).arguments.selection sourceSpace (current).lookup policy live scope
          (bodyAt (number lower) (number upper)) (.symbol "if") expected before (.selected (signature name) [selected]) ∧
        Stateful.FunctionRel current sourceSpace world (invocationReturnType (signature name) :: live) scope expected (signature name)
          (.symbol "if") (operands lower upper) selected [(reachedCall lower upper, after)] world (policy := policy) := by
    have args := arguments minimal nativePolicy external active primitive subtypes world policy after
      ((Entry.Value.symbol "if").erase :: invocationReturnType (signature name) :: live) scope lower upper
    have branches : Stateful.FunctionBranchesRel current sourceSpace world (invocationReturnType (signature name) :: live) scope
        ((operands lower upper).zip (signature name).argumentTypes) [(.symbol "if", after)] [(reachedCall lower upper, after)] world (policy := policy) := by
      simpa [operands, signature, functionAssemble, reachedCall] using
        Stateful.FunctionBranchesRel.continuing (head := (Entry.Value.symbol "if", after))
          (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) args Stateful.FunctionBranchesRel.nil
    exact ⟨name, selected, after, selectedRun, .evaluated rfl headRun branches⟩
  rcases demand with numberDemand | undefinedDemand
  · subst expected
    obtain ⟨selected, bound, renewed, _⟩ := HEFreshRangeFrame.number_range_frame policy before name bindingFresh
    have selectedRun := selection_from_query minimal nativePolicy external active primitive subtypes policy before selected
      live scope lower upper (.symbol "Number") name queried renewed
    have facts := HEFreshRangeAlias.extended_private_facts before.bindings name (.symbol "Number") bindingFresh
    rw [←bound] at facts
    obtain ⟨right, headQuery, headFresh⟩ := HECollectionInferredQueries.if_query ops external
      (invocationTypeScope headScope headLive (.symbol "if") (signature name).functionType selected.bindings) selected (signature name).functionType
    obtain ⟨after, headRun, _, _⟩ := HEIfOperatorSource.source_of_query current policy sourceSpace world headLive headScope selected name right
      headQuery facts.2 facts.1 headFresh
    exact finish selected after selectedRun headRun
  · subst expected
    have renewed : Frame.TypeRenewRel policy Atom.undefinedType (.var name) before before :=
      .unchanged (before.preserved_type_match policy (.undefinedLeft _ _))
    have selectedRun := selection_from_query minimal nativePolicy external active primitive subtypes policy before before
      live scope lower upper Atom.undefinedType name queried renewed
    obtain ⟨right, headQuery, headFresh⟩ := HECollectionInferredQueries.if_query ops external
      (invocationTypeScope headScope headLive (.symbol "if") (signature name).functionType before.bindings) before (signature name).functionType
    obtain ⟨after, _, headRun⟩ := HERangeConditionalActivation.unconstrained_operator_of_query current policy sourceSpace world
      headLive headScope before name right headQuery bindingFresh headFresh
    exact finish before after selectedRun headRun

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionIfActivation
