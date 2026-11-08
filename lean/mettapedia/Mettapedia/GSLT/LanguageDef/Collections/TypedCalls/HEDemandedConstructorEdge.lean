import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERepeatedFormalSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorDeclarationGuard
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFreshSyntaxBinding

/-!
# A typed constructor result is not a fresh query of its final syntax

The fixture contains the actual shared-formal constructor, nullary producer
and consuming function, including an unrelated annotation on the completed
constructor expression. The constructor's source derivation earns both its
applicability and its publication. A subsequent held read at DemandRange is
distinct from asking the type service a new question about that expression.

The recursive reader controls are completed finite observations from the
historical annotation-override instance of the existing inference driver.
The current supplement policy may also return the constructor-derived type,
so the late-cast-error controls are historical regressions, not claims about
the repaired native reader. No universal native-reader correspondence or
termination for arbitrary queries is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorEdge

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type Spec.Type.Presentation
open Spec.Match.Merge

def demand : Atom := .symbol "DemandRange"
def other : Atom := .symbol "OtherDemandRange"
def producer : Atom := .expression [.symbol "other-demand-result"]
def consumerSignature : SelectedTypePolicy :=
  ⟨CompletedDelivery.arrowType [demand] demand, [demand], demand, rfl⟩
def consumer : Atom := .expression [.symbol "use-demand", producer]

def space : Space := Space.ofList
  [.expression [.symbol ":", .symbol "OtherDemandPair", (HERepeatedFormalSource.signature "t").functionType],
   .expression [.symbol ":", HERepeatedFormalSource.call, other],
   .expression [.symbol ":", .symbol "other-demand-result", CompletedDelivery.arrowType [] demand],
   .expression [.symbol "=", producer, HERepeatedFormalSource.call],
   .expression [.symbol ":", .symbol "use-demand", consumerSignature.functionType],
   .expression [.symbol "=", .expression [.symbol "use-demand", .var "value"], .var "value"]]

def heldResult : Entry.Value :=
  .expression .held [.symbol "OtherDemandPair", .grounded (.int 1), .grounded (.int 2)]

def environment (services : Minimal.Services) : WorldEnvironment Space Unit :=
  WorldEnvironment.readOnly services Completed.Controls.typedDispatch scopedLookup

/-- The producer of this result is the genuine two-Number constructor call,
not an axiom saying that a nominally annotated expression is already done. -/
theorem constructor_produces_held (services : Minimal.Services) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment services) space () live scope HERepeatedFormalSource.contextualCall demand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) := by
  apply HERepeatedFormalSource.constructor_ready (environment services) rfl rfl space () live scope
  · rfl
  · simp [environment, WorldEnvironment.readOnly, NonGroundedCallRel, Minimal.HostCall,
      Completed.Controls.typedDispatch, HERepeatedFormalSource.call, Minimal.embeddedInstruction]
  · change HEConstructorAdmission.headAbsent space "OtherDemandPair" = true
    decide

theorem held_read (frame : Frame) : frame.read Policy.ready heldResult = heldResult := by
  apply HEFreshSyntaxBinding.ground_substitution
  simp [heldResult, Entry.Value.erase, TypeSubst.typeVars, TypeSubst.typeVarsList]

/-- The demanded caller consumes the exact result and reached frame. The
source's held reentry case performs no second expression-type query. -/
theorem demanded_reentry (services : Minimal.Services) (frame : Frame) (live : List Atom) (scope : List String) :
    Stateful.AtomRel (environment services) space () live scope heldResult demand frame [(heldResult, frame)] ()
      (policy := Policy.ready) := by
  have entry : Entry.Rel Policy.ready.reentry (frame.read Policy.ready heldResult).status
      (frame.read Policy.ready heldResult).erase demand .deliver := by
    rw [held_read]
    simp only [heldResult, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil, Policy.ready]
    apply Entry.Rel.held
    · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · simp [demand, Atom.atomType, Atom.expressionType, Atom.variableType]
    · rfl
    · rfl
  have delivered := Stateful.AtomRel.delivered (environment := environment services) (label := space)
    (world0 := ()) (live := live) (scope := scope) (value := heldResult) (expected := demand)
    (frame := frame) (policy := Policy.ready)
    entry
  simpa only [held_read] using delivered

theorem produced_then_demanded (services : Minimal.Services) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment services) space () live scope HERepeatedFormalSource.contextualCall demand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) ∧
      Stateful.AtomRel (environment services) space () live scope heldResult demand after [(heldResult, after)] ()
        (policy := Policy.ready) := by
  obtain ⟨after, produced⟩ := constructor_produces_held services live scope
  exact ⟨after, produced, demanded_reentry services after live scope⟩

def packet (source : Space) : NativeTypeSourcePorts.Source :=
  ⟨source.atoms, [], fun _ _ => id, 4, "subtype", fun first second => first == second⟩

/-- Historical annotation-override inference, retaining a non-answer on
unfinished work. The scope is supplied to the existing fresh-name driver.
This is deliberately not the repaired annotation-supplement instance. -/
def inferredLookup (protectedNames : List String) (source : Space) : TypeLookupRel :=
  fun bindings value expected types =>
    NativeTypeRecursiveDriver.publishTypes
      (NativeTypeScopedReads.evaluate HEConstructorDeclarationGuard.Controls.sourceOps (packet source)
        (fun tag key => .grounded (.custom tag key)) 8 (.infer true value)
        ⟨invocationTypeScope protectedNames [] value expected bindings, 0⟩).1 = some types

set_option maxHeartbeats 1200000 in
theorem producer_inferred (protectedNames : List String) (frame : Frame) (expected : Atom) :
    inferredLookup protectedNames space frame.bindings producer expected [demand] := by cbv

theorem final_expression_inferred (protectedNames : List String) (frame : Frame) (expected : Atom) :
    inferredLookup protectedNames space frame.bindings heldResult.erase expected [other] := by cbv

set_option maxHeartbeats 1200000 in
theorem consumer_head_inferred (protectedNames : List String) (frame : Frame) (expected : Atom) :
    inferredLookup protectedNames space frame.bindings (.symbol "use-demand") expected [consumerSignature.functionType] := by cbv

/-- Static selection reads the authored producer call and obtains its
declared result type. It does not query the eventual expression in its place. -/
theorem consumer_static_selection (policy : Policy) (live : List Atom) (scope : List String) :
    InvocationSelectionRel space inferredLookup policy live scope consumer (.symbol "use-demand") demand Frame.empty
      (.selected consumerSignature [Frame.empty]) := by
  let names := invocationTypeScope scope live consumer demand Frame.empty.bindings
  have same : TypeMatchRel demand demand Frame.empty.bindings Frame.empty.bindings :=
    HEContextualArithmeticSource.same_symbol_match "DemandRange" Frame.empty.bindings (by decide) (by decide)
  have accepted : TypeCheckRel policy demand Frame.empty demand (.inr Frame.empty) :=
    .accepted (.unchanged (Frame.empty.preserved_type_match policy same))
  have argument : ArgumentChecksRel space (inferredLookup names space) policy consumer producer demand 1
      [Frame.empty] [Frame.empty] [] := by
    simpa [checkedFrames, checkedFailures] using
      (ArgumentChecksRel.cons (expression := consumer) (position := 1)
        (producer_inferred names Frame.empty demand) (.cons accepted .nil) .nil)
  have checked : ApplicationChecksRel space (inferredLookup names space) policy consumer demand consumerSignature
      Frame.empty [Frame.empty] [] := by
    simpa [consumer, consumerSignature, checkedFrames, checkedFailures] using
      (ApplicationChecksRel.checked (expression := consumer) (expected := demand) (selected := consumerSignature)
        (before := Frame.empty) (operator := .symbol "use-demand") (arguments := [producer]) rfl
        (.cons argument .nil) (.cons accepted .nil))
  exact ⟨[consumerSignature.functionType], consumer_head_inferred names Frame.empty _, .selected checked (by simp)⟩

def lateError : Atom := mkError heldResult.erase (.badType demand other)

theorem final_value_needs_cast_at_a_new_boundary : ¬CompletedNativeKeepRel heldResult.erase demand := by
  rintro (stopped | undefined | atom | ⟨metaType, category, passthrough⟩)
  · simp [heldResult, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty] at stopped
  · simp [demand, Atom.undefinedType] at undefined
  · simp [demand, Atom.atomType] at atom
  · simp only [heldResult, Entry.Value.erase, List.map_cons, List.map_nil] at category
    cases category
    simp [demand, Atom.expressionType, Atom.variableType] at passthrough

/-- With the historical override reader, inserting a new completed-value
cast asks a different question and produces the old error. The supplement
reader need not reject. No existing native cast boundary is elided here. -/
theorem fresh_final_cast_rejects (frame : Frame) :
    NativeCompletedReturnRel space (inferredLookup [] space) Policy.ready heldResult demand frame
      [(Entry.Value.ofAtom lateError, frame)] := by
  have queried := final_expression_inferred [] frame demand
  have rejected : ∀ actual ∈ [other], ∀ output,
      ¬Policy.ready.matching.Rel demand actual frame.bindings output := by
    intro actual member output matched
    cases List.mem_singleton.mp member
    have fits := (FirstSuccessSourceApplicability.closed_type_match_iff demand other frame.bindings output rfl rfl).mp matched
    simp [FirstSuccessSourceApplicability.ClosedTypeFits, demand, other, Atom.undefinedType, Atom.atomType] at fits
  have cast : TypeCastBatchRel space heldResult.erase demand frame.bindings [(lateError, frame.bindings)]
      (lookup := inferredLookup [] space) (matching := Policy.ready.matching.Rel) :=
    .failure queried rejected
  apply NativeCompletedReturnRel.cast final_value_needs_cast_at_a_new_boundary cast
  refine .cons ⟨by simp [rawResult], .same frame, ?_⟩ .nil
  change Entry.Value.ofAtom lateError =
    if lateError == heldResult.erase then heldResult else Entry.Value.ofAtom lateError
  rw [show (lateError == heldResult.erase) = false by cbv]
  rfl

/-- The historical reader discrepancy is reached after a real shared-formal
constructor derivation; all judgments retain the same selected frame. -/
theorem checked_producer_reuse_is_not_a_fresh_cast (services : Minimal.Services)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment services) space () live scope HERepeatedFormalSource.contextualCall demand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) ∧
      Stateful.AtomRel (environment services) space () live scope heldResult demand after [(heldResult, after)] ()
        (policy := Policy.ready) ∧
      NativeCompletedReturnRel space (inferredLookup [] space) Policy.ready heldResult demand after
        [(Entry.Value.ofAtom lateError, after)] := by
  obtain ⟨after, produced⟩ := constructor_produces_held services live scope
  exact ⟨after, produced, demanded_reentry services after live scope, fresh_final_cast_rejects after⟩

/-- The shared-formal producer is not admitted merely because its range
has the right name: the second field must agree with the first one's type. -/
theorem wrong_second_field_is_rejected :
    (checkIfFunctionTypeIsApplicable
      (.expression [.symbol "OtherDemandPair", .grounded (.int 1), .grounded (.string "wrong")])
      (HERepeatedFormalSource.signature "t").functionType demand space Bindings.empty 64).isLeft = true := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorEdge
