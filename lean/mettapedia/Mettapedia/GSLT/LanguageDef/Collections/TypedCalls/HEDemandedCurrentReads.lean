import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConstructorProgram

/-!
# Current supplement-reader observations for the demanded constructor

The actual six-row source includes an expression-subject annotation, so a
no-expression-row global agreement theorem does not apply. These are direct
observations of the occurrence-scoped inference driver with currentOps.
The private-name supply is still threaded by the existing evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply)
open HEDemandedConstructorEdge (space packet producer consumerSignature heldResult demand other)
open HEDemandedConstructorInferred (world)
open HERepeatedFormalSource (signature)

def ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom :=
  TypeScopeMatcher.currentOps world
    (InertTypeDependencies.normalize (fun _ => false) (fun _ _ => none)) (fun _ => [])

def lookup (protectedNames : List String) (source : Space) : TypeLookupRel :=
  fun bindings value expected types =>
    NativeTypeRecursiveDriver.publishTypes
      (NativeTypeScopedReads.evaluate ops (packet source) world 8 (.infer true value)
        ⟨invocationTypeScope protectedNames [] value expected bindings, 0⟩).1 = some types

theorem symbol_read (depth : Nat) (supply : Supply) (name : String) (type : Atom)
    (declared : rawDeclarations (packet space) world (.symbol name) = [type]) :
    (NativeTypeScopedReads.evaluate ops (packet space) world (depth + 1) (.infer true (.symbol name)) supply).1 =
      some (.types [(TypeReadSupply.fresh (TypeReadSupply.remember supply [.symbol name]) type).1]) := by
  simp only [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
    NativeTypeCallGraph.closeTypes, NativeTypeCallGraph.finishTypes,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList, List.isEmpty_cons,
    Bool.false_eq_true, ite_false, ite_true, HEDemandedConstructorInferred.closure_finished,
    Option.map_some, NativeTypeRecursiveDriver.completed]

theorem pair_head_read (scope : List String) (before : Frame) (expected : Atom) :
    ∃ name,
      lookup scope space before.bindings (.symbol "OtherDemandPair") expected [(signature name).functionType] ∧
      name ∉ invocationTypeScope scope [] (.symbol "OtherDemandPair") expected before.bindings := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.symbol "OtherDemandPair") expected before.bindings, 0⟩
  let prepared := TypeReadSupply.remember supply [Atom.symbol "OtherDemandPair"]
  let original := (signature "t").functionType
  let name := instanceName prepared.used (atomVariables original).eraseDups prepared.next "t"
  have shape : (TypeReadSupply.fresh prepared original).1 = (signature name).functionType := by
    simp [TypeReadSupply.fresh, instantiateTypeSignature, original, signature,
      CompletedDelivery.arrowType, renameAtom, renameAtomList, name]
  have observed := symbol_read 7 supply "OtherDemandPair" original HEDemandedConstructorInferred.pair_declared
  refine ⟨name, ?_, ?_⟩
  · change NativeTypeRecursiveDriver.publishTypes
      (NativeTypeScopedReads.evaluate ops (packet space) world 8 (.infer true (.symbol "OtherDemandPair")) supply).1 = _
    rw [observed]
    change some [(TypeReadSupply.fresh prepared original).1] = some [(signature name).functionType]
    exact congrArg (fun type => some [type]) shape
  · exact instanceName_not_mem prepared.used (atomVariables original).eraseDups prepared.next "t"

theorem number_read (scope : List String) (before : Frame) (value : Int) (expected : Atom) :
    lookup scope space before.bindings (.grounded (.int value)) expected [.symbol "Number"] := by
  let supply : Supply := ⟨invocationTypeScope scope [] (.grounded (.int value)) expected before.bindings, 0⟩
  have observed := HERangeTypeReadPrimitives.number_read ops (packet space) world 7 value supply
  exact congrArg (fun result => NativeTypeRecursiveDriver.publishTypes result.1) observed

set_option maxHeartbeats 1200000 in
theorem producer_inferred (scope : List String) (before : Frame) (expected : Atom) :
    lookup scope space before.bindings producer expected [HEDemandedConstructorEdge.demand] := by cbv

set_option maxHeartbeats 1200000 in
theorem consumer_head_read (scope : List String) (before : Frame) (expected : Atom) :
    lookup scope space before.bindings (.symbol "use-demand") expected [consumerSignature.functionType] := by cbv

set_option maxHeartbeats 1200000 in
theorem producer_head_read (scope : List String) (before : Frame) (expected : Atom) :
    lookup scope space before.bindings (.symbol "other-demand-result") expected
      [HEDemandedConstructorProgram.producerSignature.functionType] := by cbv

def reads : HEDemandedReadInterface.Reads where
  lookup := lookup
  pair := pair_head_read
  number := number_read
  producer := producer_inferred
  consumerHead := consumer_head_read
  producerHead := producer_head_read

set_option maxHeartbeats 1600000 in
/-- Unlike the historical override policy, a new query of this completed
expression retains its annotation and also earns the constructor result. -/
theorem final_expression_read :
    lookup [] space Frame.empty.bindings heldResult.erase HEDemandedConstructorEdge.demand
      [other, HEDemandedConstructorEdge.demand] := by cbv

theorem historical_override_is_not_current :
    ¬lookup [] space Frame.empty.bindings heldResult.erase HEDemandedConstructorEdge.demand [other] := by
  intro old
  have both := final_expression_read.symm.trans old
  simp at both

/-- The repaired reader also supports an explicitly requested new boundary
cast. The source's held reentry and this fresh successful cast remain
different operations, even though their returned values now agree here. -/
theorem new_final_cast_accepts :
    NativeCompletedReturnRel space (lookup [] space) Policy.ready heldResult HEDemandedConstructorEdge.demand
      Frame.empty [(heldResult, Frame.empty)] := by
  have rejected : ∀ actual ∈ [other], ∀ output,
      ¬Policy.ready.matching.Rel HEDemandedConstructorEdge.demand actual Frame.empty.bindings output := by
    intro actual member output matched
    cases List.mem_singleton.mp member
    have fits := (FirstSuccessSourceApplicability.closed_type_match_iff
      HEDemandedConstructorEdge.demand other Frame.empty.bindings output rfl rfl).mp matched
    simp [FirstSuccessSourceApplicability.ClosedTypeFits, HEDemandedConstructorEdge.demand, other,
      Atom.undefinedType, Atom.atomType] at fits
  have matched := Frame.empty.preserved_type_match Policy.ready
    (HEContextualArithmeticSource.same_symbol_match "DemandRange" Frame.empty.bindings (by decide) (by decide))
  have cast : TypeCastBatchRel space heldResult.erase HEDemandedConstructorEdge.demand Frame.empty.bindings
      [(heldResult.erase, Frame.empty.bindings)] (lookup := lookup [] space) (matching := Policy.ready.matching.Rel) :=
    .success (earlierTypes := [other]) (laterTypes := []) final_expression_read rfl rejected matched
  apply NativeCompletedReturnRel.cast HEDemandedConstructorEdge.final_value_needs_cast_at_a_new_boundary cast
  refine .cons ⟨rfl, .same Frame.empty, ?_⟩ .nil
  simp

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentReads
