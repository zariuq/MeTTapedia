import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeScalarInstances

/-!
# The current completed-return gate at the retained source frame

The final-expression question is evaluated with the names protected by the
actual caller frame. Its closed returned types are independent of that private
supply. This earns a requested new cast after the full source computation;
it does not identify that cast with held reentry or assume the cast succeeded.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type
open HEDemandedConstructorEdge (space heldResult other)
open HEDemandedCurrentReads (lookup ops)
open HEDemandedConstructorInferred (world)
open HEDemandedConstructorEdge (packet)
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply)
open HERepeatedFormalSource (signature)

def annotationNext (supply : Supply) : Supply :=
  (NativeTypeScopedReads.primitive (packet space) world supply (.annotations heldResult.erase)).2

theorem annotation_reply (supply : Supply) :
    NativeTypeScopedReads.primitive (packet space) world supply (.annotations heldResult.erase) =
      (some (.types [other]), annotationNext supply) := by
  apply Prod.ext
  · have observed : RetainedTypePayloads.observeList world space.atoms = space.atoms :=
      TypeDependencyAdmission.observeList_resourceFree world space.atoms (by decide)
    have declared : rawDeclarations (packet space) world heldResult.erase = [other] := by
      simp only [rawDeclarations, packet, TypeDependencyAdmission.observedSpace, observed,
        show RetainedTypePayloads.observeList world [] = [] from rfl]
      cbv
    simp [NativeTypeScopedReads.primitive, declared, TypeReadSupply.freshList, TypeReadSupply.fresh,
      instantiateTypeSignature, other, renameAtom]
  · rfl

def closureNext (seeds : List Atom) (supply : Supply) : Supply :=
  (NativeTypeScopedReads.primitive (packet space) world supply (.closure seeds)).2

theorem closure_reply (seeds : List Atom) (supply : Supply) :
    NativeTypeScopedReads.primitive (packet space) world supply (.closure seeds) =
      (some (.types seeds), closureNext seeds supply) := by
  apply Prod.ext
  · simp [NativeTypeScopedReads.primitive, HEDemandedConstructorInferred.closure_finished]
  · rfl

def headName (supply : Supply) : String :=
  instanceName (TypeReadSupply.remember supply [Atom.symbol "OtherDemandPair"]).used
    (atomVariables (signature "t").functionType).eraseDups
    (TypeReadSupply.remember supply [Atom.symbol "OtherDemandPair"]).next "t"

def operatorNext (depth : Nat) (supply : Supply) : Supply :=
  (NativeTypeScopedReads.evaluate ops (packet space) world (depth + 1)
    (.operatorRows (.symbol "OtherDemandPair")) supply).2

theorem operator_reply (depth : Nat) (supply : Supply) :
    NativeTypeScopedReads.evaluate ops (packet space) world (depth + 1)
      (.operatorRows (.symbol "OtherDemandPair")) supply =
      (some (.types [(signature (headName supply)).functionType]), operatorNext depth supply) := by
  apply Prod.ext
  · have shape : (TypeReadSupply.fresh (TypeReadSupply.remember supply [Atom.symbol "OtherDemandPair"])
        (signature "t").functionType).1 = (signature (headName supply)).functionType := by
      simp [TypeReadSupply.fresh, instantiateTypeSignature, signature, CompletedDelivery.arrowType,
        renameAtom, renameAtomList, headName]
    simp only [NativeTypeScopedReads.evaluate, NativeTypeCallGraph.body, NativeTypeCallGraph.typesRead,
      NativeTypeCallGraph.finishTypes, Mettapedia.Machines.ReadOnlyQueryDemand.demand,
      Mettapedia.Machines.QueryState.run, NativeTypeScopedReads.primitive,
      HEDemandedConstructorInferred.pair_declared, TypeReadSupply.freshList, List.isEmpty_cons,
      Bool.false_eq_true, ite_false, shape, NativeTypeRecursiveDriver.completed]
  · rfl

theorem final_driver_read (depth : Nat) (supply : Supply) :
    (NativeTypeScopedReads.evaluate ops (packet space) world (depth + 2)
      (.infer true heldResult.erase) supply).1 = some (.types [other, HEDemandedConstructorEdge.demand]) := by
  have classifyReply (current : Supply) : NativeTypeScopedReads.primitive (packet space) world current
      (.classify (.symbol "OtherDemandPair") [.grounded (.int 1), .grounded (.int 2)]) =
      (some (.class_ .ordinary), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, nativeClassify, NativeTypeScopedReads.retain]
  have annotationReply (current : Supply) : NativeTypeScopedReads.primitive (packet space) world current
      (.annotations (.expression [.symbol "OtherDemandPair", .grounded (.int 1), .grounded (.int 2)])) =
      (some (.types [other]), annotationNext current) := by
    simpa only [heldResult, Entry.Value.erase, List.map_cons, List.map_nil] using annotation_reply current
  have annotationPolicy : ops.annotationPolicy = .supplement
      (fun left right => RetainedTypePayloads.observe world left == RetainedTypePayloads.observe world right) := rfl
  have childReply (current : Supply) (value : Int) := HERangeTypeReadPrimitives.number_read ops (packet space) world depth value current
  have kindReply (current : Supply) (value : Int) : NativeTypeScopedReads.primitive (packet space) world current
      (.kind (.grounded (.int value))) = (some (.kind Atom.groundedType), current) := by
    simp [NativeTypeScopedReads.primitive, NativeTypeSourcePorts.primitive, NativeTypeScopedReads.retain, getMetaType]
  have arrow (name : String) : ops.arrow (signature name).functionType =
      some ([.var name, .var name], HEDemandedConstructorEdge.demand) := rfl
  have initial : ops.initial = Atom.var := rfl
  have firstMeta (name : String) : ops.metaCheck (ops.apply Atom.var (.var name)) Atom.groundedType = none := rfl
  have secondMeta (name : String) :
      ops.metaCheck (ops.apply (TypeScopeScalarInstances.state name) (.var name)) Atom.groundedType = none := by
    change TypeScopeMatcher.metaCheckAtom (TypeScopeScalarInstances.state name name) Atom.groundedType = none
    rw [TypeScopeScalarInstances.selected_value]
    rfl
  have firstMatch (name : String) :
      ops.unify Atom.var (.symbol "Number") (ops.apply Atom.var (.var name)) =
        some (TypeScopeScalarInstances.state name) := TypeScopeScalarInstances.selected name
  have secondMatch (name : String) :
      ops.unify (TypeScopeScalarInstances.state name) (.symbol "Number")
        (ops.apply (TypeScopeScalarInstances.state name) (.var name)) =
        some (TypeScopeScalarInstances.state name) := by
    change TypeScopeMatcher.unify world (TypeScopeScalarInstances.state name) (.symbol "Number")
      (TypeScopeScalarInstances.state name name) = _
    rw [TypeScopeScalarInstances.selected_value]
    exact TypeScopeScalarInstances.repeated name
  have normalized (state : TypeScopeMatcher.State) :
      ops.normalize (ops.apply state HEDemandedConstructorEdge.demand) = HEDemandedConstructorEdge.demand := rfl
  rw [NativeTypeScopedReads.evaluate]
  simp only [heldResult, Entry.Value.erase, List.map_cons, List.map_nil,
    NativeTypeCallGraph.body, NativeTypeCallGraph.node, NativeTypeCallGraph.annotated,
    NativeTypeCallGraph.typesRead, NativeTypeCallGraph.finishTypes,
    NativeTypeCallGraph.liftViews, NativeTypeCallGraph.viewQuestion,
    NativeTypeDemand.rowsPlan, NativeTypeDemand.argsPlan, NativeTypeDemand.typesRead,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, Mettapedia.Machines.QueryState.run,
    Mettapedia.Machines.ReadOnlyQuery.bind, Mettapedia.Machines.ReadOnlyQuery.map,
    classifyReply, annotationReply, annotationPolicy, closure_reply, operator_reply, childReply, kindReply,
    arrow, initial, firstMeta, secondMeta, firstMatch, secondMatch, normalized,
    List.isEmpty_cons, List.any_cons, List.any_nil, Option.isSome_some, Bool.true_or,
    Bool.false_eq_true, ite_false, ite_true, StampInference.firstResult,
    NativeTypeRecursiveDriver.completed, Except.map]
  rfl

theorem final_expression_read_at (scope : List String) (frame : Frame) (expected : Atom) :
    lookup scope space frame.bindings heldResult.erase expected
      [other, HEDemandedConstructorEdge.demand] := by
  change NativeTypeRecursiveDriver.publishTypes
    (NativeTypeScopedReads.evaluate ops (packet space) world (6 + 2)
      (.infer true heldResult.erase) ⟨invocationTypeScope scope [] heldResult.erase expected frame.bindings, 0⟩).1 = _
  rw [final_driver_read]
  rfl

theorem completed_at_frame (scope : List String) (frame : Frame) :
    NativeCompletedReturnRel space (lookup scope space) (Policy.unchangedPreservingReady .preserve)
      heldResult HEDemandedConstructorEdge.demand frame [(heldResult, frame)] := by
  have rejected : ∀ actual ∈ [other], ∀ output,
      ¬(Policy.unchangedPreservingReady .preserve).matching.Rel
        HEDemandedConstructorEdge.demand actual frame.bindings output := by
    intro actual member output matched
    cases List.mem_singleton.mp member
    have fits := (FirstSuccessSourceApplicability.closed_type_match_iff
      HEDemandedConstructorEdge.demand other frame.bindings output rfl rfl).mp matched
    simp [FirstSuccessSourceApplicability.ClosedTypeFits, HEDemandedConstructorEdge.demand, other,
      Atom.undefinedType, Atom.atomType] at fits
  have matched := frame.preserved_type_match (Policy.unchangedPreservingReady .preserve)
    (HEContextualArithmeticSource.same_symbol_match "DemandRange" frame.bindings (by decide) (by decide))
  have cast : TypeCastBatchRel space heldResult.erase HEDemandedConstructorEdge.demand frame.bindings
      [(heldResult.erase, frame.bindings)] (lookup := lookup scope space)
      (matching := (Policy.unchangedPreservingReady .preserve).matching.Rel) :=
    .success (earlierTypes := [other]) (laterTypes := [])
      (final_expression_read_at scope frame _) rfl rejected matched
  apply NativeCompletedReturnRel.cast HEDemandedConstructorEdge.final_value_needs_cast_at_a_new_boundary cast
  refine .cons ⟨rfl, .same frame, ?_⟩ .nil
  simp

/-- The source run earns the exact retained frame before the compiled slot
and requested completed-return gate are joined to it. -/
theorem source_slot_completed {L O P H : Type}
    (minimal : Minimal.Services) (sem : Mettapedia.Machines.RegisterCode.Sem Entry.Value L O P H)
    (answer : H → List Entry.Value → Option Entry.Value) (fuses : O → Nat → Bool)
    (destination next : Nat) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedCurrentSource.environment minimal) space () [] []
        HEDemandedWholeProgram.sourceCall HEDemandedConstructorEdge.demand Frame.empty
        [(heldResult, after)] () (policy := Policy.unchangedPreservingReady .preserve) ∧
      Mettapedia.Machines.RegisterCode.exec sem answer
        (Mettapedia.Machines.RegisterCode.compile fuses (.slot 0) true destination next).1
        HEDemandedSlotJoin.localRegisters = some (.ret heldResult) ∧
      NativeCompletedReturnRel space (lookup [] space) (Policy.unchangedPreservingReady .preserve)
        heldResult HEDemandedConstructorEdge.demand after [(heldResult, after)] := by
  obtain ⟨after, source, compiled⟩ := HEDemandedCurrentSource.source_and_slot_agree
    minimal sem answer fuses destination next
  exact ⟨after, source, compiled, completed_at_frame [] after⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedCurrentReturn
