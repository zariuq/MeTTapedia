import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFrontier
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEStatefulSelectedComposition

/-!
# Source-derived collapse of a typed square/range computation

The authored equation, fresh capture, context instruction, recursive child,
snapshot collection, fold and return are composed in the existing source
semantics. The typed call's argument is held until the authored metta step.
No child result array or whole-call execution is a premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseSource

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type Spec.Type.Presentation Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionCollapseFrontier (call call_closed)
open Mettapedia.Machines.OrderedProtocol.Completion

def signature : SelectedTypePolicy := ⟨CollectionStdlibSource.collapseType, [Atom.atomType], Atom.atomType, rfl⟩

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space
local notation "ops" => HECollectionInferredQueries.currentOps external active primitive subtypes

theorem invocation (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (caller : Option Atom) (lower upper : Int) :
    ∃ afterWorld after mark, Stateful.InvocationRel current sourceSpace world live scope caller (call lower upper) before
      [(.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat), after)] afterWorld (policy := policy) := by
  obtain ⟨work, captured, rename, injective, frontier, bindings, unified, bodyRead, fresh⟩ :=
    HECollectionCollapseFrontier.complete_frame policy live before lower upper
  have apart (left right : String) (different : left ≠ right) : rename left ≠ rename right :=
    fun same => different (injective same)
  obtain ⟨afterWorld, after, mark, executed⟩ := HECollectionCollapseFunction.source minimal nativePolicy external active primitive subtypes
    world policy captured live scope (some (call lower upper).erase) lower upper
    (rename "space") (rename "eval") (rename "result") (rename "res") (rename "item")
    (apart _ _ (by decide)) (fresh _ (by decide)) (fresh _ (by decide))
    (apart _ _ (by decide)) (apart _ _ (by decide)) (apart _ _ (by decide)) (apart _ _ (by decide))
    (apart _ _ (by decide)) (apart _ _ (by decide)) (apart _ _ (by decide))
  refine ⟨afterWorld, after, mark, Stateful.InvocationRel.equations (works := [work]) ?_ frontier (by simp) ?_⟩
  · simpa only [call, Entry.Value.erase, List.map_cons, List.map_nil] using
      HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes "collapse"
        [(HECollectionSquareRange.call lower upper).erase] (by simp)
  · simpa only [List.append_nil] using
      (Stateful.InvocationEquationsRel.cons bindings unified
        (by
          rw [bodyRead]
          exact Stateful.BoundaryRel.producerFunction (by
            refine ⟨?_, Or.inr rfl⟩
            simp [HECollectionCollapseFunction.function, Entry.Value.erase, Minimal.IsFunction]) executed)
        Stateful.InvocationEquationsRel.nil)

theorem called_scoped (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) :
    ∃ afterWorld after mark, Stateful.CallRel current sourceSpace world live scope (call lower upper) Atom.atomType before
      [(.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat), after)] afterWorld (policy := policy) ∧
      EquationProtectedNames.PreservesLive live before.bindings after.bindings := by
  obtain ⟨work, captured, rename, injective, frontier, bindings, unified, bodyRead, fresh, avoids⟩ :=
    HECollectionCollapseFrontier.complete_frame_scoped policy (Atom.atomType :: live) before lower upper
  have apart (left right : String) (different : left ≠ right) : rename left ≠ rename right :=
    fun same => different (injective same)
  obtain ⟨afterWorld, after, mark, executed, kept⟩ := HECollectionCollapseFunction.source_scoped minimal nativePolicy external active primitive subtypes
    world policy captured (Atom.atomType :: live) scope (some (call lower upper).erase) lower upper
    (rename "space") (rename "eval") (rename "result") (rename "res") (rename "item")
    (apart _ _ (by decide)) (fresh _ (by decide)) (fresh _ (by decide))
    (apart _ _ (by decide)) (apart _ _ (by decide)) (apart _ _ (by decide)) (apart _ _ (by decide))
    (apart _ _ (by decide)) (apart _ _ (by decide)) (apart _ _ (by decide))
  let output := Entry.Value.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat)
  have closed : TypeSubst.typeVars output.erase = [] := by
    simpa only [output, Entry.Value.erase, TypeSubst.typeVars] using
      HECollectionCollapseFunction.squares_closed lower (upper - lower).toNat
  have fixed := HECollectionClosedAppend.closed_read policy after output closed
  have returned : Stateful.ReturnRel current sourceSpace afterWorld live scope (call lower upper) Atom.atomType output after
      [(output, after)] afterWorld (policy := policy) := by
    by_cases stopped : IsEmptyOrErrorRel output.erase
    · exact .stopped stopped
    · refine .evaluate (by simp [output, Entry.Value.erase, Atom.notReducible]) stopped ?_
      have enter : Entry.Rel policy.reentry (after.read policy output).status (after.read policy output).erase Atom.atomType .deliver := by
        rw [fixed]
        exact Entry.Rel.pass stopped (by simp only [output, Entry.Value.erase]; exact .expression _) (Or.inl rfl)
      simpa only [fixed] using Stateful.AtomRel.delivered (environment := current) (label := sourceSpace)
        (world0 := afterWorld) (live := live) (scope := scope) (value := output) (frame := after) enter
  have preserved : EquationProtectedNames.PreservesLive live before.bindings after.bindings := by
    intro name visible unbound
    obtain ⟨atom, member, occurs⟩ := visible
    have exposed : QueryVisibleName (Atom.atomType :: live) (call lower upper).erase before.bindings name :=
      Or.inr (Or.inl ⟨atom, List.mem_cons_of_mem _ member, occurs⟩)
    have freshCaptured : name ∉ specBindingVars captured.bindings := by
      rw [bindings]
      exact EquationProtectedNames.closed_query frontier (by simp) name exposed unbound (call_closed lower upper)
    exact kept name ⟨atom, List.mem_cons_of_mem _ member, occurs⟩ freshCaptured
      (Ne.symm (avoids "res" name exposed)) (Ne.symm (avoids "item" name exposed))
  refine ⟨afterWorld, after, mark, ?_, preserved⟩
  refine Stateful.CallRel.equations (works := [work]) ?_ ?_ frontier (by simp) ?_
  · simp [call, Entry.Value.erase, IsErrorRel]
  · simpa only [call, Entry.Value.erase, List.map_cons, List.map_nil] using
      HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes "collapse"
        [(HECollectionSquareRange.call lower upper).erase] (by simp)
  · simpa only [List.append_nil] using
      (Stateful.EquationBodiesRel.cons bindings unified
        (by
          rw [bodyRead]
          exact Stateful.BoundaryRel.producerFunction (by
            refine ⟨?_, Or.inr rfl⟩
            simp [HECollectionCollapseFunction.function, Entry.Value.erase, Minimal.IsFunction]) executed)
        (Stateful.BoundaryBatchRel.single_iff.mpr (.returned returned)) Stateful.EquationBodiesRel.nil)

theorem called (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) :
    ∃ afterWorld after mark, Stateful.CallRel current sourceSpace world live scope (call lower upper) Atom.atomType before
      [(.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat), after)] afterWorld (policy := policy) := by
  obtain ⟨afterWorld, after, mark, executed, _kept⟩ := called_scoped minimal nativePolicy external active primitive subtypes
    world policy before live scope lower upper
  exact ⟨afterWorld, after, mark, executed⟩

theorem selection (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (lower upper : Int) :
    (current).arguments.selection sourceSpace (current).lookup policy live scope (call lower upper).erase
      (.symbol "collapse") Atom.undefinedType before (.selected signature [before]) := by
  let names := invocationTypeScope scope live (call lower upper).erase Atom.undefinedType before.bindings
  refine ⟨[signature.functionType], HECollectionInferredQueries.closed_head ops external names before "collapse" _ _ rfl rfl,
    .selected (errors := []) ?_ (by simp)⟩
  have args : AdmissionArgumentsRel KindArgumentAdmissionRel sourceSpace ((current).lookup names sourceSpace) policy
      (call lower upper).erase 1 [(HECollectionSquareRange.call lower upper).erase] [Atom.atomType] [before] [before] [] :=
    .cons (AdmissionFramesRel.single (KindArgumentAdmissionRel.held _ _ _ _ _ _ _)) .nil
  simpa [signature, checkedFrames, checkedFailures, names] using
    AdmissionApplicationRel.checked (admit := KindArgumentAdmissionRel) (expression := (call lower upper).erase)
      (expected := Atom.undefinedType) (selected := signature) (before := before) (operator := .symbol "collapse")
      (arguments := [(HECollectionSquareRange.call lower upper).erase]) (by simp [call, Entry.Value.erase]) args
      (List.Forall₂.cons (TypeCheckRel.accepted (.unchanged (before.preserved_type_match policy (.undefinedLeft _ _)))) .nil)

theorem held_argument (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) :
    Stateful.ArgumentsRel current sourceSpace world live scope [(HECollectionSquareRange.call lower upper, Atom.atomType)] before
      [(Entry.Value.argumentPacket [HECollectionSquareRange.call lower upper], before)] world (policy := policy) := by
  have delivered : ∀ nestedLive, Stateful.AtomRel current sourceSpace world nestedLive scope
      (HECollectionSquareRange.call lower upper) Atom.atomType before [(HECollectionSquareRange.call lower upper, before)] world
      (policy := policy) := by
    intro nestedLive
    have enter : Entry.Rel policy.reentry (before.read policy (HECollectionSquareRange.call lower upper)).status
        (before.read policy (HECollectionSquareRange.call lower upper)).erase Atom.atomType .deliver := by
      rw [HECollectionSquareRange.call_read]
      exact Entry.Rel.pass (by simp [HECollectionSquareRange.call, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (by simp only [HECollectionSquareRange.call, Entry.Value.erase]; exact .expression _) (Or.inl rfl)
    simpa only [HECollectionSquareRange.call_read] using Stateful.AtomRel.delivered (environment := current)
      (label := sourceSpace) (world0 := world) (live := nestedLive) (scope := scope)
      (value := HECollectionSquareRange.call lower upper) (frame := before) enter
  apply Stateful.ArgumentsRel.cons (delivered _)
  simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
    (Stateful.ArgumentBranchesRel.continuing (head := (HECollectionSquareRange.call lower upper, before))
      (by simp [ArgumentStopped]) (Stateful.ArgumentsRel.nil (frame := before)) Stateful.ArgumentBranchesRel.nil)

theorem source_scoped (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) :
    ∃ afterWorld after mark, Stateful.AtomRel current sourceSpace world live scope (call lower upper) Atom.undefinedType before
      [(.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat), after)] afterWorld (policy := policy) ∧
      EquationProtectedNames.PreservesLive live before.bindings after.bindings := by
  obtain ⟨afterWorld, after, mark, called, kept⟩ := called_scoped minimal nativePolicy external active primitive subtypes world policy before live scope lower upper
  let output := Entry.Value.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat)
  have originalRead := HECollectionClosedAppend.closed_read policy before (call lower upper) (call_closed lower upper)
  have outputClosed : TypeSubst.typeVars output.erase = [] := by
    simpa only [output, Entry.Value.erase, TypeSubst.typeVars] using HECollectionCollapseFunction.squares_closed lower (upper - lower).toNat
  have outputRead := HECollectionClosedAppend.closed_read policy after output outputClosed
  have calls : Stateful.CallsRel current sourceSpace world live scope (invocationReturnType signature)
      ([(Entry.Value.argumentPacket [HECollectionSquareRange.call lower upper], before)].map (functionAssemble (.symbol "collapse")))
      [(output, after)] afterWorld (policy := policy) := by
    simpa [signature, invocationReturnType, Atom.atomType, Atom.expressionType, functionAssemble, call, output] using
      Stateful.CallsRel.cons called Stateful.CallsRel.nil
  have priority : SuccessPriorityRel (fun row : Result => isErrorAtom row.1.erase)
      ([(output, after)].map (readResult policy)) [(output, after)] := by
    simpa only [List.map_cons, List.map_nil, readResult, outputRead] using HECollectionAppendSource.singleton_priority (output, after)
  have complete := HEStatefulSelectedComposition.selected_of_parts current policy sourceSpace world world world afterWorld
    live scope (call lower upper) Atom.undefinedType before before before .active (.symbol "collapse") (.symbol "collapse")
    [HECollectionSquareRange.call lower upper] signature [(Entry.Value.argumentPacket [HECollectionSquareRange.call lower upper], before)]
    [(output, after)] [(output, after)]
    (by
      rw [originalRead]
      simp only [call, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) (by decide) (Or.inr rfl))
    (by rw [originalRead]; rfl)
    (by simpa only [originalRead, Entry.Value.erase, environment, id_eq] using
      selection minimal nativePolicy external active primitive subtypes policy before live scope lower upper)
    rfl (HECollectionArithmetic.closed_operator minimal nativePolicy external active primitive subtypes world policy _ _ before
      "collapse" signature.functionType (by decide) (by decide) (by decide) rfl rfl)
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (by simpa [signature, invocationReturnType, Atom.expressionType, Atom.atomType, Entry.Value.erase] using
      (held_argument minimal nativePolicy external active primitive subtypes world policy before
        (Atom.symbol "collapse" :: Atom.atomType :: live) scope lower upper)) calls priority
  refine ⟨afterWorld, after, (Entry.Value.publish policy.marking (call lower upper).erase after.source output).status, ?_, kept⟩
  simpa only [originalRead, List.map_cons, List.map_nil, publishResult, Entry.Value.publish,
    Entry.Value.withStatus, Entry.Value.status, output] using complete

theorem source (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) :
    ∃ afterWorld after mark, Stateful.AtomRel current sourceSpace world live scope (call lower upper) Atom.undefinedType before
      [(.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat), after)] afterWorld (policy := policy) := by
  obtain ⟨afterWorld, after, mark, executed, _kept⟩ := source_scoped minimal nativePolicy external active primitive subtypes
    world policy before live scope lower upper
  exact ⟨afterWorld, after, mark, executed⟩

theorem retained_run (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ afterWorld after mark, RecursiveMachine.Contextual.WorldSteps (current).view (current).services
      (current).dispatch (current).lookup policy
      ⟨world, sourceSpace, .work (.atom live scope (call lower upper) Atom.undefinedType before), stack, emitted⟩
      ⟨afterWorld, sourceSpace, .returning [(.expression mark (HECollectionSquareRange.squares lower (upper - lower).toNat), after)],
        stack, emitted⟩ (admission := (current).arguments) := by
  obtain ⟨afterWorld, after, mark, executed⟩ := source minimal nativePolicy external active primitive subtypes world policy before live scope lower upper
  exact ⟨afterWorld, after, mark, RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.atom_complete executed stack) emitted⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseSource
