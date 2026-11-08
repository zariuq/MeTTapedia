import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedConsumerFrame
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEPatternSlotReadback

/-!
# The complete demanded-constructor source program

The authored producer is evaluated as the consumer's operand after actual
inferred static selection. Its completed value and reached type frame enter
the fresh consumer equation, whose whole-argument slot returns that value.
Every query, call frontier, operand execution and publication uses one source
environment; no successful source-run premise is supplied.
Its reader instance is the historical annotation-override policy. The late
cast counterexample below preserves that historical regression; it does not
assert rejection by the repaired annotation-supplement native reader.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedWholeProgram

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Spec.Eval Spec.Eval.Completed Spec.Type
open HEDemandedConstructorEdge (space heldResult consumerSignature consumer)
open HEDemandedConstructorInferred (environment rangeDemand)
open HEDemandedConstructorProgram (producerCall)

def sourceCall : Entry.Value := .expression .active [.symbol "use-demand", producerCall]

theorem source_call_with_marking_of_reads (reads : HEDemandedReadInterface.Reads) (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (HEDemandedReadInterface.environment reads minimal) space () live scope sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
  let argLive := (Entry.Value.symbol "use-demand").erase :: invocationReturnType consumerSignature :: live
  obtain ⟨producedFrame, produced⟩ := HEDemandedConstructorProgram.producer_source_with_marking_of_reads reads minimal marking supported argLive scope
  have argTail : Stateful.ArgumentBranchesRel (HEDemandedReadInterface.environment reads minimal) space () argLive scope producerCall [] [] [] ()
      (policy := (HEDemandedPublication.policy marking)) := .nil
  have argBranches := Stateful.ArgumentBranchesRel.continuing
    (head := (heldResult, producedFrame))
    (by simp [ArgumentStopped, heldResult, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    (Stateful.ArgumentsRel.nil (environment := HEDemandedReadInterface.environment reads minimal) (label := space) (world0 := ())
      (live := heldResult.erase :: argLive) (scope := scope) (frame := producedFrame) (policy := (HEDemandedPublication.policy marking))) argTail
  have args : Stateful.ArgumentsRel (HEDemandedReadInterface.environment reads minimal) space () argLive scope [(producerCall, rangeDemand)] Frame.empty
      [(Entry.Value.argumentPacket [heldResult], producedFrame)] () (policy := (HEDemandedPublication.policy marking)) := by
    apply Stateful.ArgumentsRel.cons
    · simpa [argumentScope] using produced
    · simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using argBranches
  obtain ⟨after, called⟩ := HEDemandedConsumerFrame.consumer_call_with_marking_of_reads reads minimal marking producedFrame live scope
  have calls : Stateful.CallsRel (HEDemandedReadInterface.environment reads minimal) space () live scope (invocationReturnType consumerSignature)
      ([(Entry.Value.argumentPacket [heldResult], producedFrame)].map (functionAssemble (.symbol "use-demand")))
      [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) := by
    have combined := Stateful.CallsRel.cons (head := (HEDemandedConsumerFrame.query, producedFrame)) called Stateful.CallsRel.nil
    simpa [functionAssemble, consumerSignature, invocationReturnType, rangeDemand, HEDemandedConstructorEdge.demand,
      Atom.expressionType, HEDemandedConsumerFrame.query] using combined
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ([(heldResult, after)].map (readResult (HEDemandedPublication.policy marking))) [(heldResult, after)] := by
    simp only [List.map_cons, List.map_nil, readResult, HEDemandedPublication.read, HEDemandedConstructorEdge.held_read]
    simpa [heldResult, Entry.Value.erase, isErrorAtom] using
      (Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.successes
        (isError := fun result : Result => isErrorAtom result.1.erase) (raw := [(heldResult, after)])
        ⟨(heldResult, after), by simp, by simp [heldResult, Entry.Value.erase, isErrorAtom]⟩)
  have composed := HEStatefulSelectedComposition.selected_of_parts (HEDemandedReadInterface.environment reads minimal) (HEDemandedPublication.policy marking) space () () () ()
    live scope sourceCall rangeDemand Frame.empty Frame.empty Frame.empty .active
    (.symbol "use-demand") (.symbol "use-demand") [producerCall] consumerSignature
    [(Entry.Value.argumentPacket [heldResult], producedFrame)] [(heldResult, after)] [(heldResult, after)]
    (by
      simp only [Frame.read_empty, sourceCall, Entry.Value.status, Entry.Value.erase, List.map_cons, List.map_nil]
      exact Entry.Rel.expression (by simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (by simp [rangeDemand, HEDemandedConstructorEdge.demand, Atom.atomType, Atom.expressionType, Atom.variableType]) (Or.inr rfl))
    (by rw [Frame.read_empty]; rfl)
    (by simpa only [HEDemandedReadInterface.environment, WorldEnvironment.readOnly, id_eq,
        sourceCall, Frame.read_empty, Entry.Value.erase, List.map_cons, List.map_nil, producerCall,
        Entry.Value.erase_ofAtom, consumer] using HEDemandedConstructorInferred.consumer_selection_of_reads reads (HEDemandedPublication.policy marking) live scope)
    rfl
    (HEDemandedConstructorProgram.closed_operator_with_policy_of_reads reads minimal (HEDemandedPublication.policy marking) _ _ Frame.empty "use-demand" consumerSignature.functionType
      rfl (by decide) (by decide) (by decide) (reads.consumerHead _ Frame.empty _))
    (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
    args calls priority
  have publication := HEDemandedPublication.held marking supported consumer heldResult after.source
    (by simp [heldResult, Entry.Value.status]) (by simp [heldResult, Entry.Value.erase, isErrorAtom])
  refine ⟨after, ?_⟩
  simpa only [List.map_cons, List.map_nil, Frame.read_empty, sourceCall, Entry.Value.erase,
    producerCall, Entry.Value.erase_ofAtom, show Atom.expression [Atom.symbol "use-demand",
      HEDemandedConstructorEdge.producer] = consumer from rfl,
    publishResult, HEDemandedPublication.policy, publication] using composed

theorem source_call_with_marking (minimal : Minimal.Services) (marking : Entry.MarkPolicy)
    (supported : marking = .successes ∨ marking = .unchangedPreserving)
    (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := (HEDemandedPublication.policy marking)) :=
  source_call_with_marking_of_reads HEDemandedConstructorInferred.historicalReads minimal marking supported live scope

theorem source_call (minimal : Minimal.Services) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) :=
  source_call_with_marking minimal .successes (Or.inl rfl) live scope

/-- The whole authored program runs with the faithful mark-if-unchanged,
preserve-inherited policy. Completion is earned inside the derivation. -/
theorem source_call_preserving (minimal : Minimal.Services) (live : List Atom) (scope : List String) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () live scope sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.unchangedPreservingReady .preserve) :=
  source_call_with_marking minimal .unchangedPreserving (Or.inr rfl) live scope

/-- Under the historical annotation-override reader, a new final-value query
changes this complete program's result. Current supplement semantics may
accept that cast, so this remains explicitly a historical regression. -/
theorem whole_program_is_not_a_late_cast (minimal : Minimal.Services) :
    ∃ after : Frame,
      Stateful.AtomRel (environment minimal) space () [] [] sourceCall rangeDemand Frame.empty
        [(heldResult, after)] () (policy := Policy.ready) ∧
      NativeCompletedReturnRel space (HEDemandedConstructorEdge.inferredLookup [] space) Policy.ready heldResult rangeDemand after
        [(Entry.Value.ofAtom HEDemandedConstructorEdge.lateError, after)] := by
  obtain ⟨after, evaluated⟩ := source_call minimal [] []
  exact ⟨after, evaluated, HEDemandedConstructorEdge.fresh_final_cast_rejects after⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDemandedWholeProgram
