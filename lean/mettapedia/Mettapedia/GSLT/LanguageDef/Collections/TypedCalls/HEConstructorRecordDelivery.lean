import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorAdmission
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HESelectiveRangeGate
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDispatchDeopt
import Mettapedia.Languages.MeTTa.HE.BindingProjection

/-!
# Concrete constructor delivery under a selected open type record

The existing executable constructor certificate is reused, not replaced by a
value-level evaluation premise. Its declaration is closed, while the caller's
expected type and its retained binding record may be open. The actual range
matcher selects a record, argument delivery is derived from the recursive
certificate, and the real HE interpreter returns exactly that record with
the constructor value. This is a source-level record bridge, not just equality
of sets of ground type instances.

The closed-declaration certificate is one concrete native-relevant fragment.
Schematic constructor declarations, recursive inferred type lookup and the
source-to-native codec still need their broader adapters. No claim that all
native row-free constructor values satisfy this certificate is made.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorRecordDelivery

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem arguments_tail {space : Space} {dispatch : GroundedDispatch} {param arg : Atom}
    {params args : List Atom} (cert : CompletedArguments space dispatch (param :: params) (arg :: args)) :
    CompletedArguments space dispatch params args := by
  cases cert <;> assumption

/-- The recursive admission earns a uniform argument-delivery bound for
every incoming record. It does not require the record to be empty or closed. -/
theorem arguments_deliver {space : Space} {dispatch : GroundedDispatch} :
    ∀ params args, CompletedArguments space dispatch params args →
      (∀ param ∈ params, atomVariables param = []) →
      List.Forall₂ (ArgumentChecked space) params args ∧
        ∃ bound, ∀ extra bindings live,
          interpretArgs space dispatch args params bindings (bound + extra) live =
            [(argumentPacket args, bindings)]
  | [], [], .nil, _ => by
      refine ⟨.nil, 1, ?_⟩
      intro extra bindings live
      simpa [Nat.add_comm] using interpretArgs_nil_self bindings extra live
  | param :: params, arg :: args, cert, ground => by
      have first := cert.checked_head
      have paramGround := ground param (by simp)
      obtain ⟨checked, bound, tail⟩ := arguments_deliver params args (arguments_tail cert)
        (fun other member => ground other (List.mem_cons_of_mem _ member))
      refine ⟨.cons first checked, ?_⟩
      rcases cert.head_cases with held | leaf | ⟨range, completed, fits⟩
      · subst param
        refine ⟨bound + 2, ?_⟩
        intro extra bindings live
        rw [show bound + 2 + extra = (bound + extra + 1) + 1 by omega]
        apply interpretArgs_cons_self
        · intro retained
          exact evalAtom_held arg bindings _ retained
        · intro retained
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail (extra + 1) bindings retained
      · refine ⟨bound + matchFuel param + 2, ?_⟩
        intro extra bindings live
        rw [show bound + matchFuel param + 2 + extra = (bound + matchFuel param + extra + 1) + 1 by omega]
        apply interpretArgs_cons_self
        · intro retained
          exact evalAtom_leaf leaf paramGround first bindings (by omega) retained
        · intro retained
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            tail (matchFuel param + extra + 1) bindings retained
      · obtain ⟨valueBound, valueRun⟩ := evalAtom_completed_accepted completed
        refine ⟨bound + valueBound + 1, ?_⟩
        intro extra bindings live
        rw [show bound + valueBound + 1 + extra = (bound + valueBound + extra) + 1 by omega]
        apply interpretArgs_cons_self
        · intro retained
          have accepted : accepts param range = true := by
            rcases fits with rfl | rfl
            · exact accepts_undefined _
            · exact accepts_self _
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            valueRun (bound + extra) param bindings retained accepted
        · intro retained
          simpa [Nat.add_assoc] using tail (valueBound + extra) bindings retained

theorem applicable_selected_record {space : Space} {operator : Atom}
    {params args : List Atom} {range expected : Atom}
    (ground : atomVariables (arrowType params range) = [])
    (checked : List.Forall₂ (ArgumentChecked space) params args)
    (before after : Bindings) {fuel : Nat}
    (enough : matchFuel (arrowType params range) ≤ fuel)
    (returned : matchTypes expected range before fuel = [after]) :
    checkIfFunctionTypeIsApplicable (.expression (operator :: args)) (arrowType params range)
      expected space before (fuel + 1) = .inr [after] := by
  obtain ⟨paramsGround, _⟩ := arrowType_ground ground
  have loop := checkArgLoop_checked (expr := .expression (operator :: args))
    (bindings := before) (fuel := fuel) checked
    (fun param member => ⟨paramsGround param member,
      by have := matchFuel_param_lt (range := range) member; omega⟩) [] 1
  have lengths := checked.length_eq.symm
  rw [checkIfFunctionTypeIsApplicable]
  simp [getFunctionArgTypes_arrowType, getFunctionRetType_arrowType, lengths, loop, returned]

/-- Actual source interpretation at an open expected type returns the selected
record exactly. The range matcher, not a purported evaluation equality,
determines the new bindings. -/
theorem completed_selected_record {space : Space} {dispatch : GroundedDispatch}
    {value range : Atom} (cert : Completed space dispatch value range)
    (notError : isErrorAtom value = false) :
    ∃ bound, ∀ extra expected before after live,
      expected ≠ Atom.atomType → expected ≠ Atom.expressionType →
      matchTypes expected range before (bound + extra + 1) = [after] →
      evalAtom space dispatch value expected before (bound + extra + 4) live = [(value, after)] := by
  cases cert with
  | @typed head params args range declared ground notEmpty notExecutable notInstruction absent fields =>
      obtain ⟨paramsGround, _⟩ := arrowType_ground ground
      obtain ⟨checked, argsBound, argsRun⟩ := arguments_deliver params args fields paramsGround
      refine ⟨matchFuel (arrowType params range) + argsBound, ?_⟩
      intro extra expected before after live notAtom notExpression returned
      have applicable := applicable_selected_record (operator := .symbol head)
        ground checked before after (by omega) returned
      have notErrorHead : head ≠ "Error" := by
        intro same
        subst head
        simp [isErrorAtom] at notError
      rw [HEDispatchDeopt.strict_call declared ground notEmpty
        notErrorHead notAtom notExpression applicable (by omega) live]
      have arguments : interpretArgs space dispatch args params after
          (matchFuel (arrowType params range) + argsBound + extra + 1)
          (.symbol head :: callReturnType range :: live) = [(argumentPacket args, after)] := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          argsRun (matchFuel (arrowType params range) + extra + 1) after
            (.symbol head :: callReturnType range :: live)
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, arguments,
        HEDispatchDeopt.delivered_packet]
      have noQuery : rawQueryResults space (.expression (.symbol head :: args))
          (callReturnType range) after (matchFuel (arrowType params range) + argsBound + extra + 1)
          live = [] := by
        unfold rawQueryResults
        rw [absent]
        rfl
      rw [invoke_refused notExecutable notInstruction notError noQuery none]
      exact HEReturns.keep_clean (by simpa using notError)

/-- The executable certificate supplies the recursive premise. -/
theorem checked_selected_record {space : Space} {dispatch : GroundedDispatch}
    {depth : Nat} {value range : Atom}
    (checked : HEConstructorAdmission.check space dispatch depth value = some range)
    (notError : isErrorAtom value = false) :
    ∃ bound, ∀ extra expected before after live,
      expected ≠ Atom.atomType → expected ≠ Atom.expressionType →
      matchTypes expected range before (bound + extra + 1) = [after] →
      evalAtom space dispatch value expected before (bound + extra + 4) live = [(value, after)] :=
  completed_selected_record (HEConstructorAdmission.check_sound space dispatch depth value range checked) notError

/-- Every retained record observation is preserved by actual constructor
argument delivery, including an enclosing range whose variables are absent
from the returned value. No record-equivalence premise is assumed. -/
theorem checked_retained_observation {space : Space} {dispatch : GroundedDispatch}
    {depth : Nat} {value range : Atom}
    (checked : HEConstructorAdmission.check space dispatch depth value = some range)
    (notError : isErrorAtom value = false) :
    ∃ bound, ∀ extra expected before after live,
      expected ≠ Atom.atomType → expected ≠ Atom.expressionType →
      matchTypes expected range before (bound + extra + 1) = [after] →
      ∀ reads : BindingProjection.Applications,
        (evalAtom space dispatch value expected before (bound + extra + 4) live).map
          (fun reply => (reply.1, BindingProjection.observe reply.2 reads)) =
            [(value, BindingProjection.observe after reads)] := by
  obtain ⟨bound, delivery⟩ := checked_selected_record checked notError
  refine ⟨bound, ?_⟩
  intro extra expected before after live notAtom notExpression rangeMatched reads
  rw [delivery extra expected before after live notAtom notExpression rangeMatched]
  rfl

open FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.UniversalScopedCastAndHeadBoundary
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication

/-- Actual range matching constructs the contextual readout frame. The
recursive constructor interpretation then delivers an ordered singleton
related to that frame, with every later covered observation still available.
Neither a source-output record nor its readout certificate is assumed. -/
theorem checked_scoped_record {space : Space} {dispatch : GroundedDispatch}
    {depth : Nat} {value range : Atom}
    (checked : HEConstructorAdmission.check space dispatch depth value = some range)
    (notError : isErrorAtom value = false) :
    ∃ bound, ∀ extra expected before after live,
      expected ≠ Atom.atomType → expected ≠ Atom.expressionType →
      SyntacticallyClassCoherent before → after.hasLoop = false →
      matchTypes expected range before (bound + extra + 1) = [after] →
      ∃ frame : Spec.Eval.Completed.Frame,
        ScopedActivationRel after frame ∧
        List.Forall₂ ScopedResultRel
          (evalAtom space dispatch value expected before (bound + extra + 4) live)
          [(Spec.Eval.Entry.Value.ofAtom value, frame)] ∧
        ∀ observation readDepth (policy : Spec.Eval.Completed.Policy),
          after.applyFullCovered observation readDepth = true →
          after.applyFull observation readDepth =
            (frame.read policy (Spec.Eval.Entry.Value.ofAtom observation)).erase := by
  obtain ⟨bound, delivery⟩ := checked_selected_record checked notError
  refine ⟨bound, ?_⟩
  intro extra expected before after live notAtom notExpression coherent noLoop rangeMatched
  have member : after ∈ matchTypes expected range before (bound + extra + 1) := by
    rw [rangeMatched]
    simp
  obtain ⟨sourceOut, frame, _, _, _, _, _, _, activation⟩ :=
    matchTypes_mem_frameRelated_of_loopFree coherent member noLoop
  refine ⟨frame, activation, ?_, ?_⟩
  · rw [delivery extra expected before after live notAtom notExpression rangeMatched]
    exact .cons ⟨(Spec.Eval.Entry.Value.erase_ofAtom value).symm, activation⟩ .nil
  · intro observation readDepth policy covered
    have related : ScopedResultRel (observation, after)
        (Spec.Eval.Entry.Value.ofAtom observation, frame) :=
      ⟨(Spec.Eval.Entry.Value.erase_ofAtom observation).symm, activation⟩
    exact related.applyFull_eq_read_erase_of_covered policy readDepth covered

namespace Controls

open CompletedDelivery.Controls

def nested : Atom := succ (succ zero)
def before : Bindings := Bindings.empty.assign "saved" (.grounded (.int 9))
def selected : Bindings := before.assign "owed" nat
def expected : Atom := .var "owed"

theorem nested_admitted :
    HEConstructorAdmission.check natSpace GroundedDispatch.none 4 nested = some nat := by decide +kernel

theorem open_range_selects_record : matchTypes expected nat before 28 = [selected] := by decide +kernel

theorem actual_constructor_keeps_selected_record :
    evalAtom natSpace GroundedDispatch.none nested expected before 32 = [(nested, selected)] := by
  decide +kernel

theorem caller_range_and_saved_payload_survive :
    (evalAtom natSpace GroundedDispatch.none nested expected before 32).map
      (fun reply => (reply.2.applyFull expected 8, reply.2.applyFull (.var "saved") 8)) =
        [(nat, .grounded (.int 9))] := by
  rw [actual_constructor_keeps_selected_record]
  decide +kernel

theorem erasing_record_changes_caller_observation :
    BindingProjection.observe Bindings.empty [(expected, 8), (.var "saved", 8)] ≠
      BindingProjection.observe selected [(expected, 8), (.var "saved", 8)] := by decide +kernel

theorem bound_wrong_range_is_rejected :
    (evalAtom natSpace GroundedDispatch.none nested expected
      (before.assign "owed" bool) 32).map Prod.fst =
      [mkError nested (.badType expected nat)] := by decide +kernel

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEConstructorRecordDelivery
