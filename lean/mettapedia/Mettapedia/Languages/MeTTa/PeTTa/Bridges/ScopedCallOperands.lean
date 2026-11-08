import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedMutationSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedPatternSupport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CapturedQueryOperands

/-!
# Captured variable operands at authored call entry

Two evaluated variable operands retain their reached equations and original
caller. Their values are not reinterpreted as source code. Raw-argument
declarations remain explicit admission conditions for this five-step route.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCallOperands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)

def source (head left right : String) : Atom := .expression [.symbol head, .var left, .var right]
def entry (caller : Control) (head left right : String) (destination : Atom) : Control :=
  {caller with goals := .evaluate (source head left right) destination :: caller.goals}
def slot (caller : Control) (head left right : String) (destination : Atom) (index : Nat) : String :=
  freshName (entry caller head left right destination) index
def firstBindings (caller : Control) (head left right : String) (destination : Atom) : Equations :=
  caller.bindings ++ [(.var left, .var (slot caller head left right destination 0))]
def ready (caller : Control) (head left right : String) (destination : Atom) : Control :=
  {caller with
    bindings := firstBindings caller head left right destination ++
      [(.var right, .var (slot caller head left right destination 1))]
    goals := .invoke head [.var (slot caller head left right destination 0),
      .var (slot caller head left right destination 1)] destination :: caller.goals}

theorem slot_fresh (caller : Control) (head left right : String) (destination : Atom) (index : Nat) :
    FreshFor (slot caller head left right destination index) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (entry caller head left right destination) _ (freshName_not_mem _ _)

theorem slot_apart (caller : Control) (head left right : String) (destination : Atom) (index : Nat)
    (name : String) (argument : name = left ∨ name = right) :
    slot caller head left right destination index ≠ name := by
  intro same
  apply freshName_not_mem (entry caller head left right destination) index
  change slot caller head left right destination index ∈ (entry caller head left right destination).support
  rw [same]
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  refine Or.inr ⟨source head left right, ?_, ?_⟩
  · simp [entry, Goal.atoms]
  · rw [source, CapturedPatternSupport.mem_expression_names]
    rcases argument with rfl | rfl
    · exact ⟨.var name, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
    · exact ⟨.var name, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

theorem slots_distinct (caller : Control) (head left right : String) (destination : Atom) :
    slot caller head left right destination 1 ≠ slot caller head left right destination 0 := by
  intro same
  have indices := freshName_injective (entry caller head left right destination) same
  omega

theorem first_refined (caller : Control) (head left right : String) (destination : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (.var left) (.var (slot caller head left right destination 0)) =
      some (firstBindings caller head left right destination) := by
  apply ScopedMutationSource.refine_fresh_operand
  · exact slot_fresh caller head left right destination 0
  · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using
      slot_apart caller head left right destination 0 left (Or.inl rfl)
  · exact consistent

theorem second_refined (caller : Control) (head left right : String) (destination : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine (firstBindings caller head left right destination) (.var right)
      (.var (slot caller head left right destination 1)) =
      some (ready caller head left right destination).bindings := by
  apply ScopedMutationSource.refine_fresh_operand
  · intro pair member
    rcases List.mem_append.mp member with old | added
    · exact slot_fresh caller head left right destination 1 pair old
    · cases List.mem_singleton.mp added
      simp [encode, Mettapedia.Logic.LP.Term.freeVars,
        slot_apart caller head left right destination 1 left (Or.inl rfl), slots_distinct]
  · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using
      slot_apart caller head left right destination 1 right (Or.inr rfl)
  · exact ClosedOnceQueryFrame.refined_consistent _ _ _ (first_refined caller head left right destination consistent)

theorem ready_consistent (caller : Control) (head left right : String) (destination : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    ∃ environment, Solves environment (ready caller head left right destination).bindings :=
  ClosedOnceQueryFrame.refined_consistent _ _ _ (second_refined caller head left right destination consistent)

theorem ready_inherited (caller : Control) (head left right : String) (destination : Atom)
    (environment : Environment) (solved : Solves environment (ready caller head left right destination).bindings) :
    Solves environment caller.bindings := by
  intro pair member
  exact solved pair (List.mem_append_left _ (List.mem_append_left _ member))

theorem slot_destination_apart (caller : Control) (head left right result : String) (index : Nat) :
    slot caller head left right (.var result) index ≠ result := by
  intro same
  apply freshName_not_mem (entry caller head left right (.var result)) index
  change slot caller head left right (.var result) index ∈ (entry caller head left right (.var result)).support
  rw [same]
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ result).mpr
  exact Or.inr ⟨.var result, by simp [entry, Goal.atoms], by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

theorem ready_result_fresh (caller : Control) (head left right result : String)
    (fresh : FreshFor result caller.bindings) (leftApart : result ≠ left) (rightApart : result ≠ right) :
    FreshFor result (ready caller head left right (.var result)).bindings := by
  intro pair member
  rcases List.mem_append.mp member with earlier | last
  · rcases List.mem_append.mp earlier with old | added
    · exact fresh pair old
    · cases List.mem_singleton.mp added
      simp [encode, Mettapedia.Logic.LP.Term.freeVars, leftApart,
        Ne.symm (slot_destination_apart caller head left right result 0)]
  · cases List.mem_singleton.mp last
    simp [encode, Mettapedia.Logic.LP.Term.freeVars, rightApart,
      Ne.symm (slot_destination_apart caller head left right result 1)]

/-- Both prepared operand slots retain the closed readings of the actual
incoming principal solver. Open code-looking values are never evaluated here. -/
theorem ready_readings (caller : Control) (head left right : String) (destination : Atom)
    (before after : Environment) (leftValue rightValue : Atom)
    (beforeResolved : resolve caller.bindings = some before)
    (afterResolved : resolve (ready caller head left right destination).bindings = some after)
    (leftRead : read before (.var left) = leftValue) (rightRead : read before (.var right) = rightValue)
    (leftClosed : ∀ environment, read environment leftValue = leftValue)
    (rightClosed : ∀ environment, read environment rightValue = rightValue) :
    read after (.var (slot caller head left right destination 0)) = leftValue ∧
      read after (.var (slot caller head left right destination 1)) = rightValue := by
  have solved := resolve_sound afterResolved
  have inherited := ready_inherited caller head left right destination after solved
  have leftValueRead := CapturedQueryOperands.resolved_forces beforeResolved (.var left) leftValue leftRead leftClosed after inherited
  have rightValueRead := CapturedQueryOperands.resolved_forces beforeResolved (.var right) rightValue rightRead rightClosed after inherited
  have first := solved (.var left, .var (slot caller head left right destination 0))
    (List.mem_append_left _ (List.mem_append_right _ (by simp)))
  have second := solved (.var right, .var (slot caller head left right destination 1))
    (List.mem_append_right _ (by simp))
  exact ⟨first.symm.trans leftValueRead, second.symm.trans rightValueRead⟩

set_option maxHeartbeats 1200000 in
theorem preparation {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context)) (head left right : String) (destination : Atom)
    (ordinary : head ≠ "let*" ∧ head ≠ "if") (declared : callable program head = true)
    (leftEvaluated : Eval.argumentIsRaw program head 0 = false)
    (rightEvaluated : Eval.argumentIsRaw program head 1 = false)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine policy program).run 5
      (placed allocator world scope parents (entry caller head left right destination) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (ready caller head left right destination) context origins pending)) := by
  have first := first_refined caller head left right destination consistent
  have second := second_refined caller head left right destination consistent
  simp only [firstBindings, ready, slot, entry, source] at first second
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, entry, source, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    prepare, replace, installChild, retainChild, callArguments, freshSlots, List.range_succ,
    ordinary.1, ordinary.2, declared, leftEvaluated, rightEvaluated, firstBindings, ready, slot, first, second]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCallOperands
