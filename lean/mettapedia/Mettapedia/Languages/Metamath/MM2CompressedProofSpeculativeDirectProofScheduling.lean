import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderProofCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAssertionCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderFaultCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAdvanceCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderPeerCanary

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderProofCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAssertionCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderFaultCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderAdvanceCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderPeerCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable
open Mettapedia.Languages.ProcessCalculi.MORK.WQComputable

private theorem selectNextScheduled_cons_isSome {α : Type}
    [SchedulerKey α] (head : α) (tail : List α) :
    (selectNextScheduled (head :: tail)).isSome = true := by
  unfold selectNextScheduled
  induction tail generalizing head with
  | nil => rfl
  | cons candidate remaining induction =>
      simp only [List.foldl_cons]
      split
      · exact induction candidate
      · exact induction head

def directLookupInterface : List SourceExecFact :=
  [compressedProofStepDirective, compressedAssertionLaunchDirective,
   compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
   speculativeDirectProofDirective, speculativeDirectAssertionDirective]

private theorem directLookupInterface_does_not_preempt_direct
    (candidate : SourceExecFact) (member : candidate ∈ directLookupInterface) :
    lexLt (SchedulerKey.key candidate)
      (SchedulerKey.key speculativeDirectProofDirective) = false := by
  simp only [directLookupInterface, List.mem_cons, List.not_mem_nil,
    or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact lexLt_asymm _ _ direct_proof_preempts_cursor_proof
  · exact lexLt_asymm _ _ direct_proof_preempts_cursor_assertion
  · exact lexLt_asymm _ _ direct_proof_preempts_cursor_fault
  · exact lexLt_asymm _ _ direct_proof_preempts_cursor_advance
  · exact lexLt_irrefl _
  · exact direct_assertion_does_not_preempt_direct_proof

private theorem foldl_keeps_direct_proof
    (remaining : List SourceExecFact)
    (within : ∀ candidate ∈ remaining, candidate ∈ directLookupInterface) :
    selectNextScheduled (speculativeDirectProofDirective :: remaining) =
      some speculativeDirectProofDirective := by
  unfold selectNextScheduled
  simp only [List.foldl_cons]
  induction remaining with
  | nil => rfl
  | cons candidate remaining induction =>
      simp only [List.foldl_cons]
      rw [directLookupInterface_does_not_preempt_direct candidate
        (within candidate (by simp))]
      exact induction (fun later laterMember =>
        within later (List.mem_cons_of_mem candidate laterMember))

/-- Scheduling of the generated direct proof handler depends only on the
exact six-rule lookup interface, not on the guest data that exposed it. -/
theorem select_direct_proof_of_supported_exact {space : List Atom}
    (supported : cSupportedSourceExecFacts space =
      [compressedProofStepDirective, compressedAssertionLaunchDirective,
       compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
       speculativeDirectProofDirective, speculativeDirectAssertionDirective]) :
    selectNextScheduled (cSupportedSourceExecFacts space) =
      some speculativeDirectProofDirective := by
  rw [supported]
  let before : List SourceExecFact :=
    [compressedProofStepDirective, compressedAssertionLaunchDirective,
     compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective]
  cases selectedEq : selectNextScheduled before with
  | none =>
      have nonempty := selectNextScheduled_cons_isSome
        compressedProofStepDirective
        [compressedAssertionLaunchDirective, compressedHeapLookupFaultDirective,
         compressedHeapLookupAdvanceDirective]
      simp only [before, selectedEq, Option.isSome_none] at nonempty
      exact Bool.noConfusion nonempty
  | some incumbent =>
      have incumbentMem : incumbent ∈ before :=
        selectNextScheduled_mem selectedEq
      have directPreempts :
          lexLt (SchedulerKey.key speculativeDirectProofDirective)
            (SchedulerKey.key incumbent) = true := by
        simp only [before, List.mem_cons, List.not_mem_nil, or_false] at incumbentMem
        rcases incumbentMem with rfl | rfl | rfl | rfl
        · exact direct_proof_preempts_cursor_proof
        · exact direct_proof_preempts_cursor_assertion
        · exact direct_proof_preempts_cursor_fault
        · exact direct_proof_preempts_cursor_advance
      unfold selectNextScheduled at selectedEq ⊢
      rw [show
        [compressedProofStepDirective, compressedAssertionLaunchDirective,
         compressedHeapLookupFaultDirective, compressedHeapLookupAdvanceDirective,
         speculativeDirectProofDirective, speculativeDirectAssertionDirective] =
          before ++
            [speculativeDirectProofDirective,
             speculativeDirectAssertionDirective] by rfl]
      rw [List.foldl_append, selectedEq]
      simp only [List.foldl_cons, directPreempts, ↓reduceIte,
        direct_assertion_does_not_preempt_direct_proof, Bool.false_eq_true,
        List.foldl_nil]

/-- The direct proof handler is selected from any duplicate-tolerant ordering
of the six-rule lookup interface.  This is the scheduler theorem used by
source-derived spaces, where exact membership and no-invention are stronger
and more stable obligations than a particular list enumeration. -/
theorem select_direct_proof_of_supported_within {space : List Atom}
    (present : speculativeDirectProofDirective ∈
      cSupportedSourceExecFacts space)
    (within : ∀ candidate ∈ cSupportedSourceExecFacts space,
      candidate ∈ directLookupInterface) :
    selectNextScheduled (cSupportedSourceExecFacts space) =
      some speculativeDirectProofDirective := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp present
  have beforeWithin : ∀ candidate ∈ before,
      candidate ∈ directLookupInterface := by
    intro candidate member
    apply within candidate
    rw [split]
    simp [member]
  have afterWithin : ∀ candidate ∈ after,
      candidate ∈ directLookupInterface := by
    intro candidate member
    apply within candidate
    rw [split]
    simp [member]
  cases selectedEq : selectNextScheduled before with
  | none =>
      unfold selectNextScheduled at selectedEq ⊢
      rw [split, List.foldl_append, selectedEq]
      simp only [List.foldl_cons]
      change selectNextScheduled
        (speculativeDirectProofDirective :: after) =
          some speculativeDirectProofDirective
      exact foldl_keeps_direct_proof after afterWithin
  | some incumbent =>
      have incumbentMember : incumbent ∈ before :=
        selectNextScheduled_mem selectedEq
      have incumbentAllowed := beforeWithin incumbent incumbentMember
      have afterDirect :
          (if lexLt (SchedulerKey.key speculativeDirectProofDirective)
              (SchedulerKey.key incumbent)
            then some speculativeDirectProofDirective else some incumbent) =
            some speculativeDirectProofDirective := by
        simp only [directLookupInterface, List.mem_cons, List.not_mem_nil,
          or_false] at incumbentAllowed
        rcases incumbentAllowed with rfl | rfl | rfl | rfl | rfl | rfl
        · simp [direct_proof_preempts_cursor_proof]
        · simp [direct_proof_preempts_cursor_assertion]
        · simp [direct_proof_preempts_cursor_fault]
        · simp [direct_proof_preempts_cursor_advance]
        · simp [lexLt_irrefl]
        · simp [direct_proof_preempts_direct_assertion]
      unfold selectNextScheduled at selectedEq ⊢
      rw [split, List.foldl_append, selectedEq]
      simp only [List.foldl_cons, afterDirect]
      change selectNextScheduled
        (speculativeDirectProofDirective :: after) =
          some speculativeDirectProofDirective
      exact foldl_keeps_direct_proof after afterWithin

#print axioms select_direct_proof_of_supported_exact
#print axioms select_direct_proof_of_supported_within

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
