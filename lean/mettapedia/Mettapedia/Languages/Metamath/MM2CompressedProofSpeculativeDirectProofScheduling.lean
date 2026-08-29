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

#print axioms select_direct_proof_of_supported_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
