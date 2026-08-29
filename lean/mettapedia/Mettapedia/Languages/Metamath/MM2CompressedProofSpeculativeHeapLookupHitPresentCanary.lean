import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInstantiationCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchLastAdd

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitPresentCanary

open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

theorem direct_hit_pushes_exact_node :
    resolvedStackCell ∈ speculativeHitAfterDirect := by
  rcases direct_hit_full_instantiates_frame with
    ⟨substitution, rowMember, _pending, _lookup, _machine, _nextMachine,
      stack, _normalStack, _scan⟩
  unfold speculativeHitAfterDirect cFireReflectiveSourceExecFact
    cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row directHitFullRows
    (speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom)
    [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
     .add (.var "compressed-terminal-rule"),
     .add (.var "compressed-invalid-byte-rule"),
     .add (.var "compressed-question-rule"),
     .add (.var "compressed-question-open-fault-rule"),
     .remove directPendingTemplate, .remove directLookupTemplate,
     .remove directMachineTemplate, .add directNextMachineTemplate]
    directStackCellTemplate resolvedStackCell
    [.add directNormalStackCellTemplate, .add directResumedScanTemplate]
    substitution rowMember stack (by
      intro sink member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, rfl⟩
      · have equal := List.mem_singleton.mp member
        subst sink
        exact ⟨_, rfl⟩)

theorem direct_hit_publishes_complete_continuation :
    directNextMachine ∈ speculativeHitAfterDirect ∧
      directNormalStackCell ∈ speculativeHitAfterDirect ∧
      directResumedScan ∈ speculativeHitAfterDirect := by
  rcases direct_hit_full_instantiates_frame with
    ⟨substitution, rowMember, _pending, _lookup, _machine, nextMachine,
      _stack, normalStack, scan⟩
  unfold speculativeHitAfterDirect cFireReflectiveSourceExecFact
    cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  constructor
  · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row directHitFullRows
      (speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom)
      [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-invalid-byte-rule"),
       .add (.var "compressed-question-rule"),
       .add (.var "compressed-question-open-fault-rule"),
       .remove directPendingTemplate, .remove directLookupTemplate,
       .remove directMachineTemplate]
      directNextMachineTemplate directNextMachine
      [.add directStackCellTemplate, .add directNormalStackCellTemplate,
       .add directResumedScanTemplate]
      substitution rowMember nextMachine (by
        intro sink member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨_, rfl⟩
        · rcases List.mem_cons.mp member with rfl | member
          · exact ⟨_, rfl⟩
          · have equal := List.mem_singleton.mp member
            subst sink
            exact ⟨_, rfl⟩)
  · constructor
    · exact mem_cApplyReflectiveSinkBatch_append_add_cons_of_row directHitFullRows
        (speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom)
        [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
         .add (.var "compressed-terminal-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .remove directPendingTemplate, .remove directLookupTemplate,
         .remove directMachineTemplate, .add directNextMachineTemplate,
         .add directStackCellTemplate]
        directNormalStackCellTemplate directNormalStackCell
        [.add directResumedScanTemplate] substitution rowMember normalStack
        (by
          intro sink member
          have equal := List.mem_singleton.mp member
          subst sink
          exact ⟨_, rfl⟩)
    · exact mem_cApplyReflectiveSinkBatch_append_add_of_row directHitFullRows
        (speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom)
        [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
         .add (.var "compressed-terminal-rule"),
         .add (.var "compressed-invalid-byte-rule"),
         .add (.var "compressed-question-rule"),
         .add (.var "compressed-question-open-fault-rule"),
         .remove directPendingTemplate, .remove directLookupTemplate,
         .remove directMachineTemplate, .add directNextMachineTemplate,
         .add directStackCellTemplate, .add directNormalStackCellTemplate]
        directResumedScanTemplate directResumedScan substitution rowMember scan

#print axioms direct_hit_pushes_exact_node
#print axioms direct_hit_publishes_complete_continuation

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitPresentCanary
