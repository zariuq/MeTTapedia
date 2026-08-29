import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInstantiationCanary
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitAbsentCanary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInstantiationCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

private theorem direct_output_ne_pending (substitution : Subst)
    (template : Atom) (headName : String) (head : ∃ tail,
      template = .expression (.symbol headName :: tail))
    (different : headName ≠ "mm-compressed-step-pending") :
    instantiateTemplateAtom? substitution template ≠ some directStepPending := by
  obtain ⟨tail, rfl⟩ := head
  unfold directStepPending
  apply instantiateTemplateAtom?_expression_symbol_head_ne
  exact different

private theorem direct_output_ne_lookup (substitution : Subst)
    (template : Atom) (headName : String) (head : ∃ tail,
      template = .expression (.symbol headName :: tail))
    (different : headName ≠ "mm-compressed-heap-lookup") :
    instantiateTemplateAtom? substitution template ≠ some directLookupOne := by
  obtain ⟨tail, rfl⟩ := head
  unfold directLookupOne
  apply instantiateTemplateAtom?_expression_symbol_head_ne
  exact different

theorem direct_next_machine_ne_old_for_full_rows :
    ∀ substitution ∈ directHitFullRows,
      instantiateTemplateAtom? substitution directNextMachineTemplate ≠
        some machineWithTwoHeapEntries := by
  decide +kernel

theorem direct_hit_leaves_no_pending_step :
    directStepPending ∉ speculativeHitAfterDirect := by
  rcases direct_hit_full_instantiates_frame with
    ⟨substitution, rowMember, pending, _lookup, _machine, _nextMachine,
      _stack, _normalStack, _scan⟩
  unfold speculativeHitAfterDirect cFireReflectiveSourceExecFact
    cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    directHitFullRows
    (speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom)
    [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
     .add (.var "compressed-terminal-rule"),
     .add (.var "compressed-invalid-byte-rule"),
     .add (.var "compressed-question-rule"),
     .add (.var "compressed-question-open-fault-rule")]
    directPendingTemplate directStepPending
    [.remove directLookupTemplate, .remove directMachineTemplate,
     .add directNextMachineTemplate, .add directStackCellTemplate,
     .add directNormalStackCellTemplate, .add directResumedScanTemplate]
    substitution rowMember pending
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨directLookupTemplate, rfl⟩
  · exact Or.inl ⟨directMachineTemplate, rfl⟩
  · exact Or.inr ⟨directNextMachineTemplate, rfl, fun s _ =>
      direct_output_ne_pending s directNextMachineTemplate _ ⟨_, rfl⟩ (by decide)⟩
  · exact Or.inr ⟨directStackCellTemplate, rfl, fun s _ =>
      direct_output_ne_pending s directStackCellTemplate _ ⟨_, rfl⟩ (by decide)⟩
  · exact Or.inr ⟨directNormalStackCellTemplate, rfl, fun s _ =>
      direct_output_ne_pending s directNormalStackCellTemplate _ ⟨_, rfl⟩ (by decide)⟩
  · exact Or.inr ⟨directResumedScanTemplate, rfl, fun s _ =>
      direct_output_ne_pending s directResumedScanTemplate _ ⟨_, rfl⟩ (by decide)⟩

theorem direct_hit_leaves_no_lookup_request :
    directLookupOne ∉ speculativeHitAfterDirect := by
  rcases direct_hit_full_instantiates_frame with
    ⟨substitution, rowMember, _pending, lookup, _machine, _nextMachine,
      _stack, _normalStack, _scan⟩
  unfold speculativeHitAfterDirect cFireReflectiveSourceExecFact
    cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    directHitFullRows
    (speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom)
    [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
     .add (.var "compressed-terminal-rule"),
     .add (.var "compressed-invalid-byte-rule"),
     .add (.var "compressed-question-rule"),
     .add (.var "compressed-question-open-fault-rule"),
     .remove directPendingTemplate]
    directLookupTemplate directLookupOne
    [.remove directMachineTemplate, .add directNextMachineTemplate,
     .add directStackCellTemplate, .add directNormalStackCellTemplate,
     .add directResumedScanTemplate]
    substitution rowMember lookup
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨directMachineTemplate, rfl⟩
  · exact Or.inr ⟨directNextMachineTemplate, rfl, fun s _ =>
      direct_output_ne_lookup s directNextMachineTemplate _ ⟨_, rfl⟩ (by decide)⟩
  · exact Or.inr ⟨directStackCellTemplate, rfl, fun s _ =>
      direct_output_ne_lookup s directStackCellTemplate _ ⟨_, rfl⟩ (by decide)⟩
  · exact Or.inr ⟨directNormalStackCellTemplate, rfl, fun s _ =>
      direct_output_ne_lookup s directNormalStackCellTemplate _ ⟨_, rfl⟩ (by decide)⟩
  · exact Or.inr ⟨directResumedScanTemplate, rfl, fun s _ =>
      direct_output_ne_lookup s directResumedScanTemplate _ ⟨_, rfl⟩ (by decide)⟩

theorem direct_hit_consumes_old_machine :
    machineWithTwoHeapEntries ∉ speculativeHitAfterDirect := by
  rcases direct_hit_full_instantiates_frame with
    ⟨substitution, rowMember, _pending, _lookup, machine, _nextMachine,
      _stack, _normalStack, _scan⟩
  unfold speculativeHitAfterDirect cFireReflectiveSourceExecFact
    cApplyReflectiveTemplate
  rw [speculative_direct_proof_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    directHitFullRows
    (speculativeHitAfterTerminal.erase speculativeDirectProofDirective.atom)
    [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
     .add (.var "compressed-terminal-rule"),
     .add (.var "compressed-invalid-byte-rule"),
     .add (.var "compressed-question-rule"),
     .add (.var "compressed-question-open-fault-rule"),
     .remove directPendingTemplate, .remove directLookupTemplate]
    directMachineTemplate machineWithTwoHeapEntries
    [.add directNextMachineTemplate, .add directStackCellTemplate,
     .add directNormalStackCellTemplate, .add directResumedScanTemplate]
    substitution rowMember machine
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact Or.inr ⟨directNextMachineTemplate, rfl,
      direct_next_machine_ne_old_for_full_rows⟩
  · exact Or.inr ⟨directStackCellTemplate, rfl, fun s _ => by
      unfold directStackCellTemplate machineWithTwoHeapEntries
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directNormalStackCellTemplate, rfl, fun s _ => by
      unfold directNormalStackCellTemplate machineWithTwoHeapEntries
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directResumedScanTemplate, rfl, fun s _ => by
      unfold directResumedScanTemplate machineWithTwoHeapEntries
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩

#print axioms direct_next_machine_ne_old_for_full_rows
#print axioms direct_hit_leaves_no_pending_step
#print axioms direct_hit_leaves_no_lookup_request
#print axioms direct_hit_consumes_old_machine

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitAbsentCanary
