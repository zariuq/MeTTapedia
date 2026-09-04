import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionCapabilityOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

/-!
# Exact consumption at the compressed assertion launch

The launch removes the pending proof step, heap lookup, and old compressed
machine row.  The only opaque add sink republishes the assertion-rejoin rule;
its exact value follows from executable capability origin, so it cannot
recreate any consumed control.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchConsumption

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeCapabilityOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

private theorem pendingRow_ne_rejoinRule
    (context : DirectAssertionContext) :
    context.pendingRow ≠ compressedAssertionRejoinRule := by
  simp [DirectAssertionContext.pendingRow, compressedAssertionRejoinRule]

private theorem lookupRow_ne_rejoinRule
    (context : DirectAssertionContext) :
    context.lookupRow ≠ compressedAssertionRejoinRule := by
  simp [DirectAssertionContext.lookupRow, compressedAssertionRejoinRule]

private theorem machineRow_ne_rejoinRule
    (context : DirectAssertionContext) :
    context.machineRow ≠ compressedAssertionRejoinRule := by
  simp [DirectAssertionContext.machineRow, compressedAssertionRejoinRule]

private theorem rejoin_sink_ne_pending
    (context : DirectAssertionContext) {space : List Atom}
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation space)
    (substitution : Subst)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          space.erase speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input).map Prod.fst) :
    instantiateTemplateAtom? substitution
      (.var "compressed-assertion-rejoin-rule") ≠
        some context.pendingRow := by
  intro instantiates
  exact pendingRow_ne_rejoinRule context
    (directAssertionMatcherRow_rejoin_exact capabilities rowMember instantiates)

private theorem rejoin_sink_ne_lookup
    (context : DirectAssertionContext) {space : List Atom}
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation space)
    (substitution : Subst)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          space.erase speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input).map Prod.fst) :
    instantiateTemplateAtom? substitution
      (.var "compressed-assertion-rejoin-rule") ≠
        some context.lookupRow := by
  intro instantiates
  exact lookupRow_ne_rejoinRule context
    (directAssertionMatcherRow_rejoin_exact capabilities rowMember instantiates)

private theorem rejoin_sink_ne_machine
    (context : DirectAssertionContext) {space : List Atom}
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation space)
    (substitution : Subst)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (speculativeDirectAssertionDirective.atom ::
          space.erase speculativeDirectAssertionDirective.atom)
        speculativeDirectAssertionDirective.rule.input).map Prod.fst) :
    instantiateTemplateAtom? substitution
      (.var "compressed-assertion-rejoin-rule") ≠
        some context.machineRow := by
  intro instantiates
  exact machineRow_ne_rejoinRule context
    (directAssertionMatcherRow_rejoin_exact capabilities rowMember instantiates)

/-- The pending proof-step request is consumed and cannot be recreated by the
opaque rejoin sink. -/
theorem direct_assertion_fire_consumes_pending
    (context : DirectAssertionContext) (space : List Atom)
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation space)
    (matched : ExactDirectAssertionLaunch context space) :
    context.pendingRow ∉
      cFireReflectiveSourceExecFact space
        speculativeDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, pending, _lookup, _machine,
      _contextRow, _normalControl, _normalLabel, _reload, _rejoinRule⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_direct_assertion_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    _ _ [] directAssertionPendingTemplate context.pendingRow
    [.remove directAssertionLookupTemplate,
     .remove directAssertionMachineTemplate,
     .add directAssertionContextTemplate,
     .add directAssertionNormalControlTemplate,
     .add directAssertionNormalLabelTemplate,
     .add directAssertionReloadTemplate,
     .add (.var "compressed-assertion-rejoin-rule")]
    substitution rowMember pending
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨directAssertionLookupTemplate, rfl⟩
  · exact Or.inl ⟨directAssertionMachineTemplate, rfl⟩
  · exact Or.inr ⟨directAssertionContextTemplate, rfl, fun later _ => by
      unfold directAssertionContextTemplate DirectAssertionContext.pendingRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalControlTemplate, rfl, fun later _ => by
      unfold directAssertionNormalControlTemplate
        DirectAssertionContext.pendingRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalLabelTemplate, rfl, fun later _ => by
      unfold directAssertionNormalLabelTemplate
        DirectAssertionContext.pendingRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionReloadTemplate, rfl, fun later _ => by
      unfold directAssertionReloadTemplate DirectAssertionContext.pendingRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨.var "compressed-assertion-rejoin-rule", rfl,
      rejoin_sink_ne_pending context capabilities⟩

/-- The speculative heap-lookup cursor is consumed at the same atomic launch
boundary. -/
theorem direct_assertion_fire_consumes_lookup
    (context : DirectAssertionContext) (space : List Atom)
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation space)
    (matched : ExactDirectAssertionLaunch context space) :
    context.lookupRow ∉
      cFireReflectiveSourceExecFact space
        speculativeDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _pending, lookup, _machine,
      _contextRow, _normalControl, _normalLabel, _reload, _rejoinRule⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_direct_assertion_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    _ _ [.remove directAssertionPendingTemplate]
    directAssertionLookupTemplate context.lookupRow
    [.remove directAssertionMachineTemplate,
     .add directAssertionContextTemplate,
     .add directAssertionNormalControlTemplate,
     .add directAssertionNormalLabelTemplate,
     .add directAssertionReloadTemplate,
     .add (.var "compressed-assertion-rejoin-rule")]
    substitution rowMember lookup
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨directAssertionMachineTemplate, rfl⟩
  · exact Or.inr ⟨directAssertionContextTemplate, rfl, fun later _ => by
      unfold directAssertionContextTemplate DirectAssertionContext.lookupRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalControlTemplate, rfl, fun later _ => by
      unfold directAssertionNormalControlTemplate
        DirectAssertionContext.lookupRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalLabelTemplate, rfl, fun later _ => by
      unfold directAssertionNormalLabelTemplate
        DirectAssertionContext.lookupRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionReloadTemplate, rfl, fun later _ => by
      unfold directAssertionReloadTemplate DirectAssertionContext.lookupRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨.var "compressed-assertion-rejoin-rule", rfl,
      rejoin_sink_ne_lookup context capabilities⟩

/-- The old compressed machine row is consumed before normal assertion
verification begins. -/
theorem direct_assertion_fire_consumes_machine
    (context : DirectAssertionContext) (space : List Atom)
    (capabilities : CompressedExecutableCapabilities
      speculativeBaseExecutablePresentation space)
    (matched : ExactDirectAssertionLaunch context space) :
    context.machineRow ∉
      cFireReflectiveSourceExecFact space
        speculativeDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _pending, _lookup, machine,
      _contextRow, _normalControl, _normalLabel, _reload, _rejoinRule⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [speculative_direct_assertion_sinks_exact]
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    _ _ [.remove directAssertionPendingTemplate,
      .remove directAssertionLookupTemplate]
    directAssertionMachineTemplate context.machineRow
    [.add directAssertionContextTemplate,
     .add directAssertionNormalControlTemplate,
     .add directAssertionNormalLabelTemplate,
     .add directAssertionReloadTemplate,
     .add (.var "compressed-assertion-rejoin-rule")]
    substitution rowMember machine
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨directAssertionContextTemplate, rfl, fun later _ => by
      unfold directAssertionContextTemplate DirectAssertionContext.machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalControlTemplate, rfl, fun later _ => by
      unfold directAssertionNormalControlTemplate
        DirectAssertionContext.machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalLabelTemplate, rfl, fun later _ => by
      unfold directAssertionNormalLabelTemplate
        DirectAssertionContext.machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionReloadTemplate, rfl, fun later _ => by
      unfold directAssertionReloadTemplate DirectAssertionContext.machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨.var "compressed-assertion-rejoin-rule", rfl,
      rejoin_sink_ne_machine context capabilities⟩

#print axioms direct_assertion_fire_consumes_pending
#print axioms direct_assertion_fire_consumes_lookup
#print axioms direct_assertion_fire_consumes_machine

end Mettapedia.Languages.Metamath.MM2CompressedProofAssertionLaunchConsumption
