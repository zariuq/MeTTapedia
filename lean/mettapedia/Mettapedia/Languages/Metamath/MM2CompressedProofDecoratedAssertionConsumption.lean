import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionBridgeOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionRejoinOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSinkBatchRemoval

/-!
# Exact consumption by the decorated assertion launcher

The compiler-derived launcher consumes the pending compact step, heap lookup,
and old machine row.  Its two opaque add sinks are proved source-capability
exact before they are excluded from recreating those controls.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionConsumption

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionBridgeOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionRejoinOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
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

private theorem pendingRow_ne_bridgeRule
    (context : DirectAssertionContext) :
    context.pendingRow ≠ compressedNormalDispatchBridgeRule := by
  simp [DirectAssertionContext.pendingRow, compressedNormalDispatchBridgeRule]

private theorem lookupRow_ne_bridgeRule
    (context : DirectAssertionContext) :
    context.lookupRow ≠ compressedNormalDispatchBridgeRule := by
  simp [DirectAssertionContext.lookupRow, compressedNormalDispatchBridgeRule]

private theorem machineRow_ne_bridgeRule
    (context : DirectAssertionContext) :
    context.machineRow ≠ compressedNormalDispatchBridgeRule := by
  simp [DirectAssertionContext.machineRow, compressedNormalDispatchBridgeRule]

private theorem rejoin_sink_ne
    (candidate : Atom) (candidateNe : candidate ≠ compressedAssertionRejoinRule)
    {space : List Atom}
    (capabilities : AssertionRejoinCapabilities compressedAssertionRejoinRule
      space)
    (substitution : Subst)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.input).map Prod.fst) :
    instantiateTemplateAtom? substitution
      (.var "compressed-assertion-rejoin-rule") ≠ some candidate := by
  intro instantiates
  exact candidateNe
    (decoratedAssertionMatcherRow_rejoin_exact capabilities rowMember
      instantiates)

private theorem bridge_sink_ne
    (candidate : Atom)
    (candidateNe : candidate ≠ compressedNormalDispatchBridgeRule)
    {space : List Atom}
    (capabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space)
    (substitution : Subst)
    (rowMember : substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.input).map Prod.fst) :
    instantiateTemplateAtom? substitution (.var "normal-bridge-rule") ≠
      some candidate := by
  intro instantiates
  exact candidateNe
    (decoratedAssertionMatcherRow_bridge_exact capabilities rowMember
      instantiates)

theorem decorated_direct_assertion_fire_consumes_pending
    (context : DirectAssertionContext) (space : List Atom)
    (rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    (bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    context.pendingRow ∉
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, pending, _lookup, _machine,
      _contextRow, _normalControl, _normalLabel, _reload, _rejoin, _bridge⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [decoratedDirectAssertionDirective_sinks_exact]
  unfold decoratedDirectAssertionSinks directAssertionSinks
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    _ _ [] directAssertionPendingTemplate context.pendingRow
    [.remove directAssertionLookupTemplate,
     .remove directAssertionMachineTemplate,
     .add directAssertionContextTemplate,
     .add directAssertionNormalControlTemplate,
     .add directAssertionNormalLabelTemplate,
     .add directAssertionReloadTemplate,
     .add (.var "compressed-assertion-rejoin-rule"),
     .add (.var "normal-bridge-rule")]
    substitution rowMember pending
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      unfold directAssertionNormalLabelTemplate DirectAssertionContext.pendingRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionReloadTemplate, rfl, fun later _ => by
      unfold directAssertionReloadTemplate DirectAssertionContext.pendingRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨.var "compressed-assertion-rejoin-rule", rfl,
      rejoin_sink_ne context.pendingRow (pendingRow_ne_rejoinRule context)
        rejoinCapabilities⟩
  · exact Or.inr ⟨.var "normal-bridge-rule", rfl,
      bridge_sink_ne context.pendingRow (pendingRow_ne_bridgeRule context)
        bridgeCapabilities⟩

theorem decorated_direct_assertion_fire_consumes_lookup
    (context : DirectAssertionContext) (space : List Atom)
    (rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    (bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    context.lookupRow ∉
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _pending, lookup, _machine,
      _contextRow, _normalControl, _normalLabel, _reload, _rejoin, _bridge⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [decoratedDirectAssertionDirective_sinks_exact]
  unfold decoratedDirectAssertionSinks directAssertionSinks
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    _ _ [.remove directAssertionPendingTemplate]
    directAssertionLookupTemplate context.lookupRow
    [.remove directAssertionMachineTemplate,
     .add directAssertionContextTemplate,
     .add directAssertionNormalControlTemplate,
     .add directAssertionNormalLabelTemplate,
     .add directAssertionReloadTemplate,
     .add (.var "compressed-assertion-rejoin-rule"),
     .add (.var "normal-bridge-rule")]
    substitution rowMember lookup
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨directAssertionMachineTemplate, rfl⟩
  · exact Or.inr ⟨directAssertionContextTemplate, rfl, fun later _ => by
      unfold directAssertionContextTemplate DirectAssertionContext.lookupRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalControlTemplate, rfl, fun later _ => by
      unfold directAssertionNormalControlTemplate DirectAssertionContext.lookupRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalLabelTemplate, rfl, fun later _ => by
      unfold directAssertionNormalLabelTemplate DirectAssertionContext.lookupRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionReloadTemplate, rfl, fun later _ => by
      unfold directAssertionReloadTemplate DirectAssertionContext.lookupRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨.var "compressed-assertion-rejoin-rule", rfl,
      rejoin_sink_ne context.lookupRow (lookupRow_ne_rejoinRule context)
        rejoinCapabilities⟩
  · exact Or.inr ⟨.var "normal-bridge-rule", rfl,
      bridge_sink_ne context.lookupRow (lookupRow_ne_bridgeRule context)
        bridgeCapabilities⟩

theorem decorated_direct_assertion_fire_consumes_machine
    (context : DirectAssertionContext) (space : List Atom)
    (rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    (bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    context.machineRow ∉
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _pending, _lookup, machine,
      _contextRow, _normalControl, _normalLabel, _reload, _rejoin, _bridge⟩
  unfold cFireReflectiveSourceExecFact cApplyReflectiveTemplate
  rw [decoratedDirectAssertionDirective_sinks_exact]
  unfold decoratedDirectAssertionSinks directAssertionSinks
  apply not_mem_cApplyReflectiveSinkBatch_append_remove_cons_of_row
    _ _ [.remove directAssertionPendingTemplate,
      .remove directAssertionLookupTemplate]
    directAssertionMachineTemplate context.machineRow
    [.add directAssertionContextTemplate,
     .add directAssertionNormalControlTemplate,
     .add directAssertionNormalLabelTemplate,
     .add directAssertionReloadTemplate,
     .add (.var "compressed-assertion-rejoin-rule"),
     .add (.var "normal-bridge-rule")]
    substitution rowMember machine
  intro sink member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨directAssertionContextTemplate, rfl, fun later _ => by
      unfold directAssertionContextTemplate DirectAssertionContext.machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalControlTemplate, rfl, fun later _ => by
      unfold directAssertionNormalControlTemplate DirectAssertionContext.machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionNormalLabelTemplate, rfl, fun later _ => by
      unfold directAssertionNormalLabelTemplate DirectAssertionContext.machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨directAssertionReloadTemplate, rfl, fun later _ => by
      unfold directAssertionReloadTemplate DirectAssertionContext.machineRow
      apply instantiateTemplateAtom?_expression_symbol_head_ne
      decide⟩
  · exact Or.inr ⟨.var "compressed-assertion-rejoin-rule", rfl,
      rejoin_sink_ne context.machineRow (machineRow_ne_rejoinRule context)
        rejoinCapabilities⟩
  · exact Or.inr ⟨.var "normal-bridge-rule", rfl,
      bridge_sink_ne context.machineRow (machineRow_ne_bridgeRule context)
        bridgeCapabilities⟩

#print axioms decorated_direct_assertion_fire_consumes_pending
#print axioms decorated_direct_assertion_fire_consumes_lookup
#print axioms decorated_direct_assertion_fire_consumes_machine

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionConsumption
