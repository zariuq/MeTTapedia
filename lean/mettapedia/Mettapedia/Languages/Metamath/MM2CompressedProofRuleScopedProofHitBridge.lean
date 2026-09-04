import Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerCanonicalHitBridge
import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSemanticBridge
import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution

/-!
# Rule-scoped MORK bridge for a compressed proof hit

The earlier compressed proof-hit square used the reflective list executor.
This module executes the same generated terminal and direct-hit rules with the
rule-scoped MORK realization used by the assembled verifier.  Exact agreement
receipts connect the already-proved semantic representation to that stricter
execution path.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofRuleScopedProofHitBridge

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerCanonicalHitBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSemanticBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- The actual physical-key, guard-checking successor of the generated
terminal rule. -/
def ruleScopedHitAfterTerminal : List Atom :=
  cFireRuleScopedSourceExecFact speculativeHitProgram
    speculativeTerminalDirective

/-- The actual physical-key, rule-scoped successor of the direct proof rule. -/
def ruleScopedHitAfterDirect : List Atom :=
  cFireRuleScopedSourceExecFact ruleScopedHitAfterTerminal
    speculativeDirectProofDirective

/-- On the admitted proof-hit fixture, the stricter terminal firing has the
same exact atom presentation as the earlier reflective calculation. -/
theorem ruleScoped_terminal_agrees_exactly :
    ruleScopedHitAfterTerminal = speculativeHitAfterTerminal := by
  decide +kernel

/-- On the admitted proof-hit fixture, rule-scoped coverage, guard filtering,
and physical support identity preserve the exact direct-hit successor. -/
theorem ruleScoped_direct_agrees_exactly :
    ruleScopedHitAfterDirect = speculativeHitAfterDirect := by
  decide +kernel

theorem ruleScoped_terminal_selected :
    cRuleScopedSourceWorkQueueStep .leaveInert speculativeHitProgram =
      some ruleScopedHitAfterTerminal := by
  decide +kernel

theorem ruleScoped_direct_selected :
    cRuleScopedSourceWorkQueueStep .leaveInert ruleScopedHitAfterTerminal =
      some ruleScopedHitAfterDirect := by
  decide +kernel

/-- The exact proof occurrence selected by the semantic heap is represented
after the actual rule-scoped MORK transition. -/
theorem semantic_after_is_ruleScoped_represented :
    RepresentsProofHit proofOwner 0 semanticAfter ruleScopedHitAfterDirect := by
  rw [ruleScoped_direct_agrees_exactly]
  exact semantic_after_is_represented

/-- The generated terminal and direct proof handlers form two actual
rule-scoped MORK steps, and the second step inhabits its OSLF native type. -/
structure RuleScopedProofHitCommutingInstance : Prop where
  semanticStep :
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step
      semanticBefore semanticAfter
  terminalStep :
    cRuleScopedSourceWorkQueueStep .leaveInert speculativeHitProgram =
      some ruleScopedHitAfterTerminal
  directStep :
    cRuleScopedSourceWorkQueueStep .leaveInert ruleScopedHitAfterTerminal =
      some ruleScopedHitAfterDirect
  directNativeType :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (ruleScopedNativeListExecGSLT .leaveInert)).satisfies
        ruleScopedHitAfterTerminal
        (ruleScopedNativeListExactTargetNativeType .leaveInert
          ruleScopedHitAfterDirect).pred
  outputRepresentation :
    RepresentsProofHit proofOwner 0 semanticAfter ruleScopedHitAfterDirect

theorem generated_ruleScoped_proof_hit_commutes :
    RuleScopedProofHitCommutingInstance where
  semanticStep := semantic_direct_hit
  terminalStep := ruleScoped_terminal_selected
  directStep := ruleScoped_direct_selected
  directNativeType :=
    (satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
      .leaveInert ruleScopedHitAfterTerminal ruleScopedHitAfterDirect).2
      ruleScoped_direct_selected
  outputRepresentation := semantic_after_is_ruleScoped_represented

/-! ## Arbitrary canonical proof-hit scheduling -/

/-- Every canonical proof-hit space selects the direct proof handler under the
actual rule-scoped MORK scheduler.  This theorem deliberately states
scheduling rather than output equality: output fidelity additionally requires
physical compact-key faithfulness for the source-derived ground rows. -/
theorem canonical_ruleScoped_direct_selected
    (context : DirectProofContext) (item : ProofOccurrence) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (canonicalDirectProofSpace context item) =
      some (cFireRuleScopedSourceExecFact
        (canonicalDirectProofSpace context item)
        speculativeDirectProofDirective) := by
  unfold cRuleScopedSourceWorkQueueStep
  rw [select_direct_proof_of_supported_exact
    (canonical_direct_proof_supported_exact context item)]

/-- An arbitrary source-derived semantic proof hit and its canonical target
space share one scheduled boundary under the actual rule-scoped MORK relation.
The exact target is also witnessed by its generated OSLF native type. -/
structure RuleScopedDirectProofScheduledSquare {Other : Type}
    (context : DirectProofContext) (item : ProofOccurrence)
    (before : SemanticState Other) : Prop where
  semanticStep :
    Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step before
      (semanticHitAfter context item before)
  concreteStep :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (canonicalDirectProofSpace context item) =
      some (cFireRuleScopedSourceExecFact
        (canonicalDirectProofSpace context item)
        speculativeDirectProofDirective)
  targetNativeType :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (ruleScopedNativeListExecGSLT .leaveInert)).satisfies
        (canonicalDirectProofSpace context item)
        (ruleScopedNativeListExactTargetNativeType .leaveInert
          (cFireRuleScopedSourceExecFact
            (canonicalDirectProofSpace context item)
            speculativeDirectProofDirective)).pred

theorem canonical_ruleScoped_direct_scheduled
    {Other : Type} (context : DirectProofContext) (item : ProofOccurrence)
    (before : SemanticState Other)
    (control : before.control =
      Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Control.request context.index)
    (found : before.heap[context.index]? = some (.occurrence item)) :
    RuleScopedDirectProofScheduledSquare context item before := by
  let reflective :=
    canonical_direct_proof_hit_commutes context item before control found
  refine ⟨reflective.semanticStep,
    canonical_ruleScoped_direct_selected context item, ?_⟩
  exact
    (satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
      .leaveInert (canonicalDirectProofSpace context item)
        (cFireRuleScopedSourceExecFact
          (canonicalDirectProofSpace context item)
          speculativeDirectProofDirective)).2
      (canonical_ruleScoped_direct_selected context item)

/-- Replace the earlier reflective scheduling witness by the actual
rule-scoped MORK scheduler without changing the source semantic step. -/
theorem ruleScoped_direct_scheduled_of_reflective
    {Other : Type} (context : DirectProofContext) (item : ProofOccurrence)
    (before : SemanticState Other)
    (reflective : DirectProofHitCommutingSquare context item before
      (canonicalDirectProofSpace context item)) :
    RuleScopedDirectProofScheduledSquare context item before := by
  refine ⟨reflective.semanticStep,
    canonical_ruleScoped_direct_selected context item, ?_⟩
  exact
    (satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
      .leaveInert (canonicalDirectProofSpace context item)
        (cFireRuleScopedSourceExecFact
          (canonicalDirectProofSpace context item)
          speculativeDirectProofDirective)).2
      (canonical_ruleScoped_direct_selected context item)

/-- Every proof entry produced by an arbitrary verified compressed-action
execution reconstructs its occurrence from the execution ledger and schedules
the corresponding canonical direct hit under the actual rule-scoped MORK
relation. -/
theorem execute_derived_proof_lookup_ruleScoped_scheduled
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    {before after : MachineState source target}
    {actions : List CompressedAction}
    (execution : Execute before actions after)
    (proofPosition : Nat) (initialLedger : NodeOccurrenceLedger before)
    (context : DirectProofContext)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : after.heap[index]? = some (.proof nodeId))
    (nodeLookup : after.nodes[nodeId]? = some node) :
    let ledger := Execute.occurrenceLedger execution proofPosition initialLedger
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      RuleScopedDirectProofScheduledSquare
        (directProofContextAtMachine context after index) item
        (displayedProofRequestState after ledger index) := by
  dsimp only
  obtain ⟨sourceOccurrence, occurrenceLookup, reflective⟩ :=
    execute_derived_proof_lookup_commutes execution proofPosition initialLedger
      context index nodeId node heapLookup nodeLookup
  exact ⟨sourceOccurrence, occurrenceLookup,
    ruleScoped_direct_scheduled_of_reflective _ _ _ reflective⟩

/-- The `.proof` constructor of the compressed source machine and the actual
rule-scoped MORK direct-hit scheduler advance the same source-derived
occurrence and stack frontier. -/
theorem source_proof_action_ruleScoped_scheduled
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (before : MachineState source target)
    (ledger : NodeOccurrenceLedger before) (proofPosition : Nat)
    (context : DirectProofContext)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : before.heap[index]? = some (.proof nodeId))
    (nodeLookup : before.nodes[nodeId]? = some node) :
    let after : MachineState source target :=
      { before with stack := before.stack ++ [nodeId] }
    ∃ sourceStep : ActionStep before (.step index) after,
      (ActionStep.occurrenceLedger sourceStep proofPosition ledger).occurrences =
          ledger.occurrences ∧
        (directProofContextAtMachine context before index).nextStackPosition =
          after.stack.length ∧
        ∃ sourceOccurrence,
          ledger.occurrences[nodeId]? = some sourceOccurrence ∧
          let item := displayedProofOccurrence nodeId node sourceOccurrence
          RuleScopedDirectProofScheduledSquare
            (directProofContextAtMachine context before index) item
            (displayedProofRequestState before ledger index) := by
  obtain ⟨sourceStep, ledgerStable, frontierExact, sourceOccurrence,
      occurrenceLookup, reflective⟩ :=
    source_proof_action_commutes before ledger proofPosition context index nodeId
      node heapLookup nodeLookup
  exact ⟨sourceStep, ledgerStable, frontierExact, sourceOccurrence,
    occurrenceLookup,
    ruleScoped_direct_scheduled_of_reflective _ _ _ reflective⟩

/-- Complete compressed-theorem specialization of the actual rule-scoped
MORK scheduling boundary.  Occurrence identity is generated by the admitted
header/action derivation rather than accepted as a target-side witness. -/
theorem compressed_theorem_final_proof_lookup_ruleScoped_scheduled
    {before after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    {explicitHeaderLabels : List String}
    {bodyWords : List (List UInt8)}
    (step : CompressedTheoremStep before after label formula
      explicitHeaderLabels bodyWords)
    (context : DirectProofContext)
    (index nodeId : Nat) (node : ProofNode before.toSourcePrefix step.target)
    (heapLookup : step.finalState.heap[index]? = some (.proof nodeId))
    (nodeLookup : step.finalState.nodes[nodeId]? = some node) :
    let ledger := CompressedTheoremStep.occurrenceLedger step context.proofOwner
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      RuleScopedDirectProofScheduledSquare
        (directProofContextAtMachine context step.finalState index) item
        (displayedProofRequestState step.finalState ledger index) := by
  exact execute_derived_proof_lookup_ruleScoped_scheduled step.execution 0
    (HeaderBuild.occurrenceLedger step.header context.proofOwner 0
      (NodeOccurrenceLedger.empty before.toSourcePrefix step.target))
    context index nodeId node heapLookup nodeLookup

#print axioms ruleScoped_terminal_agrees_exactly
#print axioms ruleScoped_direct_agrees_exactly
#print axioms ruleScoped_terminal_selected
#print axioms ruleScoped_direct_selected
#print axioms semantic_after_is_ruleScoped_represented
#print axioms generated_ruleScoped_proof_hit_commutes
#print axioms canonical_ruleScoped_direct_selected
#print axioms canonical_ruleScoped_direct_scheduled
#print axioms ruleScoped_direct_scheduled_of_reflective
#print axioms execute_derived_proof_lookup_ruleScoped_scheduled
#print axioms source_proof_action_ruleScoped_scheduled
#print axioms compressed_theorem_final_proof_lookup_ruleScoped_scheduled

end Mettapedia.Languages.Metamath.MM2CompressedProofRuleScopedProofHitBridge
