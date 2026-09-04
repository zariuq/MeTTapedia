import Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalSupportHeadFaithfulness

/-!
# Physical direct proof-hit execution

This module connects the source-derived direct proof request to the actual
rule-scoped MORK matcher.  The physical matcher uses compact support identity,
so its read presentation is only a permutation of the reflective read.  The
lemmas below transport exact matcher witnesses across that permutation before
reasoning about the complete sink batch.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDirectHit

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.OccurrenceHeapProtocol
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofHeapEncoding
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedgerBridge
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeDirectProofScheduling
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitInputData
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupHitSinkCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitAbstractFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHitCanonicalFrame
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- Matcher substitutions used by the actual compact-key direct proof firing. -/
def physicalDirectProofMatcherRows (space : List Atom) : List Subst :=
  let live := morkEraseSupport space speculativeDirectProofDirective.atom
  let read := morkInsertSupport live speculativeDirectProofDirective.atom
  ((cMatchInputSpecMork [] read speculativeDirectProofDirective.rule.input).filter
      fun (substitution, _) =>
        matchSourceGuards substitution speculativeDirectProofDirective.rule.guards).map
    Prod.fst

/-- Every direct proof output variable is inherited from its compatible input. -/
theorem speculativeDirectProofDirective_sinks_variablesInherited :
    ruleSinksVariablesInherited speculativeDirectProofDirective.rule.input
      speculativeDirectProofDirective.rule.tmpl.sinks = true := by
  decide +kernel

/-- The direct proof handler uses only support-valued add and remove sinks.
Its physical result can therefore be classified without imposing an order on
the matcher enumeration. -/
theorem speculativeDirectProofDirective_supportSet :
    ReflectiveSupportSetTemplate speculativeDirectProofDirective.rule.tmpl := by
  intro sink sinkMember
  rw [speculative_direct_proof_sinks_exact] at sinkMember
  simp only [directProofSinks, List.mem_cons, List.not_mem_nil, or_false]
    at sinkMember
  rcases sinkMember with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals (subst sink; trivial)

/-- Compact-key removal is ordinary single-row erasure when the request has
both nominal and physical duplicate freedom. -/
theorem physical_direct_live_eq
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space) :
    morkEraseSupport space speculativeDirectProofDirective.atom =
      space.erase speculativeDirectProofDirective.atom := by
  exact morkEraseSupport_eq_erase_of_mem space
    speculativeDirectProofDirective.atom listNodup morkNodup directivePresent

/-- The compact-key and ordinary direct-proof reads differ only by order. -/
theorem physical_direct_read_perm
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space) :
    (morkInsertSupport
        (morkEraseSupport space speculativeDirectProofDirective.atom)
        speculativeDirectProofDirective.atom).Perm
      (speculativeDirectProofDirective.atom :: directProofLive space) := by
  rw [physical_direct_live_eq listNodup morkNodup directivePresent]
  have absent : morkSupportContains
      (space.erase speculativeDirectProofDirective.atom)
        speculativeDirectProofDirective.atom = false := by
    rw [← physical_direct_live_eq listNodup morkNodup directivePresent]
    exact morkSupportContains_morkEraseSupport_self space
      speculativeDirectProofDirective.atom
  unfold morkInsertSupport directProofLive
  rw [absent]
  exact List.perm_append_singleton speculativeDirectProofDirective.atom
    (space.erase speculativeDirectProofDirective.atom)

/-- Compatible matching is invariant between the two physical presentations
of the same direct-proof read. -/
theorem physical_direct_matcher_mem_iff
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space)
    (substitution : Subst) (consumed : List Atom) :
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space speculativeDirectProofDirective.atom)
            speculativeDirectProofDirective.atom)
          speculativeDirectProofDirective.rule.input ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (speculativeDirectProofDirective.atom :: directProofLive space)
          speculativeDirectProofDirective.rule.input := by
  rw [speculative_direct_proof_input_exact]
  unfold cMatchInputSpecMork Conformance.Computable.cmatchInputSpec
  have readPerm := physical_direct_read_perm listNodup morkNodup directivePresent
  constructor
  · intro member
    exact Conformance.Computable.cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mp atomMember)
      substitution consumed member
  · intro member
    exact Conformance.Computable.cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mpr atomMember)
      substitution consumed member

/-- Every physical matcher substitution is also an ordinary direct matcher
substitution over the same source-derived request. -/
theorem physicalDirectProofMatcherRows_subset_directProofMatcherRows
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space)
    {substitution : Subst}
    (member : substitution ∈ physicalDirectProofMatcherRows space) :
    substitution ∈ directProofMatcherRows space := by
  unfold physicalDirectProofMatcherRows at member
  rw [List.mem_map] at member
  obtain ⟨⟨matchedSubstitution, consumed⟩, filtered, equal⟩ := member
  have matched := (List.mem_filter.mp filtered).1
  have reflected := (physical_direct_matcher_mem_iff listNodup morkNodup
    directivePresent matchedSubstitution consumed).1 matched
  subst substitution
  exact List.mem_map_of_mem reflected

/-- Exact source-derived observations reconstructed by the matcher used by
the actual rule-scoped direct proof firing. -/
def PhysicalExactDirectProofMatch
    (context : DirectProofContext) (item : ProofOccurrence)
    (space : List Atom) : Prop :=
  ∃ substitution ∈ physicalDirectProofMatcherRows space,
    instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directPendingTemplate =
        some context.pendingRow ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directLookupTemplate =
        some context.lookupRow ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directMachineTemplate =
        some context.machineRow ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directNextMachineTemplate =
        some context.nextMachineRow ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directStackCellTemplate =
        some (compressedStackRow context.proofOwner
          context.stackPosition item) ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directNormalStackCellTemplate =
        some (normalStackRow context.proofOwner context.stackPosition item) ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directResumedScanTemplate =
        some context.resumedScanRow

/-- Every physical direct matcher row reconstructs the same source-derived
dynamic outputs.  This is stronger than existence of one correct witness and
is the exact premise needed to exclude a second match recreating a consumed
control row. -/
def PhysicalDirectProofMatcherExact
    (context : DirectProofContext) (item : ProofOccurrence)
    (space : List Atom) : Prop :=
  ∀ substitution ∈ physicalDirectProofMatcherRows space,
    instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directNextMachineTemplate =
        some context.nextMachineRow ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directStackCellTemplate =
        some (compressedStackRow context.proofOwner
          context.stackPosition item) ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directNormalStackCellTemplate =
        some (normalStackRow context.proofOwner context.stackPosition item) ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directResumedScanTemplate =
        some context.resumedScanRow

/-- Representation-neutral form of all-match exactness over the ordinary
compatible matcher. -/
def ReflectiveDirectProofMatcherExact
    (context : DirectProofContext) (item : ProofOccurrence)
    (space : List Atom) : Prop :=
  ∀ substitution ∈ directProofMatcherRows space,
    instantiateTemplateAtom? substitution directNextMachineTemplate =
        some context.nextMachineRow ∧
      instantiateTemplateAtom? substitution directStackCellTemplate =
        some (compressedStackRow context.proofOwner
          context.stackPosition item) ∧
      instantiateTemplateAtom? substitution directNormalStackCellTemplate =
        some (normalStackRow context.proofOwner context.stackPosition item) ∧
      instantiateTemplateAtom? substitution directResumedScanTemplate =
        some context.resumedScanRow

/-- Source-independent verifier rows retained across one direct proof hit.
The stack-successor row is structural capacity data, not machine state. -/
def directProofActivatedRuntimeRows : List Atom :=
  [compressedPrefixRule,
   MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule,
   compressedInvalidByteRule, compressedQuestionRule,
   compressedQuestionOpenFaultRule]

def directProofStaticFrame (context : DirectProofContext) : List Atom :=
  [compressedProofStepDirective.atom,
   compressedAssertionLaunchDirective.atom,
   compressedHeapLookupFaultDirective.atom,
   compressedHeapLookupAdvanceDirective.atom,
   directProofReplayRule,
   speculativeDirectAssertionDirective.atom,
   context.stackSuccessorRow] ++ directProofContinuationRows ++
    directProofActivatedRuntimeRows

private def directProofAddedStaticRows : List Atom :=
  directProofReplayRule :: directProofActivatedRuntimeRows

private theorem directProofAddedStaticRows_exec_shape
    (row : Atom) (member : row ∈ directProofAddedStaticRows) :
    ∃ tail, row = .expression (.symbol "exec" :: tail) ∧ tail.length = 3 := by
  simp only [directProofAddedStaticRows, directProofActivatedRuntimeRows,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, rfl, rfl⟩

/-- Authored executable rows introduced by the direct handler cannot share a
physical key with any of its three moving predecessor controls. -/
private theorem directProofAddedStaticRows_key_ne_controls
    (context : DirectProofContext) (row : Atom)
    (member : row ∈ directProofAddedStaticRows) :
    morkSupportKey row ≠ morkSupportKey context.pendingRow ∧
      morkSupportKey row ≠ morkSupportKey context.lookupRow ∧
      morkSupportKey row ≠ morkSupportKey context.machineRow := by
  obtain ⟨tail, rfl, tailLength⟩ :=
    directProofAddedStaticRows_exec_shape row member
  constructor
  · unfold DirectProofContext.pendingRow
    apply morkSupportKey_expression_symbol_head_ne
    · omega
    · simp
    · decide
    · decide
    · decide
    · decide
    · decide
  constructor
  · unfold DirectProofContext.lookupRow
    apply morkSupportKey_expression_symbol_head_ne
    · omega
    · simp
    · decide
    · decide
    · decide
    · decide
    · decide
  · unfold DirectProofContext.machineRow
    apply morkSupportKey_expression_symbol_head_ne
    · omega
    · simp
    · decide
    · decide
    · decide
    · decide
    · decide

theorem directProofStaticFrame_clean (context : DirectProofContext) :
    StaticFrame (directProofStaticFrame context) := by
  intro row member
  simp only [directProofStaticFrame, directProofContinuationRows,
    directProofActivatedRuntimeRows,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with (fixed | continuation) | activated
  · rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · decide +kernel
    · simp [directProofReplayRule, isDynamicRow, dynamicRowHeads]
    · decide +kernel
    · simp [isDynamicRow, dynamicRowHeads,
        DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
  · rcases continuation with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · rcases activated with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem directProofStaticFrame_fixed_mem
    (context : DirectProofContext) {row : Atom}
    (member : row ∈
      [compressedProofStepDirective.atom,
       compressedAssertionLaunchDirective.atom,
       compressedHeapLookupFaultDirective.atom,
       compressedHeapLookupAdvanceDirective.atom,
       directProofReplayRule,
       speculativeDirectAssertionDirective.atom,
       context.stackSuccessorRow]) :
    row ∈ directProofStaticFrame context := by
  unfold directProofStaticFrame
  exact List.mem_append_left _ (List.mem_append_left _ member)

private theorem directProofStaticFrame_continuation_mem
    (context : DirectProofContext) {row : Atom}
    (member : row ∈ directProofContinuationRows) :
    row ∈ directProofStaticFrame context := by
  unfold directProofStaticFrame
  exact List.mem_append_left _ (List.mem_append_right _ member)

private theorem directProofStaticFrame_activated_mem
    (context : DirectProofContext) {row : Atom}
    (member : row ∈ directProofActivatedRuntimeRows) :
    row ∈ directProofStaticFrame context := by
  unfold directProofStaticFrame
  exact List.mem_append_right _ member

private def sourceDirectDynamicRows (context : DirectProofContext)
    (item : ProofOccurrence) : List Atom :=
  [context.pendingRow, context.lookupRow,
   heapProofRow context.proofOwner context.index item,
   MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item,
   context.machineRow, context.stackSuccessorRow]

@[simp] theorem source_proof_request_live_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) :
    directProofLive
        (sourceProofRequestSpace context state ledger scanner index item) =
      directProofLive
          (canonicalDirectProofSpace
            (directContextAtBoundary context state scanner index) item) ++
        sourceProofAdditionalRows context state ledger index item := by
  unfold sourceProofRequestSpace directProofLive
  rw [List.erase_append_left]
  simp [canonicalDirectProofSpace]

private theorem source_matcher_factor_origin
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (factor : Atom) (factorMember : factor ∈ directProofPatterns)
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    ∃ beforeFactor afterFactor carrier,
      carrier ∈ speculativeDirectProofDirective.atom ::
          directProofLive
            (sourceProofRequestSpace context state ledger scanner index item) ∧
        Conformance.Computable.cmatchAtom beforeFactor factor carrier =
          some afterFactor ∧
        substitution.lookupExtends afterFactor ∧
        applySubst substitution factor = carrier := by
  unfold directProofMatcherRows at matcherMember
  rw [speculative_direct_proof_input_exact] at matcherMember
  exact
    Conformance.Computable.cmatchInputSpec_compat_factor_match_origin
      (speculativeDirectProofDirective.atom ::
        directProofLive
          (sourceProofRequestSpace context state ledger scanner index item))
      (mkPattern directProofPatterns) factor
      (by simpa [mkPattern] using factorMember) matcherMember

private theorem source_matcher_factor_covered
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (factor : Atom) (factorMember : factor ∈ directProofPatterns)
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    templateCovered substitution factor = true := by
  obtain ⟨beforeFactor, afterFactor, carrier, _carrierMember, matched,
      extension, _replay⟩ :=
    source_matcher_factor_origin context state ledger scanner index item factor
      factorMember matcherMember
  exact Conformance.Computable.templateCovered_of_lookupExtends extension factor
    (Conformance.Computable.cmatchAtom_templateCovered beforeFactor factor
      carrier afterFactor matched)

private theorem source_applySubst_expression_symbol_head_ne
    (substitution : Subst) (authoredHead candidateHead : String)
    (authoredTail candidateTail : List Atom)
    (distinct : authoredHead ≠ candidateHead) :
    applySubst substitution
        (.expression (.symbol authoredHead :: authoredTail)) ≠
      .expression (.symbol candidateHead :: candidateTail) := by
  simp [applySubst, applySubst.applySubstList, distinct]

private theorem source_matcher_dynamic_factor_origin
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (head : String) (tail : List Atom)
    (notExec : head ≠ "exec")
    (notOwnedRuntime : head ≠ "mm-compressed-owned-runtime-rule")
    (factorMember : (.expression (.symbol head :: tail) : Atom) ∈
      directProofPatterns)
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    ∃ carrier,
      (carrier ∈ sourceDirectDynamicRows
          (directContextAtBoundary context state scanner index) item ∨
        carrier ∈ sourceProofAdditionalRows context state ledger index item) ∧
      applySubst substitution (.expression (.symbol head :: tail)) = carrier := by
  obtain ⟨_beforeFactor, _afterFactor, carrier, carrierMember, _matched,
      _extension, replay⟩ :=
    source_matcher_factor_origin context state ledger scanner index item
      (.expression (.symbol head :: tail)) factorMember matcherMember
  rw [source_proof_request_live_exact] at carrierMember
  rw [canonical_direct_proof_live_exact] at carrierMember
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    at carrierMember
  rcases carrierMember with rfl | ((fixed | continuation) | extra)
  · exfalso
    exact source_applySubst_expression_symbol_head_ne substitution head
      "exec" tail _ notExec replay
  · rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution head
        "exec" tail _ notExec replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution head
        "exec" tail _ notExec replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution head
        "exec" tail _ notExec replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution head
        "exec" tail _ notExec replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution head
        "exec" tail _ notExec replay
    · exact ⟨_, Or.inl (by simp [sourceDirectDynamicRows]), replay⟩
    · exact ⟨_, Or.inl (by simp [sourceDirectDynamicRows]), replay⟩
    · exact ⟨_, Or.inl (by simp [sourceDirectDynamicRows]), replay⟩
    · exact ⟨_, Or.inl (by simp [sourceDirectDynamicRows]), replay⟩
    · exact ⟨_, Or.inl (by simp [sourceDirectDynamicRows]), replay⟩
    · exact ⟨_, Or.inl (by simp [sourceDirectDynamicRows]), replay⟩
  · simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at continuation
    rcases continuation with rfl | rfl | rfl | rfl | rfl <;>
      exfalso <;>
      exact source_applySubst_expression_symbol_head_ne substitution head
        "mm-compressed-owned-runtime-rule" tail _ notOwnedRuntime replay
  · exact ⟨carrier, Or.inr extra, replay⟩

private theorem source_additional_cannot_replay_nonpassive_head
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) (substitution : Subst)
    (head : String) (tail : List Atom) (carrier : Atom)
    (notPassive : head ∉
      ["mm-compressed-heap-proof", "mm-compressed-heap-assertion",
       "mm-compressed-node", "mm-compressed-stack-cell", "mm-stack-cell",
       "mm-compressed-save-receipt"])
    (member : carrier ∈
      sourceProofAdditionalRows context state ledger index item) :
    applySubst substitution (.expression (.symbol head :: tail)) ≠ carrier := by
  have heads := sourceProofAdditionalRows_head_cases context state ledger index
    item member
  intro replay
  rcases heads with heap | assertion | node | compact | normal | save
  · obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-heap-proof").mp heap
    exact source_applySubst_expression_symbol_head_ne substitution head
      "mm-compressed-heap-proof" tail candidateTail (by
        intro equal
        apply notPassive
        simp [equal]) replay
  · obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-heap-assertion").mp assertion
    exact source_applySubst_expression_symbol_head_ne substitution head
      "mm-compressed-heap-assertion" tail candidateTail
      (by
        intro equal
        apply notPassive
        simp [equal]) replay
  · obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-node").mp node
    exact source_applySubst_expression_symbol_head_ne substitution head
      "mm-compressed-node" tail candidateTail (by
        intro equal
        apply notPassive
        simp [equal]) replay
  · obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-stack-cell").mp compact
    exact source_applySubst_expression_symbol_head_ne substitution head
      "mm-compressed-stack-cell" tail candidateTail
      (by
        intro equal
        apply notPassive
        simp [equal]) replay
  · obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier "mm-stack-cell").mp normal
    exact source_applySubst_expression_symbol_head_ne substitution head
      "mm-stack-cell" tail candidateTail (by
        intro equal
        apply notPassive
        simp [equal]) replay
  · obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-save-receipt").mp save
    exact source_applySubst_expression_symbol_head_ne substitution head
      "mm-compressed-save-receipt" tail candidateTail
      (by
        intro equal
        apply notPassive
        simp [equal]) replay

private theorem applySubst_speculativeDirectProofDirective_loc
    (substitution : Subst) :
    applySubst substitution speculativeDirectProofDirective.loc =
      speculativeDirectProofDirective.loc := by
  have locationExact : speculativeDirectProofDirective.loc =
      .expression [.symbol "00", .symbol "mm-compressed-direct-0-proof"] := by
    decide +kernel
  rw [locationExact]
  rfl

private theorem source_direct_probe_exec_location_impossible
    (before after : Subst) (candidate : SourceExecFact)
    (surface : ∃ input output,
      candidate.atom =
        .expression [.symbol "exec", candidate.loc, input, output])
    (distinct : speculativeDirectProofDirective.loc ≠ candidate.loc)
    (matched : Conformance.Computable.cmatchAtom before directProbeSelfPattern
      candidate.atom = some after) : False := by
  obtain ⟨input, output, shape⟩ := surface
  have replay := Conformance.Computable.cmatchAtom_applySubst before
    directProbeSelfPattern candidate.atom after matched
  rw [shape] at replay
  simp only [directProbeSelfPattern, applySubst, applySubst.applySubstList,
    Atom.expression.injEq, List.cons.injEq, true_and] at replay
  rw [applySubst_speculativeDirectProofDirective_loc] at replay
  exact distinct replay.1

/-- The self-replay sink can only install the authored relocation of the
selected direct-proof body; no other executable row has its source location. -/
private theorem source_direct_self_output_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution directProofSelfTemplate = directProofReplayRule := by
  obtain ⟨beforeFactor, afterFactor, carrier, carrierMember, matched,
      _extension, replay⟩ :=
    source_matcher_factor_origin context state ledger scanner index item
      directProbeSelfPattern (by simp [directProofPatterns]) matcherMember
  rw [source_proof_request_live_exact] at carrierMember
  rw [canonical_direct_proof_live_exact] at carrierMember
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    at carrierMember
  rcases carrierMember with rfl | ((fixed | continuation) | extra)
  · rw [speculativeDirectProofDirective_atom_exact] at replay
    simp [directProbeSelfPattern, directProofSelfTemplate,
      directProofReplayRule, applySubst, applySubst.applySubstList] at replay ⊢
    aesop
  · rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
    · exact False.elim (source_direct_probe_exec_location_impossible
        beforeFactor afterFactor compressedProofStepDirective ⟨_, _, rfl⟩
        (by decide +kernel) matched)
    · exact False.elim (source_direct_probe_exec_location_impossible
        beforeFactor afterFactor compressedAssertionLaunchDirective ⟨_, _, rfl⟩
        (by decide +kernel) matched)
    · exact False.elim (source_direct_probe_exec_location_impossible
        beforeFactor afterFactor compressedHeapLookupFaultDirective ⟨_, _, rfl⟩
        (by decide +kernel) matched)
    · exact False.elim (source_direct_probe_exec_location_impossible
        beforeFactor afterFactor compressedHeapLookupAdvanceDirective ⟨_, _, rfl⟩
        (by decide +kernel) matched)
    · exact False.elim (source_direct_probe_exec_location_impossible
        beforeFactor afterFactor speculativeDirectAssertionDirective ⟨_, _, rfl⟩
        (by decide +kernel) matched)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution "exec"
        "mm-compressed-step-pending" _ _ (by decide)
        (by simpa [directProbeSelfPattern,
          DirectProofContext.pendingRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution "exec"
        "mm-compressed-heap-lookup" _ _ (by decide)
        (by simpa [directProbeSelfPattern,
          DirectProofContext.lookupRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution "exec"
        "mm-compressed-heap-proof" _ _ (by decide)
        (by simpa [directProbeSelfPattern, heapProofRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution "exec"
        "mm-compressed-node" _ _ (by decide)
        (by simpa [directProbeSelfPattern,
          MM2CompressedProofHeapEncoding.nodeRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution "exec"
        "mm-compressed-machine" _ _ (by decide)
        (by simpa [directProbeSelfPattern,
          DirectProofContext.machineRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution "exec"
        "mm-compressed-index-successor" _ _ (by decide)
        (by simpa [directProbeSelfPattern,
          DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
          using replay)
  · simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at continuation
    rcases continuation with rfl | rfl | rfl | rfl | rfl <;>
      exfalso <;>
      exact source_applySubst_expression_symbol_head_ne substitution "exec"
        "mm-compressed-owned-runtime-rule" _ _ (by decide)
        (by simpa [directProbeSelfPattern, compressedOwnedRuntimeRuleRow]
          using replay)
  · exfalso
    exact source_additional_cannot_replay_nonpassive_head context state ledger
      index item substitution "exec" _ carrier (by decide) extra
      (by simpa [directProbeSelfPattern] using replay)

private theorem source_applySubst_owned_ne_exec
    (substitution : Subst) (kind variableName : String)
    (candidate : SourceExecFact)
    (surface : ∃ input output,
      candidate.atom =
        .expression [.symbol "exec", candidate.loc, input, output]) :
    applySubst substitution (directOwnedRulePattern kind variableName) ≠
      candidate.atom := by
  obtain ⟨input, output, shape⟩ := surface
  rw [shape]
  exact source_applySubst_expression_symbol_head_ne substitution
    "mm-compressed-owned-runtime-rule" "exec" _ _ (by decide)

/-- Every owned-runtime factor is supplied by the authenticated continuation
inventory.  Dynamic source rows and executable shells cannot impersonate it. -/
private theorem source_direct_owned_factor_origin
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) (kind variableName : String)
    {substitution : Subst}
    (factorMember :
      directOwnedRulePattern kind variableName ∈ directProofPatterns)
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    ∃ carrier ∈ directProofContinuationRows,
      applySubst substitution (directOwnedRulePattern kind variableName) =
        carrier := by
  obtain ⟨_beforeFactor, _afterFactor, carrier, carrierMember, _matched,
      _extension, replay⟩ :=
    source_matcher_factor_origin context state ledger scanner index item
      (directOwnedRulePattern kind variableName) factorMember matcherMember
  rw [source_proof_request_live_exact] at carrierMember
  rw [canonical_direct_proof_live_exact] at carrierMember
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
    at carrierMember
  rcases carrierMember with rfl | ((fixed | continuation) | extra)
  · exfalso
    exact source_applySubst_owned_ne_exec substitution kind variableName
      speculativeDirectProofDirective ⟨_, _, rfl⟩ replay
  · rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
    · exfalso
      exact source_applySubst_owned_ne_exec substitution kind variableName
        compressedProofStepDirective ⟨_, _, rfl⟩ replay
    · exfalso
      exact source_applySubst_owned_ne_exec substitution kind variableName
        compressedAssertionLaunchDirective ⟨_, _, rfl⟩ replay
    · exfalso
      exact source_applySubst_owned_ne_exec substitution kind variableName
        compressedHeapLookupFaultDirective ⟨_, _, rfl⟩ replay
    · exfalso
      exact source_applySubst_owned_ne_exec substitution kind variableName
        compressedHeapLookupAdvanceDirective ⟨_, _, rfl⟩ replay
    · exfalso
      exact source_applySubst_owned_ne_exec substitution kind variableName
        speculativeDirectAssertionDirective ⟨_, _, rfl⟩ replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-owned-runtime-rule" "mm-compressed-step-pending" _ _
        (by decide) (by simpa [directOwnedRulePattern,
          DirectProofContext.pendingRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-owned-runtime-rule" "mm-compressed-heap-lookup" _ _
        (by decide) (by simpa [directOwnedRulePattern,
          DirectProofContext.lookupRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-owned-runtime-rule" "mm-compressed-heap-proof" _ _
        (by decide) (by simpa [directOwnedRulePattern, heapProofRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-owned-runtime-rule" "mm-compressed-node" _ _
        (by decide) (by simpa [directOwnedRulePattern,
          MM2CompressedProofHeapEncoding.nodeRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-owned-runtime-rule" "mm-compressed-machine" _ _
        (by decide) (by simpa [directOwnedRulePattern,
          DirectProofContext.machineRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-owned-runtime-rule" "mm-compressed-index-successor" _ _
        (by decide) (by simpa [directOwnedRulePattern,
          DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
          using replay)
  · exact ⟨carrier, continuation, replay⟩
  · exfalso
    exact source_additional_cannot_replay_nonpassive_head context state ledger
      index item substitution "mm-compressed-owned-runtime-rule" _ carrier
      (by decide) extra (by simpa [directOwnedRulePattern] using replay)

/-- Every matcher emits the same five continuation rules captured by the
source-derived speculative presentation. -/
private theorem source_direct_runtime_outputs_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution (.var "compressed-prefix-rule") =
        compressedPrefixRule ∧
      applySubst substitution (.var "compressed-terminal-rule") =
        MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule ∧
      applySubst substitution (.var "compressed-invalid-byte-rule") =
        compressedInvalidByteRule ∧
      applySubst substitution (.var "compressed-question-rule") =
        compressedQuestionRule ∧
      applySubst substitution (.var "compressed-question-open-fault-rule") =
        compressedQuestionOpenFaultRule := by
  have prefixOrigin := source_direct_owned_factor_origin context state ledger scanner
    index item "prefix" "compressed-prefix-rule"
      (by simp [directProofPatterns]) matcherMember
  have terminalOrigin := source_direct_owned_factor_origin context state ledger scanner
    index item "terminal" "compressed-terminal-rule"
      (by simp [directProofPatterns]) matcherMember
  have invalidOrigin := source_direct_owned_factor_origin context state ledger scanner
    index item "invalid-byte" "compressed-invalid-byte-rule"
      (by simp [directProofPatterns]) matcherMember
  have questionOrigin := source_direct_owned_factor_origin context state ledger scanner
    index item "question" "compressed-question-rule"
      (by simp [directProofPatterns]) matcherMember
  have questionOpenOrigin := source_direct_owned_factor_origin context state ledger
    scanner index item "question-open-fault"
      "compressed-question-open-fault-rule"
      (by simp [directProofPatterns]) matcherMember
  constructor
  · rcases prefixOrigin with ⟨prefixCarrier, prefixMember, prefixReplay⟩
    simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at prefixMember
    rcases prefixMember with rfl | rfl | rfl | rfl | rfl <;>
      simp [directOwnedRulePattern, compressedOwnedRuntimeRuleRow, applySubst,
        applySubst.applySubstList] at prefixReplay
    exact prefixReplay
  constructor
  · rcases terminalOrigin with ⟨terminalCarrier, terminalMember, terminalReplay⟩
    simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at terminalMember
    rcases terminalMember with rfl | rfl | rfl | rfl | rfl <;>
      simp [directOwnedRulePattern, compressedOwnedRuntimeRuleRow, applySubst,
        applySubst.applySubstList] at terminalReplay
    exact terminalReplay
  constructor
  · rcases invalidOrigin with ⟨invalidCarrier, invalidMember, invalidReplay⟩
    simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at invalidMember
    rcases invalidMember with rfl | rfl | rfl | rfl | rfl <;>
      simp [directOwnedRulePattern, compressedOwnedRuntimeRuleRow, applySubst,
        applySubst.applySubstList] at invalidReplay
    exact invalidReplay
  constructor
  · rcases questionOrigin with ⟨questionCarrier, questionMember, questionReplay⟩
    simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at questionMember
    rcases questionMember with rfl | rfl | rfl | rfl | rfl <;>
      simp [directOwnedRulePattern, compressedOwnedRuntimeRuleRow, applySubst,
        applySubst.applySubstList] at questionReplay
    exact questionReplay
  · rcases questionOpenOrigin with
      ⟨questionOpenCarrier, questionOpenMember, questionOpenReplay⟩
    simp only [directProofContinuationRows, List.mem_cons, List.not_mem_nil,
      or_false] at questionOpenMember
    rcases questionOpenMember with rfl | rfl | rfl | rfl | rfl <;>
      simp [directOwnedRulePattern, compressedOwnedRuntimeRuleRow, applySubst,
        applySubst.applySubstList] at questionOpenReplay
    exact questionOpenReplay

/-- The complete whole-source matcher obtains its pending request from the
canonical request row; persistent source data cannot impersonate this control. -/
theorem source_direct_pending_factor_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution directPendingTemplate =
      (directContextAtBoundary context state scanner index).pendingRow := by
  let directContext := directContextAtBoundary context state scanner index
  obtain ⟨carrier, dynamic | extra, replay⟩ :=
    source_matcher_dynamic_factor_origin context state ledger scanner index item
      "mm-compressed-step-pending"
      [.var "scope-owner", .var "proof-owner", .var "word-position",
       .var "remaining-bytes",
       .expression
        [.symbol "mm-compressed-index-code", .var "reverse-prefix",
          .var "terminal-digit"]]
      (by decide) (by decide)
      (by simp [directProofPatterns, directPendingTemplate]) matcherMember
  · simp only [sourceDirectDynamicRows, List.mem_cons, List.not_mem_nil,
      or_false] at dynamic
    rcases dynamic with rfl | rfl | rfl | rfl | rfl | rfl
    · change applySubst substitution directPendingTemplate =
        directContext.pendingRow at replay
      simpa [directContext] using replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-step-pending" "mm-compressed-heap-lookup" _ _
        (by decide) (by simpa [directPendingTemplate,
          DirectProofContext.lookupRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-step-pending" "mm-compressed-heap-proof" _ _
        (by decide) (by simpa [directPendingTemplate, heapProofRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-step-pending" "mm-compressed-node" _ _
        (by decide) (by simpa [directPendingTemplate,
          MM2CompressedProofHeapEncoding.nodeRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-step-pending" "mm-compressed-machine" _ _
        (by decide) (by simpa [directPendingTemplate,
          DirectProofContext.machineRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-step-pending" "mm-compressed-index-successor" _ _
        (by decide) (by simpa [directPendingTemplate,
          DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
          using replay)
  · exfalso
    exact source_additional_cannot_replay_nonpassive_head context state ledger
      index item substitution "mm-compressed-step-pending" _ carrier
      (by decide) extra replay

/-- The complete whole-source matcher obtains the exact lookup request. -/
theorem source_direct_lookup_factor_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution directLookupTemplate =
      (directContextAtBoundary context state scanner index).lookupRow := by
  let directContext := directContextAtBoundary context state scanner index
  obtain ⟨carrier, dynamic | extra, replay⟩ :=
    source_matcher_dynamic_factor_origin context state ledger scanner index item
      "mm-compressed-heap-lookup"
      [.var "scope-owner", .var "proof-owner", .var "word-position",
       .var "remaining-bytes", .var "compressed-index",
       .var "speculative-cursor"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directLookupTemplate]) matcherMember
  · simp only [sourceDirectDynamicRows, List.mem_cons, List.not_mem_nil,
      or_false] at dynamic
    rcases dynamic with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-lookup" "mm-compressed-step-pending" _ _
        (by decide) (by simpa [directLookupTemplate,
          DirectProofContext.pendingRow] using replay)
    · change applySubst substitution directLookupTemplate =
        directContext.lookupRow at replay
      simpa [directContext] using replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-lookup" "mm-compressed-heap-proof" _ _
        (by decide) (by simpa [directLookupTemplate, heapProofRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-lookup" "mm-compressed-node" _ _
        (by decide) (by simpa [directLookupTemplate,
          MM2CompressedProofHeapEncoding.nodeRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-lookup" "mm-compressed-machine" _ _
        (by decide) (by simpa [directLookupTemplate,
          DirectProofContext.machineRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-lookup" "mm-compressed-index-successor" _ _
        (by decide) (by simpa [directLookupTemplate,
          DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
          using replay)
  · exfalso
    exact source_additional_cannot_replay_nonpassive_head context state ledger
      index item substitution "mm-compressed-heap-lookup" _ carrier
      (by decide) extra replay

/-- The whole-source matcher obtains machine frontiers only from the canonical
machine row. -/
theorem source_direct_machine_factor_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution directMachineTemplate =
      (directContextAtBoundary context state scanner index).machineRow := by
  let directContext := directContextAtBoundary context state scanner index
  obtain ⟨carrier, dynamic | extra, replay⟩ :=
    source_matcher_dynamic_factor_origin context state ledger scanner index item
      "mm-compressed-machine"
      [.var "scope-owner", .var "proof-owner", .var "heap-next",
       .var "node-next", .var "stack-position"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directMachineTemplate]) matcherMember
  · simp only [sourceDirectDynamicRows, List.mem_cons, List.not_mem_nil,
      or_false] at dynamic
    rcases dynamic with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-machine" "mm-compressed-step-pending" _ _
        (by decide) (by simpa [directMachineTemplate,
          DirectProofContext.pendingRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-machine" "mm-compressed-heap-lookup" _ _
        (by decide) (by simpa [directMachineTemplate,
          DirectProofContext.lookupRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-machine" "mm-compressed-heap-proof" _ _
        (by decide) (by simpa [directMachineTemplate, heapProofRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-machine" "mm-compressed-node" _ _
        (by decide) (by simpa [directMachineTemplate,
          MM2CompressedProofHeapEncoding.nodeRow] using replay)
    · change applySubst substitution directMachineTemplate =
        directContext.machineRow at replay
      simpa [directContext] using replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-machine" "mm-compressed-index-successor" _ _
        (by decide) (by simpa [directMachineTemplate,
          DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
          using replay)
  · exfalso
    exact source_additional_cannot_replay_nonpassive_head context state ledger
      index item substitution "mm-compressed-machine" _ carrier
      (by decide) extra replay

/-- The whole-source matcher obtains the exact stack-successor table row. -/
theorem source_direct_successor_factor_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution directStackSuccessorPattern =
      (directContextAtBoundary context state scanner index).stackSuccessorRow := by
  let directContext := directContextAtBoundary context state scanner index
  obtain ⟨carrier, dynamic | extra, replay⟩ :=
    source_matcher_dynamic_factor_origin context state ledger scanner index item
      "mm-compressed-index-successor"
      [.expression
        [.symbol "mm-compressed-stack-owner", .var "proof-owner"],
       .var "stack-position", .var "next-stack-position"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directStackSuccessorPattern]) matcherMember
  · simp only [sourceDirectDynamicRows, List.mem_cons, List.not_mem_nil,
      or_false] at dynamic
    rcases dynamic with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-index-successor" "mm-compressed-step-pending" _ _
        (by decide) (by simpa [directStackSuccessorPattern,
          DirectProofContext.pendingRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-index-successor" "mm-compressed-heap-lookup" _ _
        (by decide) (by simpa [directStackSuccessorPattern,
          DirectProofContext.lookupRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-index-successor" "mm-compressed-heap-proof" _ _
        (by decide) (by simpa [directStackSuccessorPattern, heapProofRow]
          using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-index-successor" "mm-compressed-node" _ _
        (by decide) (by simpa [directStackSuccessorPattern,
          MM2CompressedProofHeapEncoding.nodeRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-index-successor" "mm-compressed-machine" _ _
        (by decide) (by simpa [directStackSuccessorPattern,
          DirectProofContext.machineRow] using replay)
    · change applySubst substitution directStackSuccessorPattern =
        directContext.stackSuccessorRow at replay
      simpa [directContext] using replay
  · exfalso
    exact source_additional_cannot_replay_nonpassive_head context state ledger
      index item substitution "mm-compressed-index-successor" _ carrier
      (by decide) extra replay

private theorem source_direct_owner_index_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence) {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution (.var "proof-owner") = context.proofOwner ∧
      applySubst substitution (.var "compressed-index") =
        (CompressedIndexCode.ofNat index).atom := by
  have pendingExact := source_direct_pending_factor_exact context state ledger
    scanner index item matcherMember
  have lookupExact := source_direct_lookup_factor_exact context state ledger
    scanner index item matcherMember
  simp [directPendingTemplate, directLookupTemplate,
    directContextAtBoundary, DirectProofContext.pendingRow,
    DirectProofContext.lookupRow, applySubst, applySubst.applySubstList]
    at pendingExact lookupExact
  aesop

private theorem source_additional_heap_member_of_replay
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) (substitution : Subst) (carrier : Atom)
    (additional : carrier ∈
      sourceProofAdditionalRows context state ledger index item)
    (replay : applySubst substitution directHeapProofPattern = carrier) :
    carrier ∈ heapProofRows context.proofOwner (displayedHeap state ledger) := by
  have passive := (List.mem_filter.mp additional).1
  simp only [canonicalPassiveRows, List.mem_append] at passive
  rcases passive with (((heap | assertion) | node) | stack) | save
  · exact heap
  · have head := assertionHeapRowsFrom_head context.proofOwner 0 state.heap
      carrier (by simpa [assertionHeapRows] using assertion)
    obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-heap-assertion").mp head
    exfalso
    exact source_applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-proof" "mm-compressed-heap-assertion" _ _
      (by decide) (by simpa [directHeapProofPattern] using replay)
  · have head := sourceNodeRowsFrom_head context.proofOwner 0 state.nodes
      ledger.occurrences carrier (by simpa [sourceNodeRows] using node)
    obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-node").mp head
    exfalso
    exact source_applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-proof" "mm-compressed-node" _ _
      (by decide) (by simpa [directHeapProofPattern] using replay)
  · rcases sourceStackRowsFrom_head context.proofOwner state ledger 0
        state.stack carrier (by simpa [sourceStackRows] using stack) with
      compact | normal
    · obtain ⟨candidateTail, rfl⟩ :=
        (compressedDynamicRowHead?_eq_some_iff carrier
          "mm-compressed-stack-cell").mp compact
      exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-proof" "mm-compressed-stack-cell" _ _
        (by decide) (by simpa [directHeapProofPattern] using replay)
    · obtain ⟨candidateTail, rfl⟩ :=
        (compressedDynamicRowHead?_eq_some_iff carrier "mm-stack-cell").mp
          normal
      exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-proof" "mm-stack-cell" _ _
        (by decide) (by simpa [directHeapProofPattern] using replay)
  · have head := sourceSaveRowsFrom_head context state ledger 0 state.saves
      carrier (by simpa [sourceSaveRows] using save)
    obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-save-receipt").mp head
    exfalso
    exact source_applySubst_expression_symbol_head_ne substitution
      "mm-compressed-heap-proof" "mm-compressed-save-receipt" _ _
      (by decide) (by simpa [directHeapProofPattern] using replay)

/-- The requested heap factor is exact even in the complete source display.
Any same-headed candidate is inverted to its source heap position; functional
list lookup then identifies it with the requested occurrence. -/
theorem source_direct_heap_factor_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence)
    (displayedLookup : GetElem?.getElem? (displayedHeap state ledger) index =
      some (.occurrence item))
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution directHeapProofPattern =
      heapProofRow context.proofOwner index item := by
  let directContext := directContextAtBoundary context state scanner index
  obtain ⟨carrier, dynamic | additional, replay⟩ :=
    source_matcher_dynamic_factor_origin context state ledger scanner index item
      "mm-compressed-heap-proof"
      [.var "proof-owner", .var "compressed-index", .var "node-id"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directHeapProofPattern]) matcherMember
  · simp only [sourceDirectDynamicRows, List.mem_cons, List.not_mem_nil,
      or_false] at dynamic
    rcases dynamic with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-proof" "mm-compressed-step-pending" _ _
        (by decide) (by simpa [directHeapProofPattern,
          DirectProofContext.pendingRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-proof" "mm-compressed-heap-lookup" _ _
        (by decide) (by simpa [directHeapProofPattern,
          DirectProofContext.lookupRow] using replay)
    · change applySubst substitution directHeapProofPattern =
        heapProofRow directContext.proofOwner directContext.index item at replay
      simpa [directContext, directContextAtBoundary] using replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-proof" "mm-compressed-node" _ _
        (by decide) (by simpa [directHeapProofPattern,
          MM2CompressedProofHeapEncoding.nodeRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-proof" "mm-compressed-machine" _ _
        (by decide) (by simpa [directHeapProofPattern,
          DirectProofContext.machineRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-heap-proof" "mm-compressed-index-successor" _ _
        (by decide) (by simpa [directHeapProofPattern,
          DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
          using replay)
  · have heapMember := source_additional_heap_member_of_replay context state
      ledger index item substitution carrier additional replay
    obtain ⟨ownerExact, indexExact⟩ :=
      source_direct_owner_index_exact context state ledger scanner index item
        matcherMember
    let candidate : ProofOccurrence :=
      ⟨applySubst substitution (.var "node-id"), item.value⟩
    have ownerExact' : context.proofOwner =
        (substitution.lookup "proof-owner").getD (.var "proof-owner") := by
      simpa [applySubst] using ownerExact.symm
    have indexExact' : (CompressedIndexCode.ofNat index).atom =
        (substitution.lookup "compressed-index").getD
          (.var "compressed-index") := by
      simpa [applySubst] using indexExact.symm
    have carrierAsHeap :
        heapProofRow context.proofOwner index candidate = carrier := by
      rw [← replay]
      simp [heapProofRow, candidate, ownerExact', indexExact', applySubst,
        applySubst.applySubstList]
    have candidateMember : heapProofRow context.proofOwner index candidate ∈
        heapProofRowsFrom context.proofOwner 0 (displayedHeap state ledger) := by
      simpa [heapProofRows, carrierAsHeap] using heapMember
    obtain ⟨foundIndex, actual, actualLookup, positionEqual, identityEqual⟩ :=
      heapProofRow_mem_heapProofRowsFrom_inverts context.proofOwner 0
        (displayedHeap state ledger) index candidate candidateMember
    have foundIndexEqual : foundIndex = index := by
      omega
    have actualEqual : actual = item := by
      subst foundIndex
      rw [displayedLookup] at actualLookup
      exact
        (Entry.occurrence.inj (Option.some.inj actualLookup)).symm
    subst actual
    have rowEqual : heapProofRow context.proofOwner index candidate =
        heapProofRow context.proofOwner index item :=
      (heapProofRow_eq_iff context.proofOwner index index candidate item).2
        ⟨rfl, identityEqual⟩
    have carrierEqual : carrier = heapProofRow context.proofOwner index item := by
      rw [← carrierAsHeap, rowEqual]
    have avoids := (List.mem_filter.mp additional).2
    simp only [Bool.and_eq_true, bne_iff_ne] at avoids
    exact False.elim (avoids.1 carrierEqual)

private theorem source_additional_node_member_of_replay
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (index : Nat)
    (item : ProofOccurrence) (substitution : Subst) (carrier : Atom)
    (additional : carrier ∈
      sourceProofAdditionalRows context state ledger index item)
    (replay : applySubst substitution directNodePattern = carrier) :
    carrier ∈ sourceNodeRows context.proofOwner state ledger := by
  have passive := (List.mem_filter.mp additional).1
  simp only [canonicalPassiveRows, List.mem_append] at passive
  rcases passive with (((heap | assertion) | node) | stack) | save
  · have head := heapProofRowsFrom_head context.proofOwner 0
      (displayedHeap state ledger) carrier
      (by simpa [heapProofRows] using heap)
    obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-heap-proof").mp head
    exfalso
    exact source_applySubst_expression_symbol_head_ne substitution
      "mm-compressed-node" "mm-compressed-heap-proof" _ _
      (by decide) (by simpa [directNodePattern] using replay)
  · have head := assertionHeapRowsFrom_head context.proofOwner 0 state.heap
      carrier (by simpa [assertionHeapRows] using assertion)
    obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-heap-assertion").mp head
    exfalso
    exact source_applySubst_expression_symbol_head_ne substitution
      "mm-compressed-node" "mm-compressed-heap-assertion" _ _
      (by decide) (by simpa [directNodePattern] using replay)
  · exact node
  · rcases sourceStackRowsFrom_head context.proofOwner state ledger 0
        state.stack carrier (by simpa [sourceStackRows] using stack) with
      compact | normal
    · obtain ⟨candidateTail, rfl⟩ :=
        (compressedDynamicRowHead?_eq_some_iff carrier
          "mm-compressed-stack-cell").mp compact
      exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-node" "mm-compressed-stack-cell" _ _
        (by decide) (by simpa [directNodePattern] using replay)
    · obtain ⟨candidateTail, rfl⟩ :=
        (compressedDynamicRowHead?_eq_some_iff carrier "mm-stack-cell").mp
          normal
      exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-node" "mm-stack-cell" _ _
        (by decide) (by simpa [directNodePattern] using replay)
  · have head := sourceSaveRowsFrom_head context state ledger 0 state.saves
      carrier (by simpa [sourceSaveRows] using save)
    obtain ⟨candidateTail, rfl⟩ :=
      (compressedDynamicRowHead?_eq_some_iff carrier
        "mm-compressed-save-receipt").mp head
    exfalso
    exact source_applySubst_expression_symbol_head_ne substitution
      "mm-compressed-node" "mm-compressed-save-receipt" _ _
      (by decide) (by simpa [directNodePattern] using replay)

private theorem source_direct_node_identity_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence)
    (displayedLookup : GetElem?.getElem? (displayedHeap state ledger) index =
      some (.occurrence item))
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution (.var "node-id") = item.identity := by
  have heapExact := source_direct_heap_factor_exact context state ledger scanner
    index item displayedLookup matcherMember
  simp [directHeapProofPattern, heapProofRow, applySubst,
    applySubst.applySubstList] at heapExact
  aesop

/-- The requested node factor is exact in the complete source display.  A
same-headed candidate is inverted through the node table and occurrence
ledger, so equal node identities cannot carry a different formula or source
occurrence. -/
theorem source_direct_node_factor_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index nodeId : Nat) (node : ProofNode source target)
    (sourceOccurrence : Atom) (item : ProofOccurrence)
    (itemExact : item = displayedProofOccurrence nodeId node sourceOccurrence)
    (displayedLookup : GetElem?.getElem? (displayedHeap state ledger) index =
      some (.occurrence item))
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    {substitution : Subst}
    (matcherMember : substitution ∈ directProofMatcherRows
      (sourceProofRequestSpace context state ledger scanner index item)) :
    applySubst substitution directNodePattern =
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item := by
  let directContext := directContextAtBoundary context state scanner index
  obtain ⟨carrier, dynamic | additional, replay⟩ :=
    source_matcher_dynamic_factor_origin context state ledger scanner index item
      "mm-compressed-node"
      [.var "proof-owner", .var "node-id", .var "node-formula",
       .var "node-occurrence"]
      (by decide) (by decide)
      (by simp [directProofPatterns, directNodePattern]) matcherMember
  · simp only [sourceDirectDynamicRows, List.mem_cons, List.not_mem_nil,
      or_false] at dynamic
    rcases dynamic with rfl | rfl | rfl | rfl | rfl | rfl
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-node" "mm-compressed-step-pending" _ _
        (by decide) (by simpa [directNodePattern,
          DirectProofContext.pendingRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-node" "mm-compressed-heap-lookup" _ _
        (by decide) (by simpa [directNodePattern,
          DirectProofContext.lookupRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-node" "mm-compressed-heap-proof" _ _
        (by decide) (by simpa [directNodePattern, heapProofRow] using replay)
    · change applySubst substitution directNodePattern =
        MM2CompressedProofHeapEncoding.nodeRow directContext.proofOwner item
          at replay
      simpa [directContext, directContextAtBoundary] using replay
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-node" "mm-compressed-machine" _ _
        (by decide) (by simpa [directNodePattern,
          DirectProofContext.machineRow] using replay)
    · exfalso
      exact source_applySubst_expression_symbol_head_ne substitution
        "mm-compressed-node" "mm-compressed-index-successor" _ _
        (by decide) (by simpa [directNodePattern,
          DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
          using replay)
  · have nodeMember := source_additional_node_member_of_replay context state
      ledger index item substitution carrier additional replay
    have ownerExact :=
      (source_direct_owner_index_exact context state ledger scanner index item
        matcherMember).1
    have identityExact := source_direct_node_identity_exact context state ledger
      scanner index item displayedLookup matcherMember
    let candidate : ProofOccurrence :=
      ⟨applySubst substitution (.var "node-id"),
        ⟨applySubst substitution (.var "node-formula"),
          applySubst substitution (.var "node-occurrence")⟩⟩
    have ownerExact' : context.proofOwner =
        (substitution.lookup "proof-owner").getD (.var "proof-owner") := by
      simpa [applySubst] using ownerExact.symm
    have carrierAsNode :
        MM2CompressedProofHeapEncoding.nodeRow context.proofOwner candidate =
          carrier := by
      rw [← replay]
      simp [MM2CompressedProofHeapEncoding.nodeRow, candidate, ownerExact',
        applySubst, applySubst.applySubstList]
    have candidateMember :
        MM2CompressedProofHeapEncoding.nodeRow context.proofOwner candidate ∈
          sourceNodeRowsFrom context.proofOwner 0 state.nodes
            ledger.occurrences := by
      simpa [sourceNodeRows, carrierAsNode] using nodeMember
    obtain ⟨foundIndex, foundNode, foundOccurrence, foundNodeLookup,
        foundOccurrenceLookup, candidateExact⟩ :=
      nodeRow_mem_sourceNodeRowsFrom_inverts context.proofOwner 0 state.nodes
        ledger.occurrences candidate candidateMember
    have foundIndexEqual : foundIndex = nodeId := by
      have encodedEqual :
          (CompressedIndexCode.ofNat foundIndex).atom =
            (CompressedIndexCode.ofNat nodeId).atom := by
        rw [itemExact] at identityExact
        have candidateIdentity :=
          congrArg (fun occurrence : ProofOccurrence => occurrence.identity)
            candidateExact
        simpa [candidate, displayedProofOccurrence] using
          candidateIdentity.symm.trans identityExact
      exact MM2CompressedIndexSpine.CanonicalIndexCode.ofNat_injective
        (MM2CompressedIndexSpine.CanonicalIndexCode.atom_injective encodedEqual)
    subst foundIndex
    rw [nodeLookup] at foundNodeLookup
    have foundNodeEqual : foundNode = node :=
      Option.some.inj foundNodeLookup |>.symm
    subst foundNode
    rw [occurrenceLookup] at foundOccurrenceLookup
    have foundOccurrenceEqual : foundOccurrence = sourceOccurrence :=
      Option.some.inj foundOccurrenceLookup |>.symm
    subst foundOccurrence
    have candidateEqualsItem : candidate = item := by
      simpa [itemExact] using candidateExact
    have carrierEqual : carrier =
        MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item := by
      rw [← carrierAsNode, candidateEqualsItem]
    have avoids := (List.mem_filter.mp additional).2
    simp only [Bool.and_eq_true, bne_iff_ne] at avoids
    exact False.elim (avoids.2 carrierEqual)

/-- Every compatible matcher over the complete source-derived request emits
the same four successor rows.  Heap position, node payload, and source
occurrence are reconstructed from source tables rather than accepted from an
arbitrary target row. -/
theorem source_direct_proof_matcher_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index nodeId : Nat) (node : ProofNode source target)
    (sourceOccurrence : Atom) (item : ProofOccurrence)
    (itemExact : item = displayedProofOccurrence nodeId node sourceOccurrence)
    (displayedLookup : GetElem?.getElem? (displayedHeap state ledger) index =
      some (.occurrence item))
    (nodeLookup : state.nodes[nodeId]? = some node)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence) :
    ReflectiveDirectProofMatcherExact
      (directContextAtBoundary context state scanner index) item
      (sourceProofRequestSpace context state ledger scanner index item) := by
  intro substitution matcherMember
  let directContext := directContextAtBoundary context state scanner index
  have pendingExact := source_direct_pending_factor_exact context state ledger
    scanner index item matcherMember
  have lookupExact := source_direct_lookup_factor_exact context state ledger
    scanner index item matcherMember
  have heapExact := source_direct_heap_factor_exact context state ledger scanner
    index item displayedLookup matcherMember
  have nodeExact := source_direct_node_factor_exact context state ledger scanner
    index nodeId node sourceOccurrence item itemExact displayedLookup nodeLookup
    occurrenceLookup matcherMember
  have machineExact := source_direct_machine_factor_exact context state ledger
    scanner index item matcherMember
  have successorExact := source_direct_successor_factor_exact context state ledger
    scanner index item matcherMember
  have pendingCovered := source_matcher_factor_covered context state ledger
    scanner index item directPendingTemplate
      (by simp [directProofPatterns]) matcherMember
  have heapCovered := source_matcher_factor_covered context state ledger scanner
    index item directHeapProofPattern
      (by simp [directProofPatterns]) matcherMember
  have nodeCovered := source_matcher_factor_covered context state ledger scanner
    index item directNodePattern
      (by simp [directProofPatterns]) matcherMember
  have machineCovered := source_matcher_factor_covered context state ledger
    scanner index item directMachineTemplate
      (by simp [directProofPatterns]) matcherMember
  have successorCovered := source_matcher_factor_covered context state ledger
    scanner index item directStackSuccessorPattern
      (by simp [directProofPatterns]) matcherMember
  exact
    ⟨direct_nextMachine_output_exact_of_factors directContext substitution
        pendingExact machineExact successorExact machineCovered
        successorCovered,
      direct_compactStack_output_exact_of_factors directContext item substitution
        pendingExact heapExact machineExact heapCovered
        machineCovered,
      direct_normalStack_output_exact_of_factors directContext item substitution
        pendingExact nodeExact machineExact nodeCovered
        machineCovered,
      direct_resumedScan_output_exact_of_factor directContext substitution
        pendingExact pendingCovered⟩

/-- Exactness of every ordinary matcher row transports to every compact-key
matcher row.  Physical matching contributes no new substitution. -/
theorem physicalDirectProofMatcherExact_of_reflective
    {context : DirectProofContext} {item : ProofOccurrence}
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space)
    (reflectiveExact : ReflectiveDirectProofMatcherExact context item space) :
    PhysicalDirectProofMatcherExact context item space := by
  intro substitution member
  have reflected := physicalDirectProofMatcherRows_subset_directProofMatcherRows
    listNodup morkNodup directivePresent member
  obtain ⟨nextMachine, compactStack, normalStack, resumedScan⟩ :=
    reflectiveExact substitution reflected
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact nextMachine
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact compactStack
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact normalStack
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact resumedScan
    · decide +kernel

/-- Physical compact-key matching preserves the exact source-derived static
outputs as well as the dynamic successor rows. -/
private theorem physical_direct_static_outputs_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence)
    (listNodup :
      (sourceProofRequestSpace context state ledger scanner index item).Nodup)
    (morkNodup : MorkSupportNodup
      (sourceProofRequestSpace context state ledger scanner index item))
    (directivePresent : speculativeDirectProofDirective.atom ∈
      sourceProofRequestSpace context state ledger scanner index item) :
    ∀ substitution ∈ physicalDirectProofMatcherRows
        (sourceProofRequestSpace context state ledger scanner index item),
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directProofSelfTemplate = some directProofReplayRule ∧
        instantiateRuleTemplateAtom?
            speculativeDirectProofDirective.rule.input substitution
            (.var "compressed-prefix-rule") = some compressedPrefixRule ∧
        instantiateRuleTemplateAtom?
            speculativeDirectProofDirective.rule.input substitution
            (.var "compressed-terminal-rule") =
          some MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule ∧
        instantiateRuleTemplateAtom?
            speculativeDirectProofDirective.rule.input substitution
            (.var "compressed-invalid-byte-rule") =
          some compressedInvalidByteRule ∧
        instantiateRuleTemplateAtom?
            speculativeDirectProofDirective.rule.input substitution
            (.var "compressed-question-rule") = some compressedQuestionRule ∧
        instantiateRuleTemplateAtom?
            speculativeDirectProofDirective.rule.input substitution
            (.var "compressed-question-open-fault-rule") =
          some compressedQuestionOpenFaultRule := by
  intro substitution physicalMember
  have reflectiveMember :=
    physicalDirectProofMatcherRows_subset_directProofMatcherRows listNodup
      morkNodup directivePresent physicalMember
  have selfExact := source_direct_self_output_exact context state ledger scanner
    index item reflectiveMember
  have runtimeExact := source_direct_runtime_outputs_exact context state ledger
    scanner index item reflectiveMember
  have probeCovered := source_matcher_factor_covered context state ledger scanner
    index item directProbeSelfPattern (by simp [directProofPatterns])
      reflectiveMember
  have prefixCovered := source_matcher_factor_covered context state ledger scanner
    index item (directOwnedRulePattern "prefix" "compressed-prefix-rule")
      (by simp [directProofPatterns]) reflectiveMember
  have terminalCovered := source_matcher_factor_covered context state ledger
    scanner index item
      (directOwnedRulePattern "terminal" "compressed-terminal-rule")
      (by simp [directProofPatterns]) reflectiveMember
  have invalidCovered := source_matcher_factor_covered context state ledger
    scanner index item
      (directOwnedRulePattern "invalid-byte" "compressed-invalid-byte-rule")
      (by simp [directProofPatterns]) reflectiveMember
  have questionCovered := source_matcher_factor_covered context state ledger
    scanner index item
      (directOwnedRulePattern "question" "compressed-question-rule")
      (by simp [directProofPatterns]) reflectiveMember
  have questionOpenCovered := source_matcher_factor_covered context state ledger
    scanner index item
      (directOwnedRulePattern "question-open-fault"
        "compressed-question-open-fault-rule")
      (by simp [directProofPatterns]) reflectiveMember
  have probeLocationCovered :
      templateCovered substitution speculativeDirectProofDirective.loc = true := by
    have locationExact : speculativeDirectProofDirective.loc =
        .expression
          [.symbol "00", .symbol "mm-compressed-direct-0-proof"] := by
      decide +kernel
    rw [locationExact]
    rfl
  have selfTemplateCovered :
      templateCovered substitution directProofSelfTemplate = true := by
    simpa [directProbeSelfPattern, directProofSelfTemplate, templateCovered,
      templatesCovered, probeLocationCovered] using probeCovered
  have prefixTemplateCovered :
      templateCovered substitution (.var "compressed-prefix-rule") = true := by
    simpa [directOwnedRulePattern, templateCovered, templatesCovered] using
      prefixCovered
  have terminalTemplateCovered :
      templateCovered substitution (.var "compressed-terminal-rule") = true := by
    simpa [directOwnedRulePattern, templateCovered, templatesCovered] using
      terminalCovered
  have invalidTemplateCovered :
      templateCovered substitution (.var "compressed-invalid-byte-rule") =
        true := by
    simpa [directOwnedRulePattern, templateCovered, templatesCovered] using
      invalidCovered
  have questionTemplateCovered :
      templateCovered substitution (.var "compressed-question-rule") = true := by
    simpa [directOwnedRulePattern, templateCovered, templatesCovered] using
      questionCovered
  have questionOpenTemplateCovered :
      templateCovered substitution
          (.var "compressed-question-open-fault-rule") = true := by
    simpa [directOwnedRulePattern, templateCovered, templatesCovered] using
      questionOpenCovered
  constructor
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        directProofSelfTemplate selfTemplateCovered).trans
          (congrArg some selfExact)
    · decide +kernel
  constructor
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        (.var "compressed-prefix-rule") prefixTemplateCovered).trans
          (congrArg some runtimeExact.1)
    · decide +kernel
  constructor
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        (.var "compressed-terminal-rule") terminalTemplateCovered).trans
          (congrArg some runtimeExact.2.1)
    · decide +kernel
  constructor
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        (.var "compressed-invalid-byte-rule") invalidTemplateCovered).trans
          (congrArg some runtimeExact.2.2.1)
    · decide +kernel
  constructor
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        (.var "compressed-question-rule") questionTemplateCovered).trans
          (congrArg some runtimeExact.2.2.2.1)
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        (.var "compressed-question-open-fault-rule")
          questionOpenTemplateCovered).trans
        (congrArg some runtimeExact.2.2.2.2)
    · decide +kernel

private theorem physical_direct_predecessor_controls_exact
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence)
    (listNodup :
      (sourceProofRequestSpace context state ledger scanner index item).Nodup)
    (morkNodup : MorkSupportNodup
      (sourceProofRequestSpace context state ledger scanner index item))
    (directivePresent : speculativeDirectProofDirective.atom ∈
      sourceProofRequestSpace context state ledger scanner index item) :
    ∀ substitution ∈ physicalDirectProofMatcherRows
        (sourceProofRequestSpace context state ledger scanner index item),
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directPendingTemplate =
        some (directContextAtBoundary context state scanner index).pendingRow ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directLookupTemplate =
        some (directContextAtBoundary context state scanner index).lookupRow ∧
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
          substitution directMachineTemplate =
        some (directContextAtBoundary context state scanner index).machineRow := by
  intro substitution physicalMember
  have reflectiveMember :=
    physicalDirectProofMatcherRows_subset_directProofMatcherRows listNodup
      morkNodup directivePresent physicalMember
  have pendingExact := source_direct_pending_factor_exact context state ledger
    scanner index item reflectiveMember
  have lookupExact := source_direct_lookup_factor_exact context state ledger
    scanner index item reflectiveMember
  have machineExact := source_direct_machine_factor_exact context state ledger
    scanner index item reflectiveMember
  have pendingCovered := source_matcher_factor_covered context state ledger
    scanner index item directPendingTemplate
      (by simp [directProofPatterns]) reflectiveMember
  have lookupCovered := source_matcher_factor_covered context state ledger
    scanner index item directLookupTemplate
      (by simp [directProofPatterns]) reflectiveMember
  have machineCovered := source_matcher_factor_covered context state ledger
    scanner index item directMachineTemplate
      (by simp [directProofPatterns]) reflectiveMember
  constructor
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        directPendingTemplate pendingCovered).trans (congrArg some pendingExact)
    · decide +kernel
  constructor
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        directLookupTemplate lookupCovered).trans (congrArg some lookupExact)
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact (instantiateTemplateAtom_of_covered substitution
        directMachineTemplate machineCovered).trans (congrArg some machineExact)
    · decide +kernel

/-- Every source-request row except the selected directive and its three
predecessor controls survives the complete physical direct-hit sink batch.
Compact-key separation is derived only on the generated request. -/
private theorem physical_direct_preserves_request_row
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence)
    (requestListNodup :
      (sourceProofRequestSpace context state ledger scanner index item).Nodup)
    (requestMorkNodup : MorkSupportNodup
      (sourceProofRequestSpace context state ledger scanner index item))
    (directivePresent : speculativeDirectProofDirective.atom ∈
      sourceProofRequestSpace context state ledger scanner index item)
    (row : Atom)
    (rowMember : row ∈
      sourceProofRequestSpace context state ledger scanner index item)
    (notDirective : row ≠ speculativeDirectProofDirective.atom)
    (notPending : row ≠
      (directContextAtBoundary context state scanner index).pendingRow)
    (notLookup : row ≠
      (directContextAtBoundary context state scanner index).lookupRow)
    (notMachine : row ≠
      (directContextAtBoundary context state scanner index).machineRow) :
    row ∈ cFireRuleScopedSourceExecFact
      (sourceProofRequestSpace context state ledger scanner index item)
      speculativeDirectProofDirective := by
  let request := sourceProofRequestSpace context state ledger scanner index item
  let directContext := directContextAtBoundary context state scanner index
  let rows := physicalDirectProofMatcherRows request
  have pendingMember : directContext.pendingRow ∈ request := by
    simp [request, directContext, sourceProofRequestSpace,
      canonicalDirectProofSpace]
  have lookupMember : directContext.lookupRow ∈ request := by
    simp [request, directContext, sourceProofRequestSpace,
      canonicalDirectProofSpace]
  have machineMember : directContext.machineRow ∈ request := by
    simp [request, directContext, sourceProofRequestSpace,
      canonicalDirectProofSpace]
  have notPendingKey :
      morkSupportKey row ≠ morkSupportKey directContext.pendingRow := by
    intro keysEqual
    exact notPending (morkSupportKey_injective_on requestMorkNodup rowMember
      pendingMember keysEqual)
  have notLookupKey :
      morkSupportKey row ≠ morkSupportKey directContext.lookupRow := by
    intro keysEqual
    exact notLookup (morkSupportKey_injective_on requestMorkNodup rowMember
      lookupMember keysEqual)
  have notMachineKey :
      morkSupportKey row ≠ morkSupportKey directContext.machineRow := by
    intro keysEqual
    exact notMachine (morkSupportKey_injective_on requestMorkNodup rowMember
      machineMember keysEqual)
  have liveMember : row ∈ morkEraseSupport request
      speculativeDirectProofDirective.atom := by
    rw [physical_direct_live_eq requestListNodup requestMorkNodup
      directivePresent]
    exact (List.mem_erase_of_ne notDirective).2 rowMember
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change row ∈ cApplyRuleScopedSinkBatch
    speculativeDirectProofDirective.rule.input rows
    (morkEraseSupport request speculativeDirectProofDirective.atom)
    speculativeDirectProofDirective.rule.tmpl.sinks
  apply mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
    speculativeDirectProofDirective.rule.input rows
  · intro sink sinkMember
    rw [speculative_direct_proof_sinks_exact] at sinkMember
    simp only [directProofSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨directPendingTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_direct_predecessor_controls_exact context state
            ledger scanner index item requestListNodup requestMorkNodup
              directivePresent substitution (by simpa [rows, request] using
                substitutionMember)
          have removedExact : removed = directContext.pendingRow :=
            Option.some.inj (instantiated.symm.trans exact.1)
          simpa [removedExact] using notPendingKey⟩
      | exact Or.inr ⟨directLookupTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_direct_predecessor_controls_exact context state
            ledger scanner index item requestListNodup requestMorkNodup
              directivePresent substitution (by simpa [rows, request] using
                substitutionMember)
          have removedExact : removed = directContext.lookupRow :=
            Option.some.inj (instantiated.symm.trans exact.2.1)
          simpa [removedExact] using notLookupKey⟩
      | exact Or.inr ⟨directMachineTemplate, rfl, by
          intro substitution substitutionMember removed instantiated
          have exact := physical_direct_predecessor_controls_exact context state
            ledger scanner index item requestListNodup requestMorkNodup
              directivePresent substitution (by simpa [rows, request] using
                substitutionMember)
          have removedExact : removed = directContext.machineRow :=
            Option.some.inj (instantiated.symm.trans exact.2.2)
          simpa [removedExact] using notMachineKey⟩
  · exact liveMember

/-- The canonical source-derived direct request is exact for every compact
physical matcher row. -/
theorem canonical_physical_direct_proof_matcher_exact
    (context : DirectProofContext) (item : ProofOccurrence)
    (listNodup : (canonicalDirectProofSpace context item).Nodup)
    (morkNodup : MorkSupportNodup
      (canonicalDirectProofSpace context item)) :
    PhysicalDirectProofMatcherExact context item
      (canonicalDirectProofSpace context item) := by
  apply physicalDirectProofMatcherExact_of_reflective listNodup morkNodup
  · simp [canonicalDirectProofSpace]
  · exact canonical_direct_proof_matcher_exact context item

/-- A physical direct-proof request contains the same exact source witness as
its reflective frame.  The witness is transported through the read
permutation; it is not supplied independently to physical execution. -/
theorem physical_direct_exact_match
    {Other : Type} {context : DirectProofContext} {item : ProofOccurrence}
    {before : SemanticState Other} {space : List Atom}
    (frame : DirectProofRequestFrame context item before space)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space) :
    PhysicalExactDirectProofMatch context item space := by
  rcases frame.exactMatch with
    ⟨substitution, substitutionMember, pending, lookup, machine,
      nextMachine, compactStack, normalStack, resumedScan⟩
  unfold directProofMatcherRows at substitutionMember
  rw [List.mem_map] at substitutionMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, matched, equal⟩ :=
    substitutionMember
  subst substitution
  have physicalMatched :
      (matchedSubstitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space speculativeDirectProofDirective.atom)
            speculativeDirectProofDirective.atom)
          speculativeDirectProofDirective.rule.input :=
    (physical_direct_matcher_mem_iff listNodup morkNodup directivePresent
      matchedSubstitution consumed).2 matched
  have physicalMember : matchedSubstitution ∈
      physicalDirectProofMatcherRows space := by
    unfold physicalDirectProofMatcherRows
    rw [List.mem_map]
    refine ⟨(matchedSubstitution, consumed), ?_, rfl⟩
    exact List.mem_filter.mpr ⟨physicalMatched, by
      change matchSourceGuards matchedSubstitution [] = true
      rfl⟩
  refine ⟨matchedSubstitution, physicalMember, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact pending
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact lookup
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact machine
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact nextMachine
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact compactStack
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact normalStack
    · decide +kernel
  · rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?]
    · exact resumedScan
    · decide +kernel

/-- The four dynamic successor rows produced by the direct proof handler are
present by physical support identity after the entire sink batch. -/
theorem physical_direct_dynamic_support_present
    {Other : Type} {context : DirectProofContext} {item : ProofOccurrence}
    {before : SemanticState Other} {space : List Atom}
    (frame : DirectProofRequestFrame context item before space)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space) :
    let result := cFireRuleScopedSourceExecFact space
      speculativeDirectProofDirective
    morkSupportContains result context.nextMachineRow = true ∧
      morkSupportContains result
        (compressedStackRow context.proofOwner context.stackPosition item) = true ∧
      morkSupportContains result
        (normalStackRow context.proofOwner context.stackPosition item) = true ∧
      morkSupportContains result context.resumedScanRow = true := by
  dsimp only
  let rows := physicalDirectProofMatcherRows space
  obtain ⟨substitution, substitutionMember, _pending, _lookup, _machine,
      nextMachine, compactStack, normalStack, resumedScan⟩ :=
    physical_direct_exact_match frame listNodup morkNodup directivePresent
  have addSupport (beforeSinks : List Sink) (authored candidate : Atom)
      (rest : List Sink)
      (sinkSplit : speculativeDirectProofDirective.rule.tmpl.sinks =
        beforeSinks ++ .add authored :: rest)
      (restAllAdds : ∀ sink ∈ rest, ∃ later, sink = .add later)
      (instantiates : instantiateRuleTemplateAtom?
        speculativeDirectProofDirective.rule.input substitution authored =
          some candidate) :
      morkSupportContains
        (cFireRuleScopedSourceExecFact space speculativeDirectProofDirective)
        candidate = true := by
    unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
    change morkSupportContains
      (cApplyRuleScopedSinkBatch speculativeDirectProofDirective.rule.input rows
        (morkEraseSupport space speculativeDirectProofDirective.atom)
        speculativeDirectProofDirective.rule.tmpl.sinks) candidate = true
    rw [sinkSplit]
    apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      speculativeDirectProofDirective.rule.input rows
      (morkEraseSupport space speculativeDirectProofDirective.atom)
      beforeSinks authored candidate rest substitution
      (by simpa [rows] using substitutionMember) instantiates
    intro sink sinkMember
    exact Or.inl (restAllAdds sink sinkMember)
  constructor
  · apply addSupport
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate]
      directNextMachineTemplate context.nextMachineRow
      [.add directStackCellTemplate, .add directNormalStackCellTemplate,
       .add directResumedScanTemplate]
    · exact speculative_direct_proof_sinks_exact
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · exact nextMachine
  constructor
  · apply addSupport
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate]
      directStackCellTemplate
      (compressedStackRow context.proofOwner context.stackPosition item)
      [.add directNormalStackCellTemplate, .add directResumedScanTemplate]
    · exact speculative_direct_proof_sinks_exact
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨_, rfl⟩
    · exact compactStack
  constructor
  · apply addSupport
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate,
        .add directStackCellTemplate]
      directNormalStackCellTemplate
      (normalStackRow context.proofOwner context.stackPosition item)
      [.add directResumedScanTemplate]
    · exact speculative_direct_proof_sinks_exact
    · intro sink member
      simp only [List.mem_singleton] at member
      subst sink
      exact ⟨_, rfl⟩
    · exact normalStack
  · apply addSupport
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate,
        .add directStackCellTemplate, .add directNormalStackCellTemplate]
      directResumedScanTemplate context.resumedScanRow []
    · exact speculative_direct_proof_sinks_exact
    · intro sink member
      simp at member
    · exact resumedScan

theorem DirectProofContext.nextMachineRow_ne_machineRow
    {context : DirectProofContext}
    (frontierMoves : context.nextStackPosition ≠ context.stackPosition) :
    context.nextMachineRow ≠ context.machineRow := by
  intro equal
  have atomsEqual := Atom.expression.inj equal
  have tail1 := (List.cons.inj atomsEqual).2
  have tail2 := (List.cons.inj tail1).2
  have tail3 := (List.cons.inj tail2).2
  have tail4 := (List.cons.inj tail3).2
  have tail5 := (List.cons.inj tail4).2
  have codeEqual := (List.cons.inj tail5).1
  have atomEqual :=
    MM2CompressedIndexSpine.CanonicalIndexCode.atom_injective codeEqual
  exact frontierMoves
    (MM2CompressedIndexSpine.CanonicalIndexCode.ofNat_injective atomEqual)

/-- The complete physical sink batch consumes all three predecessor controls.
The all-match premise prevents a second compatible match from recreating a
row after its authored remove sink. -/
theorem physical_direct_consumes_predecessor_controls
    {Other : Type} {context : DirectProofContext} {item : ProofOccurrence}
    {before : SemanticState Other} {space : List Atom}
    (frame : DirectProofRequestFrame context item before space)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space)
    (matcherExact : PhysicalDirectProofMatcherExact context item space)
    (frontierMoves : context.nextStackPosition ≠ context.stackPosition) :
    context.pendingRow ∉
        cFireRuleScopedSourceExecFact space speculativeDirectProofDirective ∧
      context.lookupRow ∉
        cFireRuleScopedSourceExecFact space speculativeDirectProofDirective ∧
      context.machineRow ∉
        cFireRuleScopedSourceExecFact space speculativeDirectProofDirective := by
  let rows := physicalDirectProofMatcherRows space
  obtain ⟨witness, witnessMember, witnessPending, witnessLookup,
      witnessMachine, _nextMachine, _compactStack, _normalStack,
      _resumedScan⟩ :=
    physical_direct_exact_match frame listNodup morkNodup directivePresent
  have outputExact : ∀ substitution ∈ rows,
      instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
            substitution directNextMachineTemplate =
          some context.nextMachineRow ∧
        instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
            substitution directStackCellTemplate =
          some (compressedStackRow context.proofOwner
            context.stackPosition item) ∧
        instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
            substitution directNormalStackCellTemplate =
          some (normalStackRow context.proofOwner context.stackPosition item) ∧
        instantiateRuleTemplateAtom? speculativeDirectProofDirective.rule.input
            substitution directResumedScanTemplate =
          some context.resumedScanRow := by
    intro substitution member
    exact matcherExact substitution (by simpa [rows] using member)
  have nextNotPending : context.nextMachineRow ≠ context.pendingRow := by
    simp [DirectProofContext.nextMachineRow, DirectProofContext.pendingRow]
  have compactNotPending :
      compressedStackRow context.proofOwner context.stackPosition item ≠
        context.pendingRow := by
    simp [compressedStackRow, DirectProofContext.pendingRow]
  have normalNotPending :
      normalStackRow context.proofOwner context.stackPosition item ≠
        context.pendingRow := by
    simp [normalStackRow, DirectProofContext.pendingRow]
  have scanNotPending : context.resumedScanRow ≠ context.pendingRow := by
    simp [DirectProofContext.resumedScanRow, DirectProofContext.pendingRow]
  have nextNotLookup : context.nextMachineRow ≠ context.lookupRow := by
    simp [DirectProofContext.nextMachineRow, DirectProofContext.lookupRow]
  have compactNotLookup :
      compressedStackRow context.proofOwner context.stackPosition item ≠
        context.lookupRow := by
    simp [compressedStackRow, DirectProofContext.lookupRow]
  have normalNotLookup :
      normalStackRow context.proofOwner context.stackPosition item ≠
        context.lookupRow := by
    simp [normalStackRow, DirectProofContext.lookupRow]
  have scanNotLookup : context.resumedScanRow ≠ context.lookupRow := by
    simp [DirectProofContext.resumedScanRow, DirectProofContext.lookupRow]
  have nextNotMachine :=
    Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDirectHit.DirectProofContext.nextMachineRow_ne_machineRow
      frontierMoves
  have compactNotMachine :
      compressedStackRow context.proofOwner context.stackPosition item ≠
        context.machineRow := by
    simp [compressedStackRow, DirectProofContext.machineRow]
  have normalNotMachine :
      normalStackRow context.proofOwner context.stackPosition item ≠
        context.machineRow := by
    simp [normalStackRow, DirectProofContext.machineRow]
  have scanNotMachine : context.resumedScanRow ≠ context.machineRow := by
    simp [DirectProofContext.resumedScanRow, DirectProofContext.machineRow]
  have pendingAbsent : context.pendingRow ∉
      cApplyRuleScopedSinkBatch speculativeDirectProofDirective.rule.input rows
        (morkEraseSupport space speculativeDirectProofDirective.atom)
        speculativeDirectProofDirective.rule.tmpl.sinks := by
    rw [speculative_direct_proof_sinks_exact]
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      speculativeDirectProofDirective.rule.input rows
      (morkEraseSupport space speculativeDirectProofDirective.atom)
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule")]
      directPendingTemplate context.pendingRow
      [.remove directLookupTemplate, .remove directMachineTemplate,
       .add directNextMachineTemplate, .add directStackCellTemplate,
       .add directNormalStackCellTemplate, .add directResumedScanTemplate]
      witness (by simpa [rows] using witnessMember) witnessPending
    intro sink member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨directLookupTemplate, rfl⟩
    · exact Or.inl ⟨directMachineTemplate, rfl⟩
    · exact Or.inr ⟨directNextMachineTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).1]
        exact fun equal => nextNotPending (Option.some.inj equal)⟩
    · exact Or.inr ⟨directStackCellTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.1]
        exact fun equal => compactNotPending (Option.some.inj equal)⟩
    · exact Or.inr ⟨directNormalStackCellTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.2.1]
        exact fun equal => normalNotPending (Option.some.inj equal)⟩
    · exact Or.inr ⟨directResumedScanTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.2.2]
        exact fun equal => scanNotPending (Option.some.inj equal)⟩
  have lookupAbsent : context.lookupRow ∉
      cApplyRuleScopedSinkBatch speculativeDirectProofDirective.rule.input rows
        (morkEraseSupport space speculativeDirectProofDirective.atom)
        speculativeDirectProofDirective.rule.tmpl.sinks := by
    rw [speculative_direct_proof_sinks_exact]
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      speculativeDirectProofDirective.rule.input rows
      (morkEraseSupport space speculativeDirectProofDirective.atom)
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate]
      directLookupTemplate context.lookupRow
      [.remove directMachineTemplate, .add directNextMachineTemplate,
       .add directStackCellTemplate, .add directNormalStackCellTemplate,
       .add directResumedScanTemplate]
      witness (by simpa [rows] using witnessMember) witnessLookup
    intro sink member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨directMachineTemplate, rfl⟩
    · exact Or.inr ⟨directNextMachineTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).1]
        exact fun equal => nextNotLookup (Option.some.inj equal)⟩
    · exact Or.inr ⟨directStackCellTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.1]
        exact fun equal => compactNotLookup (Option.some.inj equal)⟩
    · exact Or.inr ⟨directNormalStackCellTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.2.1]
        exact fun equal => normalNotLookup (Option.some.inj equal)⟩
    · exact Or.inr ⟨directResumedScanTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.2.2]
        exact fun equal => scanNotLookup (Option.some.inj equal)⟩
  have machineAbsent : context.machineRow ∉
      cApplyRuleScopedSinkBatch speculativeDirectProofDirective.rule.input rows
        (morkEraseSupport space speculativeDirectProofDirective.atom)
        speculativeDirectProofDirective.rule.tmpl.sinks := by
    rw [speculative_direct_proof_sinks_exact]
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      speculativeDirectProofDirective.rule.input rows
      (morkEraseSupport space speculativeDirectProofDirective.atom)
      [ .add directProofSelfTemplate,
        .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate]
      directMachineTemplate context.machineRow
      [.add directNextMachineTemplate, .add directStackCellTemplate,
       .add directNormalStackCellTemplate, .add directResumedScanTemplate]
      witness (by simpa [rows] using witnessMember) witnessMachine
    intro sink member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨directNextMachineTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).1]
        exact fun equal => nextNotMachine (Option.some.inj equal)⟩
    · exact Or.inr ⟨directStackCellTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.1]
        exact fun equal => compactNotMachine (Option.some.inj equal)⟩
    · exact Or.inr ⟨directNormalStackCellTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.2.1]
        exact fun equal => normalNotMachine (Option.some.inj equal)⟩
    · exact Or.inr ⟨directResumedScanTemplate, rfl, by
        intro substitution substitutionMember
        rw [(outputExact substitution substitutionMember).2.2.2]
        exact fun equal => scanNotMachine (Option.some.inj equal)⟩
  simpa [cFireRuleScopedSourceExecFact, cApplyRuleScopedTemplate, rows,
    physicalDirectProofMatcherRows] using
      And.intro pendingAbsent (And.intro lookupAbsent machineAbsent)

/-- On the canonical generated request, the complete physical sink batch
cannot leave or recreate any predecessor control. -/
theorem canonical_physical_direct_consumes_predecessor_controls
    {Other : Type} {context : DirectProofContext} {item : ProofOccurrence}
    {before : SemanticState Other}
    (frame : DirectProofRequestFrame context item before
      (canonicalDirectProofSpace context item))
    (listNodup : (canonicalDirectProofSpace context item).Nodup)
    (morkNodup : MorkSupportNodup
      (canonicalDirectProofSpace context item))
    (frontierMoves : context.nextStackPosition ≠ context.stackPosition) :
    context.pendingRow ∉ cFireRuleScopedSourceExecFact
        (canonicalDirectProofSpace context item)
        speculativeDirectProofDirective ∧
      context.lookupRow ∉ cFireRuleScopedSourceExecFact
        (canonicalDirectProofSpace context item)
        speculativeDirectProofDirective ∧
      context.machineRow ∉ cFireRuleScopedSourceExecFact
        (canonicalDirectProofSpace context item)
        speculativeDirectProofDirective := by
  exact physical_direct_consumes_predecessor_controls frame listNodup
    morkNodup (by simp [canonicalDirectProofSpace])
    (canonical_physical_direct_proof_matcher_exact context item listNodup
      morkNodup)
    frontierMoves

/-- The actual least-key rule-scoped scheduler selects the direct proof
handler on every exact direct request frame. -/
theorem physical_direct_ruleScoped_step
    {Other : Type} {context : DirectProofContext} {item : ProofOccurrence}
    {before : SemanticState Other} {space : List Atom}
    (frame : DirectProofRequestFrame context item before space) :
    cRuleScopedSourceWorkQueueStep .leaveInert space =
      some (cFireRuleScopedSourceExecFact space
        speculativeDirectProofDirective) := by
  unfold cRuleScopedSourceWorkQueueStep
  rw [select_direct_proof_of_supported_exact frame.supported]

/-- One physical direct hit is a nonempty rule-scoped MORK segment tied to
the semantic heap step and the exact OSLF-generated target type. -/
structure PhysicalDirectProofScheduledStep {Other : Type}
    (context : DirectProofContext) (item : ProofOccurrence)
    (before : SemanticState Other) (space : List Atom) : Prop where
  requestFrame : DirectProofRequestFrame context item before space
  listNodup : space.Nodup
  morkNodup : MorkSupportNodup space
  directivePresent : speculativeDirectProofDirective.atom ∈ space
  semanticStep : Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step before
    (semanticHitAfter context item before)
  exactPhysicalMatch : PhysicalExactDirectProofMatch context item space
  matcherExact : PhysicalDirectProofMatcherExact context item space
  concreteStep : cRuleScopedSourceWorkQueueStep .leaveInert space =
    some (cFireRuleScopedSourceExecFact space speculativeDirectProofDirective)
  nativeType :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (ruleScopedNativeListExecGSLT .leaveInert)).satisfies space
        (ruleScopedNativeListExactTargetNativeType .leaveInert
          (cFireRuleScopedSourceExecFact space
            speculativeDirectProofDirective)).pred
  dynamicSupport :
    let result := cFireRuleScopedSourceExecFact space
      speculativeDirectProofDirective
    morkSupportContains result context.nextMachineRow = true ∧
      morkSupportContains result
        (compressedStackRow context.proofOwner context.stackPosition item) = true ∧
      morkSupportContains result
        (normalStackRow context.proofOwner context.stackPosition item) = true ∧
      morkSupportContains result context.resumedScanRow = true
  predecessorControlsConsumed :
    context.pendingRow ∉
        cFireRuleScopedSourceExecFact space speculativeDirectProofDirective ∧
      context.lookupRow ∉
        cFireRuleScopedSourceExecFact space speculativeDirectProofDirective ∧
      context.machineRow ∉
        cFireRuleScopedSourceExecFact space speculativeDirectProofDirective
  resultListNodup :
    (cFireRuleScopedSourceExecFact space speculativeDirectProofDirective).Nodup
  resultMorkNodup : MorkSupportNodup
    (cFireRuleScopedSourceExecFact space speculativeDirectProofDirective)

def physical_direct_scheduled_step
    {Other : Type} {context : DirectProofContext} {item : ProofOccurrence}
    {before : SemanticState Other} {space : List Atom}
    (frame : DirectProofRequestFrame context item before space)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : speculativeDirectProofDirective.atom ∈ space)
    (reflectiveExact : ReflectiveDirectProofMatcherExact context item space)
    (frontierMoves : context.nextStackPosition ≠ context.stackPosition) :
    PhysicalDirectProofScheduledStep context item before space := by
  have moved := physical_direct_ruleScoped_step frame
  have matcherExact := physicalDirectProofMatcherExact_of_reflective listNodup
    morkNodup directivePresent reflectiveExact
  exact
    { requestFrame := frame
      listNodup := listNodup
      morkNodup := morkNodup
      directivePresent := directivePresent
      semanticStep := by
        cases before with
        | mk heap reserve control =>
            have controlEq := frame.control
            dsimp only at controlEq
            subst control
            exact Mettapedia.GSLT.SpeculativeFiniteHeapLookup.Step.hit
              heap reserve context.index (.occurrence item) frame.found
      exactPhysicalMatch :=
        physical_direct_exact_match frame listNodup morkNodup directivePresent
      matcherExact := matcherExact
      concreteStep := moved
      nativeType :=
        (satisfies_ruleScopedNativeListExactTargetNativeType_iff_step
          .leaveInert space
          (cFireRuleScopedSourceExecFact space
            speculativeDirectProofDirective)).2 moved
      dynamicSupport :=
        physical_direct_dynamic_support_present frame listNodup morkNodup
          directivePresent
      predecessorControlsConsumed :=
        physical_direct_consumes_predecessor_controls frame listNodup morkNodup
          directivePresent matcherExact frontierMoves
      resultListNodup :=
        cFireRuleScopedSourceExecFact_list_nodup space
          speculativeDirectProofDirective listNodup
      resultMorkNodup :=
        cFireRuleScopedSourceExecFact_mork_nodup space
          speculativeDirectProofDirective morkNodup }

/-- Every authored static row introduced by the direct proof handler remains
present after the complete sink batch.  The only intervening removals target
the three exact dynamic predecessor controls. -/
private theorem physical_source_direct_added_static_support_present
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) (item : ProofOccurrence)
    (scheduled :
      let request := sourceProofRequestSpace context state ledger scanner index
        item
      PhysicalDirectProofScheduledStep
        (directContextAtBoundary context state scanner index) item
        (displayedProofRequestState state ledger index) request) :
    let request := sourceProofRequestSpace context state ledger scanner index item
    let result := cFireRuleScopedSourceExecFact request
      speculativeDirectProofDirective
    ∀ row, row ∈ directProofAddedStaticRows →
      morkSupportContains result row = true := by
  dsimp only at scheduled ⊢
  let request := sourceProofRequestSpace context state ledger scanner index item
  let directContext := directContextAtBoundary context state scanner index
  let rows := physicalDirectProofMatcherRows request
  obtain ⟨substitution, substitutionMember, _pending, _lookup, _machine,
      _nextMachine, _compactStack, _normalStack, _resumedScan⟩ :=
    scheduled.exactPhysicalMatch
  have staticExact := physical_direct_static_outputs_exact context state ledger
    scanner index item scheduled.listNodup scheduled.morkNodup
    scheduled.directivePresent substitution substitutionMember
  have addSupport (beforeSinks : List Sink) (authored candidate : Atom)
      (rest : List Sink)
      (candidateMember : candidate ∈ directProofAddedStaticRows)
      (sinkSplit : speculativeDirectProofDirective.rule.tmpl.sinks =
        beforeSinks ++ .add authored :: rest)
      (instantiates : instantiateRuleTemplateAtom?
        speculativeDirectProofDirective.rule.input substitution authored =
          some candidate) :
      morkSupportContains
        (cFireRuleScopedSourceExecFact request speculativeDirectProofDirective)
        candidate = true := by
    have keySafe := directProofAddedStaticRows_key_ne_controls directContext
      candidate candidateMember
    unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
    change morkSupportContains
      (cApplyRuleScopedSinkBatch speculativeDirectProofDirective.rule.input rows
        (morkEraseSupport request speculativeDirectProofDirective.atom)
        speculativeDirectProofDirective.rule.tmpl.sinks) candidate = true
    rw [sinkSplit]
    apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      speculativeDirectProofDirective.rule.input rows
      (morkEraseSupport request speculativeDirectProofDirective.atom)
      beforeSinks authored candidate rest substitution
      (by simpa [rows] using substitutionMember) instantiates
    intro sink sinkMember
    have fullMember : sink ∈ speculativeDirectProofDirective.rule.tmpl.sinks := by
      rw [sinkSplit]
      simp [sinkMember]
    rw [speculative_direct_proof_sinks_exact] at fullMember
    simp only [directProofSinks, List.mem_cons, List.not_mem_nil, or_false]
      at fullMember
    rcases fullMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact Or.inl ⟨_, rfl⟩
      | exact Or.inr ⟨directPendingTemplate, rfl, by
          intro later laterMember removed exactRemoved
          have predecessor := physical_direct_predecessor_controls_exact context
            state ledger scanner index item scheduled.listNodup
            scheduled.morkNodup scheduled.directivePresent later
            (by simpa [rows, request] using laterMember)
          have removedExact : removed = directContext.pendingRow :=
            Option.some.inj (exactRemoved.symm.trans predecessor.1)
          simpa [removedExact] using keySafe.1⟩
      | exact Or.inr ⟨directLookupTemplate, rfl, by
          intro later laterMember removed exactRemoved
          have predecessor := physical_direct_predecessor_controls_exact context
            state ledger scanner index item scheduled.listNodup
            scheduled.morkNodup scheduled.directivePresent later
            (by simpa [rows, request] using laterMember)
          have removedExact : removed = directContext.lookupRow :=
            Option.some.inj (exactRemoved.symm.trans predecessor.2.1)
          simpa [removedExact] using keySafe.2.1⟩
      | exact Or.inr ⟨directMachineTemplate, rfl, by
          intro later laterMember removed exactRemoved
          have predecessor := physical_direct_predecessor_controls_exact context
            state ledger scanner index item scheduled.listNodup
            scheduled.morkNodup scheduled.directivePresent later
            (by simpa [rows, request] using laterMember)
          have removedExact : removed = directContext.machineRow :=
            Option.some.inj (exactRemoved.symm.trans predecessor.2.2)
          simpa [removedExact] using keySafe.2.2⟩
  intro row member
  simp only [directProofAddedStaticRows, directProofActivatedRuntimeRows,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact addSupport [] directProofSelfTemplate directProofReplayRule
      [ .add (.var "compressed-prefix-rule"),
        .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate,
        .add directStackCellTemplate, .add directNormalStackCellTemplate,
        .add directResumedScanTemplate]
      (by simp [directProofAddedStaticRows])
      speculative_direct_proof_sinks_exact staticExact.1
  · exact addSupport [.add directProofSelfTemplate]
      (.var "compressed-prefix-rule") compressedPrefixRule
      [ .add (.var "compressed-terminal-rule"),
        .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate,
        .add directStackCellTemplate, .add directNormalStackCellTemplate,
        .add directResumedScanTemplate]
      (by simp [directProofAddedStaticRows, directProofActivatedRuntimeRows])
      speculative_direct_proof_sinks_exact staticExact.2.1
  · exact addSupport
      [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule")]
      (.var "compressed-terminal-rule")
      MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule
      [ .add (.var "compressed-invalid-byte-rule"),
        .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate,
        .add directStackCellTemplate, .add directNormalStackCellTemplate,
        .add directResumedScanTemplate]
      (by simp [directProofAddedStaticRows, directProofActivatedRuntimeRows])
      speculative_direct_proof_sinks_exact staticExact.2.2.1
  · exact addSupport
      [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule")]
      (.var "compressed-invalid-byte-rule") compressedInvalidByteRule
      [ .add (.var "compressed-question-rule"),
        .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate,
        .add directStackCellTemplate, .add directNormalStackCellTemplate,
        .add directResumedScanTemplate]
      (by simp [directProofAddedStaticRows, directProofActivatedRuntimeRows])
      speculative_direct_proof_sinks_exact staticExact.2.2.2.1
  · exact addSupport
      [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-invalid-byte-rule")]
      (.var "compressed-question-rule") compressedQuestionRule
      [ .add (.var "compressed-question-open-fault-rule"),
        .remove directPendingTemplate, .remove directLookupTemplate,
        .remove directMachineTemplate, .add directNextMachineTemplate,
        .add directStackCellTemplate, .add directNormalStackCellTemplate,
        .add directResumedScanTemplate]
      (by simp [directProofAddedStaticRows, directProofActivatedRuntimeRows])
      speculative_direct_proof_sinks_exact staticExact.2.2.2.2.1
  · exact addSupport
      [.add directProofSelfTemplate, .add (.var "compressed-prefix-rule"),
       .add (.var "compressed-terminal-rule"),
       .add (.var "compressed-invalid-byte-rule"),
       .add (.var "compressed-question-rule")]
      (.var "compressed-question-open-fault-rule")
      compressedQuestionOpenFaultRule
      [.remove directPendingTemplate, .remove directLookupTemplate,
       .remove directMachineTemplate, .add directNextMachineTemplate,
       .add directStackCellTemplate, .add directNormalStackCellTemplate,
       .add directResumedScanTemplate]
      (by simp [directProofAddedStaticRows, directProofActivatedRuntimeRows])
      speculative_direct_proof_sinks_exact staticExact.2.2.2.2.2

/-- Passive source rows cannot be confused with the selected executable or
the pending, lookup, and machine controls consumed by a direct proof hit. -/
private theorem canonicalPassiveRows_ne_direct_controls
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index : Nat) {row : Atom}
    (member : row ∈ canonicalPassiveRows context state ledger) :
    row ≠ speculativeDirectProofDirective.atom ∧
      row ≠ (directContextAtBoundary context state scanner index).pendingRow ∧
      row ≠ (directContextAtBoundary context state scanner index).lookupRow ∧
      row ≠ (directContextAtBoundary context state scanner index).machineRow := by
  have heads := canonicalPassiveRows_head_cases context state ledger member
  constructor
  · intro equal
    subst row
    rw [speculativeDirectProofDirective_atom_exact] at heads
    simp [compressedDynamicRowHead?] at heads
  constructor
  · intro equal
    subst row
    simp [directContextAtBoundary, DirectProofContext.pendingRow,
      compressedDynamicRowHead?] at heads
  constructor
  · intro equal
    subst row
    simp [directContextAtBoundary, DirectProofContext.lookupRow,
      compressedDynamicRowHead?] at heads
  · intro equal
    subst row
    simp [directContextAtBoundary, DirectProofContext.machineRow,
      compressedDynamicRowHead?] at heads

/-- An executable directive cannot equal any of the three data/control rows
consumed by a direct proof hit. -/
private def directHasExecHead : Atom → Bool
  | .expression (.symbol "exec" :: _) => true
  | _ => false

private theorem exec_head_ne_direct_controls (context : DirectProofContext)
    (row : Atom) (execHead : directHasExecHead row = true) :
    row ≠ context.pendingRow ∧ row ≠ context.lookupRow ∧
      row ≠ context.machineRow := by
  constructor
  · intro equal
    subst row
    simp [DirectProofContext.pendingRow, directHasExecHead] at execHead
  constructor
  · intro equal
    subst row
    simp [DirectProofContext.lookupRow, directHasExecHead] at execHead
  · intro equal
    subst row
    simp [DirectProofContext.machineRow, directHasExecHead] at execHead

/-- No exact row outside the represented proof-action successor can survive
or be introduced by the complete physical direct-hit sink batch.  Every added
row is reconstructed from an authored sink and every retained passive row is
transported through the source stack update. -/
theorem physical_source_direct_result_rows_within_successor
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence} (index nodeId : Nat)
    (node : ProofNode source target)
    (receipt : ProofByteReceipt context scannerBefore scannerAfter
      byteOccurrence index)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node)
    (sourceOccurrence : Atom)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (ledgerAfter : NodeOccurrenceLedger
      ({ state with stack := state.stack ++ [nodeId] } :
        MachineState source target))
    (occurrencesExact : ledgerAfter.occurrences = ledger.occurrences)
    (scheduled :
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      let request := sourceProofRequestSpace context state ledger scannerAfter
        index item
      PhysicalDirectProofScheduledStep
        (directContextAtBoundary context state scannerAfter index) item
        (displayedProofRequestState state ledger index) request) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    let request := sourceProofRequestSpace context state ledger scannerAfter
      index item
    let result := cFireRuleScopedSourceExecFact request
      speculativeDirectProofDirective
    ∀ row, row ∈ result →
      row ∈ canonicalBoundaryRows context
          ({ state with stack := state.stack ++ [nodeId] } :
            MachineState source target)
          ledgerAfter scannerAfter ++
        directProofStaticFrame
          (directContextAtBoundary context state scannerAfter index) := by
  dsimp only at scheduled ⊢
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  let request := sourceProofRequestSpace context state ledger scannerAfter
    index item
  let directContext := directContextAtBoundary context state scannerAfter index
  let after : MachineState source target :=
    { state with stack := state.stack ++ [nodeId] }
  have displayedLookup :
      GetElem?.getElem? (displayedHeap state ledger) index =
        some (.occurrence item) := by
    obtain ⟨actualOccurrence, actualLookup, displayed⟩ :=
      displayedHeap_get_proof state ledger index nodeId node heapLookup
        nodeLookup
    have occurrenceEqual : actualOccurrence = sourceOccurrence := by
      rw [occurrenceLookup] at actualLookup
      exact (Option.some.inj actualLookup).symm
    simpa [item, occurrenceEqual] using displayed
  have heapPassive : heapProofRow context.proofOwner index item ∈
      canonicalPassiveRows context state ledger := by
    have encoded :=
      heapProofRow_mem_heapProofRowsFrom_of_getElem_occurrence
        context.proofOwner 0 index (displayedHeap state ledger) item
          displayedLookup
    simp only [canonicalPassiveRows, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl
      (by simpa [heapProofRows] using encoded))))
  have nodePassive :
      MM2CompressedProofHeapEncoding.nodeRow context.proofOwner item ∈
        canonicalPassiveRows context state ledger := by
    have encoded := sourceNodeRow_mem_sourceNodeRows_of_getElem
      context.proofOwner state ledger nodeId node sourceOccurrence nodeLookup
      occurrenceLookup
    simp only [canonicalPassiveRows, List.mem_append]
    exact Or.inl (Or.inl (Or.inr (by simpa [item] using encoded)))
  have passiveAfter (row : Atom)
      (member : row ∈ canonicalPassiveRows context state ledger) :
      row ∈ canonicalPassiveRows context after ledgerAfter := by
    exact (canonicalPassiveRows_push_mem_iff context state ledger nodeId node
      sourceOccurrence nodeLookup occurrenceLookup ledgerAfter occurrencesExact
      row).2 (Or.inl member)
  intro row member
  unfold cFireRuleScopedSourceExecFact at member
  change row ∈ cApplyRuleScopedTemplate
    speculativeDirectProofDirective.rule.input
    (morkEraseSupport request speculativeDirectProofDirective.atom)
    (physicalDirectProofMatcherRows request)
    speculativeDirectProofDirective.rule.tmpl at member
  rcases mem_cApplyRuleScopedTemplate_of_supportSet
      speculativeDirectProofDirective.rule.input
      (morkEraseSupport request speculativeDirectProofDirective.atom)
      (physicalDirectProofMatcherRows request)
      speculativeDirectProofDirective.rule.tmpl
      speculativeDirectProofDirective_supportSet member with prior | added
  · have requestMember : row ∈ request := (List.mem_filter.mp prior).1
    have erasedDifferent := (List.mem_filter.mp prior).2
    have sourceMember : row ∈ sourceProofRequestSpace context state ledger
        scannerAfter index item := by simpa [request] using requestMember
    rcases List.mem_append.mp sourceMember with direct | additional
    · simp only [canonicalDirectProofSpace, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at direct
      rcases direct with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl) | continuation
      · exact List.mem_append_right _
          (directProofStaticFrame_fixed_mem directContext (by simp))
      · exact List.mem_append_right _
          (directProofStaticFrame_fixed_mem directContext (by simp))
      · exact List.mem_append_right _
          (directProofStaticFrame_fixed_mem directContext (by simp))
      · exact List.mem_append_right _
          (directProofStaticFrame_fixed_mem directContext (by simp))
      · exfalso
        simp [sameMorkSupportAtom] at erasedDifferent
      · exact List.mem_append_right _
          (directProofStaticFrame_fixed_mem directContext (by simp))
      · exact False.elim (scheduled.predecessorControlsConsumed.1 member)
      · exact False.elim (scheduled.predecessorControlsConsumed.2.1 member)
      · apply List.mem_append_left
        simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false]
        exact Or.inr (passiveAfter _ heapPassive)
      · apply List.mem_append_left
        simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false]
        exact Or.inr (passiveAfter _ nodePassive)
      · exact False.elim (scheduled.predecessorControlsConsumed.2.2 member)
      · exact List.mem_append_right _
          (directProofStaticFrame_fixed_mem
            (directContextAtBoundary context state scannerAfter index) (by simp))
      · exact List.mem_append_right _
          (directProofStaticFrame_continuation_mem directContext continuation)
    · have oldPassive : row ∈ canonicalPassiveRows context state ledger :=
        (List.mem_filter.mp additional).1
      apply List.mem_append_left
      simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact Or.inr (passiveAfter row oldPassive)
  · rcases added with
      ⟨sink, sinkMember, authored, sinkExact, substitution,
        substitutionMember, instantiated⟩
    rw [speculative_direct_proof_sinks_exact] at sinkMember
    simp only [directProofSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    have staticExact := physical_direct_static_outputs_exact context state
      ledger scannerAfter index item scheduled.listNodup scheduled.morkNodup
      scheduled.directivePresent substitution substitutionMember
    have dynamicExact := scheduled.matcherExact substitution substitutionMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = directProofReplayRule :=
        Option.some.inj (instantiated.symm.trans staticExact.1)
      subst row
      exact List.mem_append_right _
        (directProofStaticFrame_fixed_mem directContext (by simp))
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = compressedPrefixRule :=
        Option.some.inj (instantiated.symm.trans staticExact.2.1)
      subst row
      exact List.mem_append_right _
        (directProofStaticFrame_activated_mem directContext (by simp
          [directProofActivatedRuntimeRows]))
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row =
          MM2CompressedProofSpeculativeHeapLookup.compressedSpeculativeTerminalRule :=
        Option.some.inj (instantiated.symm.trans staticExact.2.2.1)
      subst row
      exact List.mem_append_right _
        (directProofStaticFrame_activated_mem directContext (by simp
          [directProofActivatedRuntimeRows]))
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = compressedInvalidByteRule :=
        Option.some.inj (instantiated.symm.trans staticExact.2.2.2.1)
      subst row
      exact List.mem_append_right _
        (directProofStaticFrame_activated_mem directContext (by simp
          [directProofActivatedRuntimeRows]))
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = compressedQuestionRule :=
        Option.some.inj (instantiated.symm.trans staticExact.2.2.2.2.1)
      subst row
      exact List.mem_append_right _
        (directProofStaticFrame_activated_mem directContext (by simp
          [directProofActivatedRuntimeRows]))
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = compressedQuestionOpenFaultRule :=
        Option.some.inj (instantiated.symm.trans staticExact.2.2.2.2.2)
      subst row
      exact List.mem_append_right _
        (directProofStaticFrame_activated_mem directContext (by simp
          [directProofActivatedRuntimeRows]))
    · cases sinkExact
    · cases sinkExact
    · cases sinkExact
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = directContext.nextMachineRow :=
        Option.some.inj (instantiated.symm.trans dynamicExact.1)
      subst row
      apply List.mem_append_left
      have machineExact := directContextAtBoundary_nextMachineRow_eq_machineRow_push
        context state scannerAfter index nodeId
      simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact Or.inl (Or.inl (by simpa [directContext] using machineExact))
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = compressedStackRow context.proofOwner
          state.stack.length item := by
        simpa [directContext, directContextAtBoundary] using
          Option.some.inj (instantiated.symm.trans dynamicExact.2.1)
      subst row
      apply List.mem_append_left
      have addedStack := (canonicalPassiveRows_push_mem_iff context state ledger
        nodeId node sourceOccurrence nodeLookup occurrenceLookup ledgerAfter
        occurrencesExact _).2 (Or.inr (Or.inl rfl))
      simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact Or.inr (by simpa [after] using addedStack)
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = normalStackRow context.proofOwner
          state.stack.length item := by
        simpa [directContext, directContextAtBoundary] using
          Option.some.inj (instantiated.symm.trans dynamicExact.2.2.1)
      subst row
      apply List.mem_append_left
      have addedStack := (canonicalPassiveRows_push_mem_iff context state ledger
        nodeId node sourceOccurrence nodeLookup occurrenceLookup ledgerAfter
        occurrencesExact _).2 (Or.inr (Or.inr rfl))
      simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false]
      exact Or.inr (by simpa [after] using addedStack)
    · simp only [Sink.add.injEq] at sinkExact
      subst authored
      have rowExact : row = directContext.resumedScanRow :=
        Option.some.inj (instantiated.symm.trans dynamicExact.2.2.2)
      subst row
      apply List.mem_append_left
      have scannerExact := receipt.scannerRow_eq_resumedScanRow state
      simp [canonicalBoundaryRows, directContext, scannerExact]

/-- Every row in the complete source-derived proof-action successor is
present by physical support identity after the direct-hit sink batch. -/
theorem physical_source_direct_successor_support_complete
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence} (index nodeId : Nat)
    (node : ProofNode source target)
    (receipt : ProofByteReceipt context scannerBefore scannerAfter
      byteOccurrence index)
    (nodeLookup : state.nodes[nodeId]? = some node)
    (sourceOccurrence : Atom)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (ledgerAfter : NodeOccurrenceLedger
      ({ state with stack := state.stack ++ [nodeId] } :
        MachineState source target))
    (occurrencesExact : ledgerAfter.occurrences = ledger.occurrences)
    (scheduled :
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      let request := sourceProofRequestSpace context state ledger scannerAfter
        index item
      PhysicalDirectProofScheduledStep
        (directContextAtBoundary context state scannerAfter index) item
        (displayedProofRequestState state ledger index) request) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    let request := sourceProofRequestSpace context state ledger scannerAfter
      index item
    let result := cFireRuleScopedSourceExecFact request
      speculativeDirectProofDirective
    ∀ row, row ∈ canonicalBoundaryRows context
          ({ state with stack := state.stack ++ [nodeId] } :
            MachineState source target)
          ledgerAfter scannerAfter ++
        directProofStaticFrame
          (directContextAtBoundary context state scannerAfter index) →
      morkSupportContains result row = true := by
  dsimp only at scheduled ⊢
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  let request := sourceProofRequestSpace context state ledger scannerAfter
    index item
  let directContext := directContextAtBoundary context state scannerAfter index
  let after : MachineState source target :=
    { state with stack := state.stack ++ [nodeId] }
  let result := cFireRuleScopedSourceExecFact request
    speculativeDirectProofDirective
  have addedStatic := physical_source_direct_added_static_support_present
    context state ledger scannerAfter index item scheduled
  have preserveOld (row : Atom) (rowMember : row ∈ request)
      (notDirective : row ≠ speculativeDirectProofDirective.atom)
      (notPending : row ≠ directContext.pendingRow)
      (notLookup : row ≠ directContext.lookupRow)
      (notMachine : row ≠ directContext.machineRow) :
      morkSupportContains result row = true := by
    apply morkSupportContains_eq_true_of_mem
    exact physical_direct_preserves_request_row context state ledger scannerAfter
      index item scheduled.listNodup scheduled.morkNodup
      scheduled.directivePresent row (by simpa [request] using rowMember)
      notDirective (by simpa [directContext] using notPending)
      (by simpa [directContext] using notLookup)
      (by simpa [directContext] using notMachine)
  intro row member
  rcases List.mem_append.mp member with canonical | static
  · simp only [canonicalBoundaryRows, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at canonical
    rcases canonical with (machine | scanner) | passive
    · subst row
      have machineExact := directContextAtBoundary_nextMachineRow_eq_machineRow_push
        context state scannerAfter index nodeId
      rw [← machineExact]
      exact scheduled.dynamicSupport.1
    · subst row
      have scannerExact := receipt.scannerRow_eq_resumedScanRow state
      rw [scannerExact]
      exact scheduled.dynamicSupport.2.2.2
    · have passiveCases := (canonicalPassiveRows_push_mem_iff context state
        ledger nodeId node sourceOccurrence nodeLookup occurrenceLookup
        ledgerAfter occurrencesExact row).1 (by simpa [after] using passive)
      rcases passiveCases with old | compact | normal
      · have requestMember := canonicalPassiveRows_mem_sourceProofRequestSpace
          context state ledger scannerAfter index item old
        have avoids := canonicalPassiveRows_ne_direct_controls context state
          ledger scannerAfter index old
        exact preserveOld row (by simpa [request] using requestMember)
          avoids.1 (by simpa [directContext] using avoids.2.1)
          (by simpa [directContext] using avoids.2.2.1)
          (by simpa [directContext] using avoids.2.2.2)
      · subst row
        simpa [directContext, directContextAtBoundary] using
          scheduled.dynamicSupport.2.1
      · subst row
        simpa [directContext, directContextAtBoundary] using
          scheduled.dynamicSupport.2.2.1
  · simp only [directProofStaticFrame, List.mem_append] at static
    rcases static with (fixed | continuation) | activated
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at fixed
      rcases fixed with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · apply preserveOld
        · simp [request, sourceProofRequestSpace, canonicalDirectProofSpace]
        · decide +kernel
        · exact (exec_head_ne_direct_controls directContext
            compressedProofStepDirective.atom (by decide +kernel)).1
        · exact (exec_head_ne_direct_controls directContext
            compressedProofStepDirective.atom (by decide +kernel)).2.1
        · exact (exec_head_ne_direct_controls directContext
            compressedProofStepDirective.atom (by decide +kernel)).2.2
      · apply preserveOld
        · simp [request, sourceProofRequestSpace, canonicalDirectProofSpace]
        · decide +kernel
        · exact (exec_head_ne_direct_controls directContext
            compressedAssertionLaunchDirective.atom (by decide +kernel)).1
        · exact (exec_head_ne_direct_controls directContext
            compressedAssertionLaunchDirective.atom (by decide +kernel)).2.1
        · exact (exec_head_ne_direct_controls directContext
            compressedAssertionLaunchDirective.atom (by decide +kernel)).2.2
      · apply preserveOld
        · simp [request, sourceProofRequestSpace, canonicalDirectProofSpace]
        · decide +kernel
        · exact (exec_head_ne_direct_controls directContext
            compressedHeapLookupFaultDirective.atom (by decide +kernel)).1
        · exact (exec_head_ne_direct_controls directContext
            compressedHeapLookupFaultDirective.atom (by decide +kernel)).2.1
        · exact (exec_head_ne_direct_controls directContext
            compressedHeapLookupFaultDirective.atom (by decide +kernel)).2.2
      · apply preserveOld
        · simp [request, sourceProofRequestSpace, canonicalDirectProofSpace]
        · decide +kernel
        · exact (exec_head_ne_direct_controls directContext
            compressedHeapLookupAdvanceDirective.atom (by decide +kernel)).1
        · exact (exec_head_ne_direct_controls directContext
            compressedHeapLookupAdvanceDirective.atom (by decide +kernel)).2.1
        · exact (exec_head_ne_direct_controls directContext
            compressedHeapLookupAdvanceDirective.atom (by decide +kernel)).2.2
      · exact addedStatic directProofReplayRule
          (by simp [directProofAddedStaticRows])
      · apply preserveOld
        · simp [request, sourceProofRequestSpace, canonicalDirectProofSpace]
        · decide +kernel
        · exact (exec_head_ne_direct_controls directContext
            speculativeDirectAssertionDirective.atom (by decide +kernel)).1
        · exact (exec_head_ne_direct_controls directContext
            speculativeDirectAssertionDirective.atom (by decide +kernel)).2.1
        · exact (exec_head_ne_direct_controls directContext
            speculativeDirectAssertionDirective.atom (by decide +kernel)).2.2
      · apply preserveOld
        · simp [request, sourceProofRequestSpace, canonicalDirectProofSpace]
        · simp [speculativeDirectProofDirective_atom_exact,
            DirectProofContext.stackSuccessorRow, compressedIndexSuccessorRow]
        · simp [directContext, DirectProofContext.stackSuccessorRow,
            compressedIndexSuccessorRow, DirectProofContext.pendingRow]
        · simp [directContext, DirectProofContext.stackSuccessorRow,
            compressedIndexSuccessorRow, DirectProofContext.lookupRow]
        · simp [directContext, DirectProofContext.stackSuccessorRow,
            compressedIndexSuccessorRow, DirectProofContext.machineRow]
    · simp only [directProofContinuationRows, List.mem_cons,
        List.not_mem_nil, or_false] at continuation
      rcases continuation with rfl | rfl | rfl | rfl | rfl
      all_goals
        apply preserveOld
        · simp [request, sourceProofRequestSpace, canonicalDirectProofSpace,
            directProofContinuationRows]
        · simp [speculativeDirectProofDirective_atom_exact,
            compressedOwnedRuntimeRuleRow]
        · simp [directContext, DirectProofContext.pendingRow,
            compressedOwnedRuntimeRuleRow]
        · simp [directContext, DirectProofContext.lookupRow,
            compressedOwnedRuntimeRuleRow]
        · simp [directContext, DirectProofContext.machineRow,
            compressedOwnedRuntimeRuleRow]
    · exact addedStatic row (by
        simp [directProofAddedStaticRows, activated])

/-- With explicit duplicate-freedom of the compiler-produced successor, one
complete physical direct proof hit returns to the common running-boundary
relation.  The physical carrier is permutation-equivalent to the canonical
successor and retains compact-key uniqueness. -/
theorem physical_source_direct_returns_to_boundary_of_successor_nodup
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (wellFormed : SourceBoundaryWellFormed context state)
    (ledger : NodeOccurrenceLedger state)
    {scannerBefore scannerAfter : ScannerBoundary}
    {byteOccurrence : ByteOccurrence} (index nodeId : Nat)
    (node : ProofNode source target)
    (receipt : ProofByteReceipt context scannerBefore scannerAfter
      byteOccurrence index)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node)
    (sourceOccurrence : Atom)
    (occurrenceLookup : ledger.occurrences[nodeId]? = some sourceOccurrence)
    (sourceStep : ActionStep state (.step index)
      ({ state with stack := state.stack ++ [nodeId] } :
        MachineState source target))
    (ledgerAfter : NodeOccurrenceLedger
      ({ state with stack := state.stack ++ [nodeId] } :
        MachineState source target))
    (occurrencesExact : ledgerAfter.occurrences = ledger.occurrences)
    (scheduled :
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      let request := sourceProofRequestSpace context state ledger scannerAfter
        index item
      PhysicalDirectProofScheduledStep
        (directContextAtBoundary context state scannerAfter index) item
        (displayedProofRequestState state ledger index) request)
    (successorListNodup :
      (canonicalBoundaryRows context
          ({ state with stack := state.stack ++ [nodeId] } :
            MachineState source target)
          ledgerAfter scannerAfter ++
        directProofStaticFrame
          (directContextAtBoundary context state scannerAfter index)).Nodup)
    (successorMorkNodup : MorkSupportNodup
      (canonicalBoundaryRows context
          ({ state with stack := state.stack ++ [nodeId] } :
            MachineState source target)
          ledgerAfter scannerAfter ++
        directProofStaticFrame
          (directContextAtBoundary context state scannerAfter index))) :
    let item := displayedProofOccurrence nodeId node sourceOccurrence
    let request := sourceProofRequestSpace context state ledger scannerAfter
      index item
    PhysicalRunningBoundary context
      ({ state with stack := state.stack ++ [nodeId] } :
        MachineState source target)
      ledgerAfter scannerAfter
      (directProofStaticFrame
        (directContextAtBoundary context state scannerAfter index))
      (cFireRuleScopedSourceExecFact request
        speculativeDirectProofDirective) := by
  dsimp only at scheduled ⊢
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  let request := sourceProofRequestSpace context state ledger scannerAfter
    index item
  let result := cFireRuleScopedSourceExecFact request
    speculativeDirectProofDirective
  let successor := canonicalBoundaryRows context
      ({ state with stack := state.stack ++ [nodeId] } :
        MachineState source target)
      ledgerAfter scannerAfter ++
    directProofStaticFrame
      (directContextAtBoundary context state scannerAfter index)
  have within : ∀ row ∈ result, row ∈ successor := by
    intro row member
    simpa [result, successor, item, request] using
      physical_source_direct_result_rows_within_successor context state ledger
        index nodeId node receipt heapLookup nodeLookup sourceOccurrence
        occurrenceLookup ledgerAfter occurrencesExact scheduled row
        (by simpa [result, request] using member)
  have covered : ∀ row ∈ successor,
      morkSupportContains result row = true := by
    intro row member
    simpa [result, successor, item, request] using
      physical_source_direct_successor_support_complete context state ledger
        index nodeId node receipt nodeLookup sourceOccurrence occurrenceLookup
        ledgerAfter occurrencesExact scheduled row
        (by simpa [successor] using member)
  have exactRows : ∀ row, row ∈ result ↔ row ∈ successor := by
    intro row
    constructor
    · exact within row
    · intro member
      exact mem_of_morkSupportContains_of_reference successorMorkNodup member
        within (covered row member)
  have rowsPerm : result.Perm successor :=
    (List.perm_ext_iff_of_nodup scheduled.resultListNodup
      successorListNodup).2 exactRows
  exact
    { semantic :=
        { source_wellFormed := wellFormed.actionStep sourceStep
          staticFrame_clean := directProofStaticFrame_clean _
          exact_rows := by simpa [result, successor] using exactRows }
      rows_perm := by simpa [result, successor] using rowsPerm
      list_nodup := by simpa [result] using scheduled.resultListNodup
      mork_nodup := by simpa [result] using scheduled.resultMorkNodup }

/-- An arbitrary proof entry reconstructed from the source machine and
occurrence ledger performs the physical direct hit.  The only representation
premises are duplicate-freedom of the compiler-produced request itself. -/
theorem source_proof_lookup_physical_direct_step
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index nodeId : Nat) (node : ProofNode source target)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node)
    (requestListNodup : ∀ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      (sourceProofRequestSpace context state ledger scanner index
        (displayedProofOccurrence nodeId node sourceOccurrence)).Nodup)
    (requestMorkNodup : ∀ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      MorkSupportNodup
        (sourceProofRequestSpace context state ledger scanner index
          (displayedProofOccurrence nodeId node sourceOccurrence))) :
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      let item := displayedProofOccurrence nodeId node sourceOccurrence
      let request :=
        sourceProofRequestSpace context state ledger scanner index item
      PhysicalDirectProofScheduledStep
        (directContextAtBoundary context state scanner index) item
        (displayedProofRequestState state ledger index) request := by
  obtain ⟨sourceOccurrence, occurrenceLookup, frame⟩ :=
    source_proof_lookup_has_whole_state_request context state ledger scanner
      index nodeId node heapLookup nodeLookup
  obtain ⟨displayedOccurrence, displayedOccurrenceLookup, displayedLookup⟩ :=
    displayedHeap_get_proof state ledger index nodeId node heapLookup nodeLookup
  have displayedOccurrenceEqual : displayedOccurrence = sourceOccurrence := by
    rw [occurrenceLookup] at displayedOccurrenceLookup
    exact (Option.some.inj displayedOccurrenceLookup).symm
  subst displayedOccurrence
  let item := displayedProofOccurrence nodeId node sourceOccurrence
  have reflectiveExact : ReflectiveDirectProofMatcherExact
      (directContextAtBoundary context state scanner index) item
      (sourceProofRequestSpace context state ledger scanner index item) :=
    source_direct_proof_matcher_exact context state ledger scanner index nodeId
      node sourceOccurrence item rfl displayedLookup nodeLookup occurrenceLookup
  refine ⟨sourceOccurrence, occurrenceLookup, ?_⟩
  apply physical_direct_scheduled_step frame
    (requestListNodup sourceOccurrence occurrenceLookup)
    (requestMorkNodup sourceOccurrence occurrenceLookup)
  · simp [sourceProofRequestSpace, canonicalDirectProofSpace]
  · exact reflectiveExact
  · simp [directContextAtBoundary]

/-- Scanner-synchronised source proof action with an actual physical direct
MORK step.  The source action and physical matcher use the same decoded index,
node occurrence, stack frontier, and resumed scanner row. -/
theorem source_decoded_proof_action_physical_direct_step
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (wellFormed : SourceBoundaryWellFormed context state)
    (ledger : NodeOccurrenceLedger state) (proofPosition : Nat)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index nodeId : Nat)
    (node : ProofNode source target)
    (receipt : ProofByteReceipt context scannerBefore scannerAfter
      occurrence index)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node)
    (requestListNodup : ∀ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      (sourceProofRequestSpace context state ledger scannerAfter index
        (displayedProofOccurrence nodeId node sourceOccurrence)).Nodup)
    (requestMorkNodup : ∀ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      MorkSupportNodup
        (sourceProofRequestSpace context state ledger scannerAfter index
          (displayedProofOccurrence nodeId node sourceOccurrence))) :
    let after : MachineState source target :=
      { state with stack := state.stack ++ [nodeId] }
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      SourceStep (.request occurrence scannerBefore.phase)
        (.outcome occurrence (.decoded [.step index] scannerAfter.phase)) ∧
      ∃ sourceActionStep : ActionStep state (.step index) after,
        SourceBoundaryWellFormed context after ∧
        (ActionStep.occurrenceLedger sourceActionStep proofPosition
          ledger).occurrences = ledger.occurrences ∧
        let item := displayedProofOccurrence nodeId node sourceOccurrence
        let request :=
          sourceProofRequestSpace context state ledger scannerAfter index item
        PhysicalDirectProofScheduledStep
          (directContextAtBoundary context state scannerAfter index) item
          (displayedProofRequestState state ledger index) request := by
  let after : MachineState source target :=
    { state with stack := state.stack ++ [nodeId] }
  let sourceActionStep : ActionStep state (.step index) after :=
    .proof state index nodeId node heapLookup nodeLookup
  obtain ⟨sourceOccurrence, occurrenceLookup, physicalStep⟩ :=
    source_proof_lookup_physical_direct_step context state ledger scannerAfter
      index nodeId node heapLookup nodeLookup requestListNodup requestMorkNodup
  refine ⟨sourceOccurrence, occurrenceLookup, receipt.sourceStep,
    sourceActionStep, wellFormed.actionStep sourceActionStep, ?_, physicalStep⟩
  simp [ActionStep.occurrenceLedger, actionOccurrenceAtoms,
    heapOccurrenceKinds, heapLookup]

/-- A scanner-decoded proof byte, its source action, and the selected physical
MORK direct hit form one complete segment that returns to the shared running
boundary. -/
theorem source_decoded_proof_action_physical_direct_returns_to_boundary
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (wellFormed : SourceBoundaryWellFormed context state)
    (ledger : NodeOccurrenceLedger state) (proofPosition : Nat)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index nodeId : Nat)
    (node : ProofNode source target)
    (receipt : ProofByteReceipt context scannerBefore scannerAfter
      occurrence index)
    (heapLookup : state.heap[index]? = some (.proof nodeId))
    (nodeLookup : state.nodes[nodeId]? = some node)
    (requestListNodup : ∀ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      (sourceProofRequestSpace context state ledger scannerAfter index
        (displayedProofOccurrence nodeId node sourceOccurrence)).Nodup)
    (requestMorkNodup : ∀ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      MorkSupportNodup
        (sourceProofRequestSpace context state ledger scannerAfter index
          (displayedProofOccurrence nodeId node sourceOccurrence)))
    (successorListNodup : ∀ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      let sourceStep : ActionStep state (.step index)
          ({ state with stack := state.stack ++ [nodeId] } :
            MachineState source target) :=
        .proof state index nodeId node heapLookup nodeLookup
      let ledgerAfter := ActionStep.occurrenceLedger sourceStep proofPosition
        ledger
      (canonicalBoundaryRows context
          ({ state with stack := state.stack ++ [nodeId] } :
            MachineState source target)
          ledgerAfter scannerAfter ++
        directProofStaticFrame
          (directContextAtBoundary context state scannerAfter index)).Nodup)
    (successorMorkNodup : ∀ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence →
      let sourceStep : ActionStep state (.step index)
          ({ state with stack := state.stack ++ [nodeId] } :
            MachineState source target) :=
        .proof state index nodeId node heapLookup nodeLookup
      let ledgerAfter := ActionStep.occurrenceLedger sourceStep proofPosition
        ledger
      MorkSupportNodup
        (canonicalBoundaryRows context
            ({ state with stack := state.stack ++ [nodeId] } :
              MachineState source target)
            ledgerAfter scannerAfter ++
          directProofStaticFrame
            (directContextAtBoundary context state scannerAfter index))) :
    let after : MachineState source target :=
      { state with stack := state.stack ++ [nodeId] }
    ∃ sourceOccurrence,
      ledger.occurrences[nodeId]? = some sourceOccurrence ∧
      SourceStep (.request occurrence scannerBefore.phase)
        (.outcome occurrence (.decoded [.step index] scannerAfter.phase)) ∧
      let sourceStep : ActionStep state (.step index) after :=
        .proof state index nodeId node heapLookup nodeLookup
      let ledgerAfter := ActionStep.occurrenceLedger sourceStep proofPosition
        ledger
      SourceBoundaryWellFormed context after ∧
        ledgerAfter.occurrences = ledger.occurrences ∧
        let item := displayedProofOccurrence nodeId node sourceOccurrence
        let request := sourceProofRequestSpace context state ledger scannerAfter
          index item
        PhysicalRunningBoundary context after ledgerAfter scannerAfter
          (directProofStaticFrame
            (directContextAtBoundary context state scannerAfter index))
          (cFireRuleScopedSourceExecFact request
            speculativeDirectProofDirective) := by
  let after : MachineState source target :=
    { state with stack := state.stack ++ [nodeId] }
  let sourceStep : ActionStep state (.step index) after :=
    .proof state index nodeId node heapLookup nodeLookup
  obtain ⟨sourceOccurrence, occurrenceLookup, scheduled⟩ :=
    source_proof_lookup_physical_direct_step context state ledger scannerAfter
      index nodeId node heapLookup nodeLookup requestListNodup requestMorkNodup
  let ledgerAfter := ActionStep.occurrenceLedger sourceStep proofPosition ledger
  have occurrencesExact : ledgerAfter.occurrences = ledger.occurrences := by
    simp [ledgerAfter, sourceStep, ActionStep.occurrenceLedger,
      actionOccurrenceAtoms, heapOccurrenceKinds, heapLookup]
  have returned := physical_source_direct_returns_to_boundary_of_successor_nodup
    context state wellFormed ledger index nodeId node receipt heapLookup
      nodeLookup sourceOccurrence occurrenceLookup sourceStep ledgerAfter
      occurrencesExact scheduled
      (successorListNodup sourceOccurrence occurrenceLookup)
      (successorMorkNodup sourceOccurrence occurrenceLookup)
  refine ⟨sourceOccurrence, occurrenceLookup, receipt.sourceStep, ?_,
    occurrencesExact, ?_⟩
  · exact wellFormed.actionStep sourceStep
  · simpa [after, sourceStep, ledgerAfter] using returned

#print axioms speculativeDirectProofDirective_sinks_variablesInherited
#print axioms speculativeDirectProofDirective_supportSet
#print axioms directProofStaticFrame_clean
#print axioms physical_direct_live_eq
#print axioms physical_direct_read_perm
#print axioms physical_direct_matcher_mem_iff
#print axioms physicalDirectProofMatcherRows_subset_directProofMatcherRows
#print axioms physical_direct_exact_match
#print axioms physicalDirectProofMatcherExact_of_reflective
#print axioms canonical_physical_direct_proof_matcher_exact
#print axioms physical_direct_dynamic_support_present
#print axioms DirectProofContext.nextMachineRow_ne_machineRow
#print axioms physical_direct_consumes_predecessor_controls
#print axioms canonical_physical_direct_consumes_predecessor_controls
#print axioms physical_direct_ruleScoped_step
#print axioms physical_direct_scheduled_step
#print axioms physical_source_direct_result_rows_within_successor
#print axioms physical_source_direct_successor_support_complete
#print axioms physical_source_direct_returns_to_boundary_of_successor_nodup
#print axioms source_proof_lookup_physical_direct_step
#print axioms source_decoded_proof_action_physical_direct_step
#print axioms source_decoded_proof_action_physical_direct_returns_to_boundary

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDirectHit
