import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionBridgeOrigin
import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionRejoinOrigin
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalSupportHeadFaithfulness
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Physical launch of the decorated compressed assertion handler

The ordered verifier uses the decorated assertion directive produced by the
compiler.  This module transports its source-derived exact match to the
compact-key matcher used by rule-scoped MORK execution, then records the
selected transition and its OSLF-generated native type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedByteScannerGSLT
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionSourceBoundary
open Mettapedia.Languages.Metamath.MM2CompressedProofContinuousRepresentation
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionScheduleExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionSourceLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionBridgeOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionRejoinOrigin
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOccurrenceLedger
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalBridgeCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceAssertionRejoinCapability
open Mettapedia.Languages.Metamath.MM2CompressedProofSourceNormalBridgeCapability
open Mettapedia.Languages.Metamath.SourceGSLTCompressedTheorem
open Mettapedia.Languages.Metamath.SourceInferenceProjection
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- Substitutions enumerated by the actual compact-key assertion matcher. -/
def physicalDecoratedAssertionMatcherRows (space : List Atom) : List Subst :=
  let live := morkEraseSupport space decoratedDirectAssertionDirective.atom
  let read := morkInsertSupport live decoratedDirectAssertionDirective.atom
  ((cMatchInputSpecMork [] read decoratedDirectAssertionDirective.rule.input).filter
      fun (substitution, _) =>
        matchSourceGuards substitution
          decoratedDirectAssertionDirective.rule.guards).map Prod.fst

/-- A concrete reflective instantiation supplies exactly the coverage evidence
needed by rule-scoped instantiation.  This avoids re-normalizing the complete
compiler-produced directive to classify outputs unrelated to the witness. -/
private theorem instantiateRuleTemplateAtom?_of_reflective
    (input : InputSpec) {substitution : Subst} {template candidate : Atom}
    (instantiated : instantiateTemplateAtom? substitution template =
      some candidate) :
    instantiateRuleTemplateAtom? input substitution template =
      some candidate := by
  cases covered : templateCovered substitution template with
  | false => simp [instantiateTemplateAtom?, covered] at instantiated
  | true =>
      rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?_of_covered
        input substitution template covered]
      exact instantiated

/-- Compact-key removal agrees with ordinary erasure on a duplicate-free
physical request. -/
theorem physical_decorated_assertion_live_eq
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space) :
    morkEraseSupport space decoratedDirectAssertionDirective.atom =
      space.erase decoratedDirectAssertionDirective.atom := by
  exact morkEraseSupport_eq_erase_of_mem space
    decoratedDirectAssertionDirective.atom listNodup morkNodup directivePresent

/-- Physical insertion may choose a different list position, but presents the
same matcher input as the ordinary decorated assertion read. -/
theorem physical_decorated_assertion_read_perm
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space) :
    (morkInsertSupport
        (morkEraseSupport space decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.atom).Perm
      (decoratedDirectAssertionDirective.atom ::
        space.erase decoratedDirectAssertionDirective.atom) := by
  rw [physical_decorated_assertion_live_eq listNodup morkNodup
    directivePresent]
  have absent : morkSupportContains
      (space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.atom = false := by
    rw [← physical_decorated_assertion_live_eq listNodup morkNodup
      directivePresent]
    exact morkSupportContains_morkEraseSupport_self space
      decoratedDirectAssertionDirective.atom
  unfold morkInsertSupport
  rw [absent]
  exact List.perm_append_singleton decoratedDirectAssertionDirective.atom
    (space.erase decoratedDirectAssertionDirective.atom)

/-- Compatible decorated-assertion matching is invariant under the physical
support presentation. -/
theorem physical_decorated_assertion_matcher_mem_iff
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (substitution : Subst) (consumed : List Atom) :
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space decoratedDirectAssertionDirective.atom)
            decoratedDirectAssertionDirective.atom)
          decoratedDirectAssertionDirective.rule.input ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (decoratedDirectAssertionDirective.atom ::
            space.erase decoratedDirectAssertionDirective.atom)
          decoratedDirectAssertionDirective.rule.input := by
  rw [decoratedDirectAssertionDirective_input_exact]
  unfold cMatchInputSpecMork Conformance.Computable.cmatchInputSpec
  have readPerm := physical_decorated_assertion_read_perm listNodup morkNodup
    directivePresent
  constructor
  · intro member
    exact Conformance.Computable.cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mp atomMember)
      substitution consumed member
  · intro member
    exact Conformance.Computable.cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mpr atomMember)
      substitution consumed member

/-- Every compact physical matcher row is an ordinary decorated assertion
matcher row over the same request. -/
theorem physicalDecoratedAssertionMatcherRows_subset
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    {substitution : Subst}
    (member : substitution ∈ physicalDecoratedAssertionMatcherRows space) :
    substitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (decoratedDirectAssertionDirective.atom ::
          space.erase decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.input).map Prod.fst := by
  unfold physicalDecoratedAssertionMatcherRows at member
  rw [List.mem_map] at member
  obtain ⟨⟨matchedSubstitution, consumed⟩, filtered, equal⟩ := member
  have physicalMatched := (List.mem_filter.mp filtered).1
  have ordinaryMatched :=
    (physical_decorated_assertion_matcher_mem_iff listNodup morkNodup
      directivePresent matchedSubstitution consumed).1 physicalMatched
  subst substitution
  exact List.mem_map_of_mem ordinaryMatched

theorem directAssertionPendingTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionPendingTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

theorem directAssertionLookupTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionLookupTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

theorem directAssertionMachineTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionMachineTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionContextTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionContextTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionNormalControlTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionNormalControlTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionNormalLabelTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionNormalLabelTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionReloadTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      directAssertionReloadTemplate = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionRejoinTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      (.var "compressed-assertion-rejoin-rule") = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem directAssertionBridgeTemplate_inherited :
    ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      (.var "normal-bridge-rule") = true := by
  rw [decoratedDirectAssertionDirective_input_exact]
  decide +kernel

private theorem instantiateRuleTemplateAtom?_expression_symbol_head_ne
    (substitution : Subst) (authoredHead candidateHead : String)
    (authoredTail candidateTail : List Atom)
    (inherited : ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      (.expression (.symbol authoredHead :: authoredTail)) = true)
    (different : authoredHead ≠ candidateHead) :
    instantiateRuleTemplateAtom?
        decoratedDirectAssertionDirective.rule.input substitution
        (.expression (.symbol authoredHead :: authoredTail)) ≠
      some (.expression (.symbol candidateHead :: candidateTail)) := by
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    _ _ _ inherited]
  exact
    Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable.instantiateTemplateAtom?_expression_symbol_head_ne
      substitution authoredHead candidateHead authoredTail candidateTail
      different

private theorem physicalMatcherRow_rejoin_exact
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (capabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows space)
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      (.var "compressed-assertion-rejoin-rule") = some payload) :
    payload = compressedAssertionRejoinRule := by
  have ordinary := physicalDecoratedAssertionMatcherRows_subset listNodup
    morkNodup directivePresent rowMember
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    _ _ _ directAssertionRejoinTemplate_inherited] at instantiates
  exact decoratedAssertionMatcherRow_rejoin_exact capabilities ordinary
    instantiates

private theorem physicalMatcherRow_bridge_exact
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (capabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space)
    {substitution : Subst} {payload : Atom}
    (rowMember : substitution ∈ physicalDecoratedAssertionMatcherRows space)
    (instantiates : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      (.var "normal-bridge-rule") = some payload) :
    payload = compressedNormalDispatchBridgeRule := by
  have ordinary := physicalDecoratedAssertionMatcherRows_subset listNodup
    morkNodup directivePresent rowMember
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    _ _ _ directAssertionBridgeTemplate_inherited] at instantiates
  exact decoratedAssertionMatcherRow_bridge_exact capabilities ordinary
    instantiates
/-- Exact source-derived outputs reconstructed by a compact physical matcher
row. -/
def PhysicalExactDecoratedAssertionLaunch
    (context : DirectAssertionContext) (space : List Atom) : Prop :=
  ∃ substitution ∈ physicalDecoratedAssertionMatcherRows space,
    instantiateRuleTemplateAtom? decoratedDirectAssertionDirective.rule.input
          substitution directAssertionPendingTemplate =
        some context.pendingRow ∧
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionLookupTemplate = some context.lookupRow ∧
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionMachineTemplate = some context.machineRow ∧
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionContextTemplate = some context.assertionContextRow ∧
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionNormalControlTemplate = some context.normalControlRow ∧
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionNormalLabelTemplate = some context.normalLabelRow ∧
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionReloadTemplate = some context.reloadRow ∧
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule ∧
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          (.var "normal-bridge-rule") =
        some compressedNormalDispatchBridgeRule

/-- Transport an independently established decorated assertion match into the
actual compact-key matcher used by MORK. -/
theorem physical_decorated_assertion_exact_match
    {context : DirectAssertionContext} {space : List Atom}
    (matched : ExactDecoratedDirectAssertionLaunch context space)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space) :
    PhysicalExactDecoratedAssertionLaunch context space := by
  rcases matched with
    ⟨substitution, substitutionMember, pending, lookup, machine,
      assertionContext, normalControl, normalLabel, reload, rejoin, bridge⟩
  rw [List.mem_map] at substitutionMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, ordinaryMatched, equal⟩ :=
    substitutionMember
  subst substitution
  have physicalMatched :
      (matchedSubstitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space decoratedDirectAssertionDirective.atom)
            decoratedDirectAssertionDirective.atom)
          decoratedDirectAssertionDirective.rule.input :=
    (physical_decorated_assertion_matcher_mem_iff listNodup morkNodup
      directivePresent matchedSubstitution consumed).2 ordinaryMatched
  have physicalMember : matchedSubstitution ∈
      physicalDecoratedAssertionMatcherRows space := by
    unfold physicalDecoratedAssertionMatcherRows
    rw [List.mem_map]
    refine ⟨(matchedSubstitution, consumed), ?_, rfl⟩
    exact List.mem_filter.mpr ⟨physicalMatched, by
      rw [decoratedDirectAssertionDirective_guards_exact]
      rfl⟩
  refine ⟨matchedSubstitution, physicalMember, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact instantiateRuleTemplateAtom?_of_reflective _ pending
  · exact instantiateRuleTemplateAtom?_of_reflective _ lookup
  · exact instantiateRuleTemplateAtom?_of_reflective _ machine
  · exact instantiateRuleTemplateAtom?_of_reflective _ assertionContext
  · exact instantiateRuleTemplateAtom?_of_reflective _ normalControl
  · exact instantiateRuleTemplateAtom?_of_reflective _ normalLabel
  · exact instantiateRuleTemplateAtom?_of_reflective _ reload
  · exact instantiateRuleTemplateAtom?_of_reflective _ rejoin
  · exact instantiateRuleTemplateAtom?_of_reflective _ bridge

/-- Every sink of the decorated assertion launcher is a physical support-set
addition or removal. -/
theorem decoratedDirectAssertionDirective_supportSet :
    ReflectiveSupportSetTemplate decoratedDirectAssertionDirective.rule.tmpl := by
  rw [← all_reflectiveSupportSetSinkB_eq_true_iff]
  rw [decoratedDirectAssertionDirective_sinks_exact]
  decide +kernel

/-- The six normal-handoff rows produced by one exact physical matcher remain
present after the complete rule-scoped sink batch. -/
theorem physical_decorated_assertion_launch_support_present
    {context : DirectAssertionContext} {space : List Atom}
    (matched : ExactDecoratedDirectAssertionLaunch context space)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space) :
    let result := cFireRuleScopedSourceExecFact space
      decoratedDirectAssertionDirective
    morkSupportContains result context.assertionContextRow = true ∧
      morkSupportContains result context.normalControlRow = true ∧
      morkSupportContains result context.normalLabelRow = true ∧
      morkSupportContains result context.reloadRow = true ∧
      morkSupportContains result compressedAssertionRejoinRule = true ∧
      morkSupportContains result compressedNormalDispatchBridgeRule = true := by
  dsimp only
  let rows := physicalDecoratedAssertionMatcherRows space
  obtain ⟨substitution, substitutionMember, _pending, _lookup, _machine,
      assertionContext, normalControl, normalLabel, reload, rejoin, bridge⟩ :=
    physical_decorated_assertion_exact_match matched listNodup morkNodup
      directivePresent
  have addSupport (beforeSinks : List Sink) (authored candidate : Atom)
      (rest : List Sink)
      (sinkSplit : decoratedDirectAssertionDirective.rule.tmpl.sinks =
        beforeSinks ++ .add authored :: rest)
      (restAllAdds : ∀ sink ∈ rest, ∃ later, sink = .add later)
      (instantiates : instantiateRuleTemplateAtom?
        decoratedDirectAssertionDirective.rule.input substitution authored =
          some candidate) :
      morkSupportContains
        (cFireRuleScopedSourceExecFact space
          decoratedDirectAssertionDirective) candidate = true := by
    unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
    change morkSupportContains
      (cApplyRuleScopedSinkBatch
        decoratedDirectAssertionDirective.rule.input rows
        (morkEraseSupport space decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.tmpl.sinks) candidate = true
    rw [sinkSplit]
    apply morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      decoratedDirectAssertionDirective.rule.input rows
      (morkEraseSupport space decoratedDirectAssertionDirective.atom)
      beforeSinks authored candidate rest substitution
      (by simpa [rows] using substitutionMember) instantiates
    intro sink sinkMember
    exact Or.inl (restAllAdds sink sinkMember)
  constructor
  · apply addSupport
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate]
      directAssertionContextTemplate context.assertionContextRow
      [.add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate,
       .add directAssertionReloadTemplate,
       .add (.var "compressed-assertion-rejoin-rule"),
       .add (.var "normal-bridge-rule")]
    · exact decoratedDirectAssertionDirective_sinks_exact
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · exact assertionContext
  constructor
  · apply addSupport
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate]
      directAssertionNormalControlTemplate context.normalControlRow
      [.add directAssertionNormalLabelTemplate,
       .add directAssertionReloadTemplate,
       .add (.var "compressed-assertion-rejoin-rule"),
       .add (.var "normal-bridge-rule")]
    · exact decoratedDirectAssertionDirective_sinks_exact
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · exact normalControl
  constructor
  · apply addSupport
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate]
      directAssertionNormalLabelTemplate context.normalLabelRow
      [.add directAssertionReloadTemplate,
       .add (.var "compressed-assertion-rejoin-rule"),
       .add (.var "normal-bridge-rule")]
    · exact decoratedDirectAssertionDirective_sinks_exact
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    · exact normalLabel
  constructor
  · apply addSupport
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate]
      directAssertionReloadTemplate context.reloadRow
      [.add (.var "compressed-assertion-rejoin-rule"),
       .add (.var "normal-bridge-rule")]
    · exact decoratedDirectAssertionDirective_sinks_exact
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨_, rfl⟩
    · exact reload
  constructor
  · apply addSupport
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate,
       .add directAssertionReloadTemplate]
      (.var "compressed-assertion-rejoin-rule")
      compressedAssertionRejoinRule
      [.add (.var "normal-bridge-rule")]
    · exact decoratedDirectAssertionDirective_sinks_exact
    · intro sink member
      simp only [List.mem_singleton] at member
      subst sink
      exact ⟨_, rfl⟩
    · exact rejoin
  · apply addSupport
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate,
       .add directAssertionReloadTemplate,
       .add (.var "compressed-assertion-rejoin-rule")]
      (.var "normal-bridge-rule") compressedNormalDispatchBridgeRule []
    · exact decoratedDirectAssertionDirective_sinks_exact
    · intro sink member
      simp at member
    · exact bridge

/-- Executable authority introduced by a physical decorated-assertion launch
is confined to the two compiler-captured continuations.  The four ordinary
normal-interface outputs retain non-executable symbolic heads under every
physical matcher row. -/
def DecoratedAssertionGeneratedSupportedAtom (atom : Atom) : Prop :=
  ∀ candidate, extractSupportedSourceExecFact atom = some candidate →
    candidate = compressedAssertionRejoinDirective ∨
      candidate = compressedNormalDispatchBridgeDirective

/-- Every row published by the assertion launcher has one of the four normal
handoff heads or the executable head of a captured continuation. -/
def DecoratedAssertionPublishedAtom (atom : Atom) : Prop :=
  compressedDynamicRowHead? atom = some "mm-compressed-assertion-context" ∨
    compressedDynamicRowHead? atom = some "mm-normal-control" ∨
    compressedDynamicRowHead? atom = some "mm-linked-row" ∨
    compressedDynamicRowHead? atom =
      some "mm-reload-compressed-normal-dispatch" ∨
    compressedDynamicRowHead? atom = some "exec"

/-- Exact publication classification: ordinary handoff rows retain their
constructor head, while executable outputs are the two captured continuations
themselves. -/
def DecoratedAssertionExactPublishedAtom (atom : Atom) : Prop :=
  compressedDynamicRowHead? atom = some "mm-compressed-assertion-context" ∨
    compressedDynamicRowHead? atom = some "mm-normal-control" ∨
    compressedDynamicRowHead? atom = some "mm-linked-row" ∨
    compressedDynamicRowHead? atom =
      some "mm-reload-compressed-normal-dispatch" ∨
    atom = compressedAssertionRejoinRule ∨
    atom = compressedNormalDispatchBridgeRule

private theorem instantiated_inherited_expression_head
    (substitution : Subst) (head : String) (tail : List Atom)
    (inherited : ruleTemplateVariablesInherited
      decoratedDirectAssertionDirective.rule.input
      (.expression (.symbol head :: tail)) = true)
    {atom : Atom}
    (instantiated : instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      (.expression (.symbol head :: tail)) = some atom) :
    compressedDynamicRowHead? atom = some head := by
  rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
    _ _ _ inherited] at instantiated
  cases covered : templateCovered substitution
      (.expression (.symbol head :: tail)) with
  | false => simp [instantiateTemplateAtom?, covered] at instantiated
  | true =>
      have instantiatedExact := instantiateTemplateAtom_of_covered substitution
        (.expression (.symbol head :: tail)) covered
      have atomExact : atom = applySubst substitution
          (.expression (.symbol head :: tail)) :=
        Option.some.inj (instantiated.symm.trans instantiatedExact)
      subst atom
      rw [applySubst_expression_symbol]
      rfl

theorem physical_decorated_assertion_additions_supported_origin
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    (bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space) :
    RuleScopedTemplateAdditionsWithin
      DecoratedAssertionGeneratedSupportedAtom
      decoratedDirectAssertionDirective.rule.input
      (physicalDecoratedAssertionMatcherRows space)
      decoratedDirectAssertionDirective.rule.tmpl := by
  intro sink sinkMember
  rw [decoratedDirectAssertionDirective_sinks_exact] at sinkMember
  simp only [decoratedDirectAssertionSinks, directAssertionSinks,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at sinkMember
  rcases sinkMember with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      rfl
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · intro substitution _ atom instantiated candidate extracted
    obtain ⟨location, input, output, atomShape⟩ :=
      extractSupportedSourceExecFact_exec_shape extracted
    rw [atomShape] at instantiated
    exact False.elim
      (instantiateRuleTemplateAtom?_expression_symbol_head_ne substitution
        "mm-compressed-assertion-context" "exec" _ _
        directAssertionContextTemplate_inherited (by decide) instantiated)
  · intro substitution _ atom instantiated candidate extracted
    obtain ⟨location, input, output, atomShape⟩ :=
      extractSupportedSourceExecFact_exec_shape extracted
    rw [atomShape] at instantiated
    exact False.elim
      (instantiateRuleTemplateAtom?_expression_symbol_head_ne substitution
        "mm-normal-control" "exec" _ _
        directAssertionNormalControlTemplate_inherited (by decide) instantiated)
  · intro substitution _ atom instantiated candidate extracted
    obtain ⟨location, input, output, atomShape⟩ :=
      extractSupportedSourceExecFact_exec_shape extracted
    rw [atomShape] at instantiated
    exact False.elim
      (instantiateRuleTemplateAtom?_expression_symbol_head_ne substitution
        "mm-linked-row" "exec" _ _
        directAssertionNormalLabelTemplate_inherited (by decide) instantiated)
  · intro substitution _ atom instantiated candidate extracted
    obtain ⟨location, input, output, atomShape⟩ :=
      extractSupportedSourceExecFact_exec_shape extracted
    rw [atomShape] at instantiated
    exact False.elim
      (instantiateRuleTemplateAtom?_expression_symbol_head_ne substitution
        "mm-reload-compressed-normal-dispatch" "exec" _ _
        directAssertionReloadTemplate_inherited (by decide) instantiated)
  · intro substitution substitutionMember atom instantiated candidate extracted
    have atomExact := physicalMatcherRow_rejoin_exact listNodup morkNodup
      directivePresent rejoinCapabilities substitutionMember instantiated
    subst atom
    rw [extract_compressedAssertionRejoinRule_exact] at extracted
    exact Or.inl (Option.some.inj extracted).symm
  · intro substitution substitutionMember atom instantiated candidate extracted
    have atomExact := physicalMatcherRow_bridge_exact listNodup morkNodup
      directivePresent bridgeCapabilities substitutionMember instantiated
    subst atom
    rw [extract_compressedNormalDispatchBridgeRule_exact] at extracted
    exact Or.inr (Option.some.inj extracted).symm

/-- The launch sink batch cannot publish a row under an unrelated dynamic
head.  This is the representation-level fact used to prove that predecessor
controls are not recreated under a different payload. -/
theorem physical_decorated_assertion_additions_published
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    (bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space) :
    RuleScopedTemplateAdditionsWithin
      DecoratedAssertionPublishedAtom
      decoratedDirectAssertionDirective.rule.input
      (physicalDecoratedAssertionMatcherRows space)
      decoratedDirectAssertionDirective.rule.tmpl := by
  intro sink sinkMember
  rw [decoratedDirectAssertionDirective_sinks_exact] at sinkMember
  simp only [decoratedDirectAssertionSinks, directAssertionSinks,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at sinkMember
  rcases sinkMember with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      rfl
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · intro substitution _ atom instantiated
    exact Or.inl (instantiated_inherited_expression_head substitution
      "mm-compressed-assertion-context" _
      directAssertionContextTemplate_inherited instantiated)
  · intro substitution _ atom instantiated
    exact Or.inr (Or.inl (instantiated_inherited_expression_head substitution
      "mm-normal-control" _ directAssertionNormalControlTemplate_inherited
      instantiated))
  · intro substitution _ atom instantiated
    exact Or.inr (Or.inr (Or.inl
      (instantiated_inherited_expression_head substitution "mm-linked-row" _
        directAssertionNormalLabelTemplate_inherited instantiated)))
  · intro substitution _ atom instantiated
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (instantiated_inherited_expression_head substitution
        "mm-reload-compressed-normal-dispatch" _
        directAssertionReloadTemplate_inherited instantiated))))
  · intro substitution substitutionMember atom instantiated
    have atomExact := physicalMatcherRow_rejoin_exact listNodup morkNodup
      directivePresent rejoinCapabilities substitutionMember instantiated
    subst atom
    exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  · intro substitution substitutionMember atom instantiated
    have atomExact := physicalMatcherRow_bridge_exact listNodup morkNodup
      directivePresent bridgeCapabilities substitutionMember instantiated
    subst atom
    exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- The same physical matcher pins the two executable additions to their exact
compiler-captured representatives, not merely to an executable syntax head. -/
theorem physical_decorated_assertion_additions_exact_published
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    (bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space) :
    RuleScopedTemplateAdditionsWithin
      DecoratedAssertionExactPublishedAtom
      decoratedDirectAssertionDirective.rule.input
      (physicalDecoratedAssertionMatcherRows space)
      decoratedDirectAssertionDirective.rule.tmpl := by
  intro sink sinkMember
  rw [decoratedDirectAssertionDirective_sinks_exact] at sinkMember
  simp only [decoratedDirectAssertionSinks, directAssertionSinks,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at sinkMember
  rcases sinkMember with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      rfl
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · intro substitution _ atom instantiated
    exact Or.inl (instantiated_inherited_expression_head substitution
      "mm-compressed-assertion-context" _
      directAssertionContextTemplate_inherited instantiated)
  · intro substitution _ atom instantiated
    exact Or.inr (Or.inl (instantiated_inherited_expression_head substitution
      "mm-normal-control" _ directAssertionNormalControlTemplate_inherited
      instantiated))
  · intro substitution _ atom instantiated
    exact Or.inr (Or.inr (Or.inl
      (instantiated_inherited_expression_head substitution "mm-linked-row" _
        directAssertionNormalLabelTemplate_inherited instantiated)))
  · intro substitution _ atom instantiated
    exact Or.inr (Or.inr (Or.inr (Or.inl
      (instantiated_inherited_expression_head substitution
        "mm-reload-compressed-normal-dispatch" _
        directAssertionReloadTemplate_inherited instantiated))))
  · intro substitution substitutionMember atom instantiated
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (physicalMatcherRow_rejoin_exact listNodup morkNodup directivePresent
        rejoinCapabilities substitutionMember instantiated)))))
  · intro substitution substitutionMember atom instantiated
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (physicalMatcherRow_bridge_exact listNodup morkNodup directivePresent
        bridgeCapabilities substitutionMember instantiated)))))

/-- Any live row whose physical key differs from the three predecessor
controls survives the complete decorated-assertion transaction.  Additions
are unrestricted; the exact physical matcher pins every removal to its
source-derived control row. -/
theorem physical_decorated_assertion_preserves_row_of_remove_key_separation
    {space : List Atom} {candidate : Atom}
    (pendingSafe : ∀ substitution ∈
      physicalDecoratedAssertionMatcherRows space,
      ∀ removed, instantiateRuleTemplateAtom?
        decoratedDirectAssertionDirective.rule.input substitution
        directAssertionPendingTemplate = some removed →
        morkSupportKey candidate ≠ morkSupportKey removed)
    (lookupSafe : ∀ substitution ∈
      physicalDecoratedAssertionMatcherRows space,
      ∀ removed, instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionLookupTemplate = some removed →
        morkSupportKey candidate ≠ morkSupportKey removed)
    (machineSafe : ∀ substitution ∈
      physicalDecoratedAssertionMatcherRows space,
      ∀ removed, instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionMachineTemplate = some removed →
        morkSupportKey candidate ≠ morkSupportKey removed)
    (present : candidate ∈ morkEraseSupport space
      decoratedDirectAssertionDirective.atom) :
    candidate ∈ cFireRuleScopedSourceExecFact space
      decoratedDirectAssertionDirective := by
  let rows := physicalDecoratedAssertionMatcherRows space
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change candidate ∈ cApplyRuleScopedSinkBatch
    decoratedDirectAssertionDirective.rule.input rows
    (morkEraseSupport space decoratedDirectAssertionDirective.atom)
    decoratedDirectAssertionDirective.rule.tmpl.sinks
  apply mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
  · intro sink sinkMember
    rw [decoratedDirectAssertionDirective_sinks_exact] at sinkMember
    simp only [decoratedDirectAssertionSinks, directAssertionSinks,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with (h | h | h | h | h | h | h | h) | h
    all_goals subst sink
    · exact Or.inr ⟨_, rfl, by
        intro substitution substitutionMember removed instantiates
        exact pendingSafe substitution
          (by simpa [rows] using substitutionMember) removed instantiates⟩
    · exact Or.inr ⟨_, rfl, by
        intro substitution substitutionMember removed instantiates
        exact lookupSafe substitution
          (by simpa [rows] using substitutionMember) removed instantiates⟩
    · exact Or.inr ⟨_, rfl, by
        intro substitution substitutionMember removed instantiates
        exact machineSafe substitution
          (by simpa [rows] using substitutionMember) removed instantiates⟩
    all_goals exact Or.inl ⟨_, rfl⟩
  · exact present

/-- A matcher-independent key-separation proof is a stronger, cheaper
sufficient interface for the same physical frame law. -/
theorem physical_decorated_assertion_preserves_row_of_global_key_separation
    {space : List Atom} {candidate : Atom}
    (pendingSafe : ∀ substitution removed,
      instantiateRuleTemplateAtom?
        decoratedDirectAssertionDirective.rule.input substitution
        directAssertionPendingTemplate = some removed →
      morkSupportKey candidate ≠ morkSupportKey removed)
    (lookupSafe : ∀ substitution removed,
      instantiateRuleTemplateAtom?
        decoratedDirectAssertionDirective.rule.input substitution
        directAssertionLookupTemplate = some removed →
      morkSupportKey candidate ≠ morkSupportKey removed)
    (machineSafe : ∀ substitution removed,
      instantiateRuleTemplateAtom?
        decoratedDirectAssertionDirective.rule.input substitution
        directAssertionMachineTemplate = some removed →
      morkSupportKey candidate ≠ morkSupportKey removed)
    (present : candidate ∈ morkEraseSupport space
      decoratedDirectAssertionDirective.atom) :
    candidate ∈ cFireRuleScopedSourceExecFact space
      decoratedDirectAssertionDirective := by
  exact physical_decorated_assertion_preserves_row_of_remove_key_separation
    (pendingSafe := fun substitution _ removed instantiates =>
      pendingSafe substitution removed instantiates)
    (lookupSafe := fun substitution _ removed instantiates =>
      lookupSafe substitution removed instantiates)
    (machineSafe := fun substitution _ removed instantiates =>
      machineSafe substitution removed instantiates)
    present

/-- Compact physical capability record for rows that cannot be consumed by
the assertion launcher's three predecessor removals. -/
structure DecoratedAssertionPredecessorKeySafety (candidate : Atom) : Prop where
  pending : ∀ substitution removed,
    instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      directAssertionPendingTemplate = some removed →
    morkSupportKey candidate ≠ morkSupportKey removed
  lookup : ∀ substitution removed,
    instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      directAssertionLookupTemplate = some removed →
    morkSupportKey candidate ≠ morkSupportKey removed
  machine : ∀ substitution removed,
    instantiateRuleTemplateAtom?
      decoratedDirectAssertionDirective.rule.input substitution
      directAssertionMachineTemplate = some removed →
    morkSupportKey candidate ≠ morkSupportKey removed

theorem physical_decorated_assertion_preserves_row_of_key_safety
    {space : List Atom} {candidate : Atom}
    (safe : DecoratedAssertionPredecessorKeySafety candidate)
    (present : candidate ∈ morkEraseSupport space
      decoratedDirectAssertionDirective.atom) :
    candidate ∈ cFireRuleScopedSourceExecFact space
      decoratedDirectAssertionDirective := by
  exact physical_decorated_assertion_preserves_row_of_global_key_separation
    safe.pending safe.lookup safe.machine present

/-- Exact predecessor reconstruction is a convenient sufficient condition for
the physical key-separation frame theorem. -/
theorem physical_decorated_assertion_preserves_row
    {context : DirectAssertionContext} {space : List Atom} {candidate : Atom}
    (removeExact : ∀ substitution ∈
      physicalDecoratedAssertionMatcherRows space,
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionPendingTemplate = some context.pendingRow ∧
        instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionLookupTemplate = some context.lookupRow ∧
        instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionMachineTemplate = some context.machineRow)
    (present : candidate ∈ morkEraseSupport space
      decoratedDirectAssertionDirective.atom)
    (notPending : morkSupportKey candidate ≠
      morkSupportKey context.pendingRow)
    (notLookup : morkSupportKey candidate ≠
      morkSupportKey context.lookupRow)
    (notMachine : morkSupportKey candidate ≠
      morkSupportKey context.machineRow) :
    candidate ∈ cFireRuleScopedSourceExecFact space
      decoratedDirectAssertionDirective := by
  apply physical_decorated_assertion_preserves_row_of_remove_key_separation
  · intro substitution member removed instantiates
    have removedExact := Option.some.inj
      (instantiates.symm.trans (removeExact substitution member).1)
    simpa [removedExact] using notPending
  · intro substitution member removed instantiates
    have removedExact := Option.some.inj
      (instantiates.symm.trans (removeExact substitution member).2.1)
    simpa [removedExact] using notLookup
  · intro substitution member removed instantiates
    have removedExact := Option.some.inj
      (instantiates.symm.trans (removeExact substitution member).2.2)
    simpa [removedExact] using notMachine
  · exact present

/-- The complete physical decorated-assertion sink batch consumes the compact
pending request, heap lookup, and predecessor machine row.  Role-indexed
capability provenance prevents another matcher row from recreating a control
through either opaque executable output. -/
theorem physical_decorated_assertion_consumes_predecessor_controls
    {context : DirectAssertionContext} {space : List Atom}
    (matched : ExactDecoratedDirectAssertionLaunch context space)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : decoratedDirectAssertionDirective.atom ∈ space)
    (rejoinCapabilities : AssertionRejoinCapabilities
      compressedAssertionRejoinRule space)
    (bridgeCapabilities : NormalDispatchBridgeCapabilities
      compressedNormalDispatchBridgeRule space) :
    context.pendingRow ∉
        cFireRuleScopedSourceExecFact space
          decoratedDirectAssertionDirective ∧
      context.lookupRow ∉
        cFireRuleScopedSourceExecFact space
          decoratedDirectAssertionDirective ∧
      context.machineRow ∉
        cFireRuleScopedSourceExecFact space
          decoratedDirectAssertionDirective := by
  let rows := physicalDecoratedAssertionMatcherRows space
  obtain ⟨witness, witnessMember, pending, lookup, machine,
      _assertionContext, _normalControl, _normalLabel, _reload,
      _rejoin, _bridge⟩ :=
    physical_decorated_assertion_exact_match matched listNodup morkNodup
      directivePresent
  have contextOutputNe (substitution : Subst) (candidateHead : String)
      (candidateTail : List Atom) (different :
        "mm-compressed-assertion-context" ≠ candidateHead) :
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionContextTemplate ≠
        some (.expression (.symbol candidateHead :: candidateTail)) := by
    rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
      _ _ _ directAssertionContextTemplate_inherited]
    unfold directAssertionContextTemplate
    exact
      Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable.instantiateTemplateAtom?_expression_symbol_head_ne
        substitution "mm-compressed-assertion-context" candidateHead _ _
        different
  have normalControlOutputNe (substitution : Subst) (candidateHead : String)
      (candidateTail : List Atom)
      (different : "mm-normal-control" ≠ candidateHead) :
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionNormalControlTemplate ≠
        some (.expression (.symbol candidateHead :: candidateTail)) := by
    rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
      _ _ _ directAssertionNormalControlTemplate_inherited]
    unfold directAssertionNormalControlTemplate
    exact
      Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable.instantiateTemplateAtom?_expression_symbol_head_ne
        substitution "mm-normal-control" candidateHead _ _ different
  have normalLabelOutputNe (substitution : Subst) (candidateHead : String)
      (candidateTail : List Atom) (different : "mm-linked-row" ≠ candidateHead) :
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionNormalLabelTemplate ≠
        some (.expression (.symbol candidateHead :: candidateTail)) := by
    rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
      _ _ _ directAssertionNormalLabelTemplate_inherited]
    unfold directAssertionNormalLabelTemplate
    exact
      Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable.instantiateTemplateAtom?_expression_symbol_head_ne
        substitution "mm-linked-row" candidateHead _ _ different
  have reloadOutputNe (substitution : Subst) (candidateHead : String)
      (candidateTail : List Atom)
      (different : "mm-reload-compressed-normal-dispatch" ≠ candidateHead) :
      instantiateRuleTemplateAtom?
          decoratedDirectAssertionDirective.rule.input substitution
          directAssertionReloadTemplate ≠
        some (.expression (.symbol candidateHead :: candidateTail)) := by
    rw [instantiateRuleTemplateAtom?_eq_instantiateTemplateAtom?
      _ _ _ directAssertionReloadTemplate_inherited]
    unfold directAssertionReloadTemplate
    exact
      Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable.instantiateTemplateAtom?_expression_symbol_head_ne
        substitution "mm-reload-compressed-normal-dispatch" candidateHead _ _
        different
  have removeControl (before : List Sink) (authored candidate : Atom)
      (rest : List Sink)
      (sinkSplit : decoratedDirectAssertionDirective.rule.tmpl.sinks =
        before ++ .remove authored :: rest)
      (instantiates : instantiateRuleTemplateAtom?
        decoratedDirectAssertionDirective.rule.input witness authored =
          some candidate)
      (restSafe : ∀ sink ∈ rest,
        (∃ later, sink = .remove later) ∨
          ∃ later, sink = .add later ∧
            ∀ substitution ∈ rows,
              instantiateRuleTemplateAtom?
                decoratedDirectAssertionDirective.rule.input substitution
                later ≠ some candidate) :
      candidate ∉ cFireRuleScopedSourceExecFact space
        decoratedDirectAssertionDirective := by
    unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
    change candidate ∉
      cApplyRuleScopedSinkBatch
        decoratedDirectAssertionDirective.rule.input rows
        (morkEraseSupport space decoratedDirectAssertionDirective.atom)
        decoratedDirectAssertionDirective.rule.tmpl.sinks
    rw [sinkSplit]
    exact not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      decoratedDirectAssertionDirective.rule.input rows
      (morkEraseSupport space decoratedDirectAssertionDirective.atom)
      before authored candidate rest witness
      (by simpa [rows] using witnessMember) instantiates restSafe
  have pendingNeRejoin :
      context.pendingRow ≠ compressedAssertionRejoinRule := by
    simp [DirectAssertionContext.pendingRow, compressedAssertionRejoinRule]
  have pendingNeBridge :
      context.pendingRow ≠ compressedNormalDispatchBridgeRule := by
    simp [DirectAssertionContext.pendingRow, compressedNormalDispatchBridgeRule]
  have lookupNeRejoin :
      context.lookupRow ≠ compressedAssertionRejoinRule := by
    simp [DirectAssertionContext.lookupRow, compressedAssertionRejoinRule]
  have lookupNeBridge :
      context.lookupRow ≠ compressedNormalDispatchBridgeRule := by
    simp [DirectAssertionContext.lookupRow, compressedNormalDispatchBridgeRule]
  have machineNeRejoin :
      context.machineRow ≠ compressedAssertionRejoinRule := by
    simp [DirectAssertionContext.machineRow, compressedAssertionRejoinRule]
  have machineNeBridge :
      context.machineRow ≠ compressedNormalDispatchBridgeRule := by
    simp [DirectAssertionContext.machineRow, compressedNormalDispatchBridgeRule]
  constructor
  · apply removeControl [] directAssertionPendingTemplate context.pendingRow
      [.remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate,
       .add directAssertionReloadTemplate,
       .add (.var "compressed-assertion-rejoin-rule"),
       .add (.var "normal-bridge-rule")]
    · exact decoratedDirectAssertionDirective_sinks_exact
    · exact pending
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · exact Or.inl ⟨_, rfl⟩
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.pendingRow
        exact contextOutputNe substitution "mm-compressed-step-pending" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.pendingRow
        exact normalControlOutputNe substitution "mm-compressed-step-pending" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.pendingRow
        exact normalLabelOutputNe substitution "mm-compressed-step-pending" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.pendingRow
        exact reloadOutputNe substitution "mm-compressed-step-pending" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution substitutionMember instantiates
        exact pendingNeRejoin
          (physicalMatcherRow_rejoin_exact listNodup morkNodup
            directivePresent rejoinCapabilities
            (by simpa [rows] using substitutionMember) instantiates)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution substitutionMember instantiates
        exact pendingNeBridge
          (physicalMatcherRow_bridge_exact listNodup morkNodup
            directivePresent bridgeCapabilities
            (by simpa [rows] using substitutionMember) instantiates)
  constructor
  · apply removeControl [.remove directAssertionPendingTemplate]
      directAssertionLookupTemplate context.lookupRow
      [.remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate,
       .add directAssertionReloadTemplate,
       .add (.var "compressed-assertion-rejoin-rule"),
       .add (.var "normal-bridge-rule")]
    · exact decoratedDirectAssertionDirective_sinks_exact
    · exact lookup
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inl ⟨_, rfl⟩
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.lookupRow
        exact contextOutputNe substitution "mm-compressed-heap-lookup" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.lookupRow
        exact normalControlOutputNe substitution "mm-compressed-heap-lookup" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.lookupRow
        exact normalLabelOutputNe substitution "mm-compressed-heap-lookup" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.lookupRow
        exact reloadOutputNe substitution "mm-compressed-heap-lookup" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution substitutionMember instantiates
        exact lookupNeRejoin
          (physicalMatcherRow_rejoin_exact listNodup morkNodup
            directivePresent rejoinCapabilities
            (by simpa [rows] using substitutionMember) instantiates)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution substitutionMember instantiates
        exact lookupNeBridge
          (physicalMatcherRow_bridge_exact listNodup morkNodup
            directivePresent bridgeCapabilities
            (by simpa [rows] using substitutionMember) instantiates)
  · apply removeControl
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate]
      directAssertionMachineTemplate context.machineRow
      [.add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate,
       .add directAssertionReloadTemplate,
       .add (.var "compressed-assertion-rejoin-rule"),
       .add (.var "normal-bridge-rule")]
    · exact decoratedDirectAssertionDirective_sinks_exact
    · exact machine
    · intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.machineRow
        exact contextOutputNe substitution "mm-compressed-machine" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.machineRow
        exact normalControlOutputNe substitution "mm-compressed-machine" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.machineRow
        exact normalLabelOutputNe substitution "mm-compressed-machine" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution _
        unfold DirectAssertionContext.machineRow
        exact reloadOutputNe substitution "mm-compressed-machine" _
          (by decide)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution substitutionMember instantiates
        exact machineNeRejoin
          (physicalMatcherRow_rejoin_exact listNodup morkNodup
            directivePresent rejoinCapabilities
            (by simpa [rows] using substitutionMember) instantiates)
      · right
        refine ⟨_, rfl, ?_⟩
        intro substitution substitutionMember instantiates
        exact machineNeBridge
          (physicalMatcherRow_bridge_exact listNodup morkNodup
            directivePresent bridgeCapabilities
            (by simpa [rows] using substitutionMember) instantiates)

/-- The actual least-key rule-scoped scheduler selects the decorated assertion
handler in a source-derived request space. -/
theorem source_decorated_assertion_ruleScoped_step
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state) (scanner : ScannerBoundary)
    (index cursor : Nat) (assertion : SourceAssertion) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (sourceDecoratedAssertionRequestSpace context state ledger scanner
          index cursor assertion) =
      some (cFireRuleScopedSourceExecFact
        (sourceDecoratedAssertionRequestSpace context state ledger scanner
          index cursor assertion)
        decoratedDirectAssertionDirective) := by
  unfold sourceDecoratedAssertionRequestSpace
  unfold cRuleScopedSourceWorkQueueStep
  rw [canonicalDecoratedDirectAssertionSpace_append_selects
    (directAssertionContextAtBoundary context state scanner index cursor
      assertion)
    (sourceAssertionAdditionalRows context state ledger scanner index assertion)
    (sourceAssertionAdditionalRows_no_supported context state ledger scanner
      index assertion)]

/-- One source-derived assertion launch is a nonempty physical MORK segment.
Its primitive transition is classified by the native type generated by
passing the rule-scoped execution GSLT through OSLF. -/
structure PhysicalSourceDecoratedAssertionLaunch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion) : Prop where
  sourceLaunch : SourceDecoratedAssertionLaunchSquare context state ledger
    scannerBefore scannerAfter occurrence index cursor assertion
  listNodup :
    (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
      index cursor assertion).Nodup
  morkNodup : MorkSupportNodup
    (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
      index cursor assertion)
  exactPhysicalMatch : PhysicalExactDecoratedAssertionLaunch
    (directAssertionContextAtBoundary context state scannerAfter index cursor
      assertion)
    (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
      index cursor assertion)
  concreteStep :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
          index cursor assertion) =
      some (cFireRuleScopedSourceExecFact
        (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
          index cursor assertion)
        decoratedDirectAssertionDirective)
  concreteTrace : Nonempty (CRuleScopedTrace .leaveInert 1
    (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
      index cursor assertion)
    (cFireRuleScopedSourceExecFact
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
      decoratedDirectAssertionDirective))
  nativeTypeTrace : Nonempty (RuleScopedNativeTypeTrace .leaveInert 1
    (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
      index cursor assertion)
    (cFireRuleScopedSourceExecFact
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
      decoratedDirectAssertionDirective))
  launchSupport :
    let result := cFireRuleScopedSourceExecFact
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
      decoratedDirectAssertionDirective
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    morkSupportContains result launchContext.assertionContextRow = true ∧
      morkSupportContains result launchContext.normalControlRow = true ∧
      morkSupportContains result launchContext.normalLabelRow = true ∧
      morkSupportContains result launchContext.reloadRow = true ∧
      morkSupportContains result compressedAssertionRejoinRule = true ∧
      morkSupportContains result compressedNormalDispatchBridgeRule = true
  predecessorControlsConsumed :
    let result := cFireRuleScopedSourceExecFact
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
      decoratedDirectAssertionDirective
    let launchContext := directAssertionContextAtBoundary context state
      scannerAfter index cursor assertion
    launchContext.pendingRow ∉ result ∧
      launchContext.lookupRow ∉ result ∧
      launchContext.machineRow ∉ result
  resultListNodup :
    (cFireRuleScopedSourceExecFact
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
      decoratedDirectAssertionDirective).Nodup
  resultMorkNodup : MorkSupportNodup
    (cFireRuleScopedSourceExecFact
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)
      decoratedDirectAssertionDirective)

theorem source_decorated_assertion_physical_launch
    {source : SourcePrefix} {target : ValidatedCalculusLanguageDef}
    (context : BoundaryContext) (state : MachineState source target)
    (ledger : NodeOccurrenceLedger state)
    (scannerBefore scannerAfter : ScannerBoundary)
    (occurrence : ByteOccurrence) (index cursor : Nat)
    (assertion : SourceAssertion)
    (request : SourceAssertionRequest context state scannerBefore scannerAfter
      occurrence index assertion)
    (listNodup :
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion).Nodup)
    (morkNodup : MorkSupportNodup
      (sourceDecoratedAssertionRequestSpace context state ledger scannerAfter
        index cursor assertion)) :
    PhysicalSourceDecoratedAssertionLaunch context state ledger scannerBefore
      scannerAfter occurrence index cursor assertion := by
  let launchContext := directAssertionContextAtBoundary context state
    scannerAfter index cursor assertion
  let space := sourceDecoratedAssertionRequestSpace context state ledger
    scannerAfter index cursor assertion
  have sourceLaunch := source_decorated_assertion_launch_square context
    state ledger scannerBefore scannerAfter occurrence index cursor assertion
    request
  have directivePresent : decoratedDirectAssertionDirective.atom ∈ space := by
    simp [space, sourceDecoratedAssertionRequestSpace,
      canonicalDecoratedDirectAssertionSpace,
      decoratedDirectAssertionMatchSlice]
  have moved := source_decorated_assertion_ruleScoped_step context state ledger
    scannerAfter index cursor assertion
  let trace : CRuleScopedTrace .leaveInert 1 space
      (cFireRuleScopedSourceExecFact space decoratedDirectAssertionDirective) :=
    .step moved .refl
  exact
    { sourceLaunch := sourceLaunch
      listNodup := listNodup
      morkNodup := morkNodup
      exactPhysicalMatch :=
        physical_decorated_assertion_exact_match
          sourceLaunch.exactMatcher listNodup morkNodup directivePresent
      concreteStep := moved
      concreteTrace := ⟨trace⟩
      nativeTypeTrace := ⟨trace.toNativeTypeTrace⟩
      launchSupport :=
        physical_decorated_assertion_launch_support_present
          sourceLaunch.exactMatcher listNodup morkNodup directivePresent
      predecessorControlsConsumed :=
        physical_decorated_assertion_consumes_predecessor_controls
          sourceLaunch.exactMatcher listNodup morkNodup directivePresent
          (sourceDecoratedAssertionRequestSpace_rejoin_capabilities context
            state ledger scannerAfter index cursor assertion)
          (sourceDecoratedAssertionRequestSpace_bridge_capabilities context
            state ledger scannerAfter index cursor assertion)
      resultListNodup :=
        cFireRuleScopedSourceExecFact_list_nodup space
          decoratedDirectAssertionDirective listNodup
      resultMorkNodup :=
        cFireRuleScopedSourceExecFact_mork_nodup space
          decoratedDirectAssertionDirective morkNodup }

#print axioms physical_decorated_assertion_exact_match
#print axioms directAssertionPendingTemplate_inherited
#print axioms directAssertionLookupTemplate_inherited
#print axioms directAssertionMachineTemplate_inherited
#print axioms physical_decorated_assertion_launch_support_present
#print axioms physical_decorated_assertion_additions_supported_origin
#print axioms physical_decorated_assertion_additions_published
#print axioms physical_decorated_assertion_additions_exact_published
#print axioms physical_decorated_assertion_preserves_row_of_remove_key_separation
#print axioms physical_decorated_assertion_preserves_row_of_global_key_separation
#print axioms physical_decorated_assertion_preserves_row_of_key_safety
#print axioms physical_decorated_assertion_preserves_row
#print axioms physical_decorated_assertion_consumes_predecessor_controls
#print axioms source_decorated_assertion_ruleScoped_step
#print axioms source_decorated_assertion_physical_launch

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalDecoratedAssertionLaunch
