import Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoinSquare
import Mettapedia.Languages.ProcessCalculi.MORK.ComputableMatchExactness
import Mettapedia.Languages.ProcessCalculi.MORK.PhysicalSupportHeadFaithfulness

/-!
# Physical normal-result handoff

The shared normal assertion verifier returns its completed body to the
compressed proof machine through an actual rule-scoped MORK transition.  This
module transports the established symbolic matcher across the physical read
permutation, proves support for every handoff output, and classifies the
scheduled step through OSLF.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalResult

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionRejoinContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoin
open Mettapedia.Languages.Metamath.MM2CompressedProofNormalResultRejoinSquare
open Mettapedia.Languages.Metamath.MM2Transformation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.Conformance.Computable

/-- Matcher substitutions enumerated by the actual compact-key normal-result
firing. -/
def physicalNormalResultMatcherRows (space : List Atom) : List Subst :=
  let live := morkEraseSupport space normalResultDirective.atom
  let read := morkInsertSupport live normalResultDirective.atom
  ((cMatchInputSpecMork [] read normalResultDirective.rule.input).filter fun
      (substitution, _) =>
        matchSourceGuards substitution normalResultDirective.rule.guards).map
    Prod.fst

theorem normalResultDirective_guards_exact :
    normalResultDirective.rule.guards = [] := by
  decide +kernel

theorem normalResultDirective_sinks_variablesInherited :
    ruleSinksVariablesInherited normalResultDirective.rule.input
      normalResultDirective.rule.tmpl.sinks = true := by
  decide +kernel

theorem normalResultDirective_supportSet :
    ReflectiveSupportSetTemplate normalResultDirective.rule.tmpl := by
  intro sink member
  rw [normalResult_sinks_exact] at member
  simp only [normalResultSinks, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> trivial

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

theorem physical_normal_result_live_eq
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : normalResultDirective.atom ∈ space) :
    morkEraseSupport space normalResultDirective.atom =
      space.erase normalResultDirective.atom :=
  morkEraseSupport_eq_erase_of_mem space normalResultDirective.atom listNodup
    morkNodup directivePresent

theorem physical_normal_result_read_perm
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : normalResultDirective.atom ∈ space) :
    (morkInsertSupport (morkEraseSupport space normalResultDirective.atom)
        normalResultDirective.atom).Perm
      (normalResultDirective.atom ::
        space.erase normalResultDirective.atom) := by
  rw [physical_normal_result_live_eq listNodup morkNodup directivePresent]
  have absent : morkSupportContains
      (space.erase normalResultDirective.atom) normalResultDirective.atom =
        false := by
    rw [← physical_normal_result_live_eq listNodup morkNodup
      directivePresent]
    exact morkSupportContains_morkEraseSupport_self space
      normalResultDirective.atom
  unfold morkInsertSupport
  rw [absent]
  exact List.perm_append_singleton normalResultDirective.atom
    (space.erase normalResultDirective.atom)

theorem physical_normal_result_matcher_mem_iff
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : normalResultDirective.atom ∈ space)
    (substitution : Subst) (consumed : List Atom) :
    (substitution, consumed) ∈
        cMatchInputSpecMork []
          (morkInsertSupport
            (morkEraseSupport space normalResultDirective.atom)
            normalResultDirective.atom)
          normalResultDirective.rule.input ↔
      (substitution, consumed) ∈
        Conformance.Computable.cmatchInputSpec []
          (normalResultDirective.atom ::
            space.erase normalResultDirective.atom)
          normalResultDirective.rule.input := by
  rw [normalResult_input_exact]
  unfold cMatchInputSpecMork Conformance.Computable.cmatchInputSpec
  have readPerm := physical_normal_result_read_perm listNodup morkNodup
    directivePresent
  constructor
  · intro member
    exact cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mp atomMember)
      substitution consumed member
  · intro member
    exact cmatchPattern_mono [] _ _ _
      (fun atom atomMember => readPerm.mem_iff.mpr atomMember)
      substitution consumed member

/-- Exact normal-result outputs as instantiated by the physical matcher used
by rule-scoped MORK execution. -/
def PhysicalExactNormalResultRejoin (context : NormalResultContext)
    (space : List Atom) : Prop :=
  ∃ substitution ∈ physicalNormalResultMatcherRows space,
    instantiateRuleTemplateAtom? normalResultDirective.rule.input substitution
          normalResultControlTemplate =
        some context.rejoinContext.returnedControlRow ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution normalResultStackTemplate =
        some context.rejoinContext.returnedStackRow ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution normalResultReloadTemplate =
        some (normalAssertionReloadAtom context.proofOwner) ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule

theorem physical_exact_normal_result_rejoin_of_reflective
    (context : NormalResultContext) {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : normalResultDirective.atom ∈ space)
    (matched : ExactNormalResultRejoin context space) :
    PhysicalExactNormalResultRejoin context space := by
  rcases matched with
    ⟨substitution, rowMember, control, stack, reload, rejoin⟩
  rw [List.mem_map] at rowMember
  obtain ⟨⟨matchedSubstitution, consumed⟩, reflected, equal⟩ := rowMember
  have reflected' : (substitution, consumed) ∈
      Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          space.erase normalResultDirective.atom)
        normalResultDirective.rule.input := by
    cases equal
    exact reflected
  have physicalMatch :=
    (physical_normal_result_matcher_mem_iff listNodup morkNodup
      directivePresent substitution consumed).2 reflected'
  have physicalRow : substitution ∈ physicalNormalResultMatcherRows space := by
    unfold physicalNormalResultMatcherRows
    rw [List.mem_map]
    refine ⟨(substitution, consumed), ?_, rfl⟩
    rw [List.mem_filter]
    refine ⟨physicalMatch, ?_⟩
    rw [normalResultDirective_guards_exact]
    rfl
  exact ⟨substitution, physicalRow,
    instantiateRuleTemplateAtom?_of_reflective _ control,
    instantiateRuleTemplateAtom?_of_reflective _ stack,
    instantiateRuleTemplateAtom?_of_reflective _ reload,
    instantiateRuleTemplateAtom?_of_reflective _ rejoin⟩

/-- Every physical matcher row has the exact source-indexed consumed cursor
and output interface.  No later proof may choose a convenient matcher witness:
the statement quantifies over every row enumerated by compact MORK matching. -/
theorem physical_normal_result_matcher_interface_exact
    (context : NormalResultContext)
    (listNodup : (normalToRejoinSlice context).Nodup)
    (morkNodup : MorkSupportNodup (normalToRejoinSlice context))
    {substitution : Subst}
    (member : substitution ∈
      physicalNormalResultMatcherRows (normalToRejoinSlice context)) :
    instantiateRuleTemplateAtom? normalResultDirective.rule.input
        substitution normalResultCursorTemplate =
        some context.bodyBuiltRow ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
        substitution normalResultControlTemplate =
        some context.rejoinContext.returnedControlRow ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
        substitution normalResultStackTemplate =
        some context.rejoinContext.returnedStackRow ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
        substitution normalResultReloadTemplate =
        some (normalAssertionReloadAtom context.proofOwner) ∧
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
        substitution (.var "compressed-assertion-rejoin-rule") =
        some compressedAssertionRejoinRule := by
  unfold physicalNormalResultMatcherRows at member
  rw [List.mem_map] at member
  obtain ⟨⟨matchedSubstitution, consumed⟩, filtered, equal⟩ := member
  have physicalMatched := (List.mem_filter.mp filtered).1
  have ordinaryMatched :=
    (physical_normal_result_matcher_mem_iff listNodup morkNodup
      (by simp [normalToRejoinSlice]) matchedSubstitution consumed).1
        physicalMatched
  have ordinaryMember : matchedSubstitution ∈
      (Conformance.Computable.cmatchInputSpec []
        (normalResultDirective.atom ::
          (normalToRejoinSlice context).erase normalResultDirective.atom)
        normalResultDirective.rule.input).map Prod.fst :=
    List.mem_map_of_mem ordinaryMatched
  subst substitution
  have exact := normalToRejoin_matcher_interface_exact context ordinaryMember
  exact ⟨instantiateRuleTemplateAtom?_of_reflective _ exact.1,
    instantiateRuleTemplateAtom?_of_reflective _ exact.2.1,
    instantiateRuleTemplateAtom?_of_reflective _ exact.2.2.1,
    instantiateRuleTemplateAtom?_of_reflective _ exact.2.2.2.1,
    instantiateRuleTemplateAtom?_of_reflective _ exact.2.2.2.2⟩

private theorem normalResultSinks_control_split :
    normalResultSinks =
      [.remove normalResultCursorTemplate] ++
      .add normalResultControlTemplate ::
        [.add normalResultStackTemplate, .add normalResultReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

private theorem normalResultSinks_stack_split :
    normalResultSinks =
      [.remove normalResultCursorTemplate, .add normalResultControlTemplate] ++
      .add normalResultStackTemplate ::
        [.add normalResultReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

private theorem normalResultSinks_reload_split :
    normalResultSinks =
      [.remove normalResultCursorTemplate, .add normalResultControlTemplate,
       .add normalResultStackTemplate] ++
      .add normalResultReloadTemplate ::
        [.add (.var "compressed-assertion-rejoin-rule")] := by
  rfl

theorem physical_normal_result_support_present
    (context : NormalResultContext) (space : List Atom)
    (matched : PhysicalExactNormalResultRejoin context space) :
    let result := cFireRuleScopedSourceExecFact space normalResultDirective
    morkSupportContains result context.rejoinContext.returnedControlRow = true ∧
      morkSupportContains result context.rejoinContext.returnedStackRow = true ∧
      morkSupportContains result
        (normalAssertionReloadAtom context.proofOwner) = true ∧
      morkSupportContains result compressedAssertionRejoinRule = true := by
  dsimp only
  rcases matched with
    ⟨substitution, rowMember, control, stack, reload, rejoin⟩
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change
    let live := morkEraseSupport space normalResultDirective.atom
    cApplyRuleScopedSinkBatch normalResultDirective.rule.input
        (physicalNormalResultMatcherRows space) live
          normalResultDirective.rule.tmpl.sinks |> fun result =>
      morkSupportContains result context.rejoinContext.returnedControlRow = true ∧
        morkSupportContains result context.rejoinContext.returnedStackRow = true ∧
        morkSupportContains result
          (normalAssertionReloadAtom context.proofOwner) = true ∧
        morkSupportContains result compressedAssertionRejoinRule = true
  dsimp only
  rw [normalResult_sinks_exact]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [normalResultSinks_control_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember control (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl | rfl <;>
          exact Or.inl ⟨_, rfl⟩)
  · rw [normalResultSinks_stack_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember stack (by
        intro sink sinkMember
        simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
        rcases sinkMember with rfl | rfl <;> exact Or.inl ⟨_, rfl⟩)
  · rw [normalResultSinks_reload_split]
    exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _ _ _ _ _ substitution rowMember reload (by
        intro sink sinkMember
        simp only [List.mem_singleton] at sinkMember
        subst sink
        exact Or.inl ⟨_, rfl⟩)
  · exact morkSupportContains_cApplyRuleScopedSinkBatch_append_add_cons_of_row
      _ _ _
      [.remove normalResultCursorTemplate, .add normalResultControlTemplate,
       .add normalResultStackTemplate, .add normalResultReloadTemplate]
      (.var "compressed-assertion-rejoin-rule")
      compressedAssertionRejoinRule [] substitution rowMember rejoin (by
        intro sink sinkMember
        simp at sinkMember)

/-- Any live row whose physical key differs from the uniquely matched body
cursor survives the complete normal-result sink batch exactly.  The theorem
is presentation-neutral: callers supply the exact cursor selected by every
physical matcher row. -/
theorem physical_normal_result_preserves_row_of_exact_cursor
    {space : List Atom} (listNodup : space.Nodup)
    (morkNodup : MorkSupportNodup space)
    (directivePresent : normalResultDirective.atom ∈ space)
    {bodyBuilt candidate : Atom}
    (cursorExact : ∀ substitution ∈ physicalNormalResultMatcherRows space,
      instantiateRuleTemplateAtom? normalResultDirective.rule.input
          substitution normalResultCursorTemplate =
        some bodyBuilt)
    (present : candidate ∈ space.erase normalResultDirective.atom)
    (different : morkSupportKey candidate ≠ morkSupportKey bodyBuilt) :
    candidate ∈ cFireRuleScopedSourceExecFact space normalResultDirective := by
  let rows := physicalNormalResultMatcherRows space
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change candidate ∈
    cApplyRuleScopedSinkBatch normalResultDirective.rule.input rows
      (morkEraseSupport space normalResultDirective.atom)
      normalResultDirective.rule.tmpl.sinks
  rw [normalResult_sinks_exact]
  apply mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
  · intro sink sinkMember
    simp only [normalResultSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨normalResultCursorTemplate, rfl, by
        intro substitution substitutionMember removed instantiated
        have removedExact : removed = bodyBuilt :=
          Option.some.inj
            (instantiated.symm.trans
              (cursorExact substitution (by simpa [rows] using substitutionMember)))
        simpa [removedExact] using different⟩
    all_goals exact Or.inl ⟨_, rfl⟩
  · rw [physical_normal_result_live_eq listNodup morkNodup directivePresent]
    exact present

/-- A canonical row whose physical key differs from the consumed body cursor
survives the complete normal-result sink batch exactly, not merely by support
identity. -/
theorem physical_normal_result_preserves_row
    (context : NormalResultContext)
    (morkNodup : MorkSupportNodup (normalToRejoinSlice context))
    {candidate : Atom}
    (present : candidate ∈
      (normalToRejoinSlice context).erase normalResultDirective.atom)
    (different : morkSupportKey candidate ≠
      morkSupportKey context.bodyBuiltRow) :
    candidate ∈ cFireRuleScopedSourceExecFact
      (normalToRejoinSlice context) normalResultDirective := by
  apply physical_normal_result_preserves_row_of_exact_cursor
    (normalToRejoinSlice_nodup context) morkNodup
    (by simp [normalToRejoinSlice])
  · intro substitution substitutionMember
    exact (physical_normal_result_matcher_interface_exact context
      (normalToRejoinSlice_nodup context) morkNodup
      substitutionMember).1
  · exact present
  · exact different

private theorem applySubstList_length (substitution : Subst) :
    ∀ atoms,
      (applySubst.applySubstList substitution atoms).length = atoms.length
  | [] => rfl
  | _ :: tail => by
      simp [applySubst.applySubstList,
        applySubstList_length substitution tail]

private theorem instantiateRuleTemplateAtom?_expression_shape
    (input : InputSpec) (substitution : Subst) (head : String)
    (tail : List Atom) (instantiatedAtom : Atom)
    (instantiated : instantiateRuleTemplateAtom? input substitution
      (.expression (.symbol head :: tail)) = some instantiatedAtom) :
    ∃ instantiatedTail,
      instantiatedAtom = .expression (.symbol head :: instantiatedTail) ∧
        instantiatedTail.length = tail.length := by
  unfold instantiateRuleTemplateAtom? at instantiated
  split at instantiated
  · simp only [applySubst, applySubst.applySubstList,
      Option.some.injEq] at instantiated
    subst instantiatedAtom
    exact ⟨applySubst.applySubstList substitution tail, rfl,
      applySubstList_length substitution tail⟩
  · simp at instantiated

/-- Every compiler-owned runtime capture is a physical frame of the shared
normal-result transaction.  The only remove sink retains the literal
`mm-body-built` head under substitution, so it cannot consume a runtime
capture independently of the concrete scanner inventory stored inside it. -/
theorem physical_normal_result_preserves_runtime_capture
    {space : List Atom}
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (directivePresent : normalResultDirective.atom ∈ space)
    (kind : String) (runtimeRule : Atom)
    (captureMember : compressedOwnedRuntimeRuleRow kind runtimeRule ∈ space) :
    compressedOwnedRuntimeRuleRow kind runtimeRule ∈
      cFireRuleScopedSourceExecFact space normalResultDirective := by
  let rows := physicalNormalResultMatcherRows space
  have notDirective : compressedOwnedRuntimeRuleRow kind runtimeRule ≠
      normalResultDirective.atom := by
    intro equal
    have directiveAtom :=
      extractSupportedSourceExecFact_atom extract_normalResultRule_exact
    have selfDecoded : extractSupportedSourceExecFact
        normalResultDirective.atom = some normalResultDirective := by
      rw [directiveAtom]
      exact extract_normalResultRule_exact
    rw [← equal] at selfDecoded
    simp [compressedOwnedRuntimeRuleRow, extractSupportedSourceExecFact,
      extractRawExecFact] at selfDecoded
  have liveMember : compressedOwnedRuntimeRuleRow kind runtimeRule ∈
      morkEraseSupport space normalResultDirective.atom := by
    rw [physical_normal_result_live_eq listNodup morkNodup directivePresent]
    exact (List.mem_erase_of_ne notDirective).2 captureMember
  unfold cFireRuleScopedSourceExecFact cApplyRuleScopedTemplate
  change compressedOwnedRuntimeRuleRow kind runtimeRule ∈
    cApplyRuleScopedSinkBatch normalResultDirective.rule.input rows
      (morkEraseSupport space normalResultDirective.atom)
      normalResultDirective.rule.tmpl.sinks
  rw [normalResult_sinks_exact]
  apply mem_cApplyRuleScopedSinkBatch_of_add_or_key_nonremoving_remove
    normalResultDirective.rule.input rows
  · intro sink sinkMember
    simp only [normalResultSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr ⟨normalResultCursorTemplate, rfl, by
        intro substitution _substitutionMember removed instantiated
        unfold normalResultCursorTemplate at instantiated
        obtain ⟨removedTail, rfl, removedLength⟩ :=
          instantiateRuleTemplateAtom?_expression_shape _ _ _ _ _
            instantiated
        norm_num at removedLength
        unfold compressedOwnedRuntimeRuleRow
        exact morkSupportKey_expression_symbol_head_ne
          "mm-compressed-owned-runtime-rule" "mm-body-built"
          [.symbol kind, runtimeRule] removedTail
          (by norm_num) (by omega) (by decide) (by decide) (by decide)
          (by decide) (by decide)⟩
    all_goals exact Or.inl ⟨_, rfl⟩
  · exact liveMember

def physicalNormalResult (context : NormalResultContext) : List Atom :=
  cFireRuleScopedSourceExecFact (normalToRejoinSlice context)
    normalResultDirective

private theorem expression_key_ne_normal_result_body
    (context : NormalResultContext) (head : String) (tail : List Atom)
    (arityBound : tail.length + 1 < 64)
    (headPositive : 0 < (morkUtf8Bytes head).length)
    (headBound : (morkUtf8Bytes head).length < 64)
    (different : head ≠ "mm-body-built") :
    morkSupportKey (.expression (.symbol head :: tail)) ≠
      morkSupportKey context.bodyBuiltRow := by
  unfold NormalResultContext.bodyBuiltRow
  apply morkSupportKey_expression_symbol_head_ne
  · exact arityBound
  · norm_num
  · exact headPositive
  · decide
  · exact headBound
  · decide
  · exact different

/-- The five source-derived rows needed by the compressed rejoin matcher
survive the physical normal-result transition as exact representatives. -/
theorem physical_normal_result_preserves_rejoin_inputs
    (context : NormalResultContext)
    (morkNodup : MorkSupportNodup (normalToRejoinSlice context)) :
    context.rejoinContext.contextRow ∈ physicalNormalResult context ∧
      context.rejoinContext.normalStackSuccessorRow ∈
        physicalNormalResult context ∧
      context.rejoinContext.nodeSuccessorRow ∈
        physicalNormalResult context ∧
      context.rejoinContext.normalLabelRow ∈
        physicalNormalResult context ∧
      context.rejoinContext.resumeCaptureRow ∈
        physicalNormalResult context := by
  have preserve {candidate : Atom}
      (present : candidate ∈
        (normalToRejoinSlice context).erase normalResultDirective.atom)
      (different : morkSupportKey candidate ≠
        morkSupportKey context.bodyBuiltRow) :
      candidate ∈ physicalNormalResult context := by
    exact physical_normal_result_preserves_row context morkNodup present
      different
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply preserve
    · simp [normalToRejoinSlice]
    · unfold RejoinContext.contextRow
      apply expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide
  · apply preserve
    · simp [normalToRejoinSlice]
    · unfold RejoinContext.normalStackSuccessorRow
      apply expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide
  · apply preserve
    · simp [normalToRejoinSlice]
    · unfold RejoinContext.nodeSuccessorRow compressedIndexSuccessorRow
      apply expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide
  · apply preserve
    · simp [normalToRejoinSlice]
    · unfold RejoinContext.normalLabelRow
      apply expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide
  · apply preserve
    · simp [normalToRejoinSlice]
    · unfold RejoinContext.resumeCaptureRow compressedOwnedRuntimeRuleRow
      apply expression_key_ne_normal_result_body context
      · norm_num
      · decide
      · decide
      · decide

/-- Canonical nominal presentation of the physical normal-result successor.
The predecessor body cursor is consumed once and the four instantiated outputs
are appended once. -/
def physicalNormalResultReference (context : NormalResultContext) : List Atom :=
  ((normalToRejoinSlice context).erase normalResultDirective.atom).erase
      context.bodyBuiltRow ++
    [context.rejoinContext.returnedControlRow,
     context.rejoinContext.returnedStackRow,
     normalAssertionReloadAtom context.proofOwner,
     compressedAssertionRejoinRule]

/-- The physical remove sink consumes the source-indexed completed body row,
and none of the later exact outputs can recreate it. -/
theorem physical_normal_result_consumes_body
    (context : NormalResultContext)
    (morkNodup : MorkSupportNodup (normalToRejoinSlice context)) :
    context.bodyBuiltRow ∉ physicalNormalResult context := by
  let rows := physicalNormalResultMatcherRows (normalToRejoinSlice context)
  have listNodup := normalToRejoinSlice_nodup context
  have directivePresent : normalResultDirective.atom ∈
      normalToRejoinSlice context := by simp [normalToRejoinSlice]
  obtain ⟨substitution, substitutionMember, _control, _stack, _reload,
      _rejoin⟩ :=
    physical_exact_normal_result_rejoin_of_reflective context listNodup
      morkNodup directivePresent
      (canonical_exact_normal_result_rejoin context)
  have exactInterface : ∀ candidate ∈ rows,
      instantiateRuleTemplateAtom? normalResultDirective.rule.input candidate
            normalResultCursorTemplate = some context.bodyBuiltRow ∧
        instantiateRuleTemplateAtom? normalResultDirective.rule.input candidate
            normalResultControlTemplate =
          some context.rejoinContext.returnedControlRow ∧
        instantiateRuleTemplateAtom? normalResultDirective.rule.input candidate
            normalResultStackTemplate =
          some context.rejoinContext.returnedStackRow ∧
        instantiateRuleTemplateAtom? normalResultDirective.rule.input candidate
            normalResultReloadTemplate =
          some (normalAssertionReloadAtom context.proofOwner) ∧
        instantiateRuleTemplateAtom? normalResultDirective.rule.input candidate
            (.var "compressed-assertion-rejoin-rule") =
          some compressedAssertionRejoinRule := by
    intro candidate member
    exact physical_normal_result_matcher_interface_exact context listNodup
      morkNodup (by simpa [rows] using member)
  have absent : context.bodyBuiltRow ∉
      cApplyRuleScopedSinkBatch normalResultDirective.rule.input rows
        (morkEraseSupport (normalToRejoinSlice context)
          normalResultDirective.atom) normalResultSinks := by
    apply not_mem_cApplyRuleScopedSinkBatch_append_remove_cons_of_row
      normalResultDirective.rule.input rows
      (morkEraseSupport (normalToRejoinSlice context)
        normalResultDirective.atom) [] normalResultCursorTemplate
      context.bodyBuiltRow
      [.add normalResultControlTemplate, .add normalResultStackTemplate,
       .add normalResultReloadTemplate,
       .add (.var "compressed-assertion-rejoin-rule")]
      substitution (by simpa [rows] using substitutionMember)
      (exactInterface substitution (by simpa [rows] using substitutionMember)).1
    intro sink sinkMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl
    · exact Or.inr ⟨normalResultControlTemplate, rfl, by
        intro candidate member
        rw [(exactInterface candidate member).2.1]
        simp [NormalResultContext.bodyBuiltRow,
          RejoinContext.returnedControlRow]⟩
    · exact Or.inr ⟨normalResultStackTemplate, rfl, by
        intro candidate member
        rw [(exactInterface candidate member).2.2.1]
        simp [NormalResultContext.bodyBuiltRow,
          RejoinContext.returnedStackRow]⟩
    · exact Or.inr ⟨normalResultReloadTemplate, rfl, by
        intro candidate member
        rw [(exactInterface candidate member).2.2.2.1]
        simp [NormalResultContext.bodyBuiltRow, normalAssertionReloadAtom]⟩
    · exact Or.inr ⟨(.var "compressed-assertion-rejoin-rule"), rfl, by
        intro candidate member
        rw [(exactInterface candidate member).2.2.2.2]
        simp [NormalResultContext.bodyBuiltRow,
          compressedAssertionRejoinRule]⟩
  simpa [physicalNormalResult, cFireRuleScopedSourceExecFact,
    cApplyRuleScopedTemplate, rows, physicalNormalResultMatcherRows,
    normalResult_sinks_exact] using absent

/-- Every exact atom retained by physical normal-result execution belongs to
the canonical nominal successor. -/
theorem physical_normal_result_rows_within_reference
    (context : NormalResultContext)
    (morkNodup : MorkSupportNodup (normalToRejoinSlice context)) :
    ∀ row ∈ physicalNormalResult context,
      row ∈ physicalNormalResultReference context := by
  intro row rowMember
  let rows := physicalNormalResultMatcherRows (normalToRejoinSlice context)
  let live := morkEraseSupport (normalToRejoinSlice context)
    normalResultDirective.atom
  have listNodup := normalToRejoinSlice_nodup context
  have directivePresent : normalResultDirective.atom ∈
      normalToRejoinSlice context := by simp [normalToRejoinSlice]
  have origin : row ∈ live ∨
      RuleScopedAddedAtom normalResultDirective.rule.input rows
        normalResultDirective.rule.tmpl.sinks row := by
    apply mem_cApplyRuleScopedTemplate_of_supportSet
      normalResultDirective.rule.input live rows
        normalResultDirective.rule.tmpl normalResultDirective_supportSet
    simpa [physicalNormalResult, cFireRuleScopedSourceExecFact,
      live, rows, physicalNormalResultMatcherRows] using rowMember
  rcases origin with prior | added
  · have prior' : row ∈
        (normalToRejoinSlice context).erase normalResultDirective.atom := by
      dsimp only [live] at prior
      rw [physical_normal_result_live_eq listNodup morkNodup
        directivePresent] at prior
      exact prior
    have notBody : row ≠ context.bodyBuiltRow := by
      intro equal
      subst row
      exact (physical_normal_result_consumes_body context morkNodup) rowMember
    simp [physicalNormalResultReference, prior', notBody]
  · rcases added with
      ⟨sink, sinkMember, authored, sinkEq, substitution,
        substitutionMember, instantiated⟩
    have exact := physical_normal_result_matcher_interface_exact context
      listNodup morkNodup (by simpa [rows] using substitutionMember)
    rw [normalResult_sinks_exact] at sinkMember
    simp only [normalResultSinks, List.mem_cons, List.not_mem_nil, or_false]
      at sinkMember
    rcases sinkMember with rfl | rfl | rfl | rfl | rfl
    · cases sinkEq
    · cases sinkEq
      have rowExact := Option.some.inj (instantiated.symm.trans exact.2.1)
      subst row
      simp [physicalNormalResultReference]
    · cases sinkEq
      have rowExact := Option.some.inj (instantiated.symm.trans exact.2.2.1)
      subst row
      simp [physicalNormalResultReference]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.2.1)
      subst row
      simp [physicalNormalResultReference]
    · cases sinkEq
      have rowExact := Option.some.inj
        (instantiated.symm.trans exact.2.2.2.2)
      subst row
      simp [physicalNormalResultReference]

/-- Every canonical successor row is present in the physical result by compact
support identity. -/
theorem physical_normal_result_reference_support_complete
    (context : NormalResultContext)
    (morkNodup : MorkSupportNodup (normalToRejoinSlice context)) :
    ∀ row ∈ physicalNormalResultReference context,
      morkSupportContains (physicalNormalResult context) row = true := by
  intro row member
  simp only [physicalNormalResultReference, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with live | rfl | rfl | rfl | rfl
  · exact morkSupportContains_eq_true_of_mem
      (physical_normal_result_preserves_row context morkNodup
        (List.mem_of_mem_erase live) (by
          have liveNodup :=
            (normalToRejoinSlice_nodup context).erase
              normalResultDirective.atom
          have notBody : row ≠ context.bodyBuiltRow := by
            intro equal
            subst row
            exact liveNodup.not_mem_erase live
          let reference :=
            (normalToRejoinSlice context).erase normalResultDirective.atom
          have referenceMorkNodup : MorkSupportNodup reference := by
            dsimp only [reference]
            rw [← physical_normal_result_live_eq
              (normalToRejoinSlice_nodup context) morkNodup
              (by simp [normalToRejoinSlice])]
            exact morkEraseSupport_nodup _ _ morkNodup
          exact fun keysEqual => notBody
            (morkSupportKey_injective_on referenceMorkNodup
              (List.mem_of_mem_erase live)
              (by simp [reference, normalToRejoinSlice])
              keysEqual)))
  · exact (physical_normal_result_support_present context
      (normalToRejoinSlice context)
      (physical_exact_normal_result_rejoin_of_reflective context
        (normalToRejoinSlice_nodup context) morkNodup
        (by simp [normalToRejoinSlice])
        (canonical_exact_normal_result_rejoin context))).1
  · exact (physical_normal_result_support_present context
      (normalToRejoinSlice context)
      (physical_exact_normal_result_rejoin_of_reflective context
        (normalToRejoinSlice_nodup context) morkNodup
        (by simp [normalToRejoinSlice])
        (canonical_exact_normal_result_rejoin context))).2.1
  · exact (physical_normal_result_support_present context
      (normalToRejoinSlice context)
      (physical_exact_normal_result_rejoin_of_reflective context
        (normalToRejoinSlice_nodup context) morkNodup
        (by simp [normalToRejoinSlice])
        (canonical_exact_normal_result_rejoin context))).2.2.1
  · exact (physical_normal_result_support_present context
      (normalToRejoinSlice context)
      (physical_exact_normal_result_rejoin_of_reflective context
        (normalToRejoinSlice_nodup context) morkNodup
        (by simp [normalToRejoinSlice])
        (canonical_exact_normal_result_rejoin context))).2.2.2

/-- With the successor's compact-key uniqueness made explicit, the actual
MORK result is a permutation of the complete canonical successor. -/
theorem physical_normal_result_perm_reference
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    (physicalNormalResult context).Perm
      (physicalNormalResultReference context) := by
  have resultNodup : (physicalNormalResult context).Nodup :=
    cFireRuleScopedSourceExecFact_list_nodup _ _
      (normalToRejoinSlice_nodup context)
  have referenceNodup : (physicalNormalResultReference context).Nodup :=
    List.Nodup.of_map morkSupportKey referenceMorkNodup
  apply (List.perm_ext_iff_of_nodup resultNodup referenceNodup).2
  intro row
  constructor
  · exact physical_normal_result_rows_within_reference context
      inputMorkNodup row
  · intro member
    exact mem_of_morkSupportContains_of_reference referenceMorkNodup member
      (physical_normal_result_rows_within_reference context inputMorkNodup)
      (physical_normal_result_reference_support_complete context
        inputMorkNodup row member)

/-- The exact physical successor of the normal-result firing supplies every
row consumed by the compressed rejoin matcher.  The matcher is run over the
actual MORK result, not over a reconstructed fixture. -/
theorem physical_normal_result_supplies_exact_rejoin
    (context : NormalResultContext)
    (inputMorkNodup : MorkSupportNodup (normalToRejoinSlice context))
    (referenceMorkNodup : MorkSupportNodup
      (physicalNormalResultReference context)) :
    ExactCompressedAssertionRejoin context.rejoinContext
      (physicalNormalResult context) := by
  have perm := physical_normal_result_perm_reference context inputMorkNodup
    referenceMorkNodup
  have physicalMember {row : Atom}
      (member : row ∈ physicalNormalResultReference context) :
      row ∈ physicalNormalResult context :=
    perm.mem_iff.mpr member
  have physicalLive {row : Atom}
      (member : row ∈ physicalNormalResultReference context)
      (different : row ≠ compressedAssertionRejoinDirective.atom) :
      row ∈ (physicalNormalResult context).erase
        compressedAssertionRejoinDirective.atom :=
    (List.mem_erase_of_ne different).2 (physicalMember member)
  apply exact_compressed_assertion_rejoin_of_live_rows
  · apply physicalLive
    · simp [physicalNormalResultReference, normalToRejoinSlice]
    · simp [RejoinContext.contextRow, compressedAssertionRejoinDirective,
        compressedAssertionRejoinRule]
  · apply physicalLive
    · simp [physicalNormalResultReference]
    · simp [RejoinContext.returnedControlRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule]
  · apply physicalLive
    · simp [physicalNormalResultReference]
    · simp [RejoinContext.returnedStackRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule]
  · apply physicalLive
    · simp [physicalNormalResultReference, normalToRejoinSlice]
    · simp [RejoinContext.normalStackSuccessorRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule]
  · apply physicalLive
    · simp [physicalNormalResultReference, normalToRejoinSlice]
    · simp [RejoinContext.nodeSuccessorRow, compressedIndexSuccessorRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule]
  · apply physicalLive
    · simp [physicalNormalResultReference, normalToRejoinSlice]
    · simp [RejoinContext.normalLabelRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule]
  · apply physicalLive
    · simp [physicalNormalResultReference, normalToRejoinSlice]
    · simp [RejoinContext.resumeCaptureRow, compressedOwnedRuntimeRuleRow,
        compressedAssertionRejoinDirective, compressedAssertionRejoinRule]

theorem normalToRejoinSlice_ruleScoped_steps
    (context : NormalResultContext) :
    cRuleScopedSourceWorkQueueStep .leaveInert
        (normalToRejoinSlice context) =
      some (physicalNormalResult context) := by
  unfold cRuleScopedSourceWorkQueueStep physicalNormalResult
  rw [normalToRejoinSlice_selects_normal_result]

/-- One canonical completed normal result is an actual scheduled MORK step,
with exact physical outputs and a native-type trace generated by OSLF. -/
structure PhysicalCanonicalNormalResultStep
    (context : NormalResultContext) : Prop where
  listNodup : (normalToRejoinSlice context).Nodup
  morkNodup : MorkSupportNodup (normalToRejoinSlice context)
  exactPhysicalMatch : PhysicalExactNormalResultRejoin context
    (normalToRejoinSlice context)
  concreteStep : cRuleScopedSourceWorkQueueStep .leaveInert
      (normalToRejoinSlice context) = some (physicalNormalResult context)
  concreteTrace : Nonempty (CRuleScopedTrace .leaveInert 1
    (normalToRejoinSlice context) (physicalNormalResult context))
  nativeTypeTrace : Nonempty (RuleScopedNativeTypeTrace .leaveInert 1
    (normalToRejoinSlice context) (physicalNormalResult context))
  outputSupport :
    morkSupportContains (physicalNormalResult context)
        context.rejoinContext.returnedControlRow = true ∧
      morkSupportContains (physicalNormalResult context)
        context.rejoinContext.returnedStackRow = true ∧
      morkSupportContains (physicalNormalResult context)
        (normalAssertionReloadAtom context.proofOwner) = true ∧
      morkSupportContains (physicalNormalResult context)
        compressedAssertionRejoinRule = true
  resultListNodup : (physicalNormalResult context).Nodup
  resultMorkNodup : MorkSupportNodup (physicalNormalResult context)

def physical_canonical_normal_result_step
    (context : NormalResultContext)
    (morkNodup : MorkSupportNodup (normalToRejoinSlice context)) :
    PhysicalCanonicalNormalResultStep context := by
  have listNodup := normalToRejoinSlice_nodup context
  have directivePresent : normalResultDirective.atom ∈
      normalToRejoinSlice context := by
    simp [normalToRejoinSlice]
  have exactPhysical := physical_exact_normal_result_rejoin_of_reflective
    context listNodup morkNodup directivePresent
      (canonical_exact_normal_result_rejoin context)
  have moved := normalToRejoinSlice_ruleScoped_steps context
  let trace : CRuleScopedTrace .leaveInert 1 (normalToRejoinSlice context)
      (physicalNormalResult context) := .step moved .refl
  exact
    { listNodup := listNodup
      morkNodup := morkNodup
      exactPhysicalMatch := exactPhysical
      concreteStep := moved
      concreteTrace := ⟨trace⟩
      nativeTypeTrace := ⟨trace.toNativeTypeTrace⟩
      outputSupport :=
        physical_normal_result_support_present context
          (normalToRejoinSlice context) exactPhysical
      resultListNodup := cFireRuleScopedSourceExecFact_list_nodup _ _
        listNodup
      resultMorkNodup := cFireRuleScopedSourceExecFact_mork_nodup _ _
        morkNodup }

#print axioms normalResultDirective_guards_exact
#print axioms normalResultDirective_sinks_variablesInherited
#print axioms normalResultDirective_supportSet
#print axioms physical_normal_result_matcher_mem_iff
#print axioms physical_exact_normal_result_rejoin_of_reflective
#print axioms physical_normal_result_matcher_interface_exact
#print axioms physical_normal_result_support_present
#print axioms physical_normal_result_preserves_row_of_exact_cursor
#print axioms physical_normal_result_preserves_row
#print axioms physical_normal_result_preserves_runtime_capture
#print axioms physical_normal_result_preserves_rejoin_inputs
#print axioms physical_normal_result_consumes_body
#print axioms physical_normal_result_rows_within_reference
#print axioms physical_normal_result_reference_support_complete
#print axioms physical_normal_result_perm_reference
#print axioms physical_normal_result_supplies_exact_rejoin
#print axioms normalToRejoinSlice_ruleScoped_steps
#print axioms physical_canonical_normal_result_step

end Mettapedia.Languages.Metamath.MM2CompressedProofPhysicalNormalResult
