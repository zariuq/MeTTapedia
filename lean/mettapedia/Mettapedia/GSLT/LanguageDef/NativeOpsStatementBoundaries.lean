import Mettapedia.GSLT.LanguageDef.NativeOpsControlContinuation
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceSwitchReturns
import Mettapedia.GSLT.LanguageDef.NativeOpsTargetSwitchReturns
import Mettapedia.GSLT.LanguageDef.NativeOpsFunctionParameters

/-!
# Structured local compilation and continuation boundaries

The statement, block and ordered switch-arm laws follow every successful
lowering. Jumps target enclosing loops or fresh identifiers; visible labels
lie within the allocated supply. These facts preserve an actual tail run
under its compiled earlier sibling. A mutual factory supplies preservation
and reflection for the supported structured local statement and block
family, including ordered switch arms and their fallback, using the actual
source and lowered executions. The function comparison includes checked
parameter binding, entry guards, the unit-return suffix and lexical teardown.
It preserves and reflects the complete caller state and returned observation.
Whole-program operational adequacy and arbitrary heap/call contracts remain
separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Label)

/-- An emitted jump targets an enclosing loop or a freshly allocated label.
    This excludes jumps into the label interval of an earlier sibling. -/
def CompilerJumpOrigin (loops : List NativeIR.LoopLabels) (bound : Nat) (label : Label) : Prop :=
  (∃ active ∈ loops, label = active.entry ∨ label = active.exit) ∨ bound < label.identity

theorem compiler_jump_origin_weaken {loops : List NativeIR.LoopLabels} {lower upper : Nat}
    (inside : lower ≤ upper) (label : Label) (origin : CompilerJumpOrigin loops upper label) :
    CompilerJumpOrigin loops lower label := by
  rcases origin with old | fresh
  · exact Or.inl old
  · exact Or.inr (inside.trans_lt fresh)

theorem compiler_jump_origin_fresh_loop (supply : NativeIR.Supply)
    {loops : List NativeIR.LoopLabels} {after : Nat}
    (allocated : (NativeIR.fresh (NativeIR.fresh supply).2).2.next ≤ after)
    (label : Label) (origin : CompilerJumpOrigin (freshLoopLabels supply :: loops) after label) :
    CompilerJumpOrigin loops supply.next label := by
  rcases origin with ⟨active, member, same⟩ | fresh
  · rcases List.mem_cons.mp member with new | old
    · subst active
      rcases same with entered | exited
      · subst label
        exact Or.inr (fresh_loop_labels_above_supply supply).1
      · subst label
        exact Or.inr ((fresh_loop_labels_above_supply supply).1.trans
          (fresh_loop_labels_above_supply supply).2)
    · exact Or.inl ⟨active, old, same⟩
  · exact Or.inr ((NativeIR.fresh_strict supply).trans_le
      ((NativeIR.fresh_strict (NativeIR.fresh supply).2).le.trans allocated) |>.trans fresh)

theorem expression_jumps_respect {interface : Interface} {scope : Scope} {expression : Expr}
    {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.expression? interface scope expression supply = some output)
    (accept : Label → Prop) : CodeJumpsRespect accept output.code :=
  jump_free_code_respects accept (expression_lowering_jump_free interface scope expression supply output compiled)

theorem location_jumps_respect {interface : Interface} {scope : Scope} {location : Expr}
    {supply : NativeIR.Supply} {output : NativeLowering.Expression}
    (compiled : NativeLowering.location? interface scope location supply = some output)
    (accept : Label → Prop) : CodeJumpsRespect accept output.code :=
  jump_free_code_respects accept (location_lowering_jump_free interface scope location supply output compiled)

mutual
  theorem statement_lowering_jump_origins {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope} {statement : Statement}
      {supply : NativeIR.Supply} {output : NativeLowering.Block}
      (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.statement? interface result loops scope statement supply = some output) :
      CodeJumpsRespect (CompilerJumpOrigin loops supply.next) output.code := by
    cases statement with
    | declare name type initializer =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := declaration_lowering_exact compiled
        subst output
        exact (code_jumps_respect_append _ _ _).mpr
          ⟨expression_jumps_respect lowered _, by simp only [CodeJumpsRespect, InstructionJumpsRespect]; trivial⟩
    | set location child =>
        obtain ⟨nextScope, place, value, _, located, lowered, same⟩ := set_lowering_exact compiled
        subst output
        exact (code_jumps_respect_append _ _ _).mpr
          ⟨(code_jumps_respect_append _ _ _).mpr
            ⟨location_jumps_respect located _, expression_jumps_respect lowered _⟩,
            by simp only [CodeJumpsRespect, InstructionJumpsRespect]; trivial⟩
    | branch condition yes no =>
        obtain ⟨nextScope, test, whenTrue, whenFalse, _, testCompiled, yesCompiled, noCompiled, same⟩ :=
          branch_lowering_exact compiled
        have testBound := (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
        have yesBound := block_lowering_bounds (loop_labels_within_weaken testBound bounded) yesCompiled
        have yesOrigin := block_lowering_jump_origins (loop_labels_within_weaken testBound bounded) yesCompiled
        have noOrigin := block_lowering_jump_origins
          (loop_labels_within_weaken yesBound.1 (loop_labels_within_weaken testBound bounded)) noCompiled
        subst output
        apply (code_jumps_respect_append _ _ _).mpr
        refine ⟨expression_jumps_respect testCompiled _, ?_⟩
        simp only [CodeJumpsRespect, InstructionJumpsRespect]
        exact ⟨⟨code_jumps_respect_mono (compiler_jump_origin_weaken testBound) yesOrigin,
          code_jumps_respect_mono (compiler_jump_origin_weaken (testBound.trans yesBound.1)) noOrigin⟩, True.intro⟩
    | «while» condition body =>
        obtain ⟨nextScope, test, iteration, _, testCompiled, bodyCompiled, same⟩ := while_lowering_exact compiled
        have testBound := (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
        have bodyOrigin := block_lowering_jump_origins
          (loop_labels_within_weaken testBound (fresh_loop_labels_within supply bounded)) bodyCompiled
        have entryOrigin : CompilerJumpOrigin loops supply.next (freshLoopLabels supply).entry :=
          Or.inr (fresh_loop_labels_above_supply supply).1
        have exitOrigin : CompilerJumpOrigin loops supply.next (freshLoopLabels supply).exit :=
          Or.inr ((fresh_loop_labels_above_supply supply).1.trans (fresh_loop_labels_above_supply supply).2)
        subst output
        simp only [CodeJumpsRespect, InstructionJumpsRespect]
        refine ⟨True.intro, ?_, True.intro, True.intro⟩
        apply (code_jumps_respect_append _ _ _).mpr
        refine ⟨(code_jumps_respect_append _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
        · apply (code_jumps_respect_append _ _ _).mpr
          refine ⟨expression_jumps_respect testCompiled _, ?_⟩
          simp only [CodeJumpsRespect, InstructionJumpsRespect]
          exact ⟨⟨⟨exitOrigin, True.intro⟩, True.intro⟩, True.intro⟩
        · exact code_jumps_respect_mono (compiler_jump_origin_fresh_loop supply testBound) bodyOrigin
        · simpa only [CodeJumpsRespect, InstructionJumpsRespect] using And.intro entryOrigin True.intro
    | switch selector arms otherwise =>
        rw [NativeLowering.statement?] at compiled
        obtain ⟨nextScope, _, compiled⟩ := Option.bind_eq_some_iff.mp compiled
        obtain ⟨selected, selectorCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
        obtain ⟨armOutput, armsCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
        obtain ⟨defaultOutput, otherwiseCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
        have selectorBound := (expression_lowering_boundary _ _ _ _ _ selectorCompiled).monotone
        have armBound := cases_lowering_bounds (loop_labels_within_weaken selectorBound bounded) armsCompiled
        have armOrigin := cases_lowering_jump_origins (loop_labels_within_weaken selectorBound bounded) armsCompiled
        have defaultOrigin := block_lowering_jump_origins
          (loop_labels_within_weaken armBound.1 (loop_labels_within_weaken selectorBound bounded)) otherwiseCompiled
        cases Option.some.inj compiled
        apply (code_jumps_respect_append _ _ _).mpr
        refine ⟨expression_jumps_respect selectorCompiled _, ?_⟩
        simp only [CodeJumpsRespect, InstructionJumpsRespect]
        exact ⟨⟨arm_jumps_respect_mono (compiler_jump_origin_weaken selectorBound) armOrigin,
          code_jumps_respect_mono (compiler_jump_origin_weaken (selectorBound.trans armBound.1)) defaultOrigin⟩, True.intro⟩
    | «break» =>
        obtain ⟨active, outer, same, outputSame⟩ := break_lowering_exact compiled
        subst loops
        subst output
        simp only [CodeJumpsRespect, InstructionJumpsRespect]
        exact ⟨Or.inl ⟨active, List.mem_cons_self, Or.inr rfl⟩, True.intro⟩
    | «continue» =>
        obtain ⟨active, outer, same, outputSame⟩ := continue_lowering_exact compiled
        subst loops
        subst output
        simp only [CodeJumpsRespect, InstructionJumpsRespect]
        exact ⟨Or.inl ⟨active, List.mem_cons_self, Or.inl rfl⟩, True.intro⟩
    | effect child =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := effect_lowering_exact compiled
        subst output
        exact expression_jumps_respect lowered _
    | free child =>
        rw [NativeLowering.statement?] at compiled
        obtain ⟨nextScope, _, compiled⟩ := Option.bind_eq_some_iff.mp compiled
        obtain ⟨type, _, compiled⟩ := Option.bind_eq_some_iff.mp compiled
        obtain ⟨value, lowered, compiled⟩ := Option.bind_eq_some_iff.mp compiled
        cases type with
        | ref element | array element =>
            cases Option.some.inj compiled
            exact (code_jumps_respect_append _ _ _).mpr
              ⟨expression_jumps_respect lowered _, by simp only [CodeJumpsRespect, InstructionJumpsRespect]; trivial⟩
        | _ => cases compiled
    | «return» expression =>
        cases expression with
        | none =>
            obtain ⟨_, same⟩ := return_unit_lowering_exact compiled
            subst output
            simp only [CodeJumpsRespect, InstructionJumpsRespect]
            trivial
        | some expression =>
            obtain ⟨nextScope, value, _, lowered, same⟩ := return_value_lowering_exact compiled
            subst output
            exact (code_jumps_respect_append _ _ _).mpr
              ⟨expression_jumps_respect lowered _, by simp only [CodeJumpsRespect, InstructionJumpsRespect]; trivial⟩
    | block body =>
        obtain ⟨nextScope, inner, _, lowered, same⟩ := block_statement_lowering_exact compiled
        have origin := block_lowering_jump_origins bounded lowered
        subst output
        simp only [CodeJumpsRespect, InstructionJumpsRespect]
        exact ⟨origin, True.intro⟩
  termination_by sizeOf statement
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem block_lowering_jump_origins {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope} {body : List Statement}
      {supply : NativeIR.Supply} {output : NativeLowering.Block}
      (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.block? interface result loops scope body supply = some output) :
      CodeJumpsRespect (CompilerJumpOrigin loops supply.next) output.code := by
    cases body with
    | nil =>
        rw [NativeLowering.block?] at compiled
        cases Option.some.inj compiled
        simp only [CodeJumpsRespect]
    | cons first rest =>
        obtain ⟨head, tail, headCompiled, tailCompiled, same⟩ := block_cons_lowering_exact compiled
        have headBounds := statement_lowering_bounds bounded headCompiled
        have headOrigin := statement_lowering_jump_origins bounded headCompiled
        have tailOrigin := block_lowering_jump_origins
          (loop_labels_within_weaken headBounds.1 bounded) tailCompiled
        subst output
        exact (code_jumps_respect_append _ _ _).mpr
          ⟨headOrigin, code_jumps_respect_mono (compiler_jump_origin_weaken headBounds.1) tailOrigin⟩
  termination_by sizeOf body
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem cases_lowering_jump_origins {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope}
      {arms : List (NativeWord64.Word × List Statement)} {supply : NativeIR.Supply}
      {output : NativeLowering.Cases} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.cases? interface result loops scope arms supply = some output) :
      ArmJumpsRespect (CompilerJumpOrigin loops supply.next) output.cases := by
    cases arms with
    | nil =>
        rw [NativeLowering.cases?] at compiled
        cases Option.some.inj compiled
        simp only [ArmJumpsRespect]
    | cons arm rest =>
        cases arm with
        | mk selector body =>
            rw [NativeLowering.cases?] at compiled
            obtain ⟨bodyOutput, bodyCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
            obtain ⟨restOutput, restCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
            have bodyBounds := block_lowering_bounds bounded bodyCompiled
            have bodyOrigin := block_lowering_jump_origins bounded bodyCompiled
            have restOrigin := cases_lowering_jump_origins
              (loop_labels_within_weaken bodyBounds.1 bounded) restCompiled
            cases Option.some.inj compiled
            exact (arm_jumps_respect_cons _ _ _).mpr
              ⟨bodyOrigin, arm_jumps_respect_mono (compiler_jump_origin_weaken bodyBounds.1) restOrigin⟩
  termination_by sizeOf arms
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega
end

/-- Selection follows the actual ordered arm compiler. The chosen block
    retains its own initial supply, including allocations for earlier arms,
    and its code is exactly the target's selected code. -/
theorem cases_lowering_selection {interface : Interface} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope}
    {arms : List (NativeWord64.Word × List Statement)} {otherwise : List Statement}
    {supply : NativeIR.Supply} {output : NativeLowering.Cases} {fallback : NativeLowering.Block}
    (bounded : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.cases? interface result loops scope arms supply = some output)
    (defaultCompiled : NativeLowering.block? interface result loops scope otherwise output.supply = some fallback)
    (value : NativeWord64.Word) :
    ∃ selectedSupply selectedBlock,
      NativeLowering.block? interface result loops scope (sourceSelectCase value arms otherwise)
        selectedSupply = some selectedBlock ∧
      targetSelectCase (NativeWord64.encode value) output.cases fallback.code = selectedBlock.code ∧
      supply.next ≤ selectedSupply.next ∧ selectedBlock.supply.next ≤ fallback.supply.next := by
  induction arms generalizing supply output with
  | nil =>
      rw [NativeLowering.cases?] at compiled
      cases Option.some.inj compiled
      exact ⟨supply, fallback, defaultCompiled, rfl, Nat.le_refl _, Nat.le_refl _⟩
  | cons arm rest ih =>
      rcases arm with ⟨key, body⟩
      rw [NativeLowering.cases?] at compiled
      obtain ⟨bodyOutput, bodyCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨restOutput, restCompiled, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      have bodyBounds := block_lowering_bounds bounded bodyCompiled
      have restBounds := cases_lowering_bounds (loop_labels_within_weaken bodyBounds.1 bounded) restCompiled
      cases Option.some.inj compiled
      have sameKey : (NativeWord64.encode key == NativeWord64.encode value) = (key == value) := by
        apply Bool.eq_iff_iff.mpr
        change decide (NativeWord64.encode key = NativeWord64.encode value) = true ↔
          decide (key = value) = true
        simp only [decide_eq_true_eq, ← BitVec.toNat_inj, NativeWord64.encode_toNat, Fin.ext_iff]
      by_cases selected : key == value
      · refine ⟨supply, bodyOutput, ?_, ?_, Nat.le_refl _, ?_⟩
        · simpa [sourceSelectCase, selected] using bodyCompiled
        · simp [targetSelectCase, sameKey, selected]
        · exact restBounds.1.trans
            (block_lowering_bounds (loop_labels_within_weaken restBounds.1
              (loop_labels_within_weaken bodyBounds.1 bounded)) defaultCompiled).1
      · obtain ⟨selectedSupply, selectedBlock, selectedCompiled, sameCode, start, finish⟩ :=
          ih (loop_labels_within_weaken bodyBounds.1 bounded) restCompiled defaultCompiled
        refine ⟨selectedSupply, selectedBlock, ?_, ?_, bodyBounds.1.trans start, finish⟩
        · simpa [sourceSelectCase, selected] using selectedCompiled
        · simpa [targetSelectCase, sameKey, selected] using sameCode

theorem statement_lowering_top_label_bound {interface : Interface} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {statement : Statement}
    {supply : NativeIR.Supply} {output : NativeLowering.Block}
    (bounded : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface result loops scope statement supply = some output) :
    TopLabelsAtMost output.supply.next output.code := by
  cases statement with
  | declare name type initializer =>
      obtain ⟨nextScope, value, _, lowered, same⟩ := declaration_lowering_exact compiled
      subst output
      exact (top_labels_at_most_append _ _ _).mpr
        ⟨top_labels_at_most_of_label_free (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _,
          top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)⟩
  | set location child =>
      obtain ⟨nextScope, place, value, _, located, lowered, same⟩ := set_lowering_exact compiled
      subst output
      exact (top_labels_at_most_append _ _ _).mpr
        ⟨(top_labels_at_most_append _ _ _).mpr
          ⟨top_labels_at_most_of_label_free (location_lowering_boundary _ _ _ _ _ located).labelFree _,
            top_labels_at_most_of_label_free (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _⟩,
          top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)⟩
  | branch condition yes no =>
      obtain ⟨nextScope, test, whenTrue, whenFalse, _, lowered, _, _, same⟩ := branch_lowering_exact compiled
      subst output
      exact (top_labels_at_most_append _ _ _).mpr
        ⟨top_labels_at_most_of_label_free (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _,
          top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)⟩
  | «while» condition body =>
      obtain ⟨nextScope, test, iteration, _, testCompiled, bodyCompiled, same⟩ := while_lowering_exact compiled
      have testBound := (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
      have bodyBounds := block_lowering_bounds
        (loop_labels_within_weaken testBound (fresh_loop_labels_within supply bounded)) bodyCompiled
      have exitBound : (freshLoopLabels supply).exit.identity ≤ iteration.supply.next :=
        testBound.trans bodyBounds.1
      have entryBound : (freshLoopLabels supply).entry.identity ≤ iteration.supply.next :=
        (fresh_loop_labels_above_supply supply).2.le.trans exitBound
      subst output
      intro label member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with entered | impossible | exited
      · cases Instruction.label.inj entered
        exact entryBound
      · cases impossible
      · cases Instruction.label.inj exited
        exact exitBound
  | switch selector arms otherwise =>
      rw [NativeLowering.statement?] at compiled
      obtain ⟨nextScope, _, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨value, lowered, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨arms, _, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨otherwise, _, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      cases Option.some.inj compiled
      exact (top_labels_at_most_append _ _ _).mpr
        ⟨top_labels_at_most_of_label_free (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _,
          top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)⟩
  | «break» =>
      obtain ⟨active, outer, _, same⟩ := break_lowering_exact compiled
      subst output
      exact top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)
  | «continue» =>
      obtain ⟨active, outer, _, same⟩ := continue_lowering_exact compiled
      subst output
      exact top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)
  | effect child =>
      obtain ⟨nextScope, value, _, lowered, same⟩ := effect_lowering_exact compiled
      subst output
      exact top_labels_at_most_of_label_free (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _
  | free child =>
      rw [NativeLowering.statement?] at compiled
      obtain ⟨nextScope, _, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨type, _, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      obtain ⟨value, lowered, compiled⟩ := Option.bind_eq_some_iff.mp compiled
      cases type with
      | ref element | array element =>
          cases Option.some.inj compiled
          apply (top_labels_at_most_append _ _ _).mpr
          refine ⟨top_labels_at_most_of_label_free (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _, ?_⟩
          intro label member
          simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, false_or] at member
      | _ => cases compiled
  | «return» expression =>
      cases expression with
      | none =>
          obtain ⟨_, same⟩ := return_unit_lowering_exact compiled
          subst output
          exact top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)
      | some expression =>
          obtain ⟨nextScope, value, _, lowered, same⟩ := return_value_lowering_exact compiled
          subst output
          exact (top_labels_at_most_append _ _ _).mpr
            ⟨top_labels_at_most_of_label_free (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _,
              top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)⟩
  | block body =>
      obtain ⟨nextScope, inner, _, _, same⟩ := block_statement_lowering_exact compiled
      subst output
      exact top_labels_at_most_singleton _ _ (fun _ impossible => by cases impossible)

theorem block_lowering_top_label_bound {interface : Interface} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {body : List Statement}
    {supply : NativeIR.Supply} {output : NativeLowering.Block}
    (bounded : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.block? interface result loops scope body supply = some output) :
    TopLabelsAtMost output.supply.next output.code := by
  induction body generalizing scope supply output with
  | nil =>
      rw [NativeLowering.block?] at compiled
      cases Option.some.inj compiled
      intro label impossible
      cases impossible
  | cons first rest ih =>
      obtain ⟨head, tail, headCompiled, tailCompiled, same⟩ := block_cons_lowering_exact compiled
      have headBounds := statement_lowering_bounds bounded headCompiled
      have tailBounds := block_lowering_bounds (loop_labels_within_weaken headBounds.1 bounded) tailCompiled
      have headLabels := statement_lowering_top_label_bound bounded headCompiled
      have tailLabels := ih (loop_labels_within_weaken headBounds.1 bounded) tailCompiled
      subst output
      exact (top_labels_at_most_append _ _ _).mpr
        ⟨top_labels_at_most_weaken tailBounds.1 headLabels, tailLabels⟩

/-- Earlier compiler labels lie between the incoming and outgoing supplies.
    Neither an active outer label nor a later fresh label can resolve there. -/
theorem compiled_head_misses_tail_origins {interface : Interface} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {first : Statement}
    {supply : NativeIR.Supply} {head : NativeLowering.Block}
    (bounded : LoopLabelsWithin supply.next loops)
    (headCompiled : NativeLowering.statement? interface result loops scope first supply = some head)
    (label : Label) (origin : CompilerJumpOrigin loops head.supply.next label) :
    targetAfterLabel? head.code label = none := by
  have headBounds := statement_lowering_bounds bounded headCompiled
  have headLabels := statement_lowering_top_label_bound bounded headCompiled
  rcases origin with ⟨active, member, entered | exited⟩ | fresh
  · subst label
    exact after_label_none_of_above headBounds.2.2 (bounded active member).1
  · subst label
    exact after_label_none_of_above headBounds.2.2 (bounded active member).2
  · exact after_label_none_of_at_most headLabels fresh

/-- The actual compiled tail can be run under its own or the complete root.
    Both directions preserve states, lexical effects and the full outcome. -/
theorem compiled_tail_root_prefix_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {first : Statement} {rest : List Statement}
    {supply : NativeIR.Supply} {head tail : NativeLowering.Block}
    (bounded : LoopLabelsWithin supply.next loops)
    (headCompiled : NativeLowering.statement? interface result loops scope first supply = some head)
    (tailCompiled : NativeLowering.block? interface result loops head.scope rest head.supply = some tail)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result tail.code tail.code frame state out ↔
      TargetRun interface heap calls result (head.code ++ tail.code) tail.code frame state out := by
  have headBounds := statement_lowering_bounds bounded headCompiled
  have tailOrigin := block_lowering_jump_origins (loop_labels_within_weaken headBounds.1 bounded) tailCompiled
  exact target_run_prefix_root_on_iff head.code tailOrigin tailOrigin
    (compiled_head_misses_tail_origins bounded headCompiled) frame state out

/-- The actual earlier fragment cannot capture a jump from its compiled tail.
    State, lexical effects and the complete outcome are unchanged. -/
theorem compiled_tail_root_prefix_preserves {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {first : Statement} {rest : List Statement}
    {supply : NativeIR.Supply} {head tail : NativeLowering.Block}
    (bounded : LoopLabelsWithin supply.next loops)
    (headCompiled : NativeLowering.statement? interface result loops scope first supply = some head)
    (tailCompiled : NativeLowering.block? interface result loops head.scope rest head.supply = some tail)
    {frame : TargetFrame} {state : TargetState World} {out : TargetBlockOutcome World}
    (ran : TargetRun interface heap calls result tail.code tail.code frame state out) :
    TargetRun interface heap calls result (head.code ++ tail.code) tail.code frame state out :=
  (compiled_tail_root_prefix_iff bounded headCompiled tailCompiled frame state out).mp ran

/-- Actual compiled block sequencing has exactly the source-shaped cases:
    a normal head runs its tail, while a return or outward transfer skips it.
    The tail's own root is recovered in the inverse direction. -/
theorem compiled_block_cons_execution_iff {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {first : Statement} {rest : List Statement}
    {supply : NativeIR.Supply} {head tail : NativeLowering.Block}
    (bounded : LoopLabelsWithin supply.next loops)
    (headCompiled : NativeLowering.statement? interface result loops scope first supply = some head)
    (tailCompiled : NativeLowering.block? interface result loops head.scope rest head.supply = some tail)
    (frame : TargetFrame) (state : TargetState World) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result (head.code ++ tail.code) (head.code ++ tail.code)
        frame state out ↔
      (∃ middle post,
        TargetRun interface heap calls result head.code head.code frame state ⟨.normal, middle, post⟩ ∧
        TargetRun interface heap calls result tail.code tail.code middle post out) ∨
      (∃ headOut, TargetRun interface heap calls result head.code head.code frame state headOut ∧
        headOut.flow ≠ .normal ∧ out = headOut) := by
  have headBounds := statement_lowering_bounds bounded headCompiled
  have tailBounds := block_lowering_bounds (loop_labels_within_weaken headBounds.1 bounded) tailCompiled
  have composed := target_continuation_iff (interface := interface) (heap := heap) (calls := calls) (result := result)
    headBounds.2.1 headBounds.2.1 tailBounds.2.2 frame state out
  constructor
  · intro ran
    obtain ⟨⟨flow, middle, post⟩, headRan, following⟩ := composed.mp ran
    cases flow with
    | normal =>
        cases following with
        | normal tailRan =>
            exact .inl ⟨middle, post, headRan,
              (compiled_tail_root_prefix_iff bounded headCompiled tailCompiled middle post out).mpr tailRan⟩
    | returned value =>
        cases following
        exact .inr ⟨_, headRan, (by intro impossible; cases impossible), rfl⟩
    | jumped label =>
        cases following
        exact .inr ⟨_, headRan, (by intro impossible; cases impossible), rfl⟩
  · rintro (⟨middle, post, headRan, tailRan⟩ | ⟨⟨flow, middle, post⟩, headRan, abrupt, same⟩)
    · exact composed.mpr ⟨_, headRan, .normal
        ((compiled_tail_root_prefix_iff bounded headCompiled tailCompiled middle post out).mp tailRan)⟩
    · subst out
      cases flow with
      | normal => exact False.elim (abrupt rfl)
      | returned value => exact composed.mpr ⟨_, headRan, .returned value middle post⟩
      | jumped label => exact composed.mpr ⟨_, headRan, .jumped label middle post⟩

/-- Preservation composes independently supplied head and tail implementations.
    The actual head run establishes the profile required by the tail; an abrupt
    head skips that implementation entirely. No statement law is postulated. -/
theorem compiled_local_block_cons_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {first : Statement} {rest : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    {head tail : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (headCompiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      first supply = some head)
    (tailCompiled : NativeLowering.block? interface result loops head.scope rest head.supply = some tail)
    (supported : SourceLocalControlStatement first)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (headForward : ∀ {sourceOut : SourceBlockOutcome SourceWorld},
      SourceStatementEval interface sourceHeap sourceCalls first sourceFrame source sourceOut →
      ∃ targetOut, TargetRun interface targetHeap targetCalls result head.code head.code
          targetFrame target targetOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut targetOut ∧
        TemporaryNamesBound targetOut.frame head.supply.next ∧ TemporariesScoped targetOut.frame)
    (tailForward : ∀ {middleFrame : SourceFrame} {middle : SourceState SourceWorld}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld}
        {sourceOut : SourceBlockOutcome SourceWorld},
      SourceLocalOutcomeProfile sourceFrame head.scope ⟨.normal, middleFrame, middle⟩ →
      FrameRelated middleFrame nativeFrame → StateRelated worldRelated middle native →
      TemporaryNamesBound nativeFrame head.supply.next → TemporariesScoped nativeFrame →
      SourceBlockEval interface sourceHeap sourceCalls rest middleFrame middle sourceOut →
      ∃ targetOut, TargetRun interface targetHeap targetCalls result tail.code tail.code
          nativeFrame native targetOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut targetOut ∧
        TemporaryNamesBound targetOut.frame tail.supply.next ∧ TemporariesScoped targetOut.frame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceBlockEval interface sourceHeap sourceCalls (first :: rest) sourceFrame source sourceOut) :
    ∃ targetOut, TargetRun interface targetHeap targetCalls result (head.code ++ tail.code)
        (head.code ++ tail.code) targetFrame target targetOut ∧
      ControlOutcomeRelated worldRelated loops default sourceOut targetOut ∧
      TemporaryNamesBound targetOut.frame tail.supply.next ∧ TemporariesScoped targetOut.frame := by
  have headBounds := statement_lowering_bounds loopBounds headCompiled
  have tailBounds := block_lowering_bounds (loop_labels_within_weaken headBounds.1 loopBounds) tailCompiled
  rcases (source_statements_cons_exact first rest sourceFrame source sourceOut).mp ran with
    ⟨middleFrame, middle, headRan, tailRan⟩ | ⟨headRan, abrupt⟩
  · obtain ⟨⟨flow, nativeFrame, native⟩, firstRun, related, nativeBound, nativeScoped⟩ := headForward headRan
    have normal : flow = .normal := (control_flow_normal_iff related.flow).mp rfl
    subst flow
    have profile := compiled_local_statement_source_profile headCompiled headRan supported below coherent tagged clear
    obtain ⟨targetOut, restRun, resultRelated, finalBound, finalScoped⟩ :=
      tailForward profile related.frame related.state nativeBound nativeScoped tailRan
    exact ⟨targetOut,
      (compiled_block_cons_execution_iff loopBounds headCompiled tailCompiled targetFrame target targetOut).mpr
        (.inl ⟨nativeFrame, native, firstRun, restRun⟩), resultRelated, finalBound, finalScoped⟩
  · obtain ⟨targetOut, firstRun, related, nativeBound, nativeScoped⟩ := headForward headRan
    have nativeAbrupt : targetOut.flow ≠ .normal :=
      fun normal => abrupt ((control_flow_normal_iff related.flow).mpr normal)
    exact ⟨targetOut,
      (compiled_block_cons_execution_iff loopBounds headCompiled tailCompiled targetFrame target targetOut).mpr
        (.inr ⟨targetOut, firstRun, nativeAbrupt, rfl⟩), related,
      fun identity present => (nativeBound identity present).trans tailBounds.1, nativeScoped⟩

/-- Reflection starts from the actual complete target run. Its normal/abrupt
    decomposition supplies independent head and tail comparisons; the source
    profile is established from the reflected head rather than assumed. -/
theorem compiled_local_block_cons_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {first : Statement} {rest : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    {head tail : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (headCompiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      first supply = some head)
    (tailCompiled : NativeLowering.block? interface result loops head.scope rest head.supply = some tail)
    (supported : SourceLocalControlStatement first)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (headBackward : ∀ {targetOut : TargetBlockOutcome TargetWorld},
      TargetRun interface targetHeap targetCalls result head.code head.code targetFrame target targetOut →
      ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls first sourceFrame source sourceOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut targetOut ∧
        TemporaryNamesBound targetOut.frame head.supply.next ∧ TemporariesScoped targetOut.frame)
    (tailBackward : ∀ {middleFrame : SourceFrame} {middle : SourceState SourceWorld}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld}
        {targetOut : TargetBlockOutcome TargetWorld},
      SourceLocalOutcomeProfile sourceFrame head.scope ⟨.normal, middleFrame, middle⟩ →
      FrameRelated middleFrame nativeFrame → StateRelated worldRelated middle native →
      TemporaryNamesBound nativeFrame head.supply.next → TemporariesScoped nativeFrame →
      TargetRun interface targetHeap targetCalls result tail.code tail.code nativeFrame native targetOut →
      ∃ sourceOut, SourceBlockEval interface sourceHeap sourceCalls rest middleFrame middle sourceOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut targetOut ∧
        TemporaryNamesBound targetOut.frame tail.supply.next ∧ TemporariesScoped targetOut.frame)
    {targetOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result (head.code ++ tail.code)
      (head.code ++ tail.code) targetFrame target targetOut) :
    ∃ sourceOut, SourceBlockEval interface sourceHeap sourceCalls (first :: rest) sourceFrame source sourceOut ∧
      ControlOutcomeRelated worldRelated loops default sourceOut targetOut ∧
      TemporaryNamesBound targetOut.frame tail.supply.next ∧ TemporariesScoped targetOut.frame := by
  have headBounds := statement_lowering_bounds loopBounds headCompiled
  have tailBounds := block_lowering_bounds (loop_labels_within_weaken headBounds.1 loopBounds) tailCompiled
  rcases (compiled_block_cons_execution_iff loopBounds headCompiled tailCompiled targetFrame target targetOut).mp ran with
    ⟨nativeFrame, native, headRan, tailRan⟩ | ⟨prefixOut, headRan, abrupt, same⟩
  · obtain ⟨⟨flow, middleFrame, middle⟩, firstRun, related, nativeBound, nativeScoped⟩ := headBackward headRan
    have normal : flow = .normal := (control_flow_normal_iff related.flow).mpr rfl
    subst flow
    have profile := compiled_local_statement_source_profile headCompiled firstRun supported below coherent tagged clear
    obtain ⟨sourceOut, restRun, resultRelated, finalBound, finalScoped⟩ :=
      tailBackward profile related.frame related.state nativeBound nativeScoped tailRan
    exact ⟨sourceOut, .cons firstRun restRun, resultRelated, finalBound, finalScoped⟩
  · subst targetOut
    obtain ⟨sourceOut, firstRun, related, nativeBound, nativeScoped⟩ := headBackward headRan
    have sourceAbrupt : sourceOut.flow ≠ .normal :=
      fun normal => abrupt ((control_flow_normal_iff related.flow).mp normal)
    exact ⟨sourceOut, .stop firstRun sourceAbrupt, related,
      fun identity present => (nativeBound identity present).trans tailBounds.1, nativeScoped⟩

/-- A separately evaluated prefix without visible labels cannot intercept an
    outward branch jump. The selected body retains its own execution root. -/
theorem target_branch_after_prefix_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {earlier yes no : List Instruction} (labelFree : TopLabelFree earlier)
    {condition : NativeIR.Condition} {selected : Bool}
    {frame : TargetFrame} {state : TargetState World}
    (tested : TargetConditionEval interface frame state condition selected)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result (earlier ++ [.branch condition yes no])
      [.branch condition yes no] frame state out ↔
      ∃ inner, TargetRun interface heap calls result
        (if selected then yes else no) (if selected then yes else no) frame state inner ∧
        out = targetCloseBlock frame inner :=
  (target_label_free_prefix_root_iff labelFree _ _ frame state out).trans
    (target_branch_body_exact tested out)

/-- Branch preservation uses the actual compiled condition and an independently
    implemented selected block. Faults in the condition skip both blocks. -/
theorem compiled_branch_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {yesBody noBody : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {output : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default condition)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.branch condition yesBody noBody) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (bodyForward : ∀ (selected : Bool) {bodySupply : NativeIR.Supply} {body : NativeLowering.Block}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld} {sourceOut : SourceBlockOutcome SourceWorld},
      NativeLowering.block? interface result loops (sourceFrameScope sourceFrame)
        (if selected then yesBody else noBody) bodySupply = some body →
      LoopLabelsWithin bodySupply.next loops →
      FrameRelated sourceFrame nativeFrame → StateRelated worldRelated source native →
      TemporaryNamesBound nativeFrame bodySupply.next → TemporariesScoped nativeFrame →
      SourceBlockEval interface sourceHeap sourceCalls (if selected then yesBody else noBody)
        sourceFrame source sourceOut →
      ∃ nativeOut, TargetRun interface targetHeap targetCalls result body.code body.code
          nativeFrame native nativeOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame body.supply.next ∧ TemporariesScoped nativeOut.frame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.branch condition yesBody noBody)
      sourceFrame source sourceOut) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result output.code output.code
        targetFrame target nativeOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨nextScope, test, yes, no, _, testCompiled, yesCompiled, noCompiled, same⟩ :=
    branch_lowering_exact compiled
  subst output
  have testBoundary := expression_lowering_boundary _ _ _ _ _ testCompiled
  have testLoops := loop_labels_within_weaken testBoundary.monotone loopBounds
  have yesBounds := block_lowering_bounds testLoops yesCompiled
  have noBounds := block_lowering_bounds (loop_labels_within_weaken yesBounds.1 testLoops) noCompiled
  have jumpFree := expression_lowering_jump_free _ _ _ _ _ testCompiled
  rcases (source_branch_statement_exact condition yesBody noBody sourceFrame source sourceOut).mp ran with
    ⟨selected, middle, inner, tested, bodyRan, same⟩ | ⟨fault, after, tested, same⟩
  · subst sourceOut
    have unchanged : middle = source := child.sourceState tested
    subst middle
    obtain ⟨⟨flow, nativeFrame, post⟩, firstRun, related, protection, afterBound, afterScoped⟩ :=
      child.forward (test.code ++ [.branch (.value test.result) yes.code no.code])
        testCompiled frames states bounded hscope tested
    rcases related with ⟨_, normal, unchanged, read⟩
    cases normal
    change post = target at unchanged
    subst post
    have selectedCompiled : NativeLowering.block? interface result loops (sourceFrameScope sourceFrame)
        (if selected then yesBody else noBody) (if selected then test.supply else yes.supply) =
          some (if selected then yes else no) := by cases selected <;> assumption
    have selectedBound : TemporaryNamesBound nativeFrame
        (if selected then test.supply else yes.supply).next := by
      cases selected
      · exact fun id present => (afterBound id present).trans yesBounds.1
      · exact afterBound
    obtain ⟨nativeOut, bodyRun, bodyRelated, _, _⟩ := bodyForward selected selectedCompiled
      (by cases selected; exact loop_labels_within_weaken yesBounds.1 testLoops; exact testLoops)
      (temporary_protection_preserves_source_frame frames protection) states selectedBound afterScoped bodyRan
    have selectedTest : TargetConditionEval interface nativeFrame target (.value test.result) selected :=
      .value (by simpa only [encodeValue] using read)
    have selectedRun : TargetRun interface targetHeap targetCalls result
        (if selected then yes.code else no.code) (if selected then yes.code else no.code)
        nativeFrame target nativeOut := by cases selected <;> simpa only [Bool.false_eq_true, if_false, if_true] using bodyRun
    have tail : TargetRun interface targetHeap targetCalls result
        (test.code ++ [.branch (.value test.result) yes.code no.code])
        [.branch (.value test.result) yes.code no.code] nativeFrame target
        (targetCloseBlock nativeFrame nativeOut) :=
      (target_branch_after_prefix_exact testBoundary.labelFree selectedTest
        (targetCloseBlock nativeFrame nativeOut)).mpr ⟨nativeOut, selectedRun, rfl⟩
    refine ⟨targetCloseBlock nativeFrame nativeOut,
      target_append_normal _ _ _ jumpFree firstRun tail,
      close_control_outcomes (temporary_protection_preserves_source_frame frames protection) bodyRelated,
      ?_, target_close_block_scoped nativeFrame nativeOut⟩
    exact close_block_temporary_bound
      (fun id present => (afterBound id present).trans (yesBounds.1.trans noBounds.1)) nativeOut
  · subst sourceOut
    have unchanged : after = sourcePoison source fault := child.sourceState tested
    subst after
    obtain ⟨⟨flow, afterFrame, post⟩, firstRun, related, protection, afterBound, afterScoped⟩ :=
      child.forward (test.code ++ [.branch (.value test.result) yes.code no.code])
        testCompiled frames states bounded hscope tested
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    exact ⟨⟨.returned default, afterFrame, targetPoison target fault⟩,
      target_append_returned _ _ [.branch (.value test.result) yes.code no.code] jumpFree firstRun,
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      fun id present => (afterBound id present).trans (yesBounds.1.trans noBounds.1), afterScoped⟩

/-- Reflection decomposes the actual compiled branch run. The condition's
    independently checked boolean tag determines exactly which source block
    ran; a returned fault from the condition never consults either block. -/
theorem compiled_branch_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {yesBody noBody : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {output : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default condition)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.branch condition yesBody noBody) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (bodyBackward : ∀ (selected : Bool) {bodySupply : NativeIR.Supply} {body : NativeLowering.Block}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld} {nativeOut : TargetBlockOutcome TargetWorld},
      NativeLowering.block? interface result loops (sourceFrameScope sourceFrame)
        (if selected then yesBody else noBody) bodySupply = some body →
      LoopLabelsWithin bodySupply.next loops →
      FrameRelated sourceFrame nativeFrame → StateRelated worldRelated source native →
      TemporaryNamesBound nativeFrame bodySupply.next → TemporariesScoped nativeFrame →
      TargetRun interface targetHeap targetCalls result body.code body.code nativeFrame native nativeOut →
      ∃ sourceOut, SourceBlockEval interface sourceHeap sourceCalls
          (if selected then yesBody else noBody) sourceFrame source sourceOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame body.supply.next ∧ TemporariesScoped nativeOut.frame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result output.code output.code
      targetFrame target nativeOut) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.branch condition yesBody noBody)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨nextScope, test, yes, no, checked, testCompiled, yesCompiled, noCompiled, same⟩ :=
    branch_lowering_exact compiled
  obtain ⟨_, _, typing, _, _, _⟩ := branch_checked_scopes checked
  subst output
  have testBoundary := expression_lowering_boundary _ _ _ _ _ testCompiled
  have testLoops := loop_labels_within_weaken testBoundary.monotone loopBounds
  have yesBounds := block_lowering_bounds testLoops yesCompiled
  have noBounds := block_lowering_bounds (loop_labels_within_weaken yesBounds.1 testLoops) noCompiled
  have jumpFree := expression_lowering_jump_free _ _ _ _ _ testCompiled
  rcases target_split_jump_free_prefix _ test.code [.branch (.value test.result) yes.code no.code]
      jumpFree ran with
    ⟨nativeFrame, post, firstRun, tailRun⟩ | ⟨returned, afterFrame, post, firstRun, same⟩
  · obtain ⟨sourceResult, evaluated, related, protection, afterBound, afterScoped⟩ :=
      child.backward (test.code ++ [.branch (.value test.result) yes.code no.code])
        testCompiled frames states bounded hscope firstRun
    obtain ⟨actual, sourceSame, unchanged, read⟩ := guarded_related_normal related rfl
    cases sourceSame
    change post = target at unchanged
    subst post
    have tag := child.sourceTag typing evaluated
    cases tag with
    | bool selected =>
        have selectedTest : TargetConditionEval interface nativeFrame target (.value test.result) selected :=
          .value (by simpa only [encodeValue] using read)
        obtain ⟨inner, bodyRun, same⟩ :=
          (target_branch_after_prefix_exact testBoundary.labelFree selectedTest nativeOut).mp tailRun
        have selectedCompiled : NativeLowering.block? interface result loops (sourceFrameScope sourceFrame)
            (if selected then yesBody else noBody) (if selected then test.supply else yes.supply) =
              some (if selected then yes else no) := by cases selected <;> assumption
        have selectedBound : TemporaryNamesBound nativeFrame
            (if selected then test.supply else yes.supply).next := by
          cases selected
          · exact fun id present => (afterBound id present).trans yesBounds.1
          · exact afterBound
        have selectedRun : TargetRun interface targetHeap targetCalls result
            (if selected then yes else no).code (if selected then yes else no).code
            nativeFrame target inner := by cases selected <;> simpa only [Bool.false_eq_true, if_false, if_true] using bodyRun
        obtain ⟨sourceInner, bodySource, bodyRelated, _, _⟩ := bodyBackward selected selectedCompiled
          (by cases selected; exact loop_labels_within_weaken yesBounds.1 testLoops; exact testLoops)
          (temporary_protection_preserves_source_frame frames protection) states selectedBound afterScoped selectedRun
        subst nativeOut
        exact ⟨sourceCloseBlock sourceFrame sourceInner, .branch evaluated bodySource,
          close_control_outcomes (temporary_protection_preserves_source_frame frames protection) bodyRelated,
          close_block_temporary_bound
            (fun id present => (afterBound id present).trans (yesBounds.1.trans noBounds.1)) inner,
          target_close_block_scoped nativeFrame inner⟩
  · obtain ⟨sourceResult, evaluated, related, protection, afterBound, afterScoped⟩ :=
      child.backward (test.code ++ [.branch (.value test.result) yes.code no.code])
        testCompiled frames states bounded hscope firstRun
    obtain ⟨fault, sourceSame, valueSame, poisoned⟩ := guarded_related_returned related rfl
    cases sourceSame
    subst returned
    change post = targetPoison target fault at poisoned
    subst post
    subst nativeOut
    exact ⟨⟨.fault fault, sourceFrame, sourcePoison source fault⟩, .branchFault evaluated,
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      fun id present => (afterBound id present).trans (yesBounds.1.trans noBounds.1), afterScoped⟩

/-- The selector prefix contains no visible labels. Switch arms retain
    their own execution root, including outward loop transfers. -/
theorem target_switch_after_prefix_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {earlier : List Instruction} (labelFree : TopLabelFree earlier)
    {selector : NativeIR.Atom} {value : BitVec 64}
    {arms : List (BitVec 64 × List Instruction)} {otherwise : List Instruction}
    {frame : TargetFrame} {state : TargetState World}
    (read : TargetAtomEval interface frame state selector (.word value))
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result (earlier ++ [.switch selector arms otherwise])
      [.switch selector arms otherwise] frame state out ↔
      ∃ inner, TargetRun interface heap calls result (targetSelectCase value arms otherwise)
          (targetSelectCase value arms otherwise) frame state inner ∧
        out = targetCloseBlock frame inner := by
  rw [target_label_free_prefix_root_iff labelFree _ _ frame state out,
    target_single_nonlabel_exact _ (fun _ impossible => by cases impossible)]
  exact target_switch_instruction_exact read out

/-- Switch preservation compares the selected block produced by the actual
    arm compiler. A selector fault skips the arms and the fallback. -/
theorem compiled_switch_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {selector : Expr} {arms : List (NativeWord64.Word × List Statement)} {otherwise : List Statement}
    {supply : NativeIR.Supply} {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {output : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default selector)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.switch selector arms otherwise) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (bodyForward : ∀ (value : NativeWord64.Word) {bodySupply : NativeIR.Supply} {body : NativeLowering.Block}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld} {sourceOut : SourceBlockOutcome SourceWorld},
      NativeLowering.block? interface result loops (sourceFrameScope sourceFrame)
        (sourceSelectCase value arms otherwise) bodySupply = some body →
      LoopLabelsWithin bodySupply.next loops →
      FrameRelated sourceFrame nativeFrame → StateRelated worldRelated source native →
      TemporaryNamesBound nativeFrame bodySupply.next → TemporariesScoped nativeFrame →
      SourceBlockEval interface sourceHeap sourceCalls (sourceSelectCase value arms otherwise)
        sourceFrame source sourceOut →
      ∃ nativeOut, TargetRun interface targetHeap targetCalls result body.code body.code
          nativeFrame native nativeOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame body.supply.next ∧ TemporariesScoped nativeOut.frame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.switch selector arms otherwise)
      sourceFrame source sourceOut) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result output.code output.code
        targetFrame target nativeOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨nextScope, test, cases, fallback, _, testCompiled, casesCompiled, fallbackCompiled, same⟩ :=
    switch_lowering_exact compiled
  subst output
  have testBoundary := expression_lowering_boundary _ _ _ _ _ testCompiled
  have testLoops := loop_labels_within_weaken testBoundary.monotone loopBounds
  have casesBounds := cases_lowering_bounds testLoops casesCompiled
  have fallbackBounds := block_lowering_bounds (loop_labels_within_weaken casesBounds.1 testLoops) fallbackCompiled
  have jumpFree := expression_lowering_jump_free _ _ _ _ _ testCompiled
  rcases (source_switch_statement_exact selector arms otherwise sourceFrame source sourceOut).mp ran with
    ⟨value, middle, inner, tested, bodyRan, same⟩ | ⟨fault, after, tested, same⟩
  · subst sourceOut
    have unchanged : middle = source := child.sourceState tested
    subst middle
    obtain ⟨⟨flow, nativeFrame, post⟩, firstRun, related, protection, afterBound, afterScoped⟩ :=
      child.forward (test.code ++ [.switch test.result cases.cases fallback.code])
        testCompiled frames states bounded hscope tested
    rcases related with ⟨_, normal, unchanged, read⟩
    cases normal
    change post = target at unchanged
    subst post
    obtain ⟨bodySupply, body, selectedCompiled, selectedCode, start, _⟩ :=
      cases_lowering_selection testLoops casesCompiled fallbackCompiled value
    obtain ⟨nativeOut, bodyRun, bodyRelated, _, _⟩ := bodyForward value selectedCompiled
      (loop_labels_within_weaken start testLoops)
      (temporary_protection_preserves_source_frame frames protection) states
      (fun id present => (afterBound id present).trans start) afterScoped bodyRan
    have selectedRead : TargetAtomEval interface nativeFrame target test.result (.word (NativeWord64.encode value)) :=
      by simpa only [encodeValue] using read
    have selectedRun : TargetRun interface targetHeap targetCalls result
        (targetSelectCase (NativeWord64.encode value) cases.cases fallback.code)
        (targetSelectCase (NativeWord64.encode value) cases.cases fallback.code)
        nativeFrame target nativeOut := by simpa only [selectedCode] using bodyRun
    have tail : TargetRun interface targetHeap targetCalls result
        (test.code ++ [.switch test.result cases.cases fallback.code])
        [.switch test.result cases.cases fallback.code] nativeFrame target (targetCloseBlock nativeFrame nativeOut) :=
      (target_switch_after_prefix_exact testBoundary.labelFree selectedRead
        (targetCloseBlock nativeFrame nativeOut)).mpr ⟨nativeOut, selectedRun, rfl⟩
    exact ⟨targetCloseBlock nativeFrame nativeOut,
      target_append_normal _ _ _ jumpFree firstRun tail,
      close_control_outcomes (temporary_protection_preserves_source_frame frames protection) bodyRelated,
      close_block_temporary_bound
        (fun id present => (afterBound id present).trans (casesBounds.1.trans fallbackBounds.1)) nativeOut,
      target_close_block_scoped nativeFrame nativeOut⟩
  · subst sourceOut
    have unchanged : after = sourcePoison source fault := child.sourceState tested
    subst after
    obtain ⟨⟨flow, afterFrame, post⟩, firstRun, related, protection, afterBound, afterScoped⟩ :=
      child.forward (test.code ++ [.switch test.result cases.cases fallback.code])
        testCompiled frames states bounded hscope tested
    rcases related with ⟨_, returned, poisoned⟩
    cases returned
    change post = targetPoison target fault at poisoned
    subst post
    exact ⟨⟨.returned default, afterFrame, targetPoison target fault⟩,
      target_append_returned _ _ [.switch test.result cases.cases fallback.code] jumpFree firstRun,
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      fun id present => (afterBound id present).trans (casesBounds.1.trans fallbackBounds.1), afterScoped⟩

/-- Reflection reconstructs a source selector and its actual selected arm
    from the complete emitted execution. Untaken arms contribute no run. -/
theorem compiled_switch_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {selector : Expr} {arms : List (NativeWord64.Word × List Statement)} {otherwise : List Statement}
    {supply : NativeIR.Supply} {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {output : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default selector)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.switch selector arms otherwise) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (bodyBackward : ∀ (value : NativeWord64.Word) {bodySupply : NativeIR.Supply} {body : NativeLowering.Block}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld} {nativeOut : TargetBlockOutcome TargetWorld},
      NativeLowering.block? interface result loops (sourceFrameScope sourceFrame)
        (sourceSelectCase value arms otherwise) bodySupply = some body →
      LoopLabelsWithin bodySupply.next loops →
      FrameRelated sourceFrame nativeFrame → StateRelated worldRelated source native →
      TemporaryNamesBound nativeFrame bodySupply.next → TemporariesScoped nativeFrame →
      TargetRun interface targetHeap targetCalls result body.code body.code nativeFrame native nativeOut →
      ∃ sourceOut, SourceBlockEval interface sourceHeap sourceCalls
          (sourceSelectCase value arms otherwise) sourceFrame source sourceOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame body.supply.next ∧ TemporariesScoped nativeOut.frame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result output.code output.code targetFrame target nativeOut) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.switch selector arms otherwise)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨nextScope, test, cases, fallback, checked, testCompiled, casesCompiled, fallbackCompiled, same⟩ :=
    switch_lowering_exact compiled
  have typing := (switch_checked_type checked).1
  subst output
  have testBoundary := expression_lowering_boundary _ _ _ _ _ testCompiled
  have testLoops := loop_labels_within_weaken testBoundary.monotone loopBounds
  have casesBounds := cases_lowering_bounds testLoops casesCompiled
  have fallbackBounds := block_lowering_bounds (loop_labels_within_weaken casesBounds.1 testLoops) fallbackCompiled
  have jumpFree := expression_lowering_jump_free _ _ _ _ _ testCompiled
  rcases target_split_jump_free_prefix _ test.code [.switch test.result cases.cases fallback.code] jumpFree ran with
    ⟨nativeFrame, post, firstRun, tailRun⟩ | ⟨returned, afterFrame, post, firstRun, same⟩
  · obtain ⟨sourceResult, evaluated, related, protection, afterBound, afterScoped⟩ :=
      child.backward (test.code ++ [.switch test.result cases.cases fallback.code])
        testCompiled frames states bounded hscope firstRun
    obtain ⟨actual, sourceSame, unchanged, read⟩ := guarded_related_normal related rfl
    cases sourceSame
    change post = target at unchanged
    subst post
    have tag := child.sourceTag typing evaluated
    cases tag with
    | word value =>
        have selectedRead : TargetAtomEval interface nativeFrame target test.result (.word (NativeWord64.encode value)) :=
          by simpa only [encodeValue] using read
        obtain ⟨inner, bodyRun, same⟩ :=
          (target_switch_after_prefix_exact testBoundary.labelFree selectedRead nativeOut).mp tailRun
        obtain ⟨bodySupply, body, selectedCompiled, selectedCode, start, _⟩ :=
          cases_lowering_selection testLoops casesCompiled fallbackCompiled value
        have selectedRun : TargetRun interface targetHeap targetCalls result body.code body.code
            nativeFrame target inner := by simpa only [selectedCode] using bodyRun
        obtain ⟨sourceInner, bodySource, bodyRelated, _, _⟩ := bodyBackward value selectedCompiled
          (loop_labels_within_weaken start testLoops)
          (temporary_protection_preserves_source_frame frames protection) states
          (fun id present => (afterBound id present).trans start) afterScoped selectedRun
        subst nativeOut
        exact ⟨sourceCloseBlock sourceFrame sourceInner, .switch evaluated bodySource,
          close_control_outcomes (temporary_protection_preserves_source_frame frames protection) bodyRelated,
          close_block_temporary_bound
            (fun id present => (afterBound id present).trans (casesBounds.1.trans fallbackBounds.1)) inner,
          target_close_block_scoped nativeFrame inner⟩
  · obtain ⟨sourceResult, evaluated, related, protection, afterBound, afterScoped⟩ :=
      child.backward (test.code ++ [.switch test.result cases.cases fallback.code])
        testCompiled frames states bounded hscope firstRun
    obtain ⟨fault, sourceSame, valueSame, poisoned⟩ := guarded_related_returned related rfl
    cases sourceSame
    subst returned
    change post = targetPoison target fault at poisoned
    subst post
    subst nativeOut
    exact ⟨⟨.fault fault, sourceFrame, sourcePoison source fault⟩, .switchFault evaluated,
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      fun id present => (afterBound id present).trans (casesBounds.1.trans fallbackBounds.1), afterScoped⟩

theorem short_circuit_branch_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {yesBody noBody : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {output : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (zero : TargetZero interface result default) (supported : SourceShortCircuitExpression condition)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.branch condition yesBody noBody) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (bodyForward : ∀ (selected : Bool) {bodySupply : NativeIR.Supply} {body : NativeLowering.Block}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld} {sourceOut : SourceBlockOutcome SourceWorld},
      NativeLowering.block? interface result loops (sourceFrameScope sourceFrame)
        (if selected then yesBody else noBody) bodySupply = some body →
      LoopLabelsWithin bodySupply.next loops →
      FrameRelated sourceFrame nativeFrame → StateRelated worldRelated source native →
      TemporaryNamesBound nativeFrame bodySupply.next → TemporariesScoped nativeFrame →
      SourceBlockEval interface sourceHeap sourceCalls (if selected then yesBody else noBody)
        sourceFrame source sourceOut →
      ∃ nativeOut, TargetRun interface targetHeap targetCalls result body.code body.code
          nativeFrame native nativeOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame body.supply.next ∧ TemporariesScoped nativeOut.frame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.branch condition yesBody noBody)
      sourceFrame source sourceOut) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result output.code output.code
        targetFrame target nativeOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame :=
  compiled_branch_child_preservation loopBounds
    (short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source clear tagged result zero supported)
    compiled frames states bounded hscope bodyForward ran

theorem short_circuit_branch_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {yesBody noBody : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {output : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (clear : source.fault = none) (tagged : SourceLocalsTagged sourceFrame source.memory)
    (zero : TargetZero interface result default) (supported : SourceShortCircuitExpression condition)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.branch condition yesBody noBody) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (bodyBackward : ∀ (selected : Bool) {bodySupply : NativeIR.Supply} {body : NativeLowering.Block}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld} {nativeOut : TargetBlockOutcome TargetWorld},
      NativeLowering.block? interface result loops (sourceFrameScope sourceFrame)
        (if selected then yesBody else noBody) bodySupply = some body →
      LoopLabelsWithin bodySupply.next loops →
      FrameRelated sourceFrame nativeFrame → StateRelated worldRelated source native →
      TemporaryNamesBound nativeFrame bodySupply.next → TemporariesScoped nativeFrame →
      TargetRun interface targetHeap targetCalls result body.code body.code nativeFrame native nativeOut →
      ∃ sourceOut, SourceBlockEval interface sourceHeap sourceCalls
          (if selected then yesBody else noBody) sourceFrame source sourceOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame body.supply.next ∧ TemporariesScoped nativeOut.frame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result output.code output.code
      targetFrame target nativeOut) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.branch condition yesBody noBody)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame :=
  compiled_branch_child_reflection loopBounds
    (short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source clear tagged result zero supported)
    compiled frames states bounded hscope bodyBackward ran

/-- A compiled lexical block closes only its own scope after an independently
    compared body. Its complete state and outward flow remain related. -/
theorem compiled_scope_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {body : List Statement} {supply : NativeIR.Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.block body) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame)
    (bounded : TemporaryNamesBound targetFrame supply.next)
    (bodyForward : ∀ {value : NativeLowering.Block} {sourceOut : SourceBlockOutcome SourceWorld},
      NativeLowering.block? interface result loops (sourceFrameScope sourceFrame) body supply = some value →
      SourceBlockEval interface sourceHeap sourceCalls body sourceFrame source sourceOut →
      ∃ nativeOut, TargetRun interface targetHeap targetCalls result value.code value.code
          targetFrame target nativeOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut nativeOut)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.block body) sourceFrame source sourceOut) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result output.code output.code
        targetFrame target nativeOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨nextScope, inner, _, bodyCompiled, same⟩ := block_statement_lowering_exact compiled
  subst output
  cases ran with
  | block bodyRan =>
      obtain ⟨nativeOut, bodyRun, related⟩ := bodyForward bodyCompiled bodyRan
      have bounds := block_lowering_bounds loopBounds bodyCompiled
      exact ⟨targetCloseBlock targetFrame nativeOut,
        (target_scope_body_exact inner.code targetFrame target _).mpr ⟨nativeOut, bodyRun, rfl⟩,
        close_control_outcomes frames related,
        close_block_temporary_bound (fun id present => (bounded id present).trans bounds.1) nativeOut,
        target_close_block_scoped targetFrame nativeOut⟩

/-- The actual scope instruction supplies the body run for backward transport;
    its cleanup is then matched to source cleanup with the same caller marker. -/
theorem compiled_scope_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {body : List Statement} {supply : NativeIR.Supply} {output : NativeLowering.Block}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.block body) supply = some output)
    (frames : FrameRelated sourceFrame targetFrame)
    (bounded : TemporaryNamesBound targetFrame supply.next)
    (bodyBackward : ∀ {value : NativeLowering.Block} {nativeOut : TargetBlockOutcome TargetWorld},
      NativeLowering.block? interface result loops (sourceFrameScope sourceFrame) body supply = some value →
      TargetRun interface targetHeap targetCalls result value.code value.code targetFrame target nativeOut →
      ∃ sourceOut, SourceBlockEval interface sourceHeap sourceCalls body sourceFrame source sourceOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut nativeOut)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result output.code output.code
      targetFrame target nativeOut) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.block body) sourceFrame source sourceOut ∧
      ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨nextScope, inner, _, bodyCompiled, same⟩ := block_statement_lowering_exact compiled
  subst output
  obtain ⟨innerOut, bodyRun, same⟩ := (target_scope_body_exact inner.code targetFrame target _).mp ran
  obtain ⟨sourceOut, bodySource, related⟩ := bodyBackward bodyCompiled bodyRun
  subst nativeOut
  have bounds := block_lowering_bounds loopBounds bodyCompiled
  exact ⟨sourceCloseBlock sourceFrame sourceOut, .block bodySource, close_control_outcomes frames related,
    close_block_temporary_bound (fun id present => (bounded id present).trans bounds.1) innerOut,
    target_close_block_scoped targetFrame innerOut⟩

/-- The actual while body allocates its visible labels after both loop
labels and the condition. Neither enclosing transfer is captured by it. -/
theorem compiled_while_body_misses_loop_labels {interface : Interface} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {condition : Expr} {body : List Statement}
    {supply : NativeIR.Supply} {test : NativeLowering.Expression} {iteration : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (testCompiled : NativeLowering.expression? interface scope condition
      (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test)
    (bodyCompiled : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
      scope body test.supply = some iteration) :
    targetAfterLabel? iteration.code (freshLoopLabels supply).entry = none ∧
      targetAfterLabel? iteration.code (freshLoopLabels supply).exit = none := by
  have testBound := (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
  have activeBounds := loop_labels_within_weaken testBound (fresh_loop_labels_within supply loopBounds)
  have allocated := activeBounds (freshLoopLabels supply) List.mem_cons_self
  have bodyBounds := block_lowering_bounds activeBounds bodyCompiled
  exact ⟨after_label_none_of_above bodyBounds.2.2 allocated.1,
    after_label_none_of_above bodyBounds.2.2 allocated.2⟩

/-- The continuation of the actual compiled test executes the selected
body under its own root. Existing abrupt outcomes remain complete; only
normal completion adds the emitted entry transfer. -/
theorem compiled_while_iteration_tail_exact {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    {loops : List NativeIR.LoopLabels} {scope : Scope} {condition : Expr} {body : List Statement}
    {supply : NativeIR.Supply} {test : NativeLowering.Expression} {iteration : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (testCompiled : NativeLowering.expression? interface scope condition
      (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test)
    (bodyCompiled : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
      scope body test.supply = some iteration)
    {selected : Bool} {frame : TargetFrame} {state : TargetState World}
    (read : TargetAtomEval interface frame state test.result (.bool selected))
    (hscope : TemporariesScoped frame) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result
      (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
        iteration.code ++ [.jump (freshLoopLabels supply).entry])
      ([.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
        iteration.code ++ [.jump (freshLoopLabels supply).entry]) frame state out ↔
      if selected then
        ∃ inner, TargetRun interface heap calls result iteration.code iteration.code frame state inner ∧
          out = targetLoopBackedge (freshLoopLabels supply).entry inner
      else out = ⟨.jumped (freshLoopLabels supply).exit, frame, state⟩ := by
  have boundary := expression_lowering_boundary _ _ _ _ _ testCompiled
  have bodyBounds := block_lowering_bounds
    (loop_labels_within_weaken boundary.monotone (fresh_loop_labels_within supply loopBounds)) bodyCompiled
  obtain ⟨entryOutside, exitOutside⟩ :=
    compiled_while_body_misses_loop_labels loopBounds testCompiled bodyCompiled
  simpa only [List.append_assoc] using
    target_loop_iteration_tail_exact (heap := heap) (calls := calls) (result := result)
      boundary.labelFree bodyBounds.2.1 read hscope
      (freshLoopLabels supply).entry (freshLoopLabels supply).exit entryOutside exitOutside out


/-- The backedge is an emitted transfer, not a second body evaluation.
The normalized source flow and actual target jump preserve the complete
body state, frame and every other abrupt distinction. -/
theorem control_loop_backedge_related {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {loops : List NativeIR.LoopLabels}
    {active : NativeIR.LoopLabels} {default : TargetValue}
    {sourceOut : SourceBlockOutcome SourceWorld} {nativeOut : TargetBlockOutcome TargetWorld}
    (related : ControlOutcomeRelated worldRelated (active :: loops) default sourceOut nativeOut) :
    ControlOutcomeRelated worldRelated (active :: loops) default (sourceLoopBackedge sourceOut)
      (targetLoopBackedge active.entry nativeOut) := by
  rcases sourceOut with ⟨sourceFlow, sourceFrame, source⟩
  rcases nativeOut with ⟨nativeFlow, nativeFrame, native⟩
  rcases related with ⟨states, frames, flows⟩
  cases flows with
  | normal => exact ⟨states, frames, .continued rfl⟩
  | returned value => exact ⟨states, frames, .returned value⟩
  | fault error => exact ⟨states, frames, .fault error⟩
  | broke same => exact ⟨states, frames, .broke same⟩
  | continued same => exact ⟨states, frames, .continued same⟩

/-- A true compiled condition reaches exactly one actual body execution.
Its normal completion adds the backedge; continue already carries it.
No caller state or body contribution is evaluated a second time. -/
theorem compiled_while_true_iteration_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {body : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    {test : NativeLowering.Expression} {iteration : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default condition)
    (testCompiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) condition
      (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test)
    (bodyCompiled : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
      (sourceFrameScope sourceFrame) body test.supply = some iteration)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (bodyForward : ∀ {nativeFrame : TargetFrame} {sourceOut : SourceBlockOutcome SourceWorld},
      FrameRelated sourceFrame nativeFrame → TemporaryNamesBound nativeFrame test.supply.next →
      TemporariesScoped nativeFrame →
      SourceBlockEval interface sourceHeap sourceCalls body sourceFrame source sourceOut →
      ∃ nativeOut, TargetRun interface targetHeap targetCalls result iteration.code iteration.code
          nativeFrame target nativeOut ∧
        ControlOutcomeRelated worldRelated (freshLoopLabels supply :: loops) default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame iteration.supply.next ∧ TemporariesScoped nativeOut.frame)
    {middle : SourceState SourceWorld} {sourceOut : SourceBlockOutcome SourceWorld}
    (tested : SourceExprEval interface sourceHeap sourceCalls sourceFrame condition source
      ⟨.ok (.bool true), middle⟩)
    (bodyRan : SourceBlockEval interface sourceHeap sourceCalls body sourceFrame middle sourceOut) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result
        (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
          iteration.code ++ [.jump (freshLoopLabels supply).entry])
        (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
          iteration.code ++ [.jump (freshLoopLabels supply).entry]) targetFrame target nativeOut ∧
      ControlOutcomeRelated worldRelated (freshLoopLabels supply :: loops) default
        (sourceLoopBackedge sourceOut) nativeOut ∧
      TemporaryNamesBound nativeOut.frame iteration.supply.next ∧ TemporariesScoped nativeOut.frame := by
  have unchanged : middle = source := child.sourceState tested
  subst middle
  let tail := [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
    iteration.code ++ [.jump (freshLoopLabels supply).entry]
  let root := test.code ++ tail
  have freshBound : supply.next ≤ (NativeIR.fresh (NativeIR.fresh supply).2).2.next :=
    (NativeIR.fresh_strict supply).le.trans (NativeIR.fresh_strict (NativeIR.fresh supply).2).le
  obtain ⟨⟨flow, afterFrame, post⟩, firstRun, related, protection, afterBound, afterScoped⟩ :=
    child.forward root testCompiled frames states
      (fun id present => (bounded id present).trans freshBound) hscope tested
  rcases related with ⟨_, normal, unchanged, read⟩
  cases normal
  change post = target at unchanged
  subst post
  obtain ⟨inner, bodyRun, bodyRelated, bodyBound, bodyScoped⟩ := bodyForward
    (temporary_protection_preserves_source_frame frames protection) afterBound afterScoped bodyRan
  have actualRead : TargetAtomEval interface afterFrame target test.result (.bool true) := by
    simpa only [encodeValue] using read
  have rest : TargetRun interface targetHeap targetCalls result root tail afterFrame target
      (targetLoopBackedge (freshLoopLabels supply).entry inner) := by
    simpa only [root, tail, List.append_assoc] using
      (compiled_while_iteration_tail_exact loopBounds testCompiled bodyCompiled actualRead afterScoped
        (targetLoopBackedge (freshLoopLabels supply).entry inner)).mpr
        (by simp only [if_true]; exact ⟨inner, bodyRun, rfl⟩)
  refine ⟨targetLoopBackedge (freshLoopLabels supply).entry inner, ?_,
    control_loop_backedge_related bodyRelated, ?_, ?_⟩
  · simpa only [root, tail, List.append_assoc] using target_append_normal root test.code tail
      (expression_lowering_jump_free _ _ _ _ _ testCompiled) firstRun rest
  · cases h : inner.flow <;> simpa only [targetLoopBackedge, h] using bodyBound
  · cases h : inner.flow <;> simpa only [targetLoopBackedge, h] using bodyScoped

/-- A false condition transfers to the exit without evaluating the body. -/
theorem compiled_while_false_iteration_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {body : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    {test : NativeLowering.Expression} {iteration : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default condition)
    (testCompiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) condition
      (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test)
    (bodyCompiled : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
      (sourceFrameScope sourceFrame) body test.supply = some iteration)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {after : SourceState SourceWorld}
    (tested : SourceExprEval interface sourceHeap sourceCalls sourceFrame condition source
      ⟨.ok (.bool false), after⟩) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result
        (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
          iteration.code ++ [.jump (freshLoopLabels supply).entry])
        (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
          iteration.code ++ [.jump (freshLoopLabels supply).entry]) targetFrame target nativeOut ∧
      ControlOutcomeRelated worldRelated (freshLoopLabels supply :: loops) default
        ⟨.broke, sourceFrame, after⟩ nativeOut ∧
      TemporaryNamesBound nativeOut.frame iteration.supply.next ∧ TemporariesScoped nativeOut.frame := by
  have unchanged : after = source := child.sourceState tested
  subst after
  let tail := [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
    iteration.code ++ [.jump (freshLoopLabels supply).entry]
  let root := test.code ++ tail
  have freshBound : supply.next ≤ (NativeIR.fresh (NativeIR.fresh supply).2).2.next :=
    (NativeIR.fresh_strict supply).le.trans (NativeIR.fresh_strict (NativeIR.fresh supply).2).le
  obtain ⟨⟨flow, afterFrame, post⟩, firstRun, related, protection, afterBound, afterScoped⟩ :=
    child.forward root testCompiled frames states
      (fun id present => (bounded id present).trans freshBound) hscope tested
  rcases related with ⟨_, normal, unchanged, read⟩
  cases normal
  change post = target at unchanged
  subst post
  have actualRead : TargetAtomEval interface afterFrame target test.result (.bool false) := by
    simpa only [encodeValue] using read
  let final : TargetBlockOutcome TargetWorld := ⟨.jumped (freshLoopLabels supply).exit, afterFrame, target⟩
  have rest : TargetRun interface targetHeap targetCalls result root tail afterFrame target final := by
    simpa only [root, tail, List.append_assoc] using
      (compiled_while_iteration_tail_exact loopBounds testCompiled bodyCompiled actualRead afterScoped final).mpr
        (by simp only [Bool.false_eq_true, if_false]; rfl)
  have bodyBound := block_lowering_bounds
    (loop_labels_within_weaken (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
      (fresh_loop_labels_within supply loopBounds)) bodyCompiled
  refine ⟨final, ?_, ⟨states, temporary_protection_preserves_source_frame frames protection, .broke rfl⟩,
    fun id present => (afterBound id present).trans bodyBound.1, afterScoped⟩
  simpa only [root, tail, List.append_assoc] using target_append_normal root test.code tail
    (expression_lowering_jump_free _ _ _ _ _ testCompiled) firstRun rest

/-- A condition fault retains its poisoned state and skips the body and backedge. -/
theorem compiled_while_fault_iteration_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {body : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    {test : NativeLowering.Expression} {iteration : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default condition)
    (testCompiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) condition
      (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test)
    (bodyCompiled : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
      (sourceFrameScope sourceFrame) body test.supply = some iteration)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {after : SourceState SourceWorld} {fault : NativeWord64.Fault}
    (tested : SourceExprEval interface sourceHeap sourceCalls sourceFrame condition source
      ⟨.error fault, after⟩) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result
        (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
          iteration.code ++ [.jump (freshLoopLabels supply).entry])
        (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
          iteration.code ++ [.jump (freshLoopLabels supply).entry]) targetFrame target nativeOut ∧
      ControlOutcomeRelated worldRelated (freshLoopLabels supply :: loops) default
        ⟨.fault fault, sourceFrame, after⟩ nativeOut ∧
      TemporaryNamesBound nativeOut.frame iteration.supply.next ∧ TemporariesScoped nativeOut.frame := by
  have unchanged : after = sourcePoison source fault := child.sourceState tested
  subst after
  let tail := [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
    iteration.code ++ [.jump (freshLoopLabels supply).entry]
  let root := test.code ++ tail
  have freshBound : supply.next ≤ (NativeIR.fresh (NativeIR.fresh supply).2).2.next :=
    (NativeIR.fresh_strict supply).le.trans (NativeIR.fresh_strict (NativeIR.fresh supply).2).le
  obtain ⟨⟨flow, afterFrame, post⟩, firstRun, related, protection, afterBound, afterScoped⟩ :=
    child.forward root testCompiled frames states
      (fun id present => (bounded id present).trans freshBound) hscope tested
  rcases related with ⟨_, returned, poisoned⟩
  cases returned
  change post = targetPoison target fault at poisoned
  subst post
  have bodyBound := block_lowering_bounds
    (loop_labels_within_weaken (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
      (fresh_loop_labels_within supply loopBounds)) bodyCompiled
  refine ⟨⟨.returned default, afterFrame, targetPoison target fault⟩, ?_,
    ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
    fun id present => (afterBound id present).trans bodyBound.1, afterScoped⟩
  simpa only [root, tail, List.append_assoc] using target_append_returned root test.code tail
    (expression_lowering_jump_free _ _ _ _ _ testCompiled) firstRun

/-- Every actual compiled iteration reflects its selected authored condition,
body and complete abrupt outcome. A fault never acquires a body execution. -/
theorem compiled_while_iteration_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {body : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld}
    {test : NativeLowering.Expression} {iteration : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (child : ShortCircuitChildLaws worldRelated interface sourceHeap sourceCalls targetHeap targetCalls
      sourceFrame source result default condition)
    (testCompiled : NativeLowering.expression? interface (sourceFrameScope sourceFrame) condition
      (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test)
    (bodyCompiled : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
      (sourceFrameScope sourceFrame) body test.supply = some iteration)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    (typing : inferExpr interface (sourceFrameScope sourceFrame) condition = some .bool)
    (bodyBackward : ∀ {nativeFrame : TargetFrame} {nativeOut : TargetBlockOutcome TargetWorld},
      FrameRelated sourceFrame nativeFrame → TemporaryNamesBound nativeFrame test.supply.next →
      TemporariesScoped nativeFrame →
      TargetRun interface targetHeap targetCalls result iteration.code iteration.code nativeFrame target nativeOut →
      ∃ sourceOut, SourceBlockEval interface sourceHeap sourceCalls body sourceFrame source sourceOut ∧
        ControlOutcomeRelated worldRelated (freshLoopLabels supply :: loops) default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame iteration.supply.next ∧ TemporariesScoped nativeOut.frame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result
      (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
        iteration.code ++ [.jump (freshLoopLabels supply).entry])
      (test.code ++ [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
        iteration.code ++ [.jump (freshLoopLabels supply).entry]) targetFrame target nativeOut) :
    ∃ sourceOut,
      ((SourceExprEval interface sourceHeap sourceCalls sourceFrame condition source ⟨.ok (.bool false), source⟩ ∧
          sourceOut = ⟨.broke, sourceFrame, source⟩) ∨
        (∃ inner, SourceExprEval interface sourceHeap sourceCalls sourceFrame condition source
            ⟨.ok (.bool true), source⟩ ∧
          SourceBlockEval interface sourceHeap sourceCalls body sourceFrame source inner ∧
          sourceOut = sourceLoopBackedge inner) ∨
        (∃ fault, SourceExprEval interface sourceHeap sourceCalls sourceFrame condition source
            ⟨.error fault, sourcePoison source fault⟩ ∧
          sourceOut = ⟨.fault fault, sourceFrame, sourcePoison source fault⟩)) ∧
      ControlOutcomeRelated worldRelated (freshLoopLabels supply :: loops) default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame iteration.supply.next ∧ TemporariesScoped nativeOut.frame := by
  let tail := [.branch (.negated test.result) [.jump (freshLoopLabels supply).exit] []] ++
    iteration.code ++ [.jump (freshLoopLabels supply).entry]
  let root := test.code ++ tail
  have rootRun : TargetRun interface targetHeap targetCalls result root root targetFrame target nativeOut := by
    simpa only [root, tail, List.append_assoc] using ran
  have freshBound : supply.next ≤ (NativeIR.fresh (NativeIR.fresh supply).2).2.next :=
    (NativeIR.fresh_strict supply).le.trans (NativeIR.fresh_strict (NativeIR.fresh supply).2).le
  have testBound := expression_lowering_boundary _ _ _ _ _ testCompiled
  have bodyBound := block_lowering_bounds
    (loop_labels_within_weaken testBound.monotone (fresh_loop_labels_within supply loopBounds)) bodyCompiled
  rcases target_split_jump_free_prefix root test.code tail
      (expression_lowering_jump_free _ _ _ _ _ testCompiled) rootRun with
    ⟨afterFrame, post, firstRun, tailRun⟩ | ⟨returned, afterFrame, post, firstRun, same⟩
  · obtain ⟨sourceResult, evaluated, related, protection, afterBound, afterScoped⟩ :=
      child.backward root testCompiled frames states
        (fun id present => (bounded id present).trans freshBound) hscope firstRun
    obtain ⟨actual, sourceSame, unchanged, read⟩ := guarded_related_normal related rfl
    cases sourceSame
    change post = target at unchanged
    subst post
    have tag := child.sourceTag typing evaluated
    cases tag with
    | bool selected =>
      have actualRead : TargetAtomEval interface afterFrame target test.result (.bool selected) := by
        simpa only [encodeValue] using read
      have tailExact := compiled_while_iteration_tail_exact (heap := targetHeap) (calls := targetCalls)
        (result := result) loopBounds testCompiled bodyCompiled
        actualRead afterScoped nativeOut
      have observed := tailExact.mp (by simpa only [root, tail, List.append_assoc] using tailRun)
      cases selected with
      | false =>
        simp only [Bool.false_eq_true, if_false] at observed
        subst nativeOut
        exact ⟨⟨.broke, sourceFrame, source⟩, .inl ⟨evaluated, rfl⟩,
          ⟨states, temporary_protection_preserves_source_frame frames protection, .broke rfl⟩,
          fun id present => (afterBound id present).trans bodyBound.1, afterScoped⟩
      | true =>
        simp only [if_true] at observed
        obtain ⟨inner, bodyRun, same⟩ := observed
        obtain ⟨sourceInner, bodySource, bodyRelated, finalBound, finalScoped⟩ := bodyBackward
          (temporary_protection_preserves_source_frame frames protection) afterBound afterScoped bodyRun
        subst nativeOut
        refine ⟨sourceLoopBackedge sourceInner, .inr (.inl ⟨sourceInner, evaluated, bodySource, rfl⟩),
          control_loop_backedge_related bodyRelated, ?_, ?_⟩
        · cases h : inner.flow <;> simpa only [targetLoopBackedge, h] using finalBound
        · cases h : inner.flow <;> simpa only [targetLoopBackedge, h] using finalScoped
  · obtain ⟨sourceResult, evaluated, related, protection, afterBound, afterScoped⟩ :=
      child.backward root testCompiled frames states
        (fun id present => (bounded id present).trans freshBound) hscope firstRun
    obtain ⟨fault, sourceSame, valueSame, poisoned⟩ := guarded_related_returned related rfl
    cases sourceSame
    subst returned
    change post = targetPoison target fault at poisoned
    subst post
    subst nativeOut
    exact ⟨⟨.fault fault, sourceFrame, sourcePoison source fault⟩,
      .inr (.inr ⟨fault, evaluated, rfl⟩),
      ⟨poison_correspondence states fault, temporary_protection_preserves_source_frame frames protection, .fault fault⟩,
      fun id present => (afterBound id present).trans bodyBound.1, afterScoped⟩

theorem control_flow_continue_target {active : NativeIR.LoopLabels} {loops : List NativeIR.LoopLabels}
    {default : TargetValue} {source : SourceFlow} {target : TargetFlow}
    (related : ControlFlowRelated (active :: loops) default source target)
    (continued : source = .continued) : target = .jumped active.entry := by
  cases related with
  | continued same => rw [(List.cons.inj same).1]
  | _ => cases continued

theorem control_flow_break_target {active : NativeIR.LoopLabels} {loops : List NativeIR.LoopLabels}
    {default : TargetValue} {source : SourceFlow} {target : TargetFlow}
    (related : ControlFlowRelated (active :: loops) default source target)
    (broke : source = .broke) : target = .jumped active.exit := by
  cases related with
  | broke same => rw [(List.cons.inj same).1]
  | _ => cases broke

/-- Return and fault survive leaving the active loop. They remain distinct
through their source outcome and complete state, even when payloads coincide. -/
theorem control_flow_stopping_outer {active : NativeIR.LoopLabels} {loops : List NativeIR.LoopLabels}
    {default : TargetValue} {source : SourceFlow} {target : TargetFlow}
    (related : ControlFlowRelated (active :: loops) default source target)
    (stopped : (∃ value, source = .returned value) ∨ (∃ fault, source = .fault fault)) :
    (∃ value, target = .returned value) ∧ ControlFlowRelated loops default source target := by
  cases related with
  | returned value => exact ⟨⟨_, rfl⟩, .returned value⟩
  | fault fault => exact ⟨⟨_, rfl⟩, .fault fault⟩
  | _ => rcases stopped with ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible

/-- Finite while preservation follows every actual source repetition. The
condition implementation is constructed here; only the independently
implemented body is supplied. Its actual source run establishes the profile
required for the next test. Cleanup restores the original temporary bound. -/
theorem short_circuit_while_child_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {body : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {output : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (pure : SourceShortCircuitExpression condition) (supported : SourceLocalControlBlock body)
    (zero : TargetZero interface result default)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.while condition body) supply = some output)
    (bodyForward : ∀ {frame : SourceFrame} {state : SourceState SourceWorld}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld}
        {bodySupply : NativeIR.Supply} {iteration : NativeLowering.Block}
        {sourceOut : SourceBlockOutcome SourceWorld},
      sourceFrameScope frame = sourceFrameScope sourceFrame →
      NativeLowering.block? interface result (freshLoopLabels supply :: loops)
        (sourceFrameScope frame) body bodySupply = some iteration →
      LoopLabelsWithin bodySupply.next (freshLoopLabels supply :: loops) →
      SourceLocalsBelow frame → LocalTypesCoherent frame.bindings →
      SourceLocalsTagged frame state.memory → state.fault = none →
      FrameRelated frame nativeFrame → StateRelated worldRelated state native →
      TemporaryNamesBound nativeFrame bodySupply.next → TemporariesScoped nativeFrame →
      SourceBlockEval interface sourceHeap sourceCalls body frame state sourceOut →
      ∃ nativeOut, TargetRun interface targetHeap targetCalls result iteration.code iteration.code
          nativeFrame native nativeOut ∧
        ControlOutcomeRelated worldRelated (freshLoopLabels supply :: loops) default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame iteration.supply.next ∧ TemporariesScoped nativeOut.frame)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {sourceOut : SourceBlockOutcome SourceWorld}
    (ran : SourceStatementEval interface sourceHeap sourceCalls (.while condition body)
      sourceFrame source sourceOut) :
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result output.code output.code
        targetFrame target nativeOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨nextScope, test, iteration, _, testCompiled, bodyCompiled, same⟩ := while_lowering_exact compiled
  subst output
  let active := freshLoopLabels supply
  let code := test.code ++ [.branch (.negated test.result) [.jump active.exit] []] ++
    iteration.code ++ [.jump active.entry]
  let root := [Instruction.label active.entry, .scope code, .label active.exit]
  have different : active.entry ≠ active.exit := by
    intro same
    have impossible := congrArg NativeIR.Label.kind same
    cases impossible
  let P := fun (frame : SourceFrame) (state : SourceState SourceWorld) (out : SourceBlockOutcome SourceWorld) =>
    sourceFrameScope frame = sourceFrameScope sourceFrame →
    SourceLocalsBelow frame → LocalTypesCoherent frame.bindings →
    SourceLocalsTagged frame state.memory → state.fault = none →
    ∀ (nativeFrame : TargetFrame) (native : TargetState TargetWorld),
      FrameRelated frame nativeFrame → StateRelated worldRelated state native →
      TemporaryNamesBound nativeFrame supply.next → TemporariesScoped nativeFrame →
      ∃ nativeOut, TargetRun interface targetHeap targetCalls result root root nativeFrame native nativeOut ∧
        ControlOutcomeRelated worldRelated loops default out nativeOut ∧
        TemporaryNamesBound nativeOut.frame supply.next ∧ TemporariesScoped nativeOut.frame
  have proved : P sourceFrame source sourceOut := by
    refine source_while_run_induction condition body P ?_ ?_ ?_ ?_ ?_ ran
    · intro frame state after tested sameScope below coherent tagged clear nativeFrame native frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      obtain ⟨inner, actual, related, _, _⟩ := compiled_while_false_iteration_preservation loopBounds child
        testCurrent bodyCurrent frames states bounded hscope tested
      have closed := close_control_outcomes frames related
      rw [source_close_unchanged_block] at closed
      exact ⟨⟨.normal, (targetCloseBlock nativeFrame inner).frame, (targetCloseBlock nativeFrame inner).state⟩,
        target_scoped_loop_exit actual (control_flow_break_target related.flow rfl) different,
        ⟨closed.state, closed.frame, .normal⟩, close_block_temporary_bound bounded inner,
        target_close_block_scoped nativeFrame inner⟩
    · intro frame state after fault tested sameScope below coherent tagged clear nativeFrame native frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      obtain ⟨inner, actual, related, _, _⟩ := compiled_while_fault_iteration_preservation loopBounds child
        testCurrent bodyCurrent frames states bounded hscope tested
      obtain ⟨⟨value, returned⟩, outer⟩ := control_flow_stopping_outer related.flow (.inr ⟨fault, rfl⟩)
      have closed := close_control_outcomes frames related
      rw [source_close_unchanged_block] at closed
      exact ⟨targetCloseBlock nativeFrame inner, target_scoped_loop_return actual returned,
        ⟨closed.state, closed.frame, outer⟩, close_block_temporary_bound bounded inner,
        target_close_block_scoped nativeFrame inner⟩
    · intro frame state middle inner out tested bodyRan again ih sameScope below coherent tagged clear
        nativeFrame native frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have unchanged : middle = state := child.sourceState tested
      subst middle
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      obtain ⟨nativeInner, actual, related, _, _⟩ := compiled_while_true_iteration_preservation loopBounds child
        testCurrent bodyCurrent frames states bounded hscope
        (fun related bounded bodyScoped ran => bodyForward sameScope bodyCurrent
          (loop_labels_within_weaken (Nat.le_of_lt (child.bounds testCurrent).1)
            (fresh_loop_labels_within supply loopBounds)) below coherent tagged clear
          related states bounded bodyScoped ran) tested bodyRan
      have profile := compiled_local_block_source_profile bodyCurrent bodyRan supported below coherent tagged clear
      have cleaned := source_local_profile_close below coherent profile
      have clearAgain : (sourceCloseBlock frame inner).state.fault = none := by
        change inner.state.fault = none
        rcases again with normal | continued
        · simpa only [normal] using profile.fault
        · simpa only [continued] using profile.fault
      have nextFlow : (sourceLoopBackedge inner).flow = .continued := by
        rcases again with h | h <;> simp [sourceLoopBackedge, h]
      have entered := control_flow_continue_target related.flow nextFlow
      have closed := close_control_outcomes frames related
      obtain ⟨sameFrame, sameState⟩ := source_close_backedge_frame_state frame inner
      have nextFrames : FrameRelated (sourceCloseBlock frame inner).frame
          (targetCloseBlock nativeFrame nativeInner).frame := by simpa only [sameFrame] using closed.frame
      have nextStates : StateRelated worldRelated (sourceCloseBlock frame inner).state
          (targetCloseBlock nativeFrame nativeInner).state := by simpa only [sameState] using closed.state
      obtain ⟨last, following, finalRelated, finalBound, finalScoped⟩ := ih
        (by exact sameScope) cleaned.below cleaned.coherent cleaned.tagged clearAgain
        _ _ nextFrames nextStates (close_block_temporary_bound bounded nativeInner)
        (target_close_block_scoped nativeFrame nativeInner)
      exact ⟨last, target_scoped_loop_repeat actual entered following, finalRelated, finalBound, finalScoped⟩
    · intro frame state middle inner tested bodyRan broke sameScope below coherent tagged clear
        nativeFrame native frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have unchanged : middle = state := child.sourceState tested
      subst middle
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      obtain ⟨nativeInner, actual, related, _, _⟩ := compiled_while_true_iteration_preservation loopBounds child
        testCurrent bodyCurrent frames states bounded hscope
        (fun related bounded bodyScoped ran => bodyForward sameScope bodyCurrent
          (loop_labels_within_weaken (Nat.le_of_lt (child.bounds testCurrent).1)
            (fresh_loop_labels_within supply loopBounds)) below coherent tagged clear
          related states bounded bodyScoped ran) tested bodyRan
      have noBackedge : sourceLoopBackedge inner = inner := by simp only [sourceLoopBackedge, broke]
      rw [noBackedge] at related
      have exited := control_flow_break_target related.flow broke
      have closed := close_control_outcomes frames related
      exact ⟨⟨.normal, (targetCloseBlock nativeFrame nativeInner).frame,
          (targetCloseBlock nativeFrame nativeInner).state⟩,
        target_scoped_loop_exit actual exited different, ⟨closed.state, closed.frame, .normal⟩,
        close_block_temporary_bound bounded nativeInner, target_close_block_scoped nativeFrame nativeInner⟩
    · intro frame state middle inner tested bodyRan stopped sameScope below coherent tagged clear
        nativeFrame native frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have unchanged : middle = state := child.sourceState tested
      subst middle
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      obtain ⟨nativeInner, actual, related, _, _⟩ := compiled_while_true_iteration_preservation loopBounds child
        testCurrent bodyCurrent frames states bounded hscope
        (fun related bounded bodyScoped ran => bodyForward sameScope bodyCurrent
          (loop_labels_within_weaken (Nat.le_of_lt (child.bounds testCurrent).1)
            (fresh_loop_labels_within supply loopBounds)) below coherent tagged clear
          related states bounded bodyScoped ran) tested bodyRan
      have noBackedge : sourceLoopBackedge inner = inner := by
        rcases stopped with ⟨value, h⟩ | ⟨fault, h⟩ <;> simp [sourceLoopBackedge, h]
      rw [noBackedge] at related
      obtain ⟨⟨value, returned⟩, outer⟩ := control_flow_stopping_outer related.flow stopped
      have closed := close_control_outcomes frames related
      exact ⟨targetCloseBlock nativeFrame nativeInner, target_scoped_loop_return actual returned,
        ⟨closed.state, closed.frame, outer⟩, close_block_temporary_bound bounded nativeInner,
        target_close_block_scoped nativeFrame nativeInner⟩
  exact proved rfl below coherent tagged clear targetFrame target frames states bounded hscope

theorem control_flow_entry_source {active : NativeIR.LoopLabels} {loops : List NativeIR.LoopLabels}
    {default : TargetValue} {source : SourceFlow} {target : TargetFlow}
    (related : ControlFlowRelated (active :: loops) default source target)
    (entered : target = .jumped active.entry) (different : active.entry ≠ active.exit) : source = .continued := by
  cases related with
  | continued same => rfl
  | broke same =>
      rw [← (List.cons.inj same).1] at entered
      exact False.elim (different (TargetFlow.jumped.inj entered).symm)
  | _ => cases entered

theorem control_flow_exit_source {active : NativeIR.LoopLabels} {loops : List NativeIR.LoopLabels}
    {default : TargetValue} {source : SourceFlow} {target : TargetFlow}
    (related : ControlFlowRelated (active :: loops) default source target)
    (exited : target = .jumped active.exit) (different : active.entry ≠ active.exit) : source = .broke := by
  cases related with
  | broke same => rfl
  | continued same =>
      rw [← (List.cons.inj same).1] at exited
      exact False.elim (different (TargetFlow.jumped.inj exited))
  | _ => cases exited

theorem control_flow_returned_source {active : NativeIR.LoopLabels} {loops : List NativeIR.LoopLabels}
    {default value : TargetValue} {source : SourceFlow} {target : TargetFlow}
    (related : ControlFlowRelated (active :: loops) default source target)
    (returned : target = .returned value) :
    ((∃ value, source = .returned value) ∨ (∃ fault, source = .fault fault)) ∧
      ControlFlowRelated loops default source target := by
  cases related with
  | returned value => exact ⟨.inl ⟨value, rfl⟩, .returned value⟩
  | fault fault => exact ⟨.inr ⟨fault, rfl⟩, .fault fault⟩
  | _ => cases returned

theorem control_flow_jump_is_active {active : NativeIR.LoopLabels} {loops : List NativeIR.LoopLabels}
    {default : TargetValue} {source : SourceFlow} {target : TargetFlow} {label : Label}
    (related : ControlFlowRelated (active :: loops) default source target)
    (jumped : target = .jumped label) : label = active.entry ∨ label = active.exit := by
  cases related with
  | broke same =>
      rw [← (List.cons.inj same).1] at jumped
      exact .inr (TargetFlow.jumped.inj jumped).symm
  | continued same =>
      rw [← (List.cons.inj same).1] at jumped
      exact .inl (TargetFlow.jumped.inj jumped).symm
  | _ => cases jumped

/-- Complete reflection follows the actual target loop derivation and
recovers every selected source iteration with its complete cleanup. -/
theorem short_circuit_while_child_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue} {loops : List NativeIR.LoopLabels}
    {condition : Expr} {body : List Statement} {supply : NativeIR.Supply}
    {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
    {targetFrame : TargetFrame} {target : TargetState TargetWorld} {output : NativeLowering.Block}
    (loopBounds : LoopLabelsWithin supply.next loops)
    (pure : SourceShortCircuitExpression condition) (supported : SourceLocalControlBlock body)
    (zero : TargetZero interface result default)
    (compiled : NativeLowering.statement? interface result loops (sourceFrameScope sourceFrame)
      (.while condition body) supply = some output)
    (bodyBackward : ∀ {frame : SourceFrame} {state : SourceState SourceWorld}
        {nativeFrame : TargetFrame} {native : TargetState TargetWorld}
        {bodySupply : NativeIR.Supply} {iteration : NativeLowering.Block}
        {nativeOut : TargetBlockOutcome TargetWorld},
      sourceFrameScope frame = sourceFrameScope sourceFrame →
      NativeLowering.block? interface result (freshLoopLabels supply :: loops)
        (sourceFrameScope frame) body bodySupply = some iteration →
      LoopLabelsWithin bodySupply.next (freshLoopLabels supply :: loops) →
      SourceLocalsBelow frame → LocalTypesCoherent frame.bindings →
      SourceLocalsTagged frame state.memory → state.fault = none →
      FrameRelated frame nativeFrame → StateRelated worldRelated state native →
      TemporaryNamesBound nativeFrame bodySupply.next → TemporariesScoped nativeFrame →
      TargetRun interface targetHeap targetCalls result iteration.code iteration.code nativeFrame native nativeOut →
      ∃ sourceOut, SourceBlockEval interface sourceHeap sourceCalls body frame state sourceOut ∧
        ControlOutcomeRelated worldRelated (freshLoopLabels supply :: loops) default sourceOut nativeOut ∧
        TemporaryNamesBound nativeOut.frame iteration.supply.next ∧ TemporariesScoped nativeOut.frame)
    (below : SourceLocalsBelow sourceFrame) (coherent : LocalTypesCoherent sourceFrame.bindings)
    (tagged : SourceLocalsTagged sourceFrame source.memory) (clear : source.fault = none)
    (frames : FrameRelated sourceFrame targetFrame) (states : StateRelated worldRelated source target)
    (bounded : TemporaryNamesBound targetFrame supply.next) (hscope : TemporariesScoped targetFrame)
    {nativeOut : TargetBlockOutcome TargetWorld}
    (ran : TargetRun interface targetHeap targetCalls result output.code output.code targetFrame target nativeOut) :
    ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.while condition body)
        sourceFrame source sourceOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame supply.next ∧ TemporariesScoped nativeOut.frame := by
  obtain ⟨nextScope, test, iteration, checked, testCompiled, bodyCompiled, same⟩ := while_lowering_exact compiled
  obtain ⟨_, typing, _, _⟩ := while_checked_scope checked
  subst output
  let active := freshLoopLabels supply
  let code := test.code ++ [.branch (.negated test.result) [.jump active.exit] []] ++
    iteration.code ++ [.jump active.entry]
  let root := [Instruction.label active.entry, .scope code, .label active.exit]
  have different : active.entry ≠ active.exit := by
    intro same
    have impossible := congrArg NativeIR.Label.kind same
    cases impossible
  let P := fun (nativeFrame : TargetFrame) (native : TargetState TargetWorld)
      (out : TargetBlockOutcome TargetWorld) =>
    ∀ (frame : SourceFrame) (state : SourceState SourceWorld),
      sourceFrameScope frame = sourceFrameScope sourceFrame →
      SourceLocalsBelow frame → LocalTypesCoherent frame.bindings →
      SourceLocalsTagged frame state.memory → state.fault = none →
      FrameRelated frame nativeFrame → StateRelated worldRelated state native →
      TemporaryNamesBound nativeFrame supply.next → TemporariesScoped nativeFrame →
      ∃ sourceOut, SourceStatementEval interface sourceHeap sourceCalls (.while condition body) frame state sourceOut ∧
        ControlOutcomeRelated worldRelated loops default sourceOut out ∧
        TemporaryNamesBound out.frame supply.next ∧ TemporariesScoped out.frame
  have proved : P targetFrame target nativeOut := by
    refine target_scoped_loop_run_induction active.entry active.exit code P ?_ ?_ ?_ ?_ ?_ ran
    · intro nativeFrame native inner actual normal frame state sameScope below coherent tagged clear
        frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      have typingCurrent : inferExpr interface (sourceFrameScope frame) condition = some .bool := by
        simpa only [sameScope] using typing
      obtain ⟨sourceIteration, origin, related, _, _⟩ := compiled_while_iteration_reflection loopBounds child
        testCurrent bodyCurrent frames states bounded hscope typingCurrent
        (fun related bounded bodyScoped ran => bodyBackward sameScope bodyCurrent
          (loop_labels_within_weaken (Nat.le_of_lt (child.bounds testCurrent).1)
            (fresh_loop_labels_within supply loopBounds)) below coherent tagged clear
          related states bounded bodyScoped ran) actual
      have sourceNormal := (control_flow_normal_iff related.flow).mpr normal
      rcases origin with ⟨tested, rfl⟩ | ⟨sourceInner, tested, bodyRan, rfl⟩ | ⟨fault, tested, rfl⟩
      · cases sourceNormal
      · exact False.elim (source_loop_backedge_not_normal sourceInner sourceNormal)
      · cases sourceNormal
    · intro nativeFrame native inner value actual returned frame state sameScope below coherent tagged clear
        frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      have typingCurrent : inferExpr interface (sourceFrameScope frame) condition = some .bool := by
        simpa only [sameScope] using typing
      obtain ⟨sourceIteration, origin, related, _, _⟩ := compiled_while_iteration_reflection loopBounds child
        testCurrent bodyCurrent frames states bounded hscope typingCurrent
        (fun related bounded bodyScoped ran => bodyBackward sameScope bodyCurrent
          (loop_labels_within_weaken (Nat.le_of_lt (child.bounds testCurrent).1)
            (fresh_loop_labels_within supply loopBounds)) below coherent tagged clear
          related states bounded bodyScoped ran) actual
      have observed := control_flow_returned_source related.flow returned
      rcases origin with ⟨tested, rfl⟩ | ⟨sourceInner, tested, bodyRan, rfl⟩ | ⟨fault, tested, rfl⟩
      · rcases observed.1 with ⟨_, impossible⟩ | ⟨_, impossible⟩ <;> cases impossible
      · have stopped := (source_loop_backedge_stopping_iff sourceInner).mp observed.1
        have noBackedge : sourceLoopBackedge sourceInner = sourceInner := by
          rcases stopped with ⟨value, h⟩ | ⟨fault, h⟩ <;> simp [sourceLoopBackedge, h]
        rw [noBackedge] at related
        have outer := (control_flow_returned_source related.flow returned).2
        have closed := close_control_outcomes frames related
        exact ⟨sourceCloseBlock frame sourceInner, .whileStop tested bodyRan stopped,
          ⟨closed.state, closed.frame, outer⟩, close_block_temporary_bound bounded inner,
          target_close_block_scoped nativeFrame inner⟩
      · have closed := close_control_outcomes frames related
        rw [source_close_unchanged_block] at closed
        exact ⟨⟨.fault fault, frame, sourcePoison state fault⟩, .whileFault tested,
          ⟨closed.state, closed.frame, observed.2⟩, close_block_temporary_bound bounded inner,
          target_close_block_scoped nativeFrame inner⟩
    · intro nativeFrame native inner out actual entered ih frame state sameScope below coherent tagged clear
        frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      have typingCurrent : inferExpr interface (sourceFrameScope frame) condition = some .bool := by
        simpa only [sameScope] using typing
      obtain ⟨sourceIteration, origin, related, _, _⟩ := compiled_while_iteration_reflection loopBounds child
        testCurrent bodyCurrent frames states bounded hscope typingCurrent
        (fun related bounded bodyScoped ran => bodyBackward sameScope bodyCurrent
          (loop_labels_within_weaken (Nat.le_of_lt (child.bounds testCurrent).1)
            (fresh_loop_labels_within supply loopBounds)) below coherent tagged clear
          related states bounded bodyScoped ran) actual
      have sourceContinue := control_flow_entry_source related.flow entered different
      rcases origin with ⟨tested, rfl⟩ | ⟨sourceInner, tested, bodyRan, rfl⟩ | ⟨fault, tested, rfl⟩
      · cases sourceContinue
      · have again := (source_loop_backedge_continue_iff sourceInner).mp sourceContinue
        have profile := compiled_local_block_source_profile bodyCurrent bodyRan supported below coherent tagged clear
        have cleaned := source_local_profile_close below coherent profile
        have clearAgain : (sourceCloseBlock frame sourceInner).state.fault = none := by
          change sourceInner.state.fault = none
          rcases again with normal | continued
          · simpa only [normal] using profile.fault
          · simpa only [continued] using profile.fault
        have closed := close_control_outcomes frames related
        obtain ⟨sameFrame, sameState⟩ := source_close_backedge_frame_state frame sourceInner
        have nextFrames : FrameRelated (sourceCloseBlock frame sourceInner).frame
            (targetCloseBlock nativeFrame inner).frame := by simpa only [sameFrame] using closed.frame
        have nextStates : StateRelated worldRelated (sourceCloseBlock frame sourceInner).state
            (targetCloseBlock nativeFrame inner).state := by simpa only [sameState] using closed.state
        obtain ⟨last, following, finalRelated, finalBound, finalScoped⟩ := ih
          (sourceCloseBlock frame sourceInner).frame (sourceCloseBlock frame sourceInner).state
          (by exact sameScope) cleaned.below cleaned.coherent cleaned.tagged clearAgain nextFrames nextStates
          (close_block_temporary_bound bounded inner) (target_close_block_scoped nativeFrame inner)
        exact ⟨last, .whileRepeat tested bodyRan again following, finalRelated, finalBound, finalScoped⟩
      · cases sourceContinue
    · intro nativeFrame native inner actual exited unused frame state sameScope below coherent tagged clear
        frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      have typingCurrent : inferExpr interface (sourceFrameScope frame) condition = some .bool := by
        simpa only [sameScope] using typing
      obtain ⟨sourceIteration, origin, related, _, _⟩ := compiled_while_iteration_reflection loopBounds child
        testCurrent bodyCurrent frames states bounded hscope typingCurrent
        (fun related bounded bodyScoped ran => bodyBackward sameScope bodyCurrent
          (loop_labels_within_weaken (Nat.le_of_lt (child.bounds testCurrent).1)
            (fresh_loop_labels_within supply loopBounds)) below coherent tagged clear
          related states bounded bodyScoped ran) actual
      have sourceBreak := control_flow_exit_source related.flow exited different
      rcases origin with ⟨tested, rfl⟩ | ⟨sourceInner, tested, bodyRan, rfl⟩ | ⟨fault, tested, rfl⟩
      · have closed := close_control_outcomes frames related
        rw [source_close_unchanged_block] at closed
        exact ⟨⟨.normal, frame, state⟩, .whileDone tested,
          ⟨closed.state, closed.frame, .normal⟩, close_block_temporary_bound bounded inner,
          target_close_block_scoped nativeFrame inner⟩
      · have broke := (source_loop_backedge_break_iff sourceInner).mp sourceBreak
        have noBackedge : sourceLoopBackedge sourceInner = sourceInner := by simp only [sourceLoopBackedge, broke]
        rw [noBackedge] at related
        have closed := close_control_outcomes frames related
        exact ⟨{ sourceCloseBlock frame sourceInner with flow := .normal }, .whileBreak tested bodyRan broke,
          ⟨closed.state, closed.frame, .normal⟩, close_block_temporary_bound bounded inner,
          target_close_block_scoped nativeFrame inner⟩
      · cases sourceBreak
    · intro nativeFrame native inner label actual jumped notEntry notExit frame state sameScope below coherent tagged clear
        frames states bounded hscope
      have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls frame state clear tagged result zero pure
      have testCurrent : NativeLowering.expression? interface (sourceFrameScope frame) condition
          (NativeIR.fresh (NativeIR.fresh supply).2).2 = some test := by simpa only [sameScope] using testCompiled
      have bodyCurrent : NativeLowering.block? interface result (freshLoopLabels supply :: loops)
          (sourceFrameScope frame) body test.supply = some iteration := by simpa only [sameScope] using bodyCompiled
      have typingCurrent : inferExpr interface (sourceFrameScope frame) condition = some .bool := by
        simpa only [sameScope] using typing
      obtain ⟨sourceIteration, origin, related, _, _⟩ := compiled_while_iteration_reflection loopBounds child
        testCurrent bodyCurrent frames states bounded hscope typingCurrent
        (fun related bounded bodyScoped ran => bodyBackward sameScope bodyCurrent
          (loop_labels_within_weaken (Nat.le_of_lt (child.bounds testCurrent).1)
            (fresh_loop_labels_within supply loopBounds)) below coherent tagged clear
          related states bounded bodyScoped ran) actual
      rcases control_flow_jump_is_active related.flow jumped with same | same
      · exact False.elim (notEntry same.symm)
      · exact False.elim (notExit same.symm)
  exact proved sourceFrame source rfl below coherent tagged clear frames states bounded hscope

/-- Common comparison contract for an actual structured lowerer and
an independently defined source execution relation. Both directions retain
complete outcomes and the bound of the emitted temporary supply. -/
structure LocalControlCompilerLaws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (result : NativeType) (default : TargetValue)
    (lower : List NativeIR.LoopLabels → Scope → NativeIR.Supply → Option NativeLowering.Block)
    (sourceEval : SourceFrame → SourceState SourceWorld → SourceBlockOutcome SourceWorld → Prop) : Prop where
  forward : ∀ {loops : List NativeIR.LoopLabels} {supply : NativeIR.Supply} {output : NativeLowering.Block}
      {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
      {targetFrame : TargetFrame} {target : TargetState TargetWorld},
    LoopLabelsWithin supply.next loops →
    lower loops (sourceFrameScope sourceFrame) supply = some output →
    SourceLocalsBelow sourceFrame → LocalTypesCoherent sourceFrame.bindings →
    SourceLocalsTagged sourceFrame source.memory → source.fault = none →
    FrameRelated sourceFrame targetFrame → StateRelated worldRelated source target →
    TemporaryNamesBound targetFrame supply.next → TemporariesScoped targetFrame →
    ∀ {sourceOut : SourceBlockOutcome SourceWorld}, sourceEval sourceFrame source sourceOut →
    ∃ nativeOut, TargetRun interface targetHeap targetCalls result output.code output.code
        targetFrame target nativeOut ∧ ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame
  backward : ∀ {loops : List NativeIR.LoopLabels} {supply : NativeIR.Supply} {output : NativeLowering.Block}
      {sourceFrame : SourceFrame} {source : SourceState SourceWorld}
      {targetFrame : TargetFrame} {target : TargetState TargetWorld},
    LoopLabelsWithin supply.next loops →
    lower loops (sourceFrameScope sourceFrame) supply = some output →
    SourceLocalsBelow sourceFrame → LocalTypesCoherent sourceFrame.bindings →
    SourceLocalsTagged sourceFrame source.memory → source.fault = none →
    FrameRelated sourceFrame targetFrame → StateRelated worldRelated source target →
    TemporaryNamesBound targetFrame supply.next → TemporariesScoped targetFrame →
    ∀ {nativeOut : TargetBlockOutcome TargetWorld},
    TargetRun interface targetHeap targetCalls result output.code output.code targetFrame target nativeOut →
    ∃ sourceOut, sourceEval sourceFrame source sourceOut ∧
      ControlOutcomeRelated worldRelated loops default sourceOut nativeOut ∧
      TemporaryNamesBound nativeOut.frame output.supply.next ∧ TemporariesScoped nativeOut.frame

/-- The actual empty block performs no source or target work. Its complete
outcome preserves the existing state, frame and temporary boundary. -/
theorem local_control_empty_block_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (result : NativeType) (default : TargetValue) :
    LocalControlCompilerLaws worldRelated interface targetHeap targetCalls result default
      (fun loops scope supply => NativeLowering.block? interface result loops scope [] supply)
      (SourceBlockEval interface sourceHeap sourceCalls []) := by
  constructor
  · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
      below coherent tagged clear frames states bounded hscope out ran
    simp only [NativeLowering.block?] at compiled
    cases Option.some.inj compiled
    cases ran
    exact ⟨⟨.normal, targetFrame, target⟩, .nil _ _ _, ⟨states, frames, .normal⟩, bounded, hscope⟩
  · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
      below coherent tagged clear frames states bounded hscope out ran
    simp only [NativeLowering.block?] at compiled
    cases Option.some.inj compiled
    cases ran
    exact ⟨⟨.normal, sourceFrame, source⟩, .nil _ _, ⟨states, frames, .normal⟩, bounded, hscope⟩

/-- Sequence comparison consumes the independently established head and tail
laws. The actual head execution establishes the tail's local profile. -/
theorem local_control_block_cons_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (result : NativeType) (default : TargetValue)
    {first : Statement} {rest : List Statement}
    (headSupported : SourceLocalControlStatement first)
    (headLaw : LocalControlCompilerLaws worldRelated interface targetHeap targetCalls result default
      (fun loops scope supply => NativeLowering.statement? interface result loops scope first supply)
      (SourceStatementEval interface sourceHeap sourceCalls first))
    (tailLaw : LocalControlCompilerLaws worldRelated interface targetHeap targetCalls result default
      (fun loops scope supply => NativeLowering.block? interface result loops scope rest supply)
      (SourceBlockEval interface sourceHeap sourceCalls rest)) :
    LocalControlCompilerLaws worldRelated interface targetHeap targetCalls result default
      (fun loops scope supply => NativeLowering.block? interface result loops scope (first :: rest) supply)
      (SourceBlockEval interface sourceHeap sourceCalls (first :: rest)) := by
  constructor
  · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
      below coherent tagged clear frames states bounded hscope out ran
    obtain ⟨head, tail, headCompiled, tailCompiled, same⟩ := block_cons_lowering_exact compiled
    subst output
    have headBounds := statement_lowering_bounds loopBounds headCompiled
    refine compiled_local_block_cons_preservation loopBounds headCompiled tailCompiled
      headSupported below coherent tagged clear ?_ ?_ ran
    · exact headLaw.forward loopBounds headCompiled below coherent tagged clear frames states bounded hscope
    · intro middleFrame middle nativeFrame native sourceOut profile bodyFrames bodyStates bodyBound bodyScoped bodyRan
      have current : NativeLowering.block? interface result loops (sourceFrameScope middleFrame)
          rest head.supply = some tail := by rw [profile.scope rfl]; exact tailCompiled
      exact tailLaw.forward (loop_labels_within_weaken headBounds.1 loopBounds) current
        profile.below profile.coherent profile.tagged profile.fault
        bodyFrames bodyStates bodyBound bodyScoped bodyRan

  · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
      below coherent tagged clear frames states bounded hscope out ran
    obtain ⟨head, tail, headCompiled, tailCompiled, same⟩ := block_cons_lowering_exact compiled
    subst output
    have headBounds := statement_lowering_bounds loopBounds headCompiled
    refine compiled_local_block_cons_reflection loopBounds headCompiled tailCompiled
      headSupported below coherent tagged clear ?_ ?_ ran
    · exact headLaw.backward loopBounds headCompiled below coherent tagged clear frames states bounded hscope
    · intro middleFrame middle nativeFrame native nativeOut profile bodyFrames bodyStates bodyBound bodyScoped bodyRan
      have current : NativeLowering.block? interface result loops (sourceFrameScope middleFrame)
          rest head.supply = some tail := by rw [profile.scope rfl]; exact tailCompiled
      exact tailLaw.backward (loop_labels_within_weaken headBounds.1 loopBounds) current
        profile.below profile.coherent profile.tagged profile.fault
        bodyFrames bodyStates bodyBound bodyScoped bodyRan

/-- The supported structured local family is implemented by the actual
lowerer in both directions. Child comparisons are constructed recursively
from the same source syntax, rather than supplied by a caller. -/
theorem short_circuit_local_control_statement_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    {statement : Statement} (supported : SourceLocalControlStatement statement) :
    LocalControlCompilerLaws worldRelated interface targetHeap targetCalls result default
      (fun loops scope supply => NativeLowering.statement? interface result loops scope statement supply)
      (SourceStatementEval interface sourceHeap sourceCalls statement) := by
  let S := fun statement => LocalControlCompilerLaws worldRelated interface targetHeap targetCalls result default
    (fun loops scope supply => NativeLowering.statement? interface result loops scope statement supply)
    (SourceStatementEval interface sourceHeap sourceCalls statement)
  let B := fun body => LocalControlCompilerLaws worldRelated interface targetHeap targetCalls result default
    (fun loops scope supply => NativeLowering.block? interface result loops scope body supply)
    (SourceBlockEval interface sourceHeap sourceCalls body)
  change S statement
  induction supported using SourceLocalControlStatement.rec
    (motive_2 := fun body _ => B body) with
  | declare name type pure =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        exact short_circuit_declaration_preservation sourceHeap sourceCalls targetHeap targetCalls
          clear tagged zero pure output.code compiled frames states bounded hscope ran
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        exact short_circuit_declaration_reflection sourceHeap sourceCalls targetHeap targetCalls
          clear tagged zero pure output.code compiled frames states bounded hscope ran
  | set name pure =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        exact short_circuit_local_set_preservation sourceHeap sourceCalls targetHeap targetCalls
          clear tagged zero pure output.code compiled frames states bounded hscope ran
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        exact short_circuit_local_set_reflection sourceHeap sourceCalls targetHeap targetCalls
          clear tagged zero pure output.code compiled frames states bounded hscope ran
  | effect pure =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
          targetHeap targetCalls sourceFrame source clear tagged result zero pure
        exact effect_child_preservation child output.code compiled frames states bounded hscope ran
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
          targetHeap targetCalls sourceFrame source clear tagged result zero pure
        exact effect_child_reflection child output.code compiled frames states bounded hscope ran
  | returnValue pure =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
          targetHeap targetCalls sourceFrame source clear tagged result zero pure
        exact return_value_child_preservation child output.code compiled frames states bounded hscope ran
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
          targetHeap targetCalls sourceFrame source clear tagged result zero pure
        exact return_value_child_reflection child output.code compiled frames states bounded hscope ran
  | branch pure yesSupported noSupported yesIH noIH =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        refine short_circuit_branch_preservation sourceHeap sourceCalls targetHeap targetCalls
          loopBounds clear tagged zero pure compiled frames states bounded hscope ?_ ran
        intro selected bodySupply body nativeFrame native sourceOut bodyCompiled bodyLoops
          bodyFrames bodyStates bodyBound bodyScoped bodyRan
        cases selected
        · exact noIH.forward bodyLoops bodyCompiled below coherent tagged clear
            bodyFrames bodyStates bodyBound bodyScoped bodyRan
        · exact yesIH.forward bodyLoops bodyCompiled below coherent tagged clear
            bodyFrames bodyStates bodyBound bodyScoped bodyRan
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        refine short_circuit_branch_reflection sourceHeap sourceCalls targetHeap targetCalls
          loopBounds clear tagged zero pure compiled frames states bounded hscope ?_ ran
        intro selected bodySupply body nativeFrame native nativeOut bodyCompiled bodyLoops
          bodyFrames bodyStates bodyBound bodyScoped bodyRan
        cases selected
        · exact noIH.backward bodyLoops bodyCompiled below coherent tagged clear
            bodyFrames bodyStates bodyBound bodyScoped bodyRan
        · exact yesIH.backward bodyLoops bodyCompiled below coherent tagged clear
            bodyFrames bodyStates bodyBound bodyScoped bodyRan
  | switch pure armsSupported fallbackSupported armsIH fallbackIH =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
          targetHeap targetCalls sourceFrame source clear tagged result zero pure
        refine compiled_switch_child_preservation loopBounds child compiled frames states bounded hscope ?_ ran
        intro value bodySupply body nativeFrame native sourceOut bodyCompiled bodyLoops
          bodyFrames bodyStates bodyBound bodyScoped bodyRan
        have selectedIH := source_select_case_property B value armsIH fallbackIH
        exact selectedIH.forward bodyLoops bodyCompiled below coherent tagged clear
          bodyFrames bodyStates bodyBound bodyScoped bodyRan
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        have child := short_circuit_expression_laws worldRelated interface sourceHeap sourceCalls
          targetHeap targetCalls sourceFrame source clear tagged result zero pure
        refine compiled_switch_child_reflection loopBounds child compiled frames states bounded hscope ?_ ran
        intro value bodySupply body nativeFrame native nativeOut bodyCompiled bodyLoops
          bodyFrames bodyStates bodyBound bodyScoped bodyRan
        have selectedIH := source_select_case_property B value armsIH fallbackIH
        exact selectedIH.backward bodyLoops bodyCompiled below coherent tagged clear
          bodyFrames bodyStates bodyBound bodyScoped bodyRan
  | «while» pure bodySupported bodyIH =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        have bounds := statement_lowering_bounds loopBounds compiled
        have compared := short_circuit_while_child_preservation
          (sourceHeap := sourceHeap) (sourceCalls := sourceCalls)
          (targetHeap := targetHeap) (targetCalls := targetCalls)
          loopBounds pure bodySupported zero compiled (bodyForward := ?_)
          below coherent tagged clear frames states bounded hscope ran
        · obtain ⟨comparedOut, actual, related, finalBound, finalScoped⟩ := compared
          exact ⟨comparedOut, actual, related,
            fun identity present => (finalBound identity present).trans bounds.1, finalScoped⟩
        · intro frame state nativeFrame native bodySupply iteration sourceOut _sameScope
            bodyCompiled bodyLoops bodyBelow bodyCoherent bodyTagged bodyClear bodyFrames bodyStates
            bodyBound bodyScoped bodyRan
          exact bodyIH.forward bodyLoops bodyCompiled bodyBelow bodyCoherent bodyTagged bodyClear
            bodyFrames bodyStates bodyBound bodyScoped bodyRan
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        have bounds := statement_lowering_bounds loopBounds compiled
        have compared := short_circuit_while_child_reflection
          (sourceHeap := sourceHeap) (sourceCalls := sourceCalls)
          (targetHeap := targetHeap) (targetCalls := targetCalls)
          loopBounds pure bodySupported zero compiled (bodyBackward := ?_)
          below coherent tagged clear frames states bounded hscope ran
        · obtain ⟨comparedOut, actual, related, finalBound, finalScoped⟩ := compared
          exact ⟨comparedOut, actual, related,
            fun identity present => (finalBound identity present).trans bounds.1, finalScoped⟩
        · intro frame state nativeFrame native bodySupply iteration nativeOut _sameScope
            bodyCompiled bodyLoops bodyBelow bodyCoherent bodyTagged bodyClear bodyFrames bodyStates
            bodyBound bodyScoped bodyRan
          exact bodyIH.backward bodyLoops bodyCompiled bodyBelow bodyCoherent bodyTagged bodyClear
            bodyFrames bodyStates bodyBound bodyScoped bodyRan
  | «break» =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        obtain ⟨active, outer, sameLoops, same⟩ := break_lowering_exact compiled
        subst loops
        subst output
        cases ran
        exact ⟨⟨.jumped active.exit, targetFrame, target⟩,
          .escape (.jump active.exit targetFrame target) rfl,
          ⟨states, frames, .broke rfl⟩, bounded, hscope⟩
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        obtain ⟨active, outer, sameLoops, same⟩ := break_lowering_exact compiled
        subst loops
        subst output
        have canonical := (target_outward_jump_run_exact [Instruction.jump active.exit]
          active.exit rfl targetFrame target out).mp ran
        subst out
        exact ⟨⟨.broke, sourceFrame, source⟩, .break sourceFrame source,
          ⟨states, frames, .broke rfl⟩, bounded, hscope⟩
  | «continue» =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        obtain ⟨active, outer, sameLoops, same⟩ := continue_lowering_exact compiled
        subst loops
        subst output
        cases ran
        exact ⟨⟨.jumped active.entry, targetFrame, target⟩,
          .escape (.jump active.entry targetFrame target) rfl,
          ⟨states, frames, .continued rfl⟩, bounded, hscope⟩
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        obtain ⟨active, outer, sameLoops, same⟩ := continue_lowering_exact compiled
        subst loops
        subst output
        have canonical := (target_outward_jump_run_exact [Instruction.jump active.entry]
          active.entry rfl targetFrame target out).mp ran
        subst out
        exact ⟨⟨.continued, sourceFrame, source⟩, .continue sourceFrame source,
          ⟨states, frames, .continued rfl⟩, bounded, hscope⟩
  | returnUnit =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        obtain ⟨_, same⟩ := return_unit_lowering_exact compiled
        subst output
        cases ran
        exact ⟨⟨.returned .unit, targetFrame, target⟩, .return (.return .unit),
          ⟨states, frames, .returned .unit⟩, bounded, hscope⟩
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        obtain ⟨_, same⟩ := return_unit_lowering_exact compiled
        subst output
        have read : TargetAtomEval interface targetFrame target .unit .unit := .unit
        have canonical := (target_return_then_exact read [Instruction.return .unit] [] out).mp ran
        subst out
        exact ⟨⟨.returned .unit, sourceFrame, source⟩, .returnUnit sourceFrame source,
          ⟨states, frames, .returned .unit⟩, bounded, hscope⟩
  | block bodySupported bodyIH =>
      constructor
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        refine compiled_scope_child_preservation loopBounds compiled frames bounded ?_ ran
        intro body sourceOut bodyCompiled bodyRan
        obtain ⟨comparedOut, actual, related, _, _⟩ := bodyIH.forward loopBounds bodyCompiled
          below coherent tagged clear frames states bounded hscope bodyRan
        exact ⟨comparedOut, actual, related⟩
      · intro loops supply output sourceFrame source targetFrame target loopBounds compiled
          below coherent tagged clear frames states bounded hscope out ran
        refine compiled_scope_child_reflection loopBounds compiled frames bounded ?_ ran
        intro body nativeOut bodyCompiled bodyRan
        obtain ⟨comparedOut, actual, related, _, _⟩ := bodyIH.backward loopBounds bodyCompiled
          below coherent tagged clear frames states bounded hscope bodyRan
        exact ⟨comparedOut, actual, related⟩
  | nil =>
      exact local_control_empty_block_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls result default
  | cons headSupported tailSupported headIH tailIH =>
      exact local_control_block_cons_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls result default headSupported headIH tailIH

/-- Every supported local block obtains its comparisons from its actual
statement syntax. No separate implementation premise remains for its tail. -/
theorem short_circuit_local_control_block_laws {SourceWorld TargetWorld : Type}
    (worldRelated : SourceWorld → TargetWorld → Prop) (interface : Interface)
    (sourceHeap : SourceHeapSemantics SourceWorld) (sourceCalls : SourceCalls SourceWorld)
    (targetHeap : TargetHeapSemantics TargetWorld) (targetCalls : TargetCalls TargetWorld)
    (result : NativeType) {default : TargetValue} (zero : TargetZero interface result default)
    {body : List Statement} (supported : SourceLocalControlBlock body) :
    LocalControlCompilerLaws worldRelated interface targetHeap targetCalls result default
      (fun loops scope supply => NativeLowering.block? interface result loops scope body supply)
      (SourceBlockEval interface sourceHeap sourceCalls body) := by
  revert supported
  induction body with
  | nil =>
      intro _supported
      exact local_control_empty_block_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls result default
  | cons first rest tailIH =>
      intro supported
      cases supported with
      | cons headSupported tailSupported =>
          exact local_control_block_cons_laws worldRelated interface sourceHeap sourceCalls
            targetHeap targetCalls result default headSupported
            (short_circuit_local_control_statement_laws worldRelated interface sourceHeap sourceCalls
              targetHeap targetCalls result zero headSupported) (tailIH tailSupported)

/-- The actual context guards continue with the same full state on a clear
    entry. Their prefix contains no label and cannot capture a body jump. -/
theorem target_function_prologue_clear {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (code : List Instruction) (frame : TargetFrame) (state : TargetState World)
    (clear : state.fault = none) (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result
      ([Instruction.checkContextExists, Instruction.checkContext] ++ code)
      ([Instruction.checkContextExists, Instruction.checkContext] ++ code) frame state out ↔
      TargetRun interface heap calls result code code frame state out := by
  change TargetRun interface heap calls result _
    (.checkContextExists :: .checkContext :: code) frame state out ↔ _
  rw [target_normal_then_exact (target_context_exists_exact frame state),
    target_normal_then_exact (target_context_clear_exact frame state clear)]
  exact target_label_free_prefix_root_iff
    (by intro label member; simp at member)
    code code frame state out

/-- An existing fault returns before entering the body, while retaining the
    bound parameter frame for the caller's real scope teardown. -/
theorem target_function_prologue_fault {World : Type} {interface : Interface}
    {heap : TargetHeapSemantics World} {calls : TargetCalls World} {result : NativeType}
    (code : List Instruction) (frame : TargetFrame) (state : TargetState World)
    {fault : NativeWord64.Fault} (failed : state.fault = some fault)
    {default : TargetValue} (zero : TargetZero interface result default)
    (out : TargetBlockOutcome World) :
    TargetRun interface heap calls result
      ([Instruction.checkContextExists, Instruction.checkContext] ++ code)
      ([Instruction.checkContextExists, Instruction.checkContext] ++ code) frame state out ↔
      out = ⟨.returned default, frame, state⟩ := by
  change TargetRun interface heap calls result _
    (.checkContextExists :: .checkContext :: code) frame state out ↔ _
  rw [target_normal_then_exact (target_context_exists_exact frame state)]
  exact target_returning_then_exact
    (target_context_fault_exact frame state failed zero) _ code out

theorem function_suffix_labels_above (result : NativeType) (bound : Nat) :
    TopLabelsAbove bound
      (if result = .unit then [Instruction.return .unit] else []) := by
  split
  · exact top_labels_above_singleton bound _ (by intro label same; cases same)
  · exact top_labels_above_nil bound

/-- Header order and the operational parameter frame have the same lookups
    when the checker admits distinct parameter names. The real compiler keeps
    every emitted instruction and label allocation under this change of scope. -/
theorem function_lowering_at_parameter_frame {World : Type} {interface : Interface}
    {function : Function} {output : NativeIR.Function}
    {arguments : List SourceValue} {storage : Nat}
    {frame : SourceFrame} {before bound : SourceState World}
    (compiled : NativeLowering.function? interface function = some output)
    (parameters : sourceBindParameters function.header.parameters arguments ⟨storage, 0, []⟩ before =
      some (frame, bound)) :
    ∃ body : NativeLowering.Block,
      checkFunction interface function = true ∧
      NativeLowering.block? interface function.header.result [] (sourceFrameScope frame)
        function.body ⟨0⟩ = some body ∧
      output = ⟨function.header,
        [Instruction.checkContextExists, Instruction.checkContext] ++ body.code ++
          (if function.header.result = .unit then [Instruction.return .unit] else []),
        body.supply.next⟩ := by
  obtain ⟨headerBody, checked, headerCompiled, outputSame⟩ :=
    NativeLowering.function_lowering_exact compiled
  have agreement := source_parameter_lookup_agreement
    (check_function_entry_contract checked).1 parameters
  have related := NativeLowering.block_scope_agreement agreement interface function.header.result
    [] function.body ⟨0⟩
  rw [headerCompiled] at related
  cases actual : NativeLowering.block? interface function.header.result []
      (sourceFrameScope frame) function.body ⟨0⟩ with
  | none => rw [actual] at related; cases related
  | some body =>
      rw [actual] at related
      cases related with
      | some same =>
          refine ⟨body, checked, rfl, ?_⟩
          simpa only [same.1, same.2.1] using outputSame

/-- A source return condition determines execution of the emitted unit
    fallthrough, or bypasses it after an actual return or fault. -/
theorem function_suffix_return_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld}
    {result : NativeType} {default : TargetValue}
    (zero : TargetZero interface result default) (code : List Instruction)
    {sourceOut : SourceBlockOutcome SourceWorld} {nativeOut : TargetBlockOutcome TargetWorld}
    (related : ControlOutcomeRelated worldRelated [] default sourceOut nativeOut)
    {raw : SourceValue} (returned : sourceFunctionRawValue interface result sourceOut raw) :
    TargetContinues interface heap calls result
      (code ++ (if result = .unit then [Instruction.return .unit] else []))
      (if result = .unit then [Instruction.return .unit] else []) nativeOut
      ⟨.returned (encodeValue raw), nativeOut.frame, nativeOut.state⟩ := by
  rcases sourceOut with ⟨sourceFlow, sourceFrame, source⟩
  rcases nativeOut with ⟨nativeFlow, nativeFrame, native⟩
  cases related.flow with
  | normal =>
      obtain ⟨sameResult, sameRaw⟩ := returned
      subst result
      subst raw
      exact .normal ((target_return_then_exact TargetAtomEval.unit _ [] _).mpr rfl)
  | returned value =>
      have same : raw = value := returned
      subst raw
      exact .returned _ _ _
  | fault error =>
      have same := target_zero_unique zero (zero_preservation returned.2)
      rw [← same]
      exact .returned _ _ _
  | broke active => cases active
  | continued active => cases active

/-- The actual suffix cannot manufacture a non-unit fallthrough result.
    The retained source fault profile supplies the fault of an abrupt body. -/
theorem function_suffix_return_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {heap : TargetHeapSemantics TargetWorld} {calls : TargetCalls TargetWorld}
    {result : NativeType} {default : SourceValue}
    (zero : SourceZero interface result default) (code : List Instruction)
    {sourceOut : SourceBlockOutcome SourceWorld} {nativeOut final : TargetBlockOutcome TargetWorld}
    (related : ControlOutcomeRelated worldRelated [] (encodeValue default) sourceOut nativeOut)
    (faults : match sourceOut.flow with
      | .fault error => sourceOut.state.fault = some error
      | _ => sourceOut.state.fault = none)
    (following : TargetContinues interface heap calls result
      (code ++ (if result = .unit then [Instruction.return .unit] else []))
      (if result = .unit then [Instruction.return .unit] else []) nativeOut final)
    {raw : TargetValue} (returned : final.flow = .returned raw) :
    ∃ sourceRaw, sourceFunctionRawValue interface result sourceOut sourceRaw ∧
      raw = encodeValue sourceRaw ∧ final.frame = nativeOut.frame ∧ final.state = nativeOut.state := by
  rcases sourceOut with ⟨sourceFlow, sourceFrame, source⟩
  rcases nativeOut with ⟨nativeFlow, nativeFrame, native⟩
  cases related.flow with
  | normal =>
      cases following with
      | normal ran =>
          by_cases unitResult : result = .unit
          · rw [if_pos unitResult] at ran
            have exactRun := (target_return_then_exact TargetAtomEval.unit _ [] _).mp ran
            subst final
            cases TargetFlow.returned.inj returned
            exact ⟨.unit, ⟨unitResult, rfl⟩, rfl, rfl, rfl⟩
          · rw [if_neg unitResult] at ran
            cases ran
            cases returned
  | returned value =>
      cases following
      cases TargetFlow.returned.inj returned
      exact ⟨value, rfl, rfl, rfl, rfl⟩
  | fault error =>
      cases following
      cases TargetFlow.returned.inj returned
      exact ⟨default, ⟨faults, zero⟩, rfl, rfl, rfl⟩
  | broke active => cases active
  | continued active => cases active

/-- Whole admitted local functions preserve actual entry, body execution,
    return and lexical teardown. A pre-existing fault needs a supplied fresh
    invocation location because the target binds parameters before its guard. -/
theorem local_control_function_preservation {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {function : Function} {output : NativeIR.Function}
    (compiled : NativeLowering.function? interface function = some output)
    (supported : SourceLocalControlBlock function.body)
    {default : SourceValue} (zero : SourceZero interface function.header.result default)
    {arguments : List SourceValue} (values : SourceParameterTags function.header.parameters arguments)
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    (freshFault : source.fault ≠ none → ∃ storage, sourceFreshFrame source.memory storage)
    {sourceRaw : SourceRawResult SourceWorld}
    (ran : SourceFunctionBody interface sourceHeap sourceCalls function arguments source sourceRaw) :
    ∃ nativeRaw, TargetFunctionBody interface targetHeap targetCalls output
      (encodeValues arguments) target nativeRaw ∧ RawResultRelated worldRelated sourceRaw nativeRaw := by
  cases ran with
  | entryFault arity failed entryZero =>
      obtain ⟨storage, fresh⟩ := freshFault (by intro clear; rw [failed] at clear; cases clear)
      have existsBound := (source_parameter_arity_exact function.header.parameters arguments
        ⟨storage, 0, []⟩ source).mpr arity.symm
      cases actual : sourceBindParameters function.header.parameters arguments ⟨storage, 0, []⟩ source with
      | none => rw [actual] at existsBound; cases existsBound
      | some pair =>
          obtain ⟨body, _checked, _bodyCompiled, sameOutput⟩ :=
            function_lowering_at_parameter_frame compiled actual
          subst output
          obtain ⟨frame, bound, parameters, _frames, _boundStates⟩ :=
            function_parameters_preserved (empty_function_frames_related storage) states actual
          have targetFresh := (fresh_function_frame_correspondence states.memory storage).mp fresh
          have failedBound : bound.fault = some _ :=
            (target_parameters_preserve_fault parameters).trans (states.fault.trans failed)
          have bodyRun := (target_function_prologue_fault (heap := targetHeap) (calls := targetCalls)
            (body.code ++ (if function.header.result = .unit then [Instruction.return .unit] else []))
            frame bound failedBound (zero_preservation entryZero)
            ⟨.returned _, frame, bound⟩).mpr rfl
          have release := target_parameters_leave_scope targetFresh parameters
          refine ⟨⟨_, target⟩, ?_, ⟨rfl, states⟩⟩
          simpa only [release, List.append_assoc] using
            (TargetFunctionBody.run
              (function := ⟨function.header,
                [Instruction.checkContextExists, Instruction.checkContext] ++
                  (body.code ++ (if function.header.result = .unit then [Instruction.return .unit] else [])),
                body.supply.next⟩)
              (out := ⟨.returned _, frame, bound⟩) targetFresh parameters bodyRun rfl)
  | run clear fresh parameters bodySource returned =>
      rename_i storage sourceFrame bound sourceOut raw
      obtain ⟨body, _checked, bodyCompiled, sameOutput⟩ :=
        function_lowering_at_parameter_frame compiled parameters
      subst output
      obtain ⟨targetFrame, nativeBound, nativeParameters, frames, boundStates⟩ :=
        function_parameters_preserved (empty_function_frames_related storage) states parameters
      have targetFresh := (fresh_function_frame_correspondence states.memory storage).mp fresh
      have boundClear := (source_parameters_preserve_fault parameters).trans clear
      obtain ⟨coherent, below⟩ := source_bind_parameters_coherent function.header.parameters
        local_types_empty (source_empty_frame_below storage) parameters
      have tagged := (source_bind_parameters_tagged function.header.parameters
        (source_empty_frame_tagged source.memory storage) (source_empty_frame_below storage)
        values parameters).1
      have temporaries := target_parameters_empty_temporaries nativeParameters
      have bounded : TemporaryNamesBound targetFrame 0 := by
        intro identity present
        rw [temporaries.1] at present
        cases present
      have hscope : TemporariesScoped targetFrame := by intro identity _absent; rw [temporaries.2]
      have loops : LoopLabelsWithin 0 [] := by intro active member; cases member
      have laws := short_circuit_local_control_block_laws worldRelated interface sourceHeap sourceCalls
        targetHeap targetCalls function.header.result (zero_preservation zero) supported
      obtain ⟨nativeOut, actualBody, related, _finalBound, _finalScoped⟩ :=
        laws.forward loops bodyCompiled below coherent tagged boundClear frames boundStates bounded hscope bodySource
      have bodyBounds := block_lowering_bounds loops bodyCompiled
      have following := function_suffix_return_preservation (heap := targetHeap) (calls := targetCalls)
        (zero_preservation zero) body.code related returned
      have completeBody := target_extend_continuation bodyBounds.2.1 bodyBounds.2.1
        (function_suffix_labels_above function.header.result body.supply.next) actualBody following
      have completeRun := (target_function_prologue_clear _ targetFrame nativeBound
        (boundStates.fault.trans boundClear) _).mpr completeBody
      have released := (scope_exit_correspondence (empty_function_frames_related storage)
        related.frame related.state).2
      exact ⟨⟨encodeValue raw, (targetLeaveScope (targetEmptyFrame storage) nativeOut.frame nativeOut.state).2⟩,
        .run (out := ⟨.returned (encodeValue raw), nativeOut.frame, nativeOut.state⟩)
          targetFresh nativeParameters (by simpa only [List.append_assoc] using completeRun) rfl,
        ⟨rfl, released⟩⟩

/-- Every finite run of the actual admitted local function body reflects to
    an authored source run with its supplied result and complete post-state.
    Target entry supplies its own fresh invocation location. -/
theorem local_control_function_reflection {SourceWorld TargetWorld : Type}
    {worldRelated : SourceWorld → TargetWorld → Prop} {interface : Interface}
    {sourceHeap : SourceHeapSemantics SourceWorld} {sourceCalls : SourceCalls SourceWorld}
    {targetHeap : TargetHeapSemantics TargetWorld} {targetCalls : TargetCalls TargetWorld}
    {function : Function} {output : NativeIR.Function}
    (compiled : NativeLowering.function? interface function = some output)
    (supported : SourceLocalControlBlock function.body)
    {default : SourceValue} (zero : SourceZero interface function.header.result default)
    {arguments : List SourceValue} (values : SourceParameterTags function.header.parameters arguments)
    {source : SourceState SourceWorld} {target : TargetState TargetWorld}
    (states : StateRelated worldRelated source target)
    {nativeRaw : TargetRawResult TargetWorld}
    (ran : TargetFunctionBody interface targetHeap targetCalls output
      (encodeValues arguments) target nativeRaw) :
    ∃ sourceRaw, SourceFunctionBody interface sourceHeap sourceCalls function
      arguments source sourceRaw ∧ RawResultRelated worldRelated sourceRaw nativeRaw := by
  obtain ⟨headerBody, _checked, _headerCompiled, sameOutput⟩ :=
    NativeLowering.function_lowering_exact compiled
  subst output
  cases ran with
  | run fresh nativeParameters nativeBody returned =>
      rename_i storage nativeFrame nativeBound final raw
      obtain ⟨sourceFrame, bound, parameters, frames, boundStates⟩ :=
        function_parameters_reflected (empty_function_frames_related storage) states nativeParameters
      have sourceFresh := (fresh_function_frame_correspondence states.memory storage).mpr fresh
      cases fault : source.fault with
      | some error =>
          have failedBound : nativeBound.fault = some error :=
            (target_parameters_preserve_fault nativeParameters).trans (states.fault.trans fault)
          have canonical := (target_function_prologue_fault
            (headerBody.code ++ (if function.header.result = .unit then [Instruction.return .unit] else []))
            nativeFrame nativeBound failedBound (zero_preservation zero) final).mp
            (by simpa only [List.append_assoc] using nativeBody)
          subst final
          have rawSame := TargetFlow.returned.inj returned
          have release := target_parameters_leave_scope fresh nativeParameters
          have arity := (source_parameter_arity_exact function.header.parameters arguments
            ⟨storage, 0, []⟩ source).mp (by rw [parameters]; rfl)
          refine ⟨⟨default, source⟩, .entryFault arity.symm fault zero, ?_⟩
          exact ⟨rawSame.symm, by simpa only [release] using states⟩
      | none =>
          obtain ⟨body, _checked, bodyCompiled, sameFrameOutput⟩ :=
            function_lowering_at_parameter_frame compiled parameters
          have sameCode := congrArg NativeIR.Function.body sameFrameOutput
          change [Instruction.checkContextExists, Instruction.checkContext] ++ headerBody.code ++
              (if function.header.result = .unit then [Instruction.return .unit] else []) =
            [Instruction.checkContextExists, Instruction.checkContext] ++ body.code ++
              (if function.header.result = .unit then [Instruction.return .unit] else []) at sameCode
          rw [sameCode] at nativeBody
          have boundClear := (source_parameters_preserve_fault parameters).trans fault
          have completeBody := (target_function_prologue_clear _ nativeFrame nativeBound
            (boundStates.fault.trans boundClear) final).mp
            (by simpa only [List.append_assoc] using nativeBody)
          have loops : LoopLabelsWithin 0 [] := by intro active member; cases member
          have bodyBounds := block_lowering_bounds loops bodyCompiled
          obtain ⟨nativeOut, actualBody, following⟩ :=
            target_split_continuation bodyBounds.2.1 bodyBounds.2.1
              (function_suffix_labels_above function.header.result body.supply.next) completeBody
          obtain ⟨coherent, below⟩ := source_bind_parameters_coherent function.header.parameters
            local_types_empty (source_empty_frame_below storage) parameters
          have tagged := (source_bind_parameters_tagged function.header.parameters
            (source_empty_frame_tagged source.memory storage) (source_empty_frame_below storage)
            values parameters).1
          have temporaries := target_parameters_empty_temporaries nativeParameters
          have bounded : TemporaryNamesBound nativeFrame 0 := by
            intro identity present
            rw [temporaries.1] at present
            cases present
          have hscope : TemporariesScoped nativeFrame := by intro identity _absent; rw [temporaries.2]
          have laws := short_circuit_local_control_block_laws worldRelated interface sourceHeap sourceCalls
            targetHeap targetCalls function.header.result (zero_preservation zero) supported
          obtain ⟨sourceOut, sourceBody, related, _finalBound, _finalScoped⟩ :=
            laws.backward loops bodyCompiled below coherent tagged boundClear frames boundStates
              bounded hscope actualBody
          have profile := source_local_control_block_profiles sourceBody supported below coherent tagged
            boundClear (block_lowering_checked_scope bodyCompiled)
          obtain ⟨sourceValue, sourceReturned, sameValue, sameFrame, sameState⟩ :=
            function_suffix_return_reflection zero body.code related profile.fault following returned
          have release := (scope_exit_correspondence (empty_function_frames_related storage)
            related.frame related.state).2
          refine ⟨⟨sourceValue, (sourceLeaveScope ⟨storage, 0, []⟩ sourceOut.frame sourceOut.state).2⟩,
            .run fault sourceFresh parameters sourceBody sourceReturned, ⟨sameValue, ?_⟩⟩
          simpa only [sameFrame, sameState] using release

end Mettapedia.GSLT.LanguageDef.NativeOps
