import Mettapedia.GSLT.LanguageDef.NativeOpsControlContinuation

/-!
# Structured statement bounds from the actual compiler

The statement, block and ordered switch-arm laws cover every successful
lowering, independently of expression/heap/call execution support. They do
not establish operational adequacy by themselves.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeIR (Instruction Label)

mutual
  /-- All jumps are old loop exits/entries or identifiers actually allocated
      by this statement. Visible labels are strictly newer than its input. -/
  theorem statement_lowering_bounds {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope} {statement : Statement}
      {supply : NativeIR.Supply}
      {output : NativeLowering.Block} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.statement? interface result loops scope statement supply = some output) :
      supply.next ≤ output.supply.next ∧ CodeJumpsWithin output.supply.next output.code ∧
        TopLabelsAbove supply.next output.code := by
    cases statement with
    | declare name type initializer =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := declaration_lowering_exact compiled
        subst output
        refine ⟨(expression_lowering_boundary _ _ _ _ _ lowered).monotone, ?_, ?_⟩
        · exact (code_jumps_within_append _ _ _).mpr
            ⟨expression_jumps_within lowered _, by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial⟩
        · exact (top_labels_above_append _ _ _).mpr ⟨label_free_above (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _,
            top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | set location child =>
        obtain ⟨nextScope, place, value, _, located, lowered, same⟩ := set_lowering_exact compiled
        have locationBound := location_lowering_boundary _ _ _ _ _ located
        have valueBound := expression_lowering_boundary _ _ _ _ _ lowered
        subst output
        refine ⟨locationBound.monotone.trans valueBound.monotone, ?_, ?_⟩
        · exact (code_jumps_within_append _ _ _).mpr
            ⟨(code_jumps_within_append _ _ _).mpr
              ⟨location_jumps_within located _, expression_jumps_within lowered _⟩,
              by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial⟩
        · exact (top_labels_above_append _ _ _).mpr
            ⟨(top_labels_above_append _ _ _).mpr
              ⟨label_free_above locationBound.labelFree _, label_free_above valueBound.labelFree _⟩,
              top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | branch condition yes no =>
        obtain ⟨nextScope, test, whenTrue, whenFalse, _, testCompiled, yesCompiled, noCompiled, same⟩ :=
          branch_lowering_exact compiled
        have testBound := (expression_lowering_boundary _ _ _ _ _ testCompiled).monotone
        have yesBounds := block_lowering_bounds (loop_labels_within_weaken testBound bounded) yesCompiled
        have noBounds := block_lowering_bounds
          (loop_labels_within_weaken yesBounds.1 (loop_labels_within_weaken testBound bounded)) noCompiled
        subst output
        refine ⟨testBound.trans (yesBounds.1.trans noBounds.1), ?_, ?_⟩
        · apply (code_jumps_within_append _ _ _).mpr
          refine ⟨expression_jumps_within testCompiled _, ?_⟩
          simp only [CodeJumpsWithin, InstructionJumpsWithin]
          exact ⟨⟨code_jumps_within_weaken noBounds.1 yesBounds.2.1, noBounds.2.1⟩, True.intro⟩
        · exact (top_labels_above_append _ _ _).mpr ⟨label_free_above (expression_lowering_boundary _ _ _ _ _ testCompiled).labelFree _,
            top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
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
        refine ⟨?_, ?_, ?_⟩
        · exact (NativeIR.fresh_strict supply).le.trans
            ((NativeIR.fresh_strict (NativeIR.fresh supply).2).le.trans (testBound.trans bodyBounds.1))
        · simp only [CodeJumpsWithin, InstructionJumpsWithin]
          refine ⟨True.intro, ?_, True.intro, True.intro⟩
          apply (code_jumps_within_append _ _ _).mpr
          refine ⟨(code_jumps_within_append _ _ _).mpr ⟨?_, bodyBounds.2.1⟩, ?_⟩
          · apply (code_jumps_within_append _ _ _).mpr
            refine ⟨expression_jumps_within testCompiled _, ?_⟩
            simp only [CodeJumpsWithin, InstructionJumpsWithin]
            exact ⟨⟨⟨exitBound, True.intro⟩, True.intro⟩, True.intro⟩
          · simpa only [CodeJumpsWithin, InstructionJumpsWithin] using And.intro entryBound True.intro
        · intro label member
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
          rcases member with entry | impossible | exit
          · cases Instruction.label.inj entry
            exact (fresh_loop_labels_above_supply supply).1
          · cases impossible
          · cases Instruction.label.inj exit
            exact (fresh_loop_labels_above_supply supply).1.trans (fresh_loop_labels_above_supply supply).2
    | switch selector arms otherwise =>
        rw [NativeLowering.statement?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨selected, selectorCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨armOutput, armsCompiled, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨defaultOutput, otherwiseCompiled, compiled⟩
        have selectorBound := expression_lowering_boundary _ _ _ _ _ selectorCompiled
        have armBounds := cases_lowering_bounds (loop_labels_within_weaken selectorBound.monotone bounded) armsCompiled
        have defaultBounds := block_lowering_bounds
          (loop_labels_within_weaken armBounds.1 (loop_labels_within_weaken selectorBound.monotone bounded))
          otherwiseCompiled
        cases Option.some.inj compiled
        refine ⟨selectorBound.monotone.trans (armBounds.1.trans defaultBounds.1), ?_, ?_⟩
        · apply (code_jumps_within_append _ _ _).mpr
          refine ⟨expression_jumps_within selectorCompiled _, ?_⟩
          simp only [CodeJumpsWithin, InstructionJumpsWithin]
          exact ⟨⟨arm_jumps_within_weaken defaultBounds.1 armBounds.2, defaultBounds.2.1⟩, True.intro⟩
        · exact (top_labels_above_append _ _ _).mpr
            ⟨label_free_above selectorBound.labelFree _,
              top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | free child =>
        rw [NativeLowering.statement?] at compiled
        rcases Option.bind_eq_some_iff.mp compiled with ⟨nextScope, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨type, _, compiled⟩
        rcases Option.bind_eq_some_iff.mp compiled with ⟨value, lowered, compiled⟩
        have valueBound := expression_lowering_boundary _ _ _ _ _ lowered
        cases type with
        | ref element | array element =>
            cases Option.some.inj compiled
            refine ⟨valueBound.monotone, ?_, ?_⟩
            · exact (code_jumps_within_append _ _ _).mpr
                ⟨expression_jumps_within lowered _,
                  by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial⟩
            · exact (top_labels_above_append _ _ _).mpr
                ⟨label_free_above valueBound.labelFree _, by
                  intro label member
                  simp only [List.mem_cons, List.mem_nil_iff, reduceCtorEq, false_or] at member⟩
        | _ => cases compiled
    | «break» =>
        obtain ⟨active, outer, same, outputSame⟩ := break_lowering_exact compiled
        subst loops
        subst output
        refine ⟨Nat.le_refl _, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, InstructionJumpsWithin] using
          And.intro (bounded active (List.mem_cons_self)).2 True.intro
    | «continue» =>
        obtain ⟨active, outer, same, outputSame⟩ := continue_lowering_exact compiled
        subst loops
        subst output
        refine ⟨Nat.le_refl _, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, InstructionJumpsWithin] using
          And.intro (bounded active (List.mem_cons_self)).1 True.intro
    | effect child =>
        obtain ⟨nextScope, value, _, lowered, same⟩ := effect_lowering_exact compiled
        subst output
        exact ⟨(expression_lowering_boundary _ _ _ _ _ lowered).monotone, expression_jumps_within lowered _,
          label_free_above (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _⟩
    | «return» value =>
        cases value with
        | none =>
            obtain ⟨_, same⟩ := return_unit_lowering_exact compiled
            subst output
            exact ⟨Nat.le_refl _, by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial,
              top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        | some child =>
            obtain ⟨nextScope, value, _, lowered, same⟩ := return_value_lowering_exact compiled
            subst output
            refine ⟨(expression_lowering_boundary _ _ _ _ _ lowered).monotone, ?_, ?_⟩
            · exact (code_jumps_within_append _ _ _).mpr
                ⟨expression_jumps_within lowered _, by simp only [CodeJumpsWithin, InstructionJumpsWithin]; trivial⟩
            · exact (top_labels_above_append _ _ _).mpr ⟨label_free_above (expression_lowering_boundary _ _ _ _ _ lowered).labelFree _,
                top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
    | block child =>
        obtain ⟨nextScope, body, _, lowered, same⟩ := block_statement_lowering_exact compiled
        have bodyBounds := block_lowering_bounds bounded lowered
        subst output
        refine ⟨bodyBounds.1, ?_, top_labels_above_singleton _ _ (fun _ impossible => by cases impossible)⟩
        simpa only [CodeJumpsWithin, InstructionJumpsWithin] using And.intro bodyBounds.2.1 True.intro
  termination_by sizeOf statement
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem block_lowering_bounds {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope} {body : List Statement}
      {supply : NativeIR.Supply}
      {output : NativeLowering.Block} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.block? interface result loops scope body supply = some output) :
      supply.next ≤ output.supply.next ∧ CodeJumpsWithin output.supply.next output.code ∧
        TopLabelsAbove supply.next output.code := by
    cases body with
    | nil =>
        rw [NativeLowering.block?] at compiled
        cases Option.some.inj compiled
        exact ⟨Nat.le_refl _, by simp only [CodeJumpsWithin], top_labels_above_nil _⟩
    | cons head tail =>
        obtain ⟨first, rest, firstCompiled, restCompiled, same⟩ := block_cons_lowering_exact compiled
        have firstBounds := statement_lowering_bounds bounded firstCompiled
        have restBounds := block_lowering_bounds
          (loop_labels_within_weaken firstBounds.1 bounded) restCompiled
        subst output
        exact ⟨firstBounds.1.trans restBounds.1,
          (code_jumps_within_append _ _ _).mpr
            ⟨code_jumps_within_weaken restBounds.1 firstBounds.2.1, restBounds.2.1⟩,
          (top_labels_above_append _ _ _).mpr
            ⟨firstBounds.2.2, top_labels_above_weaken firstBounds.1 restBounds.2.2⟩⟩
  termination_by sizeOf body
  decreasing_by all_goals subst_vars; all_goals simp_wf; all_goals omega

  theorem cases_lowering_bounds {interface : Interface} {result : NativeType}
      {loops : List NativeIR.LoopLabels} {scope : Scope}
      {arms : List (NativeWord64.Word × List Statement)} {supply : NativeIR.Supply}
      {output : NativeLowering.Cases} (bounded : LoopLabelsWithin supply.next loops)
      (compiled : NativeLowering.cases? interface result loops scope arms supply = some output) :
      supply.next ≤ output.supply.next ∧ ArmJumpsWithin output.supply.next output.cases := by
    cases arms with
    | nil =>
        rw [NativeLowering.cases?] at compiled
        cases Option.some.inj compiled
        exact ⟨Nat.le_refl _, by simp only [ArmJumpsWithin]⟩
    | cons arm rest =>
        cases arm with
        | mk selector body =>
            rw [NativeLowering.cases?] at compiled
            rcases Option.bind_eq_some_iff.mp compiled with ⟨bodyOutput, bodyCompiled, compiled⟩
            rcases Option.bind_eq_some_iff.mp compiled with ⟨restOutput, restCompiled, compiled⟩
            have bodyBounds := block_lowering_bounds bounded bodyCompiled
            have restBounds := cases_lowering_bounds (loop_labels_within_weaken bodyBounds.1 bounded) restCompiled
            cases Option.some.inj compiled
            exact ⟨bodyBounds.1.trans restBounds.1,
              (arm_jumps_within_cons _ _ _).mpr
                ⟨code_jumps_within_weaken restBounds.1 bodyBounds.2.1, restBounds.2⟩⟩
  termination_by sizeOf arms
  decreasing_by
    all_goals subst_vars
    all_goals simp_wf
    all_goals omega

end


end Mettapedia.GSLT.LanguageDef.NativeOps
