import Mettapedia.GSLT.LanguageDef.NativeOpsSourceComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceControl

/-!
# Exact source dispatch and constant-return arms

These inversion and construction laws execute the existing expression and
statement relations. General dispatch distinguishes a selected block from a
selector fault. Constant-return arms retain memory, fault, local bindings and
external effects. Selection remains the source machine's ordered case lookup;
no second dispatch evaluator is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Word)

theorem source_leave_unchanged_scope {World : Type}
    (frame : SourceFrame) (state : SourceState World) :
    sourceLeaveScope frame frame state = (frame, state) := by
  have cells : (sourceDropLocals state.memory frame.storage frame.nextLocal
      frame.nextLocal).cells = state.memory.cells := by
    funext storage position
    simp only [sourceDropLocals]
    split
    · rename_i inside
      exact False.elim ((Nat.not_lt_of_ge inside.2.1) inside.2.2)
    · rfl
  have memory : sourceDropLocals state.memory frame.storage frame.nextLocal
      frame.nextLocal = state.memory := by
    exact congrArg (fun cells => SourceMemory.mk cells state.memory.owned) cells
  simp only [sourceLeaveScope, memory]

theorem source_close_unchanged_block {World : Type}
    (frame : SourceFrame) (state : SourceState World) (flow : SourceFlow) :
    sourceCloseBlock frame ⟨flow, frame, state⟩ = ⟨flow, frame, state⟩ := by
  simp only [sourceCloseBlock, source_leave_unchanged_scope]

theorem source_word_expression_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (value : Word) (state : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.word value) state out ↔
      out = ⟨.ok (.word value), state⟩ :=
  source_operand_free_expression_exact (.word value) rfl state out

theorem source_known_variable_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {name : String} {state : SourceState World} {value : SourceValue}
    (read : sourceLocalValue frame state name = some value) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.variable name) state out ↔
      out = ⟨.ok value, state⟩ := by
  rw [source_operand_free_expression_exact (.variable name) rfl]
  change (∃ actual, sourceLocalValue frame state name = some actual ∧
    out = ⟨.ok actual, state⟩) ↔ _
  simp only [read, Option.some.injEq]
  constructor
  · rintro ⟨actual, same, outcome⟩
    subst actual
    exact outcome
  · intro outcome
    exact ⟨value, rfl, outcome⟩

theorem source_return_word_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (value : Word) (state : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.return (some (.word value))) frame state out ↔
      out = ⟨.returned (.word value), frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | returnValue evaluated =>
        cases (source_word_expression_exact value state _).mp evaluated
        rfl
    | returnFault evaluated =>
        cases (source_word_expression_exact value state _).mp evaluated
  · intro same
    subst out
    exact .returnValue ((source_word_expression_exact value state _).mpr rfl)

theorem source_return_word_block_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (value : Word) (state : SourceState World) (out : SourceBlockOutcome World)
    (rest : List Statement) :
    SourceBlockEval interface heap calls (.return (some (.word value)) :: rest) frame state out ↔
      out = ⟨.returned (.word value), frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | cons firstRun _ => cases (source_return_word_exact value state _).mp firstRun
    | stop firstRun _ => exact (source_return_word_exact value state _).mp firstRun
  · intro same
    subst out
    exact .stop ((source_return_word_exact value state _).mpr rfl) (by intro bad; cases bad)

theorem source_return_switch_statement_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {name : String} {state : SourceState World} {selector result : Word}
    {arms : List (Word × List Statement)} {otherwise : List Statement}
    (read : sourceLocalValue frame state name = some (.word selector))
    (selected : sourceSelectCase selector arms otherwise = [.return (some (.word result))])
    (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.switch (.variable name) arms otherwise)
      frame state out ↔ out = ⟨.returned (.word result), frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | switch evaluated arm =>
        cases (source_known_variable_exact read _).mp evaluated
        rw [selected] at arm
        cases (source_return_word_block_exact result state _ []).mp arm
        exact source_close_unchanged_block frame state _
    | switchFault evaluated =>
        cases (source_known_variable_exact read _).mp evaluated
  · intro same
    subst out
    have arm : SourceBlockEval interface heap calls (sourceSelectCase selector arms otherwise)
        frame state ⟨.returned (.word result), frame, state⟩ := by
      rw [selected]
      exact (source_return_word_block_exact result state _ []).mpr rfl
    have ran := SourceStatementEval.switch
      ((source_known_variable_exact read _).mpr rfl) arm
    simpa only [source_close_unchanged_block] using ran

theorem source_return_switch_block_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    {name : String} {state : SourceState World} {selector result : Word}
    {arms : List (Word × List Statement)} {otherwise : List Statement}
    (read : sourceLocalValue frame state name = some (.word selector))
    (selected : sourceSelectCase selector arms otherwise = [.return (some (.word result))])
    (out : SourceBlockOutcome World) (rest : List Statement) :
    SourceBlockEval interface heap calls (.switch (.variable name) arms otherwise :: rest)
      frame state out ↔ out = ⟨.returned (.word result), frame, state⟩ := by
  constructor
  · intro ran
    cases ran with
    | cons firstRun _ =>
        cases (source_return_switch_statement_exact read selected _).mp firstRun
    | stop firstRun _ =>
        exact (source_return_switch_statement_exact read selected _).mp firstRun
  · intro same
    subst out
    exact .stop ((source_return_switch_statement_exact read selected _).mpr rfl)
      (by intro bad; cases bad)

theorem source_switch_statement_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    (selector : Expr) (arms : List (Word × List Statement)) (otherwise : List Statement)
    (frame : SourceFrame) (before : SourceState World) (out : SourceBlockOutcome World) :
    SourceStatementEval interface heap calls (.switch selector arms otherwise) frame before out ↔
      (∃ value middle inner,
        SourceExprEval interface heap calls frame selector before ⟨.ok (.word value), middle⟩ ∧
        SourceBlockEval interface heap calls (sourceSelectCase value arms otherwise) frame middle inner ∧
        out = sourceCloseBlock frame inner) ∨
      (∃ fault after,
        SourceExprEval interface heap calls frame selector before ⟨.error fault, after⟩ ∧
        out = ⟨.fault fault, frame, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | switch read body => exact Or.inl ⟨_, _, _, read, body, rfl⟩
    | switchFault read => exact Or.inr ⟨_, _, read, rfl⟩
  · rintro (⟨value, middle, inner, read, body, same⟩ | ⟨fault, after, read, same⟩)
    · subst out; exact .switch read body
    · subst out; exact .switchFault read

theorem source_select_return_map {Item : Type} (items : List Item)
    (key result : Item → Word) (selector default : Word) :
    sourceSelectCase selector
      (items.map fun item => (key item, [.return (some (.word (result item)))]))
      [.return (some (.word default))] =
      [.return (some (.word (Option.getD
        ((items.find? fun item => key item == selector).map result) default)))] := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      by_cases selected : key item == selector
      · simp [sourceSelectCase, selected]
      · simpa [sourceSelectCase, selected] using ih

theorem source_returning_cases_all {arms : List (Word × List Statement)}
    (checked : returnsCases arms = true) : ∀ arm ∈ arms, returnsBlock arm.2 = true := by
  induction arms with
  | nil => intro arm member; cases member
  | cons arm rest ih =>
      rcases arm with ⟨key, body⟩
      simp only [returnsCases, Bool.and_eq_true] at checked
      intro selected member
      rcases List.mem_cons.mp member with same | old
      · cases same; exact checked.1
      · exact ih checked.2 selected old

/-- The static return test is a sufficient condition for every finite
    authored execution to end abruptly. It does not assert termination. -/
theorem source_returning_statement_not_normal {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {statement : Statement} {frame : SourceFrame} {state : SourceState World}
    {out : SourceBlockOutcome World} (checked : returnsStatement statement = true)
    (ran : SourceStatementEval interface heap calls statement frame state out) : out.flow ≠ .normal := by
  revert checked
  induction ran using SourceStatementEval.rec
    (motive_2 := fun body _ _ out _ => returnsBlock body = true → out.flow ≠ .normal)
  all_goals first
    | (intro impossible; simp only [returnsStatement, Bool.false_eq_true] at impossible; done)
    | skip
  case returnUnit => intro _ bad; cases bad
  case returnValue => intro _ bad; cases bad
  case returnFault => intro _ bad; cases bad
  case block =>
    rename_i bodyRan bodyIH
    intro checked
    exact bodyIH (by simpa only [returnsStatement] using checked)
  case branchFault => intro _ bad; cases bad
  case switchFault => intro _ bad; cases bad
  case nil =>
    rename_i impossible
    simp only [returnsBlock, Bool.false_eq_true] at impossible
  case branch =>
    rename_i bodyRan bodyIH
    intro checked
    simp only [returnsStatement, Bool.and_eq_true] at checked
    apply bodyIH
    split
    · exact checked.1
    · exact checked.2
  case switch =>
    rename_i bodyRan bodyIH
    intro checked
    simp only [returnsStatement, Bool.and_eq_true] at checked
    apply bodyIH
    exact source_select_case_property (fun body => returnsBlock body = true) _
      (source_returning_cases_all checked.2) checked.1
  case cons =>
    rename_i headIH tailIH checked
    simp only [returnsBlock, Bool.or_eq_true] at checked
    rcases checked with headChecked | tailChecked
    · exact False.elim ((headIH headChecked) rfl)
    · exact tailIH tailChecked
  case stop =>
    rename_i abrupt _headIH _checked
    exact abrupt

theorem source_returning_block_not_normal {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World}
    {body : List Statement} {frame : SourceFrame} {state : SourceState World}
    {out : SourceBlockOutcome World} (checked : returnsBlock body = true)
    (ran : SourceBlockEval interface heap calls body frame state out) : out.flow ≠ .normal := by
  induction body generalizing frame state with
  | nil => simp only [returnsBlock, Bool.false_eq_true] at checked
  | cons first rest ih =>
      simp only [returnsBlock, Bool.or_eq_true] at checked
      cases ran with
      | cons head tail =>
          rcases checked with headChecked | tailChecked
          · exact False.elim ((source_returning_statement_not_normal headChecked head) rfl)
          · exact ih tailChecked tail
      | stop _ abrupt => exact abrupt

end Mettapedia.GSLT.LanguageDef.NativeOps
