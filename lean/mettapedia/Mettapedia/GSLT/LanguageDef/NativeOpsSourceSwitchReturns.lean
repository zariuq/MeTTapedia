import Mettapedia.GSLT.LanguageDef.NativeOpsSourceComposition
import Mettapedia.GSLT.LanguageDef.NativeOpsSourceControl

/-!
# Exact source execution of constant-return dispatch

These inversion and construction laws execute the existing expression and
statement relations. A selected arm returns its word without changing any
memory, fault, local binding or external effect. Selection remains the source
machine's ordered case lookup; no second dispatch evaluator is introduced.
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

end Mettapedia.GSLT.LanguageDef.NativeOps
