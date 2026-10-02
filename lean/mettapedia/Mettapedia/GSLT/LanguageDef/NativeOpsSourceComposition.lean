import Mettapedia.GSLT.LanguageDef.NativeOpsSourceEval

/-!
# Exact finite composition of source operands

The inversions retain the actual left-to-right evaluations, intermediate
states and first fault. Short-circuit branches contain only the calls they
execute. These laws expose the existing source relations for operational
lowering proofs; they do not add a guest evaluator or an execution bound.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Fault)

theorem source_arguments_nil_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (state : SourceState World) (out : SourceArgumentsOutcome World) :
    SourceArgumentsEval interface heap calls frame [] state out ↔ out = ⟨.ok [], state⟩ := by
  constructor
  · intro ran; cases ran; rfl
  · intro same; subst out; exact .nil state

theorem source_arguments_cons_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (first : Expr) (rest : List Expr) (before : SourceState World)
    (out : SourceArgumentsOutcome World) :
    SourceArgumentsEval interface heap calls frame (first :: rest) before out ↔
      (∃ value middle tail,
        SourceExprEval interface heap calls frame first before ⟨.ok value, middle⟩ ∧
        SourceArgumentsEval interface heap calls frame rest middle tail ∧
        out = ⟨tail.result.map (value :: ·), tail.state⟩) ∨
      (∃ fault after,
        SourceExprEval interface heap calls frame first before ⟨.error fault, after⟩ ∧
        out = ⟨.error fault, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | cons firstRun restRun => exact .inl ⟨_, _, _, firstRun, restRun, rfl⟩
    | consFault firstRun => exact .inr ⟨_, _, firstRun, rfl⟩
  · intro witnessed
    rcases witnessed with ⟨value, middle, tail, firstRun, restRun, same⟩ |
      ⟨fault, after, firstRun, same⟩
    · subst out; exact .cons firstRun restRun
    · subst out; exact .consFault firstRun

theorem source_arguments_cons_success_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (first : Expr) (rest : List Expr) (before after : SourceState World)
    (value : SourceValue) (values : List SourceValue) :
    SourceArgumentsEval interface heap calls frame (first :: rest) before
      ⟨.ok (value :: values), after⟩ ↔
    ∃ middle,
      SourceExprEval interface heap calls frame first before ⟨.ok value, middle⟩ ∧
      SourceArgumentsEval interface heap calls frame rest middle ⟨.ok values, after⟩ := by
  rw [source_arguments_cons_exact]
  constructor
  · intro witnessed
    rcases witnessed with ⟨head, middle, tail, firstRun, restRun, same⟩ |
      ⟨fault, post, _, same⟩
    · cases tail with
      | mk result state =>
          cases result with
          | error fault => cases same
          | ok tail =>
              cases same
              exact ⟨middle, firstRun, restRun⟩
    · cases same
  · rintro ⟨middle, firstRun, restRun⟩
    exact .inl ⟨value, middle, ⟨.ok values, after⟩, firstRun, restRun, rfl⟩

theorem source_arguments_cons_fault_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (first : Expr) (rest : List Expr) (before after : SourceState World) (fault : Fault) :
    SourceArgumentsEval interface heap calls frame (first :: rest) before
      ⟨.error fault, after⟩ ↔
      SourceExprEval interface heap calls frame first before ⟨.error fault, after⟩ ∨
      (∃ value middle,
        SourceExprEval interface heap calls frame first before ⟨.ok value, middle⟩ ∧
        SourceArgumentsEval interface heap calls frame rest middle ⟨.error fault, after⟩) := by
  rw [source_arguments_cons_exact]
  constructor
  · intro witnessed
    rcases witnessed with ⟨value, middle, tail, firstRun, restRun, same⟩ |
      ⟨actual, post, firstRun, same⟩
    · cases tail with
      | mk result state =>
          cases result with
          | error actual =>
              cases same
              exact .inr ⟨value, middle, firstRun, restRun⟩
          | ok tail => cases same
    · cases same; exact .inl firstRun
  · intro witnessed
    rcases witnessed with firstRun | ⟨value, middle, firstRun, restRun⟩
    · exact .inr ⟨fault, after, firstRun, rfl⟩
    · exact .inl ⟨value, middle, ⟨.error fault, after⟩, firstRun, restRun, rfl⟩

theorem source_strict_expression_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (expression : Expr) (arguments : List Expr)
    (operands : sourceStrictOperands? expression = some arguments)
    (before : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame expression before out ↔
      (∃ values middle,
        SourceArgumentsEval interface heap calls frame arguments before ⟨.ok values, middle⟩ ∧
        sourcePrimitive interface heap calls frame expression values middle out) ∨
      (∃ fault after,
        SourceArgumentsEval interface heap calls frame arguments before ⟨.error fault, after⟩ ∧
        out = ⟨.error fault, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | strict otherOperands evaluated operation =>
        cases Option.some.inj (operands.symm.trans otherOperands)
        exact .inl ⟨_, _, evaluated, operation⟩
    | strictFault otherOperands evaluated =>
        cases Option.some.inj (operands.symm.trans otherOperands)
        exact .inr ⟨_, _, evaluated, rfl⟩
    | address | addressFault | andFalse | andTrue | andFault | orTrue | orFalse | orFault =>
        cases operands
  · intro witnessed
    rcases witnessed with ⟨values, middle, evaluated, operation⟩ |
      ⟨fault, after, evaluated, same⟩
    · exact .strict operands evaluated operation
    · subst out; exact .strictFault operands evaluated

theorem source_operand_free_expression_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (expression : Expr) (operands : sourceStrictOperands? expression = some [])
    (before : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame expression before out ↔
      sourcePrimitive interface heap calls frame expression [] before out := by
  rw [source_strict_expression_exact expression [] operands]
  constructor
  · intro witnessed
    rcases witnessed with ⟨values, middle, evaluated, operation⟩ |
      ⟨fault, after, evaluated, _⟩
    · cases (source_arguments_nil_exact before _).mp evaluated
      exact operation
    · cases (source_arguments_nil_exact before _).mp evaluated
  · intro operation
    exact .inl ⟨[], before, .nil before, operation⟩

theorem source_and_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (left right : Expr) (before : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.binary .and left right) before out ↔
      (∃ after, SourceExprEval interface heap calls frame left before ⟨.ok (.bool false), after⟩ ∧
        out = ⟨.ok (.bool false), after⟩) ∨
      (∃ middle, SourceExprEval interface heap calls frame left before ⟨.ok (.bool true), middle⟩ ∧
        SourceExprEval interface heap calls frame right middle out) ∨
      (∃ fault after, SourceExprEval interface heap calls frame left before ⟨.error fault, after⟩ ∧
        out = ⟨.error fault, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | strict operands _ _ => cases operands
    | strictFault operands _ => cases operands
    | andFalse leftRun => exact .inl ⟨_, leftRun, rfl⟩
    | andTrue leftRun rightRun => exact .inr (.inl ⟨_, leftRun, rightRun⟩)
    | andFault leftRun => exact .inr (.inr ⟨_, _, leftRun, rfl⟩)
  · intro witnessed
    rcases witnessed with ⟨after, leftRun, same⟩ |
      ⟨middle, leftRun, rightRun⟩ | ⟨fault, after, leftRun, same⟩
    · subst out; exact .andFalse leftRun
    · exact .andTrue leftRun rightRun
    · subst out; exact .andFault leftRun

theorem source_or_exact {World : Type} {interface : Interface}
    {heap : SourceHeapSemantics World} {calls : SourceCalls World} {frame : SourceFrame}
    (left right : Expr) (before : SourceState World) (out : SourceOutcome World) :
    SourceExprEval interface heap calls frame (.binary .or left right) before out ↔
      (∃ after, SourceExprEval interface heap calls frame left before ⟨.ok (.bool true), after⟩ ∧
        out = ⟨.ok (.bool true), after⟩) ∨
      (∃ middle, SourceExprEval interface heap calls frame left before ⟨.ok (.bool false), middle⟩ ∧
        SourceExprEval interface heap calls frame right middle out) ∨
      (∃ fault after, SourceExprEval interface heap calls frame left before ⟨.error fault, after⟩ ∧
        out = ⟨.error fault, after⟩) := by
  constructor
  · intro ran
    cases ran with
    | strict operands _ _ => cases operands
    | strictFault operands _ => cases operands
    | orTrue leftRun => exact .inl ⟨_, leftRun, rfl⟩
    | orFalse leftRun rightRun => exact .inr (.inl ⟨_, leftRun, rightRun⟩)
    | orFault leftRun => exact .inr (.inr ⟨_, _, leftRun, rfl⟩)
  · intro witnessed
    rcases witnessed with ⟨after, leftRun, same⟩ |
      ⟨middle, leftRun, rightRun⟩ | ⟨fault, after, leftRun, same⟩
    · subst out; exact .orTrue leftRun
    · exact .orFalse leftRun rightRun
    · subst out; exact .orFault leftRun

end Mettapedia.GSLT.LanguageDef.NativeOps
