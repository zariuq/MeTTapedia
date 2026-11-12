import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyDeclarations

/-!
# Literal body modes at the actual fresh-clause frontier

The adapter reuses the existing complete clause scan and matcher. It changes
only the selected body's entry goal: a literal-held body is quoted, and an
evaluated body keeps its existing goal. An independent entry judgment reflects
both modes, including failed selections, original occurrence order and the
caller suffix. It does not evaluate an operand or match a clause twice.

This is a source-to-existing-machine scheduling component. Native driver
installation and the optional explicit-function escape are not asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyFrontier

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open EagerDFS.Destination
open CallArityDispatch SelectedBodyPolicy
open PettaSelectedBodyDeclarations (family)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (renameTypeVars)

def schedule (held : Bool) (selected : Control) : Control :=
  if held then
    {selected with goals := match selected.goals with
      | .evaluate body destination :: older => .evaluate (OutputPlan.hold body) destination :: older
      | other => other}
  else selected

def frontier (program : SpaceSemantics.Program) (control : Control) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal) : List (Nat × Control) :=
  (ClauseChoice.choices program control head arguments destination older).map fun (occurrence, selected) =>
    (occurrence, schedule (OutputPlan.rawOutput program head arguments.length) selected)

inductive Entry (program : SpaceSemantics.Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) : Nat → Control → Prop where
  | held (occurrence : Nat) (equation : SpaceSemantics.Equation) (bindings : Equations)
      (row : program.equations[occurrence]? = some equation) (sameHead : equation.head = head)
      (matched : Refinement control.bindings (.expression (.symbol head :: arguments))
        (ClauseChoice.freshPattern control occurrence equation) (some bindings))
      (literal : HoldsBody .complete arguments.length (family program head)) :
      Entry program control head arguments destination older occurrence
        {control with bindings := bindings, goals := .evaluate (OutputPlan.hold (ClauseChoice.freshBody control occurrence equation)) destination :: older}
  | evaluated (occurrence : Nat) (equation : SpaceSemantics.Equation) (bindings : Equations)
      (row : program.equations[occurrence]? = some equation) (sameHead : equation.head = head)
      (matched : Refinement control.bindings (.expression (.symbol head :: arguments))
        (ClauseChoice.freshPattern control occurrence equation) (some bindings))
      (notLiteral : ¬ HoldsBody .complete arguments.length (family program head)) :
      Entry program control head arguments destination older occurrence
        {control with bindings, goals := .evaluate (ClauseChoice.freshBody control occurrence equation) destination :: older}

/-- Even the matcher cannot select a complete equation at a foreign arity.
This follows from its common solution, not from a second arity filter. -/
theorem matched_arity (control : Control) (head : String) (arguments : List Atom)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (bindings : Equations)
    (matched : Refinement control.bindings (.expression (.symbol head :: arguments))
      (ClauseChoice.freshPattern control occurrence equation) (some bindings)) :
    equation.arguments.length = arguments.length := by
  cases matched with
  | accepted environment old linked =>
    simp only [ClauseChoice.freshPattern, ClauseChoice.pattern, renameTypeVars, List.map_cons,
      Bridges.ScopedClosedEquationSource.read_expression, List.map_cons, Atom.expression.injEq,
      List.cons.injEq] at linked
    have lengths := congrArg List.length linked.2
    simpa using lengths.symm

theorem member_iff (program : SpaceSemantics.Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) (occurrence : Nat) (next : Control) :
    (occurrence, next) ∈ frontier program control head arguments destination older ↔
      Entry program control head arguments destination older occurrence next := by
  constructor
  · intro member
    obtain ⟨⟨index, selected⟩, present, same⟩ := List.mem_map.mp member
    have indexEq : index = occurrence := congrArg Prod.fst same
    subst index
    have nextEq : schedule (OutputPlan.rawOutput program head arguments.length) selected = next :=
      congrArg Prod.snd same
    obtain ⟨equation, row, attempted⟩ := (ClauseChoice.mem_choices_iff ..).mp present
    by_cases sameHead : equation.head = head
    · obtain ⟨bindings, matched, rfl⟩ :=
        (ClauseChoice.attempt_iff control head arguments destination older occurrence equation sameHead _).mp attempted
      cases held : OutputPlan.rawOutput program head arguments.length with
      | false =>
        have notLiteral : ¬ HoldsBody .complete arguments.length (family program head) := by
          intro literal
          have accepted := (PettaSelectedBodyDeclarations.rawOutput_iff ..).mpr literal
          rw [held] at accepted
          cases accepted
        rw [← nextEq]
        simpa only [schedule, held, Bool.false_eq_true, ↓reduceIte] using
          (Entry.evaluated (destination := destination) (older := older)
            occurrence equation bindings row sameHead matched notLiteral)
      | true =>
        rw [← nextEq]
        simpa only [schedule, held, ↓reduceIte] using
          (Entry.held (destination := destination) (older := older) occurrence equation bindings row sameHead matched
            ((PettaSelectedBodyDeclarations.rawOutput_iff ..).mp held))
    · rw [ClauseChoice.wrong_head_not_selected _ _ _ _ _ _ _ sameHead] at attempted
      cases attempted
  · intro entry
    cases entry with
    | held equation bindings row sameHead matched literal =>
      have raw := (PettaSelectedBodyDeclarations.rawOutput_iff ..).mpr literal
      apply List.mem_map.mpr
      refine ⟨(occurrence, {control with bindings := bindings, goals := .evaluate (ClauseChoice.freshBody control occurrence equation) destination :: older}), ?_, ?_⟩
      · apply (ClauseChoice.mem_choices_iff ..).mpr
        exact ⟨equation, row,
          (ClauseChoice.attempt_iff control head arguments destination older occurrence equation sameHead _).mpr
            ⟨bindings, matched, rfl⟩⟩
      · simp [schedule, raw]
    | evaluated equation bindings row sameHead matched notLiteral =>
      have raw : OutputPlan.rawOutput program head arguments.length = false := by
        cases raw : OutputPlan.rawOutput program head arguments.length
        · rfl
        · exact False.elim (notLiteral ((PettaSelectedBodyDeclarations.rawOutput_iff ..).mp raw))
      apply List.mem_map.mpr
      refine ⟨(occurrence, {control with bindings := bindings, goals := .evaluate (ClauseChoice.freshBody control occurrence equation) destination :: older}), ?_, ?_⟩
      · apply (ClauseChoice.mem_choices_iff ..).mpr
        exact ⟨equation, row,
          (ClauseChoice.attempt_iff control head arguments destination older occurrence equation sameHead _).mpr
            ⟨bindings, matched, rfl⟩⟩
      · simp [schedule, raw]

theorem occurrence_order (program : SpaceSemantics.Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) :
    (frontier program control head arguments destination older).map Prod.fst =
      (ClauseChoice.choices program control head arguments destination older).map Prod.fst := by
  simp [frontier, List.map_map, Function.comp_def]

theorem occurrence_count (program : SpaceSemantics.Program) (control : Control) (head : String)
    (arguments : List Atom) (destination : Atom) (older : List Goal) :
    (frontier program control head arguments destination older).length =
      (ClauseChoice.choices program control head arguments destination older).length := by
  simp [frontier]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaSelectedBodyFrontier
