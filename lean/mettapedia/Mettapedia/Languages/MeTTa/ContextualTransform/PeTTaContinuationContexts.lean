import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaApplicationContexts

/-!
# Completed source operands and their real caller continuations

The source path supplied for an operand is lifted above the caller's actual
saved frames. Case, condition, collection and the last argument then resume
from the operand's reached state, input, output and freshness counter. The
rules retain branch substitutions and the prescribed copy/use increments.
These are completed-path laws; suspension before completion stays in the
source machine and is not mistaken for an empty operand.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContinuationContexts

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa
open Unifying PeTTaContexts

theorem operand_above_frame (registry : SpaceSemantics.Program) (before after : Configuration)
    (bindings : Subst) (inner : Atom) (answers : List Answer) (frame : Frame)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings inner)
      { after with control := .returned answers, frames := [] }) :
    Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := frame :: before.frames } bindings inner)
      { after with control := .returned answers, frames := frame :: before.frames } := by
  simpa [atExpression, appendFrames] using steps_append_frames evaluated (frame :: before.frames)

theorem operand_then_case (registry : SpaceSemantics.Program) (before after : Configuration)
    (bindings : Subst) (inner : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases)
    (answers : List Answer) (continued : List Control)
    (parsed : Eval.readCases rows = some cases)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings inner)
      { after with control := .returned answers, frames := [] })
    (selected : selectAnswers cases answers = some continued) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before bindings (.expression [.symbol "case", inner, .expression rows]))
      { after with control := .sequence continued [], frames := before.frames } := by
  have reached := Relation.ReflTransGen.head (Transition.case_enter
    (source := atExpression before bindings (.expression [.symbol "case", inner, .expression rows])) rfl parsed)
    (operand_above_frame registry before after bindings inner answers (.select cases) evaluated)
  exact reached.tail (.case_return rfl rfl selected)

theorem singleton_case_selection (bindings bound : Subst) (value body : Atom)
    (cases : SpaceSemantics.Cases) (selected : selectCase bindings value cases = some (some (bound, body))) :
    selectAnswers cases [⟨value, bindings⟩] = some [.evaluate bound body] := by
  simp [selectAnswers, selected]

theorem operand_then_case_body (registry : SpaceSemantics.Program) (before after : Configuration)
    (bindings produced bound : Subst) (inner value body : Atom)
    (rows : List Atom) (cases : SpaceSemantics.Cases)
    (parsed : Eval.readCases rows = some cases)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings inner)
      { after with control := .returned [⟨value, produced⟩], frames := [] })
    (selected : selectCase produced value cases = some (some (bound, body))) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before bindings (.expression [.symbol "case", inner, .expression rows]))
      (atExpression { after with frames := .sequence [] [] :: before.frames } bound body) := by
  exact (operand_then_case registry before after bindings inner rows cases [⟨value, produced⟩]
    [.evaluate bound body] parsed evaluated (singleton_case_selection produced bound value body cases selected)).tail
    (.sequence_enter rfl)

theorem operand_then_condition (registry : SpaceSemantics.Program) (before after : Configuration)
    (bindings : Subst) (inner yes no : Atom) (answers : List Answer)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings inner)
      { after with control := .returned answers, frames := [] }) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before bindings (.expression [.symbol "if", inner, yes, no]))
      { after with
        control := .sequence (answers.map fun answer =>
          .evaluate answer.bindings (if answer.value == Effects.boolean true then yes else no)) []
        frames := before.frames } := by
  have reached := Relation.ReflTransGen.head (Transition.if_enter
    (source := atExpression before bindings (.expression [.symbol "if", inner, yes, no])) rfl)
    (operand_above_frame registry before after bindings inner answers (.branch yes no) evaluated)
  exact reached.tail (.if_return rfl rfl)

theorem operand_then_collection (registry : SpaceSemantics.Program) (before after : Configuration)
    (bindings : Subst) (inner : Atom) (answers : List Answer)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings inner)
      { after with control := .returned answers, frames := [] }) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before bindings (.expression [.symbol "collapse", inner]))
      { after with
        control := .returned [⟨.expression (copies after.uses answers), bindings⟩]
        frames := before.frames
        uses := after.uses + answers.length } := by
  have reached := Relation.ReflTransGen.head (Transition.collapse_enter
    (source := atExpression before bindings (.expression [.symbol "collapse", inner])) rfl)
    (operand_above_frame registry before after bindings inner answers (.collect bindings) evaluated)
  exact reached.tail (.collapse_return rfl rfl)

theorem empty_collection_retains_effects (registry : SpaceSemantics.Program) (before after : Configuration)
    (bindings : Subst) (inner : Atom)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } bindings inner)
      { after with control := .returned [], frames := [] }) :
    Relation.ReflTransGen (Transition registry)
      (atExpression before bindings (.expression [.symbol "collapse", inner]))
      { after with control := .returned [⟨.expression [], bindings⟩], frames := before.frames } :=
  operand_then_collection registry before after bindings inner [] evaluated

/-- Bodies are selected from the reached public world and installed private
code. The invocation registry and that inventory determine call/arity policy. -/
theorem last_operand_then_live_equations (registry : SpaceSemantics.Program)
    (before after : Configuration) (incoming produced : Subst) (head : String)
    (inner value : Atom) (previous : List Atom) (index : Nat)
    (selected : Control) (used : Nat)
    (strict : Eval.argumentIsRaw registry head index = false)
    (ordinary : Eval.ioHead head = false) (notRemove : head ≠ "remove-atom")
    (notNative : StdLib.known head = false)
    (evaluated : Relation.ReflTransGen (Transition registry)
      (atExpression { before with frames := [] } incoming inner)
      { after with control := .returned [⟨value, produced⟩], frames := [] })
    (chosen : application (codeRegistry registry after.privateCode)
      (codeEquations after.state after.privateCode) head
      ((previous ++ [value]).map (resolve produced)) produced after.uses = some (selected, used)) :
    Relation.ReflTransGen (Transition registry)
      (PeTTaApplicationContexts.atArgument before incoming (.function head) inner [] previous index)
      { after with
        control := selected
        frames := .sequence [] [] :: before.frames
        uses := after.uses + used } := by
  have scheduled := PeTTaApplicationContexts.operand_then_arguments registry before after incoming
    (.function head) inner [] previous index [⟨value, produced⟩] strict evaluated
  have entered := scheduled.tail (Transition.sequence_enter rfl)
  exact entered.tail (.equations rfl ordinary notRemove notNative chosen)

/-- Reflection at the case continuation excludes a different branch schedule. -/
theorem case_return_exact (registry : SpaceSemantics.Program) (base : Configuration)
    (answers : List Answer) (cases : SpaceSemantics.Cases) (next : Configuration) :
    Transition registry
      { base with control := .returned answers, frames := .select cases :: base.frames } next ↔
      ∃ continued, selectAnswers cases answers = some continued ∧
        next = { base with control := .sequence continued [] } := by
  rw [← step_iff_transition]
  cases selected : selectAnswers cases answers with
  | none => simp [step, selected]
  | some continued => simp [step, selected, eq_comm]

theorem collection_return_exact (registry : SpaceSemantics.Program) (base : Configuration)
    (answers : List Answer) (bindings : Subst) (next : Configuration) :
    Transition registry
      { base with control := .returned answers, frames := .collect bindings :: base.frames } next ↔
      next = { base with
        control := .returned [⟨.expression (copies base.uses answers), bindings⟩]
        uses := base.uses + answers.length } := by
  rw [← step_iff_transition]
  simp [step, eq_comm]

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaContinuationContexts
