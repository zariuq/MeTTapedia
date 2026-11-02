import Mettapedia.Machines.ExecutionControl
import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Selecting a branch from a completed condition

The source has already returned the condition's occurrences to its branch
frame. A native caller retains the actual value and chooses its branch without
entering the source condition again. The target below includes the source's
administrative empty sequence frame, so comparison preserves every older frame,
the reached store, input and output literally.

The maintained PeTTa judgment uses its grounded Boolean codec. Native Boolean
spelling, C ownership, expression/conditional packet admission and source debit
remain separate correspondence obligations. HE's error and undecided-condition
policies retain their existing selector rather than this PeTTa-specific law.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SourceCondition

open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

abbrev Bindings := Mettapedia.Languages.ProcessCalculi.MORK.Subst

/-- Canonical three-operand control entry, using the existing operand reader. -/
def enterControl (bindings : Bindings) (plan : ExecutionControl.Plan) (fields : Array Atom)
    (before : Eval.Configuration) : Option Eval.Configuration := do
  let .branch condition yes (some no) ← ExecutionControl.read plan fields | none
  return {before with
    control := .evaluate bindings condition
    frames := .branch bindings yes no :: before.frames}

theorem planned_source_entry (program : SpaceSemantics.Program) (bindings : Bindings)
    (condition yes no : Atom) (before : Eval.Configuration) :
    (ExecutionControl.elaborate .branch 3).bind
        (fun plan => enterControl bindings plan #[condition, yes, no] before) =
      Eval.step program {before with
        control := .evaluate bindings (.expression [.symbol "if", condition, yes, no])} := by
  rfl

def inspect : Atom → Option Bool
  | .grounded (.bool truth) => some truth
  | _ => none

/-- Independent native branch selection. Unknown values take PeTTa's else
branch; the value's expression syntax does not create an invocation. -/
def selected (value yes no : Atom) : Atom :=
  match inspect value with
  | some true => yes
  | some false | none => no

theorem selection_refines (value yes no : Atom) :
    selected value yes no = (if value == Effects.boolean true then yes else no) := by
  cases value with
  | symbol name => rfl
  | var name => rfl
  | expression fields => rfl
  | grounded value =>
      cases value <;> try rfl
      rename_i truth
      cases truth <;> rfl

/-- The existing source frame carries the caller's environment and branches. -/
def source (bindings : Bindings) (value yes no : Atom) (before : Eval.Configuration) :
    Eval.Configuration :=
  {before with
    control := .returned [value]
    frames := .branch bindings yes no :: before.frames}

/-- A completed native condition enters the selected branch in the reached
state. No original producer expression is kept as executable work. -/
def resumeRetained (bindings : Bindings) (value yes no : Atom) (before : Eval.Configuration) :
    Eval.Configuration :=
  {before with
    control := .evaluate bindings (selected value yes no)
    frames := .sequence [] [] :: before.frames}

/-- Two source administrative steps consume one already-completed condition
and agree with the retained-value entry, without executing its producer. -/
theorem source_steps_refine (program : SpaceSemantics.Program) (bindings : Bindings)
    (value yes no : Atom) (before : Eval.Configuration) :
    (Eval.step program (source bindings value yes no before)).bind (Eval.step program) =
      some (resumeRetained bindings value yes no before) := by
  simp [source, resumeRetained, Eval.step, selection_refines]

theorem reached_state_preserved (bindings : Bindings) (value yes no : Atom)
    (before : Eval.Configuration) :
    (resumeRetained bindings value yes no before).state = before.state ∧
      (resumeRetained bindings value yes no before).input = before.input ∧
      (resumeRetained bindings value yes no before).output = before.output := by
  exact ⟨rfl, rfl, rfl⟩

theorem older_frames_preserved (bindings : Bindings) (value yes no : Atom)
    (before : Eval.Configuration) :
    (resumeRetained bindings value yes no before).frames = .sequence [] [] :: before.frames := rfl

/-- A changed equation program can affect future calls, but cannot turn this
already-returned condition into a new source invocation. -/
theorem program_change_keeps_completed_entry (first later : SpaceSemantics.Program)
    (bindings : Bindings) (value yes no : Atom) (before : Eval.Configuration) :
    (Eval.step first (source bindings value yes no before)).bind (Eval.step first) =
      (Eval.step later (source bindings value yes no before)).bind (Eval.step later) := by
  rw [source_steps_refine, source_steps_refine]

theorem unknown_condition_selects_else (value yes no : Atom) (unknown : inspect value = none) :
    selected value yes no = no := by simp [selected, unknown]

theorem code_shaped_value_stays_data (fields : List Atom) (yes no : Atom) :
    selected (.expression fields) yes no = no := rfl

theorem false_and_unknown_agree_only_on_selection (value yes no : Atom)
    (unknown : inspect value = none) :
    selected value yes no = selected (Effects.boolean false) yes no := by
  rw [unknown_condition_selects_else value yes no unknown]
  rfl

theorem unknown_is_not_truth :
    inspect (.expression [.symbol "println!", .grounded (.string "held")]) = none ∧
    selected (.expression [.symbol "println!", .grounded (.string "held")])
        (.symbol "yes") (.symbol "no") = .symbol "no" ∧
    selected (Effects.boolean true) (.symbol "yes") (.symbol "no") = .symbol "yes" := by
  decide +kernel

end Mettapedia.Machines.SourceCondition
