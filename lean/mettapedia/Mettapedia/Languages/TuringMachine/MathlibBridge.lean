import Mettapedia.Languages.TuringMachine.Configurations
import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Authored transition tables and Mathlib's single-tape machines

Each deterministic table row becomes a TM1 write/move/goto statement. One
source firing is one macro step; a halted source configuration receives a
separate final halt acknowledgement. The comparison preserves and reflects
halting, retains finite control support, and composes with Mathlib's TM1-to-TM0
compiler. Raw configuration terms retain trailing blanks that the quotient
tape forgets. A nondeterministic control exhibits the necessity of the
unique-row hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Turing

namespace MathlibBridge

/-- A table row as a write, move, and goto statement of Mathlib's TM1. -/
def rowStatement (entry : Transition) : TM1.Stmt Nat Nat Unit :=
  .write (fun _ _ => entry.write)
    (.move entry.move.dir (.goto (fun _ _ => entry.next)))

/-- Inspect the finite table in its authored order. -/
def tableStatement (entries : List Transition) (state : Nat) : TM1.Stmt Nat Nat Unit :=
  match entries with
  | [] => .halt
  | entry :: rest =>
      .branch (fun symbol _ => entry.state == state && entry.read == symbol)
        (rowStatement entry) (tableStatement rest state)

def machine (source : Machine) : Nat → TM1.Stmt Nat Nat Unit :=
  tableStatement source.transitions

/-- A running control state with the source's quotient tape. -/
def running (configuration : Configuration) : TM1.Cfg Nat Nat Unit :=
  ⟨some configuration.state, (), configuration.tape⟩

/-- The TM1 halt acknowledgement retains the final tape. -/
def stopped (configuration : Configuration) : TM1.Cfg Nat Nat Unit :=
  ⟨none, (), configuration.tape⟩

theorem after_state (configuration : Configuration) (entry : Transition) :
    (configuration.after entry).state = entry.next := by
  cases move : entry.move <;> simp only [Configuration.after, move]
  · cases configuration.left <;> rfl
  · cases configuration.right <;> rfl

theorem stepAux_row (entry : Transition) (configuration : Configuration) :
    TM1.stepAux (rowStatement entry) () configuration.tape =
      running (configuration.after entry) := by
  simp only [rowStatement, TM1.stepAux, running,
    Configuration.tape_after, after_state]

theorem stepAux_table (entries : List Transition) (configuration : Configuration) :
    TM1.stepAux (tableStatement entries configuration.state) () configuration.tape =
      match entries.find? (fun entry =>
          entry.state == configuration.state && entry.read == configuration.scanned) with
      | none => stopped configuration
      | some entry => running (configuration.after entry) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [tableStatement, TM1.stepAux, Configuration.tape_head,
        List.find?_cons]
      cases (entry.state == configuration.state && entry.read == configuration.scanned)
      · simpa using ih
      · simpa using stepAux_row entry configuration

/-- One authored table transition is exactly one TM1 macro step. If no row
applies, TM1 takes a final halt acknowledgement instead. -/
theorem step_running (source : Machine) (configuration : Configuration) :
    TM1.step (machine source) (running configuration) =
      some (match source.next? configuration with
        | none => stopped configuration
        | some next => running next) := by
  simp only [TM1.step, running, machine, stepAux_table, Machine.next?, Machine.entryFor]
  cases source.transitions.find? (fun entry =>
    entry.state == configuration.state && entry.read == configuration.scanned) <;> rfl

@[simp] theorem step_stopped (source : Machine) (configuration : Configuration) :
    TM1.step (machine source) (stopped configuration) = none := rfl

theorem next_none_iff_halted (source : Machine) (configuration : Configuration) :
    source.next? configuration = none ↔ Halted source configuration.term := by
  constructor
  · exact Machine.halted_of_next?_eq_none
  · intro halted
    cases next : source.next? configuration with
    | none => rfl
    | some target => exact (halted target.term (Machine.step_of_next? next)).elim

/-- First-row execution agrees with the authored relation when the table
has a unique row for each state/symbol pair. -/
theorem next_some_iff_step (source : Machine) (deterministic : source.Deterministic)
    (configuration next : Configuration) :
    source.next? configuration = some next ↔
      Step base (turingMachine source) configuration.term next.term := by
  constructor
  · exact Machine.step_of_next?
  · intro step
    cases found : source.next? configuration with
    | none => exact (Machine.halted_of_next?_eq_none found _ step).elim
    | some target =>
        have same : target.term = next.term :=
          step_unique deterministic (Machine.step_of_next? found) step
        exact congrArg some (Configuration.term_injective same)

theorem reaches_next_forward (source : Machine)
    {first last : Configuration}
    (path : StateTransition.Reaches source.next? first last) :
    Reaches source first.term last.term := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (Machine.step_of_next? step)

theorem reaches_next_reflect (source : Machine) (deterministic : source.Deterministic)
    {first : Configuration} {target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (path : Reaches source first.term target) :
    ∃ last : Configuration, target = last.term ∧
      StateTransition.Reaches source.next? first last := by
  induction path with
  | refl => exact ⟨first, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨current, rfl, reach⟩ := ih
      obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp step
      refine ⟨_, rfl, reach.tail ?_⟩
      exact (next_some_iff_step source deterministic current _).mpr
        (step_term_iff.mpr ⟨entry, member, applies, rfl⟩)

theorem next_eval_dom_iff_halts (source : Machine) (deterministic : source.Deterministic)
    (configuration : Configuration) :
    (StateTransition.eval source.next? configuration).Dom ↔
      HaltsFrom source configuration.term := by
  constructor
  · intro dom
    obtain ⟨last, member⟩ := Part.dom_iff_mem.mp dom
    obtain ⟨path, none⟩ := StateTransition.mem_eval.mp member
    exact ⟨last.term, reaches_next_forward source path,
      Machine.halted_of_next?_eq_none none⟩
  · rintro ⟨target, path, halted⟩
    obtain ⟨last, rfl, reach⟩ := reaches_next_reflect source deterministic path
    exact Part.dom_iff_mem.mpr ⟨last, StateTransition.mem_eval.mpr
      ⟨reach, (next_none_iff_halted source last).mpr halted⟩⟩

theorem reaches_running (source : Machine) (deterministic : source.Deterministic)
    {configuration : Configuration} {target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (path : Reaches source configuration.term target) :
    ∃ final : Configuration, target = final.term ∧
      StateTransition.Reaches (TM1.step (machine source))
        (running configuration) (running final) := by
  induction path with
  | refl => exact ⟨configuration, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨current, rfl, reach⟩ := ih
      obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp step
      have next : source.next? current = some (current.after entry) :=
        (next_some_iff_step source deterministic current _).mpr
          (step_term_iff.mpr ⟨entry, member, applies, rfl⟩)
      refine ⟨current.after entry, rfl, reach.tail ?_⟩
      simp only [Option.mem_def, step_running, next]

theorem halts_implies_eval_dom (source : Machine) (deterministic : source.Deterministic)
    (configuration : Configuration) (halts : HaltsFrom source configuration.term) :
    (StateTransition.eval (TM1.step (machine source)) (running configuration)).Dom := by
  obtain ⟨target, path, halted⟩ := halts
  obtain ⟨final, rfl, reach⟩ := reaches_running source deterministic path
  have none := (next_none_iff_halted source final).mpr halted
  have stoppedStep : stopped final ∈ TM1.step (machine source) (running final) := by
    simp only [Option.mem_def, step_running, none]
  exact Part.dom_iff_mem.mpr ⟨stopped final,
    StateTransition.mem_eval.mpr ⟨reach.tail stoppedStep, rfl⟩⟩

/-- Every reached TM1 state has an authored configuration witness. A final
halt acknowledgement is possible only at an authored halted configuration. -/
theorem reaches_reflect (source : Machine) {configuration : Configuration}
    {target : TM1.Cfg Nat Nat Unit}
    (path : StateTransition.Reaches (TM1.step (machine source))
      (running configuration) target) :
    ∃ final : Configuration, Reaches source configuration.term final.term ∧
      (target = running final ∨
        target = stopped final ∧ Halted source final.term) := by
  induction path with
  | refl => exact ⟨configuration, .refl, Or.inl rfl⟩
  | tail _ step ih =>
      obtain ⟨current, reach, runningEq | ⟨stoppedEq, halted⟩⟩ := ih
      · subst runningEq
        cases next : source.next? current with
        | none =>
            have same := step
            simp only [Option.mem_def, step_running, next, Option.some.injEq] at same
            exact ⟨current, reach, Or.inr ⟨same.symm,
              Machine.halted_of_next?_eq_none next⟩⟩
        | some after =>
            have same := step
            simp only [Option.mem_def, step_running, next, Option.some.injEq] at same
            exact ⟨after, reach.tail (Machine.step_of_next? next), Or.inl same.symm⟩
      · subst stoppedEq
        simp at step

theorem eval_dom_iff_halts (source : Machine) (deterministic : source.Deterministic)
    (configuration : Configuration) :
    (StateTransition.eval (TM1.step (machine source)) (running configuration)).Dom ↔
      HaltsFrom source configuration.term := by
  constructor
  · intro dom
    obtain ⟨target, value⟩ := Part.dom_iff_mem.mp dom
    obtain ⟨path, terminal⟩ := StateTransition.mem_eval.mp value
    obtain ⟨final, reach, runningEq | ⟨stoppedEq, halted⟩⟩ := reaches_reflect source path
    · subst runningEq
      simp only [step_running, Option.some_ne_none] at terminal
    · exact ⟨final.term, reach, halted⟩
  · exact halts_implies_eval_dom source deterministic configuration

def labelSupport (source : Machine) : Finset Nat :=
  insert 0 (source.transitions.map Transition.next).toFinset

theorem tableStatement_supports (entries : List Transition) (state : Nat)
    (support : Finset Nat) (closed : ∀ entry ∈ entries, entry.next ∈ support) :
    TM1.SupportsStmt support (tableStatement entries state) := by
  induction entries with
  | nil => trivial
  | cons entry rest ih =>
      refine ⟨?_, ih (fun other member => closed other (List.mem_cons_of_mem _ member))⟩
      intro symbol store
      exact closed entry (List.mem_cons_self)

/-- The generated TM1 uses a finite set of labels even though the common
numbered-state type itself is infinite. -/
theorem machine_supports (source : Machine) :
    TM1.Supports (machine source) (labelSupport source) := by
  refine ⟨Finset.mem_insert_self _ _, ?_⟩
  intro state _
  apply tableStatement_supports
  intro entry member
  exact Finset.mem_insert_of_mem
    (List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, member, rfl⟩))

def initial (input : List Nat) : Configuration :=
  ⟨0, [], input.headI, input.tail⟩

theorem running_initial (input : List Nat) :
    running (initial input) = (TM1.init input : TM1.Cfg Nat Nat Unit) := by
  cases input with
  | nil => simp [running, initial, Configuration.tape, TM1.init, Tape.mk₁,
      Tape.mk₂, listBlank_mk_blank]
  | cons symbol rest => rfl

theorem tm1_eval_dom_iff (source : Machine) (deterministic : source.Deterministic)
    (input : List Nat) :
    (TM1.eval (machine source) input).Dom ↔ HaltsFrom source (initial input).term := by
  change (StateTransition.eval (TM1.step (machine source)) (TM1.init input)).Dom ↔ _
  simpa only [running_initial] using
    eval_dom_iff_halts source deterministic (initial input)

/-- Mathlib's existing compiler lowers this same table interpreter to
single write-or-move instructions, preserving halting. -/
theorem tm0_eval_dom_iff (source : Machine) (deterministic : source.Deterministic)
    (input : List Nat) :
    (TM0.eval (TM1to0.tr (machine source)) input).Dom ↔
      HaltsFrom source (initial input).term := by
  rw [TM1to0.tr_eval]
  exact tm1_eval_dom_iff source deterministic input

theorem tm0_finitely_supported (source : Machine) :
    TM0.Supports (TM1to0.tr (machine source))
      (TM1to0.trStmts (machine source) (labelSupport source) : Set _) :=
  TM1to0.tr_supports (machine source) (machine_supports source)

/-- An ordered interpreter selects its first row. A nondeterministic
authored table can also take a different row; the determinism hypothesis
in the exact comparison is necessary. -/
theorem first_row_is_not_all_choices :
    ∃ source : Machine, ∃ target : Configuration,
      Step base (turingMachine source) Configuration.blank.term target.term ∧
        source.next? Configuration.blank ≠ some target := by
  let first : Transition := ⟨0, 0, 1, .right, 0⟩
  let second : Transition := ⟨0, 0, 2, .right, 0⟩
  let source : Machine := ⟨[first, second]⟩
  refine ⟨source, Configuration.blank.after second, ?_, ?_⟩
  · exact step_term_iff.mpr ⟨second, by simp [source], ⟨rfl, rfl⟩, rfl⟩
  · decide

end MathlibBridge
end Mettapedia.Languages.TuringMachine
