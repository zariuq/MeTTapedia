import Mettapedia.GSLT.Compilation.Uniform.ExecutableQueryRules
import Mettapedia.Languages.MeTTa.PeTTa.EvalOnTheStep

/-!
# PeTTa evaluation by a finite program of Transform rules

The same 41 authored rules are lowered by the uniform compiler. The runner
matches their rows and calls the fixed executable data operations of
`ConfigurationLanguageDef`. Equation selection, substitution and primitives
are provided by those operations. Evaluator transitions themselves come from
the compiled rules.

Readback and the source evaluator's transition theorem give a proof for
every bounded run, including completion, a primitive fault, and running out
of fuel. The support conditions are those of the existing store encoding.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ExecutableOnTheStep

open Mettapedia.GSLT.Compilation.Uniform
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
open ConfigurationEncoding (encode decode decode_encode cellSupportAfter transition_support)
open ConfigurationLanguageDef (language relationEnv)

private def checked :=
  (ExecutableQueryRules.compile EvalOnTheStep.inputs language).toOption

private theorem checked_isSome : checked.isSome = true := by
  obtain ⟨relational, authored, _⟩ := EvalOnTheStep.evaluator_compiles
  obtain ⟨schemas, compiled, _⟩ := ExecutableQueryRules.compile_complete authored
  rw [checked, compiled]
  rfl

/-- The finite program, extracted from the computed compilation result. -/
def rules : List Executable.Schema := checked.get checked_isSome

theorem compiled : ExecutableQueryRules.compile EvalOnTheStep.inputs language = .ok rules := by
  have found : checked = some rules := (Option.some_get checked_isSome).symm
  cases h : ExecutableQueryRules.compile EvalOnTheStep.inputs language with
  | error _ =>
      rw [checked, h] at found
      cases found
  | ok result =>
      rw [checked, h] at found
      rw [Option.some.inj found]

theorem rule_count : rules.length = 41 := by
  obtain ⟨_, authored, authoredCount⟩ := EvalOnTheStep.evaluator_compiles
  obtain ⟨schemas, lowered, sameCount⟩ := ExecutableQueryRules.compile_complete authored
  rw [compiled] at lowered
  rw [Except.ok.inj lowered, sameCount, authoredCount]

/-- Enumerate the actual firings of the compiled program. -/
def successors (program : SpaceSemantics.Program) (row : Pattern) : List Pattern :=
  ExecutableQueryRules.successorPatterns (relationEnv program) language rules row

theorem mem_successors (program : SpaceSemantics.Program) (before : Eval.Configuration)
    (cells : List String) (vacant : NamedSpaces.Store.EmptyTail before.state [])
    (covers : ∀ name, name ∉ cells → before.state.cells name = none) (target : Pattern) :
    target ∈ successors program (encode before cells) ↔
      ∃ after, Eval.step program before = some after ∧ target = encode after (cellSupportAfter before cells) := by
  rw [successors, ExecutableQueryRules.mem_successorPatterns (EvalOnTheStep.relations_moded program)
    (EvalOnTheStep.relations_data program) (EvalOnTheStep.configurations_carrier program) compiled
    ⟨before, cells, vacant, covers, rfl⟩]
  change Mettapedia.OSLF.Framework.TypeSynthesis.langReducesUsing (relationEnv program) language
    (encode before cells) target ↔ _
  rw [← Mettapedia.OSLF.Framework.TypeSynthesis.mem_rootFrontier_iff_langReducesUsing
    (relationEnv program) language ConfigurationLanguageDef.nonrecursive_rules,
    ConfigurationLanguageDef.frontier_eq_step program before cells vacant covers]
  simp [List.mem_map, Option.mem_toList, eq_comm]

theorem head_successor (program : SpaceSemantics.Program) (before : Eval.Configuration)
    (cells : List String) (vacant : NamedSpaces.Store.EmptyTail before.state [])
    (covers : ∀ name, name ∉ cells → before.state.cells name = none) :
    (successors program (encode before cells)).head? =
      (Eval.step program before).map fun after => encode after (cellSupportAfter before cells) := by
  cases found : successors program (encode before cells) with
  | nil =>
      cases computed : Eval.step program before with
      | none => rfl
      | some after =>
          have impossible := (mem_successors program before cells vacant covers _).mpr
            ⟨after, computed, rfl⟩
          simp [found] at impossible
  | cons row rest =>
      have member : row ∈ successors program (encode before cells) := by
        rw [found]
        exact List.mem_cons_self
      obtain ⟨after, computed, rfl⟩ := (mem_successors program before cells vacant covers row).mp member
      rw [computed]
      rfl

private def terminal (configuration : Eval.Configuration) : Option Eval.Outcome :=
  match configuration.control, configuration.frames with
  | .returned answers, [] =>
      some (.complete configuration.state answers configuration.input configuration.output)
  | .fault fault, _ => some (.fault fault configuration)
  | _, _ => none

private def drive (next : Pattern → Option Pattern) : ℕ → Pattern → Option Eval.Outcome
  | 0, row => (decode row).map fun configuration =>
      (terminal configuration).getD (.exhausted configuration)
  | fuel + 1, row =>
      match decode row with
      | none => none
      | some configuration =>
          match terminal configuration with
          | some result => some result
          | none =>
              match next row with
              | none => some (.exhausted configuration)
              | some after => drive next fuel after

/-- Run the compiled evaluator on its rows. Configuration readback observes
terminal answers and faults. The next row is obtained by rule firing. -/
def run (program : SpaceSemantics.Program) : ℕ → Pattern → Option Eval.Outcome :=
  drive fun row => (successors program row).head?

private theorem reference_run (program : SpaceSemantics.Program) (fuel : ℕ) (before : Eval.Configuration) :
    Eval.run program fuel before =
      match terminal before with
      | some result => result
      | none =>
          match fuel with
          | 0 => .exhausted before
          | n + 1 =>
              match Eval.step program before with
              | some after => Eval.run program n after
              | none => .exhausted before := by
  rw [Eval.run.eq_def]
  cases hc : before.control <;> cases hf : before.frames <;> simp [terminal, hc, hf] <;> cases fuel <;> rfl

private theorem drive_eq (program : SpaceSemantics.Program) (next : Pattern → Option Pattern)
    (linked : ∀ before cells, NamedSpaces.Store.EmptyTail before.state [] →
      (∀ name, name ∉ cells → before.state.cells name = none) →
      next (encode before cells) =
        (Eval.step program before).map (fun after => encode after (cellSupportAfter before cells))) :
    ∀ (fuel : ℕ) (before : Eval.Configuration) (cells : List String),
      NamedSpaces.Store.EmptyTail before.state [] →
      (∀ name, name ∉ cells → before.state.cells name = none) →
      drive next fuel (encode before cells) = some (Eval.run program fuel before) := by
  intro fuel
  induction fuel with
  | zero =>
      intro before cells vacant covers
      rw [drive, decode_encode before cells vacant covers, reference_run]
      cases stopped : terminal before <;> simp [stopped]
  | succ fuel ih =>
      intro before cells vacant covers
      rw [drive, decode_encode before cells vacant covers, reference_run]
      cases stopped : terminal before with
      | some outcome => simp [stopped]
      | none =>
          simp only [stopped]
          rw [linked before cells vacant covers]
          cases computed : Eval.step program before with
          | none => rfl
          | some after =>
              have stepped := (Eval.step_iff_transition program before after).mp computed
              exact ih after (cellSupportAfter before cells)
                (DeclarativeSpec.transition_empty_tail vacant stepped) (transition_support cells covers stepped)

/-- Bounded execution has exactly the source outcome, with the store and the
order and multiplicity of returned answers retained. -/
theorem run_eq (program : SpaceSemantics.Program) (fuel : ℕ) (before : Eval.Configuration) (cells : List String)
    (vacant : NamedSpaces.Store.EmptyTail before.state [])
    (covers : ∀ name, name ∉ cells → before.state.cells name = none) :
    run program fuel (encode before cells) = some (Eval.run program fuel before) :=
  drive_eq program (fun row => (successors program row).head?) (head_successor program) fuel before cells vacant covers

namespace Controls

def emptyProgram : SpaceSemantics.Program := { equations := [], declarations := [] }

def integer (value : Int) : Atom := .grounded (.int value)

def addition : Atom := .expression [.symbol "+", integer 7, integer 5]

def answers (outcome : Option Eval.Outcome) : Option (List Atom) :=
  match outcome with
  | some (.complete _ values _ _) => some values
  | _ => none

set_option maxHeartbeats 600000 in
theorem addition_evaluates :
    answers (run emptyProgram 32 (encode (Eval.start (Effects.loaded emptyProgram) addition) [])) =
      some [integer 12] := by
  rw [run_eq emptyProgram 32 _ [] (Effects.loaded_empty_tail _) (fun _ _ => rfl)]
  decide +kernel

theorem zero_fuel_exhausts :
    (match run emptyProgram 0 (encode (Eval.start (Effects.loaded emptyProgram) addition) []) with
      | some (.exhausted _) => true
      | _ => false) = true := by
  rw [run_eq emptyProgram 0 _ [] (Effects.loaded_empty_tail _) (fun _ _ => rfl)]
  rfl

end Controls

#print axioms compiled
#print axioms mem_successors
#print axioms run_eq
#print axioms Controls.addition_evaluates

end Mettapedia.Languages.MeTTa.PeTTa.ExecutableOnTheStep
