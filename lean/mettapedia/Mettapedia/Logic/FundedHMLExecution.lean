import Mettapedia.Logic.FundedHMLMachine

/-!
# Actual purse-limited execution of independently compiled modal programs

The controller executes the next instruction only after a successful stack
operation and when one purse cell is available. Its result retains the actual
ordered occurrence path. Exhausted purses and malformed programs stop at
their supplied unfinished configuration; neither produces an invented answer.

Successful unbounded execution earns the exact funded prefix length. The
compiler comparison supplies this hypothesis for every admitted formula,
independently of the controller and the funded transition presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded

open Inspection
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe u v

variable {State : Type u} {Action : Type v} {n : Nat}

def run (environment : BooleanEnv State n) :
    (program : List (Instruction State n)) → (stack : List Bool) →
    (budget spent : Nat) →
      Σ endpoint : Configuration State n, Path environment ⟨program, stack, budget, spent⟩ endpoint
  | [], stack, budget, spent => ⟨⟨[], stack, budget, spent⟩, .refl _⟩
  | instruction :: rest, stack, 0, spent =>
      ⟨⟨instruction :: rest, stack, 0, spent⟩, .refl _⟩
  | instruction :: rest, stack, budget + 1, spent =>
      match checked : instruction.execute environment stack with
      | none => ⟨⟨instruction :: rest, stack, budget + 1, spent⟩, .refl _⟩
      | some nextStack =>
          let continued := run environment rest nextStack budget (spent + 1)
          ⟨continued.1, .cons ⟨instruction, ⟨rfl, checked, rfl, rfl⟩⟩ continued.2⟩

theorem run_length (environment : BooleanEnv State n)
    (program : List (Instruction State n)) (stack output : List Bool)
    (budget spent : Nat) (computed : execute environment program stack = some output) :
    (run environment program stack budget spent).2.sites.length = min budget program.length := by
  induction program generalizing stack budget spent with
  | nil => simp only [run, OccurrencePath.sites_refl, List.length_nil, Nat.min_zero]
  | cons instruction rest inductionHypothesis =>
      cases budget with
      | zero => rfl
      | succ budget =>
          simp only [run]
          split
          · rename_i checked
            simp [execute, checked] at computed
          · rename_i nextStack checked
            have suffix : execute environment rest nextStack = some output := by
              simpa only [execute, checked, Option.bind_some] using computed
            have counted := inductionHypothesis nextStack budget (spent + 1) suffix
            change (run environment rest nextStack budget (spent + 1)).2.sites.length + 1 =
              min (budget + 1) (rest.length + 1)
            omega

theorem run_pending_length (environment : BooleanEnv State n)
    (program : List (Instruction State n)) (stack output : List Bool)
    (budget spent : Nat) (computed : execute environment program stack = some output) :
    (run environment program stack budget spent).1.pending.length = program.length - budget := by
  have programReadout := congrArg List.length
    (path_program environment (run environment program stack budget spent).2)
  rw [List.length_append, run_length environment program stack output budget spent computed] at programReadout
  change program.length = min budget program.length + _ at programReadout
  omega

theorem run_complete_iff (environment : BooleanEnv State n)
    (program : List (Instruction State n)) (stack output : List Bool)
    (budget spent : Nat) (computed : execute environment program stack = some output) :
    (run environment program stack budget spent).1.pending = [] ↔ program.length ≤ budget := by
  rw [← List.length_eq_zero_iff, run_pending_length environment program stack output budget spent computed]
  exact Nat.sub_eq_zero_iff_le

theorem run_ledger (environment : BooleanEnv State n)
    (program : List (Instruction State n)) (stack output : List Bool)
    (budget spent : Nat) (computed : execute environment program stack = some output) :
    (run environment program stack budget spent).1.remaining = budget - program.length ∧
      (run environment program stack budget spent).1.spent = spent + min budget program.length := by
  have ledger := path_funding environment (run environment program stack budget spent).2
  rw [run_length environment program stack output budget spent computed] at ledger
  change budget = _ + min budget program.length ∧ _ = spent + min budget program.length at ledger
  constructor
  · omega
  · exact ledger.2

/-- Any completed actual path, including paths supplied independently of this
controller, reads the result earned by the separate unbounded interpreter. -/
theorem completed_readout (environment : BooleanEnv State n)
    {source target : Configuration State n} (path : Path environment source target)
    (output : List Bool) (computed : execute environment source.pending source.stack = some output)
    (complete : target.pending = []) : target.stack = output := by
  have preserved := path_execution environment path
  rw [computed, complete, execute] at preserved
  exact (Option.some.inj preserved).symm

theorem compiled_run_complete (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget spent : Nat) :
    (run environment (compile presentation formula admitted state) stack budget spent).1.pending = [] ↔
      (inspect presentation formula admitted environment state).2 ≤ budget := by
  rw [run_complete_iff environment _ stack _ budget spent
    (execute_compiled presentation formula admitted environment state stack)]
  rw [compiled_length]

theorem compiled_completed_readout (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget spent : Nat)
    {target : Configuration State n}
    (path : Path environment ⟨compile presentation formula admitted state, stack, budget, spent⟩ target)
    (complete : target.pending = []) :
    target.stack = (inspect presentation formula admitted environment state).1 :: stack :=
  completed_readout environment path _
    (execute_compiled presentation formula admitted environment state stack) complete

end Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded
