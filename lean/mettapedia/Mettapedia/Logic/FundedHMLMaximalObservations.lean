import Mettapedia.Logic.FundedHMLPrepayment

/-!
# Complete observations of independently supplied maximal modal runs

Successful residual calculation and an available cell enable a real
instruction. Every maximal actual prefix therefore stops precisely at
completion or exhaustion. Its public answer and exact spending agree with
the independently executed controller, even when the supplied purse is too
small to admit a whole-program prepayment derivation.

Maximality concerns this declared instruction machine. Arbitrary early
interruption, worker time and external resource authority remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded

open Inspection
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe u v

variable {State : Type u} {Action : Type v} {n : Nat}

theorem computed_progress (environment : BooleanEnv State n)
    (source : Configuration State n) (output : List Bool)
    (successful : execute environment source.pending source.stack = some output)
    (unfinished : source.pending ≠ []) (available : 0 < source.remaining) :
    ∃ opcode target, Nonempty (Tick environment opcode source target) := by
  cases source with
  | mk program stack budget spent =>
      cases program with
      | nil => exact False.elim (unfinished rfl)
      | cons opcode rest =>
          cases checked : opcode.execute environment stack with
          | none =>
              simp only [execute, checked, Option.bind_none] at successful
              cases successful
          | some middle =>
              cases budget with
              | zero =>
                  change 0 < 0 at available
                  omega
              | succ budget =>
                  exact ⟨opcode, ⟨rest, middle, budget, spent + 1⟩,
                    ⟨⟨rfl, checked, rfl, rfl⟩⟩⟩

theorem successful_maximal_stops (environment : BooleanEnv State n)
    (source : Configuration State n) (output : List Bool)
    (successful : execute environment source.pending source.stack = some output)
    (maximal : Maximal environment source) :
    source.pending = [] ∨ source.remaining = 0 := by
  by_cases complete : source.pending = []
  · exact Or.inl complete
  · right
    by_contra nonzero
    obtain ⟨opcode, target, ⟨event⟩⟩ := computed_progress environment source output
      successful complete (by omega)
    exact maximal target ⟨⟨opcode, event⟩⟩

theorem run_maximal (environment : BooleanEnv State n)
    (program : List (Instruction State n)) (stack : List Bool) (budget spent : Nat) :
    Maximal environment (run environment program stack budget spent).1 := by
  induction program generalizing stack budget spent with
  | nil =>
      rintro target ⟨⟨opcode, event⟩⟩
      have pending := event.pending
      change [] = opcode :: target.pending at pending
      cases pending
  | cons opcode rest inductionHypothesis =>
      cases budget with
      | zero =>
          rintro target ⟨⟨nextOpcode, event⟩⟩
          have remaining := event.remaining
          change 0 = target.remaining + 1 at remaining
          omega
      | succ budget =>
          simp only [run]
          split
          · rename_i rejected
            rintro target ⟨⟨nextOpcode, event⟩⟩
            have pending := event.pending
            change opcode :: rest = nextOpcode :: target.pending at pending
            have head := (List.cons.inj pending).1
            subst nextOpcode
            have checked := event.executed
            change opcode.execute environment stack = some target.stack at checked
            rw [rejected] at checked
            cases checked
          · rename_i middle checked
            exact inductionHypothesis middle budget (spent + 1)

theorem every_maximal_successful_spent (environment : BooleanEnv State n)
    {source target : Configuration State n} (output : List Bool)
    (successful : execute environment source.pending source.stack = some output)
    (path : Path environment source target) (maximal : Maximal environment target) :
    target.spent = source.spent + min source.remaining source.pending.length := by
  have current := (path_execution environment path).symm.trans successful
  have program := congrArg List.length (path_program environment path)
  rw [List.length_append] at program
  have funding := path_funding environment path
  have bounded := path_program_bound environment path
  obtain complete | exhausted := successful_maximal_stops environment target output current maximal
  · rw [complete, List.length_nil, Nat.add_zero] at program
    have affordable := completion_requires_funding environment path complete
    rw [Nat.min_eq_right affordable, program]
    exact funding.2
  · rw [exhausted, Nat.zero_add] at funding
    have available : source.remaining ≤ source.pending.length := by
      rw [funding.1]
      exact bounded
    rw [Nat.min_eq_left available, funding.1]
    exact funding.2

theorem Prefix.maximal_answer (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget : Nat)
    (receipt : Prefix presentation formula admitted environment state stack budget)
    (maximal : Maximal environment receipt.endpoint) :
    publicAnswer receipt.endpoint =
      if (inspect presentation formula admitted environment state).2 ≤ budget then
        some (inspect presentation formula admitted environment state).1 else none := by
  by_cases affordable : (inspect presentation formula admitted environment state).2 ≤ budget
  · rw [if_pos affordable]
    exact (receipt.maximal_prepaid_answer presentation formula admitted environment state stack budget
      affordable maximal).1
  · rw [if_neg affordable]
    cases reported : publicAnswer receipt.endpoint with
    | none => rfl
    | some answer =>
        exact False.elim (affordable
          (receipt.reporting_requires_funding presentation formula admitted environment state stack budget
            answer reported))

theorem Prefix.maximal_spent (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget : Nat)
    (receipt : Prefix presentation formula admitted environment state stack budget)
    (maximal : Maximal environment receipt.endpoint) :
    receipt.endpoint.spent = min budget (inspect presentation formula admitted environment state).2 := by
  have exactAccount := every_maximal_successful_spent environment _
    (execute_compiled presentation formula admitted environment state stack) receipt.path maximal
  change receipt.endpoint.spent = 0 + min budget (compile presentation formula admitted state).length at exactAccount
  simpa only [Nat.zero_add, compiled_length presentation formula admitted environment state] using exactAccount

theorem Prefix.maximal_profile (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget : Nat)
    (receipt : Prefix presentation formula admitted environment state stack budget)
    (maximal : Maximal environment receipt.endpoint) :
    (publicAnswer receipt.endpoint, receipt.endpoint.spent) =
      (publicAnswer (attempt presentation formula admitted environment state stack budget).endpoint,
        (attempt presentation formula admitted environment state stack budget).endpoint.spent) :=
  Prod.ext
    ((receipt.maximal_answer presentation formula admitted environment state stack budget maximal).trans
      (attempt_answer presentation formula admitted environment state stack budget).symm)
    ((receipt.maximal_spent presentation formula admitted environment state stack budget maximal).trans
      (attempt_spent presentation formula admitted environment state stack budget).symm)

end Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded
