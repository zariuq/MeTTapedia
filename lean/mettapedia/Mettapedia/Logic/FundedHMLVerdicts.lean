import Mettapedia.Logic.FundedHMLExecution
import Mettapedia.GSLT.Causality.ComplementaryAssay

/-!
# Completed instruction readouts and modal certificates

The public readout examines the actual pending program and result stack. An
unfinished program has no verdict, even when its intermediate stack already
contains a Boolean. The separate compiler and execution comparisons earn
sound complementary certificates and the exact funding condition.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded

open Inspection
open Mettapedia.GSLT.Causality.ComplementaryAssay

universe u v

variable {State : Type u} {Action : Type v} {n : Nat}

def publicAnswer (configuration : Configuration State n) : Option Bool :=
  if configuration.pending = [] then configuration.stack.head? else none

theorem publicAnswer_unfinished (configuration : Configuration State n)
    (unfinished : configuration.pending ≠ []) : publicAnswer configuration = none :=
  if_neg unfinished

theorem publicAnswer_completed (configuration : Configuration State n)
    (complete : configuration.pending = []) (answer : Bool) (stack : List Bool)
    (readout : configuration.stack = answer :: stack) : publicAnswer configuration = some answer := by
  simp only [publicAnswer, complete, if_true, readout, List.head?_cons]

structure Prefix (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget : Nat) where
  endpoint : Configuration State n
  path : Path environment ⟨compile presentation formula admitted state, stack, budget, 0⟩ endpoint

variable (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget : Nat)

def attempt : Prefix presentation formula admitted environment state stack budget where
  endpoint := (run environment (compile presentation formula admitted state) stack budget 0).1
  path := (run environment (compile presentation formula admitted state) stack budget 0).2

def ModalCertificate (branch : Verdict) : Prop :=
  match branch with
  | .confirm => satisfies presentation.toLTS environment.toEnv formula state
  | .refute => ¬ satisfies presentation.toLTS environment.toEnv formula state

omit stack budget in
theorem inspected_certificate :
    ModalCertificate presentation formula environment state
      (verdictOf (inspect presentation formula admitted environment state).1) := by
  cases answer : (inspect presentation formula admitted environment state).1 with
  | false => exact (inspect_falsehood presentation formula admitted environment state).1 answer
  | true => exact (inspect_truth presentation formula admitted environment state).1 answer

/-- Every supplied actual reporting receipt has completed the whole compiled
program. Its result agrees with the independent modal inspector. -/
theorem Prefix.answer_sound (receipt : Prefix presentation formula admitted environment state stack budget)
    (answer : Bool) (reported : publicAnswer receipt.endpoint = some answer) :
    receipt.endpoint.pending = [] ∧
      answer = (inspect presentation formula admitted environment state).1 ∧
      ModalCertificate presentation formula environment state (verdictOf answer) := by
  have complete : receipt.endpoint.pending = [] := by
    by_contra unfinished
    rw [publicAnswer_unfinished _ unfinished] at reported
    cases reported
  have result := compiled_completed_readout presentation formula admitted environment state stack budget 0
    receipt.path complete
  have observed := publicAnswer_completed receipt.endpoint complete
    (inspect presentation formula admitted environment state).1 stack result
  have answerSame : answer = (inspect presentation formula admitted environment state).1 :=
    (Option.some.inj (reported.symm.trans observed))
  refine ⟨complete, answerSame, ?_⟩
  rw [answerSame]
  exact inspected_certificate presentation formula admitted environment state

theorem Prefix.reporting_requires_funding
    (receipt : Prefix presentation formula admitted environment state stack budget)
    (answer : Bool) (reported : publicAnswer receipt.endpoint = some answer) :
    (inspect presentation formula admitted environment state).2 ≤ budget := by
  have completed := (receipt.answer_sound presentation formula admitted environment state stack budget
    answer reported).1
  have affordable := completion_requires_funding environment receipt.path completed
  change (compile presentation formula admitted state).length ≤ budget at affordable
  rwa [compiled_length] at affordable

theorem Prefix.reporting_spent
    (receipt : Prefix presentation formula admitted environment state stack budget)
    (answer : Bool) (reported : publicAnswer receipt.endpoint = some answer) :
    receipt.endpoint.spent = (inspect presentation formula admitted environment state).2 := by
  have complete := (receipt.answer_sound presentation formula admitted environment state stack budget
    answer reported).1
  have program := path_program environment receipt.path
  rw [complete, List.append_nil] at program
  have account := (path_funding environment receipt.path).2
  change receipt.endpoint.spent = 0 + receipt.path.sites.length at account
  rw [Nat.zero_add, ← program] at account
  rw [compiled_length presentation formula admitted environment state] at account
  exact account

theorem attempt_answer :
    publicAnswer (attempt presentation formula admitted environment state stack budget).endpoint =
      if (inspect presentation formula admitted environment state).2 ≤ budget then
        some (inspect presentation formula admitted environment state).1 else none := by
  by_cases affordable : (inspect presentation formula admitted environment state).2 ≤ budget
  · have complete := (compiled_run_complete presentation formula admitted environment state stack budget 0).2 affordable
    exact (publicAnswer_completed _ complete _ stack
      (compiled_completed_readout presentation formula admitted environment state stack budget 0
        (attempt presentation formula admitted environment state stack budget).path complete)).trans
          (if_pos affordable).symm
  · have unfinished : (attempt presentation formula admitted environment state stack budget).endpoint.pending ≠ [] := by
      intro complete
      exact affordable ((compiled_run_complete presentation formula admitted environment state stack budget 0).1 complete)
    exact (publicAnswer_unfinished _ unfinished).trans (if_neg affordable).symm

theorem attempt_spent :
    (attempt presentation formula admitted environment state stack budget).endpoint.spent =
      min budget (inspect presentation formula admitted environment state).2 := by
  dsimp only [attempt]
  have ledger := (run_ledger environment (compile presentation formula admitted state) stack
    ((inspect presentation formula admitted environment state).1 :: stack) budget 0
      (execute_compiled presentation formula admitted environment state stack)).2
  rw [compiled_length presentation formula admitted environment state] at ledger
  simpa only [Nat.zero_add] using ledger

theorem Prefix.ledger (receipt : Prefix presentation formula admitted environment state stack budget) :
    budget = receipt.endpoint.remaining + receipt.endpoint.spent := by
  have conserved := path_ledger environment receipt.path
  simpa only [Nat.add_zero] using conserved

end Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded
