import Mettapedia.Logic.HMLStackComparison
import Mettapedia.GSLT.Causality.OccurrenceHistory

/-!
# Funded modal stack instructions and retained occurrence prefixes

An instruction consumes one purse cell and advances the actual pending program.
Its event retains the instruction and its successful stack readout. The rewrite
system and its complete event presentation use the existing occurrence-history
framework. Every prefix retains its ordered instruction occurrences.

The accounting unit is one successful instruction in this machine. Compilation,
primitive environment implementations and physical elapsed time require their
own accounts; they are not identified with this unit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded

open Inspection
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe u

structure Configuration (State : Type u) (n : Nat) where
  pending : List (Instruction State n)
  stack : List Bool
  remaining : Nat
  spent : Nat
  deriving DecidableEq

variable {State : Type u} {n : Nat}

structure Tick (environment : BooleanEnv State n) (instruction : Instruction State n)
    (source target : Configuration State n) : Type where
  pending : source.pending = instruction :: target.pending
  executed : instruction.execute environment source.stack = some target.stack
  remaining : source.remaining = target.remaining + 1
  spent : target.spent = source.spent + 1

abbrev theory (environment : BooleanEnv State n) : GSLT where
  Term := Configuration State n
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := Nonempty (Σ instruction, Tick environment instruction source target)
  rewrites_resp_left := by
    intro source other target same edge
    cases same
    exact ⟨target, edge, rfl⟩
  rewrites_resp_right := by
    intro source target other edge same
    cases same
    exact edge

abbrev presentation (environment : BooleanEnv State n) : InteractionPresentation (theory environment) where
  Site := Instruction State n
  Event := Tick environment
  sound event := ⟨⟨_, event⟩⟩

theorem presentation_complete (environment : BooleanEnv State n) :
    (presentation environment).Complete := fun edge => edge

abbrev Path (environment : BooleanEnv State n) := OccurrencePath (presentation environment)

/-- The ordered occurrence list is an actual consumed prefix of the source
program. Equal instructions at different positions remain two occurrences. -/
theorem path_program (environment : BooleanEnv State n)
    {source target : (theory environment).Term} (path : Path environment source target) :
    source.pending = path.sites ++ target.pending := by
  induction path with
  | refl => rfl
  | cons event rest inductionHypothesis =>
      rw [OccurrencePath.sites_cons, List.cons_append, ← inductionHypothesis]
      exact event.evidence.pending

theorem path_funding (environment : BooleanEnv State n)
    {source target : (theory environment).Term} (path : Path environment source target) :
    source.remaining = target.remaining + path.sites.length ∧
      target.spent = source.spent + path.sites.length := by
  induction path with
  | refl => simp only [OccurrencePath.sites_refl, List.length_nil, Nat.add_zero, and_self]
  | cons event rest inductionHypothesis =>
      have remaining := event.evidence.remaining
      have spent := event.evidence.spent
      simp only [OccurrencePath.sites_cons, List.length_cons]
      omega

theorem path_ledger (environment : BooleanEnv State n)
    {source target : (theory environment).Term} (path : Path environment source target) :
    source.remaining + source.spent = target.remaining + target.spent := by
  have account := path_funding environment path
  omega

theorem path_affordable (environment : BooleanEnv State n)
    {source target : (theory environment).Term} (path : Path environment source target) :
    path.sites.length ≤ source.remaining := by
  have account := path_funding environment path
  omega

theorem path_program_bound (environment : BooleanEnv State n)
    {source target : (theory environment).Term} (path : Path environment source target) :
    path.sites.length ≤ source.pending.length := by
  have program := congrArg List.length (path_program environment path)
  rw [List.length_append] at program
  omega

theorem path_execution (environment : BooleanEnv State n)
    {source target : (theory environment).Term} (path : Path environment source target) :
    execute environment source.pending source.stack =
      execute environment target.pending target.stack := by
  induction path with
  | refl => rfl
  | cons event rest inductionHypothesis =>
      rw [event.evidence.pending, execute, event.evidence.executed, Option.bind_some]
      exact inductionHypothesis

/-- Completing any actual path requires funding all source instructions,
independently of the controller that selected that path. -/
theorem completion_requires_funding (environment : BooleanEnv State n)
    {source target : (theory environment).Term} (path : Path environment source target)
    (complete : target.pending = []) : source.pending.length ≤ source.remaining := by
  have program := path_program environment path
  rw [complete, List.append_nil] at program
  rw [program]
  exact path_affordable environment path

def instructionAccount (environment : BooleanEnv State n) :
    OccurrenceValuation (presentation environment) Nat where
  grade _ := 1

theorem instructionAccount_readout (environment : BooleanEnv State n)
    {source target : (theory environment).Term} (path : Path environment source target) :
    (instructionAccount environment).onPath path = path.sites.length := by
  induction path with
  | refl => rfl
  | cons event rest inductionHypothesis =>
      change 1 + (instructionAccount environment).onPath rest = rest.sites.length + 1
      rw [inductionHypothesis]
      omega

end Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded
