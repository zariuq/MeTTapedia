import Mettapedia.Logic.HMLPrepaidProgram
import Mettapedia.Logic.HMLResidualEvidence

/-!
# Current prepayment evidence and progress of every actual prefix

A successful occurrence removes precisely the first supplied instruction
judgment. Its remaining derivation follows every actual occurrence path,
with identity and composition laws. An accepted unfinished configuration has
a real funded successor. Thus every maximal accepted prefix finishes, reads
its complete supplied output, and has the exact instruction account.

The theorem is conditional on an independently generated prepayment
derivation and maximality. A controller may interrupt early; no theorem here
identifies silence with a Boolean answer or supplies external purse authority.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded

open Inspection
open _root_.CategoryTheory
open Mettapedia.GSLT.Causality.OccurrenceHistory

universe u v

variable {State : Type u} {Action : Type v} {n : Nat}

abbrev Prepayment (environment : BooleanEnv State n) (configuration : Configuration State n)
    (output : List Bool) :=
  PrepaidProgram environment configuration.pending configuration.stack output configuration.remaining

/-- Advance the supplied derivation itself: after matching the actual
instruction readout, its original complete suffix is retained. -/
def advancePrepayment (environment : BooleanEnv State n)
    {opcode : Instruction State n} {source target : Configuration State n} {output : List Bool}
    (event : Tick environment opcode source target) (accepted : Prepayment environment source output) :
    Prepayment environment target output := by
  change PrepaidProgram environment source.pending source.stack output source.remaining at accepted
  rw [event.pending, event.remaining] at accepted
  cases accepted with
  | instruction judgment after =>
      have same := Option.some.inj ((judgment.sound environment).symm.trans event.executed)
      cases same
      exact after

def transportPrepayment (environment : BooleanEnv State n)
    {source target : Configuration State n} {output : List Bool}
    (path : Path environment source target) (accepted : Prepayment environment source output) :
    Prepayment environment target output :=
  match path with
  | .refl _ => accepted
  | .cons event rest =>
      transportPrepayment environment rest (advancePrepayment environment event.evidence accepted)
termination_by structural path

theorem transportPrepayment_identity (environment : BooleanEnv State n)
    (source : Configuration State n) (output : List Bool) (accepted : Prepayment environment source output) :
    transportPrepayment environment (.refl source) accepted = accepted := rfl

theorem transportPrepayment_composition (environment : BooleanEnv State n)
    {source middle target : (theory environment).Term} {output : List Bool}
    (first : Path environment source middle) (second : Path environment middle target)
    (accepted : Prepayment environment source output) :
    transportPrepayment environment (OccurrencePath.append first second) accepted =
      transportPrepayment environment second (transportPrepayment environment first accepted) := by
  revert second accepted
  induction first with
  | refl =>
      intro second accepted
      rfl
  | cons event rest inductionHypothesis =>
      intro second accepted
      exact inductionHypothesis second (advancePrepayment environment event.evidence accepted)

def prepaymentFunctor (environment : BooleanEnv State n) :
    OccurrenceCat (presentation environment) ⥤ Type u where
  obj configuration := Σ output : List Bool, Prepayment environment configuration output
  map path := TypeCat.ofHom (fun accepted =>
    ⟨accepted.1, transportPrepayment environment path accepted.2⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro accepted
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro accepted
    exact congrArg (fun proof => (⟨accepted.1, proof⟩ : Σ output, Prepayment environment _ output))
      (transportPrepayment_composition environment first second accepted.2)

def Maximal (environment : BooleanEnv State n) (configuration : Configuration State n) : Prop :=
  ∀ target, ¬ (theory environment).Step configuration target

theorem prepaid_progress (environment : BooleanEnv State n) (source : Configuration State n)
    (output : List Bool) (accepted : Prepayment environment source output)
    (unfinished : source.pending ≠ []) :
    ∃ opcode target, Nonempty (Tick environment opcode source target) ∧
      Nonempty (Prepayment environment target output) := by
  cases source with
  | mk program stack budget spent =>
      cases accepted with
      | finish => exact False.elim (unfinished rfl)
      | @instruction opcode rest stack middle output remaining judgment after =>
          exact ⟨opcode, ⟨rest, middle, remaining, spent + 1⟩,
            ⟨⟨rfl, judgment.sound environment, rfl, rfl⟩⟩, ⟨after⟩⟩

theorem prepaid_maximal_complete (environment : BooleanEnv State n)
    (source : Configuration State n) (output : List Bool)
    (accepted : Prepayment environment source output) (maximal : Maximal environment source) :
    source.pending = [] := by
  by_contra unfinished
  obtain ⟨opcode, target, ⟨event⟩, _⟩ := prepaid_progress environment source output accepted unfinished
  exact maximal target ⟨⟨opcode, event⟩⟩

theorem every_maximal_prepaid_prefix_finishes (environment : BooleanEnv State n)
    {source target : Configuration State n} (output : List Bool)
    (accepted : Prepayment environment source output) (path : Path environment source target)
    (maximal : Maximal environment target) :
    target.pending = [] ∧ target.stack = output ∧
      target.spent = source.spent + source.pending.length := by
  have current := transportPrepayment environment path accepted
  have complete := prepaid_maximal_complete environment target output current maximal
  have readout := completed_readout environment path output (accepted.computed environment) complete
  have program := congrArg List.length (path_program environment path)
  rw [complete, List.append_nil] at program
  have spent := (path_funding environment path).2
  rw [← program] at spent
  exact ⟨complete, readout, spent⟩

theorem Prefix.maximal_prepaid_answer (presentation : SuccessorPresentation State Action)
    (formula : Formula Action n) (admitted : formula.isHML = true)
    (environment : BooleanEnv State n) (state : State) (stack : List Bool) (budget : Nat)
    (receipt : Prefix presentation formula admitted environment state stack budget)
    (affordable : (inspect presentation formula admitted environment state).2 ≤ budget)
    (maximal : Maximal environment receipt.endpoint) :
    publicAnswer receipt.endpoint = some (inspect presentation formula admitted environment state).1 ∧
      ModalCertificate presentation formula environment state
        (Mettapedia.GSLT.Causality.ComplementaryAssay.verdictOf
          (inspect presentation formula admitted environment state).1) ∧
      receipt.endpoint.spent = (inspect presentation formula admitted environment state).2 := by
  have accepted := compiledPrepayment presentation formula admitted environment state stack budget affordable
  obtain ⟨complete, output, spent⟩ := every_maximal_prepaid_prefix_finishes environment _ accepted receipt.path maximal
  have reported := publicAnswer_completed receipt.endpoint complete _ stack output
  refine ⟨reported, inspected_certificate presentation formula admitted environment state, ?_⟩
  change receipt.endpoint.spent = 0 + (compile presentation formula admitted state).length at spent
  simpa only [Nat.zero_add, compiled_length presentation formula admitted environment state] using spent

end Mettapedia.Logic.ModalMuCalculus.StackInspection.Funded
