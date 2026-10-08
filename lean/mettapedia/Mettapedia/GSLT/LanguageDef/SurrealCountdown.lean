import Mettapedia.GSLT.Causality.SurrealProgramContracts
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# An authored recursive program with rank and exact cost contracts

The equation program is `countdown Z = Done` and
`countdown (S n) = countdown n`. Root-call receipts are constructed from its
actual ordered equation selector and captured environment. The source-step
relation is characterized exactly, and all natural inputs return `Done` in
the existing evaluator.

One half-unit is charged for each selected equation. Every complete retained
path from input `n` costs `(n + 1)` half-units, independently of the numerical
representation. This charge is for equation firings, not evaluator overhead.
The ordinal rank proves termination; the budget proof retains the receipts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.SurrealCountdown

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.SurrealCostValuation
open Mettapedia.GSLT.Causality.SurrealProgramContracts
open Mettapedia.SetTheory.SignExpansion.Surreal

def number : Nat → Term
  | 0 => .sym "Z"
  | n + 1 => .expr [.sym "S", number n]

theorem number_injective : Function.Injective number := by
  intro n
  induction n with
  | zero =>
      intro m same
      cases m <;> simp_all [number]
  | succ n ih =>
      intro m same
      cases m with
      | zero => simp [number] at same
      | succ m =>
          simp only [number, Term.expr.injEq, List.cons.injEq, and_true, true_and] at same
          exact congrArg Nat.succ (ih same)

def finish : Equation := ⟨"finish", "countdown", [.sym "Z"], .sym "Done"⟩

def recurse : Equation :=
  ⟨"recurse", "countdown", [.expr [.sym "S", .var "n"]],
    .expr [.sym "countdown", .var "n"]⟩

def program : Program := [finish, recurse]

def host : Host := ⟨fun _ _ => .unhandled⟩

theorem selected_zero : program.select "countdown" [number 0] = some (finish, []) := rfl

theorem selected_succ (n : Nat) :
    program.select "countdown" [number (n + 1)] = some (recurse, [("n", number n)]) := rfl

theorem program_returns (n : Nat) : Applies program host "countdown" [number n] (.sym "Done") := by
  induction n with
  | zero => exact ⟨1, rfl⟩
  | succ n ih =>
      refine Applies.equation (equation := recurse) (environment := [("n", number n)])
        (by rfl) (selected_succ n) ?_
      exact Evaluates.call (by simp [Special])
        (.cons (.variable (by rfl)) .nil) ih

theorem result_exact (n : Nat) (value : Term) :
    Applies program host "countdown" [number n] value ↔ value = .sym "Done" :=
  ⟨fun run => run.deterministic (program_returns n), fun same => same ▸ program_returns n⟩

abbrev State := Option Nat

def followsBody (environment : Env) (body : Term) : State → Prop
  | none => body = .sym "Done"
  | some n => body = recurse.body ∧ environment.lookup "n" = some (number n)

def SourceStep : State → State → Prop
  | none, _ => False
  | some n, after => ∃ equation environment,
      program.select "countdown" [number n] = some (equation, environment) ∧
        followsBody environment equation.body after

def countdownStep : State → State → Prop
  | some 0, none => True
  | some (n + 1), some m => n = m
  | _, _ => False

/-- The abstract countdown transitions are derived from the source equations,
including the terminal case and the captured recursive argument. -/
theorem source_step_iff (before after : State) : SourceStep before after ↔ countdownStep before after := by
  cases before with
  | none => exact Iff.rfl
  | some n =>
      cases n with
      | zero =>
          cases after with
          | none =>
              exact ⟨fun _ => True.intro, fun _ => ⟨finish, [], selected_zero, rfl⟩⟩
          | some m =>
              constructor
              · rintro ⟨equation, environment, selected, follows⟩
                rw [selected_zero, Option.some.injEq, Prod.mk.injEq] at selected
                obtain ⟨rfl, rfl⟩ := selected
                have impossible : (Term.sym "Done") = .expr [.sym "countdown", .var "n"] :=
                  follows.1
                cases impossible
              · exact False.elim
      | succ n =>
          cases after with
          | none =>
              constructor
              · rintro ⟨equation, environment, selected, follows⟩
                rw [selected_succ, Option.some.injEq, Prod.mk.injEq] at selected
                obtain ⟨rfl, rfl⟩ := selected
                have impossible : (Term.expr [.sym "countdown", .var "n"]) = .sym "Done" :=
                  follows
                cases impossible
              · exact False.elim
          | some m =>
              constructor
              · rintro ⟨equation, environment, selected, follows⟩
                rw [selected_succ, Option.some.injEq, Prod.mk.injEq] at selected
                obtain ⟨rfl, rfl⟩ := selected
                have same : some (number n) = some (number m) := follows.2
                exact number_injective (Option.some.inj same)
              · intro same
                cases same
                exact ⟨recurse, [("n", number n)], selected_succ n, rfl, rfl⟩

abbrev theory : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SourceStep
  rewrites_resp_left := by
    intro source other target same step
    subst other
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target other step same
    subst other
    exact step

/-- The complete authored equation and captured environment are retained. -/
structure RootReceipt (input : Nat) (after : State) where
  equation : Equation
  environment : Env
  selected : program.select "countdown" [number input] = some (equation, environment)
  destination : followsBody environment equation.body after

def Event (site : String) : State → State → Type
  | none, _ => Empty
  | some n, after => {receipt : RootReceipt n after // receipt.equation.name = site}

def presentation : InteractionPresentation theory where
  Site := String
  Event := Event
  sound := by
    intro site before after event
    cases before with
    | none => exact event.elim
    | some n =>
        exact ⟨event.1.equation, event.1.environment, event.1.selected, event.1.destination⟩

theorem presentation_complete : presentation.Complete := by
  intro before after step
  cases before with
  | none => exact step.elim
  | some n =>
      obtain ⟨equation, environment, selected, destination⟩ := step
      exact ⟨equation.name, ⟨⟨equation, environment, selected, destination⟩, rfl⟩⟩

def remaining : State → Nat
  | none => 0
  | some n => n + 1

theorem remaining_step {before after : State} (step : theory.Step before after) :
    remaining before = remaining after + 1 := by
  have source : SourceStep before after := step
  rw [source_step_iff] at source
  cases before with
  | none => cases source
  | some n =>
      cases n with
      | zero => cases after <;> simp_all [countdownStep, remaining]
      | succ n => cases after <;> simp_all [countdownStep, remaining]

def ordinalRank (state : State) : Ordinal.{0} := remaining state

theorem ordinal_rank_decreases : Ranks theory ordinalRank := by
  intro before after step
  have fewer : remaining after < remaining before := by rw [remaining_step step]; omega
  change (remaining after : Ordinal.{0}) < (remaining before : Ordinal.{0})
  exact_mod_cast fewer

theorem no_infinite_source_run :
    ¬ ∃ run : Nat → State, ∀ n, theory.Step (run n) (run (n + 1)) := by
  apply no_infinite_of_wellFounded theory
  exact Subrelation.wf (fun {_ _} step => by
    change remaining _ < remaining _
    rw [remaining_step step]
    exact Nat.lt_succ_self _) (InvImage.wf remaining Nat.lt_wfRel.wf)

theorem surreal_rank_decreases {before after : State} (step : theory.Step before after) :
    ofOrdinal (ordinalRank after) < ofOrdinal (ordinalRank before) :=
  (ranks_iff_surreal theory ordinalRank).mp ordinal_rank_decreases before after step

def half : Mettapedia.Algebra.Order.Dyadic := Mettapedia.Algebra.Order.Dyadic.ofPair 1 1

def charge : OccurrenceValuation presentation Mettapedia.Algebra.Order.Dyadic := ⟨fun _ => half⟩

theorem cost_potential {before after : State} (path : OccurrencePath presentation before after) :
    charge.onPath path + remaining after • half = remaining before • half := by
  apply event_potential_onPath charge (fun state => remaining state • half) _ path
  intro source target occurrence
  change half + remaining target • half = remaining source • half
  rw [remaining_step occurrence.step, add_nsmul, one_nsmul]
  exact add_comm _ _

theorem complete_cost (n : Nat) (path : OccurrencePath presentation (some n) none) :
    charge.onPath path = (n + 1) • half := by
  simpa [remaining] using cost_potential path

def finishOccurrence : Occurrence presentation (some 0) none :=
  ⟨"finish", ⟨⟨finish, [], selected_zero, rfl⟩, rfl⟩⟩

def recurseOccurrence (n : Nat) : Occurrence presentation (some (n + 1)) (some n) :=
  ⟨"recurse", ⟨⟨recurse, [("n", number n)], selected_succ n, ⟨rfl, rfl⟩⟩, rfl⟩⟩

def run : (n : Nat) → OccurrencePath presentation (some n) none
  | 0 => .cons finishOccurrence (.refl (P := presentation) none)
  | n + 1 => .cons (recurseOccurrence n) (run n)

theorem complete_surreal_cost (n : Nat) (path : OccurrencePath presentation (some n) none) :
    (read charge).onPath path = toSurreal ((n + 1) • half) := by
  rw [read_onPath, complete_cost]

theorem all_runs_within_budget (n : Nat) (budget : Mettapedia.Algebra.Order.Dyadic) :
    (∀ path : OccurrencePath presentation (some n) none,
      (read charge).onPath path ≤ toSurreal budget) ↔ (n + 1) • half ≤ budget := by
  constructor
  · intro fits
    simpa only [budget_iff, complete_cost] using fits (run n)
  · intro enough path
    rw [budget_iff, complete_cost]
    exact enough

theorem input_three_budget :
    (read charge).onPath (run 3) ≤ toSurreal 2 := by
  rw [budget_iff, complete_cost]
  decide +kernel

theorem input_three_refuses_small_budget :
    ¬ (read charge).onPath (run 3) ≤ toSurreal 1 := by
  rw [budget_iff, complete_cost]
  decide +kernel

theorem input_zero_budget :
    (read charge).onPath (run 0) ≤ toSurreal 1 := by
  rw [budget_iff, complete_cost]
  decide +kernel

/-- The actual authored evaluator returns the same answer for different
amounts of work. A result-only predicate cannot recover this budget contract;
the input or retained execution must remain available to its consumer. -/
theorem budget_does_not_descend_to_result :
    ¬ ∃ classify : Term → Prop, ∀ n value,
      Applies program host "countdown" [number n] value →
        (classify value ↔ (read charge).onPath (run n) ≤ toSurreal 1) := by
  rintro ⟨classify, correct⟩
  have small := (correct 0 (.sym "Done") (program_returns 0)).mpr input_zero_budget
  exact input_three_refuses_small_budget
    ((correct 3 (.sym "Done") (program_returns 3)).mp small)

end Mettapedia.GSLT.LanguageDef.SurrealCountdown
