import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreAskTiming

/-!
# Least completed outcomes with matches selected at the ask timing

The result concerns completed row sets. It requires ground initial rows,
range-restricted positive propagation and, for existence and termination, a
finite closed universe. Unique additionally requires match determinacy.
The theorem does not identify executions, budgets or implementation costs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms)

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

def QuantifiedTerminal (discipline : Discipline) (timing : SetStore.AskTiming)
    (P : Program (Terms (Term signature))) (rows : Finset (Term signature)) : Prop :=
  ∀ after, ¬ QuantifiedStep discipline timing P rows after

theorem quantified_run_is_run {discipline : Discipline} {timing : SetStore.AskTiming}
    {seed after : Finset (Term signature)}
    (run : Relation.ReflTransGen (QuantifiedStep discipline timing P) seed after) :
    Relation.ReflTransGen (SetStore.Step timing P) seed after := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (quantified_is_step step)

theorem quantified_run_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = [])
    {discipline : Discipline} {timing : SetStore.AskTiming}
    {seed after : Finset (Term signature)} :
    Relation.ReflTransGen (QuantifiedStep discipline timing P) seed after ↔
      Relation.ReflTransGen (DisciplinedStep discipline timing P) seed after := by
  constructor
  · intro run
    induction run with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih ((quantified_iff_of_no_tells silent).mp step)
  · intro run
    induction run with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih ((quantified_iff_of_no_tells silent).mpr step)

theorem quantified_terminal_iff_of_no_tells (silent : ∀ r ∈ P, r.body.tell = [])
    {discipline : Discipline} {timing : SetStore.AskTiming} {rows : Finset (Term signature)} :
    QuantifiedTerminal discipline timing P rows ↔ TerminalWith discipline timing P rows := by
  simp only [QuantifiedTerminal, TerminalWith, quantified_iff_of_no_tells silent]

theorem quantified_progress (slots : signature.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ r ∈ P, Propagates r) (rules : List (Rule (Terms (Term signature))))
    (covers : ∀ rule ∈ P, rule ∈ rules)
    (uniquePolicy : discipline = .unique → Determinate (P := P) rows)
    (notClosed : ¬ SetStoreClosure.Closed (consequence (P := P)) rows) :
    ∃ after, QuantifiedStep discipline timing P rows after := by
  obtain ⟨after, step⟩ := discipline_progress slots discipline timing rows ground pure rules covers uniquePolicy notClosed
  exact ⟨after, (quantified_iff_of_no_tells (fun r inside => (pure r inside).noTell)).mpr step⟩

theorem quantified_terminal_iff_closed (slots : signature.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ r ∈ P, Propagates r) (rules : List (Rule (Terms (Term signature))))
    (covers : ∀ rule ∈ P, rule ∈ rules)
    (uniquePolicy : discipline = .unique → Determinate (P := P) rows) :
    QuantifiedTerminal discipline timing P rows ↔ SetStoreClosure.Closed (consequence (P := P)) rows :=
  (quantified_terminal_iff_of_no_tells (fun r inside => (pure r inside).noTell)).trans
    (discipline_terminal_iff_closed slots discipline timing rows ground pure rules covers uniquePolicy)

theorem quantified_terminal_eq_closure (slots : signature.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (pure : ∀ r ∈ P, Propagates r)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    {seed after : Finset (Term signature)} (ground : GroundRows seed)
    (run : Relation.ReflTransGen (QuantifiedStep discipline timing P) seed after)
    (terminal : QuantifiedTerminal discipline timing P after)
    (uniquePolicy : discipline = .unique → Determinate (P := P) after) :
    (after : Set (Term signature)) = SetStoreClosure.closure (consequence (P := P)) seed := by
  have silent := fun r inside => (pure r inside).noTell
  exact discipline_terminal_eq_closure slots discipline timing pure rules covers ground
    ((quantified_run_iff_of_no_tells silent).mp run)
    ((quantified_terminal_iff_of_no_tells silent).mp terminal) uniquePolicy

theorem quantified_no_infinite_run (discipline : Discipline) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (carrier : Finset (Term signature))
    (closed : SetStoreClosure.Closed (consequence (P := P)) carrier)
    (run : ℕ → Finset (Term signature)) (inside : run 0 ⊆ carrier) (ground : GroundRows (run 0)) :
    ¬ ∀ n, QuantifiedStep discipline timing P (run n) (run (n + 1)) := by
  intro steps
  exact actual_no_infinite_run timing pure carrier closed run inside ground
    (fun n => quantified_is_step (steps n))

theorem quantified_exists_terminal (discipline : Discipline) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (carrier seed : Finset (Term signature))
    (closed : SetStoreClosure.Closed (consequence (P := P)) carrier) (inside : seed ⊆ carrier)
    (ground : GroundRows seed) :
    ∃ after, Relation.ReflTransGen (QuantifiedStep discipline timing P) seed after ∧
      QuantifiedTerminal discipline timing P after := by
  have silent := fun r inside => (pure r inside).noTell
  obtain ⟨after, run, terminal⟩ := discipline_exists_terminal discipline timing pure carrier seed closed inside ground
  exact ⟨after, (quantified_run_iff_of_no_tells silent).mpr run,
    (quantified_terminal_iff_of_no_tells silent).mpr terminal⟩

theorem quantified_has_least_outcome (slots : signature.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (carrier seed : Finset (Term signature)) (closed : SetStoreClosure.Closed (consequence (P := P)) carrier)
    (inside : seed ⊆ carrier) (ground : GroundRows seed)
    (uniquePolicy : discipline = .unique → ∀ rows,
      Relation.ReflTransGen (QuantifiedStep discipline timing P) seed rows → Determinate (P := P) rows) :
    ∃ after, Relation.ReflTransGen (QuantifiedStep discipline timing P) seed after ∧
      QuantifiedTerminal discipline timing P after ∧
      (after : Set (Term signature)) = SetStoreClosure.closure (consequence (P := P)) seed ∧
      ∀ other, Relation.ReflTransGen (QuantifiedStep discipline timing P) seed other →
        QuantifiedTerminal discipline timing P other → other = after := by
  have silent := fun r inside => (pure r inside).noTell
  obtain ⟨after, run, terminal, least, only⟩ := discipline_has_least_outcome slots discipline timing pure rules covers
    carrier seed closed inside ground (fun unique rows run => uniquePolicy unique rows
      ((quantified_run_iff_of_no_tells silent).mpr run))
  refine ⟨after, (quantified_run_iff_of_no_tells silent).mpr run,
    (quantified_terminal_iff_of_no_tells silent).mpr terminal, least, ?_⟩
  intro other otherRun otherTerminal
  exact only other ((quantified_run_iff_of_no_tells silent).mp otherRun)
    ((quantified_terminal_iff_of_no_tells silent).mp otherTerminal)

theorem quantified_completed_outcomes_agree (slots : signature.vars ≃ ℕ) (first second : Discipline)
    (firstTiming secondTiming : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    {seed left right : Finset (Term signature)} (ground : GroundRows seed)
    (leftRun : Relation.ReflTransGen (QuantifiedStep first firstTiming P) seed left)
    (rightRun : Relation.ReflTransGen (QuantifiedStep second secondTiming P) seed right)
    (leftEnd : QuantifiedTerminal first firstTiming P left)
    (rightEnd : QuantifiedTerminal second secondTiming P right)
    (leftUnique : first = .unique → Determinate (P := P) left)
    (rightUnique : second = .unique → Determinate (P := P) right) : left = right := by
  apply Finset.coe_injective
  exact (quantified_terminal_eq_closure slots first firstTiming pure rules covers ground leftRun leftEnd leftUnique).trans
    (quantified_terminal_eq_closure slots second secondTiming pure rules covers ground rightRun rightEnd rightUnique).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
