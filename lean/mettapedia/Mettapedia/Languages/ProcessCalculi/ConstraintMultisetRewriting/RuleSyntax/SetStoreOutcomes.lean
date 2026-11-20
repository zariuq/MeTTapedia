import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreDisciplines

/-!
# Least outcomes and termination for the positive set-store disciplines

The outcome observer is a completed terminal set. For `unique`, determinacy
is required at every reachable state, including the final one. Finite input
and a finite program do not replace the separate finite closed-carrier premise.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

def TerminalWith (discipline : Discipline) (timing : SetStore.AskTiming)
    (P : Program (Terms (Term signature))) (rows : Finset (Term signature)) : Prop :=
  ∀ after, ¬ DisciplinedStep discipline timing P rows after

theorem disciplined_run_is_run {discipline : Discipline} {timing : SetStore.AskTiming}
    {seed after : Finset (Term signature)}
    (run : Relation.ReflTransGen (DisciplinedStep discipline timing P) seed after) :
    Relation.ReflTransGen (SetStore.Step timing P) seed after := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (disciplined_is_step step)

theorem discipline_terminal_iff_closed (slots : signature.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (pure : ∀ rule ∈ P, Propagates rule) (rules : List (Rule (Terms (Term signature))))
    (covers : ∀ rule ∈ P, rule ∈ rules) (uniquePolicy : discipline = .unique → Determinate (P := P) rows) :
    TerminalWith discipline timing P rows ↔ SetStoreClosure.Closed (consequence (P := P)) rows := by
  constructor
  · intro terminal
    by_contra notClosed
    obtain ⟨after, step⟩ := discipline_progress slots discipline timing rows ground pure rules covers uniquePolicy notClosed
    exact terminal after step
  · intro closed after step
    exact closed_ground_terminal pure rows ground closed after (disciplined_is_step step)

theorem discipline_terminal_eq_closure (slots : signature.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    {seed after : Finset (Term signature)} (ground : GroundRows seed)
    (run : Relation.ReflTransGen (DisciplinedStep discipline timing P) seed after)
    (terminal : TerminalWith discipline timing P after)
    (uniquePolicy : discipline = .unique → Determinate (P := P) after) :
    (after : Set (Term signature)) = SetStoreClosure.closure (consequence (P := P)) seed := by
  have raw := disciplined_run_is_run run
  have afterGround := actual_reachable_ground timing pure ground raw
  have closed := (discipline_terminal_iff_closed slots discipline timing after afterGround pure rules covers uniquePolicy).mp terminal
  exact actual_terminal_eq_closure timing pure ground raw (closed_ground_terminal pure after afterGround closed)

theorem discipline_no_infinite_run (discipline : Discipline) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (carrier : Finset (Term signature))
    (closed : SetStoreClosure.Closed (consequence (P := P)) carrier)
    (run : ℕ → Finset (Term signature)) (inside : run 0 ⊆ carrier) (ground : GroundRows (run 0)) :
    ¬ ∀ n, DisciplinedStep discipline timing P (run n) (run (n + 1)) := by
  intro steps
  exact actual_no_infinite_run timing pure carrier closed run inside ground (fun n => disciplined_is_step (steps n))

theorem discipline_exists_terminal (discipline : Discipline) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (carrier seed : Finset (Term signature))
    (closed : SetStoreClosure.Closed (consequence (P := P)) carrier) (inside : seed ⊆ carrier)
    (ground : GroundRows seed) :
    ∃ after, Relation.ReflTransGen (DisciplinedStep discipline timing P) seed after ∧
      TerminalWith discipline timing P after := by
  classical
  have closure_eq : SetStoreClosure.closure (consequence (P := P)) carrier = (carrier : Set (Term signature)) := by
    apply Set.Subset.antisymm
    · exact (Mettapedia.GSLT.OpenEnded.ChaoticIteration.isLeast_target
        (fun m => SetStoreClosure.action (consequence m)) (carrier : Set (Term signature))).2
          ⟨Set.Subset.refl _, (SetStoreClosure.closed_action_iff _ _).mp closed⟩
    · exact SetStoreClosure.seed_subset_closure _ _
  have find : ∀ n (rows : Finset (Term signature)), carrier.card - rows.card = n → rows ⊆ carrier →
      GroundRows rows → ∃ after,
        Relation.ReflTransGen (DisciplinedStep discipline timing P) rows after ∧ TerminalWith discipline timing P after := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro rows measure subset rowsGround
      by_cases terminal : TerminalWith discipline timing P rows
      · exact ⟨rows, .refl, terminal⟩
      · obtain ⟨after, step⟩ : ∃ after, DisciplinedStep discipline timing P rows after := by
          simpa only [TerminalWith, not_forall, not_not] using terminal
        have raw := disciplined_is_step step
        have nextGround := actual_step_preserves_ground pure rowsGround raw
        have nextSubset := actual_step_le_closure pure carrier rowsGround
          (fun _ member => SetStoreClosure.seed_subset_closure _ _ (subset member)) raw
        rw [closure_eq] at nextSubset
        have card := actual_step_card_lt pure rowsGround raw
        have bound := Finset.card_le_card nextSubset
        have smaller : carrier.card - after.card < n := by omega
        obtain ⟨last, run, terminal⟩ := ih _ smaller after rfl nextSubset nextGround
        exact ⟨last, .head step run, terminal⟩
  exact find _ seed rfl inside ground

/-- All seven declared disciplines have one completed outcome under their stated hypotheses. -/
theorem discipline_has_least_outcome (slots : signature.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (carrier seed : Finset (Term signature)) (closed : SetStoreClosure.Closed (consequence (P := P)) carrier)
    (inside : seed ⊆ carrier) (ground : GroundRows seed)
    (uniquePolicy : discipline = .unique → ∀ rows,
      Relation.ReflTransGen (DisciplinedStep discipline timing P) seed rows → Determinate (P := P) rows) :
    ∃ after, Relation.ReflTransGen (DisciplinedStep discipline timing P) seed after ∧
      TerminalWith discipline timing P after ∧
      (after : Set (Term signature)) = SetStoreClosure.closure (consequence (P := P)) seed ∧
      ∀ other, Relation.ReflTransGen (DisciplinedStep discipline timing P) seed other →
        TerminalWith discipline timing P other → other = after := by
  obtain ⟨after, run, terminal⟩ := discipline_exists_terminal discipline timing pure carrier seed closed inside ground
  have result := discipline_terminal_eq_closure slots discipline timing pure rules covers ground run terminal
    (fun unique => uniquePolicy unique after run)
  refine ⟨after, run, terminal, result, ?_⟩
  intro other otherRun otherTerminal
  have otherResult := discipline_terminal_eq_closure slots discipline timing pure rules covers ground otherRun otherTerminal
    (fun unique => uniquePolicy unique other otherRun)
  apply Finset.coe_injective
  exact otherResult.trans result.symm

/-- Cross-discipline equality is equality of completed outcomes, not equality of executions. -/
theorem completed_outcomes_agree (slots : signature.vars ≃ ℕ) (first second : Discipline)
    (firstTiming secondTiming : SetStore.AskTiming) (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    {seed left right : Finset (Term signature)} (ground : GroundRows seed)
    (leftRun : Relation.ReflTransGen (DisciplinedStep first firstTiming P) seed left)
    (rightRun : Relation.ReflTransGen (DisciplinedStep second secondTiming P) seed right)
    (leftEnd : TerminalWith first firstTiming P left) (rightEnd : TerminalWith second secondTiming P right)
    (leftUnique : first = .unique → Determinate (P := P) left)
    (rightUnique : second = .unique → Determinate (P := P) right) : left = right := by
  apply Finset.coe_injective
  exact (discipline_terminal_eq_closure slots first firstTiming pure rules covers ground leftRun leftEnd leftUnique).trans
    (discipline_terminal_eq_closure slots second secondTiming pure rules covers ground rightRun rightEnd rightUnique).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
