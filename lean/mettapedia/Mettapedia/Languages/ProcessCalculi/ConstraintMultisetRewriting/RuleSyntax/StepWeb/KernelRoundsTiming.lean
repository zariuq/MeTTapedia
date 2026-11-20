import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRoundsDepth
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreTimedOutcomes

/-!
# The round licences under both explicit ask-quantifier readings

The timed-selection reading and restriction reading are different with tells.
The existing no-tell equivalence transfers stages and round lower bounds in
the propagation fragment. Nothing identifies those readings outside that
fragment, and neither is selected as a default.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds

open Mettapedia.Logic.LP
open OneFrame (Terms)
open SetStoreSyntax

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

def QuantifiedEveryAdvance (timing : SetStore.AskTiming) (P : Program (Terms (Term signature)))
    (rows after : Finset (Term signature)) : Prop :=
  QuantifiedStep .every timing P rows after ∨
    (after = rows ∧ QuantifiedTerminal .every timing P rows)

theorem quantified_advance_iff (pure : ∀ rule ∈ P, Propagates rule)
    {timing : SetStore.AskTiming} {rows after : Finset (Term signature)} :
    QuantifiedEveryAdvance timing P rows after ↔ EveryAdvance timing P rows after := by
  simp only [QuantifiedEveryAdvance, EveryAdvance,
    quantified_iff_of_no_tells (fun rule member => (pure rule member).noTell),
    quantified_terminal_iff_of_no_tells (fun rule member => (pure rule member).noTell)]

theorem quantified_every_step_eq_immediate {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) {rows after : Finset (Term signature)}
    (ground : GroundRows rows) (transition : QuantifiedStep .every timing P rows after) :
    (after : Set (Term signature)) = immediate (consequence (P := P)) (rows : Set (Term signature)) :=
  every_step_eq_immediate pure ground
    ((quantified_iff_of_no_tells (fun rule member => (pure rule member).noTell)).mp transition)

theorem quantified_every_run_stage (slots : signature.vars ≃ Nat) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (rules : List (Rule (Terms (Term signature)))) (covers : ∀ rule ∈ P, rule ∈ rules)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0))
    (advances : ∀ n, QuantifiedEveryAdvance timing P (execution n) (execution (n + 1))) (n : Nat) :
    GroundRows (execution n) ∧
      (execution n : Set (Term signature)) = stage (consequence (P := P)) (execution 0 : Set (Term signature)) n :=
  every_run_stage slots timing pure rules covers execution ground
    (fun k => (quantified_advance_iff pure).mp (advances k)) n

theorem quantified_prefix_bound (discipline : Discipline) (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule)
    (execution : Nat → Finset (Term signature)) (ground : GroundRows (execution 0))
    (n : Nat) (transitions : ∀ k, k < n →
      QuantifiedStep discipline timing P (execution k) (execution (k + 1))) :
    GroundRows (execution n) ∧
      (execution n : Set (Term signature)) ⊆ stage (consequence (P := P)) (execution 0 : Set (Term signature)) n :=
  discipline_prefix_bound discipline timing pure execution ground n
    (fun k bound => (quantified_iff_of_no_tells (fun rule member => (pure rule member).noTell)).mp
      (transitions k bound))

#print axioms quantified_advance_iff
#print axioms quantified_every_step_eq_immediate
#print axioms quantified_every_run_stage
#print axioms quantified_prefix_bound

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.KernelRounds
