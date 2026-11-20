import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Worlds.OriginSupport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.SupportSimulation

/-!
# Row-support interpretation through worlds and indexed persistent rules

For the actual propagation fragment, a singleton world's reachable settled
row supports are exactly the reachable set-store states. The same supports
are reached by actual runs holding the shared rules at persistent indices.
Both comparisons use the existing concrete intermediate bag states.

The observation includes `Settled`, so an inconsistent world whose support
function returns the empty set is not mistaken for a valid empty result.
The comparison forgets origin multiplicity and repeated propagation events;
it neither reflects divergence nor identifies whole histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.RowSupport

open Mettapedia.Logic.LP
open RuleSyntax RuleSyntax.Worlds RuleSyntax.RuleOccurrences
open OneFrame (Terms)
open RuleSyntax.SetStoreSyntax
open FragmentsOfTheStep.TransitionMaps
open LogicOverTheStep.StepSpan (Succ)

universe uOcc uR uZ

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {O : Type uOcc} [DecidableEq O]

/-- A support observation is made only at a state with a justified settled
reading. Inconsistent and unresolved row readings are not accepted. -/
def ReadsSupport (rows : Finset (Term signature)) (state : State (Terms (Term signature)) O) : Prop :=
  StepWeb.Support.Settled state ∧ StepWeb.Support.support state = rows

variable [Infinite O] {P Q : Program (Terms (Term signature))}

theorem singleton_support_reachable_iff (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P ∪ Q, Propagates rule) (slots : signature.vars ≃ ℕ)
    {state : State (Terms (Term signature)) O} (settled : StepWeb.Support.Settled state)
    (rows : Finset (Term signature)) :
    Reaches (events X O E) (ReadsSupport rows) (singleton P Q state) ↔
      Relation.ReflTransGen (SetStore.Step timing (P ∪ Q)) (StepWeb.Support.support state) rows := by
  let comparison := one_world_bisimulation (X := X) (E := E) (O := O) P Q
  rw [← StepWeb.Support.reachable_iff timing pure slots settled rows]
  constructor
  · rintro ⟨last, run, observed⟩
    obtain ⟨after, source, represented⟩ := Zag.path comparison.zag run state rfl
    rw [← represented] at observed
    exact ⟨after, source,
      ((singleton_shows P Q after (ReadsSupport rows)).mp observed).2⟩
  · rintro ⟨after, run, supported⟩
    have final_settled := (StepWeb.Support.forward_run_closure pure settled run).1
    exact ⟨singleton P Q after,
      Zig.path (stepX := Succ (step X O E (P ∪ Q)).toStep)
        (stepY := Fires (events X O E)) (map := singleton P Q)
        (fun moved => comparison.zig moved) run,
      (singleton_shows P Q after (ReadsSupport rows)).mpr ⟨final_settled, supported⟩⟩

section Held

variable {R : Type uR} [DecidableEq R] {Z : Type uZ}
  {ids : Finset R} {code : R → Rule (Terms (Term signature))}
  (zone : R → Z) (offers : Offers Q ids code)

include offers

theorem held_support_reachable_iff (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P ∪ Q, Propagates rule) (slots : signature.vars ≃ ℕ)
    {state : State (Terms (Term signature)) O} (settled : StepWeb.Support.Settled state)
    (rows : Finset (Term signature)) :
    (∃ after, Relation.ReflTransGen (Succ (rstep X O R E (ofRules Z) P).toStep)
        (holding state ids code zone) after ∧ ReadsSupport rows after.toState) ↔
      Relation.ReflTransGen (SetStore.Step timing (P ∪ Q)) (StepWeb.Support.support state) rows := by
  let comparison := LiveRules.persistentBisimulation (O := O) (P := P) X E offers zone
  rw [← StepWeb.Support.reachable_iff timing pure slots settled rows]
  constructor
  · rintro ⟨last, run, observed⟩
    obtain ⟨after, source, represented⟩ := Zag.path comparison.zag run state rfl
    rw [← represented] at observed
    exact ⟨after, source, observed.2⟩
  · rintro ⟨after, run, supported⟩
    have final_settled := (StepWeb.Support.forward_run_closure pure settled run).1
    exact ⟨holding after ids code zone,
      Zig.path (stepX := Succ (step X O E (P ∪ Q)).toStep)
        (stepY := Succ (rstep X O R E (ofRules Z) P).toStep)
        (map := fun source => holding source ids code zone)
        (fun moved => comparison.zig moved) run, final_settled, supported⟩

/-- The world support and the indexed-rule execution meet through the same
actual set-store reachability, with no origin-count claim. -/
theorem world_held_support_iff (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P ∪ Q, Propagates rule) (slots : signature.vars ≃ ℕ)
    {state : State (Terms (Term signature)) O} (settled : StepWeb.Support.Settled state)
    (rows : Finset (Term signature)) :
    Reaches (events X O E) (ReadsSupport rows) (singleton P Q state) ↔
      ∃ after, Relation.ReflTransGen (Succ (rstep X O R E (ofRules Z) P).toStep)
        (holding state ids code zone) after ∧ ReadsSupport rows after.toState :=
  (singleton_support_reachable_iff timing pure slots settled rows).trans
    (held_support_reachable_iff zone offers timing pure slots settled rows).symm

end Held

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.RowSupport
