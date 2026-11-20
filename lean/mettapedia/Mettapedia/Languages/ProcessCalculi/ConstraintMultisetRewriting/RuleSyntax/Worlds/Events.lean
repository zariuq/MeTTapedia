import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Sharing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds.Local
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRealization

/-!
# Confinement, for the comparison of systems that counts events

The tree compares two systems of events by a bijection of their fibres of events
(`Interface.EventMultiplicity.Bisimulation`), and puts two systems side by side with nothing shared
by `Interface.EventMultiplicity.asynchronous`. Two worlds of a bag, with a fixed space, fire as the
asynchronous composition of the steps of their programs with the space. This module states
confinement there.

* `events`: the events of the step of a program, each labelled by its rule: the tree's
  `Interface.Step.eventSystem`.
* `idleBeside`: for any two systems of events, **a component that has no event, and keeps none, is
  not there**: the composition is bisimilar to the other component, by a bijection of events.
* `dead_no_events`, `dead_beside_bisimilar`: a world whose knowledge has no solution has no event, so
  **beside any system of events it is not there**.
* `deadRowRealization`, `dead_row_bisimilar`: **a row published from such a world changes no fibre of
  events** of any world: the step of a program with the space, and with the space and that row, are
  related by a bijection of events at every state, with the same rules and the same results.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)
open Interface.EventMultiplicity (Bisimulation Bisimilar Realization asynchronous)
open Hosting.Alternatives.Worlds (snapshot)

universe uS uT uA uC uD uO uTm uH uE uOcc

/-! ## A component with no event -/

section Idle

variable {S : Type uS} {T : Type uT} {A : Type uA}

/-- **A component that has no event, and keeps none, is not there.** -/
def idleBeside (left : Interface.EventMultiplicity.System.{uS, uA, uC} S A)
    (right : Interface.EventMultiplicity.System.{uT, uA, uD} T A) (idle : T → Prop)
    (still : ∀ t, idle t → IsEmpty (right.Choice t)) :
    Bisimulation (asynchronous left right) left (fun p s => p.1 = s ∧ idle p.2) where
  choices := fun {p s} same =>
    match s, same with
    | _, ⟨rfl, quiet⟩ => @Equiv.sumEmpty (left.Choice p.1) (right.Choice p.2) (still p.2 quiet)
  actions := fun {p s} same choice => by
    obtain ⟨rfl, quiet⟩ := same
    cases choice with
    | inl c => rfl
    | inr c => exact (still p.2 quiet).elim c
  successors := fun {p s} same choice => by
    obtain ⟨rfl, quiet⟩ := same
    cases choice with
    | inl c => exact ⟨rfl, quiet⟩
    | inr c => exact (still p.2 quiet).elim c

end Idle

/-! ## The events of a world -/

variable {Obj : Type uO} {Tm : Obj → Type uTm} {Hom : Obj → Obj → Type uH} {O : Type uOcc}
  [DecidableEq O]

variable {X : Frames Tm Hom} {E : Extensions.{uO, uH, uE} Hom}

/-- **A world whose knowledge has no solution has no event.** -/
theorem dead_no_events (P : Program Tm) {s : State Tm O} (dead : ¬ X.Solvable s.knowledge) :
    IsEmpty ((events X O E P).Choice s) :=
  ⟨fun choice => not_admits_of_unsolvable dead choice.1 choice.2⟩

/-- **Beside any system of events, a world whose knowledge has no solution is not there**: the
asynchronous composition is bisimilar to the other component, counting events. -/
theorem dead_beside_bisimilar {S : Type uS}
    (left : Interface.EventMultiplicity.System.{uS, max uO uTm, uC} S (Rule Tm)) (P : Program Tm) (s : S)
    {d : State Tm O} (dead : ¬ X.Solvable d.knowledge) :
    Bisimilar (asynchronous left (events X O E P)) (s, d) left s :=
  ⟨_, ⟨idleBeside left (events X O E P) (fun t => ¬ X.Solvable t.knowledge)
    fun _ unsolvable => dead_no_events P unsolvable⟩, rfl, dead⟩

/-! ## A row published from a dead world -/

/-- **A row published from a world whose knowledge has no solution changes no fibre of events**: at
every state, the events of a program with the space and with the space and that row correspond one to
one, with the same rules and the same results. -/
def deadRowRealization (P R : Program Tm) {s : State Tm O} (atom : Tm s.frame)
    (dead : ¬ X.Solvable s.knowledge) :
    Realization (events X O E (P ∪ R)) (events X O E (P ∪ insert (snapshot s atom) R)) where
  state := id
  choices _ :=
    { toFun := fun c => ⟨widen (Set.union_subset_union_right _ (Set.subset_insert _ _)) c.1, c.2⟩
      invFun := fun c => ⟨⟨c.1.rule, dead_row_unused atom dead c.1 c.2, c.1.ext, c.1.opening,
        c.1.selection, c.1.seen⟩, c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  actions _ _ := rfl
  successors _ _ := rfl

/-- The same, as a bisimilarity at every state. -/
theorem dead_row_bisimilar (P R : Program Tm) {s : State Tm O} (atom : Tm s.frame)
    (dead : ¬ X.Solvable s.knowledge) (t : State Tm O) :
    Bisimilar (events X O E (P ∪ R)) t (events X O E (P ∪ insert (snapshot s atom) R)) t :=
  (deadRowRealization P R atom dead).bisimilar t

#print axioms idleBeside
#print axioms dead_no_events
#print axioms dead_beside_bisimilar
#print axioms deadRowRealization
#print axioms dead_row_bisimilar

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
