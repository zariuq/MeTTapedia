import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Equivalence.Systems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRuns

/-!
# Local event systems for worlds

A world may use any supplied family of local event systems. Choice fibres
retain distinct admitted events even when their successor states agree.
The existing single-firing construction is `events`, an explicit instance.

Extending the visible program and refusing events in inconsistent worlds
are separate properties. They are not requirements on every local policy.
In particular, a policy that selects a unique match can lose its event when
another rule becomes visible. Relational monotonicity alone asserts no
preservation of event multiplicity or action labels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds

open Interface (Frames)

universe uO uT uH uE uOcc uA uC

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {Action : Type uA}

abbrev LocalSteps (Tm : Obj → Type uT) (O : Type uOcc) (Action : Type uA) :=
  Program Tm → Interface.EventMultiplicity.System.{max uO uT uOcc,uA,uC} (State Tm O) Action

def Advances (family : LocalSteps Tm O Action) (program : Program Tm)
    (before after : State Tm O) : Prop :=
  ∃ choice : (family program).Choice before, (family program).next before choice = after

def ProgramMonotone (family : LocalSteps Tm O Action) : Prop :=
  ∀ (first second : Program Tm), first ⊆ second →
    ∀ before after, Advances family first before after → Advances family second before after

def NoEventsAtInconsistent (X : Frames Tm Hom) (family : LocalSteps Tm O Action) : Prop :=
  ∀ (program : Program Tm) (state : State Tm O), ¬ X.Solvable state.knowledge →
    IsEmpty ((family program).Choice state)

/-- A firing of a program is a firing of every larger program. -/
def widen {E : Extensions.{uO, uH, uE} Hom} {P Q : Program Tm} (inside : P ⊆ Q) {a : Obj}
    (f : Firing O E P a) : Firing O E Q a :=
  ⟨f.rule, inside f.member, f.ext, f.opening, f.selection, f.seen⟩

/-- The existing single-firing event system, with the rule as its action. -/
abbrev events (X : Frames Tm Hom) (O : Type uOcc) [DecidableEq O] (E : Extensions.{uO, uH, uE} Hom)
    (P : Program Tm) :=
  (step X O E P).toStep.eventSystem (Action := Rule Tm) (fun {_} f => f.rule)

variable (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom) [DecidableEq O]

theorem events_advances_iff (program : Program Tm) (before after : State Tm O) :
    Advances (events X O E) program before after ↔
      ∃ firing : Firing O E program before.frame,
        firing.Admits X before ∧ firing.result X before = after := by
  constructor
  · rintro ⟨⟨firing,admitted⟩,result⟩
    exact ⟨firing,admitted,result⟩
  · rintro ⟨firing,admitted,result⟩
    exact ⟨⟨firing,admitted⟩,result⟩

theorem events_program_monotone : ProgramMonotone (events X O E) := by
  rintro first second inside before after advanced
  obtain ⟨firing,admitted,result⟩ := (events_advances_iff X E first before after).mp advanced
  exact (events_advances_iff X E second before after).mpr ⟨widen inside firing,admitted,result⟩

theorem events_no_events_at_inconsistent : NoEventsAtInconsistent X (events X O E) := by
  intro program state dead
  refine ⟨?_⟩
  rintro ⟨firing,admitted⟩
  rcases admitted with ⟨_,_,⟨target,assignment,solved⟩,_⟩
  exact dead ⟨target,_,Firing.knowledge_solved firing solved⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Worlds
