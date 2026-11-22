import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface

/-!
# Emptinesses on the step, each with its scope

Each emptiness is a claim that something is absent, and each has its own scope. On any step of the
core:

| emptiness | definition | scope |
|---|---|---|
| the empty container | `EmptyStore`: no occurrence present | one state's store |
| refusal of a firing | `Refused`: the candidate is not admitted, so no event leaves by it | one candidate at one state |
| the empty answer set | `NoSuccessor`: no candidate is admitted | every candidate at one state |
| one answer, empty | `EmptyAnswer`: an admitted firing leaves the empty container | one event |
| the empty type | `NoCandidate`: the type of candidates is empty | the type of candidates |
| no solution | `Unsolvable`: the firing's information has no solution | the frames the step reads |
| refusal of permission | `Forbidden`: prepared, not admitted | permission, past preparation |

Absence of an occurrence (a guard) is a condition admission asks, scoped to the whole store at every
solution; "no verdict" is the third outcome of a guard whose evaluation is undecided
(`SchemaGuards`). Neither is a refusal: absence can permit a firing, and no verdict is neither
outcome.

## Laws between them

* `refused_no_event`: a refused candidate begins no run.
* `noCandidate_noSuccessor`: the empty type is an empty answer set; `NullSeparations` shows the
  converse fails.
* `unsolvable_refused`, `unsolvable_not_forbidden`: no solution refuses by preparation, never by
  permission.
* `forbidden_refused`, `forbidden_solvable`: a forbidden candidate is refused with solvable
  information.
* `emptyAnswer_not_noSuccessor`: one answer whose store is empty is not the empty answer set.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Interface.Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF}

section Kinds

variable (P : Interface.Step X O State Firing)

/-- **The empty container**: no occurrence is present. -/
def EmptyStore (s : State) : Prop := P.present s = ∅

/-- **Refusal of a firing**: the candidate is not admitted. -/
def Refused {s : State} (f : Firing s) : Prop := ¬ P.Admits f

/-- **The empty answer set**: no candidate at the state is admitted. -/
def NoSuccessor (s : State) : Prop := ∀ f : Firing s, ¬ P.Admits f

/-- **One answer whose store is empty**: an admitted firing leaves the empty container. -/
def EmptyAnswer (s : State) : Prop :=
  ∃ (f : Firing s) (admitted : P.Admits f), P.present (P.result f admitted) = ∅

/-- **The empty type**: there is no candidate at all. -/
def NoCandidate (s : State) : Prop := IsEmpty (Firing s)

/-- **No solution**: the firing's information has no solution in the step's frames. -/
def Unsolvable {s : State} (f : Firing s) : Prop := ¬ X.Solvable (P.information f)

/-- **Refusal of permission**: prepared, and not admitted. -/
def Forbidden {s : State} (f : Firing s) : Prop := P.Prepares f ∧ ¬ P.Admits f

end Kinds

variable {P : Interface.Step X O State Firing}

/-- **A refused candidate begins no run.** -/
theorem refused_no_event {s : State} {f : Firing s} (refused : Refused P f) :
    ∀ r : P.Run s, r.word.head? ≠ some ⟨s, f⟩ := by
  intro r
  cases r with
  | nil => simp [Interface.Step.Run.word]
  | cons g admitted _ =>
      simp only [Interface.Step.Run.word, List.head?_cons, ne_eq, Option.some.injEq]
      intro same
      have first : g = f := eq_of_heq (Sigma.mk.inj same).2
      exact refused (first ▸ admitted)

/-- **The empty type is an empty answer set.** -/
theorem noCandidate_noSuccessor {s : State} (none : NoCandidate (Firing := Firing) s) :
    NoSuccessor P s :=
  fun f => (none.false f).elim

/-- **No solution refuses by preparation.** -/
theorem unsolvable_refused {s : State} {f : Firing s} (unsolvable : Unsolvable P f) : Refused P f :=
  fun admitted => unsolvable (P.solvable_information admitted)

/-- **No solution is never a refusal of permission.** -/
theorem unsolvable_not_forbidden {s : State} {f : Firing s} (unsolvable : Unsolvable P f) :
    ¬ Forbidden P f :=
  fun forbidden => unsolvable forbidden.1.2.2

theorem forbidden_refused {s : State} {f : Firing s} (forbidden : Forbidden P f) : Refused P f :=
  forbidden.2

/-- A forbidden candidate has solvable information. -/
theorem forbidden_solvable {s : State} {f : Firing s} (forbidden : Forbidden P f) :
    X.Solvable (P.information f) :=
  forbidden.1.2.2

/-- **One answer whose store is empty is not the empty answer set.** -/
theorem emptyAnswer_not_noSuccessor {s : State} (answer : EmptyAnswer P s) : ¬ NoSuccessor P s := by
  obtain ⟨f, admitted, _⟩ := answer
  exact fun none => none f admitted

#print axioms refused_no_event
#print axioms noCandidate_noSuccessor
#print axioms unsolvable_refused
#print axioms unsolvable_not_forbidden
#print axioms emptyAnswer_not_noSuccessor

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep
