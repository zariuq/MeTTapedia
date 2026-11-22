import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.SynchronousUpdate
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Knowledge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps
import Mettapedia.GSLT.Core.OperationalReadback
import Mettapedia.GSLT.Meredith.GSLT

/-!
# The bag step and the step of the program reach the same states, where bags are runs

Both steps are relations on the states of the one frame, made theories by `TransitionMaps.theoryOf`. The
relation between states is equality.

## The reading with each member's guards at its own information (`ownCorrespondence`)

For a program of positive rules (`Scope.Positive`: equation guards only, no collect query), the bag step with
the guards of each member at its own information (`OwnSucc`) and the step of the program are related by
an `OperationalCorrespondence` at every state: a step of the program is the bag of its one firing
(`readStep`), and a bag step is a finite run of the step of the program (`forward`, by
`run_of_admitsOwn`). So reachable observations agree (`own_reachable_iff`).

## The reading with the guards at the joint information (`jointCorrespondence`)

For a program of positive rules whose terms are fixed, at states that mention only fixed terms (a set of
states the step keeps, `fixed_after`), `bagStep` and the step of the program are related in the same way
(`forward` by `run_of_admits_of_fixed`).

## Outside these fragments, the failure

* **Absence** (`absence_breaks_forward`): with the rules of `Absence.Synchronous` (module `SynchronousUpdate`), a bag step reaches a
  state that no run of the step of the program reaches. The forward law fails; the rules are not positive.
* **Shared unknowns** (`knowledge_breaks_forward`): with the rules of `Knowledge`, at a state whose rows
  are labelled by unknowns, `bagStep` has a step and the step of the program has none, so the bag's
  result is reached by no run. The forward law fails; the state does not mention only fixed terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open LogicOverTheStep.StepSpan (Succ)
open OneFrame (Terms frames ext)
open Scope (Positive)
open Mettapedia.GSLT.IndexedOperational (OperationalCorrespondence executionPath_nonempty_iff_multiStep)
open FragmentsOfTheStep.TransitionMaps (theoryOf)

section Correspondences

universe uT uS uO

variable {T : Type uT} {S : Type uS} (A : SubstitutionAction T S) (O : Type uO) [DecidableEq O]
  (P : Program (Terms T))

/-- **The bag step with each member's guards at its own information**, as a relation on states. -/
def OwnSucc (s s' : State (Terms T) O) : Prop :=
  ∃ f : Bag O (ext A) P s.frame, f.members ≠ [] ∧ f.AdmitsOwn (frames A) s ∧ f.result (frames A) s = s'

/-- The step of the program, as a theory. -/
abbrev stepTheory := theoryOf (State (Terms T) O) (Succ (step (frames A) O (ext A) P).toStep)

/-- The bag step with each member's guards at its own information, as a theory. -/
abbrev ownTheory := theoryOf (State (Terms T) O) (OwnSucc A O P)

/-- The bag step with the guards at the joint information, as a theory. -/
abbrev jointTheory := theoryOf (State (Terms T) O) (Succ (bagStep (frames A) O (ext A) P).toStep)

variable {A O P}

/-- A run of the step of the program is a path of its theory. -/
theorem path_of_run {s s' : State (Terms T) O}
    (run : Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s s') :
    Nonempty (Mettapedia.GSLT.IndexedOperational.ExecutionPath (stepTheory A O P) s s') :=
  (executionPath_nonempty_iff_multiStep _ _ _).mpr
    ((Mettapedia.GSLT.Meredith.multiStep_iff_reflTransGen _ _ _).mpr run)

/-- A step of the program is a bag step of its one firing. -/
theorem ownSucc_of_succ {s s' : State (Terms T) O} (stepped : Succ (step (frames A) O (ext A) P).toStep s s') :
    OwnSucc A O P s s' := by
  obtain ⟨g, admitted, rfl⟩ := stepped
  exact ⟨Bag.single g, List.cons_ne_nil _ _,
    (Bag.admitsOwn_single (frames A) s (Member.ofFiring g)).mpr admitted, Bag.single_result (frames A) s g⟩

/-- **A bag step of positive rules is a run of the step of the program.** -/
theorem run_of_ownSucc (positive : ∀ r ∈ P, Positive r) {s s' : State (Terms T) O}
    (stepped : OwnSucc A O P s s') :
    Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s s' := by
  obtain ⟨⟨⟨⟩, members⟩, -, own, rfl⟩ := stepped
  exact run_of_admitsOwn A members s (fun r _ => positive r.rule r.member) own

/-- **The bag step (guards at each member's own information) and the step of a positive program**: one
single step for a bag of one, one finite run for a bag. -/
def ownCorrespondence (positive : ∀ r ∈ P, Positive r) :
    OperationalCorrespondence (ownTheory A O P) (stepTheory A O P) where
  related := Eq
  readStep := by
    rintro origin current next rfl stepped
    exact Or.inr ⟨next, ownSucc_of_succ stepped, rfl⟩
  forward := by
    rintro origin after current rfl stepped
    exact ⟨after, path_of_run (run_of_ownSucc positive stepped), rfl⟩

/-- **Reachable observations agree.** -/
theorem own_reachable_iff (positive : ∀ r ∈ P, Positive r) (observation : State (Terms T) O → Prop)
    (s : State (Terms T) O) :
    (∃ s', (ownTheory A O P).MultiStep s s' ∧ observation s') ↔
      ∃ s', (stepTheory A O P).MultiStep s s' ∧ observation s' :=
  (ownCorrespondence positive).reachable_iff observation observation
    (fun {origin current} same => by rw [show origin = current from same]) rfl

/-! ## The joint reading, at states that mention only fixed terms -/

variable (A) in
/-- A state that mentions only fixed terms. -/
def FixedState (s : State (Terms T) O) : Prop := ∀ t, s.Mentions t → ∀ σ : S, A.E (A.apply σ t) t

/-- **A firing of a rule with fixed terms keeps a state that mentions only fixed terms.** -/
theorem fixed_after {s : State (Terms T) O} (fixed : FixedState A s) {g : Firing O (ext A) P PUnit.unit}
    (ground : ∀ t ∈ g.rule.terms, ∀ σ : S, A.E (A.apply σ t) t) (admitted : g.Admits (frames A) s) :
    FixedState A (g.result (frames A) s) := by
  intro t mentioned σ
  rcases Scope.footprint_of_result A admitted.1 admitted.2.1 mentioned with old | opened
  · exact fixed t old σ
  · obtain ⟨t₀, member, rfl⟩ := List.mem_map.mp opened
    have near : A.E (A.apply g.opening t₀) t₀ := ground t₀ member g.opening
    exact A.equivalence.trans (A.preserves σ near)
      (A.equivalence.trans (ground t₀ member σ) (A.equivalence.symm near))

/-- **Runs of a program with fixed terms keep states that mention only fixed terms.** -/
theorem fixed_along (ground : ∀ r ∈ P, ∀ t ∈ r.terms, ∀ σ : S, A.E (A.apply σ t) t)
    {s s' : State (Terms T) O} (fixed : FixedState A s)
    (run : Relation.ReflTransGen (Succ (step (frames A) O (ext A) P).toStep) s s') : FixedState A s' := by
  induction run with
  | refl => exact fixed
  | tail _ stepped earlier =>
      obtain ⟨g, admitted, rfl⟩ := stepped
      exact fixed_after earlier (ground g.rule g.member) admitted

/-- **The bag step (guards at the joint information) and the step of a positive program with fixed
terms**, related at states that mention only fixed terms. -/
def jointCorrespondence (positive : ∀ r ∈ P, Positive r)
    (ground : ∀ r ∈ P, ∀ t ∈ r.terms, ∀ σ : S, A.E (A.apply σ t) t) :
    OperationalCorrespondence (jointTheory A O P) (stepTheory A O P) where
  related s t := s = t ∧ FixedState A s
  readStep := by
    rintro origin current next ⟨rfl, fixed⟩ stepped
    refine Or.inr ⟨next, succ_bagStep_of_succ (frames A) O (ext A) P stepped, rfl, ?_⟩
    exact fixed_along ground fixed (Relation.ReflTransGen.single stepped)
  forward := by
    rintro origin after current ⟨rfl, fixed⟩ ⟨⟨⟨⟩, members⟩, ⟨-, admitted⟩, rfl⟩
    have run := run_of_admits_of_fixed A fixed (fun r _ => positive r.rule r.member) admitted
    exact ⟨_, path_of_run run, rfl, fixed_along ground fixed run⟩

end Correspondences

/-! ## Outside the fragments -/

section Failures

open Examples (Tm X E)

/-- **With absence, the forward law fails**: a bag step (guards at each member's own information)
reaches a state that no run of the step of the program reaches. -/
theorem absence_breaks_forward :
    ∃ s s', OwnSucc Controls.action ℕ Synchronous.program s s' ∧
      ¬ Relation.ReflTransGen (Succ (step X ℕ E Synchronous.program).toStep) s s' :=
  ⟨Synchronous.empty, _, ⟨Synchronous.both, List.cons_ne_nil _ _, Synchronous.both_admitted, rfl⟩,
    Synchronous.no_run_reaches⟩

/-- **With rows labelled by unknowns, the forward law fails for the joint reading**: a bag step from a
state where the step of the program has no step, to a state other than that one. -/
theorem knowledge_breaks_forward :
    ∃ s s', Succ (bagStep X ℕ E Knowledge.program).toStep s s' ∧
      ¬ Relation.ReflTransGen (Succ (step X ℕ E Knowledge.program).toStep) s s' := by
  refine ⟨Knowledge.start, _, ⟨Knowledge.both, Knowledge.both_fires, rfl⟩, fun run => ?_⟩
  rcases Relation.ReflTransGen.cases_head run with same | ⟨next, stepped, -⟩
  · have known := congrArg (fun s : State Tm ℕ => s.knowledge.length) same
    have before : Knowledge.start.knowledge.length = 0 := rfl
    have after : (Bag.result X Knowledge.start Knowledge.both).knowledge.length = 6 := rfl
    exact absurd (after.symm.trans (known.symm.trans before)) (by decide)
  · exact Knowledge.stopped_and_fires.1 ⟨next, stepped⟩

end Failures

#print axioms path_of_run
#print axioms ownSucc_of_succ
#print axioms run_of_ownSucc
#print axioms ownCorrespondence
#print axioms own_reachable_iff
#print axioms fixed_after
#print axioms fixed_along
#print axioms jointCorrespondence
#print axioms absence_breaks_forward
#print axioms knowledge_breaks_forward

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings
