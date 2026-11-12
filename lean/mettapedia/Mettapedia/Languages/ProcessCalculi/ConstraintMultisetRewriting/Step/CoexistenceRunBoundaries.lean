import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceAnnotated
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CoexistenceControls

/-!
# Raw paths and consistent executions have different empty-run domains

The old executable-run predicate asks for consistent knowledge even at the
empty word. The general interface's raw run category has the identity at every
state. The difference survives disjoint resources and individually consistent
components, so their tensor conditions must not be identified implicitly.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

universe uO uT uH uOcc uS uF

namespace Step.Run

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} {profile : Step X O State Firing}

theorem solvable_start_of_nonempty {state : State} (run : profile.Run state)
    (nonempty : run.word ≠ []) : X.Solvable (profile.knowledge state) := by
  cases run with
  | nil _ => exact False.elim (nonempty rfl)
  | cons _ admitted _ => exact profile.solvable_knowledge admitted

end Step.Run

namespace Coexistence.RunBoundaries

open AdmissionObservationCover.Controls (World frame)
open Coexistence.Controls (zero one zero_solvable one_solvable individually_solvable_jointly_inconsistent)

abbrev action := frame.endo ()
def label (_ : Nat) : World → Bool := fun _ => false
def left : Configuration (World → Bool) Nat := ⟨zero.equations, {0}⟩
def right : Configuration (World → Bool) Nat := ⟨one.equations, {1}⟩
def joined := Coexistence.tensor left right
abbrev profile := (AnnotatedRuns.firstOrder action label).toStep

theorem disjoint_occurrences : Disjoint left.present right.present := by decide

theorem individually_executable :
    AnnotatedRuns.Executable action label left [] ∧ AnnotatedRuns.Executable action label right [] := by
  constructor
  · obtain ⟨target, mapping, solved⟩ := zero_solvable
    cases target
    exact ⟨mapping, solved⟩
  · obtain ⟨target, mapping, solved⟩ := one_solvable
    cases target
    exact ⟨mapping, solved⟩

theorem joined_inconsistent : ¬action.Consistent joined.equations := by
  rintro ⟨mapping, solved⟩
  exact individually_solvable_jointly_inconsistent.2.2 ⟨(), mapping, solved⟩

theorem raw_identity_exists : Nonempty (profile.Run joined) := ⟨.nil joined⟩

theorem consistent_identity_does_not_exist : ¬AnnotatedRuns.Executable action label joined [] :=
  joined_inconsistent

theorem raw_and_executable_domains_differ :
    Nonempty (profile.Run joined) ∧ ¬AnnotatedRuns.Executable action label joined [] :=
  ⟨raw_identity_exists, consistent_identity_does_not_exist⟩

theorem no_event_from_joined (firing : AnnotatedRuns.Firing (World → Bool) (World → World) Nat) :
    ¬profile.Admits (s := joined) firing := by
  intro admitted
  exact joined_inconsistent ((Frames.ofSubstitution_solvable_iff action _).mp
    (profile.solvable_knowledge admitted))

theorem raw_run_is_identity (run : profile.Run joined) : run.word = [] := by
  cases run with
  | nil _ => rfl
  | cons firing admitted _ => exact False.elim (no_event_from_joined firing admitted)

end Coexistence.RunBoundaries
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
