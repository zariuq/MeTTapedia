import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceProjection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalSchedule

/-!
# Ordinary conditional schedules as realized resource runs

The existing schedule supplies actual rules, occurrence choices and checks
at their original equation prefixes. One model of its final equation store
interprets every occurrence throughout the whole schedule. The resulting
existing resource run retains the same ordered firing list; it does not
replace the schedule by an order-free mating or erase interference conditions.

Read ports are normalized by physical support at each firing. The ordinary
fixed-family action here does not instantiate stored schemas independently
at each read; that requires the separate contextual view construction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceSchedules

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Causality
open PositiveResourceProjection

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S)

def entries (assignment : S) (label : O → T) (schedule : List (ConditionalSchedule.Firing T O)) :
    List (resources A assignment label).Entry :=
  schedule.map fun firing => ⟨⟨firing.1⟩, ⟨firing.2⟩⟩

theorem final_model_models_prefix (assignment : S) (label : O → T) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (before : Configuration T O),
      ConditionalSchedule.Executable A label before schedule →
      A.Models assignment (ConditionalSchedule.follow label before schedule).equations →
      A.Models assignment before.equations
  | [], _, _, solved => solved
  | _firing :: rest, _before, executable, solved =>
      executable.1.refines assignment
        (final_model_models_prefix assignment label rest _ executable.2 solved)

/-- The same final solution grounds the whole existing ordered resource run.
Earlier conditions were already required at their own prefix; this theorem
does not discharge them retroactively with a later binding. -/
theorem realized_fires [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (before : Configuration T O),
      ConditionalSchedule.Executable A label before schedule →
      A.Models assignment (ConditionalSchedule.follow label before schedule).equations →
      (resources A assignment label).Fires (entries A assignment label schedule)
        (labels (realized A assignment label) before.present)
        (labels (realized A assignment label) (ConditionalSchedule.follow label before schedule).present)
  | [], _, _, _ => rfl
  | firing :: rest, before, executable, solved => by
      have middleModels := final_model_models_prefix A assignment label rest
        (firing.2.result label firing.1 before) executable.2 solved
      obtain ⟨enabled, destination⟩ := resource_firing A structural executable.1 middleModels
      refine ⟨enabled, ?_⟩
      change (resources A assignment label).Fires (entries A assignment label rest)
        ((resources A assignment label).fire _ (site := ⟨firing.1⟩) ⟨firing.2⟩) _
      rw [← destination]
      exact realized_fires assignment label structural rest _ executable.2 solved

theorem atomic_linear_realized_fires [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq) :
    ∀ (schedule : List (ConditionalSchedule.Firing T O)) (before : Configuration T O),
      ConditionalSchedule.Executable A label before schedule →
      A.Models assignment (ConditionalSchedule.follow label before schedule).equations →
      (resources A assignment label).takeRepublish.Fires (entries A assignment label schedule)
        (labels (realized A assignment label) before.present)
        (labels (realized A assignment label) (ConditionalSchedule.follow label before schedule).present)
  | [], _, _, _ => rfl
  | firing :: rest, before, executable, solved => by
      have middleModels := final_model_models_prefix A assignment label rest
        (firing.2.result label firing.1 before) executable.2 solved
      obtain ⟨enabled, destination⟩ := atomic_linear_rendering A structural executable.1 middleModels
      refine ⟨enabled, ?_⟩
      change (resources A assignment label).takeRepublish.Fires (entries A assignment label rest)
        ((resources A assignment label).takeRepublish.fire _ (site := ⟨firing.1⟩) ⟨firing.2⟩) _
      rw [← destination]
      exact atomic_linear_realized_fires assignment label structural rest _ executable.2 solved

/-- The inspectable compiled schedule supplies the exact same comparison.
No second proof-search or schedule interpreter is introduced. -/
theorem compiled_realized_fires [DecidableEq T] (assignment : S) (label : O → T)
    (structural : A.E = Eq) (schedule : List (ConditionalSchedule.Firing T O))
    (before : Configuration T O)
    (admitted : (ConditionalSchedule.compile label schedule).Holds A label before)
    (solved : A.Models assignment ((ConditionalSchedule.compile label schedule).result before).equations) :
    (resources A assignment label).Fires (entries A assignment label schedule)
      (labels (realized A assignment label) before.present)
      (labels (realized A assignment label) ((ConditionalSchedule.compile label schedule).result before).present) := by
  have executable := (ConditionalSchedule.compile_holds_iff A label before schedule).mp admitted
  rw [ConditionalSchedule.compile_result A label before schedule executable] at solved ⊢
  exact realized_fires A assignment label structural schedule before executable solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceSchedules
