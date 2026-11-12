import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrderChecks
import Mettapedia.Logic.LinearLogic.KnowledgeTensorFragments

/-!
# The first-order step is the whole calculus at one frame

The first-order step with every check is a checked system, and a checked system is the whole
calculus at one frame. So its executable schedules are graded proofs of the whole calculus.

* `schedule_iff_zoned_proof`: executable schedules of declared rule instances are exactly the
  graded proofs of the whole calculus, at the one frame, with nothing lent, whose grade admits
  the empty extra context and whose final knowledge is consistent.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic
open _root_.CategoryTheory

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

theorem schedule_iff_zoned_proof [DecidableEq T] [DecidableEq O] (A : SubstitutionAction T S)
    (program : Set (RuleInstance T)) (label : O → T)
    (supply : ∀ (used : Finset O) (value : T), ∃ occurrence, occurrence ∉ used ∧ label occurrence = value)
    (C : Configuration T O) (uses : List (Use T)) (finalKnown : Set S) (Γ' : Multiset T) :
    (∃ schedule : List (ConditionalSchedule.Firing T O),
      ConditionalSchedule.Executable A label C schedule ∧
      (∀ firing ∈ schedule, firing.1 ∈ program) ∧
      schedule.map (useOf label) = uses ∧
      knowledge A (ConditionalSchedule.follow label C schedule) = finalKnown ∧
      resources label (ConditionalSchedule.follow label C schedule) = Γ') ↔
      (∃ (along : (() : Unit) ⟶ ()) (grade : Multiset T → Prop), grade 0 ∧
        (checkedSystem A program).zoned.Proves () 0 (knowledge A C) (resources label C) grade
          (uses.map (Sigma.mk ())) () along finalKnown Γ') ∧ finalKnown.Nonempty := by
  constructor
  · rintro ⟨schedule, executable, declared, rfl, rfl, rfl⟩
    obtain ⟨along, run⟩ := (KnowledgeTensor.CheckedSystem.run_iff_zoned _ _ _ _ _).mp
      (checked_run_of_executable A program label schedule C executable declared)
    obtain ⟨grade, atZero, proof⟩ := KnowledgeTensor.ZonedSystem.RunUnder.proves run
    exact ⟨⟨along, grade, atZero, proof⟩, follow_consistent A label schedule C executable⟩
  · rintro ⟨⟨along, grade, atZero, proof⟩, consistent⟩
    have zonedRun : (checkedSystem A program).zoned.RunUnder () 0 (knowledge A C) (resources label C)
        (uses.map (Sigma.mk ())) () along finalKnown Γ' := by
      simpa only [add_zero] using KnowledgeTensor.ZonedSystem.Proves.run proof 0 atZero
    have run := (KnowledgeTensor.CheckedSystem.run_iff_zoned _ _ _ _ _).mpr ⟨along, zonedRun⟩
    exact executable_of_checked_run A program label supply run consistent C rfl rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrder
