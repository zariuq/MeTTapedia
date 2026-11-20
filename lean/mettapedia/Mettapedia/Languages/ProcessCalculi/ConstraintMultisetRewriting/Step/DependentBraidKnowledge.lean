import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentKnowledgeConsistency
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentExecutionBraid

/-!
# The complete execution braid fixes its source knowledge

The actual adjacent comparisons commute with the refinement to their common
source frame. Thus a single final consistency check licenses all six
strengthened executions. No such statement is inferred for an arbitrary
state automorphism that changes the source parameters.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

namespace BlockTriple

variable {Head : Type} {rules : Rules Head} {Γ : Context rules}

def iteratedBase (first second third : Helpers Γ) : iteratedFrame first second third ⟶ Γ :=
  (iteratedHelpers first second third).weaken ≫ pairBase first second

theorem iteratedFirst_base (first second third : Helpers Γ) :
    iteratedFirst first second third ≫ first.weaken = iteratedBase first second third := Category.assoc _ _ _

theorem iteratedSwapFirst_base (first second third : Helpers Γ) :
    iteratedSwapFirst first second third ≫ iteratedBase second first third = iteratedBase first second third := by
  unfold iteratedBase
  rw [← Category.assoc, iteratedSwapFirst_pair, Category.assoc, exchange_pairBase]

theorem iteratedSwapLast_base (first second third : Helpers Γ) :
    iteratedSwapLast first second third ≫ iteratedBase first third second = iteratedBase first second third := by
  rw [← iteratedFirst_base first third second, ← Category.assoc, iteratedSwapLast_first, iteratedFirst_base]

end BlockTriple

namespace KnowledgeChange

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {state : State rules O}

theorem overStart_comp {first middle last : (helperStep levels O).toStep.Run state}
    (one : PlainIso levels first.last middle.last) (two : PlainIso levels middle.last last.last)
    (firstFixed : OverStart one) (secondFixed : OverStart two) : OverStart (one.trans two) :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun map => two.frame.hom ≫ map) firstFixed).trans secondFixed)

end KnowledgeChange

namespace ExecutionBraid

open BlockTriple KnowledgeChange

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {state : State rules O}
  {first second third : HelperFiring levels O state}

theorem schedule_refinement (schedule : (helperTransport levels O).TripleSchedule first second third) :
    schedule.run.toLast = iteratedBase first.helpers second.helpers third.helpers := by
  change (((𝟙 _) ≫ (helperStep levels O).toStep.along
    (helperResidual (helperResidual first schedule.firstAccepted second) schedule.secondAccepted
      (helperResidual first schedule.firstAccepted third)) schedule.thirdAccepted) ≫
      (helperStep levels O).toStep.along (helperResidual first schedule.firstAccepted second) schedule.secondAccepted) ≫
      (helperStep levels O).toStep.along first schedule.firstAccepted = _
  rw [along, along, along, Category.id_comp]
  exact Category.assoc _ _ _

theorem exchangeFirst_overStart
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule second first third) :
    OverStart (RunStateGroupoid.endpointMap levels O (exchangeFirst one two)) := by
  unfold OverStart
  rw [exchangeFirst_frame, schedule_refinement, schedule_refinement]
  exact iteratedSwapFirst_base second.helpers first.helpers third.helpers

theorem exchangeLast_overStart
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule first third second) :
    OverStart (RunStateGroupoid.endpointMap levels O (exchangeLast one two)) := by
  unfold OverStart
  rw [exchangeLast_frame, schedule_refinement, schedule_refinement]
  exact iteratedSwapLast_base first.helpers third.helpers second.helpers

theorem exchangeFirst_license
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule second first third)
    (added : EquationStore (TotalTerm state.frame)) : RunConsistent one.run added ↔ RunConsistent two.run added :=
  licenses_correspond (RunStateGroupoid.endpointMap levels O (exchangeFirst one two)) (exchangeFirst_overStart one two)
    (by simp [Transport.TripleSchedule.run, Step.Run.word]) (by simp [Transport.TripleSchedule.run, Step.Run.word]) added

theorem exchangeLast_license
    (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule first third second)
    (added : EquationStore (TotalTerm state.frame)) : RunConsistent one.run added ↔ RunConsistent two.run added :=
  licenses_correspond (RunStateGroupoid.endpointMap levels O (exchangeLast one two)) (exchangeLast_overStart one two)
    (by simp [Transport.TripleSchedule.run, Step.Run.word]) (by simp [Transport.TripleSchedule.run, Step.Run.word]) added

theorem all_six_consistent (schedules : (helperTransport levels O).SixSchedules first second third)
    (added : EquationStore (TotalTerm state.frame)) (final : FinalConsistent schedules.abc.run added) :
    RunConsistent schedules.abc.run added ∧ RunConsistent schedules.acb.run added ∧
      RunConsistent schedules.bac.run added ∧ RunConsistent schedules.bca.run added ∧
        RunConsistent schedules.cab.run added ∧ RunConsistent schedules.cba.run added := by
  have abc := consistent_of_final schedules.abc.run added final
  have acb := (exchangeLast_license schedules.abc schedules.acb added).mp abc
  have bac := (exchangeFirst_license schedules.abc schedules.bac added).mp abc
  have bca := (exchangeLast_license schedules.bac schedules.bca added).mp bac
  have cab := (exchangeFirst_license schedules.acb schedules.cab added).mp acb
  have cba := (exchangeFirst_license schedules.bca schedules.cba added).mp bca
  exact ⟨abc, acb, bac, bca, cab, cba⟩

end ExecutionBraid

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid.all_six_consistent
