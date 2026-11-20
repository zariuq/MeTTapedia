import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentBraidKnowledge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentKnowledgeDiamond

/-!
# Actual strengthened triple cells and their execution braids

One final consistency condition on an original triple licenses all six
orders after adding source equations. The third residual is copied through
the actual strengthened pair-result equality, so the new schedules use the
same native residual construction as the original cell. The complete braid
theorem then applies to this newly constructed cell.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open KnowledgeChange

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O] {state : State rules O}

namespace DependentRun.Diamond

variable {first second : HelperFiring levels O state}
  {accepted : (helperStep levels O).Admits first} {accepted' : (helperStep levels O).Admits second}
  (diamond : Diamond first second accepted accepted')

theorem strengthened_pair_result (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) :
    (diamond.strengthened added consistent).forward.last =
      strengthen diamond.forward.last (transmitted diamond.forward added) :=
  (congrArg Step.Run.last (diamond.strengthened_forward added consistent)).trans
    (liftRun_last diamond.forward added (diamond.consistency_both added consistent).1)

theorem third_copy (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) (third : HelperFiring levels O state) :
    (diamond.strengthened added consistent).thirdForward (firing added third) =
      (diamond.strengthened_pair_result added consistent).symm ▸
        firing (transmitted diamond.forward added) (diamond.thirdForward third) := by
  apply ContextPlacement.payload_injective
  exact (eq_of_heq (ContextPlacement.payload_cast (diamond.strengthened_pair_result added consistent).symm
    (firing (transmitted diamond.forward added) (diamond.thirdForward third)))).symm

theorem third_admitted_strengthened (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) (third : HelperFiring levels O state)
    (acceptedThird : (helperStep levels O).Admits (diamond.thirdForward third))
    (thirdConsistent : (ContextualDependentEta.frames levels).Solvable
      (pushed (diamond.thirdForward third) (transmitted diamond.forward added) ++
        (diamond.thirdForward third).toFiring.information)) :
    (helperStep levels O).Admits ((diamond.strengthened added consistent).thirdForward (firing added third)) := by
  have copied := (KnowledgeChange.admits_iff _ (diamond.thirdForward third) acceptedThird).mpr thirdConsistent
  have moved := (helperStep levels O).toStep.castAdmits
    (diamond.strengthened_pair_result added consistent).symm _ copied
  exact (diamond.third_copy added consistent third).symm ▸ moved

end DependentRun.Diamond

namespace ExecutionBraid

open DependentRun

variable {first second third : HelperFiring levels O state}

theorem liftSchedule (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule second first third)
    (added : EquationStore (TotalTerm state.frame)) (consistent : RunConsistent one.run added) :
    (helperTransport levels O).TripleSchedule (firing added first) (firing added second) (firing added third) := by
  let diamond := diamond_of_admitted_orders first second one.firstAccepted two.firstAccepted
    one.secondAccepted two.secondAccepted
  have pairConsistent : FinalConsistent diamond.forward added := consistent.2.1
  let next := diamond.strengthened added pairConsistent
  refine ⟨(KnowledgeChange.admits_iff added first one.firstAccepted).mpr
      (diamond.consistency_both added pairConsistent).1.1, next.afterFirst, ?_⟩
  exact diamond.third_admitted_strengthened added pairConsistent third one.thirdAccepted consistent.2.2.1

theorem liftSchedule_run (one : (helperTransport levels O).TripleSchedule first second third)
    (two : (helperTransport levels O).TripleSchedule second first third)
    (added : EquationStore (TotalTerm state.frame)) (consistent : RunConsistent one.run added) :
    (liftSchedule one two added consistent).run = liftRun one.run added consistent := by
  let diamond := diamond_of_admitted_orders first second one.firstAccepted two.firstAccepted
    one.secondAccepted two.secondAccepted
  have pairConsistent : FinalConsistent diamond.forward added := consistent.2.1
  apply Step.Run.eq_of_word_eq
  simp only [Transport.TripleSchedule.run, liftRun, Step.Run.word, Step.Run.word_cast]
  apply congrArg (List.cons (⟨strengthen state added, firing added first⟩ :
    Σ state : State rules O, HelperFiring levels O state))
  have newFirst := (KnowledgeChange.admits_iff added first one.firstAccepted).mpr consistent.1
  have secondEvent :
      (⟨(helperStep levels O).result (firing added first) newFirst,
        helperResidual (firing added first) newFirst (firing added second)⟩ :
          Σ state : State rules O, HelperFiring levels O state) =
        ⟨strengthen ((helperStep levels O).result first one.firstAccepted) (pushed first added),
          firing (pushed first added) (helperResidual first one.firstAccepted second)⟩ := by
    rw [KnowledgeChange.residual added first second one.firstAccepted consistent.1]
    exact event_cast (result added first one.firstAccepted consistent.1).symm _
  have thirdEvent :
      (⟨(diamond.strengthened added pairConsistent).forward.last,
        (diamond.strengthened added pairConsistent).thirdForward (firing added third)⟩ :
          Σ state : State rules O, HelperFiring levels O state) =
        ⟨strengthen diamond.forward.last (transmitted diamond.forward added),
          firing (transmitted diamond.forward added) (diamond.thirdForward third)⟩ := by
    rw [diamond.third_copy added pairConsistent third]
    exact event_cast (diamond.strengthened_pair_result added pairConsistent).symm _
  exact congrArg₂ List.cons secondEvent (congrArg (fun event => [event]) thirdEvent)

theorem strengthened_schedules (schedules : (helperTransport levels O).SixSchedules first second third)
    (added : EquationStore (TotalTerm state.frame)) (final : FinalConsistent schedules.abc.run added) :
    (helperTransport levels O).SixSchedules (firing added first) (firing added second) (firing added third) := by
  obtain ⟨abc, acb, bac, bca, cab, cba⟩ := all_six_consistent schedules added final
  exact ⟨liftSchedule schedules.abc schedules.bac added abc,
    liftSchedule schedules.acb schedules.cab added acb,
    liftSchedule schedules.bac schedules.abc added bac,
    liftSchedule schedules.bca schedules.cba added bca,
    liftSchedule schedules.cab schedules.acb added cab,
    liftSchedule schedules.cba schedules.bca added cba⟩

theorem strengthened_cell (cell : (helperTransport levels O).Cell state [first, second, third])
    (added : EquationStore (TotalTerm state.frame)) (final : FinalConsistent cell.six_schedules.abc.run added) :
    (helperTransport levels O).Cell (strengthen state added)
      [firing added first, firing added second, firing added third] :=
  (strengthened_schedules cell.six_schedules added final).cell

end ExecutionBraid

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid.liftSchedule_run
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ExecutionBraid.strengthened_cell
