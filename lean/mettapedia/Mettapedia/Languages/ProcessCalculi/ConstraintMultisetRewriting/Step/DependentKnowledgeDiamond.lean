import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentKnowledgeConsistency
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentResidualCube

/-!
# Canonical dependent diamonds under stronger knowledge

The actual block exchange fixes the common source frame. Consequently one
final consistency condition licenses both strengthened orders. Their new
residuals are the transported originals, and the new canonical diamond is a
comparison of the exact strengthened executions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta KnowledgeChange

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

namespace KnowledgeChange

theorem residual_admitted {state : State rules O} (added : EquationStore (TotalTerm state.frame))
    (first second : HelperFiring levels O state) (accepted : (helperStep levels O).Admits first)
    (afterFirst : (helperStep levels O).Admits (helperResidual first accepted second))
    (one : (frames levels).Solvable (pushed first added ++ first.toFiring.information))
    (two : (frames levels).Solvable
      (pushed (helperResidual first accepted second) (pushed first added) ++
        (helperResidual first accepted second).toFiring.information)) :
    (helperStep levels O).Admits
      (helperResidual (firing added first) ((admits_iff added first accepted).mpr one) (firing added second)) := by
  have moved := (helperStep levels O).toStep.castAdmits (result added first accepted one).symm _
    ((admits_iff (pushed first added) (helperResidual first accepted second) afterFirst).mpr two)
  exact (residual added first second accepted one).symm ▸ moved

omit [DecidableEq O] in
theorem event_cast {source target : State rules O} (same : source = target) (candidate : HelperFiring levels O source) :
    (⟨target, same ▸ candidate⟩ : Σ state : State rules O, HelperFiring levels O state) = ⟨source, candidate⟩ := by
  cases same
  rfl

end KnowledgeChange

namespace DependentRun.Diamond

variable {state : State rules O} {first second : HelperFiring levels O state}
  {accepted : (helperStep levels O).Admits first} {accepted' : (helperStep levels O).Admits second}
  (diamond : Diamond first second accepted accepted')

theorem forward_refinement : diamond.forward.toLast = BlockTriple.pairBase first.helpers second.helpers := by
  change ((𝟙 _) ≫ (helperStep levels O).toStep.along (helperResidual first accepted second) diamond.afterFirst) ≫
    (helperStep levels O).toStep.along first accepted = _
  rw [along, along, Category.id_comp]
  rfl

theorem backward_refinement : diamond.backward.toLast = BlockTriple.pairBase second.helpers first.helpers := by
  change ((𝟙 _) ≫ (helperStep levels O).toStep.along (helperResidual second accepted' first) diamond.afterSecond) ≫
    (helperStep levels O).toStep.along second accepted' = _
  rw [along, along, Category.id_comp]
  rfl

theorem over_start : OverStart diamond.close := by
  unfold OverStart
  rw [diamond.forward_refinement, diamond.backward_refinement]
  exact BlockTriple.exchange_pairBase second.helpers first.helpers

theorem consistency_both (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) :
    RunConsistent diamond.forward added ∧ RunConsistent diamond.backward added := by
  have first := consistent_of_final diamond.forward added consistent
  exact ⟨first, (licenses_correspond diamond.close diamond.over_start
    (by simp [forward, Step.Run.word]) (by simp [backward, Step.Run.word]) added).mp first⟩

theorem strengthened (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) :
    Diamond (firing added first) (firing added second)
      ((KnowledgeChange.admits_iff added first accepted).mpr (diamond.consistency_both added consistent).1.1)
      ((KnowledgeChange.admits_iff added second accepted').mpr (diamond.consistency_both added consistent).2.1) :=
  diamond_of_admitted_orders _ _ _ _
    (residual_admitted added first second accepted diamond.afterFirst
      (diamond.consistency_both added consistent).1.1 (diamond.consistency_both added consistent).1.2.1)
    (residual_admitted added second first accepted' diamond.afterSecond
      (diamond.consistency_both added consistent).2.1 (diamond.consistency_both added consistent).2.2.1)

theorem strengthened_forward (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) :
    (diamond.strengthened added consistent).forward =
      liftRun diamond.forward added (diamond.consistency_both added consistent).1 := by
  apply Step.Run.eq_of_word_eq
  simp only [forward, liftRun, Step.Run.word, Step.Run.word_cast]
  apply congrArg (List.cons (⟨strengthen state added, firing added first⟩ :
    Σ state : State rules O, HelperFiring levels O state))
  apply congrArg (fun event => [event])
  rw [KnowledgeChange.residual added first second accepted (diamond.consistency_both added consistent).1.1]
  exact event_cast (result added first accepted (diamond.consistency_both added consistent).1.1).symm _

theorem strengthened_backward (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) :
    (diamond.strengthened added consistent).backward =
      liftRun diamond.backward added (diamond.consistency_both added consistent).2 := by
  apply Step.Run.eq_of_word_eq
  simp only [backward, liftRun, Step.Run.word, Step.Run.word_cast]
  apply congrArg (List.cons (⟨strengthen state added, firing added second⟩ :
    Σ state : State rules O, HelperFiring levels O state))
  apply congrArg (fun event => [event])
  rw [KnowledgeChange.residual added second first accepted' (diamond.consistency_both added consistent).2.1]
  exact event_cast (result added second accepted' (diamond.consistency_both added consistent).2.1).symm _

noncomputable def strengthenedCell (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) :
    Transport.RunRearrangement.Cell (helperTransport levels O)
      (liftRun diamond.forward added (diamond.consistency_both added consistent).1)
      (liftRun diamond.backward added (diamond.consistency_both added consistent).2) := by
  rw [← diamond.strengthened_forward added consistent, ← diamond.strengthened_backward added consistent]
  exact (diamond.strengthened added consistent).cell

theorem strengthened_frame (added : EquationStore (TotalTerm state.frame))
    (consistent : FinalConsistent diamond.forward added) :
    (diamond.strengthened added consistent).close.frame.hom = diamond.close.frame.hom := rfl

end DependentRun.Diamond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.DependentRun.Diamond.strengthenedCell
