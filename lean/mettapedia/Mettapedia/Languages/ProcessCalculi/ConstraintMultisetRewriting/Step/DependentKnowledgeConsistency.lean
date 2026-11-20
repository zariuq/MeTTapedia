import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentKnowledgeRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentStateGroupoid

/-!
# Final consistency and the source-frame condition for stronger knowledge

For a nonempty existing run, solvability of its strengthened final knowledge
is exactly the local consistency license at every firing. Final models pull
back through the actual run refinement. A comparison that fixes the common
source frame carries the added equations to corresponding endpoint equations;
the strengthening licenses then agree on its two runs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type} [DecidableEq O]

def FinalConsistent {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (added : EquationStore (TotalTerm state.frame)) : Prop :=
  (frames levels).Solvable (transmitted run added ++ run.last.knowledge)

theorem consistent_of_final : ∀ {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (added : EquationStore (TotalTerm state.frame)), FinalConsistent run added → RunConsistent run added
  | _, .nil _, _, _ => True.intro
  | _, .cons candidate accepted rest, added, final => by
      refine ⟨?_, consistent_of_final rest (pushed candidate added) final⟩
      obtain ⟨observer, solution, solved⟩ := final
      have parts := (Frames.models_append (X := frames levels) solution _ _).mp solved
      have addition : (frames levels).Models solution
          ((frames levels).applyStore rest.toLast (pushed candidate added)) := by
        rw [← transmitted_refinement]
        exact parts.1
      have beforeAdded := (Frames.models_applyStore (X := frames levels) rest.toLast solution _).mp addition
      have beforeKnown := rest.models_start solution parts.2
      exact ⟨observer, solution ≫ rest.toLast,
        (Frames.models_append (X := frames levels) _ _ _).mpr ⟨beforeAdded, beforeKnown⟩⟩

theorem final_of_consistent : ∀ {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (added : EquationStore (TotalTerm state.frame)), RunConsistent run added → run.word ≠ [] → FinalConsistent run added
  | _, .nil _, _, _, nonempty => False.elim (nonempty rfl)
  | _, .cons _ _ (.nil _), _, consistent, _ => consistent.1
  | _, .cons candidate _ (.cons next accepted rest), added, consistent, _ =>
      final_of_consistent (.cons next accepted rest) (pushed candidate added) consistent.2 (by simp [Step.Run.word])

theorem consistent_iff {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (nonempty : run.word ≠ []) (added : EquationStore (TotalTerm state.frame)) :
    RunConsistent run added ↔ FinalConsistent run added :=
  ⟨fun consistent => final_of_consistent run added consistent nonempty, consistent_of_final run added⟩

def OverStart {state : State rules O} {first second : (helperStep levels O).toStep.Run state}
    (map : PlainIso levels first.last second.last) : Prop := map.frame.hom ≫ first.toLast = second.toLast

theorem additions_correspond {state : State rules O} {first second : (helperStep levels O).toStep.Run state}
    (map : PlainIso levels first.last second.last) (overStart : OverStart map)
    (added : EquationStore (TotalTerm state.frame)) :
    (frames levels).applyStore map.frame.hom (transmitted first added) = transmitted second added := by
  rw [transmitted_refinement, transmitted_refinement, applyStore_applyStore, overStart]

def strengthenedEndpoints {state : State rules O} {first second : (helperStep levels O).toStep.Run state}
    (map : PlainIso levels first.last second.last) (overStart : OverStart map)
    (added : EquationStore (TotalTerm state.frame)) :
    PlainIso levels (strengthen first.last (transmitted first added))
      (strengthen second.last (transmitted second added)) :=
  comparison map _ _ (by rw [additions_correspond map overStart added]; exact fun _ _ => Iff.rfl)

theorem final_consistency_iff {state : State rules O} {first second : (helperStep levels O).toStep.Run state}
    (map : PlainIso levels first.last second.last) (overStart : OverStart map)
    (added : EquationStore (TotalTerm state.frame)) : FinalConsistent first added ↔ FinalConsistent second added :=
  (strengthenedEndpoints map overStart added).toStateIso.solvable_iff

theorem licenses_correspond {state : State rules O} {first second : (helperStep levels O).toStep.Run state}
    (map : PlainIso levels first.last second.last) (overStart : OverStart map)
    (nonempty : first.word ≠ []) (nonempty' : second.word ≠ [])
    (added : EquationStore (TotalTerm state.frame)) : RunConsistent first added ↔ RunConsistent second added :=
  (consistent_iff first nonempty added).trans
    ((final_consistency_iff map overStart added).trans (consistent_iff second nonempty' added).symm)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange.consistent_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange.licenses_correspond
