import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentKnowledgeStrengthening

/-!
# Complete executions under consistent knowledge strengthening

The local license checks only solvability of each enlarged information
store. It composes along execution. The constructed run preserves every
selection and its actual refinement map; its final state contains exactly
the original typed rows and the transported additional equations.
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

def transmitted : {state : State rules O} → (run : (helperStep levels O).toStep.Run state) →
    EquationStore (TotalTerm state.frame) → EquationStore (TotalTerm run.last.frame)
  | _, .nil _, added => added
  | _, .cons candidate _ rest, added => transmitted rest (pushed candidate added)

def RunConsistent : {state : State rules O} → (run : (helperStep levels O).toStep.Run state) →
    EquationStore (TotalTerm state.frame) → Prop
  | _, .nil _, _ => True
  | _, .cons candidate _ rest, added =>
      (frames levels).Solvable (pushed candidate added ++ candidate.toFiring.information) ∧
        RunConsistent rest (pushed candidate added)

def liftRun : {state : State rules O} → (run : (helperStep levels O).toStep.Run state) →
    (added : EquationStore (TotalTerm state.frame)) → RunConsistent run added →
      (helperStep levels O).toStep.Run (strengthen state added)
  | _, .nil state, added, _ => .nil (strengthen state added)
  | _, .cons candidate accepted rest, added, consistent =>
      .cons (firing added candidate) ((admits_iff added candidate accepted).mpr consistent.1)
        ((result added candidate accepted consistent.1).symm ▸ liftRun rest (pushed candidate added) consistent.2)

theorem liftRun_last : ∀ {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (added : EquationStore (TotalTerm state.frame)) (consistent : RunConsistent run added),
    (liftRun run added consistent).last = strengthen run.last (transmitted run added)
  | _, .nil _, _, _ => rfl
  | _, .cons candidate accepted rest, added, consistent => by
      simp only [liftRun, Step.Run.last, Step.Run.last_cast]
      exact liftRun_last rest (pushed candidate added) consistent.2

theorem transmitted_refinement : ∀ {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (added : EquationStore (TotalTerm state.frame)),
    transmitted run added = (frames levels).applyStore run.toLast added
  | state, .nil _, added => (Frames.applyStore_id (X := frames levels) added).symm
  | _, .cons candidate accepted rest, added => by
      change transmitted rest (pushed candidate added) = _
      rw [transmitted_refinement rest, pushed, applyStore_applyStore]
      change (frames levels).applyStore (rest.toLast ≫ candidate.helpers.weaken) added =
        (frames levels).applyStore (rest.toLast ≫ (helperStep levels O).toStep.along candidate accepted) added
      rw [along]

theorem consistent_append : ∀ {state : State rules O} (early : (helperStep levels O).toStep.Run state)
    (later : (helperStep levels O).toStep.Run early.last) (added : EquationStore (TotalTerm state.frame)),
    RunConsistent (early.append later) added ↔ RunConsistent early added ∧ RunConsistent later (transmitted early added)
  | _, .nil _, _, _ => ⟨fun valid => ⟨True.intro, valid⟩, fun valid => valid.2⟩
  | _, .cons candidate _ rest, later, added =>
      (and_congr Iff.rfl (consistent_append rest later (pushed candidate added))).trans and_assoc.symm

theorem selections : ∀ {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (added : EquationStore (TotalTerm state.frame)) (consistent : RunConsistent run added),
    (liftRun run added consistent).word.map (fun event => event.2.toFiring.selection) =
      run.word.map (fun event => event.2.toFiring.selection)
  | _, .nil _, _, _ => rfl
  | _, .cons candidate accepted rest, added, consistent => by
      simp only [liftRun, Step.Run.word, Step.Run.word_cast, List.map_cons]
      exact congrArg (List.cons candidate.toFiring.selection) (selections rest (pushed candidate added) consistent.2)

theorem refinement : ∀ {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (added : EquationStore (TotalTerm state.frame)) (consistent : RunConsistent run added),
    ContextPlacement.refinement (liftRun run added consistent) = ContextPlacement.refinement run
  | _, .nil _, _, _ => rfl
  | _, .cons candidate accepted rest, added, consistent => by
      have castMap := eq_of_heq (ContextPlacement.refinement_cast (result added candidate accepted consistent.1).symm
        (liftRun rest (pushed candidate added) consistent.2))
      have tailMap := castMap.trans (refinement rest (pushed candidate added) consistent.2)
      exact congrArg (fun data : Σ target : Context rules, target ⟶ candidate.helpers.frame =>
        (⟨data.1, data.2 ≫ (helperStep levels O).toStep.along candidate accepted⟩ :
          Σ target : Context rules, target ⟶ _)) tailMap

def typedRows (state : State rules O) : Σ frame : Context rules, O → TotalTerm frame := ⟨state.frame, state.label⟩

theorem rows_unchanged {state : State rules O} (run : (helperStep levels O).toStep.Run state)
    (added : EquationStore (TotalTerm state.frame)) (consistent : RunConsistent run added) :
    typedRows (liftRun run added consistent).last = typedRows run.last := by
  have same := congrArg typedRows (liftRun_last run added consistent)
  exact same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange.liftRun_last
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange.refinement
