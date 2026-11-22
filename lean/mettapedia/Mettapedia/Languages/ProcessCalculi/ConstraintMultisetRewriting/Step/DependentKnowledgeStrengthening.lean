import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentCanonicalDiamond
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextResidual

/-!
# Actual dependent firings under stronger knowledge

Adding equations retains the frame, occurrences and typed rows. For an
already admitted firing, admission after strengthening is equivalent to
solvability of the enlarged information: its guards already hold on every
old solution, hence on the remaining solutions. Absence and count queries
are included; no query-blindness condition is added.

The complete result transports the added equations along the actual helper
weakening. State comparisons require the added equations to correspond at
every solution, separately from equivalence of the old knowledge.
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

def strengthen (state : State rules O) (added : EquationStore (TotalTerm state.frame)) : State rules O :=
  {state with knowledge := added ++ state.knowledge}

def firing {state : State rules O} (added : EquationStore (TotalTerm state.frame))
    (candidate : HelperFiring levels O state) : HelperFiring levels O (strengthen state added) :=
  ⟨candidate.helpers, candidate.data⟩

def pushed {state : State rules O} (candidate : HelperFiring levels O state)
    (added : EquationStore (TotalTerm state.frame)) : EquationStore (TotalTerm candidate.helpers.frame) :=
  (frames levels).applyStore candidate.helpers.weaken added

omit [DecidableEq O] in
theorem information {state : State rules O} (added : EquationStore (TotalTerm state.frame))
    (candidate : HelperFiring levels O state) :
    (firing added candidate).toFiring.information = pushed candidate added ++ candidate.toFiring.information := by
  change ((frames levels).applyStore candidate.helpers.weaken (added ++ state.knowledge) ++
    candidate.toFiring.matching candidate.toFiring.takes candidate.toFiring.taken ++
    candidate.toFiring.matching candidate.toFiring.reads candidate.toFiring.read ++ candidate.toFiring.tells) = _
  simp only [pushed, Firing.information, Frames.applyStore, List.map_append, List.append_assoc]

omit [DecidableEq O] in
theorem holds {state : State rules O} (added : EquationStore (TotalTerm state.frame))
    (candidate : HelperFiring levels O state) {observer : Context rules}
    (solution : observer ⟶ candidate.helpers.frame) :
    (firing added candidate).toFiring.Holds solution ↔ candidate.toFiring.Holds solution := Iff.rfl

theorem admits_iff {state : State rules O} (added : EquationStore (TotalTerm state.frame))
    (candidate : HelperFiring levels O state) (accepted : (helperStep levels O).Admits candidate) :
    (helperStep levels O).Admits (firing added candidate) ↔
      (frames levels).Solvable (pushed candidate added ++ candidate.toFiring.information) := by
  constructor
  · intro admitted
    have solved := admitted.2.2.1
    rwa [information] at solved
  · intro solvable
    refine ⟨accepted.1, accepted.2.1, ?_, ?_⟩
    · rwa [information]
    · intro observer solution solved
      rw [information] at solved
      exact accepted.2.2.2 observer solution ((Frames.models_append _ _ _).mp solved).2

theorem result {state : State rules O} (added : EquationStore (TotalTerm state.frame))
    (candidate : HelperFiring levels O state) (accepted : (helperStep levels O).Admits candidate)
    (consistent : (frames levels).Solvable (pushed candidate added ++ candidate.toFiring.information)) :
    (helperStep levels O).result (firing added candidate) ((admits_iff added candidate accepted).mpr consistent) =
      strengthen ((helperStep levels O).result candidate accepted) (pushed candidate added) := by
  change (⟨candidate.helpers.frame, (firing added candidate).toFiring.information,
    MeTTaCalculus.OccurrenceCommits.fire state.present (candidate.toFiring.selection.commit (T := Unit)),
    relabel candidate.toFiring.row candidate.toFiring.makes accepted.1.2.2.2.2⟩ : State rules O) =
      ⟨candidate.helpers.frame, pushed candidate added ++ candidate.toFiring.information,
        MeTTaCalculus.OccurrenceCommits.fire state.present (candidate.toFiring.selection.commit (T := Unit)),
        relabel candidate.toFiring.row candidate.toFiring.makes accepted.1.2.2.2.2⟩
  rw [information]

def comparison {source target : State rules O} (map : PlainIso levels source target)
    (sourceAdded : EquationStore (TotalTerm source.frame)) (targetAdded : EquationStore (TotalTerm target.frame))
    (compatible : (frames levels).Equivalent ((frames levels).applyStore map.frame.hom sourceAdded) targetAdded) :
    PlainIso levels (strengthen source sourceAdded) (strengthen target targetAdded) where
  frame := map.frame
  knowledge := by
    intro observer solution
    change observer ⟶ target.frame at solution
    change (frames levels).Models solution ((frames levels).applyStore map.frame.hom (sourceAdded ++ source.knowledge)) ↔
      (frames levels).Models solution (targetAdded ++ target.knowledge)
    have distribution : (frames levels).applyStore map.frame.hom (sourceAdded ++ source.knowledge) =
        (frames levels).applyStore map.frame.hom sourceAdded ++ (frames levels).applyStore map.frame.hom source.knowledge :=
      List.map_append
    rw [distribution, Frames.models_append, Frames.models_append]
    exact and_congr (compatible observer solution) (map.knowledge observer solution)
  present := map.present
  label := map.label

omit [DecidableEq O] in
theorem composition (state : State rules O) (first second : EquationStore (TotalTerm state.frame)) :
    strengthen (strengthen state first) second = strengthen state (second ++ first) :=
  congrArg (fun knowledge => ({state with knowledge := knowledge} : State rules O))
    (List.append_assoc second first state.knowledge).symm

theorem residual {state : State rules O} (added : EquationStore (TotalTerm state.frame))
    (first second : HelperFiring levels O state) (accepted : (helperStep levels O).Admits first)
    (consistent : (frames levels).Solvable (pushed first added ++ first.toFiring.information)) :
    helperResidual (firing added first) ((admits_iff added first accepted).mpr consistent) (firing added second) =
      (result added first accepted consistent).symm ▸ firing (pushed first added) (helperResidual first accepted second) := by
  apply ContextPlacement.payload_injective
  exact (eq_of_heq (ContextPlacement.payload_cast (result added first accepted consistent).symm
    (firing (pushed first added) (helperResidual first accepted second)))).symm

theorem along {state : State rules O} (candidate : HelperFiring levels O state)
    (accepted : (helperStep levels O).Admits candidate) :
    (helperStep levels O).toStep.along candidate accepted = candidate.helpers.weaken := by
  change (𝟙 candidate.helpers.frame) ≫ candidate.helpers.weaken = candidate.helpers.weaken
  exact Category.id_comp _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange.admits_iff
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.KnowledgeChange.result
