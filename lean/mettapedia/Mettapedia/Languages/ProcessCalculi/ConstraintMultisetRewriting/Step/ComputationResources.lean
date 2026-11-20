import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFull

/-!
# Linear publication used by computational firings

An active typed row is consumed and its replacement is published at a fresh
occurrence. The only new equation is the reflexive match of the consumed row
with itself. This module establishes the actual full-step resource operation;
the source computational rule and its scope are supplied by a separate profile.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationResources

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head L O : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  (levels : LevelModel rules L)

def firing (state : State rules O) (source target : O) (output : TotalTerm state.frame) :
    Firing levels state :=
  ⟨.nil state.frame, [source], [], [state.label source], [],
    [(target, Make.ofRow output)], [], [], []⟩

theorem row (state : State rules O) (source target occurrence : O) (output : TotalTerm state.frame) :
    (firing levels state source target output).row occurrence = state.label occurrence :=
  reindex_id _

theorem information (state : State rules O) (source target : O) (output : TotalTerm state.frame) :
    (firing levels state source target output).information =
      state.knowledge ++ [(state.label source, state.label source)] := by
  change (frames levels).applyStore ((frames levels).id state.frame) state.knowledge ++
      [(state.label source, (frames levels).act ((frames levels).id state.frame) (state.label source))] ++
      ([] : EquationStore (TotalTerm state.frame)) ++ ([] : EquationStore (TotalTerm state.frame)) = _
  rw [Frames.applyStore_id (X := frames levels), (frames levels).act_id]
  simp only [List.append_nil]

theorem models_information (state : State rules O) (source target : O) (output : TotalTerm state.frame)
    {observer : Context rules} (solution : observer ⟶ state.frame) :
    (frames levels).Models solution (firing levels state source target output).information ↔
      (frames levels).Models solution state.knowledge := by
  rw [information, Frames.models_append]
  have reflexive : (frames levels).Models solution [(state.label source, state.label source)] := by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    exact ((frames levels).equivalence observer).refl _
  exact and_iff_left reflexive

theorem solvable_information (state : State rules O) (source target : O) (output : TotalTerm state.frame) :
    (frames levels).Solvable (firing levels state source target output).information ↔
      (frames levels).Solvable state.knowledge := by
  constructor <;> rintro ⟨observer, solution, models⟩
  · exact ⟨observer, solution, (models_information levels state source target output solution).mp models⟩
  · exact ⟨observer, solution, (models_information levels state source target output solution).mpr models⟩

theorem shapes (state : State rules O) (source target : O) (output : TotalTerm state.frame) :
    (firing levels state source target output).Shapes := by
  refine ⟨by simp [firing], by simp [Firing.made, firing], rfl, rfl, ?_⟩
  intro made member
  obtain rfl := List.mem_singleton.mp member
  exact Make.ofRow_wellTyped output

variable [DecidableEq O]

theorem admitted_iff (state : State rules O) (source target : O) (output : TotalTerm state.frame) :
    (step levels O).Admits (firing levels state source target output) ↔
      source ∈ state.present ∧ target ∉ state.present ∧ (frames levels).Solvable state.knowledge := by
  have noGuards : (frames levels).Entails (firing levels state source target output).information
      (fun _ solution => (frames levels).Models solution (firing levels state source target output).guards) :=
    fun _ _ _ => Frames.models_nil _
  have noQueries : ∀ q ∈ (firing levels state source target output).queries,
      (frames levels).Entails (firing levels state source target output).information
        (fun _ solution => q.Holds state.present (firing levels state source target output).row solution) := by
    intro query member
    exact False.elim (List.not_mem_nil member)
  constructor
  · intro accepted
    have parts := (DependentFull.admits_iff (firing levels state source target output)).mp accepted
    refine ⟨parts.2.1.1 source (List.mem_singleton_self _),
      parts.2.1.2.2.2 target (by simp [firing, Firing.made]), ?_⟩
    exact (solvable_information levels state source target output).mp parts.2.2.1
  · rintro ⟨present, fresh, solvable⟩
    apply (DependentFull.admits_iff (firing levels state source target output)).mpr
    refine ⟨shapes levels state source target output, ?_,
      (solvable_information levels state source target output).mpr solvable, noGuards, noQueries⟩
    simp [firing, Firing.made, present, fresh]

theorem result_frame (state : State rules O) (source target : O) (output : TotalTerm state.frame)
    (accepted : (step levels O).Admits (firing levels state source target output)) :
    ((step levels O).toStep.result (firing levels state source target output) accepted).frame = state.frame := rfl

theorem result_knowledge (state : State rules O) (source target : O) (output : TotalTerm state.frame)
    (accepted : (step levels O).Admits (firing levels state source target output)) :
    ((step levels O).toStep.result (firing levels state source target output) accepted).knowledge =
      state.knowledge ++ [(state.label source, state.label source)] :=
  information levels state source target output

theorem result_label (state : State rules O) (source target : O) (output : TotalTerm state.frame)
    (accepted : (step levels O).Admits (firing levels state source target output)) :
    ((step levels O).toStep.result (firing levels state source target output) accepted).label target = output := by
  change relabel (firing levels state source target output).row
    (firing levels state source target output).makes accepted.1.2.2.2.2 target = output
  simp only [firing, relabel]
  rfl

theorem other_label (state : State rules O) (source target occurrence : O) (output : TotalTerm state.frame)
    (accepted : (step levels O).Admits (firing levels state source target output)) (other : occurrence ≠ target) :
    ((step levels O).toStep.result (firing levels state source target output) accepted).label occurrence =
      state.label occurrence := by
  exact ((firing levels state source target output).label_after_of_not_mem accepted
    (by simpa [firing, Firing.made] using other)).trans (row levels state source target occurrence output)

theorem result_present (state : State rules O) (source target : O) (output : TotalTerm state.frame)
    (accepted : (step levels O).Admits (firing levels state source target output)) :
    ((step levels O).toStep.result (firing levels state source target output) accepted).present =
      (state.present \ {source}) ∪ {target} := rfl

theorem target_present (state : State rules O) (source target : O) (output : TotalTerm state.frame)
    (accepted : (step levels O).Admits (firing levels state source target output)) :
    target ∈ ((step levels O).toStep.result (firing levels state source target output) accepted).present := by
  rw [result_present]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

theorem result_models (state : State rules O) (source target : O) (output : TotalTerm state.frame)
    (accepted : (step levels O).Admits (firing levels state source target output))
    {observer : Context rules} (solution : observer ⟶ state.frame) :
    (frames levels).Models solution
        ((step levels O).toStep.result (firing levels state source target output) accepted).knowledge ↔
      (frames levels).Models solution state.knowledge :=
  models_information levels state source target output solution

theorem result_consistent (state : State rules O) (source target : O) (output : TotalTerm state.frame)
    (accepted : (step levels O).Admits (firing levels state source target output)) :
    (frames levels).Solvable
      ((step levels O).toStep.result (firing levels state source target output) accepted).knowledge :=
  (step levels O).toStep.solvable_information accepted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationResources

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationResources.admitted_iff
