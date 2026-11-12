import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextPlacement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Transport

/-!
# Result correspondence for a step in a placed helper context

The fresh helper extends the local-to-joint assignment, while the other
context is carried through the joint inclusion. The actual native result and
the resulting placement are isomorphic. Knowledge append order is compared
semantically; occurrence identities are preserved literally.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacement

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]
  {left right : Helpers.State S O} (placed : ContextPlacement left right)

abbrev leftFiring (f : Helpers.Firing left) : Helpers.Firing placed.state := f.move placed.leftMap

abbrev afterLeft (f : Helpers.Firing left) : ContextPlacement f.after right where
  frame := extend placed.frame f.helper
  leftMap := lift placed.leftMap f.helper
  rightMap := Assignment.compose (incl placed.frame f.helper) placed.rightMap

theorem transport_left_tell (f : Helpers.Firing left) :
    (Frames.contextual S).applyStore (lift placed.leftMap f.helper) [f.tell] =
      [(placed.leftFiring f).tell] := by
  have value : instantiate (lift placed.leftMap f.helper) (instantiate (incl left.frame f.helper) f.value) =
      instantiate (incl placed.frame f.helper) (instantiate placed.leftMap f.value) :=
    (Assignment.instantiate_compose _ _ _).symm.trans
      ((congrArg (fun assignment => instantiate assignment f.value)
        (compose_lift_incl placed.leftMap f.helper)).trans (Assignment.instantiate_compose _ _ _))
  change [(observe (instantiate (lift placed.leftMap f.helper) (fresh left.frame f.helper)),
      observe (instantiate (lift placed.leftMap f.helper) (instantiate (incl left.frame f.helper) f.value)))] = _
  rw [instantiate_lift_fresh, value]
  rfl

theorem transport_left_information (f : Helpers.Firing left) :
    (Frames.contextual S).applyStore (lift placed.leftMap f.helper) f.information =
      (Frames.contextual S).applyStore (incl placed.frame f.helper)
        ((Frames.contextual S).applyStore placed.leftMap left.knowledge) ++ [(placed.leftFiring f).tell] := by
  rw [Helpers.Firing.information, Frames.applyStore_append, placed.transport_left_tell]
  rw [Frames.applyStore_applyStore, Frames.applyStore_applyStore]
  exact congrArg (fun assignment => (Frames.contextual S).applyStore assignment left.knowledge ++
    [(placed.leftFiring f).tell]) (compose_lift_incl placed.leftMap f.helper)

theorem left_information_equivalent (f : Helpers.Firing left) :
    (Frames.contextual S).Equivalent (placed.leftFiring f).information (placed.afterLeft f).state.knowledge := by
  change (Frames.contextual S).Equivalent
    ((Frames.contextual S).applyStore (incl placed.frame f.helper)
      ((Frames.contextual S).applyStore placed.leftMap left.knowledge ++
        (Frames.contextual S).applyStore placed.rightMap right.knowledge) ++ [(placed.leftFiring f).tell])
    ((Frames.contextual S).applyStore (lift placed.leftMap f.helper) f.information ++
      (Frames.contextual S).applyStore (Assignment.compose (incl placed.frame f.helper) placed.rightMap) right.knowledge)
  rw [Frames.applyStore_append, placed.transport_left_information]
  have context : (Frames.contextual S).applyStore
      (Assignment.compose (incl placed.frame f.helper) placed.rightMap) right.knowledge =
      (Frames.contextual S).applyStore (incl placed.frame f.helper)
        ((Frames.contextual S).applyStore placed.rightMap right.knowledge) :=
    (Frames.applyStore_applyStore (X := Frames.contextual S) placed.rightMap
      (incl placed.frame f.helper) right.knowledge).symm
  rw [context]
  apply Frames.equivalent_of_mem_iff
  intro equation
  simp only [List.mem_append]
  tauto

def left_result_iso (f : Helpers.Firing left) :
    helperStep.StateIso (placed.leftFiring f).after (placed.afterLeft f).state where
  frame := Frames.Iso.refl _
  knowledge := (Frames.Iso.equivalent_refl _).trans (placed.left_information_equivalent f)
  rename := Equiv.refl O
  present := by
    simp only [Equiv.refl_toEmbedding, Finset.map_refl]
    change MeTTaCalculus.OccurrenceCommits.fire (left.present ∪ right.present) (f.selection.commit (T := Unit)) =
      MeTTaCalculus.OccurrenceCommits.fire left.present (f.selection.commit (T := Unit)) ∪ right.present
    exact MeTTaCalculus.OccurrenceCommits.fire_union_frame (by simp [Helpers.Firing.selection, Selection.commit])

theorem left_prepares_of_admitted (f : Helpers.Firing left)
    (allowed : helperStep.Admits (s := placed.state) (placed.leftFiring f)) : helperStep.Prepares f := by
  obtain ⟨solvedJoint, fresh, _, _⟩ := (placed.left_admission_iff f).mp allowed
  obtain ⟨target, mapping, solved⟩ := solvedJoint
  have old : (Frames.contextual S).Solvable left.knowledge :=
    ⟨target, Assignment.compose mapping placed.leftMap, placed.models_left mapping solved⟩
  exact ⟨List.nodup_singleton _, (enabled_iff f).mpr fresh, information_solvable f old⟩

def admitted_left_result_iso (f : Helpers.Firing left)
    (allowed : helperStep.Admits (s := placed.state) (placed.leftFiring f)) :
    helperStep.StateIso (helperStep.result (placed.leftFiring f) allowed) (placed.afterLeft f).state :=
  placed.left_result_iso f

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacement
