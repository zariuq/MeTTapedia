import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementBlocks

/-! # Right-hand prepared effects and their native result correspondence -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacement

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]
  {left right : Helpers.State S O} (place : ContextPlacement left right)

theorem right_information (g : Helpers.Firing right) :
    (place.rightFiring g).information = (place.afterRight g).state.knowledge := by
  have carried := place.swap.transport_left_information g
  change (Frames.contextual S).applyStore (lift place.rightMap g.helper) g.information =
    (Frames.contextual S).applyStore (incl place.frame g.helper)
      ((Frames.contextual S).applyStore place.rightMap right.knowledge) ++ [(place.rightFiring g).tell] at carried
  change (Frames.contextual S).applyStore (incl place.frame g.helper)
      ((Frames.contextual S).applyStore place.leftMap left.knowledge ++
        (Frames.contextual S).applyStore place.rightMap right.knowledge) ++ [(place.rightFiring g).tell] =
    (Frames.contextual S).applyStore (Assignment.compose (incl place.frame g.helper) place.leftMap) left.knowledge ++
      (Frames.contextual S).applyStore (lift place.rightMap g.helper) g.information
  have old : (Frames.contextual S).applyStore (Assignment.compose (incl place.frame g.helper) place.leftMap) left.knowledge =
      (Frames.contextual S).applyStore (incl place.frame g.helper)
        ((Frames.contextual S).applyStore place.leftMap left.knowledge) :=
    (Frames.applyStore_applyStore (X := Frames.contextual S) place.leftMap (incl place.frame g.helper) left.knowledge).symm
  rw [carried, old, Frames.applyStore_append, List.append_assoc]

def right_result_iso (g : Helpers.Firing right) :
    helperStep.StateIso (place.rightFiring g).after (place.afterRight g).state where
  frame := Frames.Iso.refl _
  knowledge := (Frames.Iso.equivalent_refl _).trans (by
    change (Frames.contextual S).Equivalent (place.rightFiring g).information (place.afterRight g).state.knowledge
    rw [place.right_information g]
    exact fun _ _ => Iff.rfl)
  rename := Equiv.refl O
  present := by
    simp only [Equiv.refl_toEmbedding, Finset.map_refl]
    change MeTTaCalculus.OccurrenceCommits.fire (left.present ∪ right.present) (g.selection.commit (T := Unit)) =
      left.present ∪ MeTTaCalculus.OccurrenceCommits.fire right.present (g.selection.commit (T := Unit))
    simp [MeTTaCalculus.OccurrenceCommits.fire, Helpers.Firing.selection, Selection.commit, Finset.union_assoc]

theorem move_from_swap (g : Helpers.Firing right) :
    helperTransport.move place.swapIso (place.swap.leftFiring g) = place.rightFiring g := by
  exact Firing.mk_congr _ _ (instantiate_identity _) (Frames.applyStore_id _)

theorem right_after_left_residual (f : Helpers.Firing left) (g : Helpers.Firing right)
    (allowed : helperStep.Admits (s := place.state) (place.leftFiring f)) :
    helperTransport.move (helperTransport.symm (place.left_result_iso f)) ((place.afterLeft f).rightFiring g) =
      helperTransport.residual (place.leftFiring f) allowed (place.rightFiring g) := by
  apply Firing.mk_congr _ _
  · change instantiate (generator (extend place.frame f.helper).arity)
      (instantiate (Assignment.compose (incl place.frame f.helper) place.rightMap) g.value) =
        instantiate (helperStep.along (place.leftFiring f) allowed) (instantiate place.rightMap g.value)
    rw [instantiate_identity, along_eq]
    exact Assignment.instantiate_compose _ _ _
  · change (Frames.contextual S).applyStore ((Frames.contextual S).id (extend place.frame f.helper))
      ((Frames.contextual S).applyStore ((Frames.contextual S).comp (incl place.frame f.helper) place.rightMap) g.guards) =
        (Frames.contextual S).applyStore (helperStep.along (place.leftFiring f) allowed)
          ((Frames.contextual S).applyStore place.rightMap g.guards)
    rw [Frames.applyStore_id, along_eq]
    exact (Frames.applyStore_applyStore (X := Frames.contextual S) place.rightMap (incl place.frame f.helper) g.guards).symm

theorem left_after_right_residual (f : Helpers.Firing left) (g : Helpers.Firing right)
    (allowed : helperStep.Admits (s := place.state) (place.rightFiring g)) :
    helperTransport.move (helperTransport.symm (place.right_result_iso g)) ((place.afterRight g).leftFiring f) =
      helperTransport.residual (place.rightFiring g) allowed (place.leftFiring f) := by
  apply Firing.mk_congr _ _
  · change instantiate (generator (extend place.frame g.helper).arity)
      (instantiate (Assignment.compose (incl place.frame g.helper) place.leftMap) f.value) =
        instantiate (helperStep.along (place.rightFiring g) allowed) (instantiate place.leftMap f.value)
    rw [instantiate_identity, along_eq]
    exact Assignment.instantiate_compose _ _ _
  · change (Frames.contextual S).applyStore ((Frames.contextual S).id (extend place.frame g.helper))
      ((Frames.contextual S).applyStore ((Frames.contextual S).comp (incl place.frame g.helper) place.leftMap) f.guards) =
        (Frames.contextual S).applyStore (helperStep.along (place.rightFiring g) allowed)
          ((Frames.contextual S).applyStore place.leftMap f.guards)
    rw [Frames.applyStore_id, along_eq]
    exact (Frames.applyStore_applyStore (X := Frames.contextual S) place.leftMap (incl place.frame g.helper) f.guards).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.ContextPlacement
