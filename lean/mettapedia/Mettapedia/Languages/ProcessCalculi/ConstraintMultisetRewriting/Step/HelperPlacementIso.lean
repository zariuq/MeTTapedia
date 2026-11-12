import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextSquares
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ContextualRunNaturality

/-!
# Isomorphic helper placements retain both source embeddings

The frame isomorphism commutes with the two assignments. Joint knowledge is
therefore transported semantically and occurrence identities are fixed. The
relation lifts through declaration extension and satisfies the shared local
transport contract used to construct complete contextual runs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily

variable {S : Signature} {O : Type} [DecidableEq O]

structure PlacementIso {left right : State S O} (p q : ContextPlacement left right) where
  frame : (Frames.contextual S).Iso p.frame q.frame
  left_map : Assignment.compose frame.hom p.leftMap = q.leftMap
  right_map : Assignment.compose frame.hom p.rightMap = q.rightMap

namespace PlacementIso

variable {left right : State S O} {p q z : ContextPlacement left right}

def toStateIso (mapping : PlacementIso p q) : helperStep.StateIso p.state q.state where
  frame := mapping.frame
  knowledge := by
    have leftMap : (Frames.contextual S).comp mapping.frame.hom p.leftMap = q.leftMap := mapping.left_map
    have rightMap : (Frames.contextual S).comp mapping.frame.hom p.rightMap = q.rightMap := mapping.right_map
    change (Frames.contextual S).Equivalent
      ((Frames.contextual S).applyStore mapping.frame.hom
        ((Frames.contextual S).applyStore p.leftMap left.knowledge ++
          (Frames.contextual S).applyStore p.rightMap right.knowledge))
      ((Frames.contextual S).applyStore q.leftMap left.knowledge ++
        (Frames.contextual S).applyStore q.rightMap right.knowledge)
    rw [Frames.applyStore_append, Frames.applyStore_applyStore, Frames.applyStore_applyStore, leftMap, rightMap]
    exact fun _ _ => Iff.rfl
  rename := Equiv.refl O
  present := by simp only [Equiv.refl_toEmbedding, Finset.map_refl]

def refl (p : ContextPlacement left right) : PlacementIso p p where
  frame := Frames.Iso.refl _
  left_map := by funext name; exact instantiate_identity _
  right_map := by funext name; exact instantiate_identity _

def symm (mapping : PlacementIso p q) : PlacementIso q p where
  frame := mapping.frame.symm
  left_map := by
    funext name
    have same := congrFun mapping.left_map name
    change instantiate mapping.frame.hom (p.leftMap name) = q.leftMap name at same
    change instantiate mapping.frame.inv (q.leftMap name) = p.leftMap name
    rw [← same, ← Assignment.instantiate_compose, compose_inv_hom, instantiate_identity]
  right_map := by
    funext name
    have same := congrFun mapping.right_map name
    change instantiate mapping.frame.hom (p.rightMap name) = q.rightMap name at same
    change instantiate mapping.frame.inv (q.rightMap name) = p.rightMap name
    rw [← same, ← Assignment.instantiate_compose, compose_inv_hom, instantiate_identity]

def trans (first : PlacementIso p q) (second : PlacementIso q z) : PlacementIso p z where
  frame := first.frame.trans second.frame
  left_map := by
    funext name
    change instantiate (Assignment.compose second.frame.hom first.frame.hom) (p.leftMap name) = z.leftMap name
    rw [Assignment.instantiate_compose]
    have same := congrFun first.left_map name
    change instantiate first.frame.hom (p.leftMap name) = q.leftMap name at same
    rw [same]
    exact congrFun second.left_map name
  right_map := by
    funext name
    change instantiate (Assignment.compose second.frame.hom first.frame.hom) (p.rightMap name) = z.rightMap name
    rw [Assignment.instantiate_compose]
    have same := congrFun first.right_map name
    change instantiate first.frame.hom (p.rightMap name) = q.rightMap name at same
    rw [same]
    exact congrFun second.right_map name

def swap (mapping : PlacementIso p q) : PlacementIso p.swap q.swap :=
  ⟨mapping.frame, mapping.right_map, mapping.left_map⟩

def afterLeft (mapping : PlacementIso p q) (f : Firing left) : PlacementIso (p.afterLeft f) (q.afterLeft f) where
  frame := liftIso mapping.frame f.helper
  left_map := by
    change Assignment.compose (lift mapping.frame.hom f.helper) (lift p.leftMap f.helper) = lift q.leftMap f.helper
    rw [lift_compose, mapping.left_map]
  right_map := by
    funext name
    change instantiate (lift mapping.frame.hom f.helper) (instantiate (incl p.frame f.helper) (p.rightMap name)) =
      instantiate (incl q.frame f.helper) (q.rightMap name)
    rw [← Assignment.instantiate_compose, compose_lift_incl, Assignment.instantiate_compose]
    have same := congrFun mapping.right_map name
    change instantiate mapping.frame.hom (p.rightMap name) = q.rightMap name at same
    rw [same]

theorem candidate (mapping : PlacementIso p q) (f : Firing left) :
    helperTransport.move mapping.toStateIso (p.leftFiring f) = q.leftFiring f := by
  apply Firing.mk_congr _ _
  · exact (Assignment.instantiate_compose mapping.frame.hom p.leftMap f.value).symm.trans
      (congrArg (fun assignment => instantiate assignment f.value) mapping.left_map)
  · have same : (Frames.contextual S).comp mapping.frame.hom p.leftMap = q.leftMap := mapping.left_map
    exact (Frames.applyStore_applyStore (X := Frames.contextual S) p.leftMap mapping.frame.hom f.guards).trans
      (congrArg (fun assignment => (Frames.contextual S).applyStore assignment f.guards) same)

end PlacementIso

abbrev placementTransport : (contextualRunInterpretation (S := S) (O := O)).PlacementTransport where
  Map := PlacementIso
  iso := PlacementIso.toStateIso
  candidate mapping f := mapping.candidate f
  domain _ _ framed := framed
  advance mapping f _ := mapping.afterLeft f

abbrev placementFlipCompatible : (placementTransport (S := S) (O := O)).FlipCompatible contextualFlip where
  map := PlacementIso.swap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
