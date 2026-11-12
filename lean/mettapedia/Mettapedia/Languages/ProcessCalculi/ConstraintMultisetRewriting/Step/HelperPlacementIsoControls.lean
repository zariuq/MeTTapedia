import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperPlacementIso
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextResultControls

/-!
# Native state equality does not fix embedded source meanings

The same unconstrained native state admits both interpretations. Their left
source maps agree, but their right variables denote different native names.
An identity transport fails candidate covariance; the nonidentity declaration
swap satisfies both source-map laws. Exchanging roles tests the other map.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.PlacementIsoControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers.Consumer (tiny empty first constant)

def bare : State tiny Nat := ⟨ContextResultControls.oldFrame, [], ∅⟩
def targetFrame := extend ContextResultControls.oldFrame first.helper

def fixedLeft : Assignment bare.frame.arity targetFrame.arity
  | .inl impossible => impossible.elim
  | .inr () => constant 7

abbrev p : ContextPlacement bare bare := ⟨targetFrame, fixedLeft, incl bare.frame first.helper⟩
abbrev q : ContextPlacement bare bare := ⟨targetFrame, fixedLeft, fun name => match name with
  | .inl impossible => impossible.elim
  | .inr () => fresh bare.frame first.helper⟩

theorem native_states_equal : p.state = q.state := rfl

def identityView : helperStep.StateIso p.state q.state := Step.StateIso.refl _

theorem left_source_map_agrees : Assignment.compose identityView.frame.hom p.leftMap = q.leftMap := by
  funext name
  exact instantiate_identity _

def probe : Firing bare := ⟨1, ([], ()), generator bare.frame.arity (.inr ()), []⟩

theorem probe_allowed : helperStep.Admits probe := by
  apply (admits_iff probe).mpr
  exact ⟨⟨empty, ContextResultControls.solution, Frames.models_nil _⟩, by decide, asks_nil⟩

theorem both_native_candidates_allowed : helperStep.Admits (s := p.state) (p.rightFiring probe) ∧
    helperStep.Admits (s := q.state) (q.rightFiring probe) := by
  constructor
  · exact (p.admitted_right_iff probe probe_allowed).mpr
      ⟨⟨targetFrame, (Frames.contextual tiny).id _, Frames.models_nil _⟩, by decide⟩
  · exact (q.admitted_right_iff probe probe_allowed).mpr
      ⟨⟨targetFrame, (Frames.contextual tiny).id _, Frames.models_nil _⟩, by decide⟩

def distinguish : Assignment targetFrame.arity empty.arity
  | .inl (.inl impossible) => impossible.elim
  | .inl (.inr ()) => constant 11
  | .inr () => constant 13

theorem identity_candidate_covariance_fails :
    helperTransport.move identityView (p.rightFiring probe) ≠ q.rightFiring probe := by
  intro same
  have values := congrArg (fun firing : Firing q.state => observe (instantiate distinguish firing.value)) same
  change observe (constant (declaration := empty.arity) (Γ := []) 11) = observe (constant 13) at values
  cases observe_injective values

theorem no_identity_placement_iso :
    ¬∃ mapping : PlacementIso p q, mapping.frame.hom = (Frames.contextual tiny).id targetFrame := by
  rintro ⟨mapping, same⟩
  have commutes := congrFun mapping.right_map (.inr ())
  change instantiate mapping.frame.hom (p.rightMap (.inr ())) = q.rightMap (.inr ()) at commutes
  rw [same] at commutes
  have rightMaps : p.rightMap (.inr ()) = q.rightMap (.inr ()) :=
    (instantiate_identity (p.rightMap (.inr ()))).symm.trans commutes
  have values := congrArg (instantiate distinguish) rightMaps
  change (constant (declaration := empty.arity) (Γ := []) 11) = constant 13 at values
  cases values

theorem no_identity_after_role_swap :
    ¬∃ mapping : PlacementIso p.swap q.swap, mapping.frame.hom = (Frames.contextual tiny).id targetFrame := by
  rintro ⟨mapping, same⟩
  exact no_identity_placement_iso ⟨mapping.swap, same⟩

def proper : PlacementIso p q where
  frame := Helpers.swapIso empty first.helper first.helper
  left_map := by
    funext name
    cases name with
    | inl impossible => exact impossible.elim
    | inr freshName => cases freshName; rfl
  right_map := by
    funext name
    cases name with
    | inl impossible => exact impossible.elim
    | inr freshName =>
        cases freshName
        exact swap_incl_fresh empty first.helper first.helper

theorem proper_candidate_covariance :
    helperTransport.move proper.swap.toStateIso (p.swap.leftFiring probe) = q.swap.leftFiring probe :=
  proper.swap.candidate probe

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.PlacementIsoControls
