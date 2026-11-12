import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextPlacementControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperContextResult
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Reindex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRuns

/-!
# Two admitted source origins can have one primitive native firing

A placement substitutes the same constant for two distinct local declaration
names. The local candidates are distinct and admitted. Their placed native
candidates and endpoints coincide. A source-origin reindexing retains both
generating events, and no readback can recover that origin from the primitive
firing alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.OriginProjectionControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Helpers.Consumer (tiny empty start constant)

def sourceFrame : Frames.Frame tiny := ⟨Bool, fun _ => ([], ())⟩
def source : State tiny Nat := ⟨sourceFrame, [], ∅⟩
def candidate (origin : Bool) : Firing source := ⟨1, ([], ()), generator sourceFrame.arity origin, []⟩

def placement : ContextPlacement source start :=
  ⟨empty, (fun _ => constant 7), (fun impossible => impossible.elim)⟩

theorem source_solvable : (Frames.contextual tiny).Solvable source.knowledge :=
  ⟨empty, placement.leftMap, Frames.models_nil _⟩

theorem source_allowed (origin : Bool) : helperStep.Admits (candidate origin) :=
  (admits_iff _).mpr ⟨source_solvable, by change (1 : Nat) ∉ (∅ : Finset Nat); decide, asks_nil⟩

theorem source_candidates_distinct : candidate false ≠ candidate true := by
  intro same
  have values := congrArg (fun firing : Firing source => observe firing.value) same
  cases values

theorem placed_solvable : (Frames.contextual tiny).Solvable placement.state.knowledge :=
  ⟨empty, (Frames.contextual tiny).id empty, Frames.models_nil _⟩

theorem native_allowed (origin : Bool) : helperStep.Admits (s := placement.state) (placement.leftFiring (candidate origin)) :=
  (placement.admitted_left_iff _ (source_allowed origin)).mpr
    ⟨placed_solvable, by change (1 : Nat) ∉ (∅ : Finset Nat); decide⟩

theorem primitive_candidates_equal : placement.leftFiring (candidate false) = placement.leftFiring (candidate true) := rfl

def originProfile : Step (Frames.contextual tiny) Nat (State tiny Nat) (fun state => Bool × Firing state) :=
  helperStep.toStep.reindex (fun origin => origin.2)

def observed := originProfile.eventSystem (fun origin => origin.2.helper)

def event (origin : Bool) : observed.Choice placement.state :=
  ⟨(origin, placement.leftFiring (candidate origin)), native_allowed origin⟩

def project (choice : observed.Choice placement.state) : Firing placement.state := choice.val.2

theorem events_distinct : event false ≠ event true := by
  intro same
  have origins := congrArg (fun choice : observed.Choice placement.state => choice.val.1) same
  cases origins

theorem projected_events_equal : project (event false) = project (event true) := primitive_candidates_equal

theorem successors_equal : observed.next placement.state (event false) = observed.next placement.state (event true) := rfl

theorem no_origin_readback :
    ¬∃ readback : Firing placement.state → observed.Choice placement.state,
      ∀ origin, readback (project (event origin)) = event origin := by
  rintro ⟨readback, recovers⟩
  exact events_distinct ((recovers false).symm.trans
    ((congrArg readback projected_events_equal).trans (recovers true)))

theorem joint_permission_is_not_local_permission :
    ¬helperStep.Admits ContextPlacementControls.candidate ∧
      helperStep.Admits (s := ContextPlacementControls.shared.state)
        (ContextPlacementControls.shared.leftFiring ContextPlacementControls.candidate) :=
  ⟨ContextPlacementControls.candidate_locally_refused, ContextPlacementControls.context_enables_candidate⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers.OriginProjectionControls
