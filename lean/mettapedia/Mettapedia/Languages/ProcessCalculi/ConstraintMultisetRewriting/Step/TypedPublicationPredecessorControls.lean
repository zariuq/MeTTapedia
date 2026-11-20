import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationPredecessors
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationResidualControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationOfferedCounts

/-!
# Incoming publication after a nonidentity answer-frame exchange

The actual residual application introduces X : U0 with X = Ground and
retains an input p : Ground. Its result is recertified at the exchanged
frame X : U0, p : Ground. The pending equation remains and the output's raw
variable position changes. A fixed offer table containing only the original
application distinguishes these isomorphic targets by a predecessor formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.PredecessorControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull DependentFull.Controls
open ContextualDependentParameterExchange
open LogicOverTheStep.StepSpan
open Mettapedia.OSLF.Framework.DerivedModalities

abbrev original := ResidualControls.application

theorem accepted : original.schema.Admits original.pick := (realization_admits_iff original).mp ResidualControls.admitted

def oldEnd := original.sourceResult accepted
abbrev exchangedFrame := context (smallUniverse (empty Tower.rules)) (groundType (empty Tower.rules))

def exchange : exchangedFrame ≅ oldEnd.frame := swapIso (smallUniverse (empty Tower.rules)) (groundType (empty Tower.rules))

def newEnd : State Tower.rules Nat where
  frame := exchangedFrame
  knowledge := (frames setting.levels).applyStore exchange.hom oldEnd.knowledge
  present := oldEnd.present
  label occurrence := (oldEnd.label occurrence).reindex exchange.hom

def comparison : PlainIso setting.levels oldEnd newEnd := ⟨exchange, fun _ _ => Iff.rfl, rfl, fun _ => rfl⟩

def recertified : Application setting.levels Nat ResidualControls.before := TargetChange.application original accepted comparison

theorem new_application_admitted : (realizationStep setting.levels Nat).Admits recertified :=
  TargetChange.native_admitted original accepted comparison

theorem exact_new_endpoint : (realizationStep setting.levels Nat).result recertified new_application_admitted = newEnd :=
  TargetChange.native_result original accepted comparison

theorem residual_retained : recertified.basis.knowledge = newEnd.knowledge := rfl
theorem residual_nonempty : recertified.basis.knowledge.length = 1 := rfl

def rawIndex (state : State Tower.rules Nat) : Option Nat :=
  match (state.label 9).2.code with
  | .var index => some index.val
  | _ => none

theorem old_index : rawIndex oldEnd = some 1 := rfl
theorem new_index : rawIndex newEnd = some 0 := rfl

theorem different_endpoints : oldEnd ≠ newEnd := by
  intro same
  have observed := congrArg rawIndex same
  rw [old_index, new_index] at observed
  cases observed

theorem new_identity_does_not_solve_residual :
    ¬ (frames setting.levels).Models (𝟙 exchangedFrame) newEnd.knowledge := by
  intro models
  have equality := (models _ (List.mem_singleton_self _)).2
  change Equal Tower.rules exchangedFrame.raw (.var 1) ground (.head (.sort Tower.zero)) at equality
  have types : TypeEq Tower.rules exchangedFrame.raw (.var 1) ground := ⟨_, .sort _, equality⟩
  have neutral : Neutral (TowerModel.roles (L := Nat)) (.var 1 : Tower.Tm 2) := .var 1
  exact (TypeEq.neutral_form (TowerModel.facts (L := Nat)) types exchangedFrame.formed neutral
    (.inl ⟨_, rfl⟩)).not_former.1 _ rfl

theorem common_actual_predecessor :
    Succ (realizationStep setting.levels Nat) ResidualControls.before oldEnd ∧
      Succ (realizationStep setting.levels Nat) ResidualControls.before newEnd := by
  have originalStep : Succ (realizationStep setting.levels Nat) ResidualControls.before oldEnd :=
    ⟨original, ResidualControls.admitted, realization_result original accepted⟩
  exact ⟨originalStep, CoherenceModal.predecessor_lift originalStep comparison⟩

def originalOffers : Fin 1 → Application setting.levels Nat ResidualControls.before := fun _ => original
def originalEdge : (OfferedCounts.span originalOffers).Edge := ⟨0, ResidualControls.admitted⟩

theorem offer_endpoint (edge : (OfferedCounts.span originalOffers).Edge) :
    (OfferedCounts.span originalOffers).target edge = oldEnd := realization_result original accepted

theorem unoffered_has_no_predecessor : derivedBox (OfferedCounts.span originalOffers) (fun _ => False) newEnd := by
  intro edge reaches
  exact different_endpoints ((offer_endpoint edge).symm.trans reaches)

theorem offered_has_predecessor : ¬ derivedBox (OfferedCounts.span originalOffers) (fun _ => False) oldEnd :=
  fun none => none originalEdge (offer_endpoint originalEdge)

theorem fixed_offers_distinguish_compared_targets :
    Nonempty (PlainIso setting.levels oldEnd newEnd) ∧
      derivedBox (OfferedCounts.span originalOffers) (fun _ => False) newEnd ∧
        ¬ derivedBox (OfferedCounts.span originalOffers) (fun _ => False) oldEnd :=
  ⟨⟨comparison⟩, unoffered_has_no_predecessor, offered_has_predecessor⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.PredecessorControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.PredecessorControls.exact_new_endpoint
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.PredecessorControls.fixed_offers_distinguish_compared_targets
