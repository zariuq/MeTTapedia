import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentContextSimilarity
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RunSwapWitness

/-!
# Context placement of actual residual firings

The helper payload depends on the typed frame, while contextual placement
changes the occurrence set. The result-state equality therefore carries
the placed old residual to the literal new residual. The accompanying cast
laws expose complete run heads without changing their accepted effects.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Step

universe uO uT uH uOcc uS uF

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O]
  {State : Type uS} {Firing : State → Type uF} (P : Step X O State Firing)

theorem castAdmits {source target : State} (same : source = target)
    (candidate : Firing source) (accepted : P.Admits candidate) : P.Admits (same ▸ candidate) := by
  cases same
  exact accepted

theorem castResult {source target : State} (same : source = target)
    (candidate : Firing source) (accepted : P.Admits candidate) :
    P.result (same ▸ candidate) (P.castAdmits same candidate accepted) = P.result candidate accepted := by
  cases same
  rfl

theorem castRun_cons {source target : State} (same : source = target)
    (candidate : Firing source) (accepted : P.Admits candidate)
    (rest : P.Run (P.result candidate accepted)) :
    same ▸ (Step.Run.cons candidate accepted rest) =
      Step.Run.cons (same ▸ candidate) (P.castAdmits same candidate accepted)
        ((P.castResult same candidate accepted).symm ▸ rest) := by
  cases same
  rfl

end Step

namespace DependentFull.ContextPlacement

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
  {levels : LevelModel rules L} {O : Type}

def payload {state : State rules O} (candidate : HelperFiring levels O state) :
    Σ helpers : Helpers state.frame, Natural levels O helpers.frame := ⟨candidate.helpers, candidate.data⟩

theorem payload_injective {state : State rules O} : Function.Injective (payload (levels := levels) (state := state)) := by
  rintro ⟨firstHelpers, firstData⟩ ⟨secondHelpers, secondData⟩ same
  obtain ⟨sameHelpers, sameData⟩ := Sigma.mk.inj same
  cases sameHelpers
  cases sameData
  rfl

theorem payload_cast {source target : State rules O} (same : source = target)
    (candidate : HelperFiring levels O source) : HEq (payload (same ▸ candidate)) (payload candidate) := by
  cases same
  rfl

variable [DecidableEq O]

theorem residual_placed (extra : Finset O) {state : State rules O}
    (first second : HelperFiring levels O state) (accepted : (helperStep levels O).Admits first)
    (safe : Safe extra first) :
    helperResidual (firing extra first) (admits extra first accepted safe.fresh safe.queries) (firing extra second) =
      (result extra first accepted safe).symm ▸ firing extra (helperResidual first accepted second) := by
  apply payload_injective
  exact (eq_of_heq (payload_cast (result extra first accepted safe).symm
    (firing extra (helperResidual first accepted second)))).symm

noncomputable def castSwap {source target : State rules O} (same : source = target)
    {first second : (helperStep levels O).toStep.Run source}
    (witness : (helperTransport levels O).SwapWitness first second) :
    (helperTransport levels O).SwapWitness (same ▸ first) (same ▸ second) := by
  cases same
  exact witness

theorem castSwap_depth {source target : State rules O} (same : source = target)
    {first second : (helperStep levels O).toStep.Run source}
    (witness : (helperTransport levels O).SwapWitness first second) :
    (castSwap same witness).depth = witness.depth := by
  cases same
  rfl

end DependentFull.ContextPlacement

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.DependentFull.ContextPlacement.residual_placed
