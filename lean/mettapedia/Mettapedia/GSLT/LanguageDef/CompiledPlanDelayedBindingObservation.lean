import Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
import Mettapedia.GSLT.LanguageDef.CompiledPlanActivationViewCompilation

/-!
# Compiled-plan matching as a delayed binding observation

The generic binding-store interface permits materialization-free execution
only for consumers whose direct observation commutes with the authoritative
materialize-then-observe path.  Compiled-plan activation matching is one such
consumer.

This module packages the existing nontrivial exactness theorem as that common
capability.  It does not add another matcher or term representation.  A
consumer capable of capturing a variable-bearing source application remains
outside the admitted activation-view fragment and must use the reference path.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CompiledPlanDelayedBindingObservation

open Mettapedia.GSLT.Core.BindingStoreCapabilityAlgebra
open CompiledPlanAdmission
open CompiledPlanTermSemantics
open CompiledPlanGroundDenseCompilation
open CompiledPlanActivationViewCompilation

/-- Everything the direct matcher observes without first constructing the
complete substituted producer body. -/
structure MatchClosure where
  sourceEnvironment : Substitution
  source : Term
  pattern : Term
  patternEnvironment : SourceEnvironment

/-- Reference materialization may fail when a source slot is unavailable. -/
abbrev MaterializedSource := Option GroundTerm

def materialize (request : MatchClosure) : MaterializedSource :=
  instantiateTerm request.sourceEnvironment request.source

def observeMaterialized
    (request : MatchClosure) (target : MaterializedSource) :
    Option SourceEnvironment :=
  match target with
  | none => none
  | some value => matchSource request.pattern value request.patternEnvironment

def observeDirect (request : MatchClosure) : Option SourceEnvironment :=
  matchView request.sourceEnvironment request.source request.pattern
    request.patternEnvironment

/-- Activation matching is a genuine instance of materialization-free
observation: the proof is the independent recursive view/materialized
commuting theorem, not definitional self-validation. -/
def activationMatchObservation :
    DelayedObservation MatchClosure MaterializedSource
      (Option SourceEnvironment) where
  materialize := materialize
  observeMaterialized := observeMaterialized
  observeDirect := observeDirect
  commutes request := by
    exact matchView_eq_materialized request.sourceEnvironment request.source
      request.pattern request.patternEnvironment

theorem direct_match_eq_materialize_then_match (request : MatchClosure) :
    observeDirect request =
      observeMaterialized request (materialize request) :=
  activationMatchObservation.observeDirect_exact request

/-! ## Positive and negative controls -/

private def oneSlot : Substitution
  | 0 => some (.symbol [7])
  | _ => none

private def sourceApplication : Term :=
  .application [1] (.cons (.variable 0) .nil)

private def matchingPattern : Term :=
  .application [1] (.cons (.variable 3) .nil)

/-- Positive: direct matching observes the same binding as the fully
materialized source. -/
example :
    observeDirect
        { sourceEnvironment := oneSlot
          source := sourceApplication
          pattern := matchingPattern
          patternEnvironment := emptySourceEnvironment } =
      observeMaterialized
        { sourceEnvironment := oneSlot
          source := sourceApplication
          pattern := matchingPattern
          patternEnvironment := emptySourceEnvironment }
        (materialize
          { sourceEnvironment := oneSlot
            source := sourceApplication
            pattern := matchingPattern
            patternEnvironment := emptySourceEnvironment }) := by
  exact direct_match_eq_materialize_then_match _

/-- Negative admission control: a root variable could capture the complete
constructed source, so it is not licensed as a materialization-free consumer. -/
example : consumerSafe sourceApplication (.variable 9) = false := by
  rfl

#print axioms direct_match_eq_materialize_then_match

end Mettapedia.GSLT.LanguageDef.CompiledPlanDelayedBindingObservation
