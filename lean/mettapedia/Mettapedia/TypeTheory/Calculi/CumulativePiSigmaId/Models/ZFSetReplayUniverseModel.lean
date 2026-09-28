import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayUniverseModel
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeReplay
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayUniverseFormation

/-!
# A cumulative universe model for replay interpretation

The primitive closure package is realized by the constructed set-universe
tower. Its strength is the explicit cofinal-inaccessibles hypothesis; the
chosen ground interpretation must inhabit the bottom universe. Both Pi and
Sigma use the actual maximum-level rule, and identity codes inhabit every
universe level.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetTraceProducts (tracePiSet)
open ZFSetDependentProducts (sigmaSet)

universe u

/-- The cumulative replay signature has no declared constants. -/
theorem empty_constants_model (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u}) : ConstantsModel heads constants Tower.rules where
  declared := by
    intro name type known
    cases known

/-- Advancing a universe level preserves universehood and gives its type. -/
theorem successor_qualified (level : Tower.Head)
    (isUniverse : Tower.rules.isUniverse level) :
    Tower.rules.isUniverse (TowerDecisions.headTarget level) ∧
      Tower.rules.headTyping level (TowerDecisions.headTarget level) := by
  cases isUniverse with
  | sort level => exact ⟨.sort _, .sort _⟩

/-- The existing internal universe hierarchy realizes all primitive closure
obligations, without a whole-typing or certificate-coherence hypothesis. -/
theorem universeModel (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u})
    (valuation : Nat → Nat) (groundTyped : ground ∈ universeSet h seed 0) :
    UniverseModel Tower.rules (interpretHead h seed ground valuation) where
  headTyping_mem := ZFSetReplayUniverseFormation.headTyping_membership
    h seed ground valuation groundTyped
  cumulative_subset := ZFSetReplayUniverseFormation.cumulative_subset h seed ground valuation
  pi_mem := by
    intro domainLevel bodyLevel level joined A domainTyped B bodyTyped
    cases joined with
    | sorts left right =>
      change tracePiSet A B ∈
        universeSet h seed (max (left.eval valuation) (right.eval valuation))
      exact (universeSet_closed h seed _).tracePiSet_mem
        (universeSet_mono h seed (Nat.le_max_left _ _) domainTyped) B
        (fun x inside => universeSet_mono h seed (Nat.le_max_right _ _) (bodyTyped x inside))
  sigma_mem := by
    intro domainLevel bodyLevel level joined A domainTyped B bodyTyped
    cases joined with
    | sorts left right =>
      change sigmaSet A B ∈
        universeSet h seed (max (left.eval valuation) (right.eval valuation))
      exact (universeSet_closed h seed _).sigmaSet_mem
        (universeSet_mono h seed (Nat.le_max_left _ _) domainTyped) B
        (fun x inside => universeSet_mono h seed (Nat.le_max_right _ _) (bodyTyped x inside))
  identity_mem := by
    intro level isUniverse P
    cases isUniverse with
    | sort level => exact ZFSetTraceUniverseInterpretation.truthCode_mem h seed _ P

#print axioms universeModel
#print axioms empty_constants_model
#print axioms successor_qualified

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseModel
