import Mettapedia.Enactive.ScopedGeneration
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.OutcomeContract

/-! # Task-generation comparison for the declared candidate profiles -/

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.EnactiveScopeCalibration

open Mettapedia.Enactive.ScopedGeneration
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.OutcomeContract

def recognizes (profile : Profile) (judgment : JudgmentClass) : Prop :=
  classify profile judgment = .inClass

/-- The current Russell tower genuinely covers the classes recognized by the
current monomorphic regular profile. -/
theorem monomorphicRegular_scopeIncluded_towerRussell :
    ScopeIncluded recognizes .monomorphicRegular .towerRussell := by
  intro judgmentClass recognized
  cases judgmentClass <;> simp [recognizes, classify] at recognized ⊢

/-- Coverage inclusion is directional: the monomorphic profile does not
recognize the tower's polymorphic schema class. -/
theorem not_towerRussell_scopeIncluded_monomorphicRegular :
    ¬ ScopeIncluded recognizes .towerRussell .monomorphicRegular := by
  intro included
  have := included JudgmentClass.towerPolymorphicSchema (by rfl)
  cases this


open Mettapedia.Enactive.ScopedGeneration.Canary

/-- Positive control: this actual Bennett child-parent edge is paired with an
actual strict candidate coverage increase and a legal authority refinement. -/
theorem scopedWitness :
    ScopedAuthorityGeneration recognizes 1 childTask parentTask
      .monomorphicRegular .towerRussell before after where
  taskGrowth := oneStepGeneration
  scopeGrowth := monomorphicRegular_scopeIncluded_towerRussell
  outcomeGrowth := .outsideEstablished () ()


end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.EnactiveScopeCalibration
