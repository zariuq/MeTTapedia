import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveSignaturePreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion

/-! # Subject preservation for the root-empty cumulative profile -/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive

/-- The concrete semantic level equality preserves the concrete Tower head
typing. Successor levels are compared semantically, not assumed identical. -/
theorem towerHeadPreservation : HeadPreservation Tower.rules := by
  intro n Γ head next u typed equality
  cases typed with
  | legacyGround =>
      cases next with
      | legacyGround => exact .headType .legacyGround
      | sort level => exact False.elim equality
  | sort level =>
      cases next with
      | legacyGround => exact False.elim equality
      | sort nextLevel =>
          apply Typing.conv (.headType (LevelTower.HeadTyping.sort nextLevel))
            (.headType (LevelTower.HeadTyping.sort (.succ level))) (LevelTower.IsUniverse.sort _)
          apply Relation.EqvGen.rel
          apply Step.head
          intro valuation
          exact congrArg Nat.succ (equality valuation).symm

theorem towerRootPreservation : RootPreservation Tower.rules := by
  intro n Γ source target type context typing impossible
  exact impossible.elim

/-- No preservation or conversion-boundary hypothesis remains for the
actual root-empty cumulative presentation. -/
theorem Judgment.steps_preserve_tower {Γ : Tower.Ctx n}
    {source target type : Tower.Tm n} (judgment : Judgment Tower.rules Γ source type)
    (steps : ConversionCoherence.StepStar Tower.rules source target) :
    Judgment Tower.rules Γ target type :=
  judgment.steps_preserve towerUniverseRegularity LevelTower.piConversionBoundary
    (EmptyRootConversion.sigmaConversionBoundary Tower.rules rfl LevelTower.headEq_symmetric)
    towerHeadPreservation towerRootPreservation steps


end FormationSensitive
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
