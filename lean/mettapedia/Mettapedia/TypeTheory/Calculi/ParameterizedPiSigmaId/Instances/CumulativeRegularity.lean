import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

/-! # Concrete instances and controls for FormationSensitiveTyping -/

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive

/-- The existing cumulative head rules satisfy the separate universe
regularity obligations, with no new universe or logical axiom. -/
theorem towerUniverseRegularity : UniverseRegularity Tower.rules where
  head_target := by
    intro h u typing
    cases typing <;> exact .sort _
  join_target := by
    intro u v w join
    cases join
    exact .sort _
  cumulative_target := by
    intro u v order
    cases u <;> cases v <;> simp only [LevelTower.rules, LevelTower.Cumulative] at order
    exact .sort _
  universe_typed := by
    intro u universeWitness
    cases universeWitness with
    | sort level => exact ⟨_, .sort level, .sort _⟩


#print axioms towerUniverseRegularity

end FormationSensitive
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
