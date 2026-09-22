import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles

open Mettapedia.TypeTheory.UniverseLevel

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationCheckedTelescopePrograms

/-- The native cumulative joins inhabit the closure capability. -/
theorem tower_joins {u v : Tower.Head}
    (first : Tower.rules.isUniverse u) (second : Tower.rules.isUniverse v) :
    ∃ w, Tower.rules.isUniverse w ∧ Tower.rules.join u v w := by
  cases first with
  | sort first =>
      cases second with
      | sort second => exact ⟨_, .sort _, .sorts first second⟩


end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationCheckedTelescopePrograms
