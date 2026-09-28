import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.TypedReduction
import Mettapedia.TypeTheory.UniverseLevel.Order

/-!
# Universe levels in a level order

The value side reads the universe levels of its rule package from the level
model `LevelModel rules L`, in a level order `L`: the universe of a universe is
one successor up, cumulativity does not lower levels, equal heads have equal
levels, and a join is a maximum. So a universe is strictly below every universe
that types it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open UniverseLevel (LevelOrder)

variable {Head L : Type} [LevelOrder L] {R : Rules Head}

/-- The level of a universe is below the level of its type. -/
theorem LevelModel.level_lt_of_typing (levels : LevelModel R L) {u v : Head}
    (hu : R.isUniverse u) (typing : R.headTyping u v) : levels.level u < levels.level v := by
  rw [(levels.universe_typing hu typing).2]
  exact LevelOrder.lt_succ _

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
