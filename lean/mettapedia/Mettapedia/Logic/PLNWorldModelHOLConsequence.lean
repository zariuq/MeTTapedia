import Mettapedia.Logic.PLNWorldModelHOLCompleteness

/-!
# HOL WM Consequence API

Thin public wrapper over the real HOL consequence bridge.

This file intentionally exposes the state-indexed WM consequence rule surface
without re-encoding the underlying Henkin-model semantics.
-/

namespace Mettapedia.Logic.PLNWorldModelHOLConsequence

abbrev wmConsequenceRuleOn_of_pointwise :=
  @Mettapedia.Logic.PLNWorldModelHOLCompleteness.wmConsequenceRuleOn_of_pointwise

end Mettapedia.Logic.PLNWorldModelHOLConsequence
