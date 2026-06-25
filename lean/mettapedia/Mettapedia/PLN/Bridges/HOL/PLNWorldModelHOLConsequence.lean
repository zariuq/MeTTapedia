import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness

/-!
# HOL WM Consequence API

Thin public wrapper over the real HOL consequence bridge.

This file intentionally exposes the state-indexed WM consequence rule surface
without re-encoding the underlying Henkin-model semantics.
-/

namespace Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLConsequence

noncomputable abbrev wmConsequenceRuleOn_of_pointwise :=
  @Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness.wmConsequenceRuleOn_of_pointwise

end Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLConsequence
