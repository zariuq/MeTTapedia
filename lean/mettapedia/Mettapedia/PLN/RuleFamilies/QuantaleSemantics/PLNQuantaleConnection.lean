import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction
import Mettapedia.PLN.Evidence.EvidenceSTVBridge

/-!
# PLNQuantaleConnection (Compatibility Shim)

This module previously contained an exploratory strength-level quantale packaging.
That implementation is archived at:

- `Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnectionLegacy`

The canonical active foundation is the ENNReal evidence carrier in:

- `Mettapedia.PLN.Evidence.EvidenceQuantale`

Use `PLNDeduction.STV` (and `EvidenceSTVBridge`) for STV-level interfaces.
-/

namespace Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnection

open Mettapedia.PLN.RuleFamilies.FirstOrder

/-- Legacy STV name kept for compatibility. -/
abbrev SimpleTruthValue := PLNDeduction.STV

/-- Compatibility alias for the proven distributional↔deduction STV equivalence. -/
abbrev stvIso := Mettapedia.PLN.Evidence.EvidenceSTVBridge.stvEquiv

end Mettapedia.PLN.RuleFamilies.QuantaleSemantics.PLNQuantaleConnection
