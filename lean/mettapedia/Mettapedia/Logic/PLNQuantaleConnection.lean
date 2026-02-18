import Mettapedia.Logic.PLNDeduction
import Mettapedia.Logic.EvidenceSTVBridge

/-!
# PLNQuantaleConnection (Compatibility Shim)

This module previously contained an exploratory strength-level quantale packaging.
That implementation is archived at:

- `Mettapedia/Logic/Archive/PLNQuantaleConnectionLegacy.lean`

The canonical active foundation is the ENNReal evidence carrier in:

- `Mettapedia.Logic.EvidenceQuantale`

Use `PLNDeduction.STV` (and `EvidenceSTVBridge`) for STV-level interfaces.
-/

namespace Mettapedia.Logic.PLNQuantaleConnection

open Mettapedia.Logic

/-- Legacy STV name kept for compatibility. -/
abbrev SimpleTruthValue := PLNDeduction.STV

/-- Compatibility alias for the proven distributional↔deduction STV equivalence. -/
abbrev stvIso := EvidenceSTVBridge.stvEquiv

end Mettapedia.Logic.PLNQuantaleConnection
