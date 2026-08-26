import Mettapedia.GSLT.LanguageDef.WaltersZantemaDA
import Mettapedia.GSLT.LanguageDef.CanonicalWire

/-!
# Walters--Zantema DA wire projection

This module renders the finite DA `LanguageDef` into the canonical five-field
CeTTa wire.  The renderer is deliberately partial: it accepts exactly the
constructor and pattern forms used by the closed DA profile and rejects every
unsupported form.  The generated wire is therefore a structural projection of
the proved Lean presentation rather than an independently maintained rule
table.
-/

namespace Mettapedia.GSLT.LanguageDef.WaltersZantemaDA.Wire

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WaltersZantemaDA

abbrev renderLanguage? :=
  Mettapedia.GSLT.LanguageDef.CanonicalWire.renderLanguage?

/-- The primary closed qualification instance is accepted by the partial wire
projection. -/
theorem radixTwo_renderLanguage?_isSome :
    (renderLanguage? (language radixTwo)).isSome := by
  decide +kernel

/-- Canonical generated radix-two wire text. -/
def radixTwoWire : String :=
  (renderLanguage? (language radixTwo)).getD ""

theorem radixTwoWire_nonempty : radixTwoWire ≠ "" := by
  decide +kernel

def writeRadixTwo (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path radixTwoWire

#print axioms radixTwo_renderLanguage?_isSome
#print axioms radixTwoWire_nonempty

end Mettapedia.GSLT.LanguageDef.WaltersZantemaDA.Wire
