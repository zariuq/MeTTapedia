import Mettapedia.GSLT.Readers.MM0.SpecSyntax
import Mettapedia.GSLT.Readers.Export

/-!
# The `.mm0` reader's tables: the specification `gen-tables` mirrors

The grammar and the version-2 profile of `MM0Syntax.module`, lowered to an SLR(1) automaton by the
generic `Export`. The control below is checked when this file is checked: no SLR conflict, and no
token two terminals could both read with different actions in one state (MM0's pseudo-keywords are
also identifiers, so this is the check that they never compete).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.MM0.SpecTables

open Mettapedia.GSLT.Readers.Export

def spec : Spec := { name := "MM0Syntax", grammar := Spec.grammar, profile := Spec.profile }

#guard spec.conflictFree

end Mettapedia.GSLT.Readers.MM0.SpecTables
