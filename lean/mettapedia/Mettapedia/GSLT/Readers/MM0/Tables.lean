import Mettapedia.GSLT.Readers.MM0.Syntax
import Mettapedia.GSLT.Readers.Export

/-!
# The `.mmu` reader's tables, computed from the `.module` ahead of time

The grammar and the version-2 profile of `MMUSyntax.module`, lowered to an SLR(1) automaton by the
generic `Export`. The control below is checked when this file is checked: no SLR conflict, and no
token two terminals could both read with different actions in one state (MM0's keywords are also
identifiers, so this is the check that they never compete).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.MM0.Tables

open Mettapedia.GSLT.Readers.Export

def spec : Spec := { name := "MMUSyntax", grammar := grammar, profile := profile }

#guard spec.conflictFree

end Mettapedia.GSLT.Readers.MM0.Tables
