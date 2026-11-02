import Mettapedia.GSLT.Readers.Rho.Syntax
import Mettapedia.GSLT.Readers.Export

/-!
# The mrho reader's tables: the specification `gen-tables` mirrors

The grammar and the version-2 profile of `MrhoSyntax.module`, lowered to an SLR(1) automaton by the
generic `Export`. The control below is checked when this file is checked: no SLR conflict, and no
token two terminals could both read with different actions in one state. A name and a process both
begin with `(`, and a parallel composition's components run until its `)`, so this is also the check
that one token of look-ahead decides every step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.Rho.Tables

open Mettapedia.GSLT.Readers.Export

def spec : Spec := { name := "MrhoSyntax", grammar := grammar, profile := profile }

#guard spec.conflictFree

end Mettapedia.GSLT.Readers.Rho.Tables
