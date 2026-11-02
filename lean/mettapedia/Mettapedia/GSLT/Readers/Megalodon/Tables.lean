import Mettapedia.GSLT.Readers.Megalodon.Syntax
import Mettapedia.GSLT.Readers.Export

/-!
# The reader's tables for Megalodon's record: the specification `gen-tables` mirrors

The grammar and the version-2 profile of `SexprInfoSyntax.module`, lowered to an SLR(1) automaton
by the generic `Export`. The control below is checked when this file is checked: no SLR conflict,
and no token two terminals could both read with different actions in one state. `PRIM` is both a
declaration line and a term, and the theorem lines are followed by four kinds of lines that all
begin with `(`, so this is also the check that one token of look-ahead decides every step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.Megalodon.Tables

open Mettapedia.GSLT.Readers.Export

def spec : Spec := { name := "SexprInfoSyntax", grammar := grammar, profile := profile }

#guard spec.conflictFree

end Mettapedia.GSLT.Readers.Megalodon.Tables
