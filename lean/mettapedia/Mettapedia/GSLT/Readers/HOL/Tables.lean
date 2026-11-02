import Mettapedia.GSLT.Readers.HOL.Syntax
import Mettapedia.GSLT.Readers.Export

/-!
# The ProofTrace reader's tables, computed from the `.module` ahead of time

The grammar and the version-2 profile of `ProofTraceSyntax.module`, lowered to an SLR(1) automaton
by the generic `Export`. The control below is checked when this file is checked: no SLR conflict,
and no token two terminals could both read with different actions in one state. Every keyword of
the grammar (`REFL`, `v`, `c`, `id`, ...) is also a name and `,` is both a fixed spelling and a
name (HOL Light's pair constant), so this is the check that names and keywords never compete.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.HOL.Tables

open Mettapedia.GSLT.Readers.Export

def spec : Spec := { name := "ProofTraceSyntax", grammar := grammar, profile := profile }

#guard spec.conflictFree

end Mettapedia.GSLT.Readers.HOL.Tables
