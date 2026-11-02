import Mettapedia.GSLT.Readers.Metamath.Syntax
import Mettapedia.GSLT.Readers.Export

/-!
# The Metamath reader's tables through the generic exporter

Metamath's version-1 profile, read as version 2 (`TokenProfileV2.ofV1`: the same tokens and token
sorts, `tokenize_ofV1`, `tokenHasSort_ofV1`), and its grammar, through the same `Export` as MM0's
readers, so one C engine and one MeTTa engine serve both.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.Metamath.TablesV2

open Mettapedia.GSLT.Readers.Export

def spec : Spec :=
  { name := "MetamathSyntax", grammar := grammar, profile := TokenProfileV2.ofV1 profile }

#guard spec.conflictFree

end Mettapedia.GSLT.Readers.Metamath.TablesV2
