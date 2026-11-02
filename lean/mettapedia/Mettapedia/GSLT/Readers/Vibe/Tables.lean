import Mettapedia.GSLT.Readers.Vibe.Syntax

/-!
# The reader's tables for Vibe's checker input: the specification `gen-tables` mirrors

The grammar and the binary profile of `CheckStreamSyntax.module`, lowered to an SLR(1) automaton,
once for each kind of file: `proofSpec` reads a file after `--proofs`, `setupSpec` a file before it.
The controls below are checked when this file is checked: no SLR conflict, and no state in which two
terminals could both be cut at one byte position (`BinaryTokens.Spec.conflictFree`): at the start
of an instruction only the 27 one-byte opcode sorts and the end of the file have actions, and in the
middle of an instruction exactly one operand sort does.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Readers.Vibe.Tables

open Mettapedia.GSLT.Readers.BinaryTokens

def proofSpec : Spec :=
  { name := "CheckStreamSyntax", grammar := grammar, profile := profile, start := "proof_file" }

def setupSpec : Spec :=
  { name := "CheckStreamSyntax", grammar := grammar, profile := profile, start := "setup_file" }

#guard proofSpec.conflictFree
#guard setupSpec.conflictFree

end Mettapedia.GSLT.Readers.Vibe.Tables
