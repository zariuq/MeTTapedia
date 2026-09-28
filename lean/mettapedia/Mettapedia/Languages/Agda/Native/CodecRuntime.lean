import Mettapedia.Languages.Agda.Native.SyntaxControls
import Mettapedia.Languages.Agda.Native.ProofControls

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Native.Codec.Runtime
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.Languages.Agda.Structural
open ProofControls

def replay {j : AdministrativeStatics.Judgment} (tree : NativeTree j) : Bool := check j (encode tree)

def cases : List (String × Bool) := [
  ("administrative proof", replay administrativeTree),
  ("first repeated-premise order", replay firstThenSecond),
  ("second repeated-premise order", replay secondThenFirst),
  ("missing child", (decode (.node eliminationLabel [encode (sortTree 0)])).isNone),
  ("extra child", (decode (.node eliminationLabel [encode (sortTree 0), encode nilTree, encode nilTree])).isNone),
  ("swapped children", (decode (.node eliminationLabel [encode nilTree, encode (sortTree 0)])).isNone),
  ("changed context", (decode (.node (sortLabel 0) [encode extendedTree])).isNone),
  ("changed type", !check (.core (Statics.typed emptyContext (Statics.universeTerm 0)
    (Statics.universeType 0 2).code)) (encode (sortTree 0))),
  ("changed rule", !check (.core (Statics.typed emptyContext (Statics.universeTerm 0) resultType))
    (.node (sortLabel 1) [encode emptyTree])),
  ("unknown rule", (decode (.node (.atom 999) [])).isNone),
  ("unknown nested rule", (decode (.node (.pair (.atom 0) (.pair (.atom 0) (.atom 999))) [])).isNone),
  ("nil action cannot type head", !check (.core (Statics.typed emptyContext (Statics.universeTerm 0) resultType))
    (encode nilTree)),
  ("unknown operator", (getOperator (.atom 23)).isNone),
  ("escaped variable", ((rawTerm 0 .term).get (SyntaxControls.varWire 0)).isNone),
  ("wrong variable sort", ((rawTerm 1 .type).get (SyntaxControls.varWire 0)).isNone),
  ("wrong operator sort", ((rawTerm 0 .term).get (SyntaxControls.node (.atom 20) (.atom 0))).isNone),
  ("missing argument", ((rawTerm 0 .term).get (SyntaxControls.node (.atom 0) (.atom 0))).isNone),
  ("NoAbs cannot bind", ((rawTerm 0 .term).get (SyntaxControls.unary 1 (SyntaxControls.varWire 0))).isNone),
  ("bound variable", ((rawTerm 0 .term).get (SyntaxControls.unary 0 (SyntaxControls.varWire 0))).isSome),
  ("nested ambient variable", ((rawTerm 1 .term).get (SyntaxControls.unary 0
    (SyntaxControls.unary 0 (SyntaxControls.varWire 2)))).isSome),
  ("malformed context", (context.get (.pair (.atom 0) (SyntaxControls.varWire 0))).isNone),
  ("missing substitution image", ((rawSub 2 1).get (.pair (.atom 0) (SyntaxControls.varWire 0))).isNone),
  ("Unicode name", (Utf8.read [240, 159, 140, 187]).isSome),
  ("surrogate rejected", (Utf8.read [237, 160, 128]).isNone),
  ("overlong rejected", (Utf8.read [192, 128]).isNone)]

end Mettapedia.Languages.Agda.Native.Codec.Runtime

def Mettapedia.Languages.Agda.Native.Codec.Runtime.main : IO Unit := do
  let tests := Mettapedia.Languages.Agda.Native.Codec.Runtime.cases
  for (name, passed) in tests do
    unless passed do throw (IO.userError s!"FAILED: {name}")
  IO.println s!"NATIVE CODEC RUNTIME PASS: {tests.length} checks."
