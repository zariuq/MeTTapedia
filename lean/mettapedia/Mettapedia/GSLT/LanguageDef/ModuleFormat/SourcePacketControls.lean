import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceCompositionControls
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacket
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax

/-! Shared packet checks against all three authored lexical/syntax profiles.
These are frontend boundary controls, not source-to-IR or execution proofs. -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketControls

open SourcePacket

def node (label : String) (children : List Packet) : Packet :=
  .expression [.symbol "node", .symbol label,
    children.foldr (fun first rest => .expression [.symbol "pair", first, rest]) (.symbol "nil")]

def scalar (label : String) (point : Int) : Packet :=
  .expression [.symbol "node", .symbol label, .expression [.symbol "cp", .grounded (.int point)]]

def integer (point : Int) : Packet :=
  node "source-lex:integer"
    [node "source-lex:digits-one" [scalar "source-lex:scalar-Digit" point]]

def boundaryChecks (description : Portable.SyntaxDescription) : Bool :=
  let read := readback? description.grammar description.profile
  let good := integer 55
  read "SrcInteger" good == some "7" &&
  validates description.grammar description.profile "SrcInteger" "7" good &&
  !validates description.grammar description.profile "SrcInteger" "8" good &&
  read "SrcUpperName" good == none &&
  read "SrcInteger" (integer 65) == none &&
  read "SrcInteger" (integer (-1)) == none &&
  read "SrcInteger" (integer 55296) == none &&
  read "SrcInteger" (node "missing-production" []) == none &&
  read "SrcInteger" (node "source-lex:integer" []) == none &&
  read "SrcInteger" (node "source-lex:integer" [good, good]) == none &&
  read "SrcInteger" (.expression [.symbol "node", .symbol "source-lex:integer"]) == none &&
  description.grammar.terms.all (fun row => row.syntaxPattern.all fun
    | .terminal _ | .nonTerminal _ => true
    | _ => false)

#guard GoldCoreSyntax.OCaml.description?.any boundaryChecks
#guard GoldCoreSyntax.Erlang.description?.any boundaryChecks
#guard GoldCoreSyntax.Maude.description?.any boundaryChecks

/-- Two separately labelled productions may both read back to the same input;
the reader neither selects one packet nor identifies them. -/
def ambiguityChecks (description : Portable.SyntaxDescription) : Bool := Id.run do
  let some row := description.grammar.terms.find? (·.label == "source-lex:integer") | return false
  let alternate := {row with label := "packet-control:integer-alternate"}
  let grammar := {description.grammar with terms := description.grammar.terms ++ [alternate]}
  let original := integer 55
  let other := node alternate.label
    [node "source-lex:digits-one" [scalar "source-lex:scalar-Digit" 55]]
  return original != other && readback? grammar description.profile "SrcInteger" original == some "7" &&
    readback? grammar description.profile "SrcInteger" other == some "7" &&
    readback? {grammar with terms := grammar.terms ++ [row]} description.profile "SrcInteger" original == none

#guard GoldCoreSyntax.OCaml.description?.any ambiguityChecks
#guard GoldCoreSyntax.Erlang.description?.any ambiguityChecks
#guard GoldCoreSyntax.Maude.description?.any ambiguityChecks

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketControls
