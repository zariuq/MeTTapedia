import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Reader-independent ground-atom wire

Generated build artifacts cannot rely on a host reader assigning the same
meaning to every bare spelling.  This codec represents every atom constructor
with fixed safe tags and puts all user spellings in grounded strings.  It is a
data wire only: decoding never evaluates the represented atom.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GroundAtomWireV1

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

mutual
  def encode : Atom → Atom
    | .symbol name =>
      .expression [.symbol "ground-atom-symbol-v1", .grounded (.string name)]
    | .var name =>
      .expression [.symbol "ground-atom-variable-v1", .grounded (.string name)]
    | .grounded (.int value) =>
      .expression [.symbol "ground-atom-integer-v1", .grounded (.int value)]
    | .grounded (.string value) =>
      .expression [.symbol "ground-atom-string-v1", .grounded (.string value)]
    | .grounded (.bool false) =>
      .expression [.symbol "ground-atom-boolean-v1", .symbol "false"]
    | .grounded (.bool true) =>
      .expression [.symbol "ground-atom-boolean-v1", .symbol "true"]
    | .grounded (.custom typeName data) =>
      .expression [.symbol "ground-atom-custom-v1",
        .grounded (.string typeName), .grounded (.string data)]
    | .expression items =>
      .expression [.symbol "ground-atom-expression-v1",
        .expression (encodeList items)]
  termination_by atom => sizeOf atom

  def encodeList : List Atom → List Atom
    | [] => []
    | head :: tail => encode head :: encodeList tail
  termination_by items => sizeOf items
end

mutual
  def decode : Atom → Option Atom
    | .expression [.symbol "ground-atom-symbol-v1", .grounded (.string name)] =>
      some (.symbol name)
    | .expression [.symbol "ground-atom-variable-v1", .grounded (.string name)] =>
      some (.var name)
    | .expression [.symbol "ground-atom-integer-v1", .grounded (.int value)] =>
      some (.grounded (.int value))
    | .expression [.symbol "ground-atom-string-v1", .grounded (.string value)] =>
      some (.grounded (.string value))
    | .expression [.symbol "ground-atom-boolean-v1", .symbol "false"] =>
      some (.grounded (.bool false))
    | .expression [.symbol "ground-atom-boolean-v1", .symbol "true"] =>
      some (.grounded (.bool true))
    | .expression [.symbol "ground-atom-custom-v1", .grounded (.string typeName),
      .grounded (.string data)] =>
      some (.grounded (.custom typeName data))
    | .expression [.symbol "ground-atom-expression-v1", .expression items] => do
      let decoded ← decodeList items
      some (.expression decoded)
    | _ => none
  termination_by atom => sizeOf atom

  def decodeList : List Atom → Option (List Atom)
    | [] => some []
    | head :: tail => do
        let decodedHead ← decode head
        let decodedTail ← decodeList tail
        some (decodedHead :: decodedTail)
  termination_by items => sizeOf items
end

mutual
  theorem decode_encode (atom : Atom) : decode (encode atom) = some atom := by
    match atom with
    | .symbol _ | .var _ | .grounded (.int _) | .grounded (.string _) |
        .grounded (.custom _ _) => simp [encode, decode]
    | .grounded (.bool false) | .grounded (.bool true) => simp [encode, decode]
    | .expression items =>
        simp [encode, decode, decodeList_encodeList items]
  termination_by structural atom

  theorem decodeList_encodeList (items : List Atom) :
      decodeList (encodeList items) = some items := by
    match items with
    | [] => simp [encodeList, decodeList]
    | head :: tail =>
        simp [encodeList, decodeList, decode_encode head,
          decodeList_encodeList tail]
  termination_by structural items
end

/-- Bare host literals remain strings inside the wire rather than being
reinterpreted by the reader. -/
example : decode (encode (.symbol "True")) = some (.symbol "True") := by
  exact decode_encode _

/-- Malformed constructor arity is rejected. -/
example : decode (.expression [.symbol "ground-atom-symbol-v1"]) = none := by
  simp [decode]

end Mettapedia.GSLT.Parsing.GroundAtomWireV1
