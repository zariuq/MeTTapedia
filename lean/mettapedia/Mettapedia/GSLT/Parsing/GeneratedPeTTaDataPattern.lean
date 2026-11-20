import Algorithms.MeTTa.Simple.Parser

/-!
# Structural patterns emitted by the direct PeTTa compiler

The native emitter's data-pattern branch writes an expression as nested
`cons-atom` patterns ending in `()`. Its input here is the rendered template:
source-variable spelling and scalar printing belong to the preceding renderer.
Leaves stay unchanged, including constructor names that also name operations.

The decoder and check consume complete emitted S-expression trees. This is a
compiler-evidence boundary; source reading and operational pattern matching
have their own contracts. No program is evaluated by this module.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Algorithms.MeTTa.Simple.Parser (SExpr)

mutual
  /-- A rendered atom stays an atom; an expression gets a structural spine. -/
  def encode : SExpr → SExpr
    | .atom token => .atom token
    | .list values => encodeList values

  def encodeList : List SExpr → SExpr
    | [] => .list []
    | first :: rest => .list [.atom "cons-atom", encode first, encodeList rest]
end

/-- Read exactly a complete structural data-pattern tree. A malformed spine
or an ordinary application is not an encoding of this compiler branch. -/
def decode : SExpr → Option SExpr
  | .atom token => some (.atom token)
  | .list [] => some (.list [])
  | .list [.atom "cons-atom", first, rest] => do
      let first ← decode first
      let rest ← decode rest
      match rest with
      | .list values => return .list (first :: values)
      | .atom _ => none
  | _ => none
termination_by term => sizeOf term

/-- An untrusted emitted tree must decode to the complete expected template. -/
def check (template emitted : SExpr) : Bool :=
  decide (decode emitted = some template)

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
