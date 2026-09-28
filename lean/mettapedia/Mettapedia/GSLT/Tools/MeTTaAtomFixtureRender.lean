import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Ground atom rendering for generated action controls

This renderer is restricted to fixture atoms. It rejects variables, opaque
grounded values, and symbols requiring a host lexical encoding. It is not a
TPTP printer or a general MeTTa interchange format.
-/

namespace Mettapedia.GSLT.Tools.MeTTaAtomFixtureRender

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

private def fixtureSymbol (name : String) : Bool :=
  !name.isEmpty && !(name.startsWith "$" || name.startsWith "&") &&
    name.toList.all (fun c => !c.isWhitespace &&
      !(['(', ')', '"', ';', '\\', '\x00'].contains c))

mutual
  def render : Atom → Except String String
    | .symbol name =>
        if fixtureSymbol name then .ok name else .error "fixture symbol needs lexical encoding"
    | .grounded (.int value) => .ok (toString value)
    | .grounded (.string value) => .ok (reprStr value)
    | .expression items => do
        let rendered ← renderList items
        return "(" ++ String.intercalate " " rendered ++ ")"
    | .var _ => .error "fixture variables are not ground"
    | .grounded _ => .error "opaque fixture value has no wire encoding"

  def renderList : List Atom → Except String (List String)
    | [] => .ok []
    | head :: tail => do
        let first ← render head
        let rest ← renderList tail
        return first :: rest
end

end Mettapedia.GSLT.Tools.MeTTaAtomFixtureRender
