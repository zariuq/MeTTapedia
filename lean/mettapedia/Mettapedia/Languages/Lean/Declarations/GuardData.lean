import Mettapedia.Languages.Lean.Declarations.GuardSyntax
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-! MeTTa data for scoped constructor laws, with explicit bound-variable nodes. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.GuardData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def node (name : String) (arguments : List Atom) : Atom :=
  .expression (.symbol name :: arguments)

def encode {depth : Nat} (environment : Fin depth → Atom) (next : Nat) :
    GuardSyntax.Term depth → Atom
  | .var position => environment position
  | .name identifier => node "const" [.symbol identifier]
  | .app function argument => node "app" [encode environment next function, encode environment next argument]
  | .pi domain body =>
      let binder := s!"q{next}"
      node "pi" [.symbol binder, encode environment next domain,
        encode (Fin.cases (node "bound" [.symbol binder]) environment) (next + 1) body]
  | .project owner field record =>
      node "project" [.symbol owner, .symbol (toString field), encode environment next record]

def termData (positions : List Nat) {depth : Nat} (term : GuardSyntax.Term depth) : Atom :=
  encode (fun position => node "field" [.symbol (toString (positions.getD position.val 0))]) 0 term

/-- A bound variable and a pre-existing field remain distinct below a binder. -/
example : termData (depth := 1) [7] (GuardSyntax.Term.pi (.name "A")
    (.app (.var 0) (.var 1))) =
    node "pi" [.symbol "q0", node "const" [.symbol "A"],
      node "app" [node "bound" [.symbol "q0"], node "field" [.symbol "7"]]] := rfl

end Mettapedia.Languages.Lean.Declarations.GuardData
