import Mettapedia.GSLT.Parsing.KeyedParserDispatch

/-!
# Stable data boundary for Lean parser descriptions

This schema retains descriptor structure, exact names and every option.
Named aliases and parser declarations remain references to implementations;
describing or exporting them does not prove their parsing semantics.
Version-specific Lean imports belong in the adapter, not in this schema.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.ParserDescription

inductive Name where
  | anonymous
  | str (parent : Name) (component : String)
  | num (parent : Name) (component : Nat)
  deriving DecidableEq, Repr

inductive Description where
  | constant (name : Name)
  | unary (name : Name) (body : Description)
  | binary (name : Name) (left right : Description)
  | node (kind : Name) (precedence : Nat) (body : Description)
  | trailingNode (kind : Name) (precedence leftPrecedence : Nat) (body : Description)
  | symbol (text : String)
  | nonReservedSymbol (text : String) (includeIdent : Bool)
  | category (name : Name) (precedence : Nat)
  | parser (declaration : Name)
  | nodeWithAntiquot (name : String) (kind : Name) (body : Description)
  | sepBy (body : Description) (separator : String) (separatorParser : Description) (trailing : Bool)
  | sepBy1 (body : Description) (separator : String) (separatorParser : Description) (trailing : Bool)
  | unicodeSymbol (text ascii : String) (preserveForPrinting : Bool)
  deriving DecidableEq, Repr

inductive Reference where
  | alias (name : Name) (arity : Nat)
  | category (name : Name)
  | parser (name : Name)
  deriving DecidableEq, Repr

/-- Implementations that must be supplied before the descriptor can be
realized; repeated references retain their occurrence order. -/
def dependencies : Description → List Reference
  | .constant name => [.alias name 0]
  | .unary name body => .alias name 1 :: dependencies body
  | .binary name left right => .alias name 2 :: dependencies left ++ dependencies right
  | .node _ _ body | .trailingNode _ _ _ body | .nodeWithAntiquot _ _ body => dependencies body
  | .category name _ => [.category name]
  | .parser name => [.parser name]
  | .sepBy body _ separator _ | .sepBy1 body _ separator _ => dependencies body ++ dependencies separator
  | .symbol _ | .nonReservedSymbol _ _ | .unicodeSymbol _ _ _ => []

structure Packet where
  profile : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Profile
  declaration : Name
  phase : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Phase
  description : Description
  deriving DecidableEq, Repr

/-- Serialized declaration registrations. Scope operations and local entries
are additional events; this inventory alone is not the effective grammar. -/
inductive RegistryEntry where
  | token (text : String)
  | kind (name : Name)
  | category (name declaration : Name)
      (behavior : Mettapedia.GSLT.Parsing.KeyedParserDispatch.IdentBehavior)
  | parser (category declaration : Name) (priority : Nat)
  deriving DecidableEq, Repr

def admitted (expected : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Profile) (packet : Packet) : Bool :=
  decide (packet.profile = expected)

theorem admitted_iff (expected : Mettapedia.GSLT.Parsing.KeyedParserDispatch.Profile) (packet : Packet) :
    admitted expected packet = true ↔ packet.profile = expected := by
  simp [admitted]

end Mettapedia.Languages.Lean.ParserDescription
