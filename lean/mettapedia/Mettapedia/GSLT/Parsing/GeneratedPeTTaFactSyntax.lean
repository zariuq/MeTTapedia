import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

/-!
# Whole-clause checking for the generic unconditional emission branch

This boundary starts with an already rendered unconditional rule head.
The clause includes a fresh input slot, its complete structural pattern and
the quoted result. The actual emitted equation is checked as a whole tree.
Source rendering, mode analysis and execution have separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax

open Algorithms.MeTTa.Simple.Parser (SExpr)

mutual
  def containsToken (token : String) : SExpr → Bool
    | .atom other => token == other
    | .list terms => containsTokenList token terms

  def containsTokenList (token : String) : List SExpr → Bool
    | [] => false
    | first :: rest => containsToken token first || containsTokenList token rest
end

def freshSlot (head : SExpr) (slot : String) : Bool :=
  slot.startsWith "$" && slot != "$" && slot != "$_" && !containsToken slot head

/-- The direct compiler's generic fact equation, with an explicit slot. -/
def equation (relation slot : String) (arguments : List SExpr) : SExpr :=
  let head := SExpr.list (.atom relation :: arguments)
  .list [.atom "=", .list [.atom ("gslt:" ++ relation), .atom slot],
    .list [.atom "let", GeneratedPeTTaDataPattern.encode head, .atom slot,
      .list [.atom "quote", head]]]

def equation? (head : SExpr) (slot : String) : Option SExpr :=
  match head with
  | .list (.atom relation :: arguments) => some (equation relation slot arguments)
  | _ => none

/-- Read a proposed slot; the whole equation is validated subsequently. -/
def inputSlot? : SExpr → Option String
  | .list [.atom "=", .list [_, .atom slot], _] => some slot
  | _ => none

/-- Inspect the selector and the protected echo in an emitted equation.
Only the whole-clause check establishes that they match the source head. -/
def bodyParts? : SExpr → Option (SExpr × SExpr)
  | .list [.atom "=", _,
      .list [.atom "let", selector, _, .list [.atom "quote", echo]]] => some (selector, echo)
  | _ => none

def check (head emitted : SExpr) : Bool :=
  match inputSlot? emitted with
  | none => false
  | some slot =>
      freshSlot head slot &&
        match equation? head slot with
        | none => false
        | some expected => decide (emitted = expected)

/-- Source and emitted occurrences are paired in order, without truncation
or deduplication. Missing and additional clauses fail the evidence check. -/
def checkMany : List SExpr → List SExpr → Bool
  | [], [] => true
  | head :: heads, emitted :: equations => check head emitted && checkMany heads equations
  | _, _ => false

end Mettapedia.GSLT.Parsing.GeneratedPeTTaFactSyntax
