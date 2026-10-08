import Mettapedia.Logic.LP.ClauseSubsumptionEnumeration
import Lean.Data.Json

/-! Executable observations of complete clause witness enumeration. Target
variables have one scope for the whole clause, including unused literals. -/

namespace Mettapedia.Logic.LP.ClauseSubsumptionOracle

open ClauseSubsumption

abbrev sig : LPSignature :=
  { constants := Bool, vars := Nat, relationSymbols := Bool,
    relationArity := fun _ => 1, functionSymbols := Unit,
    functionArity := fun _ => 2 }

def p (t : Term sig) : SignedAtom sig := (true, Atom.mk true (fun _ => t))
def q (t : Term sig) : SignedAtom sig := (true, Atom.mk false (fun _ => t))
def neg (l : SignedAtom sig) : SignedAtom sig := (!l.1, l.2)
def f (a b : Term sig) : Term sig := .app () ![a, b]

abbrev SignedClause := ClauseSubsumption.Clause sig

def render : Term sig → String
  | .var n => "$v" ++ toString n
  | .const true => "a"
  | .const false => "b"
  | .app _ args => "(f " ++ render (args 0) ++ " " ++ render (args 1) ++ ")"

def expr (values : List String) : String := "(" ++ String.intercalate " " values ++ ")"
def renderLiteral (l : SignedAtom sig) : String :=
  expr [if l.1 then "pos" else "neg",
    expr [if l.2.symbol then "p" else "q", render (l.2.args 0)]]
def renderClause (c : SignedClause) : String := expr (c.map renderLiteral)

def sources : List SignedClause :=
  [[], [p (.var 0)], [q (.var 0)], [neg (p (.var 0))], [p (.const true)],
   [p (.var 0), q (.var 0)], [p (.var 0), q (.var 1)],
   [q (.var 0), p (.var 0)], [p (.var 0), p (.var 1)],
   [p (.var 0), neg (q (.var 0))], [p (f (.var 0) (.var 0))],
   [p (f (.var 0) (.var 1)), q (.var 0)]]

def targets : List SignedClause :=
  [[], [p (.const true)], [p (.const true), p (.const true)],
   [p (.const true), q (.const false)], [q (.const true), p (.const true)],
   [p (.var 2), q (.var 2)], [p (.var 2), q (.var 3)],
   [p (.const true), q (.var 0)], [p (.const true), neg (q (.const true))],
   [p (f (.var 2) (.var 2)), p (f (.var 2) (.var 3)), q (.var 2)]]

def row (consume : Bool) (source target : SignedClause) : Lean.Json :=
  let observe := fun answer : Subst sig => expr ["image",
    renderClause (source.map (apply answer)), renderClause (target.map (apply answer)),
    render (answer 0), render (answer 1)]
  Lean.Json.mkObj [
    ("policy", Lean.toJson (if consume then "multiset" else "set")),
    ("source", Lean.toJson (renderClause source)),
    ("target", Lean.toJson (renderClause target)),
    ("template", Lean.toJson (observe (Subst.id sig))),
    ("answers", Lean.toJson ((searchAll consume source target).map (observe ∘ Prod.snd)))]

def corpus : Lean.Json := Lean.Json.mkObj [
  ("schema", Lean.toJson (1 : Nat)),
  ("semantics", Lean.toJson "signed syntactic clauses; ordered complete alignment witnesses; shared protected target"),
  ("cases", Lean.toJson ([false, true].flatMap fun consume =>
    sources.flatMap fun source => targets.map (row consume source)))]

end Mettapedia.Logic.LP.ClauseSubsumptionOracle

def main : IO Unit := IO.println Mettapedia.Logic.LP.ClauseSubsumptionOracle.corpus.compress
