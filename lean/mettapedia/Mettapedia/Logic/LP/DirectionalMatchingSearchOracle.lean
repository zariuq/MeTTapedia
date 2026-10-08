import Mettapedia.Logic.LP.DirectionalMatchingSearch
import Mettapedia.Logic.LP.VariantMatching
import Lean.Data.Json

/-! Executable join observations, with scope separation at each row selection.
The corpus observes original rows, instantiated rows, occurrence positions and
all query-pattern images together, so variable aliases remain visible. -/

namespace Mettapedia.Logic.LP.DirectionalMatchingSearchOracle

open DirectionalMatching Mettapedia.Data.List.OrderedOccurrenceCursor

abbrev sig : LPSignature :=
  { constants := Bool, vars := Nat, relationSymbols := Unit,
    relationArity := fun _ => 0, functionSymbols := Unit,
    functionArity := fun _ => 2 }

def f (a b : Term sig) : Term sig := .app () ![a, b]

def render : Term sig → String
  | .var n => "$v" ++ toString n
  | .const true => "a"
  | .const false => "b"
  | .app _ args => "(f " ++ render (args 0) ++ " " ++ render (args 1) ++ ")"

def expr (values : List String) : String := "(" ++ String.intercalate " " values ++ ")"

def fixtures : List (List (Term sig)) :=
  [[], [f (.const true) (.const true)],
   [f (.const true) (.const true), f (.const true) (.const true),
    f (.const true) (.const false), f (.const false) (.const true)],
   [f (.var 0) (.var 0), f (.var 0) (.var 1), f (.const true) (.const true),
    f (.const true) (.const true), f (.var 0) (.const false)],
   [f (f (.var 0) (.const true)) (.var 0),
    f (f (.const true) (.const true)) (.const true), f (.const false) (.var 0)]]

def queries : List (List (Term sig)) :=
  [[], [f (.var 0) (.var 0)], [f (.var 0) (.var 1)],
   [f (.const true) (.var 1)], [f (.const true) (.const false)],
   [f (.var 0) (.var 0), f (.var 0) (.const true)],
   [f (.var 0) (.var 1), f (.var 1) (.var 0)],
   [f (.var 0) (.var 0), f (.var 1) (.var 1)],
   [f (.var 0) (.const true), f (.const true) (.var 1), f (.var 1) (.var 0)],
   [f (f (.var 0) (.const true)) (.var 0)]]

/-- Stored rows are independent scopes, even on two selections of one row.
This injection is per premise and row; observations are compared per answer. -/
def columns (rows : List (Term sig)) (patterns : List (Term sig)) : List (Column sig) :=
  patterns.zipIdx |>.map fun (pattern, premise) =>
    (pattern, rows.zipIdx |>.map fun (row, index) =>
      ⟨index, UnificationRenaming.rename (fun n => 1000 + 100 * premise + 4 * index + n) row⟩)

def solve (mode : String) (selected : Selection sig) : Option (Hit sig) := do
  let pairs := selectionPairs selected
  if mode == "variant" then
    let mapping ← VariantMatching.solve (pairs.map Prod.fst) (pairs.map Prod.snd)
    return (selected, fun n => .var (VariantMatching.lookup mapping n))
  else
    let answer ← matchMany (reversePairs pairs)
    return (selected, answer)

def observe (mode : String) (patterns : List (Term sig)) (hit : Hit sig) : String :=
  let rows := hit.1.map fun (pattern, row) =>
    let _ := pattern
    expr ["pat:row", expr ["pat:occurrence", "0", "0", toString row.identity],
      render row.value, render (if mode == "variant" then row.value else hit.2.applyTerm row.value)]
  expr ["pat:observed", expr rows,
    expr ("patterns" :: patterns.map (render ∘ hit.2.applyTerm))]

def row (mode : String) (rows patterns : List (Term sig)) : Lean.Json :=
  let cs := columns rows patterns
  let hits := if mode == "match%" then join cs []
    else (enumerate cs []).filterMap (solve mode)
  Lean.Json.mkObj [("mode", Lean.toJson mode),
    ("rows", Lean.toJson (rows.map render)),
    ("patterns", Lean.toJson (patterns.map render)),
    ("answers", Lean.toJson (hits.map (observe mode patterns)))]

def corpus : Lean.Json := Lean.Json.mkObj
  [("schema", Lean.toJson (1 : Nat)),
   ("semantics", Lean.toJson "ordered first-order joins; fresh row scopes; exact occurrence observations"),
   ("cases", Lean.toJson (["match%", "%match", "variant"].flatMap fun mode =>
      fixtures.flatMap fun rows => queries.map (row mode rows)))]

end Mettapedia.Logic.LP.DirectionalMatchingSearchOracle

def main : IO Unit :=
  IO.println Mettapedia.Logic.LP.DirectionalMatchingSearchOracle.corpus.compress
