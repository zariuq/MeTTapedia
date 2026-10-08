import Mettapedia.Logic.LP.DirectionalMatching
import Mettapedia.Logic.LP.VariantMatching
import Lean.Data.Json

/-!
Executable finite reference corpus for native matching correspondence checks.
The output includes complete observed variable images, not just success flags.
This uses the proved LP operations independently of the native graph matcher.
-/

namespace Mettapedia.Logic.LP.DirectionalMatchingOracle

abbrev sig : LPSignature :=
  { constants := Bool, vars := Nat, relationSymbols := Unit,
    relationArity := fun _ => 1, functionSymbols := Unit,
    functionArity := fun _ => 2 }

def pair (left right : Term sig) : Term sig := .app () ![left, right]

def render : Term sig → String
  | .var n => "$v" ++ toString n
  | .const true => "a"
  | .const false => "b"
  | .app _ args => "(f " ++ render (args 0) ++ " " ++ render (args 1) ++ ")"

def terms : List (Term sig) :=
  [.var 0, .var 1, .var 2, .const true, .const false,
   pair (.var 0) (.var 0), pair (.var 0) (.var 1),
   pair (.var 1) (.var 2), pair (.var 1) (.var 0),
   pair (.const true) (.const false), pair (.var 2) (.const true),
   pair (pair (.var 0) (.var 1)) (.var 0)]

def batches : List (List (Term sig × Term sig)) :=
  [[]] ++
  terms.flatMap (fun left => terms.map (fun right => [(left, right)])) ++
  terms.flatMap (fun subject =>
    [ [(.var 0, subject), (.var 0, .var 1)],
      [(.var 0, subject), (.var 0, .const true)],
      [(pair (.var 0) (.var 1), subject), (.var 1, .var 0)],
      [(.var 1, .var 0), (pair (.var 0) (.var 1), subject)] ])

def images (mode : String) (equations : List (Term sig × Term sig)) : Option (List (Term sig)) :=
  if mode == "variant" then do
    let mapping ← VariantMatching.solve (equations.map Prod.fst) (equations.map Prod.snd)
    return (List.range 3).map (fun n => .var (VariantMatching.lookup mapping n))
  else do
    let answer ← DirectionalMatching.matchMany
      (if mode == "%match" then DirectionalMatching.reversePairs equations else equations)
    return (List.range 3).map answer

def row (mode : String) (equations : List (Term sig × Term sig)) : Lean.Json :=
  let presentation := "(" ++ String.intercalate " "
    (equations.map fun pair => "(" ++ render pair.1 ++ " " ++ render pair.2 ++ ")") ++ ")"
  let output := match images mode equations with
    | none => Lean.Json.null
    | some values => Lean.toJson ("(slots " ++ String.intercalate " " (values.map render) ++ ")")
  Lean.Json.mkObj [("mode", Lean.toJson mode), ("pairs", Lean.toJson presentation), ("images", output)]

def corpus : Lean.Json := Lean.Json.mkObj
  [("schema", Lean.toJson (1 : Nat)),
   ("semantics", Lean.toJson "finite first-order terms; shared variable identities; simultaneous variants"),
   ("cases", Lean.toJson (["match%", "%match", "variant"].flatMap fun mode =>
      batches.map (row mode)))]

end Mettapedia.Logic.LP.DirectionalMatchingOracle

def main : IO Unit :=
  IO.println Mettapedia.Logic.LP.DirectionalMatchingOracle.corpus.compress
