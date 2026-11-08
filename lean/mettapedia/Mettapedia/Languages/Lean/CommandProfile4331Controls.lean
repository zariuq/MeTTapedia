import Mettapedia.Languages.Lean.CommandProfile4331

/-! Live differential controls for the declared command grammar and pinned syntax adapter. -/

namespace Mettapedia.Languages.Lean.CommandProfile4331.Controls

open _root_.Lean _root_.Lean.Elab _root_.Lean.Elab.Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let scope ← getScope
  let tokens := (Parser.getTokenTable env).values.toList
  for input in ["namespace CEK", "namespace Mettapedia.Machines", "end CEK", "end", "section", "section Example",
      "open scoped Example", "open Example", "abbrev Env := List Val",
      "abbrev Steps : St → St → Prop := Relation.ReflTransGen StepRel",
      "/-! module documentation -/", "/-- documentation -/\nabbrev Env := List Val",
      "/-- documentation -/\ninductive Tm : Type\n  | var : Nat → Tm\n  | lit : Nat → Tm\nderiving Repr, DecidableEq",
      "/-- documentation -/\nstructure St where\n  ctl : Ctl\n  k : Kont",
      "abbrev X := (List Val)", "abbrev X := f (g a)", "abbrev X : Nat -> Nat := f",
      "inductive Empty", "inductive X where | mk : X", "structure X where\nx : Nat"] do
    let reference ← match ParserOracle4331.parse env scope `command input with
      | .ok tree => pure tree
      | .error error => throwError error
    let candidates := Mettapedia.GSLT.Parsing.LeanCommandProfile.parse tokens input (3 * input.toList.length + 32)
    if candidates.isEmpty then throwError "GSLT profile produced no candidate: {input}"
    for candidate in candidates do
      match compare 256 reference candidate with
      | .ok true => pure ()
      | .ok false =>
          let observed := observation 256 (command candidate)
          let detail := match observed with | .ok json => json.compress | .error error => error
          throwError "syntax mismatch for {input}: {detail}"
      | .error error => throwError error
    logInfo m!"GSLT syntax agrees: {input.take 55} ({candidates.length} candidates)"
  for input in ["structure X where\n  x : Nat\n y : Nat", "structure X where\n  x : Nat\n    y : Nat",
      "abbrev X :=", "namespace", "abbrev X := (Nat", "/-- unfinished"] do
    if let .ok _ := ParserOracle4331.parse env scope `command input then
      throwError "negative source unexpectedly accepted by Lean: {input}"
    unless (Mettapedia.GSLT.Parsing.LeanCommandProfile.parse tokens input (3 * input.toList.length + 32)).isEmpty do
      throwError "negative source unexpectedly accepted by GSLT: {input}"
  for (input, token) in [("abbrev X := freshLexicalProbe", "freshLexicalProbe"),
      ("abbrev X := (freshLexicalProbe)", "freshLexicalProbe)")] do
    let altered := Parser.parserExtension.addLocalEntry env (.token token)
    if let .ok _ := ParserOracle4331.parse altered scope `command input then
      throwError "new token did not supersede the identifier: {token}"
    let changedTokens := (Parser.getTokenTable altered).values.toList
    unless (Mettapedia.GSLT.Parsing.LeanCommandProfile.parse changedTokens input
        (3 * input.toList.length + 32)).isEmpty do
      throwError "lexical dependency was not observed: {token}"
  let source ← match ParserOracle4331.parse env scope `command "namespace Original" with
    | .ok tree => pure tree | .error error => throwError error
  unless compare 256 source (.namespace_ "Invented") == .ok false do
    throwError "changed syntax payload was accepted"
  logInfo "Negative syntax, layout, token-extension and wrong-tree controls passed"

end Mettapedia.Languages.Lean.CommandProfile4331.Controls
