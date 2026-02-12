import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# MeTTaIL Macro Export

Render a Lean `LanguageDef` into Rust `language! { ... }` macro text so Lean can
act as the source-of-truth for language definitions consumed by `mettail-rust`.
-/

namespace Mettapedia.OSLF.MeTTaIL.Export

open Mettapedia.OSLF.MeTTaIL.Syntax

private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def ctorName (raw : String) : String :=
  "C_" ++ raw

private def renderCollType : CollType → String
  | .vec => "Vec"
  | .hashBag => "HashBag"
  | .hashSet => "HashSet"

partial def renderTypeExpr : TypeExpr → String
  | .base n => n
  | .arrow d c => s!"[{renderTypeExpr d} -> {renderTypeExpr c}]"
  | .multiBinder t => s!"{renderTypeExpr t}*"
  | .collection ct t => s!"{renderCollType ct}({renderTypeExpr t})"

private def renderParamSyntaxTokens (idx : Nat) : TermParam → List String
  | .simple n _ => [n]
  | .abstraction n _ => [quote "^", s!"x{idx}", quote ".", n]
  | .multiAbstraction n _ => [quote "^[", s!"xs{idx}", quote "].", n]

private def renderTermParam (idx : Nat) : TermParam → String
  | .simple n t => s!"{n}:{renderTypeExpr t}"
  | .abstraction n t => s!"^x{idx}.{n}:{renderTypeExpr t}"
  | .multiAbstraction n t => s!"^[xs{idx}].{n}:{renderTypeExpr t}"

private def indexed {α : Type} (xs : List α) : List (Nat × α) :=
  let rec go (i : Nat) : List α → List (Nat × α)
    | [] => []
    | x :: rest => (i, x) :: go (i + 1) rest
  go 0 xs

private def commaJoin (parts : List (List String)) : List String :=
  match parts with
  | [] => []
  | first :: rest =>
      rest.foldl (fun acc p => acc ++ [quote ","] ++ p) first

private def renderTermSyntax (label : String) (params : List TermParam) : String :=
  let paramTokens := (indexed params).map fun (idx, p) => renderParamSyntaxTokens idx p
  match paramTokens with
  | [] => quote (ctorName label)
  | _ =>
      let args := commaJoin paramTokens
      String.intercalate " " ([quote (ctorName label), quote "("] ++ args ++ [quote ")"])

partial def renderPattern : Pattern → String
  | .bvar n => s!"bvar{n}"
  | .fvar x => x
  | .apply c [] => ctorName c
  | .apply c args =>
      let renderedArgs := args.map renderPattern
      s!"({ctorName c} {String.intercalate " " renderedArgs})"
  | .lambda body => s!"^x.{renderPattern body}"
  | .multiLambda _ body => s!"^[xs].{renderPattern body}"
  | .subst body repl => s!"(eval {renderPattern body} {renderPattern repl})"
  | .collection .hashBag elems rest =>
      let rendered := elems.map renderPattern
      let core := String.intercalate ", " rendered
      match rest with
      | none => "{" ++ core ++ "}"
      | some r =>
          if core.isEmpty then
            "{..." ++ r ++ "}"
          else
            "{" ++ core ++ ", ..." ++ r ++ "}"
  | .collection .vec elems rest =>
      let rendered := elems.map renderPattern
      let core := String.intercalate ", " rendered
      match rest with
      | none => "[" ++ core ++ "]"
      | some r =>
          if core.isEmpty then
            "[..." ++ r ++ "]"
          else
            "[" ++ core ++ ", ..." ++ r ++ "]"
  | .collection .hashSet elems rest =>
      let rendered := elems.map renderPattern
      let core := String.intercalate ", " rendered
      match rest with
      | none => "#{" ++ core ++ "}"
      | some r =>
          if core.isEmpty then
            "#{..." ++ r ++ "}"
          else
            "#{" ++ core ++ ", ..." ++ r ++ "}"

private def renderPremise : Premise → String
  | .freshness fc => s!"{fc.varName} # {renderPattern fc.term}"
  | .congruence src tgt => s!"{renderPattern src} ~> {renderPattern tgt}"
  | .relationQuery rel args =>
      s!"{rel}({String.intercalate ", " (args.map renderPattern)})"

private def renderGrammarRule (rule : GrammarRule) : String :=
  let renderedParams := (indexed rule.params).map fun (idx, p) => renderTermParam idx p
  let paramBlock :=
    if renderedParams.isEmpty then
      ""
    else
      String.intercalate ", " renderedParams ++ " "
  let syntaxText := renderTermSyntax rule.label rule.params
  s!"        {ctorName rule.label} . {paramBlock}|- {syntaxText} : {rule.category};"

private def renderEquation (idx : Nat) (eqn : Equation) : String :=
  let gate :=
    if eqn.premises.isEmpty then
      "|-"
    else
      s!"| {String.intercalate ", " (eqn.premises.map renderPremise)} |-"
  s!"        E{idx} . {gate} {renderPattern eqn.left} = {renderPattern eqn.right};"

private def renderRewrite (idx : Nat) (rw : RewriteRule) : String :=
  let gate :=
    if rw.premises.isEmpty then
      "|-"
    else
      s!"| {String.intercalate ", " (rw.premises.map renderPremise)} |-"
  s!"        R{idx} . {gate} {renderPattern rw.left} ~> {renderPattern rw.right};"

private def renderSection (title : String) (lines : List String) : String :=
  let body :=
    if lines.isEmpty then
      ""
    else
      "\n" ++ String.intercalate "\n" lines ++ "\n"
  "    " ++ title ++ " {" ++ body ++ "    }"

/-- Render a Lean `LanguageDef` into Rust `language! { ... }` macro text. -/
def renderLanguage (lang : LanguageDef) : String :=
  let typeLines := lang.types.map (fun t => s!"        {t}")
  let termLines := lang.terms.map renderGrammarRule
  let eqLines := (indexed lang.equations).map (fun (idx, eqn) => renderEquation idx eqn)
  let rwLines := (indexed lang.rewrites).map (fun (idx, rw) => renderRewrite idx rw)
  String.intercalate "\n"
    [ "language! {"
    , s!"    name: {lang.name},"
    , ""
    , renderSection "types" typeLines ++ ","
    , ""
    , renderSection "terms" termLines ++ ","
    , ""
    , renderSection "equations" eqLines ++ ","
    , ""
    , renderSection "rewrites" rwLines ++ ","
    , "}"
    ]

/-- Write rendered macro text to a file. -/
def writeLanguage (path : System.FilePath) (lang : LanguageDef) : IO Unit := do
  IO.FS.writeFile path (renderLanguage lang ++ "\n")

end Mettapedia.OSLF.MeTTaIL.Export
