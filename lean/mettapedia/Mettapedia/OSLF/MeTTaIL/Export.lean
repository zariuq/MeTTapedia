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
  raw

private def renderCollType : CollType → String
  | .vec => "Vec"
  | .hashBag => "HashBag"
  | .hashSet => "HashSet"

private def renderTypeDecl (typeDecl : TypeDecl) : String :=
  match typeDecl.carrier with
  | .ast => typeDecl.name
  | .tokenLabel => s!"![label] as {typeDecl.name}"
  | .tokenRaw => s!"![raw] as {typeDecl.name}"
  | .tokenProof => s!"![proofTok] as {typeDecl.name}"
  | .tokenPath => s!"![path] as {typeDecl.name}"
  -- CarrierKind models "builtin integer" abstractly; Rust export picks i64 as default.
  | .builtinInt => s!"![i64] as {typeDecl.name}"
  | .builtinString => s!"![str] as {typeDecl.name}"
  | .builtinBool => s!"![bool] as {typeDecl.name}"

partial def renderTypeExpr : TypeExpr → String
  | .base n => n
  | .arrow d c => s!"[{renderTypeExpr d} -> {renderTypeExpr c}]"
  | .multiBinder t => s!"{renderTypeExpr t}*"
  | .collection ct t => s!"{renderCollType ct}({renderTypeExpr t})"

private def renderParamSyntaxTokens (idx : Nat) : TermParam → List String
  | .simple n _ => [n]
  | .abstractionNamed binder? n _ =>
      let binder := binder?.getD s!"x{idx}"
      [quote "^", binder, quote ".", n]
  | .multiAbstractionNamed binders n _ =>
      let renderedBinders :=
        if binders.isEmpty then
          s!"xs{idx}"
        else
          String.intercalate "," binders
      [quote s!"^[{renderedBinders}].", n]

private def renderTermParam (idx : Nat) : TermParam → String
  | .simple n t => s!"{n}:{renderTypeExpr t}"
  | .abstractionNamed binder? n t =>
      let binder := binder?.getD s!"x{idx}"
      s!"^{binder}.{n}:{renderTypeExpr t}"
  | .multiAbstractionNamed binders n t =>
      let renderedBinders :=
        if binders.isEmpty then
          s!"xs{idx}"
        else
          String.intercalate "," binders
      s!"^[{renderedBinders}].{n}:{renderTypeExpr t}"

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

private def renderCtorSyntax (label : String) (params : List TermParam) : String :=
  let paramTokens := (indexed params).map fun (idx, p) => renderParamSyntaxTokens idx p
  match paramTokens with
  | [] => quote (ctorName label)
  | _ =>
      let args := commaJoin paramTokens
      String.intercalate " " ([quote (ctorName label), quote "("] ++ args ++ [quote ")"])

mutual

private partial def renderSyntaxOp : SyntaxPatternOp → String
  | .var name => name
  | .sep collection separator none => s!"{collection}.*sep({quote separator})"
  | .sep _ separator (some source) => s!"{renderSyntaxOp source}.*sep({quote separator})"
  | .zip left right => s!"*zip({left}, {right})"
  | .map source params body =>
      let renderedParams := String.intercalate ", " params
      let renderedBody := String.intercalate " " (body.map renderSyntaxItem)
      s!"{renderSyntaxOp source}.*map(|{renderedParams}| {renderedBody})"
  | .opt inner =>
      let renderedInner := String.intercalate " " (inner.map renderSyntaxItem)
      s!"*opt({renderedInner})"

private partial def renderSyntaxItem : SyntaxItem → String
  | .terminal t => quote t
  | .nonTerminal n => n
  | .separator s => quote s
  | .delimiter l r => String.intercalate " " [quote l, quote r]
  | .op op => renderSyntaxOp op

end

private def renderUserSyntax (rule : GrammarRule) : String :=
  let tokens := rule.syntaxPattern.map renderSyntaxItem
  if tokens.isEmpty then
    renderCtorSyntax rule.label rule.params
  else
    String.intercalate " " tokens

partial def renderPattern : Pattern → String
  | .bvar n => s!"bvar{n}"
  | .fvar x => x
  | pat@(.apply c args) =>
      match Pattern.zipArgs? pat with
      | some (first, second) =>
          s!"*zip({renderPattern first}, {renderPattern second})"
      | none =>
          match Pattern.mapArgs? pat with
          | some (source, params, body) =>
              let renderedParams := String.intercalate ", " params
              s!"{renderPattern source}.*map(|{renderedParams}| {renderPattern body})"
          | none =>
              match Pattern.evalArgs? pat with
              | some (scope, repl) =>
                  s!"(eval {renderPattern scope} {renderPattern repl})"
              | none =>
                  match args with
                  | [] => ctorName c
                  | _ =>
                      let renderedArgs := args.map renderPattern
                      s!"({ctorName c} {String.intercalate " " renderedArgs})"
  | .lambda (some nm) body => s!"^{nm}.{renderPattern body}"
  | .lambda none body => s!"^x.{renderPattern body}"
  | .multiLambda _ nms body =>
      let renderedBinders := if nms.isEmpty then "xs" else String.intercalate "," nms
      s!"^[{renderedBinders}].{renderPattern body}"
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

private def renderFreshnessTarget (pat : Pattern) : String :=
  match pat.collectionRestName? with
  | some rest => s!"...{rest}"
  | none => renderPattern pat

/-- Render a premise, disambiguating overloaded relation names by arity.
    `overloaded` is the set of relation names that appear with multiple arities. -/
private def renderPremise (overloaded : List String) : Premise → String
  | .freshness fc => s!"{fc.varName} # {renderFreshnessTarget fc.term}"
  | .congruence src tgt => s!"{renderPattern src} ~> {renderPattern tgt}"
  | .relationQuery rel args =>
      let name := if overloaded.contains rel then s!"{rel}{args.length}" else rel
      s!"{name}({String.intercalate ", " (args.map renderPattern)})"
  | .forAll collection param body =>
      s!"forAll({collection}, {param}, {renderPremise overloaded body})"

private def renderPremisesWithSurface (overloaded : List String) (premises : List Premise)
    (surface : List String) : String :=
  if premises.isEmpty then
    "|-"
  else
    let rendered :=
      if surface.length = premises.length then
        surface
      else
        premises.map (renderPremise overloaded)
    s!"| {String.intercalate ", " rendered} |-"

private def renderGrammarRule (rule : GrammarRule) : String :=
  let renderedParams := (indexed rule.params).map fun (idx, p) => renderTermParam idx p
  let paramBlock :=
    if renderedParams.isEmpty then
      ""
    else
      String.intercalate ", " renderedParams ++ " "
  let syntaxText := renderCtorSyntax rule.label rule.params
  s!"        {ctorName rule.label} . {paramBlock}|- {syntaxText} : {rule.category};"

private def renderGrammarRuleWithUserSyntax (rule : GrammarRule) : String :=
  let renderedParams := (indexed rule.params).map fun (idx, p) => renderTermParam idx p
  let paramBlock :=
    if renderedParams.isEmpty then
      ""
    else
      String.intercalate ", " renderedParams ++ " "
  let syntaxText := renderUserSyntax rule
  s!"        {ctorName rule.label} . {paramBlock}|- {syntaxText} : {rule.category};"

private def renderEquation (overloaded : List String) (_idx : Nat) (eqn : Equation) : String :=
  let gate := renderPremisesWithSurface overloaded eqn.premises eqn.premiseSurface
  let lhs := eqn.leftSurface?.getD (renderPattern eqn.left)
  let rhs := eqn.rightSurface?.getD (renderPattern eqn.right)
  s!"        {eqn.name} . {gate} {lhs} = {rhs};"

private def renderRewrite (overloaded : List String) (_idx : Nat) (rw : RewriteRule) : String :=
  let gate := renderPremisesWithSurface overloaded rw.premises rw.premiseSurface
  let lhs := rw.leftSurface?.getD (renderPattern rw.left)
  let rhs := rw.rightSurface?.getD (renderPattern rw.right)
  s!"        {rw.name} . {gate} {lhs} ~> {rhs};"

private def renderSection (title : String) (lines : List String) : String :=
  let body :=
    if lines.isEmpty then
      ""
    else
      "\n" ++ String.intercalate "\n" lines ++ "\n"
  "    " ++ title ++ " {" ++ body ++ "    }"

/-- Collect (relation-name, arity) pairs from all premises in a language. -/
private def collectRelationArities (lang : LanguageDef) : List (String × Nat) :=
  let rec fromPremise : Premise → List (String × Nat)
    | .relationQuery rel args => [(rel, args.length)]
    | .forAll _ _ body => fromPremise body
    | _ => []
  let fromPremises (ps : List Premise) : List (String × Nat) :=
    (ps.map fromPremise).flatten
  let fromEqs := (lang.equations.map (fun e => fromPremises e.premises)).flatten
  let fromRws := (lang.rewrites.map (fun r => fromPremises r.premises)).flatten
  fromEqs ++ fromRws

/-- Find relation names that appear with multiple distinct arities. -/
private def overloadedRelations (lang : LanguageDef) : List String :=
  let pairs := collectRelationArities lang
  let names := pairs.map Prod.fst |>.eraseDups
  names.filter fun name =>
    let arities := (pairs.filter (fun p => p.1 == name)).map Prod.snd |>.eraseDups
    arities.length > 1

/-- Render a Lean `LanguageDef` into Rust `language! { ... }` macro text. -/
def renderLanguage (lang : LanguageDef) : String :=
  let overloaded := overloadedRelations lang
  let typeLines := lang.types.map (fun t => s!"        {renderTypeDecl t}")
  let termLines := lang.terms.map renderGrammarRule
  let eqLines := (indexed lang.equations).map (fun (idx, eqn) => renderEquation overloaded idx eqn)
  let rwLines := (indexed lang.rewrites).map (fun (idx, rw) => renderRewrite overloaded idx rw)
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

/-- Render a Lean `LanguageDef` into Rust `language! { ... }` macro text,
using `syntaxPattern` for concrete term parsing when provided. -/
def renderLanguageWithUserSyntax (lang : LanguageDef) : String :=
  let overloaded := overloadedRelations lang
  let typeLines := lang.types.map (fun t => s!"        {renderTypeDecl t}")
  let termLines := lang.terms.map renderGrammarRuleWithUserSyntax
  let eqLines := (indexed lang.equations).map (fun (idx, eqn) => renderEquation overloaded idx eqn)
  let rwLines := (indexed lang.rewrites).map (fun (idx, rw) => renderRewrite overloaded idx rw)
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
