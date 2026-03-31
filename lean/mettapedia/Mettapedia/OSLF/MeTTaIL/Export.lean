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

/-- Sanitize an identifier for Rust compatibility.
    Replaces Unicode semantic operators with ASCII prefixes. -/
private def sanitizeForRust (s : String) : String :=
  s.replace "⊛" "sem_"

private def ctorName (raw : String) : String :=
  sanitizeForRust raw

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

def renderTypeExpr : TypeExpr → String
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

private def renderSyntaxOp : SyntaxPatternOp → String
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

private def renderSyntaxItem : SyntaxItem → String
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

private def renderEvalPolicySuffix (policy? : Option TermEvalPolicy) : String :=
  match policy? with
  | none => ""
  | some .rewrite => " ![rewrite]"
  | some .fold => " ![fold]"
  | some .oracle => " ![oracle]"

private theorem args_elem_lt_apply (c : String) (args : List Pattern) (a : Pattern)
    (h : a ∈ args) : sizeOf a < sizeOf (Pattern.apply c args) := by
  have := List.sizeOf_lt_of_mem h
  simp [Pattern.apply.sizeOf_spec]
  omega

def renderPattern : Pattern → String
  | .bvar n => s!"bvar{n}"
  | .fvar x => x
  | .apply c [] => ctorName c
  | .apply c [arg] => s!"({ctorName c} {renderPattern arg})"
  -- map: more specific binary pattern (second arg is multiLambda)
  | .apply c [source, .multiLambda _ params body] =>
      if c == Pattern.mapHead then
        let renderedParams := String.intercalate ", " params
        s!"{renderPattern source}.*map(|{renderedParams}| {renderPattern body})"
      else
        s!"({ctorName c} {renderPattern source} {renderPattern (.multiLambda 0 params body)})"
  -- zip/eval/generic binary
  | .apply c [first, second] =>
      if c == Pattern.zipHead then
        s!"*zip({renderPattern first}, {renderPattern second})"
      else if c == Pattern.evalHead then
        s!"(eval {renderPattern first} {renderPattern second})"
      else
        s!"({ctorName c} {renderPattern first} {renderPattern second})"
  -- n-ary (3+)
  | .apply c args =>
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
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (exact Nat.lt_trans (List.sizeOf_lt_of_mem ‹_›) (by omega))
    | (exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem ‹_›) (by omega))

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

private def renderPremises (overloaded : List String) (premises : List Premise) : String :=
  if premises.isEmpty then
    "|-"
  else
    s!"| {String.intercalate ", " (premises.map (renderPremise overloaded))} |-"

private def renderGrammarRule (rule : GrammarRule) : String :=
  let renderedParams := (indexed rule.params).map fun (idx, p) => renderTermParam idx p
  let paramBlock :=
    if renderedParams.isEmpty then
      ""
    else
      String.intercalate ", " renderedParams ++ " "
  let syntaxText := renderCtorSyntax rule.label rule.params
  s!"        {ctorName rule.label} . {paramBlock}|- {syntaxText} : {rule.category}{renderEvalPolicySuffix rule.evalPolicy?};"

private def renderGrammarRuleWithUserSyntax (rule : GrammarRule) : String :=
  let renderedParams := (indexed rule.params).map fun (idx, p) => renderTermParam idx p
  let paramBlock :=
    if renderedParams.isEmpty then
      ""
    else
      String.intercalate ", " renderedParams ++ " "
  let syntaxText := renderUserSyntax rule
  s!"        {ctorName rule.label} . {paramBlock}|- {syntaxText} : {rule.category}{renderEvalPolicySuffix rule.evalPolicy?};"

private def renderEquation (overloaded : List String) (_idx : Nat) (eqn : Equation) : String :=
  let gate := renderPremises overloaded eqn.premises
  s!"        {eqn.name} . {gate} {renderPattern eqn.left} = {renderPattern eqn.right};"

private def renderRewrite (overloaded : List String) (_idx : Nat) (rw : RewriteRule) : String :=
  let gate := renderPremises overloaded rw.premises
  s!"        {rw.name} . {gate} {renderPattern rw.left} ~> {renderPattern rw.right};"

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

/-- Render a DatalogTerm to Ascent-compatible syntax. -/
private def renderDatalogTerm : DatalogTerm → String
  | .var v => v
  | .const c => c

/-- Render a DatalogAtom to Ascent-compatible syntax. -/
private def renderDatalogAtom (a : DatalogAtom) : String :=
  s!"{a.rel}({String.intercalate ", " (a.args.map renderDatalogTerm)})"

/-- Render a DatalogClause to Ascent-compatible syntax. -/
private def renderDatalogClause (dc : DatalogClause) : String :=
  let head := renderDatalogAtom dc.head
  if dc.body.isEmpty then
    s!"        {head}."
  else
    let body := String.intercalate ", " (dc.body.map renderDatalogAtom)
    s!"        {head} :- {body}."

/-- Render a LogicDecl to Ascent-compatible syntax. -/
private def renderLogicDecl : LogicDecl → Option String
  | .relation sig =>
    let types := String.intercalate ", " (sig.argTypes.map renderTypeExpr)
    some s!"        relation {sig.name}({types});"
  | .ruleText t => some s!"        {t}"
  | .datalogClause dc => some (renderDatalogClause dc)

def renderLanguage (lang : LanguageDef) : String :=
  let overloaded := overloadedRelations lang
  let typeLines := lang.types.map (fun t => s!"        {renderTypeDecl t}")
  let termLines := lang.terms.map renderGrammarRule
  let eqLines := (indexed lang.equations).map (fun (idx, eqn) => renderEquation overloaded idx eqn)
  let rwLines := (indexed lang.rewrites).map (fun (idx, rw) => renderRewrite overloaded idx rw)
  let logicLines := lang.logic.filterMap renderLogicDecl
  let sections :=
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
    ] ++ (if logicLines.isEmpty then [] else
    [ ""
    , renderSection "logic" logicLines ++ ","
    ]) ++
    [ "}" ]
  String.intercalate "\n" sections

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
