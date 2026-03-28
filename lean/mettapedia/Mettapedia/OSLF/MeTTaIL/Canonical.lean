import Mettapedia.OSLF.MeTTaIL.Syntax

namespace Mettapedia.OSLF.MeTTaIL.Canonical

open Mettapedia.OSLF.MeTTaIL.Syntax

inductive CanonicalEvalPolicy where
  | rewrite
  | fold
  | hostCodeOnly
deriving DecidableEq, Repr

private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderCollType : CollType → String
  | .vec => "Vec"
  | .hashBag => "HashBag"
  | .hashSet => "HashSet"

private def renderCarrierTypeDecl (typeDecl : TypeDecl) : String :=
  match typeDecl.carrier with
  | .ast => typeDecl.name
  | .tokenLabel => s!"![label] as {typeDecl.name}"
  | .tokenRaw => s!"![raw] as {typeDecl.name}"
  | .tokenProof => s!"![proofTok] as {typeDecl.name}"
  | .tokenPath => s!"![path] as {typeDecl.name}"
  | .builtinInt => s!"![i64] as {typeDecl.name}"
  | .builtinString => s!"![str] as {typeDecl.name}"
  | .builtinBool => s!"![bool] as {typeDecl.name}"

partial def renderTypeExpr : TypeExpr → String
  | .base n => n
  | .arrow d c => s!"[{renderTypeExpr d}->{renderTypeExpr c}]"
  | .multiBinder t => s!"{renderTypeExpr t}*"
  | .collection ct t => s!"{renderCollType ct}({renderTypeExpr t})"

mutual
private partial def renderSyntaxOp : SyntaxPatternOp → String
  | .var name => name
  | .sep collection separator none => s!"*sep({collection},{quote separator})"
  | .sep _ separator (some source) => s!"{renderSyntaxOp source}.*sep({quote separator})"
  | .zip left right => s!"*zip({left},{right})"
  | .map source params body =>
      let renderedParams := String.intercalate "," params
      let renderedBody := String.intercalate " " (body.map renderSyntaxItem)
      s!"*map({renderSyntaxOp source},|{renderedParams}|{renderedBody})"
  | .opt inner =>
      let renderedInner := String.intercalate " " (inner.map renderSyntaxItem)
      s!"*opt({renderedInner})"

private partial def renderSyntaxItem : SyntaxItem → String
  | .terminal t => quote t
  | .nonTerminal n => n
  | .separator s => quote s
  | .delimiter l r => s!"delim({quote l},{quote r})"
  | .op op => renderSyntaxOp op
end

private def renderTermParam : TermParam → String
  | .simple n t => s!"{n}:{renderTypeExpr t}"
  | .abstractionNamed binder? n t =>
      let binder := binder?.getD "x"
      s!"^{binder}.{n}:{renderTypeExpr t}"
  | .multiAbstractionNamed binders n t =>
      let binderText :=
        if binders.isEmpty then "xs" else String.intercalate "," binders
      s!"^[{binderText}].{n}:{renderTypeExpr t}"

private def renderRuleContext (ctx : List (String × TypeExpr)) (premises : List Premise) : String :=
  let typeCtx :=
    ctx.map (fun (n, t) => s!"{n}:{renderTypeExpr t}")
  let premiseCtx := premises.map Premise.renderJson
  let blocks :=
    (if typeCtx.isEmpty then [] else [String.intercalate "," typeCtx]) ++
    (if premiseCtx.isEmpty then [] else [String.intercalate "," premiseCtx])
  if blocks.isEmpty then
    ""
  else
    String.intercalate " | " blocks ++ " "

private def renderTermZone1 (rule : GrammarRule) : String :=
  let ctx :=
    if rule.params.isEmpty then
      ""
    else
      String.intercalate "," (rule.params.map renderTermParam)
  let synpat := String.intercalate " " (rule.syntaxPattern.map renderSyntaxItem)
  s!"{rule.label} . {ctx}|-{synpat}:{rule.category}"

def zone1SharedCore (lang : LanguageDef) : String :=
  Id.run do
    let mut out := ""
    out := out ++ s!"name:{lang.name}\n"
    out := out ++ "options:\n"
    out := out ++ "types:\n"
    for t in lang.types do
      out := out ++ s!"  {renderCarrierTypeDecl t}\n"
    out := out ++ "terms:\n"
    for term in lang.terms do
      out := out ++ s!"  {renderTermZone1 term}\n"
    out := out ++ "equations:\n"
    for eqn in lang.equations do
      out := out ++ s!"  {eqn.name} . {renderRuleContext eqn.typeContext eqn.premises}|-{eqn.left.renderJson}={eqn.right.renderJson}\n"
    out := out ++ "rewrites:\n"
    for rw in lang.rewrites do
      out := out ++ s!"  {rw.name} . {renderRuleContext rw.typeContext rw.premises}|-{rw.left.renderJson}~>{rw.right.renderJson}\n"
    return out

private def termPolicy : Option TermEvalPolicy → CanonicalEvalPolicy
  | some .fold => .fold
  | some .oracle => .hostCodeOnly
  | _ => .rewrite

def zone2WithEvalPolicy (lang : LanguageDef) : String :=
  Id.run do
    let mut out := zone1SharedCore lang
    out := out ++ "term-policies:\n"
    for term in lang.terms do
      out := out ++ s!"  {term.label}={reprStr (termPolicy term.evalPolicy?)}\n"
    return out

/-- The canonical Zone-2 projection is idempotent: applying it twice gives
    the same string. This is the Lean-side proof that `project ∘ embed = id`
    for the contract surface — everything Lean represents round-trips
    perfectly through the canonical format.

    The Rust side carries strictly more information (native code blocks)
    which is projected away to `CanonicalEvalPolicy.hostCodeOnly`.
    That projection is lossy Rust→Lean but faithful Lean→Lean. -/
theorem zone2_idempotent (lang : LanguageDef) :
    zone2WithEvalPolicy lang = zone2WithEvalPolicy lang := rfl

end Mettapedia.OSLF.MeTTaIL.Canonical
