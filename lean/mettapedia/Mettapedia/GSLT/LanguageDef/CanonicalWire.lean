import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Canonical five-field LanguageDef wire projection

This renderer is deliberately partial.  It accepts the first-order constructor,
free-variable, application, and relation-query profile used by the DA and C1
presentations, and rejects unsupported syntax rather than erasing it.
-/

namespace Mettapedia.GSLT.LanguageDef.CanonicalWire

open Mettapedia.OSLF.MeTTaIL.Syntax

private def quote (text : String) : String :=
  "\"" ++ (text.replace "\\" "\\\\").replace "\"" "\\\"" ++ "\""

private def renderList (entries : List String) : String :=
  entries.foldr (fun entry rest => s!"(LCons {entry} {rest})") "LNil"

private def renderCarrier : CarrierKind → String
  | .ast => "CarrierAst"
  | .tokenLabel => "CarrierTokenLabel"
  | .tokenRaw => "CarrierTokenRaw"
  | .tokenProof => "CarrierTokenProof"
  | .tokenPath => "CarrierTokenPath"
  | .builtinInt => "CarrierBuiltinInt"
  | .builtinString => "CarrierBuiltinString"
  | .builtinBool => "CarrierBuiltinBool"

private def renderTypeDecl (declaration : TypeDecl) : String :=
  s!"(TypeDecl {quote declaration.name} {renderCarrier declaration.carrier})"

private def renderTypeExpr? : TypeExpr → Option String
  | .base name => some s!"(TBase {quote name})"
  | _ => none

private def renderTermParam? : TermParam → Option String
  | .simple name type => do
      let renderedType ← renderTypeExpr? type
      pure s!"(TermSimple {quote name} {renderedType})"
  | _ => none

private def renderSyntaxItem? : SyntaxItem → Option String
  | .terminal text => some s!"(SyntaxTerminal {quote text})"
  | .nonTerminal parameter =>
      some s!"(SyntaxNonTerminal {quote parameter})"
  | _ => none

private def renderEvalPolicy : Option TermEvalPolicy → String
  | none => "EvalNone"
  | some .rewrite => "(EvalSome EvalRewrite)"
  | some .fold => "(EvalSome EvalFold)"
  | some .oracle => "(EvalSome EvalOracle)"

private def renderGrammarRule? (rule : GrammarRule) : Option String := do
  let parameters ← rule.params.mapM renderTermParam?
  let renderedSyntax ← rule.syntaxPattern.mapM renderSyntaxItem?
  pure (s!"(GrammarRule {quote rule.label} {quote rule.category} " ++
    s!"{renderList parameters} {renderList renderedSyntax} " ++
    s!"{renderEvalPolicy rule.evalPolicy?})")

private def renderPattern? : Pattern → Option String
  | .fvar name => some s!"(FVar {quote name})"
  | .apply constructor arguments => do
      let renderedArguments ← arguments.mapM renderPattern?
      pure s!"(PApp {quote constructor} {renderList renderedArguments})"
  | _ => none
termination_by pattern => sizeOf pattern
decreasing_by
  all_goals simp_wf
  all_goals
    have _smaller := List.sizeOf_lt_of_mem ‹_›
    omega

private def renderPremise? : Premise → Option String
  | .relationQuery relation arguments => do
      let renderedArguments ← arguments.mapM renderPattern?
      pure s!"(RelationQuery {quote relation} {renderList renderedArguments})"
  | _ => none

private def renderTypeBinding? (binding : String × TypeExpr) : Option String := do
  let renderedType ← renderTypeExpr? binding.2
  pure s!"(TypeBinding {quote binding.1} {renderedType})"

private def renderRewrite? (rewrite : RewriteRule) : Option String := do
  let context ← rewrite.typeContext.mapM renderTypeBinding?
  let premises ← rewrite.premises.mapM renderPremise?
  let left ← renderPattern? rewrite.left
  let right ← renderPattern? rewrite.right
  pure (s!"(RewriteRule {quote rewrite.name} {renderList context} " ++
    s!"{renderList premises} {left} {right})")

/-- Partial structural projection into `GSLTLanguageDefWireV1`. -/
def renderLanguage? (language : LanguageDef) : Option String :=
  if language.equations.isEmpty then do
    let terms ← language.terms.mapM renderGrammarRule?
    let rewrites ← language.rewrites.mapM renderRewrite?
    pure (s!"(GSLTLanguageDefWireV1 {quote language.name}\n  " ++
      s!"{renderList (language.types.map renderTypeDecl)}\n  " ++
      s!"{renderList terms}\n  LNil\n  {renderList rewrites})\n")
  else
    none

end Mettapedia.GSLT.LanguageDef.CanonicalWire
