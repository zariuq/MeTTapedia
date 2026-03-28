import MeTTailCore
import Mettapedia.OSLF.MeTTaIL.Syntax

namespace Mettapedia.OSLF.MeTTaIL.CoreSyntaxBridge

abbrev CoreCollType := MeTTailCore.MeTTaIL.Syntax.CollType
abbrev SpecCollType := Mettapedia.OSLF.MeTTaIL.Syntax.CollType

abbrev CoreTypeExpr := MeTTailCore.MeTTaIL.Syntax.TypeExpr
abbrev SpecTypeExpr := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr

abbrev CoreTermParam := MeTTailCore.MeTTaIL.Syntax.TermParam
abbrev SpecTermParam := Mettapedia.OSLF.MeTTaIL.Syntax.TermParam

abbrev CoreSyntaxItem := MeTTailCore.MeTTaIL.Syntax.SyntaxItem
abbrev SpecSyntaxItem := Mettapedia.OSLF.MeTTaIL.Syntax.SyntaxItem

abbrev CoreGrammarRule := MeTTailCore.MeTTaIL.Syntax.GrammarRule
abbrev SpecGrammarRule := Mettapedia.OSLF.MeTTaIL.Syntax.GrammarRule

abbrev CorePattern := MeTTailCore.MeTTaIL.Syntax.Pattern
abbrev SpecPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

abbrev CoreFreshnessCondition := MeTTailCore.MeTTaIL.Syntax.FreshnessCondition
abbrev SpecFreshnessCondition := Mettapedia.OSLF.MeTTaIL.Syntax.FreshnessCondition

abbrev CorePremise := MeTTailCore.MeTTaIL.Syntax.Premise
abbrev SpecPremise := Mettapedia.OSLF.MeTTaIL.Syntax.Premise

abbrev CoreEquation := MeTTailCore.MeTTaIL.Syntax.Equation
abbrev SpecEquation := Mettapedia.OSLF.MeTTaIL.Syntax.Equation

abbrev CoreRewriteRule := MeTTailCore.MeTTaIL.Syntax.RewriteRule
abbrev SpecRewriteRule := Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule

abbrev CoreLanguageDef := MeTTailCore.MeTTaIL.Syntax.LanguageDef
abbrev SpecLanguageDef := Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef
abbrev SpecTypeDecl := Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl

private def coreToSpecTypeDecl (typeName : String) : Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl :=
  Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl.plain typeName

private def specToCoreTypeName (typeDecl : SpecTypeDecl) : Except String String := do
  match typeDecl.carrier with
  | .ast => pure typeDecl.name
  | carrier =>
      throw s!"Cannot lower type '{typeDecl.name}' with non-AST carrier '{repr carrier}' to core LanguageDef.types : List String."

def specToCoreCollType : SpecCollType → CoreCollType
  | .vec => .vec
  | .hashBag => .hashBag
  | .hashSet => .hashSet

def specToCoreTypeExpr : SpecTypeExpr → CoreTypeExpr
  | .base s => .base s
  | .arrow a b => .arrow (specToCoreTypeExpr a) (specToCoreTypeExpr b)
  | .multiBinder t => .multiBinder (specToCoreTypeExpr t)
  | .collection ct t => .collection (specToCoreCollType ct) (specToCoreTypeExpr t)

def specToCoreTermParam : SpecTermParam → CoreTermParam
  | .simple x t => .simple x (specToCoreTypeExpr t)
  | .abstractionNamed _ x t => .abstraction x (specToCoreTypeExpr t)
  | .multiAbstractionNamed _ x t => .multiAbstraction x (specToCoreTypeExpr t)

def specToCoreSyntaxItem : SpecSyntaxItem → Except String CoreSyntaxItem
  | .terminal s => pure (.terminal s)
  | .nonTerminal s => pure (.nonTerminal s)
  | .separator s => pure (.separator s)
  | .delimiter a b => pure (.delimiter a b)
  | .op _ =>
      throw "Cannot lower syntax metasyntax operators (*zip/*map/*opt/*sep chains) to core SyntaxItem; core only supports flat syntax items."

def specToCoreGrammarRule (g : SpecGrammarRule) : Except String CoreGrammarRule := do
  match g.evalPolicy? with
  | none => pure ()
  | some .rewrite => pure ()
  | some .fold =>
      throw s!"Cannot lower fold term `{g.label}` to core GrammarRule; core has no fold/native eval-policy form."
  | some .oracle =>
      throw s!"Cannot lower oracle term `{g.label}` to core GrammarRule; core has no oracle eval-policy form."
  let syntaxPattern ← g.syntaxPattern.mapM specToCoreSyntaxItem
  pure
    { label := g.label
      category := g.category
      params := g.params.map specToCoreTermParam
      syntaxPattern := syntaxPattern }

def specToCorePattern : SpecPattern → Except String CorePattern
  | .bvar n => pure (.bvar n)
  | .fvar x => pure (.fvar x)
  | pat@(.apply c args) =>
      match Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.zipArgs? pat with
      | some _ =>
          throw "Cannot lower rule-pattern *zip(...) to core Pattern; core only supports first-order constructor patterns."
      | none =>
          match Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.mapArgs? pat with
          | some _ =>
              throw "Cannot lower rule-pattern .*map(|...| ...) to core Pattern; core only supports first-order constructor patterns."
          | none =>
              match Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.evalArgs? pat with
              | some _ =>
                  throw "Cannot lower authored eval(...) pattern to core Pattern; core only supports explicit subst nodes."
              | none =>
                  do
                    let args' ← args.mapM specToCorePattern
                    pure (.apply c args')
  | .lambda _ body => do
      let body' ← specToCorePattern body
      pure (.lambda body')
  | .multiLambda n _ body => do
      let body' ← specToCorePattern body
      pure (.multiLambda n body')
  | .subst body repl => do
      let body' ← specToCorePattern body
      let repl' ← specToCorePattern repl
      pure (.subst body' repl')
  | .collection ct elems rest =>
      do
        let elems' ← elems.mapM specToCorePattern
        pure (.collection (specToCoreCollType ct) elems' rest)

def specToCoreFreshnessChecked (fc : SpecFreshnessCondition) :
    Except String CoreFreshnessCondition := do
  match fc.term.collectionRestName? with
  | some rest =>
      throw s!"Cannot lower freshness target `...{rest}` to core FreshnessCondition; core only supports direct pattern freshness."
  | none =>
      pure { varName := fc.varName, term := ← specToCorePattern fc.term }

def specToCorePremise : SpecPremise → Except String CorePremise
  | .freshness fc => return .freshness (← specToCoreFreshnessChecked fc)
  | .congruence a b => do
      let a' ← specToCorePattern a
      let b' ← specToCorePattern b
      pure (.congruence a' b')
  | .relationQuery rel args => do
      let args' ← args.mapM specToCorePattern
      pure (.relationQuery rel args')
  | .forAll collection _ _ =>
      throw s!"Cannot lower forAll premise over collection `{collection}` to core Premise; core has no quantified premise form."

def specToCoreEquation (eqn : SpecEquation) : Except String CoreEquation := do
  let premises ← eqn.premises.mapM specToCorePremise
  pure
    { name := eqn.name
      typeContext := eqn.typeContext.map (fun (x, t) => (x, specToCoreTypeExpr t))
      premises := premises
      left := ← specToCorePattern eqn.left
      right := ← specToCorePattern eqn.right }

def specToCoreRewriteRule (r : SpecRewriteRule) : Except String CoreRewriteRule := do
  let premises ← r.premises.mapM specToCorePremise
  pure
    { name := r.name
      typeContext := r.typeContext.map (fun (x, t) => (x, specToCoreTypeExpr t))
      premises := premises
      left := ← specToCorePattern r.left
      right := ← specToCorePattern r.right }

def specToCoreLanguage (lang : SpecLanguageDef) : Except String CoreLanguageDef := do
  let coreTypes ← lang.types.mapM specToCoreTypeName
  let coreTerms ← lang.terms.mapM specToCoreGrammarRule
  let coreEquations ← lang.equations.mapM specToCoreEquation
  let coreRewrites ← lang.rewrites.mapM specToCoreRewriteRule
  pure
    { name := lang.name
      types := coreTypes
      terms := coreTerms
      equations := coreEquations
      rewrites := coreRewrites
      congruenceCollections := lang.congruenceCollections.map
        (fun ct => ({ collectionType := specToCoreCollType ct } : MeTTailCore.MeTTaIL.Syntax.CongruenceCollection)) }

end Mettapedia.OSLF.MeTTaIL.CoreSyntaxBridge
