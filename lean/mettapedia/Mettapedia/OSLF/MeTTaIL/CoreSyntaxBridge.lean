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

private def coreToSpecTypeDecl (typeName : String) : Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl :=
  Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl.plain typeName

private def specToCoreTypeName (typeDecl : Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl) : String :=
  typeDecl.name

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
  | .abstraction x t => .abstraction x (specToCoreTypeExpr t)
  | .multiAbstraction x t => .multiAbstraction x (specToCoreTypeExpr t)

def specToCoreSyntaxItem : SpecSyntaxItem → CoreSyntaxItem
  | .terminal s => .terminal s
  | .nonTerminal s => .nonTerminal s
  | .separator s => .separator s
  | .delimiter a b => .delimiter a b

def specToCoreGrammarRule (g : SpecGrammarRule) : CoreGrammarRule :=
  { label := g.label
    category := g.category
    params := g.params.map specToCoreTermParam
    syntaxPattern := g.syntaxPattern.map specToCoreSyntaxItem }

def specToCorePattern : SpecPattern → CorePattern
  | .bvar n => .bvar n
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map specToCorePattern)
  | .lambda body => .lambda (specToCorePattern body)
  | .multiLambda n body => .multiLambda n (specToCorePattern body)
  | .subst body repl => .subst (specToCorePattern body) (specToCorePattern repl)
  | .collection ct elems rest =>
      .collection (specToCoreCollType ct) (elems.map specToCorePattern) rest

def specToCoreFreshness (fc : SpecFreshnessCondition) : CoreFreshnessCondition :=
  { varName := fc.varName
    term := specToCorePattern fc.term }

def specToCorePremise : SpecPremise → CorePremise
  | .freshness fc => .freshness (specToCoreFreshness fc)
  | .congruence a b => .congruence (specToCorePattern a) (specToCorePattern b)
  | .relationQuery rel args => .relationQuery rel (args.map specToCorePattern)
  | .forAll _ _ body => specToCorePremise body

def specToCoreEquation (eqn : SpecEquation) : CoreEquation :=
  { name := eqn.name
    typeContext := eqn.typeContext.map (fun (x, t) => (x, specToCoreTypeExpr t))
    premises := eqn.premises.map specToCorePremise
    left := specToCorePattern eqn.left
    right := specToCorePattern eqn.right }

def specToCoreRewriteRule (r : SpecRewriteRule) : CoreRewriteRule :=
  { name := r.name
    typeContext := r.typeContext.map (fun (x, t) => (x, specToCoreTypeExpr t))
    premises := r.premises.map specToCorePremise
    left := specToCorePattern r.left
    right := specToCorePattern r.right }

def specToCoreLanguage (lang : SpecLanguageDef) : CoreLanguageDef :=
  { name := lang.name
    types := lang.types.map specToCoreTypeName
    terms := lang.terms.map specToCoreGrammarRule
    equations := lang.equations.map specToCoreEquation
    rewrites := lang.rewrites.map specToCoreRewriteRule
    congruenceCollections := lang.congruenceCollections.map
      (fun ct => ({ collectionType := specToCoreCollType ct } : MeTTailCore.MeTTaIL.Syntax.CongruenceCollection)) }

end Mettapedia.OSLF.MeTTaIL.CoreSyntaxBridge
