import Algorithms.MeTTa.HE.Lowering
import Algorithms.MeTTa.PeTTa.Lowering

namespace Algorithms.MeTTa.ProfileChecksum

open MeTTailCore.MeTTaIL.Syntax
open Algorithms.MeTTa.Simple
open Algorithms.MeTTa.HE
open Algorithms.MeTTa.PeTTa

private def mix (h n : Nat) : Nat :=
  (h * 16777619 + n + 2166136261) % 1000000007

private def checksumString (s : String) : Nat :=
  s.toList.foldl (fun h c => mix h c.toNat) 0

private def checksumOptionString : Option String → Nat
  | none => 11
  | some s => mix 13 (checksumString s)

private def checksumList (f : α → Nat) : List α → Nat
  | [] => 17
  | x :: xs => mix (f x) (checksumList f xs)

private def checksumCollType : CollType → Nat
  | .vec => 101
  | .hashBag => 103
  | .hashSet => 107

private def checksumTypeExpr : TypeExpr → Nat
  | .base s => mix 109 (checksumString s)
  | .arrow a b => mix 113 (mix (checksumTypeExpr a) (checksumTypeExpr b))
  | .multiBinder t => mix 127 (checksumTypeExpr t)
  | .collection ct t => mix 131 (mix (checksumCollType ct) (checksumTypeExpr t))

private def checksumTermParam : TermParam → Nat
  | .simple x t => mix 137 (mix (checksumString x) (checksumTypeExpr t))
  | .abstraction x t => mix 139 (mix (checksumString x) (checksumTypeExpr t))
  | .multiAbstraction x t => mix 149 (mix (checksumString x) (checksumTypeExpr t))

private def checksumSyntaxItem : SyntaxItem → Nat
  | .terminal s => mix 151 (checksumString s)
  | .nonTerminal s => mix 157 (checksumString s)
  | .separator s => mix 163 (checksumString s)
  | .delimiter a b => mix 167 (mix (checksumString a) (checksumString b))

private def checksumGrammarRule (g : GrammarRule) : Nat :=
  let h0 := mix 173 (checksumString g.label)
  let h1 := mix h0 (checksumString g.category)
  let h2 := mix h1 (checksumList checksumTermParam g.params)
  mix h2 (checksumList checksumSyntaxItem g.syntaxPattern)

mutual
  private def checksumPattern : Pattern → Nat
    | .bvar n => mix 179 n
    | .fvar x => mix 181 (checksumString x)
    | .apply c args => mix 191 (mix (checksumString c) (checksumPatternList args))
    | .lambda body => mix 193 (checksumPattern body)
    | .multiLambda n body => mix 197 (mix n (checksumPattern body))
    | .subst body repl => mix 199 (mix (checksumPattern body) (checksumPattern repl))
    | .collection ct elems rest =>
        mix 211 (mix (checksumCollType ct)
          (mix (checksumPatternList elems) (checksumOptionString rest)))

  private def checksumPatternList : List Pattern → Nat
    | [] => 17
    | x :: xs => mix (checksumPattern x) (checksumPatternList xs)
end

private def checksumFreshness (fc : FreshnessCondition) : Nat :=
  mix 223 (mix (checksumString fc.varName) (checksumPattern fc.term))

private def checksumPremise : Premise → Nat
  | .freshness fc => mix 227 (checksumFreshness fc)
  | .congruence src tgt => mix 229 (mix (checksumPattern src) (checksumPattern tgt))
  | .relationQuery rel args => mix 233 (mix (checksumString rel) (checksumList checksumPattern args))

private def checksumEquation (eqn : Equation) : Nat :=
  let h0 := mix 239 (checksumString eqn.name)
  let h1 := mix h0 (checksumList (fun (p : String × TypeExpr) =>
      mix (checksumString p.1) (checksumTypeExpr p.2)) eqn.typeContext)
  let h2 := mix h1 (checksumList checksumPremise eqn.premises)
  let h3 := mix h2 (checksumPattern eqn.left)
  mix h3 (checksumPattern eqn.right)

private def checksumRewriteRule (rule : RewriteRule) : Nat :=
  let h0 := mix 241 (checksumString rule.name)
  let h1 := mix h0 (checksumList (fun (p : String × TypeExpr) =>
      mix (checksumString p.1) (checksumTypeExpr p.2)) rule.typeContext)
  let h2 := mix h1 (checksumList checksumPremise rule.premises)
  let h3 := mix h2 (checksumPattern rule.left)
  mix h3 (checksumPattern rule.right)

private def checksumCongruenceCollection (cc : CongruenceCollection) : Nat :=
  mix 251 (checksumCollType cc.collectionType)

def checksumLanguageDef (lang : LanguageDef) : Nat :=
  let h0 := mix 257 (checksumString lang.name)
  let h1 := mix h0 (checksumList checksumString lang.types)
  let h2 := mix h1 (checksumList checksumGrammarRule lang.terms)
  let h3 := mix h2 (checksumList checksumEquation lang.equations)
  let h4 := mix h3 (checksumList checksumRewriteRule lang.rewrites)
  mix h4 (checksumList checksumCongruenceCollection lang.congruenceCollections)

def checksumRelationTuple (row : RelationTuple) : Nat :=
  mix 263 (mix (checksumString row.relation) (checksumList checksumPattern row.tuple))

mutual
  private def checksumFrozenHEAtom : FrozenHEAtom → Nat
    | .symbol s => mix 269 (checksumString s)
    | .variable s => mix 271 (checksumString s)
    | .expr xs => mix 277 (checksumFrozenHEAtomList xs)

  private def checksumFrozenHEAtomList : List FrozenHEAtom → Nat
    | [] => 17
    | x :: xs => mix (checksumFrozenHEAtom x) (checksumFrozenHEAtomList xs)
end

private def checksumFrozenHEPremise : FrozenHEPremise → Nat
  | .relationQuery rel args =>
      mix 281 (mix (checksumString rel) (checksumList checksumFrozenHEAtom args))

private def checksumFrozenHEEquation (eqn : FrozenHEEquation) : Nat :=
  let h0 := mix 283 (checksumFrozenHEAtom eqn.lhs)
  let h1 := mix h0 (checksumFrozenHEAtom eqn.rhs)
  mix h1 (checksumList checksumFrozenHEPremise eqn.premises)

private def checksumFrozenHERelationTuple (row : FrozenHERelationTuple) : Nat :=
  mix 293 (mix (checksumString row.relation) (checksumList checksumFrozenHEAtom row.tuple))

def checksumFrozenHEConfig (cfg : FrozenHEConfig) : Nat :=
  let h0 := mix 307 (checksumList checksumFrozenHEEquation cfg.equations)
  let h1 := mix h0 (checksumList checksumFrozenHERelationTuple cfg.relationFacts)
  let h2 := mix h1 (checksumList checksumFrozenHERelationTuple cfg.builtinFacts)
  let h3 := mix h2 cfg.maxSteps
  mix h3 cfg.maxNodes

private def checksumFrozenPeTTaPremise : FrozenPeTTaPremise → Nat
  | .relationQuery rel args =>
      mix 311 (mix (checksumString rel) (checksumList checksumPattern args))

private def checksumFrozenPeTTaRule (rule : FrozenPeTTaRule) : Nat :=
  let h0 := mix 313 (checksumPattern rule.lhs)
  let h1 := mix h0 (checksumPattern rule.rhs)
  mix h1 (checksumList checksumFrozenPeTTaPremise rule.premises)

def checksumFrozenPeTTaConfig (cfg : FrozenPeTTaConfig) : Nat :=
  let h0 := mix 317 (checksumList checksumFrozenPeTTaRule cfg.rules)
  let h1 := mix h0 (checksumList checksumPattern cfg.facts)
  let h2 := mix h1 (checksumList checksumRelationTuple cfg.relationFacts)
  let h3 := mix h2 (checksumList checksumRelationTuple cfg.builtinFacts)
  let h4 := mix h3 cfg.maxSteps
  mix h4 cfg.maxNodes

end Algorithms.MeTTa.ProfileChecksum
