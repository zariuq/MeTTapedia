import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.SpaceOps

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.Profile
open MeTTailCore.MeTTaIL.Match

structure Policy where
  selfSpaceAtom : Pattern := .apply "&self" []
  selfRelationName : String := "selfFact"
  relationNameOfSpace? : Pattern → Option String
  clearRewritesOnSelfRemoveAll : Bool := true
  loadSelfEqFactsAsRewrites : Bool := true

def defaultRelationNameOfSpace? : Pattern → Option String
  | .apply "&self" [] => some "selfFact"
  | .apply space [] =>
      if space.startsWith "&" then
        some s!"spaceFact:{space}"
      else
        none
  | _ => none

def defaultPolicy : Policy :=
  { relationNameOfSpace? := defaultRelationNameOfSpace? }

structure Interface (σ : Type) where
  bundle : σ → SpecBundle
  setBundle : σ → SpecBundle → σ
  eval : σ → Pattern → σ × List Pattern
  applyBindings : Bindings → Pattern → Pattern
  normalizePattern : Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings
  dedupPatterns : List Pattern → List Pattern

private def eqFactToRule? (idx : Nat) (fact : Pattern) : Option RewriteRule :=
  match fact with
  | .apply "=" [lhs, rhs] =>
      some
        { name := s!"SELF_FACT_RULE_{idx}"
          typeContext := []
          premises := []
          left := lhs
          right := rhs }
  | _ => none

private def removeRuleForEqFact (normalize : Pattern → Pattern)
    (rules : List RewriteRule) (fact : Pattern) : List RewriteRule :=
  match fact with
  | .apply "=" [lhs, rhs] =>
      let lhsN := normalize lhs
      let rhsN := normalize rhs
      rules.filter (fun r =>
        !(normalize r.left == lhsN && normalize r.right == rhsN))
  | _ => rules

def factsForSpace (I : Interface σ) (P : Policy) (s : σ) (space : Pattern) : List Pattern :=
  match P.relationNameOfSpace? space with
  | none => []
  | some rel =>
      (((I.bundle s).relationEnv.tuples rel [(.fvar "_")]).filterMap fun row =>
        match row with
        | [fact] => some fact
        | _ => none).reverse

partial def matchFactsAgainstSpace (I : Interface σ) (facts : List Pattern) : Pattern → List Bindings
  | .apply "," [lhs, rhs] =>
      (matchFactsAgainstSpace I facts lhs).flatMap fun bL =>
        (matchFactsAgainstSpace I facts rhs).filterMap fun bR =>
          mergeBindings bL bR
  | pat =>
      let patN := I.normalizePattern pat
      match patN with
      | .fvar x =>
          facts.filterMap fun fact =>
            match fact with
            | .apply _ [] => some [(x, fact)]
            | _ => none
      | _ =>
          facts.flatMap fun fact =>
            I.matchPattern patN fact

def findBindingsInSpace (I : Interface σ) (P : Policy) (s : σ) (space pat : Pattern) :
    List Bindings :=
  matchFactsAgainstSpace I (factsForSpace I P s space) pat

private partial def evalSequence (I : Interface σ) (s : σ)
    (terms : List Pattern) (acc : List Pattern) : σ × List Pattern :=
  match terms with
  | [] => (s, acc)
  | t :: ts =>
      let (s1, out) := I.eval s t
      evalSequence I s1 ts (acc ++ out)

def evalMatchIntrinsic (I : Interface σ) (P : Policy) (s : σ)
    (space pat tmpl : Pattern) : σ × List Pattern :=
  let facts := factsForSpace I P s space
  let bindings := matchFactsAgainstSpace I facts pat
  let (sDyn, outRev) :=
    bindings.foldl
      (fun (acc : σ × List Pattern) bs =>
        let sess := acc.1
        let collected := acc.2
        let tmplSub := I.applyBindings bs tmpl
        let (sess', out) :=
          match tmplSub with
          | .apply "Expr" elems => evalSequence I sess elems []
          | _ => I.eval sess tmplSub
        (sess', out.reverse ++ collected))
      (s, [])
  let dynamicOut := outRev.reverse
  let builtinOut3 :=
    ((I.bundle sDyn).builtins.relation "spaceMatch" [pat, tmpl, .fvar "_out"]).filterMap fun row =>
      match row with
      | [_pat, _tmpl, out] => some out
      | _ => none
  let builtinOut2 :=
    ((I.bundle sDyn).builtins.relation "spaceMatch" [pat, tmpl]).filterMap fun row =>
      match row with
      | [_pat, out] => some out
      | _ => none
  (sDyn, dynamicOut ++ builtinOut3 ++ builtinOut2)

def addAtom (I : Interface σ) (P : Policy) (s : σ) (space fact : Pattern) : σ × List Pattern :=
  match P.relationNameOfSpace? space with
  | none => (s, [])
  | some rel =>
      let env' : RelationEnv :=
        { tuples := fun qRel args =>
            let base := (I.bundle s).relationEnv.tuples qRel args
            if rel == qRel && args.length == 1 then
              [fact] :: base
            else
              base }
      let bundle0 : SpecBundle := { I.bundle s with relationEnv := env' }
      let lang' :=
        if P.loadSelfEqFactsAsRewrites && rel == P.selfRelationName then
          match eqFactToRule? bundle0.language.rewrites.length fact with
          | some rule =>
              { bundle0.language with rewrites := bundle0.language.rewrites ++ [rule] }
          | none => bundle0.language
        else
          bundle0.language
      let bundle' : SpecBundle := { bundle0 with language := lang' }
      (I.setBundle s bundle', [fact])

def removeAtom (I : Interface σ) (P : Policy) (s : σ) (space fact : Pattern) : σ × List Pattern :=
  match P.relationNameOfSpace? space with
  | none => (s, [])
  | some rel =>
      let env' : RelationEnv :=
        { tuples := fun qRel args =>
            let base := (I.bundle s).relationEnv.tuples qRel args
            if rel == qRel && args.length == 1 then
              base.filter (fun tup => tup != [fact])
            else
              base }
      let bundle0 : SpecBundle := { I.bundle s with relationEnv := env' }
      let lang' :=
        if P.loadSelfEqFactsAsRewrites && rel == P.selfRelationName then
          { bundle0.language with rewrites := removeRuleForEqFact I.normalizePattern bundle0.language.rewrites fact }
        else
          bundle0.language
      let bundle' : SpecBundle := { bundle0 with language := lang' }
      (I.setBundle s bundle', [fact])

def removeAllAtoms (I : Interface σ) (P : Policy) (s : σ) (space : Pattern)
    (echo : Pattern) : σ × List Pattern :=
  match P.relationNameOfSpace? space with
  | none => (s, [echo])
  | some rel =>
      let env' : RelationEnv :=
        { tuples := fun qRel args =>
            if qRel == rel then
              []
            else
              (I.bundle s).relationEnv.tuples qRel args }
      let lang' : LanguageDef :=
        if P.clearRewritesOnSelfRemoveAll && rel == P.selfRelationName then
          { (I.bundle s).language with rewrites := [] }
        else
          (I.bundle s).language
      let bundle' : SpecBundle := { I.bundle s with relationEnv := env', language := lang' }
      (I.setBundle s bundle', [echo])

def getAtoms (I : Interface σ) (P : Policy) (s : σ) (space : Pattern) : σ × List Pattern :=
  (s, factsForSpace I P s space)

end Algorithms.MeTTa.Simple.Semantics.SpaceOps
