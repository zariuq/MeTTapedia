import MeTTailCore.MeTTaIL.Match
import MeTTailCore.MeTTaIL.Substitution

namespace MeTTailCore.MeTTaIL.Engine

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match
open MeTTailCore.MeTTaIL.Substitution

abbrev rewriteStepNoPremises (lang : LanguageDef) (term : Pattern) : List Pattern :=
  rewriteStep lang term

/-- Rewrite one subterm in a collection (no premises). -/
def rewriteInCollectionNoPremises (lang : LanguageDef) (ct : CollType)
    (elems : List Pattern) (rest : Option String) : List Pattern :=
  if _hct : LanguageDef.allowsCongruenceIn lang ct then
    let rec go : List Pattern → List Pattern
      | [] => []
      | e :: es =>
        let headRed := (rewriteStepNoPremises lang e).map (fun e' => .collection ct (e' :: es) rest)
        let tailRed := (go es).map (fun coll =>
          match coll with
          | .collection _ tail rest' => .collection ct (e :: tail) rest'
          | _ => coll)
        headRed ++ tailRed
    go elems
  else
    []

/-- Top-level + one-level congruence rewrite (no premises). -/
def rewriteWithContextNoPremises (lang : LanguageDef) (term : Pattern) : List Pattern :=
  let topReducts := rewriteStepNoPremises lang term
  let subReducts := match term with
    | .collection ct elems rest => rewriteInCollectionNoPremises lang ct elems rest
    | _ => []
  topReducts ++ subReducts

abbrev rewriteWithContext (lang : LanguageDef) (term : Pattern) : List Pattern :=
  rewriteWithContextNoPremises lang term

/-- Resolve freshness variable binder lookup. -/
private def resolveFreshVarName (bindings : Bindings) (x : String) : Option String :=
  match bindings.lookup x with
  | some (.fvar y) => some y
  | some _ => none
  | none => some x

/-- Pluggable relation environment for relation-query premises. -/
structure RelationEnv where
  tuples : String → List Pattern → List (List Pattern)

namespace RelationEnv

def empty : RelationEnv where
  tuples := fun _ _ => []

end RelationEnv

private def builtinRelationTuples (lang : LanguageDef) (rel : String) (args : List Pattern) :
    List (List Pattern) :=
  match rel, args with
  | "reduces", [src, _] =>
      (rewriteWithContextNoPremises lang src).map fun tgt => [src, tgt]
  | "eq", [lhs, rhs] =>
      [[lhs, lhs], [rhs, rhs]]
  | _, _ => []

private def relationQueryStep (relEnv : RelationEnv) (lang : LanguageDef)
    (bindings : Bindings) (rel : String) (args : List Pattern) : List Bindings :=
  let argPats := args.map (applyBindings bindings)
  let tuples := builtinRelationTuples lang rel argPats ++ relEnv.tuples rel argPats
  tuples.flatMap fun tuple =>
    (matchArgs argPats tuple).filterMap fun bPrem =>
      mergeBindings bindings bPrem

/-- Evaluate one premise under current bindings. -/
def premiseStepWithEnv (relEnv : RelationEnv) (lang : LanguageDef) (bindings : Bindings) :
    Premise → List Bindings
  | .freshness fc =>
      let term' := applyBindings bindings fc.term
      match resolveFreshVarName bindings fc.varName with
      | some x => if checkFreshness { varName := x, term := term' } then [bindings] else []
      | none => []
  | .congruence src tgt =>
      let src' := applyBindings bindings src
      (rewriteWithContextNoPremises lang src').flatMap fun cand =>
        (matchPattern tgt cand).filterMap fun bPrem =>
          mergeBindings bindings bPrem
  | .relationQuery rel args =>
      relationQueryStep relEnv lang bindings rel args

abbrev premiseStep (lang : LanguageDef) (bindings : Bindings) : Premise → List Bindings :=
  premiseStepWithEnv RelationEnv.empty lang bindings

/-- Apply all premises left-to-right. -/
def applyPremisesWithEnv (relEnv : RelationEnv) (lang : LanguageDef)
    (premises : List Premise) (seed : Bindings) : List Bindings :=
  premises.foldl
    (fun acc prem => acc.flatMap fun bs => premiseStepWithEnv relEnv lang bs prem)
    [seed]

abbrev applyPremises (lang : LanguageDef) (premises : List Premise) (seed : Bindings) : List Bindings :=
  applyPremisesWithEnv RelationEnv.empty lang premises seed

def premiseHoldsWithEnv (relEnv : RelationEnv) (lang : LanguageDef)
    (bindings : Bindings) (premise : Premise) : Bool :=
  !(premiseStepWithEnv relEnv lang bindings premise).isEmpty

def premisesHoldWithEnv (relEnv : RelationEnv) (lang : LanguageDef)
    (bindings : Bindings) (premises : List Premise) : Bool :=
  !(applyPremisesWithEnv relEnv lang premises bindings).isEmpty

abbrev premiseHolds (lang : LanguageDef) (bindings : Bindings) (premise : Premise) : Bool :=
  premiseHoldsWithEnv RelationEnv.empty lang bindings premise

abbrev premisesHold (lang : LanguageDef) (bindings : Bindings) (premises : List Premise) : Bool :=
  premisesHoldWithEnv RelationEnv.empty lang bindings premises

/-- Apply one rule with premise-aware bindings. -/
def applyRuleWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (rule : RewriteRule) (term : Pattern) : List Pattern :=
  (matchPattern rule.left term).flatMap fun bs =>
    (applyPremisesWithEnv relEnv lang rule.premises bs).map fun bs' =>
      applyBindings bs' rule.right

abbrev applyRuleWithPremises (lang : LanguageDef) (rule : RewriteRule) (term : Pattern) : List Pattern :=
  applyRuleWithPremisesUsing RelationEnv.empty lang rule term

def rewriteStepWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (term : Pattern) : List Pattern :=
  lang.rewrites.flatMap fun rule => applyRuleWithPremisesUsing relEnv lang rule term

abbrev rewriteStepWithPremises (lang : LanguageDef) (term : Pattern) : List Pattern :=
  rewriteStepWithPremisesUsing RelationEnv.empty lang term

/-- Rewrite one subterm in a collection (premise-aware). -/
def rewriteInCollectionWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (ct : CollType) (elems : List Pattern) (rest : Option String) : List Pattern :=
  if _hct : LanguageDef.allowsCongruenceIn lang ct then
    let rec go : List Pattern → List Pattern
      | [] => []
      | e :: es =>
        let headRed := (rewriteStepWithPremisesUsing relEnv lang e).map
          (fun e' => .collection ct (e' :: es) rest)
        let tailRed := (go es).map (fun coll =>
          match coll with
          | .collection _ tail rest' => .collection ct (e :: tail) rest'
          | _ => coll)
        headRed ++ tailRed
    go elems
  else
    []

abbrev rewriteInCollectionWithPremises (lang : LanguageDef) (ct : CollType)
    (elems : List Pattern) (rest : Option String) : List Pattern :=
  rewriteInCollectionWithPremisesUsing RelationEnv.empty lang ct elems rest

/-- Top-level + one-level congruence rewrite (premise-aware). -/
def rewriteWithContextWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (term : Pattern) : List Pattern :=
  let topReducts := rewriteStepWithPremisesUsing relEnv lang term
  let subReducts := match term with
    | .collection ct elems rest => rewriteInCollectionWithPremisesUsing relEnv lang ct elems rest
    | _ => []
  topReducts ++ subReducts

abbrev rewriteWithContextWithPremises (lang : LanguageDef) (term : Pattern) : List Pattern :=
  rewriteWithContextWithPremisesUsing RelationEnv.empty lang term

def fullRewriteToNormalForm (lang : LanguageDef) (term : Pattern)
    (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match rewriteWithContext lang term with
    | [] => term
    | q :: _ => fullRewriteToNormalForm lang q fuel

def fullRewriteToNormalFormWithPremisesUsing (relEnv : RelationEnv) (lang : LanguageDef)
    (term : Pattern) (fuel : Nat := 1000) : Pattern :=
  match fuel with
  | 0 => term
  | fuel + 1 =>
    match rewriteWithContextWithPremisesUsing relEnv lang term with
    | [] => term
    | q :: _ => fullRewriteToNormalFormWithPremisesUsing relEnv lang q fuel

abbrev fullRewriteToNormalFormWithPremises (lang : LanguageDef) (term : Pattern)
    (fuel : Nat := 1000) : Pattern :=
  fullRewriteToNormalFormWithPremisesUsing RelationEnv.empty lang term fuel

end MeTTailCore.MeTTaIL.Engine
