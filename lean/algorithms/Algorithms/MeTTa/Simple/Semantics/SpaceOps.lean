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
  rewrites : σ → List RewriteRule
  setBundle : σ → SpecBundle → σ
  eval : σ → Pattern → σ × List Pattern
  applyBindings : Bindings → Pattern → Pattern
  normalizePattern : Pattern → Pattern
  normalizeForSpaceMatch : Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings
  dedupPatterns : List Pattern → List Pattern

structure Preservation (I : Interface σ) (P : σ → Prop) where
  eval_preserves :
    ∀ {s : σ} {term : Pattern} {s' : σ} {out : List Pattern},
      I.eval s term = (s', out) → P s → P s'
  setBundle_preserves :
    ∀ {s : σ} {bundle : SpecBundle},
      P s → P (I.setBundle s bundle)

private def dedupBindings (xs : List Bindings) : List Bindings :=
  (xs.foldl
    (fun acc x => if acc.contains x then acc else x :: acc)
    []).reverse

private def eqBindingsFromRules (I : Interface σ) (lhs rhs : Pattern)
    (rules : List RewriteRule) : List Bindings :=
  rules.foldl
    (fun acc rule =>
      if rule.premises.isEmpty then
        let fromLhs := I.matchPattern rule.left lhs
        let out :=
          fromLhs.flatMap (fun bL =>
            let lhsSub := I.applyBindings bL lhs
            let ruleLeftSub := I.applyBindings bL rule.left
            let lhsCheck := I.matchPattern lhsSub ruleLeftSub
            if lhsCheck.isEmpty then
              []
            else
              lhsCheck.flatMap (fun bCheck =>
                match mergeBindings bL bCheck with
                | none => []
                | some bLC =>
                    let rhsSub := I.applyBindings bLC rhs
                    let ruleRightSub := I.applyBindings bLC rule.right
                    (I.matchPattern rhsSub ruleRightSub).filterMap
                      (fun bR => mergeBindings bLC bR)))
        acc ++ out
      else
        acc)
    []

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
  | .apply ctor [] =>
      if ctor.startsWith "$" then
        let name := (ctor.drop 1).toString
        if name.isEmpty then
          []
        else
          facts.filterMap fun fact =>
            match I.normalizeForSpaceMatch fact with
            | .apply head _ => some [(name, .apply head [])]
            | _ => none
      else
        let patN := I.normalizeForSpaceMatch (I.normalizePattern (.apply ctor []))
        facts.flatMap fun fact =>
          I.matchPattern patN (I.normalizeForSpaceMatch fact)
  | pat =>
      let patN := I.normalizeForSpaceMatch (I.normalizePattern pat)
      match patN with
      | .fvar x =>
          facts.map (fun fact => [(x, fact)])
      | _ =>
          facts.flatMap fun fact =>
            I.matchPattern patN (I.normalizeForSpaceMatch fact)

def findBindingsInSpace (I : Interface σ) (P : Policy) (s : σ) (space pat : Pattern) :
    List Bindings :=
  let factBs := matchFactsAgainstSpace I (factsForSpace I P s space) pat
  let ruleBs :=
    match P.relationNameOfSpace? space, I.normalizePattern pat with
    | some rel, .apply "=" [lhs, rhs] =>
        if rel == P.selfRelationName then
          eqBindingsFromRules I lhs rhs (I.rewrites s)
        else
          []
    | _, _ => []
  dedupBindings (factBs ++ ruleBs)

/-- Find bindings using an externally provided candidate fact list.
    Semantics are unchanged; only fact enumeration can differ. -/
def findBindingsInSpaceWithFacts (I : Interface σ) (P : Policy) (s : σ)
    (candidateFacts : List Pattern) (space pat : Pattern) : List Bindings :=
  let factBs := matchFactsAgainstSpace I candidateFacts pat
  let ruleBs :=
    match P.relationNameOfSpace? space, I.normalizePattern pat with
    | some rel, .apply "=" [lhs, rhs] =>
        if rel == P.selfRelationName then
          eqBindingsFromRules I lhs rhs (I.rewrites s)
        else
          []
    | _, _ => []
  dedupBindings (factBs ++ ruleBs)

private def evalSequence (I : Interface σ) (s : σ)
    (terms : List Pattern) (acc : List Pattern) : σ × List Pattern :=
  match terms with
  | [] => (s, acc)
  | t :: ts =>
      let (s1, out) := I.eval s t
      evalSequence I s1 ts (acc ++ out)

private theorem evalSequence_preserves
    (I : Interface σ) (P : σ → Prop) (H : Preservation I P)
    (s : σ) (terms : List Pattern) (acc : List Pattern) :
    P s → P (evalSequence I s terms acc).1 := by
  intro hP
  induction terms generalizing s acc with
  | nil =>
      simpa [evalSequence] using hP
  | cons t ts ih =>
      let out := I.eval s t
      have h1 : P out.1 := H.eval_preserves rfl hP
      simpa [evalSequence, out] using ih out.1 (acc ++ out.2) h1

def evalMatchIntrinsic (I : Interface σ) (P : Policy) (s : σ)
    (space pat tmpl : Pattern) : σ × List Pattern :=
  let bindings := findBindingsInSpace I P s space pat
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

theorem evalMatchIntrinsic_preserves
    (I : Interface σ) (Pred : σ → Prop) (H : Preservation I Pred)
    (P : Policy) (s : σ) (space pat tmpl : Pattern) :
    Pred s → Pred (evalMatchIntrinsic I P s space pat tmpl).1 := by
  intro hP
  unfold evalMatchIntrinsic
  let bindings := findBindingsInSpace I P s space pat
  let f := fun (acc : σ × List Pattern) bs =>
    let sess := acc.1
    let collected := acc.2
    let tmplSub := I.applyBindings bs tmpl
    let (sess', out) :=
      match tmplSub with
      | .apply "Expr" elems => evalSequence I sess elems []
      | _ => I.eval sess tmplSub
    (sess', out.reverse ++ collected)
  have hFold :
      ∀ (bsList : List Bindings) (sess : σ) (collected : List Pattern),
        Pred sess →
        Pred ((bsList.foldl f (sess, collected)).1) := by
    intro bsList
    induction bsList with
    | nil =>
        intro sess collected hSess
        simp [f, hSess]
    | cons bs rest ih =>
        intro sess collected hSess
        simp [f]
        let tmplSub := I.applyBindings bs tmpl
        have hStep :
            Pred
              ((match tmplSub with
                | .apply "Expr" elems => evalSequence I sess elems []
                | _ => I.eval sess tmplSub).1) := by
          cases hT : tmplSub with
          | fvar x =>
              simpa [hT] using H.eval_preserves (s := sess) (term := .fvar x) rfl hSess
          | bvar n =>
              simpa [hT] using H.eval_preserves (s := sess) (term := .bvar n) rfl hSess
          | apply ctor args =>
              by_cases hCtor : ctor = "Expr"
              · subst hCtor
                simpa [hT] using evalSequence_preserves I Pred H sess args [] hSess
              · simpa [hT, hCtor] using
                  H.eval_preserves (s := sess) (term := .apply ctor args) rfl hSess
          | lambda body =>
              simpa [hT] using H.eval_preserves (s := sess) (term := .lambda body) rfl hSess
          | multiLambda n body =>
              simpa [hT] using H.eval_preserves (s := sess) (term := .multiLambda n body) rfl hSess
          | subst body repl =>
              simpa [hT] using H.eval_preserves (s := sess) (term := .subst body repl) rfl hSess
          | collection ct elems restTail =>
              simpa [hT] using H.eval_preserves
                (s := sess) (term := .collection ct elems restTail) rfl hSess
        exact ih _ _ hStep
  simpa [bindings, f] using hFold bindings s [] hP

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

theorem addAtom_preserves
    (I : Interface σ) (Pred : σ → Prop) (H : Preservation I Pred)
    (P : Policy) (s : σ) (space fact : Pattern) :
    Pred s → Pred (addAtom I P s space fact).1 := by
  intro hP
  unfold addAtom
  split
  · simpa using hP
  · exact H.setBundle_preserves hP

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

theorem removeAtom_preserves
    (I : Interface σ) (Pred : σ → Prop) (H : Preservation I Pred)
    (P : Policy) (s : σ) (space fact : Pattern) :
    Pred s → Pred (removeAtom I P s space fact).1 := by
  intro hP
  unfold removeAtom
  split
  · simpa using hP
  · exact H.setBundle_preserves hP

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

theorem removeAllAtoms_preserves
    (I : Interface σ) (Pred : σ → Prop) (H : Preservation I Pred)
    (P : Policy) (s : σ) (space echo : Pattern) :
    Pred s → Pred (removeAllAtoms I P s space echo).1 := by
  intro hP
  unfold removeAllAtoms
  split
  · simpa using hP
  · exact H.setBundle_preserves hP

def getAtoms (I : Interface σ) (P : Policy) (s : σ) (space : Pattern) : σ × List Pattern :=
  (s, factsForSpace I P s space)

theorem getAtoms_preserves
    (I : Interface σ) (Pred : σ → Prop) (P : Policy) (s : σ) (space : Pattern) :
    Pred s → Pred (getAtoms I P s space).1 := by
  intro hP
  simp [getAtoms, hP]

end Algorithms.MeTTa.Simple.Semantics.SpaceOps
