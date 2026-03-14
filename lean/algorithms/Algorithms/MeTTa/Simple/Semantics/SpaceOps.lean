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

private theorem eqBindingsFromRules_eval_irrelevant
    (I : Interface σ) (eval' : σ → Pattern → σ × List Pattern)
    (lhs rhs : Pattern) (rules : List RewriteRule) :
    eqBindingsFromRules I lhs rhs rules =
      eqBindingsFromRules ({ I with eval := eval' }) lhs rhs rules := by
  cases I
  simp [eqBindingsFromRules]

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

private def matchFactsAgainstSpaceDepth : Pattern → Nat
  | .bvar _ => 1
  | .fvar _ => 1
  | .apply _ args =>
      1 + args.foldl (fun h a => Nat.max h (matchFactsAgainstSpaceDepth a)) 0
  | .lambda body =>
      1 + matchFactsAgainstSpaceDepth body
  | .multiLambda _ body =>
      1 + matchFactsAgainstSpaceDepth body
  | .subst body repl =>
      1 + Nat.max (matchFactsAgainstSpaceDepth body) (matchFactsAgainstSpaceDepth repl)
  | .collection _ elems _ =>
      1 + elems.foldl (fun h a => Nat.max h (matchFactsAgainstSpaceDepth a)) 0

def matchFactsAgainstSpace (I : Interface σ) (facts : List Pattern) : Pattern → List Bindings
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
termination_by pat => matchFactsAgainstSpaceDepth pat
decreasing_by
  all_goals
    simp [matchFactsAgainstSpaceDepth]
    first
    | have h :
          matchFactsAgainstSpaceDepth lhs ≤
            (matchFactsAgainstSpaceDepth lhs).max (matchFactsAgainstSpaceDepth rhs) :=
          Nat.le_max_left _ _
      omega
    | have h :
          matchFactsAgainstSpaceDepth rhs ≤
            (matchFactsAgainstSpaceDepth lhs).max (matchFactsAgainstSpaceDepth rhs) :=
          Nat.le_max_right _ _
      omega

private theorem matchFactsAgainstSpace_eval_irrelevant
    (I : Interface σ) (eval' : σ → Pattern → σ × List Pattern)
    (facts : List Pattern) (pat : Pattern) :
    matchFactsAgainstSpace I facts pat =
      matchFactsAgainstSpace ({ I with eval := eval' }) facts pat := by
  have hMain :
      ∀ n, ∀ pat : Pattern,
        matchFactsAgainstSpaceDepth pat ≤ n →
        matchFactsAgainstSpace I facts pat =
          matchFactsAgainstSpace ({ I with eval := eval' }) facts pat := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
        intro pat hDepth
        cases pat with
        | bvar m =>
            cases I
            unfold matchFactsAgainstSpace
            simp
        | fvar x =>
            cases I
            unfold matchFactsAgainstSpace
            simp
        | apply ctor args =>
            cases args with
            | nil =>
                cases I
                unfold matchFactsAgainstSpace
                simp
            | cons a rest =>
                cases rest with
                | nil =>
                    cases I
                    unfold matchFactsAgainstSpace
                    simp
                | cons b rest2 =>
                    cases rest2 with
                    | nil =>
                        by_cases hComma : ctor = ","
                        · subst hComma
                          have hLtA :
                              matchFactsAgainstSpaceDepth a <
                                matchFactsAgainstSpaceDepth (.apply "," [a, b]) := by
                            simp [matchFactsAgainstSpaceDepth]
                            have hLe :
                                matchFactsAgainstSpaceDepth a ≤
                                  (matchFactsAgainstSpaceDepth a).max
                                    (matchFactsAgainstSpaceDepth b) :=
                              Nat.le_max_left _ _
                            omega
                          have hLtB :
                              matchFactsAgainstSpaceDepth b <
                                matchFactsAgainstSpaceDepth (.apply "," [a, b]) := by
                            simp [matchFactsAgainstSpaceDepth]
                            have hLe :
                                matchFactsAgainstSpaceDepth b ≤
                                  (matchFactsAgainstSpaceDepth a).max
                                    (matchFactsAgainstSpaceDepth b) :=
                              Nat.le_max_right _ _
                            omega
                          have hA :=
                            ih (matchFactsAgainstSpaceDepth a)
                              (Nat.lt_of_lt_of_le hLtA hDepth)
                              a (Nat.le_refl _)
                          have hB :=
                            ih (matchFactsAgainstSpaceDepth b)
                              (Nat.lt_of_lt_of_le hLtB hDepth)
                              b (Nat.le_refl _)
                          unfold matchFactsAgainstSpace
                          simp [hA, hB]
                        · cases I
                          unfold matchFactsAgainstSpace
                          simp [hComma]
                    | cons c rest3 =>
                        cases I
                        unfold matchFactsAgainstSpace
                        simp
        | lambda body =>
            cases I
            unfold matchFactsAgainstSpace
            simp
        | multiLambda m body =>
            cases I
            unfold matchFactsAgainstSpace
            simp
        | subst body repl =>
            cases I
            unfold matchFactsAgainstSpace
            simp
        | collection ct elems rest =>
            cases I
            unfold matchFactsAgainstSpace
            simp
  exact hMain (matchFactsAgainstSpaceDepth pat) pat (Nat.le_refl _)

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

/-- `findBindingsInSpace` depends only on the non-`eval` fields of the interface. -/
theorem findBindingsInSpace_eval_irrelevant
    (I : Interface σ) (eval' : σ → Pattern → σ × List Pattern)
    (P : Policy) (s : σ) (space pat : Pattern) :
    findBindingsInSpace I P s space pat =
      findBindingsInSpace ({ I with eval := eval' }) P s space pat := by
  cases I with
  | mk bundle rewrites setBundle eval0 applyBindings normalizePattern normalizeForSpaceMatch matchPattern dedupPatterns =>
      let I0 : Interface σ := {
        bundle := bundle
        rewrites := rewrites
        setBundle := setBundle
        eval := eval0
        applyBindings := applyBindings
        normalizePattern := normalizePattern
        normalizeForSpaceMatch := normalizeForSpaceMatch
        matchPattern := matchPattern
        dedupPatterns := dedupPatterns
      }
      let I1 : Interface σ := { I0 with eval := eval' }
      change findBindingsInSpace I0 P s space pat = findBindingsInSpace I1 P s space pat
      unfold findBindingsInSpace
      have hFacts :
          factsForSpace I1 P s space = factsForSpace I0 P s space := by
        simp [I0, I1, factsForSpace]
      rw [hFacts]
      rw [← matchFactsAgainstSpace_eval_irrelevant
        (I := I0) (eval' := eval') (facts := factsForSpace I0 P s space) (pat := pat)]
      have hRule :
          (match P.relationNameOfSpace? space, I0.normalizePattern pat with
            | some rel, .apply "=" [lhs, rhs] =>
                if rel == P.selfRelationName then
                  eqBindingsFromRules I0 lhs rhs (I0.rewrites s)
                else
                  []
            | _, _ => []) =
          (match P.relationNameOfSpace? space, I1.normalizePattern pat with
            | some rel, .apply "=" [lhs, rhs] =>
                if rel == P.selfRelationName then
                  eqBindingsFromRules I1 lhs rhs (I1.rewrites s)
                else
                  []
            | _, _ => []) := by
        by_cases hRel : P.relationNameOfSpace? space = none
        · simp [hRel]
        · cases hSpace : P.relationNameOfSpace? space with
          | none =>
              contradiction
          | some rel =>
              cases hNorm : I0.normalizePattern pat with
              | bvar n =>
                  simp
              | fvar x =>
                  simp
              | lambda body =>
                  simp
              | multiLambda n body =>
                  simp
              | subst body repl =>
                  simp
              | collection ct elems rest =>
                  simp
              | apply ctor args =>
                  cases args with
                  | nil =>
                      simp
                  | cons a rest =>
                      cases rest with
                      | nil =>
                          simp
                      | cons b rest2 =>
                          cases rest2 with
                          | nil =>
                              by_cases hEqCtor : ctor = "="
                              · subst hEqCtor
                                by_cases hEq : rel == P.selfRelationName
                                · simp [hEq]
                                  exact eqBindingsFromRules_eval_irrelevant
                                    (I := I0) (eval' := eval') (lhs := a) (rhs := b)
                                    (rules := I0.rewrites s)
                                · simp [hEq]
                              · simp [hEqCtor]
                          | cons c rest3 =>
                              simp
      rw [hRule]

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

/-- Evaluate a substituted match template. `Expr` templates enumerate their elements in
sequence; all other templates are evaluated directly. -/
def evalMatchedTemplate (I : Interface σ) (s : σ) (tmplSub : Pattern) : σ × List Pattern :=
  match tmplSub with
  | .apply "Expr" elems => evalSequence I s elems []
  | _ => I.eval s tmplSub

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

private theorem evalSequence_eq_of_eval_agreement
    (I₁ I₂ : Interface σ) (s : σ) (terms : List Pattern) (acc : List Pattern)
    (hEval : ∀ (s : σ) (term : Pattern), I₁.eval s term = I₂.eval s term) :
    evalSequence I₁ s terms acc = evalSequence I₂ s terms acc := by
  induction terms generalizing s acc with
  | nil =>
      rfl
  | cons t ts ih =>
      cases h₁ : I₁.eval s t with
      | mk s₁ out₁ =>
          cases h₂ : I₂.eval s t with
          | mk s₂ out₂ =>
              have hEq : (s₁, out₁) = (s₂, out₂) := by
                simpa [h₁, h₂] using hEval s t
              cases hEq
              simpa [evalSequence, h₁, h₂] using ih s₁ (acc ++ out₁)

/-- `evalMatchedTemplate` depends on the interface only through its `eval` field. -/
theorem evalMatchedTemplate_eq_of_eval_agreement
    (I₁ I₂ : Interface σ) (s : σ) (tmplSub : Pattern)
    (hEval : ∀ (s : σ) (term : Pattern), I₁.eval s term = I₂.eval s term) :
    evalMatchedTemplate I₁ s tmplSub = evalMatchedTemplate I₂ s tmplSub := by
  cases tmplSub with
  | fvar x =>
      simpa [evalMatchedTemplate] using hEval s (.fvar x)
  | bvar n =>
      simpa [evalMatchedTemplate] using hEval s (.bvar n)
  | apply ctor args =>
      by_cases hExpr : ctor = "Expr"
      · subst hExpr
        simpa [evalMatchedTemplate] using
          evalSequence_eq_of_eval_agreement I₁ I₂ s args [] hEval
      · simpa [evalMatchedTemplate, hExpr] using hEval s (.apply ctor args)
  | lambda body =>
      simpa [evalMatchedTemplate] using hEval s (.lambda body)
  | multiLambda n body =>
      simpa [evalMatchedTemplate] using hEval s (.multiLambda n body)
  | subst body repl =>
      simpa [evalMatchedTemplate] using hEval s (.subst body repl)
  | collection ct elems rest =>
      simpa [evalMatchedTemplate] using hEval s (.collection ct elems rest)

def evalMatchIntrinsic (I : Interface σ) (P : Policy) (s : σ)
    (space pat tmpl : Pattern) : σ × List Pattern :=
  let bindings := findBindingsInSpace I P s space pat
  let (sDyn, outRev) :=
    bindings.foldl
      (fun (acc : σ × List Pattern) bs =>
        let sess := acc.1
        let collected := acc.2
        let tmplSub := I.applyBindings bs tmpl
        let (sess', out) := evalMatchedTemplate I sess tmplSub
        (sess', out.reverse ++ collected))
      (s, [])
  let dynamicOut := outRev.reverse
  let builtinOut3 :=
    ((I.bundle sDyn).builtins.relation "spaceMatch" [pat, tmpl, .fvar "_out"]).filterMap fun row =>
      match row with
      | [_pat, _tmpl, out] => some out
      | _ => none
  (sDyn, dynamicOut ++ builtinOut3)

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
    let (sess', out) := evalMatchedTemplate I sess tmplSub
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
            Pred ((evalMatchedTemplate I sess tmplSub).1) := by
          cases hT : tmplSub with
          | fvar x =>
              simpa [evalMatchedTemplate, hT] using
                H.eval_preserves (s := sess) (term := .fvar x) rfl hSess
          | bvar n =>
              simpa [evalMatchedTemplate, hT] using
                H.eval_preserves (s := sess) (term := .bvar n) rfl hSess
          | apply ctor args =>
              by_cases hCtor : ctor = "Expr"
              · subst hCtor
                simpa [evalMatchedTemplate, hT] using
                  evalSequence_preserves I Pred H sess args [] hSess
              · simpa [evalMatchedTemplate, hT, hCtor] using
                  H.eval_preserves (s := sess) (term := .apply ctor args) rfl hSess
          | lambda body =>
              simpa [evalMatchedTemplate, hT] using
                H.eval_preserves (s := sess) (term := .lambda body) rfl hSess
          | multiLambda n body =>
              simpa [evalMatchedTemplate, hT] using
                H.eval_preserves (s := sess) (term := .multiLambda n body) rfl hSess
          | subst body repl =>
              simpa [evalMatchedTemplate, hT] using
                H.eval_preserves (s := sess) (term := .subst body repl) rfl hSess
          | collection ct elems restTail =>
              simpa [evalMatchedTemplate, hT] using H.eval_preserves
                (s := sess) (term := .collection ct elems restTail) rfl hSess
        exact ih _ _ hStep
  simpa [bindings, f] using hFold bindings s [] hP

private theorem evalMatchIntrinsic_predicate_fold_acc
    (I : Interface σ) (s : σ) (bindings : List Bindings) (tmpl : Pattern)
    (acc : List Pattern)
    (hApplyPredicate :
      ∀ (bs : Bindings) (expr : Pattern),
        I.applyBindings bs (.apply "Predicate" [expr]) =
          .apply "Predicate" [I.applyBindings bs expr])
    (hEvalPredicate :
      ∀ (s : σ) (expr : Pattern),
        I.eval s (.apply "Predicate" [expr]) = (s, [expr])) :
    bindings.foldl
        (fun (accState : σ × List Pattern) bs =>
        let sess := accState.1
        let collected := accState.2
        let tmplSub := I.applyBindings bs (.apply "Predicate" [tmpl])
        let (sess', out) := evalMatchedTemplate I sess tmplSub
        (sess', out.reverse ++ collected))
        (s, acc) =
      (s, (bindings.map (fun bs => I.applyBindings bs tmpl)).reverse ++ acc) := by
  induction bindings generalizing acc with
  | nil =>
      simp
  | cons bs rest ih =>
      simp [List.foldl_cons, hApplyPredicate]
      have hPredEval :
          evalMatchedTemplate I s (.apply "Predicate" [I.applyBindings bs tmpl]) =
            (s, [I.applyBindings bs tmpl]) := by
        simpa [evalMatchedTemplate, hApplyPredicate] using
          hEvalPredicate s (I.applyBindings bs tmpl)
      simp [hPredEval]
      simpa [hApplyPredicate] using ih (I.applyBindings bs tmpl :: acc)

/-- When the template is wrapped in `Predicate`, `evalMatchIntrinsic` becomes a pure
normal-form enumerator: each binding contributes exactly the substituted payload, with
no recursive evaluation beyond the `Predicate` shell. -/
theorem evalMatchIntrinsic_predicate_template
    (I : Interface σ) (P : Policy) (s : σ) (space pat tmpl : Pattern)
    (hApplyPredicate :
      ∀ (bs : Bindings) (expr : Pattern),
        I.applyBindings bs (.apply "Predicate" [expr]) =
          .apply "Predicate" [I.applyBindings bs expr])
    (hEvalPredicate :
      ∀ (s : σ) (expr : Pattern),
        I.eval s (.apply "Predicate" [expr]) = (s, [expr])) :
    evalMatchIntrinsic I P s space pat (.apply "Predicate" [tmpl]) =
      let bindings := findBindingsInSpace I P s space pat
      let builtinOut3 :=
        ((I.bundle s).builtins.relation "spaceMatch"
          [pat, .apply "Predicate" [tmpl], .fvar "_out"]).filterMap fun row =>
            match row with
            | [_pat, _tmpl, out] => some out
            | _ => none
      (s, bindings.map (fun bs => I.applyBindings bs tmpl) ++ builtinOut3) := by
  unfold evalMatchIntrinsic
  let bindings := findBindingsInSpace I P s space pat
  have hFold :=
    evalMatchIntrinsic_predicate_fold_acc
      I s bindings tmpl [] hApplyPredicate hEvalPredicate
  have hState :
      (bindings.foldl
          (fun (accState : σ × List Pattern) bs =>
            let sess := accState.1
            let collected := accState.2
            let tmplSub := I.applyBindings bs (.apply "Predicate" [tmpl])
            let (sess', out) := evalMatchedTemplate I sess tmplSub
            (sess', out.reverse ++ collected))
          (s, [])).1 = s := by
    exact congrArg Prod.fst hFold
  have hOutRev :
      (bindings.foldl
          (fun (accState : σ × List Pattern) bs =>
            let sess := accState.1
            let collected := accState.2
            let tmplSub := I.applyBindings bs (.apply "Predicate" [tmpl])
            let (sess', out) := evalMatchedTemplate I sess tmplSub
            (sess', out.reverse ++ collected))
          (s, [])).2 =
        (bindings.map (fun bs => I.applyBindings bs tmpl)).reverse := by
    simpa using congrArg Prod.snd hFold
  dsimp [bindings]
  apply Prod.ext
  · exact hState
  · rw [hState, hOutRev]
    simp [bindings]

private theorem evalMatchIntrinsic_fold_eq_of_evalMatchedTemplate_agreement
    (I₁ I₂ : Interface σ) (s : σ) (bindings : List Bindings) (tmpl : Pattern)
    (hApply :
      ∀ (bs : Bindings) (term : Pattern),
        I₁.applyBindings bs term = I₂.applyBindings bs term)
    (hEval :
      ∀ (sess : σ) (bs : Bindings),
        evalMatchedTemplate I₁ sess (I₁.applyBindings bs tmpl) =
          evalMatchedTemplate I₂ sess (I₂.applyBindings bs tmpl))
    (acc : List Pattern) :
    bindings.foldl
        (fun (accState : σ × List Pattern) bs =>
          let sess := accState.1
          let collected := accState.2
          let tmplSub := I₁.applyBindings bs tmpl
          let (sess', out) := evalMatchedTemplate I₁ sess tmplSub
          (sess', out.reverse ++ collected))
        (s, acc) =
      bindings.foldl
        (fun (accState : σ × List Pattern) bs =>
          let sess := accState.1
          let collected := accState.2
          let tmplSub := I₂.applyBindings bs tmpl
          let (sess', out) := evalMatchedTemplate I₂ sess tmplSub
          (sess', out.reverse ++ collected))
        (s, acc) := by
  induction bindings generalizing s acc with
  | nil =>
      rfl
  | cons bs rest ih =>
      simp only [List.foldl_cons]
      have hApplyBs : I₁.applyBindings bs tmpl = I₂.applyBindings bs tmpl :=
        hApply bs tmpl
      have hStep :
          evalMatchedTemplate I₁ s (I₁.applyBindings bs tmpl) =
            evalMatchedTemplate I₂ s (I₂.applyBindings bs tmpl) :=
        hEval s bs
      rw [hApplyBs] at hStep
      cases hOut : evalMatchedTemplate I₂ s (I₂.applyBindings bs tmpl) with
      | mk s' out =>
          have hOut₁ :
              evalMatchedTemplate I₁ s (I₁.applyBindings bs tmpl) = (s', out) := by
            simpa [hApplyBs, hOut] using hStep
          simp [hOut₁]
          exact ih s' (out.reverse ++ acc)

/-- Compositional congruence for `evalMatchIntrinsic`.
If two interfaces discover the same bindings and agree on the evaluation of every
substituted template produced by those bindings, they produce the same match result. -/
theorem evalMatchIntrinsic_eq_of_evalMatchedTemplate_agreement
    (I₁ I₂ : Interface σ) (P : Policy) (s : σ) (space pat tmpl : Pattern)
    (hBindings :
      findBindingsInSpace I₁ P s space pat =
        findBindingsInSpace I₂ P s space pat)
    (hApply :
      ∀ (bs : Bindings) (term : Pattern),
        I₁.applyBindings bs term = I₂.applyBindings bs term)
    (hBundle : ∀ (sess : σ), I₁.bundle sess = I₂.bundle sess)
    (hEval :
      ∀ (sess : σ) (bs : Bindings),
        evalMatchedTemplate I₁ sess (I₁.applyBindings bs tmpl) =
          evalMatchedTemplate I₂ sess (I₂.applyBindings bs tmpl)) :
    evalMatchIntrinsic I₁ P s space pat tmpl =
      evalMatchIntrinsic I₂ P s space pat tmpl := by
  unfold evalMatchIntrinsic
  rw [hBindings]
  let bindings := findBindingsInSpace I₂ P s space pat
  let f₁ := fun (accState : σ × List Pattern) bs =>
    let sess := accState.1
    let collected := accState.2
    let tmplSub := I₁.applyBindings bs tmpl
    let (sess', out) := evalMatchedTemplate I₁ sess tmplSub
    (sess', out.reverse ++ collected)
  let f₂ := fun (accState : σ × List Pattern) bs =>
    let sess := accState.1
    let collected := accState.2
    let tmplSub := I₂.applyBindings bs tmpl
    let (sess', out) := evalMatchedTemplate I₂ sess tmplSub
    (sess', out.reverse ++ collected)
  have hFold :
      bindings.foldl f₁ (s, []) = bindings.foldl f₂ (s, []) := by
    exact
      evalMatchIntrinsic_fold_eq_of_evalMatchedTemplate_agreement
        I₁ I₂ s bindings tmpl hApply hEval []
  cases hFold₂ : bindings.foldl f₂ (s, []) with
  | mk sDyn outRev =>
      have hFold₁ : bindings.foldl f₁ (s, []) = (sDyn, outRev) := by
        simpa [hFold₂] using hFold
      simp [bindings, f₁, f₂, hFold₁, hFold₂, hBundle sDyn]

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
