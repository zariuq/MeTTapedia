import MeTTailCore
import Algorithms.MeTTa.Simple.Parser
import Algorithms.MeTTa.Simple.Relations
import Algorithms.MeTTa.Simple.Semantics.PredicateControl
import Algorithms.MeTTa.Simple.Semantics.ControlFlow
import Algorithms.MeTTa.Simple.Semantics.Dispatch
import Algorithms.MeTTa.Simple.Semantics.SpaceOps
import Algorithms.MeTTa.Simple.Semantics.PeTTaCore

namespace Algorithms.MeTTa.Simple

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Engine
open MeTTailCore.MeTTaIL.Profile
open MeTTailCore.MeTTaIL.Match
open MeTTailCore.MeTTaIL.Substitution
open MeTTailCore.MeTTaSyntax

structure Diagnostics where
  parsedLines : Nat := 0
  appliedStmts : Nat := 0
  evalCalls : Nat := 0
  errors : Nat := 0
  messages : List String := []
deriving Repr, DecidableEq

structure Session where
  bundle : SpecBundle
  syntaxSpec : SyntaxSpec := MeTTailCore.MeTTaSyntax.petta
  maxSteps : Nat
  maxNodes : Nat
  diag : Diagnostics := {}

namespace Session

abbrev SyntaxStmt := MeTTailCore.MeTTaSyntax.SyntaxCommand

private def defaultMaxNodes (maxSteps : Nat) : Nat :=
  maxSteps * 256 + 1

def new (bundle : SpecBundle) : Session :=
  { bundle := bundle
    syntaxSpec := MeTTailCore.MeTTaSyntax.petta
    maxSteps := bundle.policy.maxFuel
    maxNodes := defaultMaxNodes bundle.policy.maxFuel
    diag := {} }

def load (s : Session) (bundle : SpecBundle) : Session :=
  { s with
      bundle := bundle
      maxSteps := bundle.policy.maxFuel
      maxNodes := defaultMaxNodes bundle.policy.maxFuel }

def withSyntax (s : Session) (syntaxSpec : SyntaxSpec) : Session :=
  { s with syntaxSpec := syntaxSpec }

def withBounds (s : Session) (maxSteps maxNodes : Nat) : Session :=
  { s with maxSteps := maxSteps, maxNodes := maxNodes }

def loadRules (s : Session) (rules : List RewriteRule) : Session :=
  let lang' : LanguageDef := { s.bundle.language with rewrites := rules }
  let bundle' : SpecBundle := { s.bundle with language := lang' }
  { s with bundle := bundle' }

private def boolOfPattern? : Pattern → Option Bool
  | .apply "True" [] => some true
  | .apply "False" [] => some false
  | .apply "true" [] => some true
  | .apply "false" [] => some false
  | _ => none

private def patternOfBool (b : Bool) : Pattern :=
  if b then .apply "True" [] else .apply "False" []

private def spacePolicy : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Policy :=
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.defaultPolicy

private def selfSpaceAtom : Pattern := spacePolicy.selfSpaceAtom

private def spaceRelationName? : Pattern → Option String :=
  spacePolicy.relationNameOfSpace?

private def spaceMutationInterface : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
  bundle := fun s => s.bundle
  setBundle := fun s b => { s with bundle := b }
  eval := fun s _ => (s, [])
  applyBindings := fun _ p => p
  normalizePattern := fun p => p
  matchPattern := matchPattern
  dedupPatterns := fun xs => xs
}

private def factsForSpace (s : Session) (space : Pattern) : List Pattern :=
  let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
    bundle := fun s => s.bundle
    setBundle := fun s b => { s with bundle := b }
    eval := fun s _ => (s, [])
    applyBindings := fun _ p => p
    normalizePattern := fun p => p
    matchPattern := matchPattern
    dedupPatterns := fun xs => xs
  }
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.factsForSpace I spacePolicy s space

private def dollarHeadVarName? : Pattern → Option String
  | .apply ctor [] =>
      if ctor.startsWith "$" then
        let name := (ctor.drop 1).toString
        if name.isEmpty then none else some name
      else
        none
  | _ => none

private def bindingLookup (bs : Bindings) (name : String) : Option Pattern :=
  bs.find? (·.1 == name) |>.map (·.2)

private partial def normalizeDollarVars : Pattern → Pattern
  | .fvar x => .fvar x
  | .bvar n => .bvar n
  | .apply ctor [] =>
      if ctor.startsWith "$" then
        let name := (ctor.drop 1).toString
        if name.isEmpty then .apply ctor [] else .fvar name
      else
        .apply ctor []
  | .apply ctor args =>
      .apply ctor (args.map normalizeDollarVars)
  | .lambda body =>
      .lambda (normalizeDollarVars body)
  | .multiLambda n body =>
      .multiLambda n (normalizeDollarVars body)
  | .subst body repl =>
      .subst (normalizeDollarVars body) (normalizeDollarVars repl)
  | .collection ct elems rest =>
      .collection ct (elems.map normalizeDollarVars) rest

private partial def applyBindingsCompat (bs : Bindings) : Pattern → Pattern
  | .fvar x =>
      match bindingLookup bs x with
      | some (.fvar y) =>
          if y == x then
            .fvar x
          else
            applyBindingsCompat bs (.fvar y)
      | some v => applyBindingsCompat bs v
      | none => .fvar x
  | .apply ctor [] =>
      match dollarHeadVarName? (.apply ctor []) with
      | some x =>
          match bindingLookup bs x with
          | some v => applyBindingsCompat bs v
          | none => .apply ctor []
      | none => .apply ctor []
  | .apply ctor args =>
      let args' := args.map (applyBindingsCompat bs)
      match dollarHeadVarName? (.apply ctor []) with
      | some x =>
          match bindingLookup bs x with
          | some (.apply c []) => .apply c args'
          | some v =>
              let v' := applyBindingsCompat bs v
              if args'.isEmpty then
                v'
              else
                .apply "Expr" (v' :: args')
          | none => .apply ctor args'
      | none => .apply ctor args'
  | .lambda body =>
      .lambda (applyBindingsCompat bs body)
  | .multiLambda n body =>
      .multiLambda n (applyBindingsCompat bs body)
  | .subst body repl =>
      .subst (applyBindingsCompat bs body) (applyBindingsCompat bs repl)
  | .collection ct elems rest =>
      .collection ct (elems.map (applyBindingsCompat bs)) rest
  | .bvar n => .bvar n

private def insertUniquePattern (xs : List Pattern) (x : Pattern) : List Pattern :=
  if xs.contains x then xs else x :: xs

private def dedupPatternList (xs : List Pattern) : List Pattern :=
  (xs.foldl insertUniquePattern []).reverse

private def matchFactsAgainstSpace (facts : List Pattern) : Pattern → List Bindings :=
  let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
    bundle := fun s => s.bundle
    setBundle := fun s b => { s with bundle := b }
    eval := fun s _ => (s, [])
    applyBindings := fun _ p => p
    normalizePattern := normalizeDollarVars
    matchPattern := matchPatternMeTTa
    dedupPatterns := dedupPatternList
  }
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.matchFactsAgainstSpace I facts

private def intrinsicFromBuiltins (s : Session) (ctor : String) (args : List Pattern) :
    List Pattern :=
  let rel := intrinsicRelationName ctor
  let rows := s.bundle.builtins.relation rel args
  rows.filterMap fun row =>
    match row with
    | [out] => some out
    | _ => none

private def intrinsicDirect (s : Session) (ctor : String) (args : List Pattern) : List Pattern :=
  intrinsicFromBuiltins s ctor args

private def reduceArgsFirst (ctor : String) : Bool :=
  ctor = "==" || ctor = "!=" ||
  ctor = "<" || ctor = ">" || ctor = "<=" || ctor = ">=" ||
  ctor = "+" || ctor = "-" || ctor = "*" || ctor = "/" || ctor = "%"

private partial def hasFreeVars : Pattern → Bool
  | .fvar _ => true
  | .bvar _ => false
  | .apply _ args => args.any hasFreeVars
  | .lambda body => hasFreeVars body
  | .multiLambda _ body => hasFreeVars body
  | .subst body repl => hasFreeVars body || hasFreeVars repl
  | .collection _ elems _ => elems.any hasFreeVars

mutual
  private partial def intrinsicReduceArgs (s : Session) : List Pattern → List (List Pattern)
    | [] => []
    | arg :: rest =>
        let headRed := intrinsicStep s arg
        if !headRed.isEmpty then
          headRed.map (fun arg' => arg' :: rest)
        else
          (intrinsicReduceArgs s rest).map (fun rest' => arg :: rest')

  private partial def intrinsicStep (s : Session) : Pattern → List Pattern
    | .apply ctor args =>
        if reduceArgsFirst ctor then
          let reducedArgs := intrinsicReduceArgs s args
          if !reducedArgs.isEmpty then
            reducedArgs.map (fun args' => .apply ctor args')
          else
            intrinsicDirect s ctor args
        else
          let direct := intrinsicDirect s ctor args
          if !direct.isEmpty then
            direct
          else
            (intrinsicReduceArgs s args).map (fun args' => .apply ctor args')
    | _ => []
end

private def dedupPatterns (xs : List Pattern) : List Pattern :=
  (xs.foldl
    (fun acc x => if acc.contains x then acc else x :: acc)
    []).reverse

private def compatRewriteInterface : Algorithms.MeTTa.Simple.Semantics.Dispatch.CompatRewriteInterface Session := {
  rewrites := fun s => s.bundle.language.rewrites
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
}

def step (s : Session) (term : Pattern) : List Pattern :=
  let intrinsic := intrinsicStep s term
  let compat := Algorithms.MeTTa.Simple.Semantics.Dispatch.compatRewriteStep compatRewriteInterface s term
  let generated :=
    if compat.isEmpty then
      SpecBundle.rewriteWithContext s.bundle term
    else
      []
  dedupPatterns (intrinsic ++ compat ++ generated)

private def withMessage (s : Session) (msg : String) : Session :=
  { s with diag := { s.diag with messages := msg :: s.diag.messages } }

private def noteParsed (s : Session) : Session :=
  { s with diag := { s.diag with parsedLines := s.diag.parsedLines + 1 } }

private def noteApplied (s : Session) : Session :=
  { s with diag := { s.diag with appliedStmts := s.diag.appliedStmts + 1 } }

private def noteEval (s : Session) : Session :=
  { s with diag := { s.diag with evalCalls := s.diag.evalCalls + 1 } }

private def noteError (s : Session) (msg : String) : Session :=
  let s' := { s with diag := { s.diag with errors := s.diag.errors + 1 } }
  withMessage s' msg

private def insertUnique (xs : List Pattern) (x : Pattern) : List Pattern :=
  if xs.contains x then xs else x :: xs

private def enqueueNext (pending : List (Pattern × Nat)) (depth : Nat)
    (terms : List Pattern) : List (Pattern × Nat) :=
  (terms.map (fun t => (t, depth))) ++ pending

mutual
  private partial def patternCmp (a b : Pattern) : Ordering :=
    match numericOfPattern? a, numericOfPattern? b with
    | some x, some y =>
        if x < y then
          .lt
        else if y < x then
          .gt
        else
          .eq
    | some _, none => .lt
    | none, some _ => .gt
    | none, none =>
        match a, b with
        | .fvar x, .fvar y => compare x y
        | .fvar _, _ => .lt
        | _, .fvar _ => .gt
        | .bvar n, .bvar m =>
            if n < m then .lt else if m < n then .gt else .eq
        | .bvar _, _ => .lt
        | _, .bvar _ => .gt
        | .apply ca as, .apply cb bs =>
            match compare ca cb with
            | .eq => patternListCmp as bs
            | ord => ord
        | .apply _ _, _ => .lt
        | _, .apply _ _ => .gt
        | .lambda x, .lambda y => patternCmp x y
        | .lambda _, _ => .lt
        | _, .lambda _ => .gt
        | .multiLambda na xa, .multiLambda nb xb =>
            if na < nb then .lt
            else if nb < na then .gt
            else patternCmp xa xb
        | .multiLambda _ _, _ => .lt
        | _, .multiLambda _ _ => .gt
        | .subst ba ra, .subst bb rb =>
            match patternCmp ba bb with
            | .eq => patternCmp ra rb
            | ord => ord
        | .subst _ _, _ => .lt
        | _, .subst _ _ => .gt
        | .collection cta ea _, .collection ctb eb _ =>
            let sa := reprStr cta
            let sb := reprStr ctb
            if sa < sb then .lt
            else if sb < sa then .gt
            else patternListCmp ea eb

  private partial def patternListCmp : List Pattern → List Pattern → Ordering
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | a :: as, b :: bs =>
        match patternCmp a b with
        | .eq => patternListCmp as bs
        | ord => ord
end

private def patternLt (a b : Pattern) : Bool :=
  patternCmp a b == .lt

private def insertPatternSorted (x : Pattern) : List Pattern → List Pattern
  | [] => [x]
  | y :: ys =>
      if patternLt x y then
        x :: y :: ys
      else
        y :: insertPatternSorted x ys

private def sortPatterns : List Pattern → List Pattern
  | [] => []
  | x :: xs => insertPatternSorted x (sortPatterns xs)

mutual
  private partial def evalWithStateCore (s : Session) (term : Pattern) : Session × List Pattern :=
    evalAuxStateful s s.maxNodes [(term, 0)] []

  private partial def firstRuleReduction? (s : Session) (term : Pattern) : Option Pattern :=
    (s.bundle.language.rewrites).findSome? (fun rule =>
      if rule.premises.isEmpty then
        let leftN := normalizeDollarVars rule.left
        let rightN := normalizeDollarVars rule.right
        match matchPatternMeTTa leftN term with
        | [] => none
        | bs :: _ => some (applyBindingsCompat bs rightN)
      else
        none)

  private partial def evalDeterministicArgs (s : Session) (fuel : Nat)
      (args : List Pattern) : Session × List Pattern :=
    match args with
    | [] => (s, [])
    | a :: rest =>
        let (s1, aV) := evalDeterministicCore s fuel a
        let (s2, restV) := evalDeterministicArgs s1 fuel rest
        (s2, aV :: restV)

  private partial def evalDeterministicCore (s : Session) (fuel : Nat)
      (term : Pattern) : Session × Pattern :=
    match fuel with
    | 0 => (s, term)
    | fuel + 1 =>
        match term with
        | .apply "if" [cond, thenBr, elseBr] =>
            let (s1, condV) := evalDeterministicCore s fuel cond
            match boolOfPattern? condV with
            | some true => evalDeterministicCore s1 fuel thenBr
            | some false => evalDeterministicCore s1 fuel elseBr
            | none => (s1, .apply "if" [condV, thenBr, elseBr])
        | .apply ctor args =>
            let (s1, argsV) := evalDeterministicArgs s fuel args
            let callV := .apply ctor argsV
            let direct := intrinsicDirect s1 ctor argsV
            if !direct.isEmpty then
              let out := direct.headD callV
              if out == callV then
                (s1, out)
              else
                evalDeterministicCore s1 fuel out
            else
              match firstRuleReduction? s1 callV with
              | some rhs =>
                  evalDeterministicCore s1 fuel rhs
              | none =>
                  let arities := rewriteAritiesForHead s1 ctor
                  let hasExact := arities.any (fun n => n == argsV.length)
                  let hasLarger := arities.any (fun n => n > argsV.length)
                  if hasLarger && !hasExact then
                    (s1, partialPattern ctor argsV)
                  else
                    (s1, callV)
        | _ => (s, term)

  private partial def evalAuxStateful (s : Session) (fuel : Nat)
      (pending : List (Pattern × Nat)) (normals : List Pattern) : Session × List Pattern :=
    match fuel with
    | 0 => (s, normals.reverse ++ pending.map Prod.fst)
    | fuel + 1 =>
        match pending with
        | [] => (s, normals.reverse)
        | (term, depth) :: rest =>
            let (s0, term0, _) := runNestedEffects s true false term
            if depth >= s.maxSteps then
              evalAuxStateful s0 fuel rest (insertUnique normals term0)
            else
              match intrinsicStateful s0 term0 with
              | some (s1, intrinsicOut) =>
                  let preserveMultiplicity :=
                    match term0 with
                    | .apply "let" _ => true
                    | .apply "match" _ => true
                    | .apply "foldall" _ => true
                    | .apply "forall" _ => true
                    | _ => false
                  let reducts :=
                    if preserveMultiplicity then
                      intrinsicOut
                    else
                      dedupPatterns intrinsicOut
                  if reducts.isEmpty then
                    evalAuxStateful s1 fuel rest normals
                  else
                    let pending' := enqueueNext rest (depth + 1) reducts
                    evalAuxStateful s1 fuel pending' normals
              | none =>
                  let reducts := s0.step term0
                  if reducts.isEmpty then
                    evalAuxStateful s0 fuel rest (insertUnique normals term0)
                  else
                    let pending' := enqueueNext rest (depth + 1) reducts
                    evalAuxStateful s0 fuel pending' normals

  private partial def evalSequenceStateful (s : Session)
      (terms : List Pattern) (acc : List Pattern) : Session × List Pattern :=
    match terms with
    | [] => (s, acc)
    | t :: ts =>
        let (s1, out) := evalWithStateCore s t
        evalSequenceStateful s1 ts (acc ++ out)

  private partial def evalMatchIntrinsic (s : Session)
      (space pat tmpl : Pattern) : Session × List Pattern :=
    let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
      bundle := fun s => s.bundle
      setBundle := fun s b => { s with bundle := b }
      eval := evalWithStateCore
      applyBindings := applyBindingsCompat
      normalizePattern := normalizeDollarVars
      matchPattern := matchPatternMeTTa
      dedupPatterns := dedupPatternList
    }
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic I spacePolicy s space pat tmpl

  private partial def findBindingsInSpace (s : Session) (space pat : Pattern) : List Bindings :=
    let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
      bundle := fun s => s.bundle
      setBundle := fun s b => { s with bundle := b }
      eval := fun s _ => (s, [])
      applyBindings := applyBindingsCompat
      normalizePattern := normalizeDollarVars
      matchPattern := matchPatternMeTTa
      dedupPatterns := dedupPatternList
    }
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.findBindingsInSpace I spacePolicy s space pat

  private partial def findBindingsInRules (s : Session) (pat : Pattern) : List Bindings :=
    s.bundle.language.rewrites.foldl
      (fun acc rule =>
        if rule.premises.isEmpty then
            acc ++ matchPatternMeTTa pat rule.left
        else
          acc)
      []

  private partial def typeCandidatesInSelf (s : Session) (x : Pattern) : List Pattern :=
    let facts := factsForSpace s selfSpaceAtom
    let fromFacts :=
      facts.foldl
        (fun acc fact =>
          match fact with
          | .apply ":" [lhs, ty] =>
              if (matchPatternMeTTa lhs x).isEmpty then
                acc
              else
                if acc.contains ty then acc else ty :: acc
          | _ => acc)
        []
    fromFacts.reverse

  private partial def predicatePolicyOf (s : Session) :
      Algorithms.MeTTa.Simple.Semantics.PredicateControl.Policy :=
    { specialHeads := s.syntaxSpec.predicateSpecialHeads }

  private partial def decodePredicateSpacePattern? (s : Session) :
      Pattern → Option (Pattern × Pattern) :=
    Algorithms.MeTTa.Simple.Semantics.PredicateControl.decodePredicateSpacePattern? (predicatePolicyOf s)

  private partial def isFailurePattern : Pattern → Bool :=
    Algorithms.MeTTa.Simple.Semantics.PredicateControl.isFailurePattern

  private partial def isEmptyResult : Pattern → Bool
    | .apply "empty" [] => true
    | .apply "Empty" [] => true
    | .apply "()" [] => true
    | _ => false

  private partial def bindingsForCondition? (s : Session) : Pattern → Option (List Bindings)
    | .apply "find" [space, pat] =>
        some (findBindingsInSpace s space pat)
    | .apply "succeedsPredicate" [pred] =>
        match decodePredicateSpacePattern? s pred with
        | some (space, pat) => some (findBindingsInSpace s space pat)
        | none => some []
    | .apply "is-member" [x, xs] =>
        let elems := tupleElems xs
        let varName? :=
          match x with
          | .fvar n => some n
          | .apply ctor [] =>
              if ctor.startsWith "$" then
                let n := (ctor.drop 1).toString
                if n.isEmpty then none else some n
              else
                none
          | _ => none
        match varName? with
        | some n =>
            some (elems.map (fun e => [(n, e)]))
        | none =>
            let (_sX, xVals0) := evalWithStateCore s x
            let xVals := if xVals0.isEmpty then [x] else xVals0
            let bs :=
              xVals.flatMap (fun xv =>
                elems.flatMap (fun e => matchPatternMeTTa xv e))
            some (dedupBindings bs)
    | .apply "=" [lhs, rhs] =>
        let (_sL, lhsOut0) := evalWithStateCore s lhs
        let (_sR, rhsOut0) := evalWithStateCore s rhs
        let lhsVals := if lhsOut0.isEmpty then [lhs] else lhsOut0
        let rhsVals := if rhsOut0.isEmpty then [rhs] else rhsOut0
        let raw :=
          lhsVals.flatMap (fun lv =>
            rhsVals.flatMap (fun rv =>
              let byL := matchPatternMeTTa lv rv
              let byR := matchPatternMeTTa rv lv
              let byEq := if lv == rv then ([[]] : List Bindings) else []
              byL ++ byR ++ byEq))
        some (dedupBindings raw)
    | .apply op [lhs, rhs] =>
        let isCmp :=
          op == "<" || op == ">" || op == "<=" || op == ">=" ||
          op == "==" || op == "!="
        if !isCmp then
          none
        else
          let lhsPairs := (constrainedCallBindingsAndValues s lhs).2
          let rhsPairs := (constrainedCallBindingsAndValues s rhs).2
          if !lhsPairs.isEmpty then
            let (_sR, rhsOut0) := evalWithStateCore s rhs
            let rhsVals := if rhsOut0.isEmpty then [rhs] else rhsOut0
            let raw :=
              lhsPairs.flatMap (fun (bs, lv) =>
                rhsVals.filterMap (fun rv =>
                  let ok :=
                    (intrinsicStep s (.apply op [lv, rv])).any
                      (fun p => boolOfPattern? p == some true)
                  if ok then some bs else none))
            some (dedupBindings raw)
          else if !rhsPairs.isEmpty then
            let (_sL, lhsOut0) := evalWithStateCore s lhs
            let lhsVals := if lhsOut0.isEmpty then [lhs] else lhsOut0
            let raw :=
              rhsPairs.flatMap (fun (bs, rv) =>
                lhsVals.filterMap (fun lv =>
                  let ok :=
                    (intrinsicStep s (.apply op [lv, rv])).any
                      (fun p => boolOfPattern? p == some true)
                  if ok then some bs else none))
            some (dedupBindings raw)
          else
            none
    | _ => none

  private partial def evalThenForBindings (s : Session) (thenBr : Pattern)
      (bindings : List Bindings) : Session × List Pattern :=
    bindings.foldl
      (fun (acc : Session × List Pattern) bs =>
        let sess := acc.1
        let outAcc := acc.2
        let thenSub := applyBindingsCompat bs thenBr
        let (sess', out) := evalWithStateCore sess thenSub
        (sess', outAcc ++ out))
      (s, [])

  private partial def evalIfIntrinsic (s : Session)
      (cond thenBr elseBr : Pattern) : Session × List Pattern :=
    match bindingsForCondition? s cond with
    | some bindings =>
        if bindings.isEmpty then
          evalWithStateCore s elseBr
        else
          evalThenForBindings s thenBr bindings
    | none =>
        let (sCond, condOut) := evalWithStateCore s cond
        let bools := condOut.filterMap boolOfPattern?
        if bools.isEmpty then
          (sCond, [])
        else
          bools.foldl
            (fun (acc : Session × List Pattern) b =>
              let sess := acc.1
              let outAcc := acc.2
              let (sess', out) :=
                if b then
                  evalWithStateCore sess thenBr
                else
                  evalWithStateCore sess elseBr
              (sess', outAcc ++ out))
            (sCond, [])

  private partial def matchLetPattern (pat value : Pattern) : List Bindings :=
    match normalizeDollarVars pat with
    | .fvar x => [[(x, value)]]
    | .apply ctor [] =>
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name.isEmpty then [] else [[(name, value)]]
        else
          matchPatternMeTTa pat value
    | _ => matchPatternMeTTa pat value

  private partial def isConstraintLetPattern : Pattern → Bool
    | .fvar "constraint" => true
    | .apply "$constraint" [] => true
    | .apply "constraint" [] => true
    | _ => false

  private partial def mergeBindingsLists (lhs rhs : List Bindings) : List Bindings :=
    lhs.flatMap (fun b1 => rhs.filterMap (fun b2 => mergeBindings b1 b2))

  private partial def dedupBindings (xs : List Bindings) : List Bindings :=
    (xs.foldl
      (fun acc x => if acc.contains x then acc else x :: acc)
      []).reverse

  private partial def bindingsForConstraintExpr (s : Session)
      (expr : Pattern) : Session × List Bindings :=
    let conjuncts :=
      match expr with
      | .apply "Expr" elems => elems
      | e => [e]
    conjuncts.foldl
      (fun (acc : Session × List Bindings) c =>
        let sess := acc.1
        let curr := acc.2
        match decodePredicateSpacePattern? sess c with
        | some (space, pat) =>
            let nextFacts := findBindingsInSpace sess space pat
            let nextRules :=
              if space == selfSpaceAtom then
                findBindingsInRules sess pat
              else
                []
            let next := nextFacts ++ nextRules
            (sess, mergeBindingsLists curr next)
        | none =>
            let (sess', out) := evalWithStateCore sess c
            if out.any isTruthy then
              (sess', curr)
            else
              (sess', []))
      (s, [[]])

  private partial def evalLetIntrinsic (s : Session)
      (pat val body : Pattern) : Session × List Pattern :=
    if isConstraintLetPattern pat then
      let (sB, bs) := bindingsForConstraintExpr s val
      if bs.isEmpty then
        (sB, [])
      else
        evalThenForBindings sB body bs
    else
      match pat with
      | .apply "True" [] =>
          match bindingsForCondition? s val with
          | some bs =>
              if bs.isEmpty then
                (s, [])
              else
                evalThenForBindings s body bs
          | none =>
              let (sVals, values) := evalWithStateCore s val
              values.foldl
                (fun (acc : Session × List Pattern) v =>
                  let sess := acc.1
                  let outAcc := acc.2
                  let matched := matchLetPattern pat v
                  matched.foldl
                    (fun (acc2 : Session × List Pattern) bs =>
                      let sess2 := acc2.1
                      let outAcc2 := acc2.2
                      let bodySub := applyBindingsCompat bs body
                      let (sess3, out) := evalWithStateCore sess2 bodySub
                      (sess3, outAcc2 ++ out))
                    (sess, outAcc))
                (sVals, [])
      | _ =>
          let (sVals, values) := evalWithStateCore s val
          values.foldl
            (fun (acc : Session × List Pattern) v =>
              let sess := acc.1
              let outAcc := acc.2
              let matched := matchLetPattern pat v
              matched.foldl
                (fun (acc2 : Session × List Pattern) bs =>
                  let sess2 := acc2.1
                  let outAcc2 := acc2.2
                  let bodySub := applyBindingsCompat bs body
                  let (sess3, out) := evalWithStateCore sess2 bodySub
                  (sess3, outAcc2 ++ out))
                (sess, outAcc))
            (sVals, [])

  private partial def evalTranslatePredicateWithEnv (s : Session) (env : Bindings)
      (expr : Pattern) : Session × List Pattern × Option Bindings :=
    let iface : Algorithms.MeTTa.Simple.Semantics.PredicateControl.Interface Session := {
      eval := evalWithStateCore
      findBindingsInSpace := findBindingsInSpace
      applyBindings := applyBindingsCompat
      intrinsicStep := intrinsicStep
    }
    Algorithms.MeTTa.Simple.Semantics.PredicateControl.evalTranslatePredicateWithEnv
      iface s env expr (predicatePolicyOf s)

  private partial def evalPrognWithEnv (s : Session) (env : Bindings)
      (exprs : List Pattern) : Session × List Pattern × Bindings :=
    let iface : Algorithms.MeTTa.Simple.Semantics.PredicateControl.Interface Session := {
      eval := evalWithStateCore
      findBindingsInSpace := findBindingsInSpace
      applyBindings := applyBindingsCompat
      intrinsicStep := intrinsicStep
    }
    Algorithms.MeTTa.Simple.Semantics.PredicateControl.evalPrognWithEnv
      iface s env exprs (predicatePolicyOf s)

  private partial def evalProg1WithEnv (s : Session) (env : Bindings)
      (exprs : List Pattern) : Session × List Pattern × Bindings :=
    let iface : Algorithms.MeTTa.Simple.Semantics.PredicateControl.Interface Session := {
      eval := evalWithStateCore
      findBindingsInSpace := findBindingsInSpace
      applyBindings := applyBindingsCompat
      intrinsicStep := intrinsicStep
    }
    Algorithms.MeTTa.Simple.Semantics.PredicateControl.evalProg1WithEnv
      iface s env exprs (predicatePolicyOf s)

  private partial def listConcatMapP (f : Pattern → List (List Pattern)) :
      List Pattern → List (List Pattern)
    | [] => []
    | x :: xs => f x ++ listConcatMapP f xs

  private partial def evalCallableApply (s : Session)
      (callable : Pattern) (args : List Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.evalCallableApply iface s callable args

  private partial def evalCaseIntrinsic (s : Session)
      (keyExpr branchesExpr : Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.ControlFlow.Interface Session := {
      eval := evalWithStateCore
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      evalCallableApply := evalCallableApply
      evalGeneratorValues := evalGeneratorValues
      isTruthy := isTruthy
      patternOfBool := patternOfBool
    }
    Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic iface s keyExpr branchesExpr

  private partial def evalForRuleEnumeration (s : Session) (expr : Pattern) :
      Session × List Pattern :=
    match intrinsicStateful s expr with
    | some (s1, out) =>
        let out' := if out.isEmpty then [expr] else out
        (s1, out')
    | none =>
        let (s1, out0) := evalWithStateCore s expr
        let out := if out0.isEmpty then [expr] else out0
        (s1, out)

  private partial def enumerateCallByRules (s : Session) (expr : Pattern) :
      Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules iface s expr

  private partial def refineCallableOutWithArgEnumeration (s : Session)
      (expr : Pattern) (baseOut : List Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
      iface s expr baseOut

  private partial def evalGeneratorValues (s : Session) (genExpr : Pattern) :
      Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.evalGeneratorValues iface s genExpr

  private partial def evalFoldallIntrinsic (s : Session)
      (aggExpr genExpr initExpr : Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.ControlFlow.Interface Session := {
      eval := evalWithStateCore
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      evalCallableApply := evalCallableApply
      evalGeneratorValues := evalGeneratorValues
      isTruthy := isTruthy
      patternOfBool := patternOfBool
    }
    Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic iface s aggExpr genExpr initExpr

  private partial def isTruthy : Pattern → Bool :=
    Algorithms.MeTTa.Simple.Semantics.PredicateControl.isTruthy

  private partial def evalForallIntrinsic (s : Session)
      (genExpr checkExpr : Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.ControlFlow.Interface Session := {
      eval := evalWithStateCore
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      evalCallableApply := evalCallableApply
      evalGeneratorValues := evalGeneratorValues
      isTruthy := isTruthy
      patternOfBool := patternOfBool
    }
    Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic iface s genExpr checkExpr

  private partial def matchHeadArgWithEval (s : Session)
      (patArg termArg : Pattern) : List Bindings :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.matchHeadArgWithEval iface s patArg termArg

  private partial def matchHeadArgsWithEval (s : Session)
      (patArgs termArgs : List Pattern) (states : List Bindings) : List Bindings :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.matchHeadArgsWithEval
      iface s patArgs termArgs states

  private partial def compatFunctionHeadRewrite (s : Session) (term : Pattern) :
      List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite iface s term

  private partial def hasCompatHeadConstraintRule
      (s : Session) (ctor : String) (arity : Nat) : Bool :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule iface s ctor arity

  private partial def rewriteAritiesForHead (s : Session) (ctor : String) : List Nat :=
    (s.bundle.language.rewrites).foldl
      (fun acc rule =>
        match rule.left with
        | .apply lCtor lArgs =>
            if lCtor == ctor then
              lArgs.length :: acc
            else
              acc
        | _ => acc)
      []

  private partial def rewriteCountForHeadArity (s : Session) (ctor : String) (arity : Nat) : Nat :=
    (s.bundle.language.rewrites).foldl
      (fun acc rule =>
        if rule.premises.isEmpty then
          match rule.left with
          | .apply lCtor lArgs =>
              if lCtor == ctor && lArgs.length == arity then
                acc + 1
              else
                acc
          | _ => acc
        else
          acc)
      0

  private partial def partialPattern (ctor : String) (args : List Pattern) : Pattern :=
    .apply "partial" [.apply ctor [], tupleOfElems args]

  private partial def isRuleCallableHead (s : Session) (ctor : String) : Bool :=
    (rewriteAritiesForHead s ctor).any (fun _ => true)

  private partial def isEagerCallableHead (s : Session) (ctor : String) : Bool :=
    reduceArgsFirst ctor ||
    ctor = "repr" || ctor = "call" || ctor = "eval" || ctor = "reduce" ||
    ctor = "chain" || ctor = "map-atom" ||
    isRuleCallableHead s ctor

  private partial def constrainedCallBindingsAndValues
      (s : Session) (expr : Pattern) : Session × List (Bindings × Pattern) :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.constrainedCallBindingsAndValues iface s expr

  private partial def evalTupleIntrinsic (s : Session)
      (elems : List Pattern) : Session × List Pattern :=
    let rec evalElems (sess : Session) : List Pattern → Session × List (List Pattern)
      | [] => (sess, [[]])
      | e :: rest =>
          let (sessHead, headOut0) := evalWithStateCore sess e
          let heads := if headOut0.isEmpty then [e] else headOut0
          let (sessTail, tails) := evalElems sessHead rest
          let combos :=
            listConcatMapP (fun h => tails.map (fun t => h :: t)) heads
          (sessTail, combos)
    let (s1, combos) := evalElems s elems
    let built :=
      combos.foldl
        (fun (acc : Session × List Pattern) xs =>
          let sess := acc.1
          let outAcc := acc.2
          let isCallableHead : String → Bool := fun ctor =>
            isRuleCallableHead sess ctor
          let fallback :=
            match xs with
            | [] => .apply "()" []
            | h :: tl =>
                match h with
                | .apply ctor [] =>
                    if isCallableHead ctor then
                      .apply ctor tl
                    else
                      .apply "Expr" xs
                | _ => .apply "Expr" xs
          match xs with
          | [] =>
              (sess, outAcc ++ [fallback])
          | h :: tl =>
              let tryCallable :=
                match h with
                | .apply "partial" _ => true
                | .apply "|->" _ => true
                | .lambda _ => true
                | .multiLambda _ _ => true
                | .fvar _ => true
                | .apply ctor _ => isCallableHead ctor
                | _ => false
              if tryCallable then
                let (sess', out0) := evalCallableApply sess h tl
                if out0.isEmpty then
                  (sess', outAcc ++ [fallback])
                else
                  (sess', outAcc ++ out0)
              else
                (sess, outAcc ++ [fallback]))
        (s1, [])
    built

  private partial def decodeLetBinding? : Pattern → Option (Pattern × Pattern)
    | .apply head [val] =>
        if head.startsWith "$" then
          let name := (head.drop 1).toString
          if name.isEmpty then none else some (.fvar name, val)
        else
          some (.apply head [], val)
    | .apply "Expr" [pat, val] => some (pat, val)
    | .collection _ [pat, val] _ => some (pat, val)
    | _ => none

  private partial def decodeLetBindings? : Pattern → Option (List (Pattern × Pattern))
    | .apply "Expr" elems => elems.mapM decodeLetBinding?
    | .collection _ elems _ => elems.mapM decodeLetBinding?
    | b =>
        match decodeLetBinding? b with
        | some one => some [one]
        | none => none

  private partial def evalLetStarDeterministic (s : Session)
      (bindings : List (Pattern × Pattern)) (body : Pattern) : Session × List Pattern :=
    let rec loop (sess : Session) (env : Bindings) :
        List (Pattern × Pattern) → Session × Option Bindings
      | [] => (sess, some env)
      | (pat, val) :: rest =>
          let valSub := applyBindingsCompat env val
          if valSub == .apply "cut" [] then
            let matched := matchLetPattern pat (patternOfBool true)
            let merged? := matched.findSome? (fun bs => mergeBindings env bs)
            match merged? with
            | none => (sess, none)
            | some env' =>
                let (sess', out?) := loop sess env' rest
                (sess', out?)
          else
            let directLambda? :=
              match valSub with
              | .apply "|->" [_, _] => some valSub
              | .lambda _ => some valSub
              | .multiLambda _ _ => some valSub
              | _ => none
            match directLambda? with
            | some v =>
                let merged? := (matchLetPattern pat v).findSome? (fun bs => mergeBindings env bs)
                match merged? with
                | none => (sess, none)
                | some env' =>
                    loop sess env' rest
            | none =>
                let (sessVals, vals) := evalWithStateCore sess valSub
                let firstVal? := vals.head?
                match firstVal? with
                | none => (sessVals, none)
                | some v =>
                    let merged? := (matchLetPattern pat v).findSome? (fun bs => mergeBindings env bs)
                    match merged? with
                    | none => (sessVals, none)
                    | some env' =>
                        loop sessVals env' rest
    let (s1, env?) := loop s [] bindings
    match env? with
    | none => (s1, [])
    | some env =>
        let bodySub := applyBindingsCompat env body
        evalWithStateCore s1 bodySub

  private partial def patternToSExpr : Pattern → String
    | .fvar x => "$" ++ x
    | .bvar n => s!"#{n}"
    | .apply "()" [] => "()"
    | .apply "partial" [fn, bound] =>
        let fnS := patternToSExpr fn
        let elems := tupleElems bound
        let boundS := "(" ++ String.intercalate " " (elems.map patternToSExpr) ++ ")"
        "(partial " ++ fnS ++ " " ++ boundS ++ ")"
    | .apply ctor [] => ctor
    | .apply ctor args =>
        "(" ++ ctor ++ " " ++ String.intercalate " " (args.map patternToSExpr) ++ ")"
    | .lambda body =>
        "(lambda " ++ patternToSExpr body ++ ")"
    | .multiLambda n body =>
        s!"(multi-lambda {n} {patternToSExpr body})"
    | .subst body repl =>
        "(subst " ++ patternToSExpr body ++ " " ++ patternToSExpr repl ++ ")"
    | .collection _ elems _ =>
        "(" ++ String.intercalate " " (elems.map patternToSExpr) ++ ")"

  private partial def intrinsicStateful (s : Session)
      (term : Pattern) : Option (Session × List Pattern) :=
    let pIface : Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Interface Session := {
      eval := evalWithStateCore
      evalDeterministic := evalDeterministicCore
      evalCallableApply := evalCallableApply
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      dedupPatterns := dedupPatternList
      typeCandidates := typeCandidatesInSelf
    }
    match Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic pIface s term with
    | some out => some out
    | none =>
      match term with
    | .apply "if" [cond, thenBr, elseBr] =>
        let (s', out) := evalIfIntrinsic s cond thenBr elseBr
        if out.isEmpty then
          none
        else
          some (s', dedupPatternList out)
    | .apply "if" [cond, thenBr] =>
        let (s', out) := evalIfIntrinsic s cond thenBr (.apply "()" [])
        if out.isEmpty then
          none
        else
          some (s', dedupPatternList out)
    | .apply "add-atom" [space, fact] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          setBundle := fun s b => { s with bundle := b }
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom I spacePolicy s space fact
        some (s', out)
    | .apply "remove-atom" [space, fact] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          setBundle := fun s b => { s with bundle := b }
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom I spacePolicy s space fact
        some (s', out)
    | .apply "remove-all-atoms" [space] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          setBundle := fun s b => { s with bundle := b }
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms I spacePolicy s space term
        some (s', out)
    | .apply "get-atoms" [space] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          setBundle := fun s b => { s with bundle := b }
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms I spacePolicy s space
        some (s', out)
    | .apply "match" [space, pat, tmpl] =>
        let (s', out) := evalMatchIntrinsic s space pat tmpl
        some (s', out)
    | .apply "match" [pat, tmpl] =>
        let (s', out) := evalMatchIntrinsic s selfSpaceAtom pat tmpl
        some (s', out)
    | .apply "case" [keyExpr, branchesExpr] =>
        let (s', out) := evalCaseIntrinsic s keyExpr branchesExpr
        some (s', dedupPatternList out)
    | .apply "foldall" [agg, gen, init] =>
        let (s', out) := evalFoldallIntrinsic s agg gen init
        some (s', dedupPatternList out)
    | .apply "forall" [gen, check] =>
        let (s', out) := evalForallIntrinsic s gen check
        some (s', out)
    | .apply "find" [space, pat] =>
        let bindings := findBindingsInSpace s space pat
        if bindings.isEmpty then
          some (s, [patternOfBool false])
        else
          some (s, [patternOfBool true])
    | .apply "succeedsPredicate" [pred] =>
        match decodePredicateSpacePattern? s pred with
        | some (space, pat) =>
            let bindings := findBindingsInSpace s space pat
            if bindings.isEmpty then
              some (s, [patternOfBool false])
            else
              some (s, [patternOfBool true])
        | none =>
            some (s, [patternOfBool false])
    | .apply "Predicate" [expr] =>
        some (s, [expr])
    | .apply "translatePredicate" [expr] =>
        let (s1, out, _env?) := evalTranslatePredicateWithEnv s [] expr
        some (s1, dedupPatternList out)
    | .apply "catch" [expr] =>
        let (s1, out) := evalWithStateCore s expr
        some (s1, out)
    | .apply "catch" [expr, _handler, fallback] =>
        let (s1, out) := evalWithStateCore s expr
        let failed := out.isEmpty || out.all isFailurePattern
        if failed then
          let (s2, outFallback) := evalWithStateCore s1 fallback
          some (s2, outFallback)
        else
          some (s1, out)
    | .apply "once" [arg] =>
        let (s', out) := evalWithStateCore s arg
        match out with
        | [] => some (s', [.apply "()" []])
        | x :: _ => some (s', [x])
    | .apply "progn" exprs =>
        let (s', out, _env) := evalPrognWithEnv s [] exprs
        some (s', out)
    | .apply "prog1" exprs =>
        let (s', out, _env) := evalProg1WithEnv s [] exprs
        some (s', out)
    | .apply "cut" [] =>
        some (s, [patternOfBool true])
    | .apply "hide" [arg] =>
        let (s', _out) :=
          match arg with
          | .apply "Expr" elems => evalSequenceStateful s elems []
          | _ => evalWithStateCore s arg
        some (s', [.apply "empty" []])
    | .apply "let" [pat, val, body] =>
        let (s', out) := evalLetIntrinsic s pat val body
        some (s', out)
    | .apply "let*" [binds, body] =>
        match decodeLetBindings? binds with
        | none => some (s, [term])
        | some bs =>
            let (s', out) := evalLetStarDeterministic s bs body
            some (s', out)
    | .apply "collapse" [arg] =>
        match arg with
        | .apply ctor args =>
            if hasCompatHeadConstraintRule s ctor args.length then
              let (sFH, pairs) := constrainedCallBindingsAndValues s arg
              let out := (pairs.map Prod.snd).filter (fun p => !isEmptyResult p)
              some (sFH, [tupleOfElems out])
            else
              let (s', out) := evalWithStateCore s arg
              let out' := out.filter (fun p => !isEmptyResult p)
              some (s', [tupleOfElems out'])
        | _ =>
            let (s', out) := evalWithStateCore s arg
            let out' := out.filter (fun p => !isEmptyResult p)
            some (s', [tupleOfElems out'])
    | .apply "superpose" [arg] =>
        let (sEval, out) := evalWithStateCore s arg
        let (s', flatRev) :=
          out.foldl
            (fun (acc : Session × List Pattern) x =>
              let sess := acc.1
              let collectedRev := acc.2
              let (sess', evaled) := evalWithStateCore sess x
              let pieces :=
                if evaled.isEmpty then
                  [x]
                else
                  evaled
              let flatPieces : List Pattern :=
                pieces.foldr
                  (fun p acc =>
                    tupleElems p ++ acc)
                  []
              let flatPieces := sortPatterns (flatPieces.filter (fun p => !isEmptyResult p))
              (sess', List.reverse flatPieces ++ collectedRev))
            (sEval, [])
        some (s', List.reverse flatRev)
    | .apply "msort" [arg] =>
        let (s', out) := evalWithStateCore s arg
        let sortTupleLike : Pattern → Pattern := fun p =>
          let elems := sortPatterns (tupleElems p)
          match elems with
          | [] => .apply "()" []
          | h :: tl =>
              match h with
              | .apply ctor [] => .apply ctor tl
              | _ => .apply "Expr" elems
        let sorted :=
          match out with
          | [one] => [sortTupleLike one]
          | _ => sortPatterns out
        some (s', sorted)
    | .apply "space" [left, right] =>
        let (sL, outL) := evalWithStateCore s left
        let (sR, outR) := evalWithStateCore sL right
        let lefts := if outL.isEmpty then [left] else outL
        let rights := if outR.isEmpty then [right] else outR
        let combos : List Pattern :=
          lefts.foldr
            (fun l acc =>
              (rights.map fun r => .apply "space" [l, r]) ++ acc)
            []
        some (sR, combos)
    | .apply "Expr" elems =>
        let (s', out) := evalTupleIntrinsic s elems
        some (s', dedupPatternList out)
    | .apply "repr" [arg] =>
        let (s', argV) := evalDeterministicCore s 1024 arg
        some (s', [.apply s!"\"{patternToSExpr argV}\"" []])
    | .apply ctor args =>
        let detRuleCount := rewriteCountForHeadArity s ctor args.length
        let detFuel := Nat.max 4096 (s.maxSteps * 65536)
        if detRuleCount == 1 && !(hasFreeVars (.apply ctor args)) then
          let (sDet, detOut) := evalDeterministicCore s detFuel (.apply ctor args)
          if detOut != .apply ctor args then
            some (sDet, [detOut])
          else
            none
        else
        let fromHeads := compatFunctionHeadRewrite s (.apply ctor args)
        if !fromHeads.isEmpty then
          some (s, dedupPatternList fromHeads)
        else if hasCompatHeadConstraintRule s ctor args.length then
          some (s, [])
        else
          let rec reduceArgs (prefixRev : List Pattern) (rest : List Pattern) : List Pattern :=
            match rest with
            | [] => []
            | a :: tail =>
                let aRed := step s a
                let rebuilt :=
                  aRed.map (fun a' => .apply ctor (prefixRev.reverse ++ (a' :: tail)))
                rebuilt ++ reduceArgs (a :: prefixRev) tail
          let reducts := dedupPatternList (reduceArgs [] args)
          if reducts.isEmpty then
            let arities := rewriteAritiesForHead s ctor
            let hasExact := arities.any (fun n => n == args.length)
            let hasLarger := arities.any (fun n => n > args.length)
            if hasLarger && !hasExact then
              some (s, [partialPattern ctor args])
            else
              none
          else
            some (s, reducts)
    | _ => none

  private partial def runNestedEffectsArgs (s : Session) (parentCallable : Bool)
      (args : List Pattern) (accRev : List Pattern) (changed : Bool) :
      Session × List Pattern × Bool :=
    match args with
    | [] => (s, accRev.reverse, changed)
    | a :: rest =>
        let (s1, a', ch) := runNestedEffects s false parentCallable a
        runNestedEffectsArgs s1 parentCallable rest (a' :: accRev) (changed || ch)

  /-- Execute stateful intrinsics under a term before reducing the term itself.
  This is the runtime hook that makes nested side-effects observable. -/
  private partial def runNestedEffects (s : Session) (isRoot : Bool)
      (parentCallable : Bool) (term : Pattern) : Session × Pattern × Bool :=
    match term with
    | .apply "let" [pat, val, body] =>
        (s, .apply "let" [pat, val, body], false)
    | .apply "let*" [binds, body] =>
        (s, .apply "let*" [binds, body], false)
    | .apply "quote" [q] =>
        (s, .apply "quote" [q], false)
    | .apply "add-atom" [space, fact] =>
        (s, .apply "add-atom" [space, fact], false)
    | .apply "remove-atom" [space, fact] =>
        (s, .apply "remove-atom" [space, fact], false)
    | .apply "remove-all-atoms" [space] =>
        (s, .apply "remove-all-atoms" [space], false)
    | .apply "get-atoms" [space] =>
        (s, .apply "get-atoms" [space], false)
    | .apply "import!" [space, path] =>
        (s, .apply "import!" [space, path], false)
    | .apply "import!" [space, path, opts] =>
        (s, .apply "import!" [space, path, opts], false)
    | .apply "call" args =>
      if isRoot then
        let (s1, args', changedArgs) := runNestedEffectsArgs s true args [] false
        (s1, .apply "call" args', changedArgs)
      else
        match intrinsicStateful s (.apply "call" args) with
        | some (s1, out) =>
            let repl := out.headD (.apply "call" args)
            (s1, repl, true)
        | none =>
            let (s1, args', changedArgs) := runNestedEffectsArgs s true args [] false
            (s1, .apply "call" args', changedArgs)
    | .apply "eval" args =>
      if isRoot then
        let (s1, args', changedArgs) := runNestedEffectsArgs s true args [] false
        (s1, .apply "eval" args', changedArgs)
      else
        match intrinsicStateful s (.apply "eval" args) with
        | some (s1, out) =>
            let repl := out.headD (.apply "eval" args)
            (s1, repl, true)
        | none =>
            let (s1, args', changedArgs) := runNestedEffectsArgs s true args [] false
            (s1, .apply "eval" args', changedArgs)
    | .apply "reduce" args =>
      if isRoot then
        let (s1, args', changedArgs) := runNestedEffectsArgs s true args [] false
        (s1, .apply "reduce" args', changedArgs)
      else
        match intrinsicStateful s (.apply "reduce" args) with
        | some (s1, out) =>
            let repl := out.headD (.apply "reduce" args)
            (s1, repl, true)
        | none =>
            let (s1, args', changedArgs) := runNestedEffectsArgs s true args [] false
            (s1, .apply "reduce" args', changedArgs)
    | .apply "chain" args =>
      if isRoot then
        let (s1, args', changedArgs) := runNestedEffectsArgs s true args [] false
        (s1, .apply "chain" args', changedArgs)
      else
        match intrinsicStateful s (.apply "chain" args) with
        | some (s1, out) =>
            let repl := out.headD (.apply "chain" args)
            (s1, repl, true)
        | none =>
            let (s1, args', changedArgs) := runNestedEffectsArgs s true args [] false
            (s1, .apply "chain" args', changedArgs)
    | .apply "match" args =>
      if isRoot then
        (s, .apply "match" args, false)
      else
          let (s1, args', changedArgs) := runNestedEffectsArgs s false args [] false
          (s1, .apply "match" args', changedArgs)
    | .apply "collapse" args =>
      if isRoot then
          (s, .apply "collapse" args, false)
      else
          match intrinsicStateful s (.apply "collapse" args) with
          | some (s1, out) =>
              let repl := out.headD (.apply "collapse" args)
              (s1, repl, true)
          | none =>
              (s, .apply "collapse" args, false)
    | .apply "superpose" args =>
      if isRoot then
          (s, .apply "superpose" args, false)
      else
          let (s1, args', changedArgs) := runNestedEffectsArgs s false args [] false
          (s1, .apply "superpose" args', changedArgs)
    | .apply "msort" args =>
      if isRoot then
          (s, .apply "msort" args, false)
      else
          match intrinsicStateful s (.apply "msort" args) with
          | some (s1, out) =>
              let repl := out.headD (.apply "msort" args)
              (s1, repl, true)
          | none =>
              (s, .apply "msort" args, false)
    | .apply ctor args =>
        let currentCallable := isEagerCallableHead s ctor
        let (s1, args', changedArgs) := runNestedEffectsArgs s currentCallable args [] false
        let term' := .apply ctor args'
        if !isRoot && !parentCallable && isRuleCallableHead s1 ctor && !args'.isEmpty then
          (s1, .apply "quote" [term'], true)
        else
          (s1, term', changedArgs)
    | .lambda body =>
        let (s1, body', changed) := runNestedEffects s false false body
        (s1, .lambda body', changed)
    | .multiLambda n body =>
        let (s1, body', changed) := runNestedEffects s false false body
        (s1, .multiLambda n body', changed)
    | .subst body repl =>
        let (s1, body', c1) := runNestedEffects s false false body
        let (s2, repl', c2) := runNestedEffects s1 false false repl
        (s2, .subst body' repl', c1 || c2)
    | .collection ct elems rest =>
        let (s1, elems', changed) := runNestedEffectsArgs s false elems [] false
        (s1, .collection ct elems' rest, changed)
    | _ =>
        (s, term, false)

end

def evalWithState (s : Session) (term : Pattern) : Session × List Pattern :=
  evalWithStateCore s term

def eval (s : Session) (term : Pattern) : List Pattern :=
  (evalWithState s term).2

def evalOne (s : Session) (term : Pattern) : Pattern :=
  match eval s term with
  | [] => term
  | t :: _ => t

def diagnostics (s : Session) : Diagnostics :=
  { s.diag with messages := s.diag.messages.reverse }

def parseStmtWith (syntaxSpec : SyntaxSpec) (input : String) : Except String SyntaxStmt :=
  Algorithms.MeTTa.Simple.Parser.parseStmtWith syntaxSpec input

def parseStmt (input : String) : Except String SyntaxStmt :=
  parseStmtWith MeTTailCore.MeTTaSyntax.petta input

def parseLineWith (syntaxSpec : SyntaxSpec) (line : String) : Except String SyntaxStmt :=
  Algorithms.MeTTa.Simple.Parser.parseLineWith syntaxSpec line

def parseLine (line : String) : Except String SyntaxStmt :=
  parseLineWith MeTTailCore.MeTTaSyntax.petta line

def parseProgramWith (syntaxSpec : SyntaxSpec) (text : String) : Except String (List (Nat × SyntaxStmt)) :=
  Algorithms.MeTTa.Simple.Parser.parseProgramWith syntaxSpec text

def parseProgram (text : String) : Except String (List (Nat × SyntaxStmt)) :=
  parseProgramWith MeTTailCore.MeTTaSyntax.petta text

private def mkRuleName (s : Session) : String :=
  s!"USER_RULE_{s.bundle.language.rewrites.length}"

private def addRelationTuple (env : RelationEnv) (row : RelationTuple) : RelationEnv :=
  { tuples := fun rel args =>
      let base := env.tuples rel args
      if row.relation == rel && row.tuple.length == args.length then
        row.tuple :: base
      else
        base }

private def addBuiltinTuple (tbl : BuiltinTable) (row : RelationTuple) : BuiltinTable :=
  { relation := fun rel args =>
      let base := tbl.relation rel args
      if row.relation == rel && row.tuple.length == args.length then
        row.tuple :: base
      else
        base }

private def trueAtom : Pattern := .apply "True" []
private def falseAtom : Pattern := .apply "False" []

private def renderPattern (p : Pattern) : String :=
  reprStr p

private def renderPatternList (xs : List Pattern) : String :=
  "[" ++ String.intercalate ", " (xs.map renderPattern) ++ "]"

private def floatEqTol : Float := 0.000001

private def numericAtomEq (a b : Pattern) : Option Bool :=
  match numericOfPattern? a, numericOfPattern? b with
  | some x, some y => some (Float.abs (x - y) <= floatEqTol)
  | _, _ => none

private def exprToListForm? : Pattern → Option Pattern
  | .apply "Expr" [] => some (.apply "()" [])
  | .apply "Expr" (.apply head [] :: tail) =>
      if head == "Expr" then
        none
      else
        some (.apply head tail)
  | _ => none

mutual
  private partial def patternSemEq : Pattern → Pattern → Bool
    | a, b =>
        match exprToListForm? a with
        | some a' => patternSemEq a' b
        | none =>
            match exprToListForm? b with
            | some b' => patternSemEq a b'
            | none =>
              match a, b with
              | .bvar n, .bvar m => n = m
              | .fvar x, .fvar y => x == y
              | .apply ca as, .apply cb bs =>
                  if as.isEmpty && bs.isEmpty then
                    match boolOfPattern? (.apply ca []), boolOfPattern? (.apply cb []) with
                    | some ba, some bb => ba = bb
                    | _, _ =>
                        match numericAtomEq (.apply ca []) (.apply cb []) with
                        | some ok => ok
                        | none => ca == cb
                  else
                    ca == cb && patternListSemEq as bs
              | .lambda x1, .lambda y1 => patternSemEq x1 y1
              | .multiLambda na x1, .multiLambda nb y1 =>
                  na = nb && patternSemEq x1 y1
              | .subst ba ra, .subst bb rb =>
                  patternSemEq ba bb && patternSemEq ra rb
              | .collection cta ea ra, .collection ctb eb rb =>
                  cta = ctb && ra = rb && patternListSemEq ea eb
              | _, _ => false

  private partial def patternListSemEq : List Pattern → List Pattern → Bool
    | [], [] => true
    | a :: as, b :: bs => patternSemEq a b && patternListSemEq as bs
    | _, _ => false
end

private def runStrictTest (s : Session) (actual expected : Pattern) : Session × List Pattern :=
  let (s1, actualOut) := evalWithState s actual
  let (s2, expectedOut) := evalWithState s1 expected
  let sameDirect := patternListSemEq actualOut expectedOut
  let sameTupleFallback :=
    match expectedOut with
    | [expOne] => patternSemEq (tupleOfElems actualOut) expOne
    | _ => false
  let same := sameDirect || sameTupleFallback
  let s0 := noteEval (noteEval s2)
  if same then
    let s1 := withMessage s0 s!"test passed: actual={renderPatternList actualOut}"
    (s1, [trueAtom])
  else
    let s1 := noteError s0
      s!"test failed: actual={renderPatternList actualOut} expected={renderPatternList expectedOut}"
    (s1, [falseAtom])

def applyStmt (s : Session) (stmt : SyntaxStmt) : Session × List Pattern :=
  match stmt with
  | .empty => (s, [])
  | .defineEq lhs rhs =>
      let rule : RewriteRule := {
        name := mkRuleName s
        typeContext := []
        premises := []
        left := lhs
        right := rhs
      }
      let rules' := s.bundle.language.rewrites ++ [rule]
      let s0 := (noteApplied s).loadRules rules'
      let s' := withMessage s0 s!"loaded rule {rule.name}"
      (s', [])
  | .defineType lhs rhs =>
      let p := .apply ":" [lhs, rhs]
      let row : RelationTuple := { relation := "selfFact", tuple := [p] }
      let env' := addRelationTuple s.bundle.relationEnv row
      let bundle' : SpecBundle := { s.bundle with relationEnv := env' }
      let s0 := noteApplied { s with bundle := bundle' }
      let s' := withMessage s0 "added type fact to relation selfFact/1"
      (s', [])
  | .fact p =>
      let row : RelationTuple := { relation := "selfFact", tuple := [p] }
      let env' := addRelationTuple s.bundle.relationEnv row
      let bundle' : SpecBundle := { s.bundle with relationEnv := env' }
      let s0 := noteApplied { s with bundle := bundle' }
      let s' := withMessage s0 "added fact to relation selfFact/1"
      (s', [])
  | .eval term =>
      match term with
      | .apply "test" [actual, expected] =>
          let (s0, out) := runStrictTest s actual expected
          let s' := noteApplied s0
          (s', out)
      | .apply "test" [actual, expected, expectedBool] =>
          let (s0, out) := runStrictTest s actual expected
          let actualBool := match out with | [b] => b | _ => falseAtom
          let (sBool, expectedBoolOut) := evalWithState s0 expectedBool
          let sameBool := expectedBoolOut = [actualBool]
          let s1 := noteEval sBool
          let s2 :=
            if sameBool then
              withMessage s1 s!"test bool matched: {renderPattern actualBool}"
            else
              noteError s1
                s!"test bool mismatch: expected={renderPatternList expectedBoolOut} actual={renderPatternList [actualBool]}"
          let s' := noteApplied s2
          (s', out)
      | _ =>
          let (sEval, out) := evalWithState s term
          let s0 := noteApplied (noteEval sEval)
          let s' := withMessage s0 s!"query produced {out.length} result(s)"
          (s', out)
  | .relationFact rel tuple =>
      let row : RelationTuple := { relation := rel, tuple := tuple }
      let env' := addRelationTuple s.bundle.relationEnv row
      let bundle' : SpecBundle := { s.bundle with relationEnv := env' }
      let s0 := noteApplied { s with bundle := bundle' }
      let s' := withMessage s0 s!"added relation fact {rel}/{tuple.length}"
      (s', [])
  | .builtinFact rel tuple =>
      let row : RelationTuple := { relation := rel, tuple := tuple }
      let builtins' := addBuiltinTuple s.bundle.builtins row
      let bundle' : SpecBundle := { s.bundle with builtins := builtins' }
      let s0 := noteApplied { s with bundle := bundle' }
      let s' := withMessage s0 s!"added builtin fact {rel}/{tuple.length}"
      (s', [])
  | .setFuel n =>
      let policy' : RuntimePolicy := { s.bundle.policy with maxFuel := n }
      let bundle' : SpecBundle := { s.bundle with policy := policy' }
      let s' : Session :=
        { s with
          bundle := bundle'
          maxSteps := n
          maxNodes := defaultMaxNodes n }
      let s0 := noteApplied s'
      let s'' := withMessage s0 s!"set max fuel to {n}"
      (s'', [])
  | .import path =>
      let s0 := noteApplied s
      let s' := withMessage s0 s!"import directive recorded (not yet implemented): {path}"
      (s', [])
  | .newSpace name =>
      let s0 := noteApplied s
      let s' := withMessage s0 s!"new-space directive recorded (space={name})"
      (s', [])
  | .addAtom space atom =>
      match spaceRelationName? space with
      | none =>
          let s' := noteError (noteApplied s) s!"invalid space in add-atom directive: {renderPattern space}"
          (s', [])
      | some rel =>
          let (s', _out) :=
            Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom
              spaceMutationInterface spacePolicy s space atom
          let s0 := noteApplied s'
          let s' := withMessage s0 s!"added atom to {rel}/1"
          (s', [])
  | .removeAtom space atom =>
      match spaceRelationName? space with
      | none =>
          let s' := noteError (noteApplied s) s!"invalid space in remove-atom directive: {renderPattern space}"
          (s', [])
      | some rel =>
          let (s', _out) :=
            Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom
              spaceMutationInterface spacePolicy s space atom
          let s0 := noteApplied s'
          let s' := withMessage s0 s!"removed atom from {rel}/1"
          (s', [])
  | .directive head args =>
      let row : RelationTuple := { relation := "selfFact", tuple := [.apply head args] }
      let env' := addRelationTuple s.bundle.relationEnv row
      let bundle' : SpecBundle := { s.bundle with relationEnv := env' }
      let s0 := noteApplied { s with bundle := bundle' }
      let s' := withMessage s0 s!"lowered directive {head} to selfFact/1"
      (s', [])

def evalExpr (s : Session) (input : String) : Except String (Session × List Pattern) := do
  let expr ← Algorithms.MeTTa.Simple.Parser.parseExpr input
  let (s1, out) := evalWithState s expr
  let s' := withMessage (noteEval s1) s!"evalExpr produced {out.length} result(s)"
  pure (s', out)

private def runParsed (s : Session) (lineNo : Nat) (stmt : SyntaxStmt) :
    Session × Option (Nat × List Pattern) :=
  let s1 := noteParsed s
  let (s2, out) := applyStmt s1 stmt
  if out.isEmpty then
    (s2, none)
  else
    (s2, some (lineNo, out))

private def runLine (s : Session) (lineNo : Nat) (line : String) :
    Session × Option (Nat × List Pattern) :=
  match parseLineWith s.syntaxSpec line with
  | .ok stmt => runParsed s lineNo stmt
  | .error err =>
      let s2 := noteError (noteParsed s) s!"line {lineNo}: {err}"
      (s2, none)

private def runLinesAux (s : Session) (lineNo : Nat) :
    List String → Session × List (Nat × List Pattern)
  | [] => (s, [])
  | line :: rest =>
      let (s1, out?) := runLine s lineNo line
      let (s2, outs) := runLinesAux s1 (lineNo + 1) rest
      match out? with
      | none => (s2, outs)
      | some out => (s2, out :: outs)

def runLines (s : Session) (lines : List String) : Session × List (Nat × List Pattern) :=
  runLinesAux s 1 lines

private def runProgramAux (s : Session) :
    List (Nat × SyntaxStmt) → Session × List (Nat × List Pattern)
  | [] => (s, [])
  | (lineNo, stmt) :: rest =>
      let (s1, out?) := runParsed s lineNo stmt
      let (s2, outs) := runProgramAux s1 rest
      match out? with
      | none => (s2, outs)
      | some out => (s2, out :: outs)

def runText (s : Session) (text : String) : Session × List (Nat × List Pattern) :=
  match parseProgramWith s.syntaxSpec text with
  | .ok program => runProgramAux s program
  | .error err => (noteError s err, [])

def loadText (s : Session) (text : String) : Session :=
  (runText s text).1

def loadFile (s : Session) (path : System.FilePath) : IO Session := do
  let text ← IO.FS.readFile path
  pure (loadText s text)

end Session

end Algorithms.MeTTa.Simple
