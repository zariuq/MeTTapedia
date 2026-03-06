import MeTTailCore
import Algorithms.MeTTa.Simple.Parser
import Algorithms.MeTTa.Simple.Relations
import Algorithms.MeTTa.Simple.Semantics.PredicateControl
import Algorithms.MeTTa.Simple.Semantics.ControlFlow
import Algorithms.MeTTa.Simple.Semantics.Dispatch
import Algorithms.MeTTa.Simple.Semantics.CallSolve
import Algorithms.MeTTa.Simple.Semantics.SpaceOps
import Algorithms.MeTTa.Simple.Semantics.ImportOps
import Algorithms.MeTTa.Simple.Semantics.TranslatorOps
import Algorithms.MeTTa.Simple.Semantics.PeTTaCore
import Algorithms.MeTTa.Simple.Semantics.ConditionSolver
import Algorithms.MeTTa.Simple.Semantics.DeterministicEval
import Algorithms.MeTTa.Simple.Semantics.StateEffects
import Algorithms.MeTTa.Simple.Semantics.StreamOps
import Algorithms.MeTTa.Simple.Semantics.Assertions
import Algorithms.MeTTa.Simple.Backend.CompiledBundle
import Algorithms.MeTTa.Simple.Backend.RuleIndex
import Algorithms.MeTTa.Simple.Backend.ReferenceEval
import Algorithms.MeTTa.Simple.Backend.SessionDeterministic
import Algorithms.MeTTa.Simple.Backend.OptimizedEval
import Algorithms.MeTTa.Simple.Backend.OptimizedRefinement

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

structure VectorEntry where
  atom : Pattern
  vector : List Float
deriving Repr

structure VectorSpace where
  dim : Nat
  entries : List VectorEntry := []
deriving Repr

structure Session where
  bundle : SpecBundle
  compiledRules : Algorithms.MeTTa.Simple.Backend.CompiledBundle.View :=
    Algorithms.MeTTa.Simple.Backend.CompiledBundle.empty
  useCompiledIndexes : Bool := true
  syntaxSpec : SyntaxSpec := MeTTailCore.MeTTaSyntax.petta
  assertionPolicy : Algorithms.MeTTa.Simple.Semantics.Assertions.Policy := {}
  maxSteps : Nat
  maxNodes : Nat
  moduleSources : List (String × String) := []
  loadedModules : List String := []
  translatorRuleHeads : List String := []
  stateCells : List (String × Pattern) := []
  vectorSpaces : List (String × VectorSpace) := []
  diag : Diagnostics := {}

namespace Session

abbrev SyntaxStmt := MeTTailCore.MeTTaSyntax.SyntaxCommand

private def defaultMaxNodes (maxSteps : Nat) : Nat :=
  maxSteps * 256 + 1

private def compileRulesFromBundle (bundle : SpecBundle) :
    Algorithms.MeTTa.Simple.Backend.CompiledBundle.View :=
  let rec normalize : Pattern → Pattern
    | .fvar x => .fvar x
    | .bvar n => .bvar n
    | .apply ctor [] =>
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name.isEmpty then .apply ctor [] else .fvar name
        else
          .apply ctor []
    | .apply ctor args =>
        .apply ctor (args.map normalize)
    | .lambda body =>
        .lambda (normalize body)
    | .multiLambda n body =>
        .multiLambda n (normalize body)
    | .subst body repl =>
        .subst (normalize body) (normalize repl)
    | .collection ct elems rest =>
        .collection ct (elems.map normalize) rest
  let selfFacts :=
    ((bundle.relationEnv.tuples "selfFact" [(.fvar "_")]).filterMap fun row =>
      match row with
      | [fact] => some fact
      | _ => none).reverse
  Algorithms.MeTTa.Simple.Backend.CompiledBundle.build
    normalize bundle.language.rewrites selfFacts

theorem compileRulesFromBundle_premiseFreeRulesForHeadArity_eq_scan
    (bundle : SpecBundle) (ctor : String) (arity : Nat) :
    Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity
        (compileRulesFromBundle bundle) ctor arity
      =
    Algorithms.MeTTa.Simple.Backend.CompiledBundle.scanPremiseFreeRulesForHeadArity
      bundle.language.rewrites ctor arity := by
  unfold compileRulesFromBundle
  simp [Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity_build_eq_scan]

private def withBundleCompiled (s : Session) (bundle : SpecBundle) : Session :=
  { s with
      bundle := bundle
      compiledRules := compileRulesFromBundle bundle }

def CompiledConsistent (s : Session) : Prop :=
  s.compiledRules = compileRulesFromBundle s.bundle

abbrev WF (s : Session) : Prop := CompiledConsistent s

theorem compiledConsistent_withBundleCompiled (s : Session) (bundle : SpecBundle) :
    CompiledConsistent (withBundleCompiled s bundle) := by
  rfl

def new (bundle : SpecBundle) : Session :=
  { bundle := bundle
    compiledRules := compileRulesFromBundle bundle
    syntaxSpec := MeTTailCore.MeTTaSyntax.petta
    maxSteps := bundle.policy.maxFuel
    maxNodes := defaultMaxNodes bundle.policy.maxFuel
    diag := {} }

theorem compiledConsistent_new (bundle : SpecBundle) :
    CompiledConsistent (new bundle) := by
  rfl

def load (s : Session) (bundle : SpecBundle) : Session :=
  let s' := withBundleCompiled s bundle
  { s' with
      maxSteps := bundle.policy.maxFuel
      maxNodes := defaultMaxNodes bundle.policy.maxFuel }

theorem compiledConsistent_load (s : Session) (bundle : SpecBundle) :
    CompiledConsistent (load s bundle) := by
  unfold load
  simp [CompiledConsistent, withBundleCompiled]

def withModuleSources (s : Session) (sources : List (String × String)) : Session :=
  { s with moduleSources := sources }

theorem compiledConsistent_withModuleSources (s : Session)
    (sources : List (String × String))
    (h : CompiledConsistent s) :
    CompiledConsistent (withModuleSources s sources) := by
  simpa [withModuleSources, CompiledConsistent] using h

def withSyntax (s : Session) (syntaxSpec : SyntaxSpec) : Session :=
  { s with syntaxSpec := syntaxSpec }

theorem compiledConsistent_withSyntax (s : Session) (syntaxSpec : SyntaxSpec)
    (h : CompiledConsistent s) :
    CompiledConsistent (withSyntax s syntaxSpec) := by
  simpa [withSyntax, CompiledConsistent] using h

def withAssertionPolicy (s : Session)
    (assertionPolicy : Algorithms.MeTTa.Simple.Semantics.Assertions.Policy) : Session :=
  { s with assertionPolicy := assertionPolicy }

theorem compiledConsistent_withAssertionPolicy (s : Session)
    (assertionPolicy : Algorithms.MeTTa.Simple.Semantics.Assertions.Policy)
    (h : CompiledConsistent s) :
    CompiledConsistent (withAssertionPolicy s assertionPolicy) := by
  simpa [withAssertionPolicy, CompiledConsistent] using h

def withCompiledIndexes (s : Session) (enabled : Bool) : Session :=
  { s with useCompiledIndexes := enabled }

theorem compiledConsistent_withCompiledIndexes (s : Session) (enabled : Bool)
    (h : CompiledConsistent s) :
    CompiledConsistent (withCompiledIndexes s enabled) := by
  simpa [withCompiledIndexes, CompiledConsistent] using h

def withBounds (s : Session) (maxSteps maxNodes : Nat) : Session :=
  { s with maxSteps := maxSteps, maxNodes := maxNodes }

theorem compiledConsistent_withBounds (s : Session) (maxSteps maxNodes : Nat)
    (h : CompiledConsistent s) :
    CompiledConsistent (withBounds s maxSteps maxNodes) := by
  simpa [withBounds, CompiledConsistent] using h

def loadRules (s : Session) (rules : List RewriteRule) : Session :=
  let lang' : LanguageDef := { s.bundle.language with rewrites := rules }
  let bundle' : SpecBundle := { s.bundle with language := lang' }
  withBundleCompiled s bundle'

theorem compiledConsistent_loadRules (s : Session) (rules : List RewriteRule) :
    CompiledConsistent (loadRules s rules) := by
  unfold loadRules
  exact compiledConsistent_withBundleCompiled s _

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
  rewrites := fun s => s.bundle.language.rewrites
  setBundle := withBundleCompiled
  eval := fun s _ => (s, [])
  applyBindings := fun _ p => p
  normalizePattern := fun p => p
  normalizeForSpaceMatch := fun p => p
  matchPattern := matchPattern
  dedupPatterns := fun xs => xs
}


private def factsForSpace (s : Session) (space : Pattern) : List Pattern :=
  let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
    bundle := fun s => s.bundle
    rewrites := fun s => s.bundle.language.rewrites
    setBundle := withBundleCompiled
    eval := fun s _ => (s, [])
    applyBindings := fun _ p => p
    normalizePattern := fun p => p
    normalizeForSpaceMatch := fun p => p
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

private partial def lambdaParamNamesCompat : Pattern → List String
  | .fvar x => [x]
  | .apply "Expr" elems =>
      (elems.map lambdaParamNamesCompat).foldr (· ++ ·) []
  | .apply ctor args =>
      let headNames :=
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name.isEmpty then [] else [name]
        else
          []
      headNames ++ ((args.map lambdaParamNamesCompat).foldr (· ++ ·) [])
  | _ => []

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

private def isHESyntax (s : Session) : Bool :=
  s.syntaxSpec == MeTTailCore.MeTTaSyntax.he

private partial def normalizeHESpacePattern : Pattern → Pattern
  | .fvar x => .fvar x
  | .bvar n => .bvar n
  | .apply "Sym" [tok] =>
      match normalizeHESpacePattern tok with
      | .apply name [] => .apply name []
      | tok' => .apply "Sym" [tok']
  | .apply "Expr" (head :: args) =>
      let head' := normalizeHESpacePattern head
      let args' := args.map normalizeHESpacePattern
      match head' with
      | .apply name [] => .apply name args'
      | _ => .apply "Expr" (head' :: args')
  | .apply ctor [] =>
      .apply ctor []
  | .apply ctor args =>
      .apply ctor (args.map normalizeHESpacePattern)
  | .lambda body =>
      .lambda (normalizeHESpacePattern body)
  | .multiLambda n body =>
      .multiLambda n (normalizeHESpacePattern body)
  | .subst body repl =>
      .subst (normalizeHESpacePattern body) (normalizeHESpacePattern repl)
  | .collection ct elems rest =>
      .collection ct (elems.map normalizeHESpacePattern) rest

private def normalizeSpaceMatchPattern (s : Session) : Pattern → Pattern :=
  if isHESyntax s then
    fun p => normalizeHESpacePattern (normalizeDollarVars p)
  else
    normalizeDollarVars

private partial def applyBindingsCompat (bs : Bindings) : Pattern → Pattern :=
  let rec go (visited : List String) : Pattern → Pattern
    | .fvar x =>
        if visited.contains x then
          .fvar x
        else
          match bindingLookup bs x with
          | some (.fvar y) =>
              if y == x then
                .fvar x
              else
                go (x :: visited) (.fvar y)
          | some v => go (x :: visited) v
          | none => .fvar x
    | .apply ctor [] =>
        match dollarHeadVarName? (.apply ctor []) with
        | some x =>
            if visited.contains x then
              .apply ctor []
            else
              match bindingLookup bs x with
              | some v => go (x :: visited) v
              | none => .apply ctor []
        | none => .apply ctor []
    | .apply "|->" [params, body] =>
        let bound := lambdaParamNamesCompat params
        let bs' := bs.filter (fun b => !(bound.contains b.1))
        .apply "|->" [params, applyBindingsCompat bs' body]
    | .apply ctor args =>
        let args' := args.map (go visited)
        match dollarHeadVarName? (.apply ctor []) with
        | some x =>
            if visited.contains x then
              .apply ctor args'
            else
              match bindingLookup bs x with
              | some (.apply c []) => .apply c args'
              | some v =>
                  let v' := go (x :: visited) v
                  match v' with
                  | .apply "partial" [_base, _bound] =>
                      if args'.isEmpty then
                        v'
                      else
                        .apply "Expr" (v' :: args')
                  | .apply "|->" _ =>
                      if args'.isEmpty then
                        v'
                      else
                        .apply "Expr" (v' :: args')
                  | .lambda _ =>
                      if args'.isEmpty then
                        v'
                      else
                        .apply "Expr" (v' :: args')
                  | .multiLambda _ _ =>
                      if args'.isEmpty then
                        v'
                      else
                        .apply "Expr" (v' :: args')
                  | .apply c boundArgs =>
                      if boundArgs.isEmpty then
                        .apply c args'
                      else if args'.isEmpty then
                        v'
                      else
                        .apply "Expr" (v' :: args')
                  | _ =>
                      if args'.isEmpty then
                        v'
                      else
                        .apply "Expr" (v' :: args')
              | none => .apply ctor args'
        | none => .apply ctor args'
    | .lambda body =>
        .lambda (go visited body)
    | .multiLambda n body =>
        .multiLambda n (go visited body)
    | .subst body repl =>
        .subst (go visited body) (go visited repl)
    | .collection ct elems rest =>
        .collection ct (elems.map (go visited)) rest
    | .bvar n => .bvar n
  go []

private def insertUniquePattern (xs : List Pattern) (x : Pattern) : List Pattern :=
  if xs.contains x then xs else x :: xs

private def dedupPatternList (xs : List Pattern) : List Pattern :=
  (xs.foldl insertUniquePattern []).reverse

private def tupleAt? (xs : List Pattern) (n : Nat) : Option Pattern :=
  match xs.drop n with
  | [] => none
  | x :: _ => some x

private def vectorSpaceName? : Pattern → Option String
  | .apply name [] =>
      let n := name.trimAscii.toString
      if n.isEmpty then none else some n
  | .fvar name =>
      let n := name.trimAscii.toString
      if n.isEmpty then none else some n
  | _ => none

private def vectorOfPattern? (p : Pattern) : Option (List Float) :=
  (tupleElems p).mapM floatOfPattern?

private def normalizeVectorToDim (dim : Nat) (xs : List Float) : List Float :=
  let base := xs.take dim
  base ++ List.replicate (dim - base.length) 0.0

private def lookupVectorSpace? (s : Session) (name : String) : Option VectorSpace :=
  (s.vectorSpaces.find? (fun p => p.1 == name)).map Prod.snd

private def putVectorSpace (spaces : List (String × VectorSpace))
    (name : String) (vs : VectorSpace) : List (String × VectorSpace) :=
  match spaces with
  | [] => [(name, vs)]
  | (k, v) :: rest =>
      if k == name then
        (name, vs) :: rest
      else
        (k, v) :: putVectorSpace rest name vs

private def withVectorSpace (s : Session) (name : String) (vs : VectorSpace) : Session :=
  { s with vectorSpaces := putVectorSpace s.vectorSpaces name vs }

theorem compiledConsistent_withVectorSpace (s : Session) (name : String) (vs : VectorSpace)
    (h : CompiledConsistent s) :
    CompiledConsistent (withVectorSpace s name vs) := by
  simpa [withVectorSpace, CompiledConsistent] using h

theorem compiledConsistent_withStateCells (s : Session) (cells : List (String × Pattern))
    (h : CompiledConsistent s) :
    CompiledConsistent ({ s with stateCells := cells }) := by
  simpa [CompiledConsistent] using h

theorem compiledConsistent_withTranslatorRuleHeads (s : Session) (heads : List String)
    (h : CompiledConsistent s) :
    CompiledConsistent ({ s with translatorRuleHeads := heads }) := by
  simpa [CompiledConsistent] using h

private def addVectorEntry (vs : VectorSpace) (atom : Pattern) (vec : List Float) : VectorSpace :=
  let vecN := normalizeVectorToDim vs.dim vec
  let keep := vs.entries.filter (fun e => e.atom != atom)
  { vs with entries := { atom := atom, vector := vecN } :: keep }

private def squaredDistance (a b : List Float) : Float :=
  let aN := normalizeVectorToDim (Nat.max a.length b.length) a
  let bN := normalizeVectorToDim (Nat.max a.length b.length) b
  (List.zip aN bN).foldl
    (fun acc xy =>
      let d := xy.1 - xy.2
      acc + d * d)
    0.0

private partial def tokenStrings : Pattern → List String
  | .fvar n => ["$" ++ n]
  | .bvar n => [s!"#{n}"]
  | .apply ctor [] => [ctor]
  | .apply ctor args =>
      ctor :: (args.foldl (fun acc a => acc ++ tokenStrings a) [])
  | .lambda body => tokenStrings body
  | .multiLambda _ body => tokenStrings body
  | .subst body repl => tokenStrings body ++ tokenStrings repl
  | .collection _ elems _ =>
      elems.foldl (fun acc e => acc ++ tokenStrings e) []

private def sriVector (dim : Nat) (atom : Pattern) : List Float :=
  let toks := tokenStrings atom
  let rec build (i : Nat) (acc : List Float) : List Float :=
    if h : i < dim then
      let pos :=
        toks.foldl
          (fun s t =>
            let code := (t.toList.foldl (fun n c => n + c.toNat) 0)
            let seed := code + i * 131 + t.length * 17
            if seed % 2 = 0 then s + 1.0 else s - 1.0)
          0.0
      build (i + 1) (pos :: acc)
    else
      acc.reverse
  build 0 []

private def topKEntries (vs : VectorSpace) (query : List Float) (k : Nat) :
    List (Pattern × Float) :=
  let ranked : Array (Pattern × Float) :=
    (vs.entries.map (fun e => (e.atom, squaredDistance e.vector query))).toArray
      |>.qsort (fun a b => a.2 < b.2)
  ranked.toList.take k

private def floatLiteralPattern (f : Float) : Pattern :=
  .apply (toString f) []

private def matchFactsAgainstSpace (facts : List Pattern) : Pattern → List Bindings :=
  let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
    bundle := fun s => s.bundle
    rewrites := fun s => s.bundle.language.rewrites
    setBundle := withBundleCompiled
    eval := fun s _ => (s, [])
    applyBindings := fun _ p => p
    normalizePattern := normalizeDollarVars
    normalizeForSpaceMatch := normalizeDollarVars
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

private def builtinPartialMinArity? (ctor : String) : Option Nat :=
  if ctor = "+" || ctor = "*" || ctor = "/" || ctor = "%" ||
     ctor = "==" || ctor = "!=" ||
     ctor = "<" || ctor = ">" || ctor = "<=" || ctor = ">=" then
    some 2
  else
    none

private def deterministicPreserveArgs (ctor : String) : Bool :=
  ctor = "let" || ctor = "let*" ||
  ctor = "match" || ctor = "case" || ctor = "foldall" || ctor = "forall" ||
  ctor = "progn" || ctor = "prog1" ||
  ctor = "add-atom" || ctor = "remove-atom" || ctor = "remove-all-atoms" ||
  ctor = "get-atoms" || ctor = "import!" ||
  ctor = "call" || ctor = "eval" || ctor = "reduce" || ctor = "chain" ||
  ctor = "quote"

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

def dedupPatterns (xs : List Pattern) : List Pattern :=
  (xs.foldl
    (fun acc x => if acc.contains x then acc else x :: acc)
    []).reverse

private def compatRewriteInterface : Algorithms.MeTTa.Simple.Semantics.Dispatch.CompatRewriteInterface Session := {
  rewrites := fun s => s.bundle.language.rewrites
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
}

private def translatorInterface : Algorithms.MeTTa.Simple.Semantics.TranslatorOps.Interface Session := {
  rewrites := fun s => s.bundle.language.rewrites
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
}

def step (s : Session) (term : Pattern) : List Pattern :=
  let intrinsic := intrinsicStep s term
  let translated :=
    Algorithms.MeTTa.Simple.Semantics.TranslatorOps.translateCall
      translatorInterface s s.translatorRuleHeads term
  let compat :=
    if translated.isEmpty then
      Algorithms.MeTTa.Simple.Semantics.Dispatch.compatRewriteStep compatRewriteInterface s term
    else
      []
  let generated :=
    if compat.isEmpty && translated.isEmpty then
      SpecBundle.rewriteWithContext s.bundle term
    else
      []
  let intrinsic' := if compat.isEmpty then intrinsic else []
  intrinsic' ++ translated ++ compat ++ generated

private def withMessage (s : Session) (msg : String) : Session :=
  { s with diag := { s.diag with messages := msg :: s.diag.messages } }

theorem compiledConsistent_withMessage (s : Session) (msg : String)
    (h : CompiledConsistent s) :
    CompiledConsistent (withMessage s msg) := by
  simpa [withMessage, CompiledConsistent] using h

private def noteParsed (s : Session) : Session :=
  { s with diag := { s.diag with parsedLines := s.diag.parsedLines + 1 } }

theorem compiledConsistent_noteParsed (s : Session)
    (h : CompiledConsistent s) :
    CompiledConsistent (noteParsed s) := by
  simpa [noteParsed, CompiledConsistent] using h

private def noteApplied (s : Session) : Session :=
  { s with diag := { s.diag with appliedStmts := s.diag.appliedStmts + 1 } }

theorem compiledConsistent_noteApplied (s : Session)
    (h : CompiledConsistent s) :
    CompiledConsistent (noteApplied s) := by
  simpa [noteApplied, CompiledConsistent] using h

private def noteEval (s : Session) : Session :=
  { s with diag := { s.diag with evalCalls := s.diag.evalCalls + 1 } }

theorem compiledConsistent_noteEval (s : Session)
    (h : CompiledConsistent s) :
    CompiledConsistent (noteEval s) := by
  simpa [noteEval, CompiledConsistent] using h

private def noteError (s : Session) (msg : String) : Session :=
  let s' := { s with diag := { s.diag with errors := s.diag.errors + 1 } }
  withMessage s' msg

theorem compiledConsistent_noteError (s : Session) (msg : String)
    (h : CompiledConsistent s) :
    CompiledConsistent (noteError s msg) := by
  unfold noteError
  exact compiledConsistent_withMessage _ _ (by
    simpa [CompiledConsistent] using h)

def insertUnique (xs : List Pattern) (x : Pattern) : List Pattern :=
  if xs.contains x then xs else x :: xs

def enqueueNext (pending : List (Pattern × Nat)) (depth : Nat)
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

private def detMemoLimit (s : Session) : Nat :=
  Nat.max 4096 (s.maxNodes / 2)

private def compiledRuleView (s : Session) :
    Algorithms.MeTTa.Simple.Backend.CompiledBundle.View :=
  s.compiledRules

private def collectPremiseFreeRulesForHeadArity
    (ctor : String) (arity : Nat) (rules : List RewriteRule) : List RewriteRule :=
  Algorithms.MeTTa.Simple.Backend.CompiledBundle.scanPremiseFreeRulesForHeadArity
    rules ctor arity

mutual
  private partial def evalWithStateCore (s : Session) (term : Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
      maxNodes := fun s => s.maxNodes
      maxSteps := fun s => s.maxSteps
      runNestedEffects := runNestedEffects
      intrinsicStateful := intrinsicStateful
      isEagerCallableHead := isEagerCallableHead
      step := step
      enqueueNext := enqueueNext
      insertUnique := insertUnique
      dedupPatterns := dedupPatterns
    }
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore iface s term

  private partial def firstRuleReductionRaw? (s : Session) (term : Pattern) : Option Pattern :=
    (s.bundle.language.rewrites).findSome? (fun rule =>
      if rule.premises.isEmpty then
        let leftN := normalizeDollarVars rule.left
        let rightN := normalizeDollarVars rule.right
        match matchPatternMeTTa leftN term with
        | [] => none
        | bs :: _ => some (applyBindingsCompat bs rightN)
      else
        none)

  private partial def firstRuleReduction? (s : Session) (term : Pattern) : Option Pattern :=
    if s.useCompiledIndexes then
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.firstPremiseFreeReduction?
        (compiledRuleView s)
        matchPatternMeTTa
        applyBindingsCompat
        term
    else
      firstRuleReductionRaw? s term

  private partial def evalDeterministicCore (s : Session) (fuel : Nat)
      (term : Pattern) : Session × Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.DeterministicEval.Interface Session := {
      evalTupleIntrinsic := evalTupleIntrinsic
      translateCall := fun s callRaw =>
        Algorithms.MeTTa.Simple.Semantics.TranslatorOps.translateCall
          translatorInterface s s.translatorRuleHeads callRaw
      deterministicPreserveArgs := deterministicPreserveArgs
      intrinsicDirect := intrinsicDirect
      firstRuleReduction? := firstRuleReduction?
      rewriteAritiesForHead := rewriteAritiesForHead
      builtinPartialMinArity := builtinPartialMinArity?
      partialPattern := partialPattern
      memoLimit := detMemoLimit
    }
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval iface s fuel term

  private partial def evalAuxStateful (s : Session) (fuel : Nat)
      (pending : List (Pattern × Nat)) (normals : List Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
      maxNodes := fun s => s.maxNodes
      maxSteps := fun s => s.maxSteps
      runNestedEffects := runNestedEffects
      intrinsicStateful := intrinsicStateful
      isEagerCallableHead := isEagerCallableHead
      step := step
      enqueueNext := enqueueNext
      insertUnique := insertUnique
      dedupPatterns := dedupPatterns
    }
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful
      iface s fuel pending normals

  private partial def evalSequenceStateful (s : Session)
      (terms : List Pattern) (acc : List Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
      maxNodes := fun s => s.maxNodes
      maxSteps := fun s => s.maxSteps
      runNestedEffects := runNestedEffects
      intrinsicStateful := intrinsicStateful
      isEagerCallableHead := isEagerCallableHead
      step := step
      enqueueNext := enqueueNext
      insertUnique := insertUnique
      dedupPatterns := dedupPatterns
    }
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalSequenceStateful iface s terms acc

  private partial def evalMatchIntrinsic (s : Session)
      (space pat tmpl : Pattern) : Session × List Pattern :=
    let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
      bundle := fun s => s.bundle
      rewrites := fun s => s.bundle.language.rewrites
      setBundle := withBundleCompiled
      eval := evalWithStateCore
      applyBindings := applyBindingsCompat
      normalizePattern := normalizeDollarVars
      normalizeForSpaceMatch := normalizeSpaceMatchPattern s
      matchPattern := matchPatternMeTTa
      dedupPatterns := dedupPatternList
    }
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic I spacePolicy s space pat tmpl


  private partial def findBindingsInSpace (s : Session) (space pat : Pattern) : List Bindings :=
    let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
      bundle := fun s => s.bundle
      rewrites := fun s => s.bundle.language.rewrites
      setBundle := withBundleCompiled
      eval := fun s _ => (s, [])
      applyBindings := applyBindingsCompat
      normalizePattern := normalizeDollarVars
      normalizeForSpaceMatch := normalizeSpaceMatchPattern s
      matchPattern := matchPatternMeTTa
      dedupPatterns := dedupPatternList
    }
    let candidateFacts :=
      if s.useCompiledIndexes && space == selfSpaceAtom then
        Algorithms.MeTTa.Simple.Backend.CompiledBundle.candidateSelfFacts
          (compiledRuleView s)
          (normalizeSpaceMatchPattern s (normalizeDollarVars pat))
      else
        factsForSpace s space
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.findBindingsInSpaceWithFacts
      I spacePolicy s candidateFacts space pat

  private partial def findBindingsInRulesRaw (s : Session) (pat : Pattern) : List Bindings :=
    s.bundle.language.rewrites.foldl
      (fun acc rule =>
        if rule.premises.isEmpty then
          acc ++ matchPatternMeTTa pat rule.left
        else
          acc)
      []

  private partial def premiseFreeRulesForHeadArityRaw
      (s : Session) (ctor : String) (arity : Nat) : List RewriteRule :=
    collectPremiseFreeRulesForHeadArity ctor arity s.bundle.language.rewrites

  private partial def premiseFreeRulesForHeadArity
      (s : Session) (ctor : String) (arity : Nat) : List RewriteRule :=
    if s.useCompiledIndexes then
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity
        (compiledRuleView s) ctor arity
    else
      premiseFreeRulesForHeadArityRaw s ctor arity

  private partial def findBindingsInRules (s : Session) (pat : Pattern) : List Bindings :=
    if s.useCompiledIndexes then
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRuleBindings
        (compiledRuleView s)
        matchPatternMeTTa
        pat
    else
      findBindingsInRulesRaw s pat

  private partial def typeCandidatesInSelf (s : Session) (x : Pattern) : List Pattern :=
    if s.useCompiledIndexes then
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.typeCandidatesForSelf
        (compiledRuleView s)
        matchPatternMeTTa
        x
    else
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

  private partial def bindingsForConditionLeaf? (s : Session) : Pattern → Option (List Bindings)
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
          booleanConditionBindings? s (.apply op [lhs, rhs])
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
            let (_sL, lhsOut0) := evalWithStateCore s lhs
            let (_sR, rhsOut0) := evalWithStateCore s rhs
            let lhsVals := if lhsOut0.isEmpty then [lhs] else lhsOut0
            let rhsVals := if rhsOut0.isEmpty then [rhs] else rhsOut0
            let ok :=
              lhsVals.any (fun lv =>
                rhsVals.any (fun rv =>
                  (intrinsicStep s (.apply op [lv, rv])).any
                    (fun p => boolOfPattern? p == some true)))
            some (if ok then ([[]] : List Bindings) else [])
    | _ => none

  private partial def booleanConditionBindings? (s : Session) (cond : Pattern) :
      Option (List Bindings) :=
    let I : Algorithms.MeTTa.Simple.Semantics.ConditionSolver.Interface Session := {
      eval := evalWithStateCore
      applyBindings := applyBindingsCompat
      boolOfPattern? := boolOfPattern?
      dedupBindings := dedupBindings
      leafBindings? := bindingsForConditionLeaf?
    }
    Algorithms.MeTTa.Simple.Semantics.ConditionSolver.satisfyingBindingsForBoolCondition I s cond

  private partial def bindingsForCondition? (s : Session) : Pattern → Option (List Bindings)
    | cond =>
        match bindingsForConditionLeaf? s cond with
        | some bs => some bs
        | none => booleanConditionBindings? s cond

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
        let (sCond, condOut) :=
          match cond with
          | .apply "superpose" [_] =>
              match intrinsicStateful s cond with
              | some (s1, out) =>
                  let vals := if out.isEmpty then [cond] else out
                  (s1, vals)
              | none =>
                  let (s1, out) := evalWithStateCore s cond
                  let vals := if out.isEmpty then [cond] else out
                  (s1, vals)
          | _ =>
              let (s1, out) := evalWithStateCore s cond
              let vals := if out.isEmpty then [cond] else out
              (s1, vals)
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
        match c with
        | .apply "True" [] | .apply "true" [] =>
            (sess, curr)
        | .apply "False" [] | .apply "false" [] =>
            (sess, [])
        | _ =>
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
    let directLambdaVals? : Option (List Pattern) :=
      match val with
      | .apply "|->" [_, _] => some [val]
      | .lambda _ => some [val]
      | .multiLambda _ _ => some [val]
      | _ => none
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
              let (sVals, values) :=
                match directLambdaVals? with
                | some vs => (s, vs)
                | none => evalWithStateCore s val
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
          let (sVals, values) :=
            match directLambdaVals? with
            | some vs => (s, vs)
            | none => evalWithStateCore s val
          let patN := normalizeDollarVars pat
          let valN := normalizeDollarVars val
          let valsN := values.map normalizeDollarVars
          let useCallConstraintSolver :=
            Algorithms.MeTTa.Simple.Semantics.CallSolve.shouldAttemptCallConstraintSolve
              patN valN valsN
          let callSolveFuel : Nat :=
            Algorithms.MeTTa.Simple.Semantics.CallSolve.recommendedSolveFuel patN
          let (sCall, callBs) :=
            if useCallConstraintSolver then
              solveCallConstraintBindings sVals patN valsN callSolveFuel
            else
              (sVals, [])
          if !callBs.isEmpty then
            evalThenForBindings sCall body callBs
          else
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
              (sCall, [])

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
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
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
    let evalKeyValuesPreservingMultiplicity : Session → Pattern → Session × List Pattern :=
      fun sess key =>
        match key with
        | .apply "superpose" [_] =>
            match intrinsicStateful sess key with
            | some (sess', out) =>
                let vals := if out.isEmpty then [key] else out
                (sess', vals)
            | none =>
                let (sess', out) := evalWithStateCore sess key
                let vals := if out.isEmpty then [key] else out
                (sess', vals)
        | _ =>
            let (sess', out) := evalWithStateCore sess key
            let vals := if out.isEmpty then [key] else out
            (sess', vals)
    let iface : Algorithms.MeTTa.Simple.Semantics.ControlFlow.Interface Session := {
      eval := evalWithStateCore
      evalKeyValues := evalKeyValuesPreservingMultiplicity
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
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
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
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
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
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
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
      evalKeyValues := evalWithStateCore
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
      evalKeyValues := evalWithStateCore
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
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
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
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
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
      Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
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
    if s.useCompiledIndexes then
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.hasCompatHeadConstraintRule
        (compiledRuleView s) ctor arity
    else
      let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
        rewrites := fun s => s.bundle.language.rewrites
        premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
        eval := evalWithStateCore
        evalForRuleEnumeration := evalForRuleEnumeration
        applyBindings := applyBindingsCompat
        matchPattern := matchPatternMeTTa
        normalizePattern := normalizeDollarVars
        dedupBindings := dedupBindings
      }
      Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule iface s ctor arity

  private partial def rewriteAritiesForHead (s : Session) (ctor : String) : List Nat :=
    if s.useCompiledIndexes then
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.rewriteAritiesForHead
        (compiledRuleView s) ctor
    else
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
    if s.useCompiledIndexes then
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.rewriteCountForHeadArity
        (compiledRuleView s) ctor arity
    else
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
    if s.useCompiledIndexes then
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.hasRuleHead
        (compiledRuleView s) ctor
    else
      (rewriteAritiesForHead s ctor).any (fun _ => true)

  partial def isEagerCallableHead (s : Session) (ctor : String) : Bool :=
    reduceArgsFirst ctor ||
    ctor = "repr" || ctor = "call" || ctor = "eval" || ctor = "reduce" ||
    ctor = "chain" || ctor = "map-atom" ||
    isRuleCallableHead s ctor

  private partial def constrainedCallBindingsAndValues
      (s : Session) (expr : Pattern) : Session × List (Bindings × Pattern) :=
    let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
      eval := evalWithStateCore
      evalForRuleEnumeration := evalForRuleEnumeration
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    Algorithms.MeTTa.Simple.Semantics.Dispatch.constrainedCallBindingsAndValues iface s expr

  private partial def solveCallConstraintBindings
      (s : Session) (patTerm : Pattern) (vals : List Pattern) (fuel : Nat := 4) :
      Session × List Bindings :=
    let iface : Algorithms.MeTTa.Simple.Semantics.CallSolve.Interface Session := {
      normalizePattern := normalizeDollarVars
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      dedupBindings := dedupBindings
      hasCompatHeadConstraintRule := hasCompatHeadConstraintRule
      constrainedCallBindingsAndValues := constrainedCallBindingsAndValues
    }
    Algorithms.MeTTa.Simple.Semantics.CallSolve.solveCallConstraintBindings
      iface s patTerm vals fuel

  private partial def evalTupleElems (sess : Session) :
      List Pattern → Session × List (List Pattern)
    | [] => (sess, [[]])
    | e :: rest =>
        let (sessHead, headOut0) := evalWithStateCore sess e
        let heads := if headOut0.isEmpty then [e] else headOut0
        let (sessTail, tails) := evalTupleElems sessHead rest
        let combos :=
          listConcatMapP (fun h => tails.map (fun t => h :: t)) heads
        (sessTail, combos)

  private partial def evalTupleFallback (sess : Session) (xs : List Pattern) : Pattern :=
    let isCallableHead : String → Bool := fun ctor =>
      isRuleCallableHead sess ctor
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

  private partial def evalTupleBuildStep (acc : Session × List Pattern)
      (xs : List Pattern) : Session × List Pattern :=
    let sess := acc.1
    let outAcc := acc.2
    let fallback := evalTupleFallback sess xs
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
          | .apply ctor _ => isRuleCallableHead sess ctor
          | _ => false
        if tryCallable then
          let (sess', out0) := evalCallableApply sess h tl
          if out0.isEmpty then
            (sess', outAcc ++ [fallback])
          else
            (sess', outAcc ++ out0)
        else
          (sess, outAcc ++ [fallback])

  private partial def evalTupleBuilt (s : Session) (combos : List (List Pattern)) :
      Session × List Pattern :=
    combos.foldl evalTupleBuildStep (s, [])

  private partial def evalTupleIntrinsic (s : Session)
      (elems : List Pattern) : Session × List Pattern :=
    let (s1, combos) := evalTupleElems s elems
    evalTupleBuilt s1 combos

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

  partial def intrinsicStateful (s : Session)
      (term : Pattern) : Option (Session × List Pattern) :=
    let pIface : Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Interface Session := {
      eval := evalWithStateCore
      evalDeterministic := evalDeterministicCore
      evalCallableApply := evalCallableApply
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      findBindingsInSpace := findBindingsInSpace
      dedupPatterns := dedupPatternList
      typeCandidates := typeCandidatesInSelf
    }
    match Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic pIface s term with
    | some out => some out
    | none =>
        let stateI : Algorithms.MeTTa.Simple.Semantics.StateEffects.Interface Session := {
          eval := evalWithStateCore
          snapshot := fun sess => sess
          isFailure := isFailurePattern
          truePattern := patternOfBool true
          getStateCells := fun sess => sess.stateCells
          withStateCells := fun sess cells => { sess with stateCells := cells }
        }
        let preIntrinsic :=
          match Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic stateI s term with
          | some out => some out
          | none =>
              let streamI : Algorithms.MeTTa.Simple.Semantics.StreamOps.Interface Session := {
                evalValues := fun sess expr =>
                  match intrinsicStateful sess expr with
                  | some (s1, out0) =>
                      let out := if out0.isEmpty then [expr] else out0
                      (s1, out)
                  | none =>
                      let (s1, out0) := evalWithStateCore sess expr
                      let out := if out0.isEmpty then [expr] else out0
                      (s1, out)
              }
              Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic streamI s term
        match preIntrinsic with
        | some out => some out
        | none =>
          match term with
    | .apply "if" [cond, thenBr, elseBr] =>
        let (s', out) := evalIfIntrinsic s cond thenBr elseBr
        if out.isEmpty then
          none
        else
          some (s', out)
    | .apply "if" [cond, thenBr] =>
        let (s', out) := evalIfIntrinsic s cond thenBr (.apply "()" [])
        if out.isEmpty then
          none
        else
          some (s', out)
    | .apply "add-atom" [space, fact] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          rewrites := fun s => s.bundle.language.rewrites
          setBundle := withBundleCompiled
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          normalizeForSpaceMatch := normalizeSpaceMatchPattern s
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom I spacePolicy s space fact
        some (s', out)
    | .apply "add-atom!" [space, fact] =>
        let factNorm :=
          match fact with
          | .apply "=" [lhs, rhs] =>
              match boolOfPattern? rhs with
              | some true => lhs
              | some false => .apply "empty" []
              | none => fact
          | _ => fact
        if factNorm == .apply "empty" [] then
          some (s, [patternOfBool false])
        else
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          rewrites := fun s => s.bundle.language.rewrites
          setBundle := withBundleCompiled
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          normalizeForSpaceMatch := normalizeSpaceMatchPattern s
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom I spacePolicy s space factNorm
        some (s', out)
    | .apply "remove-atom" [space, fact] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          rewrites := fun s => s.bundle.language.rewrites
          setBundle := withBundleCompiled
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          normalizeForSpaceMatch := normalizeSpaceMatchPattern s
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom I spacePolicy s space fact
        some (s', out)
    | .apply "remove-atom!" [space, fact] =>
        let factNorm :=
          match fact with
          | .apply "=" [lhs, rhs] =>
              match boolOfPattern? rhs with
              | some true => lhs
              | some false => .apply "empty" []
              | none => fact
          | _ => fact
        if factNorm == .apply "empty" [] then
          some (s, [patternOfBool false])
        else
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          rewrites := fun s => s.bundle.language.rewrites
          setBundle := withBundleCompiled
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          normalizeForSpaceMatch := normalizeSpaceMatchPattern s
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom I spacePolicy s space factNorm
        some (s', out)
    | .apply "remove-all-atoms" [space] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          rewrites := fun s => s.bundle.language.rewrites
          setBundle := withBundleCompiled
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          normalizeForSpaceMatch := normalizeSpaceMatchPattern s
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms I spacePolicy s space term
        some (s', out)
    | .apply "remove-all-atoms!" [space] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          rewrites := fun s => s.bundle.language.rewrites
          setBundle := withBundleCompiled
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          normalizeForSpaceMatch := normalizeSpaceMatchPattern s
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms I spacePolicy s space term
        some (s', out)
    | .apply "get-atoms" [space] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          rewrites := fun s => s.bundle.language.rewrites
          setBundle := withBundleCompiled
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          normalizeForSpaceMatch := normalizeSpaceMatchPattern s
          matchPattern := matchPatternMeTTa
          dedupPatterns := dedupPatternList
        }
        let (s', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms I spacePolicy s space
        some (s', out)
    | .apply "get-atoms!" [space] =>
        let I : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
          bundle := fun s => s.bundle
          rewrites := fun s => s.bundle.language.rewrites
          setBundle := withBundleCompiled
          eval := evalWithStateCore
          applyBindings := applyBindingsCompat
          normalizePattern := normalizeDollarVars
          normalizeForSpaceMatch := normalizeSpaceMatchPattern s
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
        some (s', out)
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
    | .apply "add-translator-rule!" [arg] =>
        let heads' := Algorithms.MeTTa.Simple.Semantics.TranslatorOps.addHead s.translatorRuleHeads arg
        some ({ s with translatorRuleHeads := heads' }, [patternOfBool true])
    | .apply "remove-translator-rule!" [arg] =>
        let heads' := Algorithms.MeTTa.Simple.Semantics.TranslatorOps.removeHead s.translatorRuleHeads arg
        some ({ s with translatorRuleHeads := heads' }, [patternOfBool true])
    | .apply "new-atom-vectorspace" [space, dimPat] =>
        match (vectorSpaceName? space, intOfPattern? dimPat) with
        | (some name, some dimI) =>
            if dimI <= 0 then
              some (s, [patternOfBool false])
            else
              let dim := dimI.natAbs
              let s' := withVectorSpace s name { dim := dim, entries := [] }
              some (s', [patternOfBool true])
        | _ => some (s, [patternOfBool false])
    | .apply "add-atom-vector" [space, atom, vecPat] =>
        match (vectorSpaceName? space, vectorOfPattern? vecPat) with
        | (some name, some vec) =>
            match lookupVectorSpace? s name with
            | some vs =>
                let vs' := addVectorEntry vs atom vec
                let s' := withVectorSpace s name vs'
                some (s', [patternOfBool true])
            | none => some (s, [patternOfBool false])
        | _ => some (s, [patternOfBool false])
    | .apply "add-atom-SRI" [space, atom] =>
        match vectorSpaceName? space with
        | some name =>
            match lookupVectorSpace? s name with
            | some vs =>
                let vec := sriVector vs.dim atom
                let vs' := addVectorEntry vs atom vec
                let s' := withVectorSpace s name vs'
                some (s', [patternOfBool true])
            | none => some (s, [patternOfBool false])
        | none => some (s, [patternOfBool false])
    | .apply "match-k" [kPat, space, queryPat] =>
        match (intOfPattern? kPat, vectorSpaceName? space, vectorOfPattern? queryPat) with
        | (some kI, some name, some qv) =>
            match lookupVectorSpace? s name with
            | some vs =>
                let k : Nat := if kI <= 0 then 0 else kI.natAbs
                let hits := topKEntries vs qv k
                let rows := hits.map (fun h => tupleOfElems [h.1, floatLiteralPattern h.2])
                some (s, [tupleOfElems rows])
            | none => some (s, [tupleOfElems []])
        | _ => some (s, [tupleOfElems []])
    | .apply "match-sri" [kPat, space, query] =>
        match (intOfPattern? kPat, vectorSpaceName? space) with
        | (some kI, some name) =>
            match lookupVectorSpace? s name with
            | some vs =>
                let k : Nat := if kI <= 0 then 0 else kI.natAbs
                let qv := sriVector vs.dim query
                let hits := topKEntries vs qv k
                let rows := hits.map (fun h => tupleOfElems [h.1, floatLiteralPattern h.2])
                some (s, [tupleOfElems rows])
            | none => some (s, [tupleOfElems []])
        | _ => some (s, [tupleOfElems []])
    | .apply "match-SRI" [kPat, space, query] =>
        match (intOfPattern? kPat, vectorSpaceName? space) with
        | (some kI, some name) =>
            match lookupVectorSpace? s name with
            | some vs =>
                let k : Nat := if kI <= 0 then 0 else kI.natAbs
                let qv := sriVector vs.dim query
                let hits := topKEntries vs qv k
                let rows := hits.map (fun h => tupleOfElems [h.1, floatLiteralPattern h.2])
                some (s, [tupleOfElems rows])
            | none => some (s, [tupleOfElems []])
        | _ => some (s, [tupleOfElems []])
    | .apply "atom-of" [x] =>
        let (s1, x1, _) := runNestedEffects s true false x
        let (s2, out) :=
          match intrinsicStateful s1 x1 with
          | some (sI, outI) =>
              if outI.isEmpty then
                (sI, [x1])
              else
                (sI, outI)
          | none =>
              let reducts := step s1 x1
              if reducts.isEmpty then
                (s1, [x1])
              else
                (s1, reducts)
        let extracted :=
          out.filterMap fun candidate =>
            match tupleAt? (tupleElems candidate) 0 with
            | none => none
            | some row => tupleAt? (tupleElems row) 0
        if extracted.isEmpty then
          some (s2, [])
        else
          some (s2, dedupPatternList extracted)
    | .apply "once" [arg] =>
        let (s', out) := evalWithStateCore s arg
        match out with
        | [] => some (s', [.apply "()" []])
        | x :: _ => some (s', [x])
    | .apply "nop" [arg] =>
        let (s', _out) := evalWithStateCore s arg
        some (s', [.apply "()" []])
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
        let (s', flat) :=
          out.foldl
            (fun (acc : Session × List Pattern) x =>
              let sess := acc.1
              let collected := acc.2
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
              let flatPieces := flatPieces.filter (fun p => !isEmptyResult p)
              (sess', collected ++ flatPieces))
            (sEval, [])
        some (s', flat)
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
        let termExpr := .apply "Expr" elems
        let (s', out0) := evalTupleIntrinsic s elems
        let out1 := out0
        let outNonRefl := out1.filter (fun p => p != termExpr)
        let heLoweredHead :=
          match elems with
          | .apply "Sym" [_] :: _ => true
          | _ => false
        if outNonRefl.isEmpty && heLoweredHead then
          let rew := (step s' termExpr).filter (fun p => p != termExpr)
          if rew.isEmpty then
            some (s', [])
          else
            some (s', rew)
        else
          some (s', out1)
    | .apply "repr" [arg] =>
        let (s', argV) := evalDeterministicCore s 1024 arg
        some (s', [.apply s!"\"{patternToSExpr argV}\"" []])
    | .apply ctor args =>
        let needsPartial : Bool :=
          match builtinPartialMinArity? ctor with
          | some minArity => decide (args.length < minArity)
          | none => false
        if needsPartial then
          some (s, [partialPattern ctor args])
        else
          let fallback : Session × List Pattern :=
            let (sFH, fromHeads) := compatFunctionHeadRewrite s (.apply ctor args)
            if !fromHeads.isEmpty then
              (sFH, fromHeads)
            else if hasCompatHeadConstraintRule s ctor args.length then
              (s, [])
            else
              let rec reduceArgs (prefixRev : List Pattern) (rest : List Pattern) : List Pattern :=
                match rest with
                | [] => []
                | a :: tail =>
                    let aRed0 :=
                      match intrinsicStateful s a with
                      | some (_sA, outA) =>
                          if outA.isEmpty then step s a else outA
                      | none => step s a
                    let aRed := aRed0.filter (fun a' => a' != a)
                    let rebuilt :=
                      aRed.map (fun a' => .apply ctor (prefixRev.reverse ++ (a' :: tail)))
                    rebuilt ++ reduceArgs (a :: prefixRev) tail
              let reducts := reduceArgs [] args
              if reducts.isEmpty then
                let arities := rewriteAritiesForHead s ctor
                let hasExact := arities.any (fun n => n == args.length)
                let hasLarger := arities.any (fun n => n > args.length)
                if hasLarger && !hasExact && !args.isEmpty then
                  (s, [partialPattern ctor args])
                else
                  (s, [])
              else
                (s, reducts)
          let out := fallback.2
          if out.isEmpty then none else some fallback
    | _ => none

  partial def runNestedEffectsArgs (s : Session) (parentCallable : Bool)
      (args : List Pattern) (accRev : List Pattern) (changed : Bool) :
      Session × List Pattern × Bool :=
    let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
      maxNodes := fun s => s.maxNodes
      maxSteps := fun s => s.maxSteps
      runNestedEffects := runNestedEffects
      intrinsicStateful := intrinsicStateful
      isEagerCallableHead := isEagerCallableHead
      step := step
      enqueueNext := enqueueNext
      insertUnique := insertUnique
      dedupPatterns := dedupPatterns
    }
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffectsArgs
      iface s parentCallable args accRev changed

  /-- Execute stateful intrinsics under a term before reducing the term itself.
  This is the runtime hook that makes nested side-effects observable. -/
  partial def runNestedEffects (s : Session) (isRoot : Bool)
      (_parentCallable : Bool) (term : Pattern) : Session × Pattern × Bool :=
    let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
      maxNodes := fun s => s.maxNodes
      maxSteps := fun s => s.maxSteps
      runNestedEffects := runNestedEffects
      intrinsicStateful := intrinsicStateful
      isEagerCallableHead := isEagerCallableHead
      step := step
      enqueueNext := enqueueNext
      insertUnique := insertUnique
      dedupPatterns := dedupPatterns
    }
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
      iface s isRoot _parentCallable term

end

def referenceEvalInterface :
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
  maxNodes := fun s => s.maxNodes
  maxSteps := fun s => s.maxSteps
  runNestedEffects := runNestedEffects
  intrinsicStateful := intrinsicStateful
  isEagerCallableHead := isEagerCallableHead
  step := step
  enqueueNext := enqueueNext
  insertUnique := insertUnique
  dedupPatterns := dedupPatterns
}

def referenceEvalWithStateCore (s : Session) (term : Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore referenceEvalInterface s term

def referenceEvalAuxStateful (s : Session) (fuel : Nat)
    (pending : List (Pattern × Nat)) (normals : List Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful
    referenceEvalInterface s fuel pending normals

def referenceEvalSequenceStateful (s : Session)
    (terms : List Pattern) (acc : List Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalSequenceStateful
    referenceEvalInterface s terms acc

def referenceRunNestedEffectsArgs (s : Session) (parentCallable : Bool)
    (args accRev : List Pattern) (changed : Bool) : Session × List Pattern × Bool :=
  Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffectsArgs
    referenceEvalInterface s parentCallable args accRev changed

def referenceRunNestedEffects (s : Session) (isRoot parentCallable : Bool)
    (term : Pattern) : Session × Pattern × Bool :=
  Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
    referenceEvalInterface s isRoot parentCallable term

private def deterministicEvalInterface :
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.Interface Session := {
  evalTupleIntrinsic := evalTupleIntrinsic
  translateCall := fun s callRaw =>
    Algorithms.MeTTa.Simple.Semantics.TranslatorOps.translateCall
      translatorInterface s s.translatorRuleHeads callRaw
  deterministicPreserveArgs := deterministicPreserveArgs
  intrinsicDirect := intrinsicDirect
  firstRuleReduction? := firstRuleReduction?
  rewriteAritiesForHead := rewriteAritiesForHead
  builtinPartialMinArity := builtinPartialMinArity?
  partialPattern := partialPattern
  memoLimit := detMemoLimit
}

private theorem compiledConsistent_of_evalTupleBuildStep
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {acc : Session × List Pattern} {xs : List Pattern}
    (hAcc : CompiledConsistent acc.1) :
    CompiledConsistent (evalTupleBuildStep acc xs).1 := by
  cases acc with
  | mk sess outAcc =>
      cases xs with
      | nil =>
          simpa [evalTupleBuildStep] using hAcc
      | cons h tl =>
          by_cases hTry :
              (match h with
              | .apply "partial" _ => true
              | .apply "|->" _ => true
              | .lambda _ => true
              | .multiLambda _ _ => true
              | .fvar _ => true
              | .apply ctor _ => isRuleCallableHead sess ctor
              | _ => false)
          · simp [evalTupleBuildStep, hTry]
            cases hCall : evalCallableApply sess h tl with
            | mk sess' out0 =>
                have hSess' : CompiledConsistent sess' :=
                  hEvalCallablePres sess h tl sess' out0 hCall hAcc
                by_cases hEmpty : out0.isEmpty
                · simpa [hCall, hEmpty] using hSess'
                · simpa [hCall, hEmpty] using hSess'
          · simp [evalTupleBuildStep, hTry]
            simpa using hAcc

private theorem compiledConsistent_foldl_evalTupleBuildStep
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    ∀ (combos : List (List Pattern)) (acc : Session × List Pattern),
      CompiledConsistent acc.1 →
      CompiledConsistent ((combos.foldl evalTupleBuildStep acc).1) := by
  intro combos
  induction combos with
  | nil =>
      intro acc hAcc
      simpa
  | cons xs rest ih =>
      intro acc hAcc
      have hStep :
          CompiledConsistent (evalTupleBuildStep acc xs).1 :=
        compiledConsistent_of_evalTupleBuildStep hEvalCallablePres hAcc
      simpa [List.foldl] using ih (evalTupleBuildStep acc xs) hStep

private theorem compiledConsistent_of_evalTupleBuilt
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    (s : Session) (combos : List (List Pattern))
    (hs : CompiledConsistent s) :
    CompiledConsistent (evalTupleBuilt s combos).1 := by
  simpa [evalTupleBuilt] using
    compiledConsistent_foldl_evalTupleBuildStep hEvalCallablePres combos (s, []) hs

private theorem compiledConsistent_of_evalTupleElems
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1) :
    ∀ (s : Session) (elems : List Pattern),
      CompiledConsistent s →
      CompiledConsistent (evalTupleElems s elems).1 := by
  intro s elems hs
  induction elems generalizing s with
  | nil =>
      simpa [evalTupleElems] using hs
  | cons e rest ih =>
      have hHead : CompiledConsistent (evalWithStateCore s e).1 :=
        hEvalCorePres s e hs
      cases hEvalHead : evalWithStateCore s e with
      | mk s1 headOut0 =>
          have hs1 : CompiledConsistent s1 := by
            simpa [hEvalHead] using hHead
          have hTail : CompiledConsistent (evalTupleElems s1 rest).1 :=
            ih s1 hs1
          cases hEvalTail : evalTupleElems s1 rest with
          | mk s2 tails =>
              have hs2 : CompiledConsistent s2 := by
                simpa [hEvalTail] using hTail
              simpa [evalTupleElems, hEvalHead, hEvalTail] using hs2

private theorem compiledConsistent_of_evalTupleIntrinsic
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {elems : List Pattern} {s' : Session} {out : List Pattern}
    (hTuple : evalTupleIntrinsic s elems = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hElems : CompiledConsistent (evalTupleElems s elems).1 :=
    compiledConsistent_of_evalTupleElems hEvalCorePres s elems hs
  cases hEvalElems : evalTupleElems s elems with
  | mk s1 combos =>
      have hs1 : CompiledConsistent s1 := by
        simpa [hEvalElems] using hElems
      have hBuilt : CompiledConsistent (evalTupleBuilt s1 combos).1 :=
        compiledConsistent_of_evalTupleBuilt hEvalCallablePres s1 combos hs1
      have hState : (evalTupleBuilt s1 combos).1 = s' := by
        simpa [evalTupleIntrinsic, hEvalElems] using congrArg Prod.fst hTuple
      simpa [hState] using hBuilt

private def pettaCoreInterface :
    Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Interface Session := {
  eval := evalWithStateCore
  evalDeterministic := evalDeterministicCore
  evalCallableApply := evalCallableApply
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
  findBindingsInSpace := findBindingsInSpace
  dedupPatterns := dedupPatternList
  typeCandidates := typeCandidatesInSelf
}

theorem premiseFreeRulesForHeadArityRaw_eq_collect
    (s : Session) (ctor : String) (arity : Nat) :
    premiseFreeRulesForHeadArityRaw s ctor arity =
      collectPremiseFreeRulesForHeadArity ctor arity s.bundle.language.rewrites := by
  rfl

private def deterministicSearchInterface :
    Algorithms.MeTTa.Simple.Backend.SessionDeterministic.Interface Session := {
  rewrites := fun s => s.bundle.language.rewrites
  useCompiledIndexes := fun s => s.useCompiledIndexes
  compiledRules := compiledRuleView
  premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
  normalizePattern := normalizeDollarVars
  matchPattern := matchPatternMeTTa
  applyBindings := applyBindingsCompat
  evalTupleIntrinsic := evalTupleIntrinsic
  translateCall := fun s callRaw =>
    Algorithms.MeTTa.Simple.Semantics.TranslatorOps.translateCall
      translatorInterface s s.translatorRuleHeads callRaw
  deterministicPreserveArgs := deterministicPreserveArgs
  intrinsicDirect := intrinsicDirect
  rewriteAritiesForHead := rewriteAritiesForHead
  builtinPartialMinArity := builtinPartialMinArity?
  partialPattern := partialPattern
  memoLimit := detMemoLimit
}

private def spaceEvalInterface (s0 : Session) :
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
  bundle := fun s => s.bundle
  rewrites := fun s => s.bundle.language.rewrites
  setBundle := withBundleCompiled
  eval := evalWithStateCore
  applyBindings := applyBindingsCompat
  normalizePattern := normalizeDollarVars
  normalizeForSpaceMatch := normalizeSpaceMatchPattern s0
  matchPattern := matchPatternMeTTa
  dedupPatterns := dedupPatternList
}

private theorem spaceEvalInterface_preservation
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (s0 : Session) :
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.Preservation
      (spaceEvalInterface s0) CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    setBundle_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (evalWithStateCore s term).1 := hEvalCorePres s term hs
    have hState : (evalWithStateCore s term).1 = s' := by
      simpa [spaceEvalInterface] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s bundle hs
    exact compiledConsistent_withBundleCompiled s bundle

private theorem deterministicEvalInterface_preservation
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.Preservation
      deterministicEvalInterface CompiledConsistent := by
  refine {
    evalTupleIntrinsic_preserves := ?_
  }
  intro s elems s' out hTuple hs
  exact compiledConsistent_of_evalTupleIntrinsic hEvalCorePres hEvalCallablePres hTuple hs

private theorem compiledConsistent_of_evalDeterministicCore
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {fuel : Nat} {term : Pattern} {s' : Session} {out : Pattern}
    (hEval : evalDeterministicCore s fuel term = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval_preserves
      deterministicEvalInterface CompiledConsistent
      (deterministicEvalInterface_preservation hEvalCorePres hEvalCallablePres)
      s fuel term hs
  have hState : (evalDeterministicCore s fuel term).1 = s' := by
    simpa [evalDeterministicCore] using congrArg Prod.fst hEval
  simpa [hState] using hPres

private theorem pettaCoreInterface_preservation
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Preservation
      pettaCoreInterface CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    evalDeterministic_preserves := ?_,
    evalCallableApply_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (evalWithStateCore s term).1 := hEvalCorePres s term hs
    have hState : (evalWithStateCore s term).1 = s' := by
      simpa [pettaCoreInterface] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s fuel term s' out hEval hs
    exact compiledConsistent_of_evalDeterministicCore
      hEvalCorePres hEvalCallablePres hEval hs
  · intro s fn args s' out hEval hs
    exact hEvalCallablePres s fn args s' out hEval hs

private theorem compiledConsistent_of_pettaCore_evalIntrinsic
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {term : Pattern} {s' : Session} {out : List Pattern}
    (hPeTTa :
      Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
        pettaCoreInterface s term = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic_preserves
      pettaCoreInterface CompiledConsistent
      (pettaCoreInterface_preservation hEvalCorePres hEvalCallablePres)
      s term hs
  simpa [hPeTTa] using hPres

private def stateEffectsInterface :
    Algorithms.MeTTa.Simple.Semantics.StateEffects.Interface Session := {
  eval := evalWithStateCore
  snapshot := fun sess => sess
  isFailure := isFailurePattern
  truePattern := patternOfBool true
  getStateCells := fun sess => sess.stateCells
  withStateCells := fun sess cells => { sess with stateCells := cells }
}

private theorem stateEffectsInterface_preservation
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1) :
    Algorithms.MeTTa.Simple.Semantics.StateEffects.Preservation
      stateEffectsInterface CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    snapshot_preserves := ?_,
    withStateCells_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (evalWithStateCore s term).1 := hEvalCorePres s term hs
    have hState : (evalWithStateCore s term).1 = s' := by
      simpa [stateEffectsInterface] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s hs
    simpa [stateEffectsInterface] using hs
  · intro s cells hs
    exact compiledConsistent_withStateCells s cells hs

private theorem compiledConsistent_of_stateEffects_evalIntrinsic
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    {s : Session} {term : Pattern} {s' : Session} {out : List Pattern}
    (hState :
      Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
        stateEffectsInterface s term = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic_preserves
      stateEffectsInterface CompiledConsistent
      (stateEffectsInterface_preservation hEvalCorePres) s term hs
  simpa [hState] using hPres

private def streamOpsInterface :
    Algorithms.MeTTa.Simple.Semantics.StreamOps.Interface Session := {
  evalValues := fun sess expr =>
    match intrinsicStateful sess expr with
    | some (s1, out0) =>
        let out := if out0.isEmpty then [expr] else out0
        (s1, out)
    | none =>
        let (s1, out0) := evalWithStateCore sess expr
        let out := if out0.isEmpty then [expr] else out0
        (s1, out)
}

private theorem streamOpsInterface_preservation
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    Algorithms.MeTTa.Simple.Semantics.StreamOps.Preservation
      streamOpsInterface CompiledConsistent := by
  refine { evalValues_preserves := ?_ }
  intro s expr s' out hEval hs
  unfold streamOpsInterface at hEval
  cases hIntr : intrinsicStateful s expr with
  | none =>
      simp [hIntr] at hEval
      have hPres : CompiledConsistent (evalWithStateCore s expr).1 :=
        hEvalCorePres s expr hs
      have hState : (evalWithStateCore s expr).1 = s' := hEval.1
      simpa [hState] using hPres
  | some res =>
      rcases res with ⟨s1, out0⟩
      simp [hIntr] at hEval
      have hPres : CompiledConsistent s1 :=
        hIntrinsicPres s expr s1 out0 hIntr hs
      have hState : s1 = s' := hEval.1
      simpa [hState] using hPres

private theorem compiledConsistent_of_streamOps_evalIntrinsic
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {term : Pattern} {s' : Session} {out : List Pattern}
    (hStream :
      Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
        streamOpsInterface s term = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic_preserves
      streamOpsInterface CompiledConsistent
      (streamOpsInterface_preservation hEvalCorePres hIntrinsicPres) s term hs
  simpa [hStream] using hPres

private def hasDeterministicBlockingRewriteBodies (s : Session) : Bool :=
  Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasDeterministicBlockingRewriteBodies
    deterministicSearchInterface s

private def hasMultipleRootCandidates (term : Pattern)
    (candidates : List RewriteRule) : Bool :=
  Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootCandidates
    deterministicSearchInterface term candidates

private theorem hasMultipleRootCandidates_congr
    (term : Pattern) {candidates₁ candidates₂ : List RewriteRule}
    (h : candidates₁ = candidates₂) :
    hasMultipleRootCandidates term candidates₁ =
      hasMultipleRootCandidates term candidates₂ := by
  simpa [hasMultipleRootCandidates] using
    Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootCandidates_congr
      deterministicSearchInterface term h

private def hasMultipleRootRuleChoices (s : Session) (term : Pattern) : Bool :=
  Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices
    deterministicSearchInterface s term

theorem premiseFreeRulesForHeadArity_eq_index_when_enabled
    (s : Session) (ctor : String) (arity : Nat)
    (hEnabled : s.useCompiledIndexes = true) :
    premiseFreeRulesForHeadArity s ctor arity =
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity
        (compiledRuleView s) ctor arity := by
  simp [premiseFreeRulesForHeadArity, hEnabled]

theorem premiseFreeRulesForHeadArity_eq_raw_when_disabled
    (s : Session) (ctor : String) (arity : Nat)
    (hDisabled : s.useCompiledIndexes = false) :
    premiseFreeRulesForHeadArity s ctor arity =
      premiseFreeRulesForHeadArityRaw s ctor arity := by
  simp [premiseFreeRulesForHeadArity, hDisabled]

theorem premiseFreeRulesForHeadArity_index_eq_raw_of_compiledRules_consistent
    (s : Session) (ctor : String) (arity : Nat)
    (hCompiled : s.compiledRules = compileRulesFromBundle s.bundle) :
    Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity
        (compiledRuleView s) ctor arity
      =
    premiseFreeRulesForHeadArityRaw s ctor arity := by
  unfold compiledRuleView premiseFreeRulesForHeadArityRaw
  rw [hCompiled]
  simpa [collectPremiseFreeRulesForHeadArity] using
    compileRulesFromBundle_premiseFreeRulesForHeadArity_eq_scan
      s.bundle ctor arity

theorem hasMultipleRootRuleChoices_apply_uses_index_when_enabled
    (s : Session) (ctor : String) (args : List Pattern)
    (hEnabled : s.useCompiledIndexes = true) :
    hasMultipleRootRuleChoices s (.apply ctor args) =
      hasMultipleRootCandidates (.apply ctor args)
        (Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity
          (compiledRuleView s) ctor args.length) := by
  simp [hasMultipleRootRuleChoices,
    Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices,
    hasMultipleRootCandidates,
    Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootCandidates,
    deterministicSearchInterface, premiseFreeRulesForHeadArity, hEnabled]

theorem hasMultipleRootRuleChoices_apply_uses_raw_when_disabled
    (s : Session) (ctor : String) (args : List Pattern)
    (hDisabled : s.useCompiledIndexes = false) :
    hasMultipleRootRuleChoices s (.apply ctor args) =
      hasMultipleRootCandidates (.apply ctor args)
        (collectPremiseFreeRulesForHeadArity ctor args.length s.bundle.language.rewrites) := by
  simp [hasMultipleRootRuleChoices,
    Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices,
    hasMultipleRootCandidates,
    Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootCandidates,
    deterministicSearchInterface, premiseFreeRulesForHeadArity, hDisabled,
    premiseFreeRulesForHeadArityRaw_eq_collect]

theorem hasMultipleRootRuleChoices_apply_enabled_eq_disabled_of_compiledRules_consistent
    (s : Session) (ctor : String) (args : List Pattern)
    (hCompiled : s.compiledRules = compileRulesFromBundle s.bundle) :
    hasMultipleRootRuleChoices (withCompiledIndexes s true) (.apply ctor args) =
      hasMultipleRootRuleChoices (withCompiledIndexes s false) (.apply ctor args) := by
  have hIndexRaw :
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity
          (compiledRuleView (withCompiledIndexes s true)) ctor args.length
        =
      premiseFreeRulesForHeadArityRaw (withCompiledIndexes s false) ctor args.length := by
    simpa [withCompiledIndexes, compiledRuleView, premiseFreeRulesForHeadArityRaw] using
      (premiseFreeRulesForHeadArity_index_eq_raw_of_compiledRules_consistent
        (s := s) (ctor := ctor) (arity := args.length) hCompiled)
  have hIndexCollect :
      Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity
          (compiledRuleView (withCompiledIndexes s true)) ctor args.length
        =
      collectPremiseFreeRulesForHeadArity
        ctor args.length (withCompiledIndexes s false).bundle.language.rewrites := by
    simpa [premiseFreeRulesForHeadArityRaw] using hIndexRaw
  have hContrib :=
    hasMultipleRootCandidates_congr
      (.apply ctor args) hIndexCollect
  calc
    hasMultipleRootRuleChoices (withCompiledIndexes s true) (.apply ctor args)
        =
      hasMultipleRootCandidates (.apply ctor args)
        (Algorithms.MeTTa.Simple.Backend.CompiledBundle.premiseFreeRulesForHeadArity
          (compiledRuleView (withCompiledIndexes s true)) ctor args.length) := by
            simpa using
              (hasMultipleRootRuleChoices_apply_uses_index_when_enabled
                (s := withCompiledIndexes s true) (ctor := ctor) (args := args) rfl)
    _ =
      hasMultipleRootCandidates (.apply ctor args)
        (collectPremiseFreeRulesForHeadArity
          ctor args.length (withCompiledIndexes s false).bundle.language.rewrites) := hContrib
    _ =
      hasMultipleRootRuleChoices (withCompiledIndexes s false) (.apply ctor args) := by
            simpa using
              (hasMultipleRootRuleChoices_apply_uses_raw_when_disabled
                (s := withCompiledIndexes s false) (ctor := ctor) (args := args) rfl).symm

theorem hasMultipleRootRuleChoices_enabled_eq_disabled_of_compiledRules_consistent
    (s : Session) (term : Pattern)
    (hCompiled : s.compiledRules = compileRulesFromBundle s.bundle) :
    hasMultipleRootRuleChoices (withCompiledIndexes s true) term =
      hasMultipleRootRuleChoices (withCompiledIndexes s false) term := by
  cases term with
  | fvar x =>
      simp [hasMultipleRootRuleChoices,
        Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices]
  | bvar n =>
      simp [hasMultipleRootRuleChoices,
        Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices]
  | apply ctor args =>
      simpa using
        hasMultipleRootRuleChoices_apply_enabled_eq_disabled_of_compiledRules_consistent
          (s := s) (ctor := ctor) (args := args) hCompiled
  | lambda body =>
      simp [hasMultipleRootRuleChoices,
        Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices]
  | multiLambda n body =>
      simp [hasMultipleRootRuleChoices,
        Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices]
  | subst body repl =>
      simp [hasMultipleRootRuleChoices,
        Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices]
  | collection ct elems rest =>
      simp [hasMultipleRootRuleChoices,
        Algorithms.MeTTa.Simple.Backend.SessionDeterministic.hasMultipleRootRuleChoices]

theorem hasMultipleRootRuleChoices_eq_raw_of_compiledRules_consistent
    (s : Session) (term : Pattern)
    (hCompiled : s.compiledRules = compileRulesFromBundle s.bundle) :
    hasMultipleRootRuleChoices s term =
      hasMultipleRootRuleChoices (withCompiledIndexes s false) term := by
  have hSelf : s = withCompiledIndexes s s.useCompiledIndexes := by
    cases s <;> rfl
  cases hUse : s.useCompiledIndexes with
  | false =>
      have hFalse : s = withCompiledIndexes s false := by
        simpa [hUse] using hSelf
      rw [hFalse]
      simp [withCompiledIndexes]
  | true =>
      have hTrue : s = withCompiledIndexes s true := by
        simpa [hUse] using hSelf
      rw [hTrue]
      simpa using
        hasMultipleRootRuleChoices_enabled_eq_disabled_of_compiledRules_consistent
          (s := s) (term := term) hCompiled

private def acceptUnchangedDeterministic : Pattern → Bool :=
  Algorithms.MeTTa.Simple.Backend.SessionDeterministic.acceptUnchangedDeterministic

def optimizedBackendInterface : Algorithms.MeTTa.Simple.Backend.OptimizedEval.Interface Session := {
  maxNodes := fun s => s.maxNodes
  shouldUseDeterministicInStrict :=
    Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy.shouldUseDeterministicInStrict
  hasDeterministicBlockingRewriteBodies := hasDeterministicBlockingRewriteBodies
  hasMultipleRootRuleChoices := hasMultipleRootRuleChoices
  evalDeterministicCore := evalDeterministicCore
  evalWithStateCore := referenceEvalWithStateCore
  isResolvedDeterministicResult :=
    Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy.isResolvedDeterministicResult
  acceptUnchangedDeterministic := acceptUnchangedDeterministic
}

def evalWithState (s : Session) (term : Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState optimizedBackendInterface s term

theorem evalWithState_eq_optimizedBackend
    (s : Session) (term : Pattern) :
    evalWithState s term =
      Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
        optimizedBackendInterface s term := by
  rfl

theorem optimizedBackendInterface_evalWithStateCore_eq_reference
    (s : Session) (term : Pattern) :
    optimizedBackendInterface.evalWithStateCore s term =
      referenceEvalWithStateCore s term := by
  rfl

theorem evalWithState_eq_reference_of_guard_failure
    (s : Session) (term : Pattern)
    (hFail :
      optimizedBackendInterface.shouldUseDeterministicInStrict term = false ∨
      optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = true ∨
      optimizedBackendInterface.hasMultipleRootRuleChoices s term = true ∨
      optimizedBackendInterface.isResolvedDeterministicResult
        ((optimizedBackendInterface.evalDeterministicCore s
          (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2) = false ∨
      (((optimizedBackendInterface.evalDeterministicCore s
          (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2 != term) ||
        optimizedBackendInterface.acceptUnchangedDeterministic term) = false) :
    evalWithState s term = optimizedBackendInterface.evalWithStateCore s term := by
  simpa [evalWithState_eq_optimizedBackend] using
    Algorithms.MeTTa.Simple.Backend.OptimizedRefinement.evalWithState_eq_reference_of_guard_failure
      (I := optimizedBackendInterface) (s := s) (term := term) hFail

theorem evalWithState_eq_reference_of_deterministic_agreement
    (hAgree :
      ∀ (s : Session) (term : Pattern),
        optimizedBackendInterface.shouldUseDeterministicInStrict term = true →
        optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false →
        optimizedBackendInterface.hasMultipleRootRuleChoices s term = false →
        optimizedBackendInterface.isResolvedDeterministicResult
          ((optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2) = true →
        (((optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2 != term) ||
          optimizedBackendInterface.acceptUnchangedDeterministic term) = true →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          optimizedBackendInterface s term =
        optimizedBackendInterface.evalWithStateCore s term)
    (s : Session) (term : Pattern) :
    evalWithState s term = optimizedBackendInterface.evalWithStateCore s term := by
  simpa [evalWithState_eq_optimizedBackend] using
    Algorithms.MeTTa.Simple.Backend.OptimizedRefinement.evalWithState_eq_reference_of_deterministic_agreement
      (I := optimizedBackendInterface) hAgree s term

theorem evalWithState_eq_reference_of_deterministic_agreement_raw_guard
    (s : Session) (term : Pattern)
    (hs : CompiledConsistent s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        optimizedBackendInterface.shouldUseDeterministicInStrict term = true →
        optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false →
        optimizedBackendInterface.hasMultipleRootRuleChoices
          (withCompiledIndexes s false) term = false →
        optimizedBackendInterface.isResolvedDeterministicResult
          ((optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2) = true →
        (((optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2 != term) ||
        optimizedBackendInterface.acceptUnchangedDeterministic term) = true →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          optimizedBackendInterface s term =
        optimizedBackendInterface.evalWithStateCore s term)
    :
    evalWithState s term = optimizedBackendInterface.evalWithStateCore s term := by
  by_cases hStrict : optimizedBackendInterface.shouldUseDeterministicInStrict term = true
  · by_cases hBlocked : optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false
    · by_cases hMulti : optimizedBackendInterface.hasMultipleRootRuleChoices s term = false
      · by_cases hResolved :
          optimizedBackendInterface.isResolvedDeterministicResult
            ((optimizedBackendInterface.evalDeterministicCore s
              (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2) = true
        · by_cases hAccept :
            (((optimizedBackendInterface.evalDeterministicCore s
                (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2 != term) ||
              optimizedBackendInterface.acceptUnchangedDeterministic term) = true
          · have hEqRaw :
                optimizedBackendInterface.hasMultipleRootRuleChoices s term =
                  optimizedBackendInterface.hasMultipleRootRuleChoices
                    (withCompiledIndexes s false) term :=
              hasMultipleRootRuleChoices_eq_raw_of_compiledRules_consistent
                (s := s) (term := term) hs
            have hMultiRaw :
                optimizedBackendInterface.hasMultipleRootRuleChoices
                  (withCompiledIndexes s false) term = false := by
              simpa [hMulti] using hEqRaw
            exact hAgreeRaw s term hStrict hBlocked hMultiRaw hResolved hAccept
          · have hAcceptFalse :
                (((optimizedBackendInterface.evalDeterministicCore s
                    (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2 != term) ||
                  optimizedBackendInterface.acceptUnchangedDeterministic term) = false := by
                cases hA :
                  (((optimizedBackendInterface.evalDeterministicCore s
                      (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2 != term) ||
                    optimizedBackendInterface.acceptUnchangedDeterministic term) <;>
                  simp [hA] at hAccept ⊢
            exact evalWithState_eq_reference_of_guard_failure s term <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr hAcceptFalse
        · have hResolvedFalse :
              optimizedBackendInterface.isResolvedDeterministicResult
                ((optimizedBackendInterface.evalDeterministicCore s
                  (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2) = false := by
              cases hR :
                optimizedBackendInterface.isResolvedDeterministicResult
                  ((optimizedBackendInterface.evalDeterministicCore s
                    (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2) <;>
                simp [hR] at hResolved ⊢
          exact evalWithState_eq_reference_of_guard_failure s term <|
            Or.inr <| Or.inr <| Or.inr <| Or.inl hResolvedFalse
      · have hMultiTrue :
            optimizedBackendInterface.hasMultipleRootRuleChoices s term = true := by
          cases hM : optimizedBackendInterface.hasMultipleRootRuleChoices s term <;>
            simp [hM] at hMulti ⊢
        exact evalWithState_eq_reference_of_guard_failure s term <|
          Or.inr <| Or.inr <| Or.inl hMultiTrue
    · have hBlockedTrue :
          optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = true := by
        cases hB : optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s <;>
          simp [hB] at hBlocked ⊢
      exact evalWithState_eq_reference_of_guard_failure s term <|
        Or.inr <| Or.inl hBlockedTrue
  · have hStrictFalse :
        optimizedBackendInterface.shouldUseDeterministicInStrict term = false := by
      cases hS : optimizedBackendInterface.shouldUseDeterministicInStrict term <;>
        simp [hS] at hStrict ⊢
    exact evalWithState_eq_reference_of_guard_failure s term <| Or.inl hStrictFalse

theorem compiledConsistent_evalWithState_of_reference_and_deterministic_agreement
    (hCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (optimizedBackendInterface.evalWithStateCore s term).1)
    (s : Session) (term : Pattern)
    (hs : CompiledConsistent s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        optimizedBackendInterface.shouldUseDeterministicInStrict term = true →
        optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false →
        optimizedBackendInterface.hasMultipleRootRuleChoices
          (withCompiledIndexes s false) term = false →
        optimizedBackendInterface.isResolvedDeterministicResult
          ((optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2) = true →
        (((optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2 != term) ||
        optimizedBackendInterface.acceptUnchangedDeterministic term) = true →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          optimizedBackendInterface s term =
        optimizedBackendInterface.evalWithStateCore s term)
    :
    CompiledConsistent (evalWithState s term).1 := by
  have hEq :
      evalWithState s term = optimizedBackendInterface.evalWithStateCore s term :=
    evalWithState_eq_reference_of_deterministic_agreement_raw_guard
      (s := s) (term := term) hs hAgreeRaw
  simpa [hEq] using hCorePres s term hs

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

private partial def containsQuoteHead : Pattern → Bool
  | .fvar _ => false
  | .bvar _ => false
  | .apply ctor args =>
      ctor == "quote" || args.any containsQuoteHead
  | .lambda body => containsQuoteHead body
  | .multiLambda _ body => containsQuoteHead body
  | .subst body repl => containsQuoteHead body || containsQuoteHead repl
  | .collection _ elems _ => elems.any containsQuoteHead

private def assertionSemanticsInterface :
    Algorithms.MeTTa.Simple.Semantics.Assertions.Interface Session := {
  eval := evalWithState
  normalizeStrictValue := fun s p =>
    if containsQuoteHead p then
      (s, p)
    else
      let (s1, out) := evalWithState s (.apply "reduce" [.apply "quote" [p]])
      (s1, out.headD p)
  noteEval := noteEval
  withMessage := withMessage
  noteError := noteError
  renderPattern := renderPattern
  trueAtom := trueAtom
  falseAtom := falseAtom
}

private theorem assertionSemanticsInterface_preservation
    (hEvalPres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithState s term).1) :
    Algorithms.MeTTa.Simple.Semantics.Assertions.Preservation
      assertionSemanticsInterface CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    normalizeStrictValue_preserves := ?_,
    noteEval_preserves := ?_,
    withMessage_preserves := ?_,
    noteError_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (evalWithState s term).1 := hEvalPres s term hs
    have hState : (evalWithState s term).1 = s' := by
      simpa [assertionSemanticsInterface] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s term s' out hNorm hs
    by_cases hQuote : containsQuoteHead term
    · simp [assertionSemanticsInterface, hQuote] at hNorm
      rcases hNorm with ⟨rfl, rfl⟩
      simpa using hs
    · simp [assertionSemanticsInterface, hQuote] at hNorm
      have hPres :
          CompiledConsistent
            (evalWithState s (.apply "reduce" [.apply "quote" [term]])).1 :=
        hEvalPres s (.apply "reduce" [.apply "quote" [term]]) hs
      have hState :
          (evalWithState s (.apply "reduce" [.apply "quote" [term]])).1 = s' := by
        exact hNorm.1
      simpa [hState] using hPres
  · intro s hs
    exact compiledConsistent_noteEval s hs
  · intro s msg hs
    exact compiledConsistent_withMessage s msg hs
  · intro s msg hs
    exact compiledConsistent_noteError s msg hs

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
      let eqFact := .apply "=" [lhs, rhs]
      let row : RelationTuple := { relation := "selfFact", tuple := [eqFact] }
      let env' := addRelationTuple s.bundle.relationEnv row
      let bundle' : SpecBundle := {
        s.bundle with
          language := { s.bundle.language with rewrites := rules' }
          relationEnv := env'
      }
      let s0 := noteApplied (withBundleCompiled s bundle')
      let s' := withMessage s0 s!"loaded rule {rule.name} and added selfFact/1 equation fact"
      (s', [])
  | .defineType lhs rhs =>
      let p := .apply ":" [lhs, rhs]
      let row : RelationTuple := { relation := "selfFact", tuple := [p] }
      let env' := addRelationTuple s.bundle.relationEnv row
      let bundle' : SpecBundle := { s.bundle with relationEnv := env' }
      let s0 := noteApplied (withBundleCompiled s bundle')
      let s' := withMessage s0 "added type fact to relation selfFact/1"
      (s', [])
  | .fact p =>
      let row : RelationTuple := { relation := "selfFact", tuple := [p] }
      let env' := addRelationTuple s.bundle.relationEnv row
      let bundle' : SpecBundle := { s.bundle with relationEnv := env' }
      let s0 := noteApplied (withBundleCompiled s bundle')
      let s' := withMessage s0 "added fact to relation selfFact/1"
      (s', [])
  | .eval term =>
      match Algorithms.MeTTa.Simple.Semantics.Assertions.evalAssertionCommand?
          assertionSemanticsInterface s.assertionPolicy s term with
      | some (s0, out) =>
          let s' := noteApplied s0
          (s', out)
      | none =>
          let (sEval, out) := evalWithState s term
          let s0 := noteApplied (noteEval sEval)
          let s' := withMessage s0 s!"query produced {out.length} result(s)"
          (s', out)
  | .relationFact rel tuple =>
      let row : RelationTuple := { relation := rel, tuple := tuple }
      let env' := addRelationTuple s.bundle.relationEnv row
      let bundle' : SpecBundle := { s.bundle with relationEnv := env' }
      let s0 := noteApplied (withBundleCompiled s bundle')
      let s' := withMessage s0 s!"added relation fact {rel}/{tuple.length}"
      (s', [])
  | .builtinFact rel tuple =>
      let row : RelationTuple := { relation := rel, tuple := tuple }
      let builtins' := addBuiltinTuple s.bundle.builtins row
      let bundle' : SpecBundle := { s.bundle with builtins := builtins' }
      let s0 := noteApplied (withBundleCompiled s bundle')
      let s' := withMessage s0 s!"added builtin fact {rel}/{tuple.length}"
      (s', [])
  | .setFuel n =>
      let policy' : RuntimePolicy := { s.bundle.policy with maxFuel := n }
      let bundle' : SpecBundle := { s.bundle with policy := policy' }
      let s' : Session :=
        { (withBundleCompiled s bundle') with
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
      let s0 := noteApplied (withBundleCompiled s bundle')
      let s' := withMessage s0 s!"lowered directive {head} to selfFact/1"
      (s', [])

theorem compiledConsistent_applyStmt_eval
    (hEvalPres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithState s term).1)
    (s : Session) (term : Pattern)
    (hs : CompiledConsistent s) :
    CompiledConsistent (applyStmt s (.eval term)).1 := by
  by_cases hCmd :
      Algorithms.MeTTa.Simple.Semantics.Assertions.evalAssertionCommand?
        assertionSemanticsInterface s.assertionPolicy s term = none
  · have hsEval : CompiledConsistent (evalWithState s term).1 := hEvalPres s term hs
    have hEval1 : CompiledConsistent (noteEval (evalWithState s term).1) :=
      compiledConsistent_noteEval _ hsEval
    have hEval2 : CompiledConsistent (noteApplied (noteEval (evalWithState s term).1)) :=
      compiledConsistent_noteApplied _ hEval1
    have hEval3 :
        CompiledConsistent
          (withMessage
            (noteApplied (noteEval (evalWithState s term).1))
            s!"query produced {(evalWithState s term).2.length} result(s)") :=
      compiledConsistent_withMessage _ _ hEval2
    simpa [applyStmt, hCmd] using hEval3
  · cases hRes :
        Algorithms.MeTTa.Simple.Semantics.Assertions.evalAssertionCommand?
          assertionSemanticsInterface s.assertionPolicy s term with
    | none =>
        contradiction
    | some res =>
        cases res with
        | mk s0 out =>
            have hs0 : CompiledConsistent s0 := by
              simpa [hRes] using
                (Algorithms.MeTTa.Simple.Semantics.Assertions.evalAssertionCommand?_preserves
                  assertionSemanticsInterface CompiledConsistent
                  (assertionSemanticsInterface_preservation hEvalPres)
                  s.assertionPolicy s term hs)
            have hApplied : CompiledConsistent (noteApplied s0) :=
              compiledConsistent_noteApplied s0 hs0
            simpa [applyStmt, hRes] using hApplied

theorem compiledConsistent_applyStmt_eval_of_reference_and_deterministic_agreement
    (hCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (optimizedBackendInterface.evalWithStateCore s term).1)
    (s : Session) (term : Pattern)
    (hs : CompiledConsistent s)
    (hAgreeRaw :
      ∀ (s : Session) (term : Pattern),
        optimizedBackendInterface.shouldUseDeterministicInStrict term = true →
        optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = false →
        optimizedBackendInterface.hasMultipleRootRuleChoices
          (withCompiledIndexes s false) term = false →
        optimizedBackendInterface.isResolvedDeterministicResult
          ((optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2) = true →
        (((optimizedBackendInterface.evalDeterministicCore s
            (Nat.max 4096 (optimizedBackendInterface.maxNodes s)) term).2 != term) ||
        optimizedBackendInterface.acceptUnchangedDeterministic term) = true →
        Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
          optimizedBackendInterface s term =
        optimizedBackendInterface.evalWithStateCore s term)
    :
    CompiledConsistent (applyStmt s (.eval term)).1 := by
  exact
    compiledConsistent_applyStmt_eval
      (fun s term hs =>
        compiledConsistent_evalWithState_of_reference_and_deterministic_agreement
          hCorePres s term hs hAgreeRaw)
      s term hs

def evalExpr (s : Session) (input : String) : Except String (Session × List Pattern) := do
  let expr ← Algorithms.MeTTa.Simple.Parser.parseExpr input
  let (s1, out) := evalWithState s expr
  let s' := withMessage (noteEval s1) s!"evalExpr produced {out.length} result(s)"
  pure (s', out)

mutual
  private partial def runImportIfNeeded (s : Session) (stmt : SyntaxStmt) : Session :=
    match Algorithms.MeTTa.Simple.Semantics.ImportOps.moduleNameOfStmt? stmt with
    | none => s
    | some modName =>
        let loadedKey := Algorithms.MeTTa.Simple.Semantics.ImportOps.canonicalModuleKey modName
        if s.loadedModules.contains loadedKey then
          s
        else
          match Algorithms.MeTTa.Simple.Semantics.ImportOps.lookupModuleSource? s.moduleSources modName with
          | none => s
          | some text =>
              let s0 : Session := { s with loadedModules := loadedKey :: s.loadedModules }
              match parseProgramWith s0.syntaxSpec text with
              | .ok program =>
                  let (s1, _outs) := runProgramAux s0 program
                  s1
              | .error err =>
                  noteError s0 s!"import parse failed for {modName}: {err}"

  private partial def runParsed (s : Session) (lineNo : Nat) (stmt : SyntaxStmt) :
      Session × Option (Nat × List Pattern) :=
    let s1 := noteParsed s
    let (s2, out) := applyStmt s1 stmt
    let s3 := runImportIfNeeded s2 stmt
    if out.isEmpty then
      (s3, none)
    else
      (s3, some (lineNo, out))

  private partial def runProgramAux (s : Session) :
      List (Nat × SyntaxStmt) → Session × List (Nat × List Pattern)
    | [] => (s, [])
    | (lineNo, stmt) :: rest =>
        let (s1, out?) := runParsed s lineNo stmt
        let (s2, outs) := runProgramAux s1 rest
        match out? with
        | none => (s2, outs)
        | some out => (s2, out :: outs)
end

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
