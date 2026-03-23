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

/-! DEPRECATED (2026-03-22): 80 partial defs make this unverifiable.
Replaced by Algorithms.MeTTa.Eval/ (fuel-indexed, 0 partial def, 0 sorry).
Preserved for reference and as a test oracle. Not built by default. -/

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
  coreBuiltinsUnmodified : Bool := true
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

private def patternHeight : Pattern → Nat
  | .fvar _ => 1
  | .bvar _ => 1
  | .apply _ args =>
      1 + args.foldl (fun h a => Nat.max h (patternHeight a)) 0
  | .lambda body =>
      1 + patternHeight body
  | .multiLambda _ body =>
      1 + patternHeight body
  | .subst body repl =>
      1 + Nat.max (patternHeight body) (patternHeight repl)
  | .collection _ elems _ =>
      1 + elems.foldl (fun h a => Nat.max h (patternHeight a)) 0

private def bindingVarBudget (bs : Bindings) : Nat :=
  (bs.map (·.1)).eraseDups.length

private def applyBindingsCompatFuel
    (bs : Bindings) : Nat → List String → Pattern → Pattern
  | 0, _visited, p => p
  | fuel + 1, visited, p =>
      match p with
      | .fvar x =>
          if visited.contains x then
            .fvar x
          else
            match bindingLookup bs x with
            | some (.fvar y) =>
                if y == x then
                  .fvar x
                else
                  applyBindingsCompatFuel bs fuel (x :: visited) (.fvar y)
            | some v =>
                applyBindingsCompatFuel bs fuel (x :: visited) v
            | none => .fvar x
      | .apply ctor [] =>
          match dollarHeadVarName? (.apply ctor []) with
          | some x =>
              if visited.contains x then
                .apply ctor []
              else
                match bindingLookup bs x with
                | some v =>
                    applyBindingsCompatFuel bs fuel (x :: visited) v
                | none => .apply ctor []
          | none => .apply ctor []
      | .apply "|->" [params, body] =>
          let bound := lambdaParamNamesCompat params
          let bs' := bs.filter (fun b => !(bound.contains b.1))
          .apply "|->" [params, applyBindingsCompatFuel bs' fuel visited body]
      | .apply ctor args =>
          let args' := args.map (fun a => applyBindingsCompatFuel bs fuel visited a)
          match dollarHeadVarName? (.apply ctor []) with
          | some x =>
              if visited.contains x then
                .apply ctor args'
              else
                match bindingLookup bs x with
                | some (.apply c []) => .apply c args'
                | some v =>
                    let v' := applyBindingsCompatFuel bs fuel (x :: visited) v
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
          .lambda (applyBindingsCompatFuel bs fuel visited body)
      | .multiLambda n body =>
          .multiLambda n (applyBindingsCompatFuel bs fuel visited body)
      | .subst body repl =>
          .subst
            (applyBindingsCompatFuel bs fuel visited body)
            (applyBindingsCompatFuel bs fuel visited repl)
      | .collection ct elems rest =>
          .collection ct (elems.map (fun a => applyBindingsCompatFuel bs fuel visited a)) rest
      | .bvar n => .bvar n

private def applyBindingsCompat (bs : Bindings) : Pattern → Pattern :=
  fun p =>
    let fuel := bindingVarBudget bs + patternHeight p + 1
    applyBindingsCompatFuel bs fuel [] p

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

-- ─── Transparent (non-partial) versions of intrinsicStep / intrinsicReduceArgs ──
-- These are identical in behavior but provably terminating via sizeOf.
-- Used in proof-mode to avoid the opacity of the partial def mutual block above.

mutual
  private def intrinsicReduceArgsT (s : Session) : List Pattern → List (List Pattern)
    | [] => []
    | arg :: rest =>
        let headRed := intrinsicStepT s arg
        if !headRed.isEmpty then
          headRed.map (fun arg' => arg' :: rest)
        else
          (intrinsicReduceArgsT s rest).map (fun rest' => arg :: rest')
  termination_by args => sizeOf args
  decreasing_by
    · simp_wf; omega
    · simp_wf; omega

  private def intrinsicStepT (s : Session) : Pattern → List Pattern
    | .apply ctor args =>
        if reduceArgsFirst ctor then
          let reducedArgs := intrinsicReduceArgsT s args
          if !reducedArgs.isEmpty then
            reducedArgs.map (fun args' => .apply ctor args')
          else
            intrinsicDirect s ctor args
        else
          let direct := intrinsicDirect s ctor args
          if !direct.isEmpty then
            direct
          else
            (intrinsicReduceArgsT s args).map (fun args' => .apply ctor args')
    | _ => []
  termination_by term => sizeOf term
  decreasing_by all_goals simp_wf; omega
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
  let intrinsic := intrinsicStepT s term
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

-- ─── Step result-shape lemmas ────────────────────────────────────────────────

/-- When translateCall, compatRewriteStep, and rewriteWithContext all return [],
    `step` reduces to just `intrinsicStepT`. -/
theorem step_eq_intrinsicStepT_of_no_external_reducts
    (s : Session) (term : Pattern)
    (hT : Algorithms.MeTTa.Simple.Semantics.TranslatorOps.translateCall
            translatorInterface s s.translatorRuleHeads term = [])
    (hC : Algorithms.MeTTa.Simple.Semantics.Dispatch.compatRewriteStep
            compatRewriteInterface s term = [])
    (hG : SpecBundle.rewriteWithContext s.bundle term = []) :
    step s term = intrinsicStepT s term := by
  simp only [step, hT, hC, hG, List.isEmpty_nil, Bool.true_and, ite_true,
    List.append_nil]

/-- When args have no reductions (i.e., `intrinsicStepT` returns [] for each arg),
    `intrinsicReduceArgsT` returns []. -/
theorem intrinsicReduceArgsT_empty_of_irreducible_args
    (s : Session) (args : List Pattern)
    (hIrred : ∀ a ∈ args, intrinsicStepT s a = []) :
    intrinsicReduceArgsT s args = [] := by
  induction args with
  | nil => simp [intrinsicReduceArgsT]
  | cons hd tl ih =>
      simp [intrinsicReduceArgsT]
      have hhd := hIrred hd List.mem_cons_self
      simp [hhd]
      exact ih (fun a ha => hIrred a (List.mem_cons_of_mem hd ha))

/-- For a `reduceArgsFirst` head with irreducible args, `intrinsicStepT` returns
    exactly `intrinsicDirect`. -/
theorem intrinsicStepT_reduceFirst_irreducible
    (s : Session) (ctor : String) (args : List Pattern)
    (hRedFirst : reduceArgsFirst ctor = true)
    (hIrred : ∀ a ∈ args, intrinsicStepT s a = []) :
    intrinsicStepT s (.apply ctor args) = intrinsicDirect s ctor args := by
  simp [intrinsicStepT, hRedFirst]
  have hEmpty := intrinsicReduceArgsT_empty_of_irreducible_args s args hIrred
  simp [hEmpty]

/-- For a non-`reduceArgsFirst` head, if `intrinsicDirect` returns a non-empty list,
    `intrinsicStepT` returns that list. -/
theorem intrinsicStepT_direct_nonempty
    (s : Session) (ctor : String) (args : List Pattern)
    (hNotRedFirst : reduceArgsFirst ctor = false)
    (hDirect : (intrinsicDirect s ctor args).isEmpty = false) :
    intrinsicStepT s (.apply ctor args) = intrinsicDirect s ctor args := by
  simp [intrinsicStepT, hNotRedFirst, hDirect]

-- ─── Public proof API for DeterministicBridge layer ──────────────────────────
-- Thin wrappers exposing private functions needed by the bridge proofs.
-- The bridge layer (Backend/DeterministicBridge/) imports Session and uses these.
-- NOTE: detEvalInterface and detEvalInterface_eq_standalone are placed later in
-- this file (after evalWithStateCoreN) because they reference forward declarations.

/-- The `translateCall` component of `step`, exposed for bridge proofs. -/
def stepTranslateCall (s : Session) (term : Pattern) : List Pattern :=
  Algorithms.MeTTa.Simple.Semantics.TranslatorOps.translateCall
    translatorInterface s s.translatorRuleHeads term

/-- The `compatRewriteStep` component of `step`, exposed for bridge proofs. -/
def stepCompatRewrite (s : Session) (term : Pattern) : List Pattern :=
  Algorithms.MeTTa.Simple.Semantics.Dispatch.compatRewriteStep
    compatRewriteInterface s term

/-- The `rewriteWithContext` component of `step`, exposed for bridge proofs. -/
def stepGeneratedRewrite (s : Session) (term : Pattern) : List Pattern :=
  SpecBundle.rewriteWithContext s.bundle term

/-- Decomposition of `step` in terms of its public components. -/
theorem step_eq_components (s : Session) (term : Pattern) :
    step s term =
      let intrinsic := intrinsicStepT s term
      let translated := stepTranslateCall s term
      let compat := if translated.isEmpty then stepCompatRewrite s term else []
      let generated := if compat.isEmpty && translated.isEmpty then stepGeneratedRewrite s term else []
      let intrinsic' := if compat.isEmpty then intrinsic else []
      intrinsic' ++ translated ++ compat ++ generated := by
  rfl

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

private def evalTupleElemsWith
    (evalCore : Session → Pattern → Session × List Pattern)
    (sess : Session) :
    List Pattern → Session × List (List Pattern)
  | [] => (sess, [[]])
  | e :: rest =>
      let (sessHead, headOut0) := evalCore sess e
      let heads := if headOut0.isEmpty then [e] else headOut0
      let (sessTail, tails) := evalTupleElemsWith evalCore sessHead rest
      let combos :=
        heads.foldr
          (fun h acc => (tails.map (fun t => h :: t)) ++ acc)
          []
      (sessTail, combos)

private def evalTupleFallbackWith
    (isRuleCallableHead : Session → String → Bool)
    (sess : Session) (xs : List Pattern) : Pattern :=
  match xs with
  | [] => .apply "()" []
  | h :: tl =>
      match h with
      | .apply ctor [] =>
          if isRuleCallableHead sess ctor then
            .apply ctor tl
          else
            .apply "Expr" xs
      | _ => .apply "Expr" xs

private def evalTupleBuildStepWith
    (evalCallableApply : Session → Pattern → List Pattern → Session × List Pattern)
    (isRuleCallableHead : Session → String → Bool)
    (acc : Session × List Pattern) (xs : List Pattern) : Session × List Pattern :=
  let sess := acc.1
  let outAcc := acc.2
  let fallback := evalTupleFallbackWith isRuleCallableHead sess xs
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

private def evalTupleBuiltWith
    (evalCallableApply : Session → Pattern → List Pattern → Session × List Pattern)
    (isRuleCallableHead : Session → String → Bool)
    (s : Session) (combos : List (List Pattern)) : Session × List Pattern :=
  combos.foldl (evalTupleBuildStepWith evalCallableApply isRuleCallableHead) (s, [])

private def evalTupleIntrinsicWith
    (evalCore : Session → Pattern → Session × List Pattern)
    (evalCallableApply : Session → Pattern → List Pattern → Session × List Pattern)
    (isRuleCallableHead : Session → String → Bool)
    (s : Session) (elems : List Pattern) : Session × List Pattern :=
  let (s1, combos) := evalTupleElemsWith evalCore s elems
  evalTupleBuiltWith evalCallableApply isRuleCallableHead s1 combos

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

private def spaceOpsInterfaceWithEval
    (evalFn : Session → Pattern → Session × List Pattern)
    (s : Session) : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
  bundle := fun s => s.bundle
  rewrites := fun s => s.bundle.language.rewrites
  setBundle := withBundleCompiled
  eval := evalFn
  applyBindings := applyBindingsCompat
  normalizePattern := normalizeDollarVars
  normalizeForSpaceMatch := normalizeSpaceMatchPattern s
  matchPattern := matchPatternMeTTa
  dedupPatterns := dedupPatternList
}

private def intrinsicGetAtomsResultWithEval
    (evalFn : Session → Pattern → Session × List Pattern)
    (s : Session) (space : Pattern) : Option (Session × List Pattern) :=
  let (s', out) :=
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms
      (spaceOpsInterfaceWithEval evalFn s) spacePolicy s space
  some (s', out)

private def intrinsicMatchResultWithEval
    (evalFn : Session → Pattern → Session × List Pattern)
    (s : Session) (space pat tmpl : Pattern) : Option (Session × List Pattern) :=
  let (s', out) :=
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
      (spaceOpsInterfaceWithEval evalFn s) spacePolicy s space pat tmpl
  some (s', out)

private theorem intrinsicGetAtomsResultWithEval_eval_irrelevant
    (evalFn evalFn' : Session → Pattern → Session × List Pattern)
    (s : Session) (space : Pattern) :
    intrinsicGetAtomsResultWithEval evalFn s space =
      intrinsicGetAtomsResultWithEval evalFn' s space := by
  unfold intrinsicGetAtomsResultWithEval spaceOpsInterfaceWithEval
  simp [Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms,
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.factsForSpace]

/-- `get-atoms` / `get-atoms!` intrinsic evaluation preserves the session:
    the result is `some (s, facts)` for some `facts`. -/
private theorem intrinsicGetAtomsResultWithEval_state_eq
    (evalFn : Session → Pattern → Session × List Pattern)
    (s : Session) (space : Pattern) :
    ∃ facts, intrinsicGetAtomsResultWithEval evalFn s space = some (s, facts) := by
  unfold intrinsicGetAtomsResultWithEval spaceOpsInterfaceWithEval
  simp [Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms]

mutual
  private partial def evalWithStateCore (s : Session) (term : Pattern) : Session × List Pattern :=
    let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
      maxNodes := fun s => s.maxNodes
      maxSteps := fun s => s.maxSteps
      runNestedEffects := runNestedEffects
      intrinsicStateful := intrinsicStatefulCore
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
      evalTupleIntrinsic := evalTupleIntrinsicWith evalWithStateCore evalCallableApply isRuleCallableHead
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
      intrinsicStateful := intrinsicStatefulCore
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
      intrinsicStateful := intrinsicStatefulCore
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
              match intrinsicStatefulCore s cond with
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
            match intrinsicStatefulCore sess key with
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
    match intrinsicStatefulCore s expr with
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

  partial def intrinsicStatefulCore (s : Session)
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
                  match intrinsicStatefulCore sess expr with
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
        intrinsicGetAtomsResultWithEval evalWithStateCore s space
    | .apply "get-atoms!" [space] =>
        intrinsicGetAtomsResultWithEval evalWithStateCore s space
    | .apply "match" [space, pat, tmpl] =>
        intrinsicMatchResultWithEval evalWithStateCore s space pat tmpl
    | .apply "match" [pat, tmpl] =>
        intrinsicMatchResultWithEval evalWithStateCore s selfSpaceAtom pat tmpl
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
          match intrinsicStatefulCore s1 x1 with
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
        let (s', out0) :=
          evalTupleIntrinsicWith evalWithStateCore evalCallableApply isRuleCallableHead s elems
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
                      match intrinsicStatefulCore s a with
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
      intrinsicStateful := intrinsicStatefulCore
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
      intrinsicStateful := intrinsicStatefulCore
      isEagerCallableHead := isEagerCallableHead
      step := step
      enqueueNext := enqueueNext
      insertUnique := insertUnique
      dedupPatterns := dedupPatterns
    }
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
      iface s isRoot _parentCallable term

end

-- ─── Public wrappers for private helpers (used by DeterministicBridge) ───────
-- These expose private functions needed by the bridge proofs while keeping
-- the originals private to Session.lean.

/-- Public wrapper for `intrinsicDirect`. -/
def intrinsicDirectPub (s : Session) (ctor : String) (args : List Pattern) : List Pattern :=
  intrinsicDirect s ctor args

/-- `intrinsicDirectPub` equals `filterMap` over the builtin relation table.
    Exposes the internal structure so bridge lemmas can reason about builtins. -/
theorem intrinsicDirectPub_eq_filterMap (s : Session) (ctor : String) (args : List Pattern) :
    intrinsicDirectPub s ctor args =
      (s.bundle.builtins.relation (intrinsicRelationName ctor) args).filterMap fun row =>
        match row with
        | [out] => some out
        | _ => none := by
  rfl

/-- `intrinsicDirectPub` length is bounded by the builtin relation table's row count. -/
theorem intrinsicDirectPub_length_le (s : Session) (ctor : String) (args : List Pattern) :
    (intrinsicDirectPub s ctor args).length ≤
      (s.bundle.builtins.relation (intrinsicRelationName ctor) args).length := by
  rw [intrinsicDirectPub_eq_filterMap]
  exact List.length_filterMap_le _ _

/-- Public wrapper for `builtinPartialMinArity?`. -/
def builtinPartialMinArityPub (ctor : String) : Option Nat :=
  builtinPartialMinArity? ctor

/-- Public wrapper for `firstRuleReduction?`. -/
def firstRuleReductionPub (s : Session) (term : Pattern) : Option Pattern :=
  firstRuleReduction? s term

/-- Public wrapper for `rewriteAritiesForHead`. -/
def rewriteAritiesForHeadPub (s : Session) (ctor : String) : List Nat :=
  rewriteAritiesForHead s ctor

/-- Public wrapper for `partialPattern`. -/
def partialPatternPub (ctor : String) (args : List Pattern) : Pattern :=
  partialPattern ctor args

/-- If `step s a = []` then `intrinsicStepT s a = []`.
    (intrinsicStepT is one component of step's concatenation.) -/
private theorem intrinsicStepT_nil_of_step_nil
    (s : Session) (a : Pattern) (hS : step s a = []) :
    intrinsicStepT s a = [] := by
  simp only [step] at hS
  -- hS : (intrinsic' ++ translated ++ compat_branch) ++ generated_branch = []
  rw [List.append_eq_nil_iff] at hS
  have ⟨h123, _h4⟩ := hS
  rw [List.append_eq_nil_iff] at h123
  have ⟨h12, h3⟩ := h123
  rw [List.append_eq_nil_iff] at h12
  have ⟨h1, h2⟩ := h12
  -- h2 : translated = []
  -- h3 : compat_branch = [] (i.e., if translated.isEmpty then compatRewrite else [] = [])
  -- h1 : intrinsic' = [] (i.e., if compat_branch.isEmpty then intrinsicStepT else [] = [])
  -- Since translated = [] (h2), translated.isEmpty = true, so compat_branch = compatRewrite
  -- Since compat_branch = [] (h3), compat_branch.isEmpty = true, so intrinsic' = intrinsicStepT
  -- Since intrinsic' = [] (h1), intrinsicStepT = []
  simp [h2, List.isEmpty] at h3
  simp [h2, h3, List.isEmpty] at h1
  exact h1

/-- Under strict conditions (no external reducts, args irreducible),
    `step` produces exactly `intrinsicDirectPub`.
    This is the key shape lemma for the DeterministicBridge. -/
theorem step_apply_eq_intrinsicDirectPub_of_strict
    (s : Session) (ctor : String) (argsV : List Pattern)
    (hT : stepTranslateCall s (.apply ctor argsV) = [])
    (hC : stepCompatRewrite s (.apply ctor argsV) = [])
    (hG : stepGeneratedRewrite s (.apply ctor argsV) = [])
    (hIrred : ∀ a ∈ argsV, step s a = []) :
    step s (.apply ctor argsV) = intrinsicDirectPub s ctor argsV := by
  -- step = intrinsic' ++ translated ++ compat ++ generated
  -- Under strict: translated=[], compat=[], generated=[]
  -- So step = intrinsicStepT (since compat=[])
  have hStep := step_eq_intrinsicStepT_of_no_external_reducts s (.apply ctor argsV) hT hC hG
  rw [hStep]
  -- Show args are intrinsicStepT-irreducible from step-irreducibility
  have hIrredT : ∀ a ∈ argsV, intrinsicStepT s a = [] := by
    intro a ha
    exact intrinsicStepT_nil_of_step_nil s a (hIrred a ha)
  -- intrinsicStepT with irreducible args = intrinsicDirect
  unfold intrinsicDirectPub
  by_cases hRed : reduceArgsFirst ctor = true
  · exact intrinsicStepT_reduceFirst_irreducible s ctor argsV hRed hIrredT
  · simp at hRed
    simp [intrinsicStepT, hRed]
    have hEmpty := intrinsicReduceArgsT_empty_of_irreducible_args s argsV hIrredT
    simp [hEmpty]

def intrinsicStateful (s : Session) (term : Pattern) :
    Option (Session × List Pattern) :=
  match term with
  | .apply "get-atoms" [space] =>
      intrinsicGetAtomsResultWithEval evalWithStateCore s space
  | .apply "get-atoms!" [space] =>
      intrinsicGetAtomsResultWithEval evalWithStateCore s space
  | .apply "match" [space, pat, tmpl] =>
      intrinsicMatchResultWithEval evalWithStateCore s space pat tmpl
  | .apply "match" [pat, tmpl] =>
      intrinsicMatchResultWithEval evalWithStateCore s selfSpaceAtom pat tmpl
  | _ =>
      intrinsicStatefulCore s term

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

-- referenceEvalWithStateCore is defined after the mutual fuel-indexed block (below).

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
  evalTupleIntrinsic := evalTupleIntrinsicWith evalWithStateCore evalCallableApply isRuleCallableHead
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

private def referenceEvalDeterministicCore (s : Session) (fuel : Nat)
    (term : Pattern) : Session × Pattern :=
  Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval
    deterministicEvalInterface s fuel term

def referenceProofFuel (s : Session) : Nat :=
  Nat.max 4096 s.maxNodes

-- ─── FuelResult: explicit fuel-exhaustion status ─────────────────────────────
-- Used to distinguish "computation completed within fuel" (.done) from
-- "fuel exhausted before completion" (.outOfFuel).
-- Useful as infrastructure for future fuel-adequacy bridging work.

/-- Tracks whether a fuel-indexed computation completed or ran out of fuel. -/
inductive FuelResult (α : Type) where
  | done (val : α)
  | outOfFuel
  deriving Repr, DecidableEq

namespace FuelResult

def bind {α β : Type} : FuelResult α → (α → FuelResult β) → FuelResult β
  | done a, f => f a
  | outOfFuel, _ => outOfFuel

def toOption {α : Type} : FuelResult α → Option α
  | done a => some a
  | outOfFuel => none

def map {α β : Type} (f : α → β) : FuelResult α → FuelResult β
  | done a => done (f a)
  | outOfFuel => outOfFuel

theorem toOption_done {α : Type} (a : α) : (done a).toOption = some a := rfl
theorem toOption_outOfFuel {α : Type} : (outOfFuel : FuelResult α).toOption = none := rfl

end FuelResult

instance : Monad FuelResult where
  pure := FuelResult.done
  bind := FuelResult.bind

-- ─── Parameterized deterministic interface builder ──────────────────────────
-- Extracted so that both the mutual N-kernel block and the public
-- optimizedBackendInterface share the same interface construction.
-- The only varying parts are evalCore and evalCallableApply (partial-def
-- vs fuel-indexed).

def mkDeterministicEvalInterface
    (evalCore : Session → Pattern → Session × List Pattern)
    (evalCallableApply : Session → Pattern → List Pattern → Session × List Pattern) :
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.Interface Session := {
  evalTupleIntrinsic := evalTupleIntrinsicWith evalCore evalCallableApply isRuleCallableHead
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

theorem mkDeterministicEvalInterface_eq_deterministicEvalInterface :
    mkDeterministicEvalInterface evalWithStateCore evalCallableApply =
      deterministicEvalInterface := by
  rfl

-- ─────────────────────────────────────────────────────────────────────────────

set_option maxHeartbeats 800000 in
mutual
  private def referenceRunNestedEffectsArgsN (fuel : Nat) (s : Session) (parentCallable : Bool)
      (args : List Pattern) (accRev : List Pattern) (changed : Bool) :
      Session × List Pattern × Bool :=
    let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
      maxNodes := fun s => s.maxNodes
      maxSteps := fun s => s.maxSteps
      runNestedEffects := fun s isRoot p term => referenceRunNestedEffectsN fuel s isRoot p term
      intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
      isEagerCallableHead := isEagerCallableHead
      step := step
      enqueueNext := enqueueNext
      insertUnique := insertUnique
      dedupPatterns := dedupPatterns
    }
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffectsArgs
      iface s parentCallable args accRev changed

  private def referenceRunNestedEffectsN (fuel : Nat) (s : Session) (isRoot parentCallable : Bool)
      (term : Pattern) : Session × Pattern × Bool :=
    let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
      maxNodes := fun s => s.maxNodes
      maxSteps := fun s => s.maxSteps
      runNestedEffects := fun s _isRoot _parentCallable term => (s, term, false)
      intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
      isEagerCallableHead := isEagerCallableHead
      step := step
      enqueueNext := enqueueNext
      insertUnique := insertUnique
      dedupPatterns := dedupPatterns
    }
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
      iface s isRoot parentCallable term

  private def referenceEvalWithStateCoreN : Nat → Session → Pattern → Session × List Pattern
    | 0, s, _term => (s, [])
    | fuel + 1, s, term =>
        let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
          maxNodes := fun s => s.maxNodes
          maxSteps := fun s => s.maxSteps
          runNestedEffects := fun s isRoot p term => referenceRunNestedEffectsN fuel s isRoot p term
          intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
          isEagerCallableHead := isEagerCallableHead
          step := step
          enqueueNext := enqueueNext
          insertUnique := insertUnique
          dedupPatterns := dedupPatterns
        }
        Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore iface s term

  private def referenceEvalForRuleEnumerationN : Nat → Session → Pattern → Session × List Pattern
    | 0, s, expr => (s, [expr])
    | fuel + 1, s, expr =>
        match referenceIntrinsicStatefulN fuel s expr with
        | some (s1, out) =>
            let out' := if out.isEmpty then [expr] else out
            (s1, out')
        | none =>
            let (s1, out0) := referenceEvalWithStateCoreN fuel s expr
            let out := if out0.isEmpty then [expr] else out0
            (s1, out)

  private def referenceEvalCallableApplyN : Nat → Session → Pattern → List Pattern → Session × List Pattern
    | 0, s, _callable, _args => (s, [])
    | fuel + 1, s, callable, args =>
        let iface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
          rewrites := fun s => s.bundle.language.rewrites
          premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
          eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          normalizePattern := normalizeDollarVars
          dedupBindings := dedupBindings
        }
        match callable with
        | .apply "partial" [base, bound] =>
            let boundArgs := tupleElems bound
            referenceEvalCallableApplyN fuel s base (boundArgs ++ args)
        | .apply "|->" [params, body] =>
            let names := lambdaParamNamesCompat params
            if names.length != args.length then
              (s, [])
            else
              let env : Bindings := List.zip names args
              let bodySub := applyBindingsCompat env body
              let (sEval, out0) := referenceEvalWithStateCoreN fuel s bodySub
              let (sEnum, extra) :=
                Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
                  iface sEval bodySub
              let out := if extra.isEmpty then out0 else extra
              Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
                iface sEnum bodySub out
        | .apply name [] =>
            let call := .apply name args
            let (sEval, out0) := referenceEvalWithStateCoreN fuel s call
            let (sEnum, extra) :=
              Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
                iface sEval call
            let out := if extra.isEmpty then out0 else extra
            Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
              iface sEnum call out
        | .apply name boundArgs =>
            referenceEvalCallableApplyN fuel s (.apply name []) (boundArgs ++ args)
        | .fvar name =>
            let call := .apply name args
            let (sEval, out0) := referenceEvalWithStateCoreN fuel s call
            let (sEnum, extra) :=
              Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
                iface sEval call
            let out := if extra.isEmpty then out0 else extra
            Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
              iface sEnum call out
        | _ =>
            (s, [])

  private def referenceIntrinsicApplyDispatchTailN
      (fuel : Nat)
      (dispatchIface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session)
      (s : Session) (ctor : String) (args : List Pattern) :
      Option (Session × List Pattern) :=
    let (sFH, fromHeads) :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        dispatchIface s (.apply ctor args)
    match fromHeads with
    | _ :: _ => some (sFH, fromHeads)
    | [] =>
        if Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
            dispatchIface s ctor args.length then
          none
        else
          let reducts : List Pattern :=
            (List.range args.length).foldl (fun acc i =>
              let a := args.getD i (.apply "" [])
              let aRed0 :=
                match referenceIntrinsicStatefulN fuel s a with
                | some (_sA, outA) =>
                    if outA.isEmpty then step s a else outA
                | none => step s a
              let aRed := aRed0.filter (fun a' => a' != a)
              let built :=
                aRed.map (fun a' =>
                  .apply ctor (args.take i ++ [a'] ++ args.drop (i + 1)))
              acc ++ built) []
          match reducts with
          | _ :: _ => some (s, reducts)
          | [] =>
              let arities := rewriteAritiesForHead s ctor
              let hasExact := arities.any (fun n => n == args.length)
              let hasLarger := arities.any (fun n => n > args.length)
              if hasLarger && !hasExact && !args.isEmpty then
                some (s, [partialPattern ctor args])
              else
                none

  private def referenceIntrinsicApplyFallbackN
      (fuel : Nat) (s : Session) (ctor : String) (args : List Pattern) :
      Option (Session × List Pattern) :=
    let dispatchIface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
      rewrites := fun s => s.bundle.language.rewrites
      premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
      eval := fun s term => referenceEvalWithStateCoreN fuel s term
      evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
      applyBindings := applyBindingsCompat
      matchPattern := matchPatternMeTTa
      normalizePattern := normalizeDollarVars
      dedupBindings := dedupBindings
    }
    match builtinPartialMinArity? ctor with
    | some minArity =>
        if args.length < minArity then
          some (s, [partialPattern ctor args])
        else
          referenceIntrinsicApplyDispatchTailN fuel dispatchIface s ctor args
    | none =>
        referenceIntrinsicApplyDispatchTailN fuel dispatchIface s ctor args

  private def referenceIntrinsicStatefulN : Nat → Session → Pattern → Option (Session × List Pattern)
    | 0, _s, _term => none
    | fuel + 1, s, term =>
        let referenceEvalDeterministicCoreN (s : Session) (detFuel : Nat) (term : Pattern) : Session × Pattern :=
          Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval
            (mkDeterministicEvalInterface
              (fun s term => referenceEvalWithStateCoreN fuel s term)
              (fun s fn args => referenceEvalCallableApplyN fuel s fn args))
            s detFuel term
        let pIface : Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Interface Session := {
          eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalDeterministic := referenceEvalDeterministicCoreN
          evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
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
              eval := fun s term => referenceEvalWithStateCoreN fuel s term
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
                      match referenceIntrinsicStatefulN fuel sess expr with
                      | some (s1, out0) =>
                          let out := if out0.isEmpty then [expr] else out0
                          (s1, out)
                      | none =>
                          let (s1, out0) := referenceEvalWithStateCoreN fuel sess expr
                          let out := if out0.isEmpty then [expr] else out0
                          (s1, out)
                  }
                  Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic streamI s term
            let controlFlowI : Algorithms.MeTTa.Simple.Semantics.ControlFlow.Interface Session := {
              eval := fun s term => referenceEvalWithStateCoreN fuel s term
              evalKeyValues := fun sess key =>
                match key with
                | .apply "superpose" [arg] =>
                    match referenceIntrinsicStatefulN fuel sess (.apply "superpose" [arg]) with
                    | some (sess', out) =>
                        let vals := if out.isEmpty then [.apply "superpose" [arg]] else out
                        (sess', vals)
                    | none =>
                        let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                        let vals := if out.isEmpty then [key] else out
                        (sess', vals)
                | _ =>
                    let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                    let vals := if out.isEmpty then [key] else out
                    (sess', vals)
              evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
              evalGeneratorValues := fun sess genExpr =>
                let (s1, out0) := referenceEvalWithStateCoreN fuel sess genExpr
                let (sCall, callOut) :=
                  match genExpr with
                  | .apply "Expr" (callable :: args) =>
                      referenceEvalCallableApplyN fuel s1 callable args
                  | _ =>
                      (s1, [])
                let baseOut := if callOut.isEmpty then out0 else callOut
                let dispatchI : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
                  rewrites := fun s => s.bundle.language.rewrites
                  premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
                  eval := fun s term => referenceEvalWithStateCoreN fuel s term
                  evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
                  applyBindings := applyBindingsCompat
                  matchPattern := matchPatternMeTTa
                  normalizePattern := normalizeDollarVars
                  dedupBindings := dedupBindings
                }
                let (sEnum, extra) :=
                  Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
                    dispatchI sCall genExpr
                let out := if extra.isEmpty then baseOut else extra
                (sEnum, out)
              applyBindings := applyBindingsCompat
              matchPattern := matchPatternMeTTa
              isTruthy := isTruthy
              patternOfBool := patternOfBool
            }
            match preIntrinsic with
            | some out => some out
            | none =>
                match term with
                | .apply "add-atom" [space, fact] =>
                    let spaceI : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
                      bundle := fun s => s.bundle
                      rewrites := fun s => s.bundle.language.rewrites
                      setBundle := withBundleCompiled
                      eval := fun s term => referenceEvalWithStateCoreN fuel s term
                      applyBindings := applyBindingsCompat
                      normalizePattern := normalizeDollarVars
                      normalizeForSpaceMatch := normalizeSpaceMatchPattern s
                      matchPattern := matchPatternMeTTa
                      dedupPatterns := dedupPatternList
                    }
                    let (s', out) :=
                      Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom
                        spaceI spacePolicy s space fact
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
                      let spaceI : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
                        bundle := fun s => s.bundle
                        rewrites := fun s => s.bundle.language.rewrites
                        setBundle := withBundleCompiled
                        eval := fun s term => referenceEvalWithStateCoreN fuel s term
                        applyBindings := applyBindingsCompat
                        normalizePattern := normalizeDollarVars
                        normalizeForSpaceMatch := normalizeSpaceMatchPattern s
                        matchPattern := matchPatternMeTTa
                        dedupPatterns := dedupPatternList
                      }
                      let (s', out) :=
                        Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom
                          spaceI spacePolicy s space factNorm
                      some (s', out)
                | .apply "remove-atom" [space, fact] =>
                    let spaceI : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
                      bundle := fun s => s.bundle
                      rewrites := fun s => s.bundle.language.rewrites
                      setBundle := withBundleCompiled
                      eval := fun s term => referenceEvalWithStateCoreN fuel s term
                      applyBindings := applyBindingsCompat
                      normalizePattern := normalizeDollarVars
                      normalizeForSpaceMatch := normalizeSpaceMatchPattern s
                      matchPattern := matchPatternMeTTa
                      dedupPatterns := dedupPatternList
                    }
                    let (s', out) :=
                      Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom
                        spaceI spacePolicy s space fact
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
                      let spaceI : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
                        bundle := fun s => s.bundle
                        rewrites := fun s => s.bundle.language.rewrites
                        setBundle := withBundleCompiled
                        eval := fun s term => referenceEvalWithStateCoreN fuel s term
                        applyBindings := applyBindingsCompat
                        normalizePattern := normalizeDollarVars
                        normalizeForSpaceMatch := normalizeSpaceMatchPattern s
                        matchPattern := matchPatternMeTTa
                        dedupPatterns := dedupPatternList
                      }
                      let (s', out) :=
                        Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom
                          spaceI spacePolicy s space factNorm
                      some (s', out)
                | .apply "remove-all-atoms" [space] =>
                    let spaceI : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
                      bundle := fun s => s.bundle
                      rewrites := fun s => s.bundle.language.rewrites
                      setBundle := withBundleCompiled
                      eval := fun s term => referenceEvalWithStateCoreN fuel s term
                      applyBindings := applyBindingsCompat
                      normalizePattern := normalizeDollarVars
                      normalizeForSpaceMatch := normalizeSpaceMatchPattern s
                      matchPattern := matchPatternMeTTa
                      dedupPatterns := dedupPatternList
                    }
                    let (s', out) :=
                      Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms
                        spaceI spacePolicy s space term
                    some (s', out)
                | .apply "remove-all-atoms!" [space] =>
                    let spaceI : Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
                      bundle := fun s => s.bundle
                      rewrites := fun s => s.bundle.language.rewrites
                      setBundle := withBundleCompiled
                      eval := fun s term => referenceEvalWithStateCoreN fuel s term
                      applyBindings := applyBindingsCompat
                      normalizePattern := normalizeDollarVars
                      normalizeForSpaceMatch := normalizeSpaceMatchPattern s
                      matchPattern := matchPatternMeTTa
                      dedupPatterns := dedupPatternList
                    }
                    let (s', out) :=
                      Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms
                        spaceI spacePolicy s space term
                    some (s', out)
                | .apply "get-atoms" [space] =>
                    intrinsicGetAtomsResultWithEval
                      (fun s term => referenceEvalWithStateCoreN fuel s term) s space
                | .apply "get-atoms!" [space] =>
                    intrinsicGetAtomsResultWithEval
                      (fun s term => referenceEvalWithStateCoreN fuel s term) s space
                | .apply "match" [space, pat, tmpl] =>
                    intrinsicMatchResultWithEval
                      (fun s term => referenceEvalWithStateCoreN fuel s term) s space pat tmpl
                | .apply "match" [pat, tmpl] =>
                    intrinsicMatchResultWithEval
                      (fun s term => referenceEvalWithStateCoreN fuel s term)
                      s selfSpaceAtom pat tmpl
                | .apply "case" [keyExpr, branchesExpr] =>
                    let (s', out) :=
                      Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic
                        controlFlowI s keyExpr branchesExpr
                    some (s', out)
                | .apply "foldall" [aggExpr, genExpr, initExpr] =>
                    let (s', out) :=
                      Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic
                        controlFlowI s aggExpr genExpr initExpr
                    some (s', out)
                | .apply "forall" [genExpr, checkExpr] =>
                    let (s', out) :=
                      Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic
                        controlFlowI s genExpr checkExpr
                    some (s', out)
                -- Phase 1a: state-unchanged branches (no SCC calls)
                | .apply "cut" [] =>
                    some (s, [patternOfBool true])
                | .apply "Predicate" [expr] =>
                    some (s, [expr])
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
                | .apply "add-translator-rule!" [th] =>
                    let heads' :=
                      Algorithms.MeTTa.Simple.Semantics.TranslatorOps.addHead
                        s.translatorRuleHeads th
                    some ({ s with translatorRuleHeads := heads' }, [patternOfBool true])
                | .apply "remove-translator-rule!" [th] =>
                    let heads' :=
                      Algorithms.MeTTa.Simple.Semantics.TranslatorOps.removeHead
                        s.translatorRuleHeads th
                    some ({ s with translatorRuleHeads := heads' }, [patternOfBool true])
                -- Vector space branches (modifies vectorSpaces only; CC preserved)
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
                            let rows := hits.map (fun entry =>
                              tupleOfElems [entry.1, floatLiteralPattern entry.2])
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
                            let rows := hits.map (fun entry =>
                              tupleOfElems [entry.1, floatLiteralPattern entry.2])
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
                            let rows := hits.map (fun entry =>
                              tupleOfElems [entry.1, floatLiteralPattern entry.2])
                            some (s, [tupleOfElems rows])
                        | none => some (s, [tupleOfElems []])
                    | _ => some (s, [tupleOfElems []])
                -- Phase 1b: single referenceEvalWithStateCoreN call (variable named evalArg)
                | .apply "once" [evalArg] =>
                    let (s', out) := referenceEvalWithStateCoreN fuel s evalArg
                    match out with
                    | [] => some (s', [.apply "()" []])
                    | x :: _ => some (s', [x])
                | .apply "nop" [evalArg] =>
                    let (s', _out) := referenceEvalWithStateCoreN fuel s evalArg
                    some (s', [.apply "()" []])
                | .apply "catch" [evalArg] =>
                    let (s1, out) := referenceEvalWithStateCoreN fuel s evalArg
                    some (s1, out)
                | .apply "msort" [evalArg] =>
                    let (s', out) := referenceEvalWithStateCoreN fuel s evalArg
                    let sortTupleLike : Pattern → Pattern := fun p =>
                      let elems := sortPatterns (tupleElems p)
                      match elems with
                      | [] => .apply "()" []
                      | hd :: tl =>
                          match hd with
                          | .apply ctor [] => .apply ctor tl
                          | _ => .apply "Expr" elems
                    let sorted :=
                      match out with
                      | [one] => [sortTupleLike one]
                      | _ => sortPatterns out
                    some (s', sorted)
                -- Phase 3: catch-3, superpose, hide, space, collapse, atom-of
                -- (simplified versions; state preservation is what matters here)
                | .apply "catch" [expr, _handler, fallback] =>
                    -- Simplified: eval expr, then eval fallback; both steps preserve CC.
                    let (s1, _out) := referenceEvalWithStateCoreN fuel s expr
                    let (s2, out2) := referenceEvalWithStateCoreN fuel s1 fallback
                    some (s2, out2)
                | .apply "superpose" [arg] =>
                    -- Simplified: single eval; state preserved.
                    let (s', out) := referenceEvalWithStateCoreN fuel s arg
                    some (s', out)
                | .apply "hide" [arg] =>
                    -- Single eval call; output discarded.
                    let (s', _out) := referenceEvalWithStateCoreN fuel s arg
                    some (s', [.apply "empty" []])
                | .apply "space" [left, right] =>
                    -- Two chained eval calls; state from second.
                    let (sL, _outL) := referenceEvalWithStateCoreN fuel s left
                    let (sR, _outR) := referenceEvalWithStateCoreN fuel sL right
                    some (sR, [])
                | .apply "collapse" [arg] =>
                    -- Single eval call; simplified output.
                    let (s', out) := referenceEvalWithStateCoreN fuel s arg
                    some (s', [tupleOfElems out])
                -- Phase 4: simple remaining branches (1-step or 2-step chain)
                | .apply "translatePredicate" [expr] =>
                    let (s', out) := referenceEvalWithStateCoreN fuel s expr
                    some (s', out)
                | .apply "if" [cond, thenBr, _elseBr] =>
                    let (s1, _cv) := referenceEvalWithStateCoreN fuel s cond
                    let (s2, out) := referenceEvalWithStateCoreN fuel s1 thenBr
                    some (s2, out)
                | .apply "if" [cond, thenBr] =>
                    let (s1, _cv) := referenceEvalWithStateCoreN fuel s cond
                    let (s2, out) := referenceEvalWithStateCoreN fuel s1 thenBr
                    some (s2, out)
                | .apply "let" [_pat, valExpr, body] =>
                    let (s1, _vs) := referenceEvalWithStateCoreN fuel s valExpr
                    let (s2, out) := referenceEvalWithStateCoreN fuel s1 body
                    some (s2, out)
                | .apply "let*" [_binds, body] =>
                    let (s', out) := referenceEvalWithStateCoreN fuel s body
                    some (s', out)
                | .apply "progn" _exprs =>
                    -- Simplified: state unchanged, result is unit.
                    some (s, [.apply "()" []])
                | .apply "prog1" _exprs =>
                    -- Simplified: state unchanged, result is unit.
                    some (s, [.apply "()" []])
                -- Phase 5: Expr, repr — need evalTupleIntrinsicWith / evalDeterministicCore
                | .apply "Expr" elems =>
                    let (s', out) :=
                      evalTupleIntrinsicWith
                        (fun s term => referenceEvalWithStateCoreN fuel s term)
                        (fun s fn args => referenceEvalCallableApplyN fuel s fn args)
                        isRuleCallableHead s elems
                    some (s', out)
                | .apply "repr" [arg] =>
                    -- Simplified: eval arg deterministically; state may change.
                    let (s', _argV) := referenceEvalDeterministicCoreN s 1024 arg
                    some (s', [])
                -- Phase 6: atom-of — faithful to the live intrinsicStateful branch.
                -- Uses `step` (pure, no state mutation) as the none-branch fallback,
                -- then applies the same tupleAt? extraction and dedup as the live code.
                | .apply "atom-of" [x] =>
                    let (s1, x1, _) := referenceRunNestedEffectsN fuel s true false x
                    let (s2, out) :=
                      match referenceIntrinsicStatefulN fuel s1 x1 with
                      | some (sI, outI) =>
                          if outI.isEmpty then (sI, [x1]) else (sI, outI)
                      | none =>
                          let reducts := step s1 x1
                          if reducts.isEmpty then (s1, [x1]) else (s1, reducts)
                    let extracted :=
                      out.filterMap fun candidate =>
                        match tupleAt? (tupleElems candidate) 0 with
                        | none => none
                        | some row => tupleAt? (tupleElems row) 0
                    if extracted.isEmpty then some (s2, [])
                    else some (s2, dedupPatternList extracted)
                -- Phase 7: generic .apply ctor args — faithful to the live intrinsicStateful branch.
                -- Sub-case A: builtinPartialMinArity — state unchanged.
                -- Sub-case B: compatFunctionHeadRewrite (inline dispatch iface) — state from dispatch.
                -- Sub-case C: hasCompatHeadConstraintRule — out empty → none.
                -- Sub-case D: reduceArgs (calls referenceIntrinsicStatefulN fuel s a; state unchanged).
                -- Sub-case E: arities/hasLarger — state unchanged.
                | .apply ctor args => referenceIntrinsicApplyFallbackN fuel s ctor args
                | _ => none
end

-- ─── Standalone N-kernel deterministic core ─────────────────────────────────
-- Matches the `let referenceEvalDeterministicCoreN` inside
-- `referenceIntrinsicStatefulN`, but is a top-level definition usable from
-- `optimizedBackendInterface` and in proof modules.
-- `outerFuel` controls sub-expression evaluation depth (for Expr handling);
-- `detFuel` controls the det evaluator's own recursion depth.

def referenceEvalDeterministicCoreNStandalone
    (outerFuel : Nat) (s : Session) (detFuel : Nat) (term : Pattern) : Session × Pattern :=
  Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval
    (mkDeterministicEvalInterface
      (fun s' t => referenceEvalWithStateCoreN outerFuel s' t)
      (fun s' fn args => referenceEvalCallableApplyN outerFuel s' fn args))
    s detFuel term

-- Faithful fuel-indexed mirror of ReferenceEval.runNestedEffects.
-- Unlike referenceRunNestedEffectsN, I.runNestedEffects is wired to the
-- self-recursive fuel-decremented call (not the stub `(s, term, false)`).
-- The backend never calls I.runNestedEffects from stepAux, so the difference is
-- currently computationally irrelevant, but the interface is now semantically
-- well-formed — a prerequisite for the eventual equivalence proof.
private def faithfulReferenceRunNestedEffectsN :
    Nat → Session → Bool → Bool → Pattern → Session × Pattern × Bool
  | 0, s, _isRoot, _parentCallable, term => (s, term, false)
  | fuel + 1, s, isRoot, parentCallable, term =>
      let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
        maxNodes := fun s => s.maxNodes
        maxSteps := fun s => s.maxSteps
        runNestedEffects :=
          fun s isRoot p term => faithfulReferenceRunNestedEffectsN fuel s isRoot p term
        intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
        isEagerCallableHead := isEagerCallableHead
        step := step
        enqueueNext := enqueueNext
        insertUnique := insertUnique
        dedupPatterns := dedupPatterns
      }
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
        iface s isRoot parentCallable term

-- Faithful fuel-indexed mirror of ReferenceEval.runNestedEffectsArgs.
-- I.runNestedEffects is wired to faithfulReferenceRunNestedEffectsN (not the stub).
-- No fuel pattern-match needed here since this function does not recurse on fuel directly.
private def faithfulReferenceRunNestedEffectsArgsN (fuel : Nat) (s : Session)
    (parentCallable : Bool) (args : List Pattern) (accRev : List Pattern) (changed : Bool) :
    Session × List Pattern × Bool :=
  let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
    maxNodes := fun s => s.maxNodes
    maxSteps := fun s => s.maxSteps
    runNestedEffects :=
      fun s isRoot p term => faithfulReferenceRunNestedEffectsN fuel s isRoot p term
    intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
    isEagerCallableHead := isEagerCallableHead
    step := step
    enqueueNext := enqueueNext
    insertUnique := insertUnique
    dedupPatterns := dedupPatterns
  }
  Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffectsArgs
    iface s parentCallable args accRev changed

-- Stage 2: faithful/stubbed nested-effects equivalence.
-- Both interfaces agree on intrinsicStateful and isEagerCallableHead;
-- runNestedEffects_ext shows the I.runNestedEffects field is never called, so they agree.

/-- `faithfulReferenceRunNestedEffectsN (n+1)` agrees with `referenceRunNestedEffectsN n`.
    Both use `referenceIntrinsicStatefulN n` as `intrinsicStateful` and the same
    `isEagerCallableHead`; the `I.runNestedEffects` field is never called by the backend. -/
theorem faithfulReferenceRunNestedEffectsN_eq (n : Nat) (s : Session)
    (isRoot parentCallable : Bool) (term : Pattern) :
    faithfulReferenceRunNestedEffectsN (n + 1) s isRoot parentCallable term =
    referenceRunNestedEffectsN n s isRoot parentCallable term := by
  simp only [faithfulReferenceRunNestedEffectsN, referenceRunNestedEffectsN]
  apply Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects_ext <;> rfl

/-- `faithfulReferenceRunNestedEffectsArgsN fuel` agrees with `referenceRunNestedEffectsArgsN fuel`.
    The `I.runNestedEffects` field is never called by `runNestedEffectsArgs`, so the
    faithful vs stubbed wiring is irrelevant. -/
theorem faithfulReferenceRunNestedEffectsArgsN_eq (fuel : Nat) (s : Session)
    (parentCallable : Bool) (args accRev : List Pattern) (changed : Bool) :
    faithfulReferenceRunNestedEffectsArgsN fuel s parentCallable args accRev changed =
    referenceRunNestedEffectsArgsN fuel s parentCallable args accRev changed := by
  simp only [faithfulReferenceRunNestedEffectsArgsN, referenceRunNestedEffectsArgsN]
  apply Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffectsArgs_ext <;> rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- Stage 3b: Faithful FuelResult-based kernel (F-kernel).
--
-- These wrap the N-kernel in FuelResult, replacing semantic fallback values at
-- fuel=0 with explicit `.outOfFuel`.  The only difference from the N-kernel is
-- the base case:  N returns (s, []) / (s, [expr]) / none; F returns .outOfFuel.
--
-- Theorem order:
--   3b.1  Definitions (below)
--   3b.2  Preservation: .done (s', out) → CompiledConsistent s'
--   3b.3  Simulation:   .done res → referenceEval*N fuel = res  (trivial by def)
-- ─────────────────────────────────────────────────────────────────────────────

/-- FuelResult wrapper around `referenceEvalWithStateCoreN`.
    `.outOfFuel` at fuel=0 (NOT the semantic fallback `(s, [])`).
    `.done res` iff `fuel > 0` and `res = referenceEvalWithStateCoreN fuel s term`. -/
private def faithfulEvalWithStateCoreF :
    Nat → Session → Pattern → FuelResult (Session × List Pattern)
  | 0, _s, _term => .outOfFuel
  | fuel + 1, s, term => .done (referenceEvalWithStateCoreN (fuel + 1) s term)

/-- FuelResult wrapper around `referenceIntrinsicStatefulN`.
    `.outOfFuel` at fuel=0 (NOT `none`, which conflates "no intrinsic" with "out of fuel"). -/
private def faithfulIntrinsicStatefulF :
    Nat → Session → Pattern → FuelResult (Option (Session × List Pattern))
  | 0, _s, _term => .outOfFuel
  | fuel + 1, s, term => .done (referenceIntrinsicStatefulN (fuel + 1) s term)

/-- FuelResult wrapper around `referenceEvalCallableApplyN`.
    `.outOfFuel` at fuel=0 (NOT the semantic fallback `(s, [])`). -/
private def faithfulEvalCallableApplyF :
    Nat → Session → Pattern → List Pattern → FuelResult (Session × List Pattern)
  | 0, _s, _callable, _args => .outOfFuel
  | fuel + 1, s, callable, args => .done (referenceEvalCallableApplyN (fuel + 1) s callable args)

/-- FuelResult wrapper around `referenceEvalForRuleEnumerationF`.
    `.outOfFuel` at fuel=0 (NOT the semantic fallback `(s, [expr])`). -/
private def faithfulEvalForRuleEnumerationF :
    Nat → Session → Pattern → FuelResult (Session × List Pattern)
  | 0, _s, _term => .outOfFuel
  | fuel + 1, s, term => .done (referenceEvalForRuleEnumerationN (fuel + 1) s term)

-- Stage 3b.2: Preservation on .done results.
-- Theorems are placed after the N-kernel preservation lemmas (compiledConsistent_of_reference*N),
-- which are defined later in the file.  See faithfulEvalWithStateCoreF_preserves etc. below.

-- Stage 3b.3: One-way simulation — .done res implies N-kernel agrees.
-- Trivially true by definition; the harder simulation to the live path requires
-- N-adequacy (Stage 3c, deferred).

/-- `.done res` from the F-kernel implies `referenceEvalWithStateCoreN fuel s term = res`. -/
theorem faithfulEvalWithStateCoreF_done_eq_N
    (fuel : Nat) (s : Session) (term : Pattern) (res : Session × List Pattern)
    (hdone : faithfulEvalWithStateCoreF fuel s term = .done res) :
    referenceEvalWithStateCoreN fuel s term = res := by
  cases fuel with
  | zero => simp [faithfulEvalWithStateCoreF] at hdone
  | succ n => simpa [faithfulEvalWithStateCoreF] using hdone

/-- `.done r` from the intrinsic F-kernel implies `referenceIntrinsicStatefulN fuel s term = r`. -/
theorem faithfulIntrinsicStatefulF_done_eq_N
    (fuel : Nat) (s : Session) (term : Pattern) (r : Option (Session × List Pattern))
    (hdone : faithfulIntrinsicStatefulF fuel s term = .done r) :
    referenceIntrinsicStatefulN fuel s term = r := by
  cases fuel with
  | zero => simp [faithfulIntrinsicStatefulF] at hdone
  | succ n => simpa [faithfulIntrinsicStatefulF] using hdone

/-- `.done res` from the callable-apply F-kernel implies
    `referenceEvalCallableApplyN fuel s callable args = res`. -/
theorem faithfulEvalCallableApplyF_done_eq_N
    (fuel : Nat) (s : Session) (callable : Pattern) (args : List Pattern)
    (res : Session × List Pattern)
    (hdone : faithfulEvalCallableApplyF fuel s callable args = .done res) :
    referenceEvalCallableApplyN fuel s callable args = res := by
  cases fuel with
  | zero => simp [faithfulEvalCallableApplyF] at hdone
  | succ n => simpa [faithfulEvalCallableApplyF] using hdone

/-- `.done res` from the rule-enumeration F-kernel implies
    `referenceEvalForRuleEnumerationN fuel s term = res`. -/
theorem faithfulEvalForRuleEnumerationF_done_eq_N
    (fuel : Nat) (s : Session) (term : Pattern) (res : Session × List Pattern)
    (hdone : faithfulEvalForRuleEnumerationF fuel s term = .done res) :
    referenceEvalForRuleEnumerationN fuel s term = res := by
  cases fuel with
  | zero => simp [faithfulEvalForRuleEnumerationF] at hdone
  | succ n => simpa [faithfulEvalForRuleEnumerationF] using hdone

-- ─────────────────────────────────────────────────────────────────────────────

def referenceEvalWithStateCore (s : Session) (term : Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore referenceEvalInterface s term

private def referenceDeterministicEvalInterfaceN (fuel : Nat) :
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.Interface Session := {
  evalTupleIntrinsic := evalTupleIntrinsicWith
    (fun s term => referenceEvalWithStateCoreN fuel s term)
    (fun s fn args => referenceEvalCallableApplyN fuel s fn args)
    isRuleCallableHead
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

private def referenceEvalDeterministicCoreN (fuel : Nat) (s : Session) (detFuel : Nat)
    (term : Pattern) : Session × Pattern :=
  Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval
    (referenceDeterministicEvalInterfaceN fuel) s detFuel term

private def referencePettaCoreInterfaceN (fuel : Nat) :
    Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Interface Session := {
  eval := fun s term => referenceEvalWithStateCoreN fuel s term
  evalDeterministic := referenceEvalDeterministicCoreN fuel
  evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
  findBindingsInSpace := findBindingsInSpace
  dedupPatterns := dedupPatternList
  typeCandidates := typeCandidatesInSelf
}

private def referenceStateEffectsInterfaceN (fuel : Nat) :
    Algorithms.MeTTa.Simple.Semantics.StateEffects.Interface Session := {
  eval := fun s term => referenceEvalWithStateCoreN fuel s term
  snapshot := fun sess => sess
  isFailure := isFailurePattern
  truePattern := patternOfBool true
  getStateCells := fun sess => sess.stateCells
  withStateCells := fun sess cells => { sess with stateCells := cells }
}

private def referenceStreamOpsInterfaceN (fuel : Nat) :
    Algorithms.MeTTa.Simple.Semantics.StreamOps.Interface Session := {
  evalValues := fun sess expr =>
    match referenceIntrinsicStatefulN fuel sess expr with
    | some (s1, out0) =>
        let out := if out0.isEmpty then [expr] else out0
        (s1, out)
    | none =>
        let (s1, out0) := referenceEvalWithStateCoreN fuel sess expr
        let out := if out0.isEmpty then [expr] else out0
        (s1, out)
}

private def referenceDispatchInterfaceN (fuel : Nat) :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
  rewrites := fun s => s.bundle.language.rewrites
  premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
  eval := fun s term => referenceEvalWithStateCoreN fuel s term
  evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
  normalizePattern := normalizeDollarVars
  dedupBindings := dedupBindings
}

private theorem compiledConsistent_of_referenceEvalWithStateCoreN_of_intrinsic
    (hIntrinsicPres :
      ∀ (fuel : Nat) (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    ∀ (fuel : Nat) (s : Session) (term : Pattern),
      CompiledConsistent s →
      CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1 := by
  intro fuel
  cases fuel with
  | zero =>
      intro s term hs
      simp [referenceEvalWithStateCoreN]
      simpa using hs
  | succ fuel =>
      intro s term hs
      let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
        maxNodes := fun s => s.maxNodes
        maxSteps := fun s => s.maxSteps
        runNestedEffects := fun s isRoot parentCallable term =>
          referenceRunNestedEffectsN fuel s isRoot parentCallable term
        intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
        isEagerCallableHead := isEagerCallableHead
        step := step
        enqueueNext := enqueueNext
        insertUnique := insertUnique
        dedupPatterns := dedupPatterns
      }
      have hIntrinsicPresRef :
          ∀ {s : Session} {term : Pattern} {s' : Session} {out : List Pattern},
            iface.intrinsicStateful s term = some (s', out) →
            CompiledConsistent s →
            CompiledConsistent s' := by
        intro s term s' out hIntr hs
        simpa [iface] using hIntrinsicPres fuel s term s' out hIntr hs
      have hPres :
          Algorithms.MeTTa.Simple.Backend.ReferenceEval.Preservation
            iface CompiledConsistent := by
        exact
          Algorithms.MeTTa.Simple.Backend.ReferenceEval.preservation_of_intrinsicStateful
            iface CompiledConsistent hIntrinsicPresRef
      simpa [referenceEvalWithStateCoreN, iface] using
        Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore_preserves
          iface CompiledConsistent hPres s term hs

private theorem compiledConsistent_of_referenceEvalForRuleEnumerationN_of_intrinsic
    (hIntrinsicPres :
      ∀ (fuel : Nat) (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    ∀ (fuel : Nat) (s : Session) (expr : Pattern),
      CompiledConsistent s →
      CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1 := by
  intro fuel
  cases fuel with
  | zero =>
      intro s expr hs
      simp [referenceEvalForRuleEnumerationN]
      simpa using hs
  | succ fuel =>
      intro s expr hs
      unfold referenceEvalForRuleEnumerationN
      cases hIntr : referenceIntrinsicStatefulN fuel s expr with
      | none =>
          simp
          exact compiledConsistent_of_referenceEvalWithStateCoreN_of_intrinsic
            hIntrinsicPres fuel s expr hs
      | some res =>
          rcases res with ⟨s1, out0⟩
          simp
          exact hIntrinsicPres fuel s expr s1 out0 hIntr hs


private theorem referenceDispatchInterfaceN_preservation
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1) :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.Preservation
      (referenceDispatchInterfaceN fuel) CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    evalForRuleEnumeration_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1 :=
      hEvalCorePres s term hs
    have hState : (referenceEvalWithStateCoreN fuel s term).1 = s' := by
      simpa [referenceDispatchInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s expr s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1 :=
      hEvalForRulePres s expr hs
    have hState : (referenceEvalForRuleEnumerationN fuel s expr).1 = s' := by
      simpa [referenceDispatchInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres

private theorem compiledConsistent_of_referenceEnumerateCallByRulesN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    {s : Session} {expr : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
        (referenceDispatchInterfaceN fuel) s expr).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules_preserves
      (referenceDispatchInterfaceN fuel) CompiledConsistent
      (referenceDispatchInterfaceN_preservation fuel hEvalCorePres hEvalForRulePres)
      s expr hs

private theorem compiledConsistent_of_referenceCompatFunctionHeadRewriteN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    {s : Session} {term : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        (referenceDispatchInterfaceN fuel) s term).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite_preserves
      (referenceDispatchInterfaceN fuel) CompiledConsistent
      (referenceDispatchInterfaceN_preservation fuel hEvalCorePres hEvalForRulePres)
      s term hs

private theorem compiledConsistent_of_referenceCompatFunctionHeadRewriteN_result
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    {s s' : Session} {term : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        (referenceDispatchInterfaceN fuel) s term = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceCompatFunctionHeadRewriteN
      (fuel := fuel) (hEvalCorePres := hEvalCorePres) (hEvalForRulePres := hEvalForRulePres)
      (s := s) (term := term) hs
  simpa [hEval] using hCC

private theorem referenceIntrinsicApplyDispatchTailN_stateCases
    (fuel : Nat)
    (dispatchIface : Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session)
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicApplyDispatchTailN fuel dispatchIface s ctor args =
        some (s', out)) :
    s' = s ∨
    s' =
      (Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        dispatchIface s (.apply ctor args)).1 := by
  unfold referenceIntrinsicApplyDispatchTailN at h
  cases hCompat :
      Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        dispatchIface s (.apply ctor args) with
  | mk sFH fromHeads =>
      cases fromHeads with
      | nil =>
          by_cases hConstraint :
              Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
                dispatchIface s ctor args.length
          · simp [hCompat, hConstraint] at h
          · have hTail := h
            simp [hCompat, hConstraint] at hTail
            cases hReducts :
                (List.map
                    (fun x2 =>
                      List.map
                        (fun a' =>
                          Pattern.apply ctor (List.take x2 args ++ a' :: List.drop (x2 + 1) args))
                        (List.filter (fun a' => a' != args[x2]?.getD (Pattern.apply "" []))
                          (match referenceIntrinsicStatefulN fuel s (args[x2]?.getD (Pattern.apply "" [])) with
                          | some (_sA, outA) =>
                              if outA = [] then s.step (args[x2]?.getD (Pattern.apply "" [])) else outA
                          | none => s.step (args[x2]?.getD (Pattern.apply "" [])))))
                    (List.range args.length)).flatten with
            | nil =>
                simp [hReducts] at hTail
                exact Or.inl hTail.2.1.symm
            | cons hd tl =>
                simp [hReducts] at hTail
                exact Or.inl hTail.1.symm
      | cons hd tl =>
          simp [hCompat] at h
          exact Or.inr (by
            simpa [hCompat] using h.1.symm)

private theorem referenceIntrinsicApplyFallbackN_stateCases
    (fuel : Nat)
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicApplyFallbackN fuel s ctor args = some (s', out)) :
    s' = s ∨
    s' =
      (Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        (referenceDispatchInterfaceN fuel) s (.apply ctor args)).1 := by
  unfold referenceIntrinsicApplyFallbackN at h
  split at h
  · rename_i minArity
    split at h
    · exact Or.inl ((congrArg Prod.fst (Option.some.inj h)).symm)
    · exact
        referenceIntrinsicApplyDispatchTailN_stateCases
          fuel (referenceDispatchInterfaceN fuel)
          (by simpa [referenceDispatchInterfaceN] using h)
  · exact
      referenceIntrinsicApplyDispatchTailN_stateCases
        fuel (referenceDispatchInterfaceN fuel)
        (by simpa [referenceDispatchInterfaceN] using h)

private theorem compiledConsistent_of_referenceIntrinsicApplyFallbackN_result
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicApplyFallbackN fuel s ctor args = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCases :=
    referenceIntrinsicApplyFallbackN_stateCases
      (fuel := fuel) (s := s) (s' := s') (ctor := ctor) (args := args) (out := out) h
  cases hCases with
  | inl hState =>
      simpa [hState] using hs
  | inr hState =>
      have hCompat :
          CompiledConsistent
            (Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
              (referenceDispatchInterfaceN fuel) s (.apply ctor args)).1 :=
        compiledConsistent_of_referenceCompatFunctionHeadRewriteN
          fuel hEvalCorePres hEvalForRulePres hs
      simpa [hState] using hCompat

private theorem compiledConsistent_of_referenceRefineCallableOutN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    {s : Session} {expr : Pattern} {baseOut : List Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
        (referenceDispatchInterfaceN fuel) s expr baseOut).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration_preserves
      (referenceDispatchInterfaceN fuel) CompiledConsistent
      (referenceDispatchInterfaceN_preservation fuel hEvalCorePres hEvalForRulePres)
      s expr baseOut hs

private theorem compiledConsistent_of_referenceDispatchPostprocessN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (s : Session) (expr : Pattern) (baseOut : List Pattern)
    (hs : CompiledConsistent s) :
    let (sEnum, extra) :=
      Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
        (referenceDispatchInterfaceN fuel) s expr
    let out := if extra.isEmpty then baseOut else extra
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
        (referenceDispatchInterfaceN fuel) sEnum expr out).1 := by
  have hEnum :
      CompiledConsistent
        (Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
          (referenceDispatchInterfaceN fuel) s expr).1 :=
    compiledConsistent_of_referenceEnumerateCallByRulesN fuel hEvalCorePres hEvalForRulePres hs
  cases hEnumRun :
      Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
        (referenceDispatchInterfaceN fuel) s expr with
  | mk sEnum extra =>
      have hsEnum : CompiledConsistent sEnum := by
        simpa [hEnumRun] using hEnum
      have hRefine :
          CompiledConsistent
            (Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
              (referenceDispatchInterfaceN fuel) sEnum expr
              (if extra.isEmpty then baseOut else extra)).1 :=
        compiledConsistent_of_referenceRefineCallableOutN
          fuel hEvalCorePres hEvalForRulePres hsEnum
      simpa [hEnumRun] using hRefine

private theorem referenceStateEffectsInterfaceN_preservation
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1) :
    Algorithms.MeTTa.Simple.Semantics.StateEffects.Preservation
      (referenceStateEffectsInterfaceN fuel) CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    snapshot_preserves := ?_,
    withStateCells_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1 :=
      hEvalCorePres s term hs
    have hState : (referenceEvalWithStateCoreN fuel s term).1 = s' := by
      simpa [referenceStateEffectsInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s hs
    simpa [referenceStateEffectsInterfaceN] using hs
  · intro s cells hs
    exact compiledConsistent_withStateCells s cells hs

private theorem compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s : Session} {term : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Option.getD
        (Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
          (referenceStateEffectsInterfaceN fuel) s term)
        (s, [])).1 := by
  intro hs
  cases hState :
      Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
        (referenceStateEffectsInterfaceN fuel) s term with
  | none =>
      simp
      simpa using hs
  | some res =>
      have hPres :=
        Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic_preserves
          (referenceStateEffectsInterfaceN fuel) CompiledConsistent
          (referenceStateEffectsInterfaceN_preservation fuel hEvalCorePres)
          s term hs
      simpa [hState] using hPres

private theorem referenceStreamOpsInterfaceN_preservation
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    Algorithms.MeTTa.Simple.Semantics.StreamOps.Preservation
      (referenceStreamOpsInterfaceN fuel) CompiledConsistent := by
  refine { evalValues_preserves := ?_ }
  intro s expr s' out hEval hs
  unfold referenceStreamOpsInterfaceN at hEval
  cases hIntr : referenceIntrinsicStatefulN fuel s expr with
  | none =>
      simp [hIntr] at hEval
      have hPres : CompiledConsistent (referenceEvalWithStateCoreN fuel s expr).1 :=
        hEvalCorePres s expr hs
      have hState : (referenceEvalWithStateCoreN fuel s expr).1 = s' := hEval.1
      simpa [hState] using hPres
  | some res =>
      rcases res with ⟨s1, out0⟩
      simp [hIntr] at hEval
      have hPres : CompiledConsistent s1 :=
        hIntrinsicPres s expr s1 out0 hIntr hs
      have hState : s1 = s' := hEval.1
      simpa [hState] using hPres

private theorem compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {term : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Option.getD
        (Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
          (referenceStreamOpsInterfaceN fuel) s term)
        (s, [])).1 := by
  intro hs
  cases hStream :
      Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
        (referenceStreamOpsInterfaceN fuel) s term with
  | none =>
      simp
      simpa using hs
  | some res =>
      have hPres :=
        Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic_preserves
          (referenceStreamOpsInterfaceN fuel) CompiledConsistent
          (referenceStreamOpsInterfaceN_preservation fuel hEvalCorePres hIntrinsicPres)
          s term hs
      simpa [hStream] using hPres

private def referenceEvalKeyValuesPreservingMultiplicityN (fuel : Nat)
    (sess : Session) (key : Pattern) : Session × List Pattern :=
  match key with
  | .apply "superpose" [arg] =>
      match referenceIntrinsicStatefulN fuel sess (.apply "superpose" [arg]) with
      | some (sess', out) =>
          let vals := if out.isEmpty then [.apply "superpose" [arg]] else out
          (sess', vals)
      | none =>
          let (sess', out) := referenceEvalWithStateCoreN fuel sess key
          let vals := if out.isEmpty then [key] else out
          (sess', vals)
  | _ =>
      let (sess', out) := referenceEvalWithStateCoreN fuel sess key
      let vals := if out.isEmpty then [key] else out
      (sess', vals)

private theorem compiledConsistent_of_referenceEvalKeyValuesPreservingMultiplicityN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    (sess : Session) (key : Pattern) :
    CompiledConsistent sess →
    CompiledConsistent (referenceEvalKeyValuesPreservingMultiplicityN fuel sess key).1 := by
  intro hs
  cases key with
  | fvar x =>
      simpa [referenceEvalKeyValuesPreservingMultiplicityN] using hEvalCorePres sess (.fvar x) hs
  | bvar n =>
      simpa [referenceEvalKeyValuesPreservingMultiplicityN] using hEvalCorePres sess (.bvar n) hs
  | lambda body =>
      simpa [referenceEvalKeyValuesPreservingMultiplicityN] using
        hEvalCorePres sess (.lambda body) hs
  | multiLambda n body =>
      simpa [referenceEvalKeyValuesPreservingMultiplicityN] using
        hEvalCorePres sess (.multiLambda n body) hs
  | subst body repl =>
      simpa [referenceEvalKeyValuesPreservingMultiplicityN] using
        hEvalCorePres sess (.subst body repl) hs
  | collection ct elems rest =>
      simpa [referenceEvalKeyValuesPreservingMultiplicityN] using
        hEvalCorePres sess (.collection ct elems rest) hs
  | apply ctor args =>
      cases args with
      | nil =>
          simpa [referenceEvalKeyValuesPreservingMultiplicityN] using
            hEvalCorePres sess (.apply ctor []) hs
      | cons arg rest =>
          cases rest with
          | nil =>
              by_cases hCtor : ctor = "superpose"
              · subst hCtor
                cases hIntr : referenceIntrinsicStatefulN fuel sess (.apply "superpose" [arg]) with
                | none =>
                    simp [referenceEvalKeyValuesPreservingMultiplicityN, hIntr]
                    exact hEvalCorePres sess (.apply "superpose" [arg]) hs
                | some res =>
                    rcases res with ⟨sess', out⟩
                    simp [referenceEvalKeyValuesPreservingMultiplicityN, hIntr]
                    exact hIntrinsicPres sess (.apply "superpose" [arg]) sess' out hIntr hs
              · simpa [referenceEvalKeyValuesPreservingMultiplicityN, hCtor] using
                  hEvalCorePres sess (.apply ctor [arg]) hs
          | cons arg2 rest2 =>
              simpa [referenceEvalKeyValuesPreservingMultiplicityN] using
                hEvalCorePres sess (.apply ctor (arg :: arg2 :: rest2)) hs

private def referenceEvalGeneratorValuesN (fuel : Nat)
    (s : Session) (genExpr : Pattern) : Session × List Pattern :=
  let (s1, out0) := referenceEvalWithStateCoreN fuel s genExpr
  let (sCall, callOut) :=
    match genExpr with
    | .apply "Expr" (callable :: args) =>
        referenceEvalCallableApplyN fuel s1 callable args
    | _ =>
        (s1, [])
  let baseOut := if callOut.isEmpty then out0 else callOut
  let (sEnum, extra) :=
    Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
      (referenceDispatchInterfaceN fuel) sCall genExpr
  let out := if extra.isEmpty then baseOut else extra
  (sEnum, out)

private theorem compiledConsistent_of_referenceEvalGeneratorValuesN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (s : Session) (genExpr : Pattern) :
    CompiledConsistent s →
    CompiledConsistent (referenceEvalGeneratorValuesN fuel s genExpr).1 := by
  intro hs
  unfold referenceEvalGeneratorValuesN
  have hS1 : CompiledConsistent (referenceEvalWithStateCoreN fuel s genExpr).1 :=
    hEvalCorePres s genExpr hs
  cases hEval : referenceEvalWithStateCoreN fuel s genExpr with
  | mk s1 out0 =>
      have hs1 : CompiledConsistent s1 := by
        simpa [hEval] using hS1
      cases genExpr with
      | apply ctor args =>
          by_cases hExpr : ctor = "Expr"
          ·
              subst hExpr
              cases args with
              | nil =>
                  simp
                  exact
                    compiledConsistent_of_referenceEnumerateCallByRulesN
                      fuel hEvalCorePres hEvalForRulePres hs1
              | cons callable rest =>
                  have hCall :
                      CompiledConsistent (referenceEvalCallableApplyN fuel s1 callable rest).1 :=
                    hEvalCallablePres s1 callable rest hs1
                  cases hCallRun : referenceEvalCallableApplyN fuel s1 callable rest with
                  | mk sCall callOut =>
                      have hsCall : CompiledConsistent sCall := by
                        simpa [hCallRun] using hCall
                      simp [hCallRun]
                      exact
                        compiledConsistent_of_referenceEnumerateCallByRulesN
                          fuel hEvalCorePres hEvalForRulePres hsCall
          ·
              simp [hExpr]
              exact
                compiledConsistent_of_referenceEnumerateCallByRulesN
                  fuel hEvalCorePres hEvalForRulePres hs1
      | _ =>
          simp
          exact
            compiledConsistent_of_referenceEnumerateCallByRulesN
              fuel hEvalCorePres hEvalForRulePres hs1

private def referenceControlFlowInterfaceN (fuel : Nat) :
    Algorithms.MeTTa.Simple.Semantics.ControlFlow.Interface Session := {
  eval := fun s term => referenceEvalWithStateCoreN fuel s term
  evalKeyValues := fun s key => referenceEvalKeyValuesPreservingMultiplicityN fuel s key
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
  evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
  evalGeneratorValues := fun s genExpr => referenceEvalGeneratorValuesN fuel s genExpr
  isTruthy := isTruthy
  patternOfBool := patternOfBool
}

private theorem referenceControlFlowInterfaceN_preservation
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    Algorithms.MeTTa.Simple.Semantics.ControlFlow.Preservation
      (referenceControlFlowInterfaceN fuel) CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    evalKeyValues_preserves := ?_,
    evalCallableApply_preserves := ?_,
    evalGeneratorValues_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1 :=
      hEvalCorePres s term hs
    have hState : (referenceEvalWithStateCoreN fuel s term).1 = s' := by
      simpa [referenceControlFlowInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s term s' out hEval hs
    have hPres :
        CompiledConsistent (referenceEvalKeyValuesPreservingMultiplicityN fuel s term).1 :=
      compiledConsistent_of_referenceEvalKeyValuesPreservingMultiplicityN
        fuel hEvalCorePres hIntrinsicPres s term hs
    have hState : (referenceEvalKeyValuesPreservingMultiplicityN fuel s term).1 = s' := by
      simpa [referenceControlFlowInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s fn args s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1 :=
      hEvalCallablePres s fn args hs
    have hState : (referenceEvalCallableApplyN fuel s fn args).1 = s' := by
      simpa [referenceControlFlowInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s genExpr s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalGeneratorValuesN fuel s genExpr).1 :=
      compiledConsistent_of_referenceEvalGeneratorValuesN
        fuel hEvalCorePres hEvalCallablePres hEvalForRulePres s genExpr hs
    have hState : (referenceEvalGeneratorValuesN fuel s genExpr).1 = s' := by
      simpa [referenceControlFlowInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres

private theorem compiledConsistent_of_referenceCaseIntrinsicN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {keyExpr branchesExpr : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic
        (referenceControlFlowInterfaceN fuel) s keyExpr branchesExpr).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic_preserves
      (referenceControlFlowInterfaceN fuel) CompiledConsistent
      (referenceControlFlowInterfaceN_preservation
        fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres)
      s keyExpr branchesExpr hs

private theorem compiledConsistent_of_referenceFoldallIntrinsicN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {aggExpr genExpr initExpr : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic
        (referenceControlFlowInterfaceN fuel) s aggExpr genExpr initExpr).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic_preserves
      (referenceControlFlowInterfaceN fuel) CompiledConsistent
      (referenceControlFlowInterfaceN_preservation
        fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres)
      s aggExpr genExpr initExpr hs

private theorem compiledConsistent_of_referenceForallIntrinsicN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {genExpr checkExpr : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic
        (referenceControlFlowInterfaceN fuel) s genExpr checkExpr).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic_preserves
      (referenceControlFlowInterfaceN fuel) CompiledConsistent
      (referenceControlFlowInterfaceN_preservation
        fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres)
      s genExpr checkExpr hs

private theorem compiledConsistent_of_referenceCaseIntrinsicInlineN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {keyExpr branchesExpr : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic
        { eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalKeyValues := fun sess key =>
            match key with
            | .apply "superpose" [arg] =>
                match referenceIntrinsicStatefulN fuel sess (.apply "superpose" [arg]) with
                | some (sess', out) =>
                    let vals := if out.isEmpty then [.apply "superpose" [arg]] else out
                    (sess', vals)
                | none =>
                    let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                    let vals := if out.isEmpty then [key] else out
                    (sess', vals)
            | _ =>
                let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                let vals := if out.isEmpty then [key] else out
                (sess', vals)
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
          evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
          isTruthy := isTruthy
          patternOfBool := patternOfBool } s keyExpr branchesExpr).1 := by
  intro hs
  change CompiledConsistent
    (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic
      (referenceControlFlowInterfaceN fuel) s keyExpr branchesExpr).1
  exact
    compiledConsistent_of_referenceCaseIntrinsicN
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (s := s) (keyExpr := keyExpr) (branchesExpr := branchesExpr) hs

private theorem compiledConsistent_of_referenceFoldallIntrinsicInlineN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {aggExpr genExpr initExpr : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic
        { eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalKeyValues := fun sess key =>
            match key with
            | .apply "superpose" [arg] =>
                match referenceIntrinsicStatefulN fuel sess (.apply "superpose" [arg]) with
                | some (sess', out) =>
                    let vals := if out.isEmpty then [.apply "superpose" [arg]] else out
                    (sess', vals)
                | none =>
                    let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                    let vals := if out.isEmpty then [key] else out
                    (sess', vals)
            | _ =>
                let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                let vals := if out.isEmpty then [key] else out
                (sess', vals)
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
          evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
          isTruthy := isTruthy
          patternOfBool := patternOfBool } s aggExpr genExpr initExpr).1 := by
  intro hs
  change CompiledConsistent
    (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic
      (referenceControlFlowInterfaceN fuel) s aggExpr genExpr initExpr).1
  exact
    compiledConsistent_of_referenceFoldallIntrinsicN
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (s := s) (aggExpr := aggExpr) (genExpr := genExpr) (initExpr := initExpr) hs

private theorem compiledConsistent_of_referenceForallIntrinsicInlineN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {genExpr checkExpr : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic
        { eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalKeyValues := fun sess key =>
            match key with
            | .apply "superpose" [arg] =>
                match referenceIntrinsicStatefulN fuel sess (.apply "superpose" [arg]) with
                | some (sess', out) =>
                    let vals := if out.isEmpty then [.apply "superpose" [arg]] else out
                    (sess', vals)
                | none =>
                    let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                    let vals := if out.isEmpty then [key] else out
                    (sess', vals)
            | _ =>
                let (sess', out) := referenceEvalWithStateCoreN fuel sess key
                let vals := if out.isEmpty then [key] else out
                (sess', vals)
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
          evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
          isTruthy := isTruthy
          patternOfBool := patternOfBool } s genExpr checkExpr).1 := by
  intro hs
  change CompiledConsistent
    (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic
      (referenceControlFlowInterfaceN fuel) s genExpr checkExpr).1
  exact
    compiledConsistent_of_referenceForallIntrinsicN
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (s := s) (genExpr := genExpr) (checkExpr := checkExpr) hs

private theorem compiledConsistent_of_referenceCaseIntrinsicInlineN_result
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {keyExpr branchesExpr : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic
        { eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
          evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
          isTruthy := isTruthy
          patternOfBool := patternOfBool } s keyExpr branchesExpr = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceCaseIntrinsicInlineN
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (s := s) (keyExpr := keyExpr) (branchesExpr := branchesExpr) hs
  have hS :
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s keyExpr branchesExpr).fst = s' := by
    simpa using congrArg Prod.fst hEval
  exact hS.symm ▸ hCC

private theorem compiledConsistent_of_referenceCaseIntrinsicInlineN_conj
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {keyExpr branchesExpr : Pattern} {out : List Pattern}
    (hEval :
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s keyExpr branchesExpr).fst = s' ∧
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalCaseIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s keyExpr branchesExpr).snd = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  obtain ⟨hS, hOut⟩ := hEval
  exact
    compiledConsistent_of_referenceCaseIntrinsicInlineN_result
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (hEval := Prod.ext hS hOut) hs

private theorem compiledConsistent_of_referenceFoldallIntrinsicInlineN_result
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {aggExpr genExpr initExpr : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic
        { eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
          evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
          isTruthy := isTruthy
          patternOfBool := patternOfBool } s aggExpr genExpr initExpr = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceFoldallIntrinsicInlineN
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (s := s) (aggExpr := aggExpr) (genExpr := genExpr) (initExpr := initExpr) hs
  have hS :
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s aggExpr genExpr initExpr).fst = s' := by
    simpa using congrArg Prod.fst hEval
  exact hS.symm ▸ hCC

private theorem compiledConsistent_of_referenceFoldallIntrinsicInlineN_conj
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {aggExpr genExpr initExpr : Pattern} {out : List Pattern}
    (hEval :
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s aggExpr genExpr initExpr).fst = s' ∧
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalFoldallIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s aggExpr genExpr initExpr).snd = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  obtain ⟨hS, hOut⟩ := hEval
  exact
    compiledConsistent_of_referenceFoldallIntrinsicInlineN_result
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (hEval := Prod.ext hS hOut) hs

private theorem compiledConsistent_of_referenceForallIntrinsicInlineN_result
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {genExpr checkExpr : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic
        { eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
          evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
          isTruthy := isTruthy
          patternOfBool := patternOfBool } s genExpr checkExpr = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceForallIntrinsicInlineN
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (s := s) (genExpr := genExpr) (checkExpr := checkExpr) hs
  have hS :
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s genExpr checkExpr).fst = s' := by
    simpa using congrArg Prod.fst hEval
  exact hS.symm ▸ hCC

private theorem compiledConsistent_of_referenceForallIntrinsicInlineN_conj
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {genExpr checkExpr : Pattern} {out : List Pattern}
    (hEval :
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s genExpr checkExpr).fst = s' ∧
      (Algorithms.MeTTa.Simple.Semantics.ControlFlow.evalForallIntrinsic
          { eval := fun s term => referenceEvalWithStateCoreN fuel s term
            evalKeyValues := fun sess key => referenceEvalKeyValuesPreservingMultiplicityN fuel sess key
            applyBindings := applyBindingsCompat
            matchPattern := matchPatternMeTTa
            evalCallableApply := fun s fn args => referenceEvalCallableApplyN fuel s fn args
            evalGeneratorValues := fun sess genExpr => referenceEvalGeneratorValuesN fuel sess genExpr
            isTruthy := isTruthy
            patternOfBool := patternOfBool } s genExpr checkExpr).snd = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  obtain ⟨hS, hOut⟩ := hEval
  exact
    compiledConsistent_of_referenceForallIntrinsicInlineN_result
      fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
      (hEval := Prod.ext hS hOut) hs

private def referenceSpaceEvalInterface (s0 : Session) :
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
  bundle := fun s => s.bundle
  rewrites := fun s => s.bundle.language.rewrites
  setBundle := withBundleCompiled
  eval := referenceEvalWithStateCore
  applyBindings := applyBindingsCompat
  normalizePattern := normalizeDollarVars
  normalizeForSpaceMatch := normalizeSpaceMatchPattern s0
  matchPattern := matchPatternMeTTa
  dedupPatterns := dedupPatternList
}

private def referenceSpaceEvalInterfaceN (fuel : Nat) (s0 : Session) :
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.Interface Session := {
  bundle := fun s => s.bundle
  rewrites := fun s => s.bundle.language.rewrites
  setBundle := withBundleCompiled
  eval := fun s term => referenceEvalWithStateCoreN fuel s term
  applyBindings := applyBindingsCompat
  normalizePattern := normalizeDollarVars
  normalizeForSpaceMatch := normalizeSpaceMatchPattern s0
  matchPattern := matchPatternMeTTa
  dedupPatterns := dedupPatternList
}

/-- Evaluate a substituted `match` template through the live reference interface.
    This is a public wrapper exposing the compositional `SpaceOps` boundary without
    leaking the private interface record itself. -/
def matchTemplateAfterBindings
    (bs : Bindings) (tmpl : Pattern) : Pattern :=
  applyBindingsCompat bs tmpl

/-- Substituting a `get-atoms` template preserves the outer head and only
    substitutes its argument. -/
theorem matchTemplateAfterBindings_getAtoms
    (bs : Bindings) (spaceExpr : Pattern) :
    matchTemplateAfterBindings bs (.apply "get-atoms" [spaceExpr]) =
      .apply "get-atoms" [matchTemplateAfterBindings bs spaceExpr] := by
  have hHead : dollarHeadVarName? (.apply "get-atoms" []) = none := by
    native_decide
  have hHeight :
      patternHeight (.apply "get-atoms" [spaceExpr]) = 1 + patternHeight spaceExpr := by
    simp [patternHeight, Nat.max_eq_right (Nat.zero_le _)]
  unfold matchTemplateAfterBindings applyBindingsCompat
  rw [hHeight]
  simp [bindingVarBudget, Nat.add_assoc, Nat.add_comm]
  have hFuel :
      1 + (1 + (patternHeight spaceExpr + (List.map (fun x => x.fst) bs).eraseDups.length)) =
        Nat.succ (1 + (patternHeight spaceExpr + (List.map (fun x => x.fst) bs).eraseDups.length)) := by
    omega
  rw [hFuel]
  simp [applyBindingsCompatFuel, hHead]

/-- Substituting a `get-atoms!` template preserves the outer head and only
    substitutes its argument. -/
theorem matchTemplateAfterBindings_getAtomsBang
    (bs : Bindings) (spaceExpr : Pattern) :
    matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr]) =
      .apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr] := by
  have hHead : dollarHeadVarName? (.apply "get-atoms!" []) = none := by
    native_decide
  have hHeight :
      patternHeight (.apply "get-atoms!" [spaceExpr]) = 1 + patternHeight spaceExpr := by
    simp [patternHeight, Nat.max_eq_right (Nat.zero_le _)]
  unfold matchTemplateAfterBindings applyBindingsCompat
  rw [hHeight]
  simp [bindingVarBudget, Nat.add_assoc, Nat.add_comm]
  have hFuel :
      1 + (1 + (patternHeight spaceExpr + (List.map (fun x => x.fst) bs).eraseDups.length)) =
        Nat.succ (1 + (patternHeight spaceExpr + (List.map (fun x => x.fst) bs).eraseDups.length)) := by
    omega
  rw [hFuel]
  simp [applyBindingsCompatFuel, hHead]

/-- Evaluate a substituted `match` template through the live reference interface.
    This is a public wrapper exposing the compositional `SpaceOps` boundary without
    leaking the private interface record itself. -/
def referenceMatchEvalMatchedTemplate
    (s0 sess : Session) (tmplSub : Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate
    (referenceSpaceEvalInterface s0) sess tmplSub

/-- Evaluate a substituted `match` template through the fuel-indexed total reference
    interface. -/
def totalMatchEvalMatchedTemplate
    (fuel : Nat) (s0 sess : Session) (tmplSub : Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate
    (referenceSpaceEvalInterfaceN fuel s0) sess tmplSub

/-- Intrinsic `match` result at the live-reference boundary. -/
def referenceMatchIntrinsicResult
    (s : Session) (space pat tmpl : Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
    (referenceSpaceEvalInterface s) spacePolicy s space pat tmpl

/-- Intrinsic `match` result at the fuel-indexed total-reference boundary. -/
def totalMatchIntrinsicResult
    (fuel : Nat) (s : Session) (space pat tmpl : Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
    (referenceSpaceEvalInterfaceN fuel s) spacePolicy s space pat tmpl

/-- Binding enumeration used by the live-reference `match` intrinsic boundary. -/
def referenceMatchBindings
    (s : Session) (space pat : Pattern) : List Bindings :=
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.findBindingsInSpace
    (referenceSpaceEvalInterface s) spacePolicy s space pat

/-- Binding enumeration used by the fuel-indexed total-reference `match` boundary. -/
def totalMatchBindings
    (fuel : Nat) (s : Session) (space pat : Pattern) : List Bindings :=
  Algorithms.MeTTa.Simple.Semantics.SpaceOps.findBindingsInSpace
    (referenceSpaceEvalInterfaceN fuel s) spacePolicy s space pat

/-- Live-reference and fuel-indexed total-reference `match` binding enumeration agree
    because `findBindingsInSpace` is independent of the interface `eval` field. -/
theorem referenceMatchBindings_eq_totalMatchBindings
    (fuel : Nat) (s : Session) (space pat : Pattern) :
    referenceMatchBindings s space pat = totalMatchBindings fuel s space pat := by
  unfold referenceMatchBindings totalMatchBindings
  have hIface :
      referenceSpaceEvalInterfaceN fuel s =
        { referenceSpaceEvalInterface s with
            eval := fun s term => referenceEvalWithStateCoreN fuel s term } := by
    rfl
  rw [hIface]
  simpa using
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.findBindingsInSpace_eval_irrelevant
      (I := referenceSpaceEvalInterface s)
      (eval' := fun s term => referenceEvalWithStateCoreN fuel s term)
      (P := spacePolicy) (s := s) (space := space) (pat := pat)

/-- Compositional adequacy for the intrinsic `match` boundary.
    This is the primary theorem shape to use downstream: if live-reference and
    fuel-indexed total-reference agree on evaluating the specific substituted
    templates that arise from the match bindings, then the intrinsic `match`
    enumeration itself agrees. -/
theorem referenceMatchIntrinsicResult_eq_total_of_bindingwise_evalMatchedTemplate_agreement
    (fuel : Nat) (s : Session) (space pat tmpl : Pattern)
    (hBindings : referenceMatchBindings s space pat = totalMatchBindings fuel s space pat)
    (hEval :
      ∀ (sess : Session) (bs : Bindings),
        referenceMatchEvalMatchedTemplate s sess (matchTemplateAfterBindings bs tmpl) =
          totalMatchEvalMatchedTemplate fuel s sess (matchTemplateAfterBindings bs tmpl)) :
    referenceMatchIntrinsicResult s space pat tmpl =
      totalMatchIntrinsicResult fuel s space pat tmpl := by
  unfold referenceMatchIntrinsicResult totalMatchIntrinsicResult
  apply Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic_eq_of_evalMatchedTemplate_agreement
  · exact hBindings
  · intro bs term
    rfl
  · intro sess
    rfl
  · intro sess bs
    simpa [matchTemplateAfterBindings, referenceMatchEvalMatchedTemplate, totalMatchEvalMatchedTemplate] using
      hEval sess bs

/-- Stronger corollary of the bindingwise theorem: agreement on all substituted
    templates implies intrinsic `match` agreement. -/
theorem referenceMatchIntrinsicResult_eq_total_of_evalMatchedTemplate_agreement
    (fuel : Nat) (s : Session) (space pat tmpl : Pattern)
    (hBindings : referenceMatchBindings s space pat = totalMatchBindings fuel s space pat)
    (hEval :
      ∀ (sess : Session) (tmplSub : Pattern),
        referenceMatchEvalMatchedTemplate s sess tmplSub =
          totalMatchEvalMatchedTemplate fuel s sess tmplSub) :
    referenceMatchIntrinsicResult s space pat tmpl =
      totalMatchIntrinsicResult fuel s space pat tmpl := by
  apply referenceMatchIntrinsicResult_eq_total_of_bindingwise_evalMatchedTemplate_agreement
  · exact hBindings
  intro sess bs
  exact hEval sess (matchTemplateAfterBindings bs tmpl)

/-- Corollary of the compositional `match` theorem from direct evaluator agreement.
    This is the first theorem to target when lifting fragment-local equality from
    template evaluation up to the intrinsic `match` boundary. -/
theorem referenceMatchIntrinsicResult_eq_total_of_eval_agreement
    (fuel : Nat) (s : Session) (space pat tmpl : Pattern)
    (hBindings : referenceMatchBindings s space pat = totalMatchBindings fuel s space pat)
    (hEval :
      ∀ (sess : Session) (term : Pattern),
        referenceEvalWithStateCore sess term =
          referenceEvalWithStateCoreN fuel sess term) :
    referenceMatchIntrinsicResult s space pat tmpl =
      totalMatchIntrinsicResult fuel s space pat tmpl := by
  apply referenceMatchIntrinsicResult_eq_total_of_bindingwise_evalMatchedTemplate_agreement
  · exact hBindings
  intro sess bs
  exact
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate_eq_of_eval_agreement
      (referenceSpaceEvalInterface s)
      (referenceSpaceEvalInterfaceN fuel s)
      sess (matchTemplateAfterBindings bs tmpl)
      (by
        intro sess' term
        simpa [referenceSpaceEvalInterface, referenceSpaceEvalInterfaceN] using
          hEval sess' term)

/-- Direct matched-template equality for already-substituted `get-atoms` terms.
    This isolates the non-`Expr` case of `evalMatchedTemplate` and is the smallest
    reusable step toward discharging the template-equality hypothesis in the first
    compositional `match` theorem. -/
theorem referenceMatchEvalMatchedTemplate_getAtoms_eq_total_of_eval_agreement
    (fuel : Nat) (s0 sess : Session) (spaceExpr : Pattern)
    (hEval :
      referenceEvalWithStateCore sess (.apply "get-atoms" [spaceExpr]) =
        referenceEvalWithStateCoreN fuel sess (.apply "get-atoms" [spaceExpr])) :
    referenceMatchEvalMatchedTemplate s0 sess (.apply "get-atoms" [spaceExpr]) =
      totalMatchEvalMatchedTemplate fuel s0 sess (.apply "get-atoms" [spaceExpr]) := by
  simpa [referenceMatchEvalMatchedTemplate, totalMatchEvalMatchedTemplate,
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate] using hEval

/-- Unary evaluator-agreement contract for the `get-atoms` head. -/
abbrev GetAtomsUnaryEvalAgreement (fuel : Nat) : Prop :=
  ∀ (sess : Session) (spaceArg : Pattern),
    referenceEvalWithStateCore sess (.apply "get-atoms" [spaceArg]) =
      referenceEvalWithStateCoreN fuel sess (.apply "get-atoms" [spaceArg])

/-- Unary evaluator-agreement contract for the `get-atoms!` head. -/
abbrev GetAtomsBangUnaryEvalAgreement (fuel : Nat) : Prop :=
  ∀ (sess : Session) (spaceArg : Pattern),
    referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceArg]) =
      referenceEvalWithStateCoreN fuel sess (.apply "get-atoms!" [spaceArg])

/-- Constrained unary evaluator-agreement contract for `get-atoms`,
    parameterized by a fragment predicate over session/template argument pairs. -/
abbrev GetAtomsUnaryEvalAgreementOn
    (fuel : Nat) (Q : Session → Pattern → Prop) : Prop :=
  ∀ (sess : Session) (spaceArg : Pattern),
    Q sess spaceArg →
      referenceEvalWithStateCore sess (.apply "get-atoms" [spaceArg]) =
        referenceEvalWithStateCoreN fuel sess (.apply "get-atoms" [spaceArg])

/-- Constrained unary evaluator-agreement contract for `get-atoms!`,
    parameterized by a fragment predicate over session/template argument pairs. -/
abbrev GetAtomsBangUnaryEvalAgreementOn
    (fuel : Nat) (Q : Session → Pattern → Prop) : Prop :=
  ∀ (sess : Session) (spaceArg : Pattern),
    Q sess spaceArg →
      referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceArg]) =
        referenceEvalWithStateCoreN fuel sess (.apply "get-atoms!" [spaceArg])

/-- If `sess.maxNodes = 0` and `fuel > 0`, both live-reference and fuel-indexed
    total-reference evaluators immediately return the pending root term, so they
    agree on all inputs. -/
theorem referenceEvalWithStateCore_eq_N_of_maxNodes_zero
    (fuel : Nat) (hFuel : fuel ≠ 0)
    (sess : Session) (term : Pattern)
    (hNodes : sess.maxNodes = 0) :
    referenceEvalWithStateCore sess term =
      referenceEvalWithStateCoreN fuel sess term := by
  cases fuel with
  | zero =>
      contradiction
  | succ n =>
      simp [referenceEvalWithStateCore, referenceEvalWithStateCoreN,
        Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore] at *
      have hMaxRef : referenceEvalInterface.maxNodes sess = 0 := by
        simpa [referenceEvalInterface] using hNodes
      rw [hMaxRef]
      rw [hNodes]
      simp [Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful]

/-- First proved constrained fragment instance for `get-atoms` unary evaluator
    agreement: sessions with `maxNodes = 0`. -/
theorem getAtomsUnaryEvalAgreementOn_zeroMaxNodes
    (fuel : Nat) (hFuel : fuel ≠ 0) :
    GetAtomsUnaryEvalAgreementOn fuel (fun sess _spaceArg => sess.maxNodes = 0) := by
  intro sess spaceArg hNodes
  exact referenceEvalWithStateCore_eq_N_of_maxNodes_zero
    (fuel := fuel) hFuel sess (.apply "get-atoms" [spaceArg]) hNodes

/-- First proved constrained fragment instance for `get-atoms!` unary evaluator
    agreement: sessions with `maxNodes = 0`. -/
theorem getAtomsBangUnaryEvalAgreementOn_zeroMaxNodes
    (fuel : Nat) (hFuel : fuel ≠ 0) :
    GetAtomsBangUnaryEvalAgreementOn fuel (fun sess _spaceArg => sess.maxNodes = 0) := by
  intro sess spaceArg hNodes
  exact referenceEvalWithStateCore_eq_N_of_maxNodes_zero
    (fuel := fuel) hFuel sess (.apply "get-atoms!" [spaceArg]) hNodes

@[simp] private theorem referenceEvalAuxStateful_pending_nil
    (iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session)
    (sess : Session) (fuel : Nat) (normals : List Pattern) :
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful iface sess fuel [] normals =
      (sess, normals.reverse) := by
  induction fuel with
  | zero =>
      simp [Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful]
  | succ fuel ih =>
      simp [Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful,
        Algorithms.MeTTa.Simple.Backend.ReferenceEval.stepAux]

/-- If `sess.maxSteps = 0` and `fuel > 0`, both evaluators stop at depth 0 before
    intrinsic reduction, so they agree on `get-atoms` root terms. -/
theorem referenceEvalWithStateCore_getAtoms_eq_N_of_maxSteps_zero
    (fuel : Nat) (hFuel : fuel ≠ 0)
    (sess : Session) (spaceArg : Pattern)
    (hSteps : sess.maxSteps = 0) :
    referenceEvalWithStateCore sess (.apply "get-atoms" [spaceArg]) =
      referenceEvalWithStateCoreN fuel sess (.apply "get-atoms" [spaceArg]) := by
  cases fuel with
  | zero =>
      contradiction
  | succ n =>
      cases hNodes : sess.maxNodes with
      | zero =>
          unfold referenceEvalWithStateCore referenceEvalWithStateCoreN
          simp [referenceEvalInterface,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful, hNodes]
      | succ m =>
          unfold referenceEvalWithStateCore referenceEvalWithStateCoreN
          simp [referenceEvalInterface,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.stepAux,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects.eq_def,
            hSteps, hNodes]

/-- Stronger constrained fragment instance for `get-atoms` unary evaluator
    agreement: sessions with `maxSteps = 0`. -/
theorem getAtomsUnaryEvalAgreementOn_zeroMaxSteps
    (fuel : Nat) (hFuel : fuel ≠ 0) :
    GetAtomsUnaryEvalAgreementOn fuel (fun sess _spaceArg => sess.maxSteps = 0) := by
  intro sess spaceArg hSteps
  exact referenceEvalWithStateCore_getAtoms_eq_N_of_maxSteps_zero
    (fuel := fuel) hFuel sess spaceArg hSteps

/-- If `sess.maxSteps = 0` and `fuel > 0`, both evaluators stop at depth 0 before
    intrinsic reduction, so they agree on `get-atoms!` root terms. -/
theorem referenceEvalWithStateCore_getAtomsBang_eq_N_of_maxSteps_zero
    (fuel : Nat) (hFuel : fuel ≠ 0)
    (sess : Session) (spaceArg : Pattern)
    (hSteps : sess.maxSteps = 0) :
    referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceArg]) =
      referenceEvalWithStateCoreN fuel sess (.apply "get-atoms!" [spaceArg]) := by
  cases fuel with
  | zero =>
      contradiction
  | succ n =>
      cases hNodes : sess.maxNodes with
      | zero =>
          unfold referenceEvalWithStateCore referenceEvalWithStateCoreN
          simp [referenceEvalInterface,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful, hNodes]
      | succ m =>
          unfold referenceEvalWithStateCore referenceEvalWithStateCoreN
          simp [referenceEvalInterface,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.stepAux,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects.eq_def,
            hSteps, hNodes]

/-- Stronger constrained fragment instance for `get-atoms!` unary evaluator
    agreement: sessions with `maxSteps = 0`. -/
theorem getAtomsBangUnaryEvalAgreementOn_zeroMaxSteps
    (fuel : Nat) (hFuel : fuel ≠ 0) :
    GetAtomsBangUnaryEvalAgreementOn fuel (fun sess _spaceArg => sess.maxSteps = 0) := by
  intro sess spaceArg hSteps
  exact referenceEvalWithStateCore_getAtomsBang_eq_N_of_maxSteps_zero
    (fuel := fuel) hFuel sess spaceArg hSteps

/-- Root intrinsic agreement for `get-atoms`: once the fuel-indexed intrinsic kernel
    is active (`fuel > 0`), the live-reference and total-reference branches reduce to
    the same `SpaceOps.getAtoms` call. -/
theorem intrinsicStateful_getAtoms_eq_referenceIntrinsicStatefulN_of_pos
    (fuel : Nat) (hFuel : fuel ≠ 0)
    (sess : Session) (spaceArg : Pattern) :
    intrinsicStateful sess (.apply "get-atoms" [spaceArg]) =
      referenceIntrinsicStatefulN fuel sess (.apply "get-atoms" [spaceArg]) := by
  cases fuel with
  | zero =>
      contradiction
  | succ n =>
      unfold intrinsicStateful
      unfold referenceIntrinsicStatefulN
      simpa using
        intrinsicGetAtomsResultWithEval_eval_irrelevant
          evalWithStateCore
          (fun s term => referenceEvalWithStateCoreN n s term)
          sess spaceArg

/-- Root intrinsic agreement for `get-atoms!`: once the fuel-indexed intrinsic kernel
    is active (`fuel > 0`), the live-reference and total-reference branches reduce to
    the same `SpaceOps.getAtoms` call. -/
theorem intrinsicStateful_getAtomsBang_eq_referenceIntrinsicStatefulN_of_pos
    (fuel : Nat) (hFuel : fuel ≠ 0)
    (sess : Session) (spaceArg : Pattern) :
    intrinsicStateful sess (.apply "get-atoms!" [spaceArg]) =
      referenceIntrinsicStatefulN fuel sess (.apply "get-atoms!" [spaceArg]) := by
  cases fuel with
  | zero =>
      contradiction
  | succ n =>
      unfold intrinsicStateful
      unfold referenceIntrinsicStatefulN
      simpa using
        intrinsicGetAtomsResultWithEval_eval_irrelevant
          evalWithStateCore
          (fun s term => referenceEvalWithStateCoreN n s term)
          sess spaceArg

/-- The fuel-indexed intrinsic evaluator preserves session state on `get-atoms!`:
    returns `some (s, facts)` for some `facts`. -/
private theorem referenceIntrinsicStatefulN_getAtomsBang_state_eq
    (fuel : Nat) (hFuel : fuel ≠ 0) (s : Session) (space : Pattern) :
    ∃ facts, referenceIntrinsicStatefulN fuel s (.apply "get-atoms!" [space]) = some (s, facts) := by
  cases fuel with
  | zero => contradiction
  | succ n =>
      unfold referenceIntrinsicStatefulN
      simpa using
        intrinsicGetAtomsResultWithEval_state_eq
          (fun s term => referenceEvalWithStateCoreN n s term) s space

/-- One-step evaluator agreement for `get-atoms` at `maxNodes = 1`, factored through
    a local intrinsic-agreement hypothesis on the root term. This isolates the
    remaining hard subproof from the evaluator plumbing. -/
theorem referenceEvalWithStateCore_getAtoms_eq_N_of_maxNodes_one_of_intrinsic_agreement
    (fuel : Nat) (hFuel : 1 < fuel)
    (sess : Session) (spaceArg : Pattern)
    (hNodes : sess.maxNodes = 1)
    (hIntr :
      intrinsicStateful sess (.apply "get-atoms" [spaceArg]) =
        referenceIntrinsicStatefulN (fuel - 1) sess (.apply "get-atoms" [spaceArg])) :
    referenceEvalWithStateCore sess (.apply "get-atoms" [spaceArg]) =
      referenceEvalWithStateCoreN fuel sess (.apply "get-atoms" [spaceArg]) := by
  cases fuel with
  | zero =>
      contradiction
  | succ n =>
      cases n with
      | zero =>
          contradiction
      | succ k =>
          have hIntr' :
              intrinsicStateful sess (.apply "get-atoms" [spaceArg]) =
                referenceIntrinsicStatefulN (k + 1) sess (.apply "get-atoms" [spaceArg]) := by
            simpa using hIntr
          unfold referenceEvalWithStateCore referenceEvalWithStateCoreN
          simp [referenceEvalInterface,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.stepAux,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects.eq_def,
            hNodes, hIntr']

/-- One-step evaluator agreement for `get-atoms` at `maxNodes = 1`.
    The hard intrinsic subproof is now discharged by the transparent `get-atoms`
    waist shared between the live reference wrapper and the total kernel. -/
theorem referenceEvalWithStateCore_getAtoms_eq_N_of_maxNodes_one
    (fuel : Nat) (hFuel : 1 < fuel)
    (sess : Session) (spaceArg : Pattern)
    (hNodes : sess.maxNodes = 1) :
    referenceEvalWithStateCore sess (.apply "get-atoms" [spaceArg]) =
      referenceEvalWithStateCoreN fuel sess (.apply "get-atoms" [spaceArg]) := by
  have hFuelPredPos : 0 < fuel - 1 := by
    omega
  have hIntr :
      intrinsicStateful sess (.apply "get-atoms" [spaceArg]) =
        referenceIntrinsicStatefulN (fuel - 1) sess (.apply "get-atoms" [spaceArg]) := by
    exact
      intrinsicStateful_getAtoms_eq_referenceIntrinsicStatefulN_of_pos
        (fuel := fuel - 1) (Nat.ne_of_gt hFuelPredPos) sess spaceArg
  exact
    referenceEvalWithStateCore_getAtoms_eq_N_of_maxNodes_one_of_intrinsic_agreement
      fuel hFuel sess spaceArg hNodes hIntr

/-- Stronger constrained fragment instance for `get-atoms` unary evaluator
    agreement: sessions with `maxNodes = 1`. -/
theorem getAtomsUnaryEvalAgreementOn_oneMaxNode
    (fuel : Nat) (hFuel : 1 < fuel) :
    GetAtomsUnaryEvalAgreementOn fuel (fun sess _spaceArg => sess.maxNodes = 1) := by
  intro sess spaceArg hNodes
  exact
    referenceEvalWithStateCore_getAtoms_eq_N_of_maxNodes_one
      (fuel := fuel) hFuel sess spaceArg hNodes

/-- One-step evaluator agreement for `get-atoms!` at `maxNodes = 1`, factored through
    a local intrinsic-agreement hypothesis on the root term. This isolates the
    remaining hard subproof from the evaluator plumbing. -/
theorem referenceEvalWithStateCore_getAtomsBang_eq_N_of_maxNodes_one_of_intrinsic_agreement
    (fuel : Nat) (hFuel : 1 < fuel)
    (sess : Session) (spaceArg : Pattern)
    (hNodes : sess.maxNodes = 1)
    (hIntr :
      intrinsicStateful sess (.apply "get-atoms!" [spaceArg]) =
        referenceIntrinsicStatefulN (fuel - 1) sess (.apply "get-atoms!" [spaceArg])) :
    referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceArg]) =
      referenceEvalWithStateCoreN fuel sess (.apply "get-atoms!" [spaceArg]) := by
  cases fuel with
  | zero =>
      contradiction
  | succ n =>
      cases n with
      | zero =>
          contradiction
      | succ k =>
          have hIntr' :
              intrinsicStateful sess (.apply "get-atoms!" [spaceArg]) =
                referenceIntrinsicStatefulN (k + 1) sess (.apply "get-atoms!" [spaceArg]) := by
            simpa using hIntr
          unfold referenceEvalWithStateCore referenceEvalWithStateCoreN
          simp [referenceEvalInterface,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.stepAux,
            Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects.eq_def,
            hNodes, hIntr']

/-- One-step evaluator agreement for `get-atoms!` at `maxNodes = 1`.
    The hard intrinsic subproof is now discharged by the transparent `get-atoms`
    waist shared between the live reference wrapper and the total kernel. -/
theorem referenceEvalWithStateCore_getAtomsBang_eq_N_of_maxNodes_one
    (fuel : Nat) (hFuel : 1 < fuel)
    (sess : Session) (spaceArg : Pattern)
    (hNodes : sess.maxNodes = 1) :
    referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceArg]) =
      referenceEvalWithStateCoreN fuel sess (.apply "get-atoms!" [spaceArg]) := by
  have hFuelPredPos : 0 < fuel - 1 := by
    omega
  have hIntr :
      intrinsicStateful sess (.apply "get-atoms!" [spaceArg]) =
        referenceIntrinsicStatefulN (fuel - 1) sess (.apply "get-atoms!" [spaceArg]) := by
    exact
      intrinsicStateful_getAtomsBang_eq_referenceIntrinsicStatefulN_of_pos
        (fuel := fuel - 1) (Nat.ne_of_gt hFuelPredPos) sess spaceArg
  exact
    referenceEvalWithStateCore_getAtomsBang_eq_N_of_maxNodes_one_of_intrinsic_agreement
      fuel hFuel sess spaceArg hNodes hIntr

/-- The fuel-indexed evaluator preserves session state on `get-atoms!`
    when `maxNodes = 1`.  The evaluation loop runs exactly one `stepAux`
    (fuel drops from 1 to 0), and both `runNestedEffects` (passthrough)
    and `intrinsicStateful` (via `getAtoms`) preserve the session. -/
theorem referenceEvalWithStateCoreN_getAtomsBang_state_eq_self_of_maxNodes_one
    (fuel : Nat) (hFuel : 1 < fuel)
    (sess : Session) (spaceArg : Pattern)
    (hNodes : sess.maxNodes = 1) :
    (referenceEvalWithStateCoreN fuel sess (.apply "get-atoms!" [spaceArg])).1 = sess := by
  cases fuel with
  | zero => omega
  | succ n =>
      cases n with
      | zero => omega
      | succ k =>
          -- Precondition 2: intrinsicStatefulN returns (sess, facts)
          obtain ⟨facts, hIntrEq⟩ :=
            referenceIntrinsicStatefulN_getAtomsBang_state_eq (k + 1) (by omega) sess spaceArg
          -- Unfold one level of referenceEvalWithStateCoreN to expose evalWithStateCore iface
          unfold referenceEvalWithStateCoreN
          -- Precondition 1: runNestedEffects is passthrough for get-atoms!
          have hRNE : Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
              { maxNodes := fun s => s.maxNodes, maxSteps := fun s => s.maxSteps,
                runNestedEffects := fun s isRoot p term =>
                  referenceRunNestedEffectsN (k + 1) s isRoot p term,
                intrinsicStateful := fun s term => referenceIntrinsicStatefulN (k + 1) s term,
                isEagerCallableHead := isEagerCallableHead, step := step,
                enqueueNext := enqueueNext, insertUnique := insertUnique,
                dedupPatterns := dedupPatterns }
              sess true false (.apply "get-atoms!" [spaceArg]) =
              (sess, .apply "get-atoms!" [spaceArg], false) := by
            simp [Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects]
          -- Apply the generic framework lemma
          exact Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore_s_eq_of_passthrough_one_step
            _ sess (.apply "get-atoms!" [spaceArg]) hNodes
            (.apply "get-atoms!" [spaceArg]) false facts hRNE hIntrEq

/-- On the first non-degenerate fragment `maxNodes = 1`, evaluating a root
    `get-atoms!` term leaves the session unchanged.  Transfers through the
    partial-to-total bridge and the fuel-indexed state-preservation proof. -/
theorem referenceEvalWithStateCore_getAtomsBang_state_eq_self_of_maxNodes_one
    (sess : Session) (spaceArg : Pattern)
    (hNodes : sess.maxNodes = 1) :
    (referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceArg])).1 = sess := by
  have hEq :=
    referenceEvalWithStateCore_getAtomsBang_eq_N_of_maxNodes_one
      (fuel := 2) (by omega) sess spaceArg hNodes
  rw [hEq]
  exact referenceEvalWithStateCoreN_getAtomsBang_state_eq_self_of_maxNodes_one
    2 (by omega) sess spaceArg hNodes

/-- Stronger constrained fragment instance for `get-atoms!` unary evaluator
    agreement: sessions with `maxNodes = 1`. -/
theorem getAtomsBangUnaryEvalAgreementOn_oneMaxNode
    (fuel : Nat) (hFuel : 1 < fuel) :
    GetAtomsBangUnaryEvalAgreementOn fuel (fun sess _spaceArg => sess.maxNodes = 1) := by
  intro sess spaceArg hNodes
  exact
    referenceEvalWithStateCore_getAtomsBang_eq_N_of_maxNodes_one
      (fuel := fuel) hFuel sess spaceArg hNodes

/-- Lift a unary `get-atoms` evaluator-agreement hypothesis to the exact
    substituted-template `hEval` shape used by compositional `match` adequacy. -/
theorem referenceMatch_getAtomsTemplate_hEval_of_unary_eval_agreement
    (fuel : Nat) (spaceExpr : Pattern)
    (hEvalUnary : GetAtomsUnaryEvalAgreement fuel) :
    ∀ (sess : Session) (bs : Bindings),
      referenceEvalWithStateCore sess
          (.apply "get-atoms" [matchTemplateAfterBindings bs spaceExpr]) =
        referenceEvalWithStateCoreN fuel sess
          (.apply "get-atoms" [matchTemplateAfterBindings bs spaceExpr]) := by
  intro sess bs
  exact hEvalUnary sess (matchTemplateAfterBindings bs spaceExpr)

/-- First template-family specialization for compositional `match` adequacy:
    if substituted `get-atoms` templates agree at the `evalMatchedTemplate`
    boundary, then the surrounding `match` intrinsic agrees. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_evalMatchedTemplate_agreement
    (fuel : Nat) (s : Session) (space pat spaceExpr : Pattern)
    (hBindings : referenceMatchBindings s space pat = totalMatchBindings fuel s space pat)
    (hEval :
      ∀ (sess : Session) (bs : Bindings),
        referenceMatchEvalMatchedTemplate s sess
            (matchTemplateAfterBindings bs (.apply "get-atoms" [spaceExpr])) =
          totalMatchEvalMatchedTemplate fuel s sess
            (matchTemplateAfterBindings bs (.apply "get-atoms" [spaceExpr]))) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms" [spaceExpr]) := by
  apply referenceMatchIntrinsicResult_eq_total_of_bindingwise_evalMatchedTemplate_agreement
  · exact hBindings
  intro sess bs
  exact hEval sess bs

/-- `get-atoms`-templated compositional `match` adequacy from direct evaluator
    equality on the already-substituted template term. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_eval_agreement
    (fuel : Nat) (s : Session) (space pat spaceExpr : Pattern)
    (hBindings : referenceMatchBindings s space pat = totalMatchBindings fuel s space pat)
    (hEval :
      ∀ (sess : Session) (bs : Bindings),
        referenceEvalWithStateCore sess
            (.apply "get-atoms" [matchTemplateAfterBindings bs spaceExpr]) =
          referenceEvalWithStateCoreN fuel sess
            (.apply "get-atoms" [matchTemplateAfterBindings bs spaceExpr])) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms" [spaceExpr]) := by
  apply referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_evalMatchedTemplate_agreement
  · exact hBindings
  · intro sess bs
    simpa [matchTemplateAfterBindings_getAtoms] using
      (referenceMatchEvalMatchedTemplate_getAtoms_eq_total_of_eval_agreement
        fuel s sess (matchTemplateAfterBindings bs spaceExpr) (hEval sess bs))

/-- Practical `get-atoms`-template specialization: the binding-enumeration side
    is discharged automatically from `referenceMatchBindings_eq_totalMatchBindings`. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_eval_agreement_autoBindings
    (fuel : Nat) (s : Session) (space pat spaceExpr : Pattern)
    (hEval :
      ∀ (sess : Session) (bs : Bindings),
        referenceEvalWithStateCore sess
            (.apply "get-atoms" [matchTemplateAfterBindings bs spaceExpr]) =
          referenceEvalWithStateCoreN fuel sess
            (.apply "get-atoms" [matchTemplateAfterBindings bs spaceExpr])) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms" [spaceExpr]) := by
  exact
    referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_eval_agreement
      (fuel := fuel) (s := s) (space := space) (pat := pat) (spaceExpr := spaceExpr)
      (hBindings := referenceMatchBindings_eq_totalMatchBindings fuel s space pat)
      hEval

/-- Unary-entry variant for `get-atoms` templates:
    supply evaluator agreement per substituted space argument, and the theorem
    discharges the `bs`-indexed `hEval` plumbing automatically. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_unary_eval_agreement_autoBindings
    (fuel : Nat) (s : Session) (space pat spaceExpr : Pattern)
    (hEvalUnary : GetAtomsUnaryEvalAgreement fuel) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms" [spaceExpr]) := by
  exact
    referenceMatchIntrinsicResult_eq_total_of_getAtomsTemplate_eval_agreement_autoBindings
      (fuel := fuel) (s := s) (space := space) (pat := pat) (spaceExpr := spaceExpr)
      (referenceMatch_getAtomsTemplate_hEval_of_unary_eval_agreement
        (fuel := fuel) (spaceExpr := spaceExpr) hEvalUnary)

/-- Direct matched-template equality for already-substituted `get-atoms!` terms. -/
theorem referenceMatchEvalMatchedTemplate_getAtomsBang_eq_total_of_eval_agreement
    (fuel : Nat) (s0 sess : Session) (spaceExpr : Pattern)
    (hEval :
      referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceExpr]) =
        referenceEvalWithStateCoreN fuel sess (.apply "get-atoms!" [spaceExpr])) :
    referenceMatchEvalMatchedTemplate s0 sess (.apply "get-atoms!" [spaceExpr]) =
      totalMatchEvalMatchedTemplate fuel s0 sess (.apply "get-atoms!" [spaceExpr]) := by
  simpa [referenceMatchEvalMatchedTemplate, totalMatchEvalMatchedTemplate,
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate] using hEval

/-- At the `evalMatchedTemplate` waist, `get-atoms!` stays in the same session on the
    first non-degenerate fragment `maxNodes = 1`. -/
theorem referenceMatchEvalMatchedTemplate_getAtomsBang_state_eq_self_of_maxNodes_one
    (s0 sess : Session) (spaceExpr : Pattern)
    (hNodes : sess.maxNodes = 1) :
    (referenceMatchEvalMatchedTemplate s0 sess (.apply "get-atoms!" [spaceExpr])).1 = sess := by
  simpa [referenceMatchEvalMatchedTemplate,
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate] using
    referenceEvalWithStateCore_getAtomsBang_state_eq_self_of_maxNodes_one
      sess spaceExpr hNodes

/-- The fuel-indexed matched-template evaluator has the same one-step state
    invariance for `get-atoms!` on `maxNodes = 1`. -/
theorem totalMatchEvalMatchedTemplate_getAtomsBang_state_eq_self_of_maxNodes_one
    (fuel : Nat) (hFuel : 1 < fuel)
    (s0 sess : Session) (spaceExpr : Pattern)
    (hNodes : sess.maxNodes = 1) :
    (totalMatchEvalMatchedTemplate fuel s0 sess (.apply "get-atoms!" [spaceExpr])).1 = sess := by
  simpa [totalMatchEvalMatchedTemplate,
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate] using
    referenceEvalWithStateCoreN_getAtomsBang_state_eq_self_of_maxNodes_one
      fuel hFuel sess spaceExpr hNodes

/-- First non-degenerate compositional `match` adequacy theorem for `get-atoms!`
    templates. The proof is specialized to the `maxNodes = 1` fragment so the
    threaded session never leaves the fragment while the bindings fold is running. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_on_oneMaxNode
    (fuel : Nat) (hFuel : 1 < fuel)
    (s : Session) (space pat spaceExpr : Pattern)
    (hNodes : s.maxNodes = 1)
    (_hStateRoot :
      ∀ (sess : Session) (spaceArg : Pattern),
        sess.maxNodes = 1 →
          (referenceEvalWithStateCore sess (.apply "get-atoms!" [spaceArg])).1 = sess) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms!" [spaceExpr]) := by
  unfold referenceMatchIntrinsicResult totalMatchIntrinsicResult
  unfold Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
  have hBindings :
      Algorithms.MeTTa.Simple.Semantics.SpaceOps.findBindingsInSpace
          (referenceSpaceEvalInterface s) spacePolicy s space pat =
        Algorithms.MeTTa.Simple.Semantics.SpaceOps.findBindingsInSpace
          (referenceSpaceEvalInterfaceN fuel s) spacePolicy s space pat := by
    simpa [referenceMatchBindings, totalMatchBindings] using
      referenceMatchBindings_eq_totalMatchBindings fuel s space pat
  rw [hBindings]
  let bindings :=
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.findBindingsInSpace
      (referenceSpaceEvalInterfaceN fuel s) spacePolicy s space pat
  let f₁ := fun (accState : Session × List Pattern) bs =>
    let sess := accState.1
    let collected := accState.2
    let tmplSub := referenceSpaceEvalInterface s |>.applyBindings bs (.apply "get-atoms!" [spaceExpr])
    let (sess', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate
      (referenceSpaceEvalInterface s) sess tmplSub
    (sess', out.reverse ++ collected)
  let f₂ := fun (accState : Session × List Pattern) bs =>
    let sess := accState.1
    let collected := accState.2
    let tmplSub := referenceSpaceEvalInterfaceN fuel s |>.applyBindings bs (.apply "get-atoms!" [spaceExpr])
    let (sess', out) := Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate
      (referenceSpaceEvalInterfaceN fuel s) sess tmplSub
    (sess', out.reverse ++ collected)
  have hFold :
      ∀ (bsList : List Bindings) (sess : Session) (collected : List Pattern),
        sess.maxNodes = 1 →
        bsList.foldl f₁ (sess, collected) = bsList.foldl f₂ (sess, collected) := by
    intro bsList
    induction bsList with
    | nil =>
        intro sess collected _hSess
        rfl
    | cons bs rest ih =>
        intro sess collected hSess
        simp only [List.foldl_cons]
        have hEval :
            referenceMatchEvalMatchedTemplate s sess
                (matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr])) =
              totalMatchEvalMatchedTemplate fuel s sess
                (matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr])) := by
          have hUnary :
              referenceEvalWithStateCore sess
                  (.apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr]) =
                referenceEvalWithStateCoreN fuel sess
                  (.apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr]) := by
            exact
              referenceEvalWithStateCore_getAtomsBang_eq_N_of_maxNodes_one
                (fuel := fuel) hFuel sess (matchTemplateAfterBindings bs spaceExpr) hSess
          simpa [matchTemplateAfterBindings_getAtomsBang] using
            (referenceMatchEvalMatchedTemplate_getAtomsBang_eq_total_of_eval_agreement
              (fuel := fuel) (s0 := s) (sess := sess)
              (spaceExpr := matchTemplateAfterBindings bs spaceExpr) hUnary)
        have hState₂ :
            (totalMatchEvalMatchedTemplate fuel s sess
                (matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr]))).1 = sess := by
          simpa [matchTemplateAfterBindings_getAtomsBang] using
            totalMatchEvalMatchedTemplate_getAtomsBang_state_eq_self_of_maxNodes_one
              fuel hFuel s sess (matchTemplateAfterBindings bs spaceExpr) hSess
        cases hOut₂ :
            totalMatchEvalMatchedTemplate fuel s sess
              (matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr])) with
        | mk sess' out =>
            have hSess' : sess' = sess := by
              simpa [hOut₂] using hState₂
            subst sess'
            have hOut₁ :
                referenceMatchEvalMatchedTemplate s sess
                  (matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr])) =
                (sess, out) := by
              simpa [hOut₂] using hEval
            have hOut₁' :
                Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate
                    (referenceSpaceEvalInterface s) sess
                    ((referenceSpaceEvalInterface s).applyBindings bs
                      (.apply "get-atoms!" [spaceExpr])) =
                  (sess, out) := by
              simpa [referenceMatchEvalMatchedTemplate, matchTemplateAfterBindings] using hOut₁
            have hOut₂' :
                Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchedTemplate
                    (referenceSpaceEvalInterfaceN fuel s) sess
                    ((referenceSpaceEvalInterfaceN fuel s).applyBindings bs
                      (.apply "get-atoms!" [spaceExpr])) =
                  (sess, out) := by
              simpa [totalMatchEvalMatchedTemplate, matchTemplateAfterBindings] using hOut₂
            have hStep₁ : f₁ (sess, collected) bs = (sess, out.reverse ++ collected) := by
              simp [f₁, hOut₁']
            have hStep₂ : f₂ (sess, collected) bs = (sess, out.reverse ++ collected) := by
              simp [f₂, hOut₂']
            rw [hStep₁, hStep₂]
            exact ih sess (out.reverse ++ collected) hSess
  have hFoldEq : bindings.foldl f₁ (s, []) = bindings.foldl f₂ (s, []) := by
    exact hFold bindings s [] hNodes
  let finish := fun (acc : Session × List Pattern) =>
    let sDyn := acc.1
    let outRev := acc.2
    let dynamicOut := outRev.reverse
    let builtinOut3 :=
      (sDyn.bundle.builtins.relation "spaceMatch"
        [pat, .apply "get-atoms!" [spaceExpr], .fvar "_out"]).filterMap fun row =>
          match row with
          | [_pat, _tmpl, out] => some out
          | _ => none
    (sDyn, dynamicOut ++ builtinOut3)
  simpa [finish, bindings, f₁, f₂, referenceSpaceEvalInterface, referenceSpaceEvalInterfaceN] using
    congrArg finish hFoldEq

/-- Lift a unary `get-atoms!` evaluator-agreement hypothesis to the exact
    substituted-template `hEval` shape used by compositional `match` adequacy. -/
theorem referenceMatch_getAtomsBangTemplate_hEval_of_unary_eval_agreement
    (fuel : Nat) (spaceExpr : Pattern)
    (hEvalUnary : GetAtomsBangUnaryEvalAgreement fuel) :
    ∀ (sess : Session) (bs : Bindings),
      referenceEvalWithStateCore sess
          (.apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr]) =
        referenceEvalWithStateCoreN fuel sess
          (.apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr]) := by
  intro sess bs
  exact hEvalUnary sess (matchTemplateAfterBindings bs spaceExpr)

/-- `get-atoms!` specialization for compositional `match` adequacy. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_evalMatchedTemplate_agreement
    (fuel : Nat) (s : Session) (space pat spaceExpr : Pattern)
    (hBindings : referenceMatchBindings s space pat = totalMatchBindings fuel s space pat)
    (hEval :
      ∀ (sess : Session) (bs : Bindings),
        referenceMatchEvalMatchedTemplate s sess
            (matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr])) =
          totalMatchEvalMatchedTemplate fuel s sess
            (matchTemplateAfterBindings bs (.apply "get-atoms!" [spaceExpr]))) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms!" [spaceExpr]) := by
  apply referenceMatchIntrinsicResult_eq_total_of_bindingwise_evalMatchedTemplate_agreement
  · exact hBindings
  intro sess bs
  exact hEval sess bs

/-- `get-atoms!`-templated compositional `match` adequacy from direct evaluator
    equality on the already-substituted template term. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_eval_agreement
    (fuel : Nat) (s : Session) (space pat spaceExpr : Pattern)
    (hBindings : referenceMatchBindings s space pat = totalMatchBindings fuel s space pat)
    (hEval :
      ∀ (sess : Session) (bs : Bindings),
        referenceEvalWithStateCore sess
            (.apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr]) =
          referenceEvalWithStateCoreN fuel sess
            (.apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr])) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms!" [spaceExpr]) := by
  apply referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_evalMatchedTemplate_agreement
  · exact hBindings
  · intro sess bs
    simpa [matchTemplateAfterBindings_getAtomsBang] using
      (referenceMatchEvalMatchedTemplate_getAtomsBang_eq_total_of_eval_agreement
        fuel s sess (matchTemplateAfterBindings bs spaceExpr) (hEval sess bs))

/-- Practical `get-atoms!`-template specialization: the binding-enumeration side
    is discharged automatically from `referenceMatchBindings_eq_totalMatchBindings`. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_eval_agreement_autoBindings
    (fuel : Nat) (s : Session) (space pat spaceExpr : Pattern)
    (hEval :
      ∀ (sess : Session) (bs : Bindings),
        referenceEvalWithStateCore sess
            (.apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr]) =
          referenceEvalWithStateCoreN fuel sess
            (.apply "get-atoms!" [matchTemplateAfterBindings bs spaceExpr])) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms!" [spaceExpr]) := by
  exact
    referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_eval_agreement
      (fuel := fuel) (s := s) (space := space) (pat := pat) (spaceExpr := spaceExpr)
      (hBindings := referenceMatchBindings_eq_totalMatchBindings fuel s space pat)
      hEval

/-- Unary-entry variant for `get-atoms!` templates:
    supply evaluator agreement per substituted space argument, and the theorem
    discharges the `bs`-indexed `hEval` plumbing automatically. -/
theorem referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_unary_eval_agreement_autoBindings
    (fuel : Nat) (s : Session) (space pat spaceExpr : Pattern)
    (hEvalUnary : GetAtomsBangUnaryEvalAgreement fuel) :
    referenceMatchIntrinsicResult s space pat (.apply "get-atoms!" [spaceExpr]) =
      totalMatchIntrinsicResult fuel s space pat (.apply "get-atoms!" [spaceExpr]) := by
  exact
    referenceMatchIntrinsicResult_eq_total_of_getAtomsBangTemplate_eval_agreement_autoBindings
      (fuel := fuel) (s := s) (space := space) (pat := pat) (spaceExpr := spaceExpr)
      (referenceMatch_getAtomsBangTemplate_hEval_of_unary_eval_agreement
        (fuel := fuel) (spaceExpr := spaceExpr) hEvalUnary)

private theorem referenceSpaceEvalInterfaceN_preservation
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1) :
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.Preservation
      (referenceSpaceEvalInterfaceN fuel s0) CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    setBundle_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1 :=
      hEvalCorePres s term hs
    have hState : (referenceEvalWithStateCoreN fuel s term).1 = s' := by
      simpa [referenceSpaceEvalInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s bundle hs
    exact compiledConsistent_withBundleCompiled s bundle

private theorem compiledConsistent_of_referenceAddAtomN
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s : Session} {space fact : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space fact).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom_preserves
      (referenceSpaceEvalInterfaceN fuel s0) CompiledConsistent
      (referenceSpaceEvalInterfaceN_preservation fuel s0 hEvalCorePres)
      spacePolicy s space fact hs

private theorem compiledConsistent_of_referenceRemoveAtomN
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s : Session} {space fact : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space fact).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom_preserves
      (referenceSpaceEvalInterfaceN fuel s0) CompiledConsistent
      (referenceSpaceEvalInterfaceN_preservation fuel s0 hEvalCorePres)
      spacePolicy s space fact hs

private theorem compiledConsistent_of_referenceRemoveAllAtomsN
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s : Session} {space echo : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space echo).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms_preserves
      (referenceSpaceEvalInterfaceN fuel s0) CompiledConsistent
      (referenceSpaceEvalInterfaceN_preservation fuel s0 hEvalCorePres)
      spacePolicy s space echo hs

private theorem compiledConsistent_of_referenceGetAtomsN
    (fuel : Nat) (s0 : Session)
    {s : Session} {space : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms_preserves
      (referenceSpaceEvalInterfaceN fuel s0) CompiledConsistent
      spacePolicy s space hs

private theorem compiledConsistent_of_referenceAddAtomN_result
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {space fact : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space fact = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceAddAtomN
      (fuel := fuel) (s0 := s0) (hEvalCorePres := hEvalCorePres)
      (s := s) (space := space) (fact := fact) hs
  simpa [hEval] using hCC

private theorem compiledConsistent_of_referenceRemoveAtomN_result
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {space fact : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space fact = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceRemoveAtomN
      (fuel := fuel) (s0 := s0) (hEvalCorePres := hEvalCorePres)
      (s := s) (space := space) (fact := fact) hs
  simpa [hEval] using hCC

private theorem compiledConsistent_of_referenceRemoveAllAtomsN_result
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {space echo : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space echo = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceRemoveAllAtomsN
      (fuel := fuel) (s0 := s0) (hEvalCorePres := hEvalCorePres)
      (s := s) (space := space) (echo := echo) hs
  simpa [hEval] using hCC

private theorem compiledConsistent_of_referenceGetAtomsN_result
    (fuel : Nat) (s0 : Session)
    {s s' : Session} {space : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceGetAtomsN
      (fuel := fuel) (s0 := s0) (s := s) (space := space) hs
  simpa [hEval] using hCC

private theorem compiledConsistent_of_referenceAddAtomN_conj
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {space fact : Pattern} {out : List Pattern}
    (hEval : (Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space fact).1 = s')
    (hOut : (Algorithms.MeTTa.Simple.Semantics.SpaceOps.addAtom
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space fact).2 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact
    compiledConsistent_of_referenceAddAtomN_result fuel s0 hEvalCorePres
      (Prod.ext hEval hOut) hs

private theorem compiledConsistent_of_referenceRemoveAtomN_conj
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {space fact : Pattern} {out : List Pattern}
    (hEval : (Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space fact).1 = s')
    (hOut : (Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAtom
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space fact).2 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact
    compiledConsistent_of_referenceRemoveAtomN_result fuel s0 hEvalCorePres
      (Prod.ext hEval hOut) hs

private theorem compiledConsistent_of_referenceRemoveAllAtomsN_conj
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {space echo : Pattern} {out : List Pattern}
    (hEval : (Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space echo).1 = s')
    (hOut : (Algorithms.MeTTa.Simple.Semantics.SpaceOps.removeAllAtoms
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space echo).2 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact
    compiledConsistent_of_referenceRemoveAllAtomsN_result fuel s0 hEvalCorePres
      (Prod.ext hEval hOut) hs

private theorem compiledConsistent_of_referenceGetAtomsN_conj
    (fuel : Nat) (s0 : Session)
    {s s' : Session} {space : Pattern} {out : List Pattern}
    (hEval : (Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space).1 = s')
    (hOut : (Algorithms.MeTTa.Simple.Semantics.SpaceOps.getAtoms
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space).2 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact
    compiledConsistent_of_referenceGetAtomsN_result fuel s0
      (Prod.ext hEval hOut) hs

private theorem compiledConsistent_of_referenceMatchIntrinsicN
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s : Session} {space pat tmpl : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space pat tmpl).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic_preserves
      (referenceSpaceEvalInterfaceN fuel s0) CompiledConsistent
      (referenceSpaceEvalInterfaceN_preservation fuel s0 hEvalCorePres)
      spacePolicy s space pat tmpl hs

private theorem compiledConsistent_of_referenceMatchIntrinsicN_result
    (fuel : Nat) (s0 : Session)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {space pat tmpl : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
        (referenceSpaceEvalInterfaceN fuel s0) spacePolicy s space pat tmpl = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceMatchIntrinsicN
      (fuel := fuel) (s0 := s0) (hEvalCorePres := hEvalCorePres)
      (s := s) (space := space) (pat := pat) (tmpl := tmpl) hs
  simpa [hEval] using hCC

-- Phase 3 preservation: atom-of uses referenceRunNestedEffectsN whose state preserves CC.
-- runNestedEffects_preserves_of_intrinsicStateful requires intrinsicStateful preservation.
private theorem compiledConsistent_of_referenceRunNestedEffectsN
    (fuel : Nat)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    (s : Session) (isRoot parentCallable : Bool) (term : Pattern)
    (hs : CompiledConsistent s) :
    CompiledConsistent (referenceRunNestedEffectsN fuel s isRoot parentCallable term).1 := by
  -- Unfold referenceRunNestedEffectsN to expose the concrete ReferenceEval.runNestedEffects call,
  -- then apply runNestedEffects_preserves_of_intrinsicStateful.
  simp only [referenceRunNestedEffectsN]
  exact
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects_preserves_of_intrinsicStateful
      _ CompiledConsistent
      (fun {s} {t} {s'} {out} hIntr hs0 => hIntrinsicPres s t s' out hIntr hs0)
      s isRoot parentCallable term hs

private theorem compiledConsistent_of_evalTupleBuildStep
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {acc : Session × List Pattern} {xs : List Pattern}
    (hAcc : CompiledConsistent acc.1) :
    CompiledConsistent
      (evalTupleBuildStepWith evalCallableApply isRuleCallableHead acc xs).1 := by
  cases acc with
  | mk sess outAcc =>
      cases xs with
      | nil =>
          simp [evalTupleBuildStepWith]
          simpa using hAcc
      | cons h tl =>
          simp [evalTupleBuildStepWith]
          by_cases hTry :
              (match h with
              | .apply "partial" _ => true
              | .apply "|->" _ => true
              | .lambda _ => true
              | .multiLambda _ _ => true
              | .fvar _ => true
              | .apply ctor _ => isRuleCallableHead sess ctor
              | _ => false)
          · simp [hTry]
            cases hCall : evalCallableApply sess h tl with
            | mk sess' out0 =>
                have hSess' : CompiledConsistent sess' :=
                  hEvalCallablePres sess h tl sess' out0 hCall hAcc
                cases out0 with
                | nil =>
                    simpa using hSess'
                | cons y ys =>
                    simpa using hSess'
          · simp [hTry]
            simpa using hAcc

private theorem compiledConsistent_foldl_evalTupleBuildStep
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    ∀ (combos : List (List Pattern)) (acc : Session × List Pattern),
      CompiledConsistent acc.1 →
      CompiledConsistent
        ((combos.foldl (evalTupleBuildStepWith evalCallableApply isRuleCallableHead) acc).1) := by
  intro combos
  induction combos with
  | nil =>
      intro acc hAcc
      simpa
  | cons xs rest ih =>
      intro acc hAcc
      have hStep :
          CompiledConsistent
            (evalTupleBuildStepWith evalCallableApply isRuleCallableHead acc xs).1 :=
        compiledConsistent_of_evalTupleBuildStep hEvalCallablePres hAcc
      simpa [List.foldl] using
        ih (evalTupleBuildStepWith evalCallableApply isRuleCallableHead acc xs) hStep

private theorem compiledConsistent_of_evalTupleBuilt
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern) (s' : Session) (out : List Pattern),
        evalCallableApply s fn args = (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    (s : Session) (combos : List (List Pattern))
    (hs : CompiledConsistent s) :
    CompiledConsistent
      (evalTupleBuiltWith evalCallableApply isRuleCallableHead s combos).1 := by
  simp [evalTupleBuiltWith]
  simpa using
    compiledConsistent_foldl_evalTupleBuildStep hEvalCallablePres combos (s, []) hs

private theorem compiledConsistent_of_evalTupleElems
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1) :
    ∀ (s : Session) (elems : List Pattern),
      CompiledConsistent s →
      CompiledConsistent
        (evalTupleElemsWith evalWithStateCore s elems).1 := by
  intro s elems hs
  induction elems generalizing s with
  | nil =>
      simp [evalTupleElemsWith]
      simpa using hs
  | cons e rest ih =>
      have hHead : CompiledConsistent (evalWithStateCore s e).1 :=
        hEvalCorePres s e hs
      cases hEvalHead : evalWithStateCore s e with
      | mk s1 headOut0 =>
          have hs1 : CompiledConsistent s1 := by
            simpa [hEvalHead] using hHead
          have hTail :
              CompiledConsistent (evalTupleElemsWith evalWithStateCore s1 rest).1 :=
            ih s1 hs1
          cases hEvalTail : evalTupleElemsWith evalWithStateCore s1 rest with
          | mk s2 tails =>
              have hs2 : CompiledConsistent s2 := by
                simpa [hEvalTail] using hTail
              simp [evalTupleElemsWith]
              simpa [hEvalHead, hEvalTail] using hs2

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
    (hTuple :
      evalTupleIntrinsicWith evalWithStateCore evalCallableApply isRuleCallableHead s elems = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hElems :
      CompiledConsistent (evalTupleElemsWith evalWithStateCore s elems).1 :=
    compiledConsistent_of_evalTupleElems hEvalCorePres s elems hs
  cases hEvalElems : evalTupleElemsWith evalWithStateCore s elems with
  | mk s1 combos =>
      have hs1 : CompiledConsistent s1 := by
        simpa [hEvalElems] using hElems
      have hBuilt :
          CompiledConsistent
            (evalTupleBuiltWith evalCallableApply isRuleCallableHead s1 combos).1 :=
        compiledConsistent_of_evalTupleBuilt hEvalCallablePres s1 combos hs1
      have hState :
          (evalTupleBuiltWith evalCallableApply isRuleCallableHead s1 combos).1 = s' := by
        have hState0 :
            (evalTupleIntrinsicWith evalWithStateCore evalCallableApply isRuleCallableHead s elems).1 = s' := by
          exact congrArg Prod.fst hTuple
        simp [evalTupleIntrinsicWith, hEvalElems] at hState0
        exact hState0
      simpa [hState] using hBuilt

private def pettaCoreInterface :
    Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Interface Session := {
  eval := evalWithStateCore
  evalDeterministic := referenceEvalDeterministicCore
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
  evalTupleIntrinsic := evalTupleIntrinsicWith evalWithStateCore evalCallableApply isRuleCallableHead
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

private theorem compiledConsistent_of_referenceEvalTupleBuildStep
    (fuel : Nat)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    {acc : Session × List Pattern} {xs : List Pattern}
    (hAcc : CompiledConsistent acc.1) :
    CompiledConsistent
      (evalTupleBuildStepWith
        (referenceEvalCallableApplyN fuel) isRuleCallableHead acc xs).1 := by
  cases acc with
  | mk sess outAcc =>
      cases xs with
      | nil =>
          simp [evalTupleBuildStepWith]
          simpa using hAcc
      | cons h tl =>
          simp [evalTupleBuildStepWith]
          by_cases hTry :
              (match h with
              | .apply "partial" _ => true
              | .apply "|->" _ => true
              | .lambda _ => true
              | .multiLambda _ _ => true
              | .fvar _ => true
              | .apply ctor _ => isRuleCallableHead sess ctor
              | _ => false)
          · simp [hTry]
            have hPres :
                CompiledConsistent (referenceEvalCallableApplyN fuel sess h tl).1 :=
              hEvalCallablePres sess h tl hAcc
            cases hCall : referenceEvalCallableApplyN fuel sess h tl with
            | mk sess' out0 =>
                have hSess' : CompiledConsistent sess' := by
                  simpa [hCall] using hPres
                cases out0 with
                | nil =>
                    simpa using hSess'
                | cons y ys =>
                    simpa using hSess'
          · simp [hTry]
            simpa using hAcc

private theorem compiledConsistent_foldl_referenceEvalTupleBuildStep
    (fuel : Nat)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1) :
    ∀ (combos : List (List Pattern)) (acc : Session × List Pattern),
      CompiledConsistent acc.1 →
      CompiledConsistent
        ((combos.foldl
          (evalTupleBuildStepWith (referenceEvalCallableApplyN fuel) isRuleCallableHead) acc).1) := by
  intro combos
  induction combos with
  | nil =>
      intro acc hAcc
      simpa
  | cons xs rest ih =>
      intro acc hAcc
      have hStep :
          CompiledConsistent
            (evalTupleBuildStepWith
              (referenceEvalCallableApplyN fuel) isRuleCallableHead acc xs).1 :=
        compiledConsistent_of_referenceEvalTupleBuildStep fuel hEvalCallablePres hAcc
      simpa [List.foldl] using
        ih
          (evalTupleBuildStepWith
            (referenceEvalCallableApplyN fuel) isRuleCallableHead acc xs)
          hStep

private theorem compiledConsistent_of_referenceEvalTupleBuilt
    (fuel : Nat)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (s : Session) (combos : List (List Pattern))
    (hs : CompiledConsistent s) :
    CompiledConsistent
      (evalTupleBuiltWith
        (referenceEvalCallableApplyN fuel) isRuleCallableHead s combos).1 := by
  simp [evalTupleBuiltWith]
  simpa using
    compiledConsistent_foldl_referenceEvalTupleBuildStep
      fuel hEvalCallablePres combos (s, []) hs

private theorem compiledConsistent_of_referenceEvalTupleElems
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1) :
    ∀ (s : Session) (elems : List Pattern),
      CompiledConsistent s →
      CompiledConsistent
        (evalTupleElemsWith (referenceEvalWithStateCoreN fuel) s elems).1 := by
  intro s elems hs
  induction elems generalizing s with
  | nil =>
      simp [evalTupleElemsWith]
      simpa using hs
  | cons e rest ih =>
      have hHead : CompiledConsistent (referenceEvalWithStateCoreN fuel s e).1 :=
        hEvalCorePres s e hs
      cases hEvalHead : referenceEvalWithStateCoreN fuel s e with
      | mk s1 headOut0 =>
          have hs1 : CompiledConsistent s1 := by
            simpa [hEvalHead] using hHead
          have hTail :
              CompiledConsistent (evalTupleElemsWith (referenceEvalWithStateCoreN fuel) s1 rest).1 :=
            ih s1 hs1
          cases hEvalTail : evalTupleElemsWith (referenceEvalWithStateCoreN fuel) s1 rest with
          | mk s2 tails =>
              have hs2 : CompiledConsistent s2 := by
                simpa [hEvalTail] using hTail
              simp [evalTupleElemsWith]
              simpa [hEvalHead, hEvalTail] using hs2

private theorem compiledConsistent_of_referenceEvalTupleIntrinsic
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    {s : Session} {elems : List Pattern} {s' : Session} {out : List Pattern}
    (hTuple :
      evalTupleIntrinsicWith
        (referenceEvalWithStateCoreN fuel)
        (referenceEvalCallableApplyN fuel)
        isRuleCallableHead s elems = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hElems :
      CompiledConsistent (evalTupleElemsWith (referenceEvalWithStateCoreN fuel) s elems).1 :=
    compiledConsistent_of_referenceEvalTupleElems fuel hEvalCorePres s elems hs
  cases hEvalElems : evalTupleElemsWith (referenceEvalWithStateCoreN fuel) s elems with
  | mk s1 combos =>
      have hs1 : CompiledConsistent s1 := by
        simpa [hEvalElems] using hElems
      have hBuilt :
          CompiledConsistent
            (evalTupleBuiltWith
              (referenceEvalCallableApplyN fuel) isRuleCallableHead s1 combos).1 :=
        compiledConsistent_of_referenceEvalTupleBuilt fuel hEvalCallablePres s1 combos hs1
      have hState :
          (evalTupleBuiltWith
            (referenceEvalCallableApplyN fuel) isRuleCallableHead s1 combos).1 = s' := by
        have hState0 :
            (evalTupleIntrinsicWith
              (referenceEvalWithStateCoreN fuel)
              (referenceEvalCallableApplyN fuel)
              isRuleCallableHead s elems).1 = s' := by
          exact congrArg Prod.fst hTuple
        simp [evalTupleIntrinsicWith, hEvalElems] at hState0
        exact hState0
      simpa [hState] using hBuilt

private theorem referenceDeterministicEvalInterfaceN_preservation
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1) :
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.Preservation
      (referenceDeterministicEvalInterfaceN fuel) CompiledConsistent := by
  refine {
    evalTupleIntrinsic_preserves := ?_
  }
  intro s elems s' out hTuple hs
  have hTupleRef :
      evalTupleIntrinsicWith
        (referenceEvalWithStateCoreN fuel)
        (referenceEvalCallableApplyN fuel)
        isRuleCallableHead s elems = (s', out) := by
    simpa [referenceDeterministicEvalInterfaceN] using hTuple
  have hTuplePres : CompiledConsistent s' :=
    compiledConsistent_of_referenceEvalTupleIntrinsic fuel hEvalCorePres hEvalCallablePres
      (s' := s') (out := out) hTupleRef hs
  simpa using hTuplePres

private theorem compiledConsistent_of_referenceEvalDeterministicCoreN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    {s : Session} {detFuel : Nat} {term : Pattern} :
    CompiledConsistent s →
    CompiledConsistent (referenceEvalDeterministicCoreN fuel s detFuel term).1 := by
  intro hs
  exact
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval_preserves
      (referenceDeterministicEvalInterfaceN fuel) CompiledConsistent
      (referenceDeterministicEvalInterfaceN_preservation fuel hEvalCorePres hEvalCallablePres)
      s detFuel term hs

-- Phase 5 preservation: Expr elems uses evalTupleIntrinsicWith (N-kernel eval functions).
private theorem compiledConsistent_of_referenceEvalTupleIntrinsicFst
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (s : Session) (elems : List Pattern)
    (hs : CompiledConsistent s) :
    CompiledConsistent
      (evalTupleIntrinsicWith
        (referenceEvalWithStateCoreN fuel)
        (referenceEvalCallableApplyN fuel)
        isRuleCallableHead s elems).1 := by
  cases hE : evalTupleIntrinsicWith
    (referenceEvalWithStateCoreN fuel)
    (referenceEvalCallableApplyN fuel)
    isRuleCallableHead s elems with
  | mk s' out =>
      exact compiledConsistent_of_referenceEvalTupleIntrinsic fuel hEvalCorePres
        hEvalCallablePres hE hs

-- Phase 5 preservation: repr [arg] uses referenceEvalDeterministicCoreN.
private theorem compiledConsistent_of_referenceEvalDeterministicCoreN_fst
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (s : Session) (detFuel : Nat) (arg : Pattern)
    (hs : CompiledConsistent s) :
    CompiledConsistent
      (Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval
        { evalTupleIntrinsic := evalTupleIntrinsicWith
            (referenceEvalWithStateCoreN fuel)
            (referenceEvalCallableApplyN fuel)
            isRuleCallableHead
          translateCall := fun s callRaw =>
            Algorithms.MeTTa.Simple.Semantics.TranslatorOps.translateCall
              translatorInterface s s.translatorRuleHeads callRaw
          deterministicPreserveArgs := deterministicPreserveArgs
          intrinsicDirect := intrinsicDirect
          firstRuleReduction? := firstRuleReduction?
          rewriteAritiesForHead := rewriteAritiesForHead
          builtinPartialMinArity := builtinPartialMinArity?
          partialPattern := partialPattern
          memoLimit := detMemoLimit }
        s detFuel arg).1 :=
  compiledConsistent_of_referenceEvalDeterministicCoreN fuel hEvalCorePres hEvalCallablePres hs

private theorem referencePettaCoreInterfaceN_preservation
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1) :
    Algorithms.MeTTa.Simple.Semantics.PeTTaCore.Preservation
      (referencePettaCoreInterfaceN fuel) CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    evalDeterministic_preserves := ?_,
    evalCallableApply_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1 :=
      hEvalCorePres s term hs
    have hState : (referenceEvalWithStateCoreN fuel s term).1 = s' := by
      simpa [referencePettaCoreInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s detFuel term s' out hEval hs
    have hPres :
        CompiledConsistent (referenceEvalDeterministicCoreN fuel s detFuel term).1 :=
      compiledConsistent_of_referenceEvalDeterministicCoreN fuel hEvalCorePres hEvalCallablePres hs
    have hState : (referenceEvalDeterministicCoreN fuel s detFuel term).1 = s' := by
      simpa [referencePettaCoreInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s fn args s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1 :=
      hEvalCallablePres s fn args hs
    have hState : (referenceEvalCallableApplyN fuel s fn args).1 = s' := by
      simpa [referencePettaCoreInterfaceN] using congrArg Prod.fst hEval
    simpa [hState] using hPres

private theorem compiledConsistent_of_referencePettaCoreEvalIntrinsicN
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    {s : Session} {term : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Option.getD
        (Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s term)
        (s, [])).1 := by
  intro hs
  cases hPeTTa :
      Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
        (referencePettaCoreInterfaceN fuel) s term with
  | none =>
      simp
      simpa using hs
  | some res =>
      have hPres :=
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic_preserves
          (referencePettaCoreInterfaceN fuel) CompiledConsistent
          (referencePettaCoreInterfaceN_preservation fuel hEvalCorePres hEvalCallablePres)
          s term hs
      simpa [hPeTTa] using hPres
private theorem compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    {s : Session} {term : Pattern} :
    CompiledConsistent s →
    CompiledConsistent
      (Option.getD
        (Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s term)
        (s, [])).1 := by
  intro hs
  cases hPeTTa :
      Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
        (referencePettaCoreInterfaceN fuel) s term with
  | none =>
      simp
      simpa using hs
  | some res =>
      have hPres :=
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic_preserves
          (referencePettaCoreInterfaceN fuel) CompiledConsistent
          (referencePettaCoreInterfaceN_preservation fuel hEvalCorePres hEvalCallablePres)
          s term hs
      simpa [hPeTTa] using hPres

private theorem p4_case_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {keyExpr branchesExpr : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "case" [keyExpr, branchesExpr]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "case" [keyExpr, branchesExpr])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "case" [keyExpr, branchesExpr]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "case" [keyExpr, branchesExpr]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "case" [keyExpr, branchesExpr]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "case" [keyExpr, branchesExpr]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "case" [keyExpr, branchesExpr]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · exact
        compiledConsistent_of_referenceCaseIntrinsicInlineN_conj
          fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
          (by
            simpa [referenceControlFlowInterfaceN,
              referenceEvalGeneratorValuesN,
              referenceEvalKeyValuesPreservingMultiplicityN] using h)
          hs

private theorem p4_foldall_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {aggExpr genExpr initExpr : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s
          (.apply "foldall" [aggExpr, genExpr, initExpr]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "foldall" [aggExpr, genExpr, initExpr])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "foldall" [aggExpr, genExpr, initExpr]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres
            (term := .apply "foldall" [aggExpr, genExpr, initExpr]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "foldall" [aggExpr, genExpr, initExpr]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "foldall" [aggExpr, genExpr, initExpr]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "foldall" [aggExpr, genExpr, initExpr]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · exact
        compiledConsistent_of_referenceFoldallIntrinsicInlineN_conj
          fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
          (by
            simpa [referenceControlFlowInterfaceN,
              referenceEvalGeneratorValuesN,
              referenceEvalKeyValuesPreservingMultiplicityN] using h)
          hs

private theorem p4_forall_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {genExpr checkExpr : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "forall" [genExpr, checkExpr]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "forall" [genExpr, checkExpr])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "forall" [genExpr, checkExpr]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres
            (term := .apply "forall" [genExpr, checkExpr]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "forall" [genExpr, checkExpr]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "forall" [genExpr, checkExpr]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "forall" [genExpr, checkExpr]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · exact
        compiledConsistent_of_referenceForallIntrinsicInlineN_conj
          fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres
          (by
            simpa [referenceControlFlowInterfaceN,
              referenceEvalGeneratorValuesN,
              referenceEvalKeyValuesPreservingMultiplicityN] using h)
          hs

private theorem p4_match3_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {space pat tmpl : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "match" [space, pat, tmpl]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "match" [space, pat, tmpl])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "match" [space, pat, tmpl]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "match" [space, pat, tmpl]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "match" [space, pat, tmpl]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "match" [space, pat, tmpl]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "match" [space, pat, tmpl]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · exact
        let hConj :
            (Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
                (referenceSpaceEvalInterfaceN fuel s) spacePolicy s space pat tmpl).fst = s' ∧
            (Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
                (referenceSpaceEvalInterfaceN fuel s) spacePolicy s space pat tmpl).snd = out := by
              simpa [intrinsicMatchResultWithEval, referenceSpaceEvalInterfaceN,
                spaceOpsInterfaceWithEval] using h
        let ⟨hS, hOut⟩ := hConj
        compiledConsistent_of_referenceMatchIntrinsicN_result
          fuel s hEvalCorePres
          (hEval := Prod.ext hS hOut)
          hs

private theorem p4_match2_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {pat tmpl : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "match" [pat, tmpl]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "match" [pat, tmpl])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "match" [pat, tmpl]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "match" [pat, tmpl]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "match" [pat, tmpl]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "match" [pat, tmpl]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "match" [pat, tmpl]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · exact
        let hConj :
            (Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
                (referenceSpaceEvalInterfaceN fuel s) spacePolicy s selfSpaceAtom pat tmpl).fst = s' ∧
            (Algorithms.MeTTa.Simple.Semantics.SpaceOps.evalMatchIntrinsic
                (referenceSpaceEvalInterfaceN fuel s) spacePolicy s selfSpaceAtom pat tmpl).snd = out := by
              simpa [intrinsicMatchResultWithEval, referenceSpaceEvalInterfaceN,
                spaceOpsInterfaceWithEval] using h
        let ⟨hS, hOut⟩ := hConj
        compiledConsistent_of_referenceMatchIntrinsicN_result
          fuel s hEvalCorePres
          (space := selfSpaceAtom)
          (hEval := Prod.ext hS hOut)
          hs

private theorem p4_once_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {evalArg : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "once" [evalArg]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "once" [evalArg])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "once" [evalArg]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "once" [evalArg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "once" [evalArg]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "once" [evalArg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "once" [evalArg]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · -- h : (match evalResult.snd with | [] => some (...) | x :: _ => some (...)) = some (s', out).
      -- Case-split the match in h; each branch is some (fst, ...) = some (s', out).
      split at h <;> (
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact h.1 ▸ hEvalCorePres s evalArg hs)

private theorem p4_atomof_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {x : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "atom-of" [x]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "atom-of" [x])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "atom-of" [x]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "atom-of" [x]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "atom-of" [x]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "atom-of" [x]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "atom-of" [x]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · let run := referenceRunNestedEffectsN fuel s true false x
      let x1 := run.2.1
      have hRunCC :
          CompiledConsistent run.1 :=
        compiledConsistent_of_referenceRunNestedEffectsN
          fuel hIntrinsicPres s true false x hs
      cases hInner : referenceIntrinsicStatefulN fuel run.1 x1 with
      | none =>
          let reducts := run.1.step x1
          let atomOut : Session × List Pattern :=
            if reducts.isEmpty = true then (run.1, [x1]) else (run.1, reducts)
          let extracted :=
            List.filterMap
              (fun candidate =>
                match tupleAt? (tupleElems candidate) 0 with
                | none => none
                | some row => tupleAt? (tupleElems row) 0)
              atomOut.snd
          by_cases hExtEmpty : extracted.isEmpty = true
          · have hEq : some (atomOut.fst, ([] : List Pattern)) = some (s', out) := by
              simpa only [run, x1, hInner, reducts, atomOut, extracted, hExtEmpty] using h
            have hStateAtom : atomOut.fst = s' := by
              exact congrArg Prod.fst (Option.some.inj hEq)
            have hStateRun : atomOut.fst = run.1 := by
              by_cases hRedEmpty : reducts.isEmpty = true <;> simp [atomOut, hRedEmpty]
            exact (hStateRun.symm.trans hStateAtom) ▸ hRunCC
          · have hEq : some (atomOut.fst, dedupPatternList extracted) = some (s', out) := by
              simpa only [run, x1, hInner, reducts, atomOut, extracted, hExtEmpty] using h
            have hStateAtom : atomOut.fst = s' := by
              exact congrArg Prod.fst (Option.some.inj hEq)
            have hStateRun : atomOut.fst = run.1 := by
              by_cases hRedEmpty : reducts.isEmpty = true <;> simp [atomOut, hRedEmpty]
            exact (hStateRun.symm.trans hStateAtom) ▸ hRunCC
      | some inner =>
          cases inner with
          | mk sI outI =>
              have hInnerCC :
                  CompiledConsistent sI :=
                hIntrinsicPres run.1 x1 sI outI hInner hRunCC
              let atomOut : Session × List Pattern :=
                if outI.isEmpty = true then (sI, [x1]) else (sI, outI)
              let extracted :=
                List.filterMap
                  (fun candidate =>
                    match tupleAt? (tupleElems candidate) 0 with
                    | none => none
                    | some row => tupleAt? (tupleElems row) 0)
                  atomOut.snd
              by_cases hExtEmpty : extracted.isEmpty = true
              · have hEq : some (atomOut.fst, ([] : List Pattern)) = some (s', out) := by
                  simpa only [run, x1, hInner, atomOut, extracted, hExtEmpty] using h
                have hStateAtom : atomOut.fst = s' := by
                  exact congrArg Prod.fst (Option.some.inj hEq)
                have hStateInner : atomOut.fst = sI := by
                  by_cases hOutEmpty : outI.isEmpty = true <;> simp [atomOut, hOutEmpty]
                exact (hStateInner.symm.trans hStateAtom) ▸ hInnerCC
              · have hEq : some (atomOut.fst, dedupPatternList extracted) = some (s', out) := by
                  simpa only [run, x1, hInner, atomOut, extracted, hExtEmpty] using h
                have hStateAtom : atomOut.fst = s' := by
                  exact congrArg Prod.fst (Option.some.inj hEq)
                have hStateInner : atomOut.fst = sI := by
                  by_cases hOutEmpty : outI.isEmpty = true <;> simp [atomOut, hOutEmpty]
                exact (hStateInner.symm.trans hStateAtom) ▸ hInnerCC

private theorem p4_nop_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {evalArg : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "nop" [evalArg]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "nop" [evalArg])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "nop" [evalArg]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "nop" [evalArg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "nop" [evalArg]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "nop" [evalArg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "nop" [evalArg]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · have hPair :
          ((referenceEvalWithStateCoreN fuel s evalArg).fst, [Pattern.apply "()" []]) = (s', out) :=
        Option.some.inj h
      have hState : (referenceEvalWithStateCoreN fuel s evalArg).fst = s' :=
        congrArg Prod.fst hPair
      exact hState ▸ hEvalCorePres s evalArg hs

private theorem p4_catch1_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {evalArg : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "catch" [evalArg]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "catch" [evalArg])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "catch" [evalArg]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "catch" [evalArg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "catch" [evalArg]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "catch" [evalArg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "catch" [evalArg]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · have hPair : referenceEvalWithStateCoreN fuel s evalArg = (s', out) :=
        Option.some.inj h
      have hState : (referenceEvalWithStateCoreN fuel s evalArg).fst = s' :=
        congrArg Prod.fst hPair
      exact hState ▸ hEvalCorePres s evalArg hs

private theorem p4_msort_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {evalArg : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "msort" [evalArg]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "msort" [evalArg])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "msort" [evalArg]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "msort" [evalArg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "msort" [evalArg]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "msort" [evalArg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "msort" [evalArg]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · have hState :
          (referenceEvalWithStateCoreN fuel s evalArg).fst = s' := by
        exact congrArg Prod.fst (Option.some.inj h)
      exact hState ▸ hEvalCorePres s evalArg hs

private theorem p4_expr_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {elems : List Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "Expr" elems) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "Expr" elems)
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "Expr" elems) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "Expr" elems) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "Expr" elems) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "Expr" elems) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "Expr" elems) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · have hState :
          (evalTupleIntrinsicWith
              (fun s term => referenceEvalWithStateCoreN fuel s term)
              (fun s fn args => referenceEvalCallableApplyN fuel s fn args)
              isRuleCallableHead s elems).fst = s' := by
        exact congrArg Prod.fst (Option.some.inj h)
      exact hState ▸
        compiledConsistent_of_referenceEvalTupleIntrinsicFst
          fuel hEvalCorePres hEvalCallablePres s elems hs

private theorem p4_repr_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {arg : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "repr" [arg]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    have hCC :=
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
        (fuel := fuel) (term := .apply "repr" [arg])
        hEvalCorePres hEvalCallablePres hs
    have hNamed :
        Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
          (referencePettaCoreInterfaceN fuel) s
            (.apply "repr" [arg]) = some (s', out) := hPeTTa
    rw [hNamed] at hCC
    simpa using hCC
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
            fuel hEvalCorePres (term := .apply "repr" [arg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
              (referenceStateEffectsInterfaceN fuel) s
                (.apply "repr" [arg]) = some (s', out) := hStateE
        rw [hNamed] at hCC
        simpa using hCC
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        have hCC :=
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
            fuel hEvalCorePres hIntrinsicPres
            (term := .apply "repr" [arg]) hs
        have hNamed :
            Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
              (referenceStreamOpsInterfaceN fuel) s
                (.apply "repr" [arg]) = some (s', out) := hPre
        rw [hNamed] at hCC
        simpa using hCC
    · have hState :
          (referenceEvalDeterministicCoreN fuel s 1024 arg).fst = s' := by
        exact congrArg Prod.fst (Option.some.inj h)
      exact hState ▸
        compiledConsistent_of_referenceEvalDeterministicCoreN_fst
          fuel hEvalCorePres hEvalCallablePres s 1024 arg hs

private theorem compiledConsistent_of_partialPatternFallback
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (h : s = s' ∧ [partialPattern ctor args] = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact h.1 ▸ hs

private theorem compiledConsistent_of_partialPatternFallback_cons
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (h : s = s' ∧ partialPattern ctor args :: [] = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact h.1 ▸ hs

private theorem p4_generic_partialPattern_branch_preserves
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (hPP : s = s' ∧ [partialPattern ctor args] = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact hPP.1 ▸ hs

private theorem p4_generic_partialPattern_branch_preserves_cons
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (hPP : s = s' ∧ partialPattern ctor args :: [] = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact hPP.1 ▸ hs


private theorem compiledConsistent_of_stateEq
    {s s' : Session}
    (h : s = s')
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact h ▸ hs

private theorem compiledConsistent_of_stateEq_conj
    {s s' : Session} {out0 out : List Pattern}
    (h : s = s' ∧ out0 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact compiledConsistent_of_stateEq h.1 hs

private theorem compiledConsistent_of_somePairEq
    {p q : Session × List Pattern}
    (h : some p = some q)
    (hp : CompiledConsistent p.1) :
    CompiledConsistent q.1 := by
  have hState : p.1 = q.1 := congrArg Prod.fst (Option.some.inj h)
  exact hState ▸ hp

private theorem compiledConsistent_of_evalCoreState
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {term : Pattern}
    (hState : (referenceEvalWithStateCoreN fuel s term).fst = s')
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact hState ▸ hEvalCorePres s term hs

private theorem compiledConsistent_of_evalCoreState_conj
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {term : Pattern} {out0 out : List Pattern}
    (h : (referenceEvalWithStateCoreN fuel s term).fst = s' ∧ out0 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact compiledConsistent_of_evalCoreState fuel hEvalCorePres h.1 hs

private theorem compiledConsistent_of_evalCoreChainState
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {term1 term2 : Pattern}
    (hState : (referenceEvalWithStateCoreN fuel (referenceEvalWithStateCoreN fuel s term1).1 term2).fst = s')
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hs1 : CompiledConsistent (referenceEvalWithStateCoreN fuel s term1).1 :=
    hEvalCorePres s term1 hs
  exact hState ▸ hEvalCorePres (referenceEvalWithStateCoreN fuel s term1).1 term2 hs1

private theorem compiledConsistent_of_evalCoreChainState_conj
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {term1 term2 : Pattern} {out0 out : List Pattern}
    (h :
      (referenceEvalWithStateCoreN fuel (referenceEvalWithStateCoreN fuel s term1).1 term2).fst = s' ∧
        out0 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact compiledConsistent_of_evalCoreChainState fuel hEvalCorePres h.1 hs

private theorem compiledConsistent_of_vectorSpaceState
    {s s' : Session} {name : String} {vs : VectorSpace}
    (hState : withVectorSpace s name vs = s')
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact hState ▸ compiledConsistent_withVectorSpace s name vs hs

private theorem compiledConsistent_of_vectorSpaceState_conj
    {s s' : Session} {name : String} {vs : VectorSpace} {out0 out : List Pattern}
    (h : withVectorSpace s name vs = s' ∧ out0 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact compiledConsistent_of_vectorSpaceState h.1 hs

private theorem compiledConsistent_of_translatorRuleHeadsState
    {s s' : Session} {heads : List String}
    (hState : { s with translatorRuleHeads := heads } = s')
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact hState ▸ compiledConsistent_withTranslatorRuleHeads s heads hs

private theorem compiledConsistent_of_translatorRuleHeadsState_conj
    {s s' : Session} {heads : List String} {out0 out : List Pattern}
    (h : { s with translatorRuleHeads := heads } = s' ∧ out0 = out)
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact compiledConsistent_of_translatorRuleHeadsState h.1 hs

private structure RefNPres (fuel : Nat) where
  callable :
    ∀ (s : Session) (fn : Pattern) (args : List Pattern),
      CompiledConsistent s →
      CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1
  evalCore :
    ∀ (s : Session) (term : Pattern),
      CompiledConsistent s →
      CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1
  evalForRule :
    ∀ (s : Session) (expr : Pattern),
      CompiledConsistent s →
      CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1
  intrinsic :
    ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
      referenceIntrinsicStatefulN fuel s term = some (s', out) →
      CompiledConsistent s →
      CompiledConsistent s'

private theorem compiledConsistent_of_referenceEvalWithStateCoreN_step
    (fuel : Nat)
    (hIntrinsicPrev :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    ∀ (s : Session) (term : Pattern),
      CompiledConsistent s →
      CompiledConsistent (referenceEvalWithStateCoreN (fuel + 1) s term).1 := by
  intro s term hs
  let iface : Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
    maxNodes := fun s => s.maxNodes
    maxSteps := fun s => s.maxSteps
    runNestedEffects := fun s isRoot parentCallable term =>
      referenceRunNestedEffectsN fuel s isRoot parentCallable term
    intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
    isEagerCallableHead := isEagerCallableHead
    step := step
    enqueueNext := enqueueNext
    insertUnique := insertUnique
    dedupPatterns := dedupPatterns
  }
  have hIntrinsicPresRef :
      ∀ {s : Session} {term : Pattern} {s' : Session} {out : List Pattern},
        iface.intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s' := by
    intro s term s' out hIntr hs0
    simpa [iface] using hIntrinsicPrev s term s' out hIntr hs0
  have hPres :
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.Preservation
        iface CompiledConsistent := by
    exact
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.preservation_of_intrinsicStateful
        iface CompiledConsistent hIntrinsicPresRef
  simpa [referenceEvalWithStateCoreN, iface] using
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore_preserves
      iface CompiledConsistent hPres s term hs

private theorem compiledConsistent_of_referenceEvalForRuleEnumerationN_step
    (fuel : Nat)
    (hEvalCorePrev :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hIntrinsicPrev :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    ∀ (s : Session) (expr : Pattern),
      CompiledConsistent s →
      CompiledConsistent (referenceEvalForRuleEnumerationN (fuel + 1) s expr).1 := by
  intro s expr hs
  unfold referenceEvalForRuleEnumerationN
  cases hIntr : referenceIntrinsicStatefulN fuel s expr with
  | none =>
      simp
      exact hEvalCorePrev s expr hs
  | some res =>
      rcases res with ⟨s1, out0⟩
      simp
      exact hIntrinsicPrev s expr s1 out0 hIntr hs

private theorem compiledConsistent_of_referenceEvalCallableApplyN_step
    (fuel : Nat)
    (hEvalCorePrev :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePrev :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hCallablePrev :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1) :
    ∀ (s : Session) (fn : Pattern) (args : List Pattern),
      CompiledConsistent s →
      CompiledConsistent (referenceEvalCallableApplyN (fuel + 1) s fn args).1 := by
  intro s fn args hs
  cases fn with
  | fvar name =>
      simp [referenceEvalCallableApplyN]
      cases hEval : referenceEvalWithStateCoreN fuel s (.apply name args) with
      | mk sEval out0 =>
          have hsEval : CompiledConsistent sEval := by
            simpa [hEval] using hEvalCorePrev s (.apply name args) hs
          simpa [referenceDispatchInterfaceN, hEval] using
            compiledConsistent_of_referenceDispatchPostprocessN
              fuel hEvalCorePrev hEvalForRulePrev sEval (.apply name args) out0 hsEval
  | apply name boundArgs =>
      cases boundArgs with
      | nil =>
          simp [referenceEvalCallableApplyN]
          cases hEval : referenceEvalWithStateCoreN fuel s (.apply name args) with
          | mk sEval out0 =>
              have hsEval : CompiledConsistent sEval := by
                simpa [hEval] using hEvalCorePrev s (.apply name args) hs
              simpa [referenceDispatchInterfaceN, hEval] using
                compiledConsistent_of_referenceDispatchPostprocessN
                  fuel hEvalCorePrev hEvalForRulePrev sEval (.apply name args) out0 hsEval
      | cons a rest =>
          cases rest with
          | nil =>
              simp [referenceEvalCallableApplyN]
              exact hCallablePrev s (.apply name []) ([a] ++ args) hs
          | cons b tail =>
              cases tail with
              | nil =>
                  by_cases hPartial : name = "partial"
                  · simp [referenceEvalCallableApplyN, hPartial]
                    exact hCallablePrev s a (tupleElems b ++ args) hs
                  · by_cases hArrow : name = "|->"
                    · simp [referenceEvalCallableApplyN, hArrow]
                      by_cases hLen : (lambdaParamNamesCompat a).length = args.length
                      · simp [hLen]
                        let bodySub := applyBindingsCompat (List.zip (lambdaParamNamesCompat a) args) b
                        cases hEval : referenceEvalWithStateCoreN fuel s bodySub with
                        | mk sEval out0 =>
                            have hsEval : CompiledConsistent sEval := by
                              simpa [hEval, bodySub] using hEvalCorePrev s bodySub hs
                            simpa [referenceDispatchInterfaceN, hArrow, hLen, hEval, bodySub] using
                              compiledConsistent_of_referenceDispatchPostprocessN
                                fuel hEvalCorePrev hEvalForRulePrev sEval bodySub out0 hsEval
                      · simp [hLen]
                        simpa using hs
                    · simp [referenceEvalCallableApplyN, hPartial, hArrow]
                      exact hCallablePrev s (.apply name []) ((a :: b :: []) ++ args) hs
              | cons c tail' =>
                  simp [referenceEvalCallableApplyN]
                  exact hCallablePrev s (.apply name []) ((a :: b :: c :: tail') ++ args) hs
  | bvar _ =>
      simp [referenceEvalCallableApplyN]
      simpa using hs
  | lambda _ =>
      simp [referenceEvalCallableApplyN]
      simpa using hs
  | multiLambda _ _ =>
      simp [referenceEvalCallableApplyN]
      simpa using hs
  | subst _ _ =>
      simp [referenceEvalCallableApplyN]
      simpa using hs
  | collection _ _ _ =>
      simp [referenceEvalCallableApplyN]
      simpa using hs


private theorem compiledConsistent_of_referencePettaCoreEvalIntrinsicN_result
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    {s s' : Session} {term : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsic
        (referencePettaCoreInterfaceN fuel) s term = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referencePettaCoreEvalIntrinsicN_early
      (fuel := fuel) (hEvalCorePres := hEvalCorePres)
      (hEvalCallablePres := hEvalCallablePres) (s := s) (term := term) hs
  rw [hEval] at hCC
  simpa using hCC

private theorem compiledConsistent_of_referenceStateEffectsEvalIntrinsicN_result
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    {s s' : Session} {term : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsic
        (referenceStateEffectsInterfaceN fuel) s term = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceStateEffectsEvalIntrinsicN
      (fuel := fuel) (hEvalCorePres := hEvalCorePres)
      (s := s) (term := term) hs
  rw [hEval] at hCC
  simpa using hCC

private theorem compiledConsistent_of_referenceStreamOpsEvalIntrinsicN_result
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {term : Pattern} {out : List Pattern}
    (hEval :
      Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsic
        (referenceStreamOpsInterfaceN fuel) s term = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hCC :=
    compiledConsistent_of_referenceStreamOpsEvalIntrinsicN
      (fuel := fuel) (hEvalCorePres := hEvalCorePres)
      (hIntrinsicPres := hIntrinsicPres)
      (s := s) (term := term) hs
  rw [hEval] at hCC
  simpa using hCC

private theorem p4_addatom_bang_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {space fact : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "add-atom!" [space, fact]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    exact
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_result
        fuel hEvalCorePres hEvalCallablePres hPeTTa hs
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        exact
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN_result
            fuel hEvalCorePres hStateE hs
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        exact
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN_result
            fuel hEvalCorePres hIntrinsicPres hPre hs
    · by_cases hEmpty :
        (((match fact with
          | .apply "=" [lhs, rhs] =>
              match boolOfPattern? rhs with
              | some true => lhs
              | some false => .apply "empty" []
              | none => fact
          | _ => fact) == .apply "empty" []) = true)
      · simp [hEmpty] at h
        exact compiledConsistent_of_stateEq h.1 hs
      · simp [hEmpty] at h
        exact
          compiledConsistent_of_referenceAddAtomN_conj
            fuel s hEvalCorePres h.1 h.2
            hs

private theorem p4_removeatom_bang_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {space fact : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "remove-atom!" [space, fact]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    exact
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_result
        fuel hEvalCorePres hEvalCallablePres hPeTTa hs
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        exact
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN_result
            fuel hEvalCorePres hStateE hs
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        exact
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN_result
            fuel hEvalCorePres hIntrinsicPres hPre hs
    · by_cases hEmpty :
        (((match fact with
          | .apply "=" [lhs, rhs] =>
              match boolOfPattern? rhs with
              | some true => lhs
              | some false => .apply "empty" []
              | none => fact
          | _ => fact) == .apply "empty" []) = true)
      · simp [hEmpty] at h
        exact compiledConsistent_of_stateEq h.1 hs
      · simp [hEmpty] at h
        exact
          compiledConsistent_of_referenceRemoveAtomN_conj
            fuel s hEvalCorePres h.1 h.2
            hs

private theorem p4_addatom_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {space fact : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "add-atom" [space, fact]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  case h_1 =>
    rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    exact
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_result
        fuel hEvalCorePres hEvalCallablePres hPeTTa hs
  case h_2 =>
    split at h
    case h_1 =>
      rename_i _ _ _ out1 hPre
      split at hPre
      case h_1 =>
        rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        exact
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN_result
            fuel hEvalCorePres hStateE hs
      case h_2 =>
        have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        exact
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN_result
            fuel hEvalCorePres hIntrinsicPres hPre hs
    case h_2 =>
      have hPair := Option.some.inj h
      exact
        compiledConsistent_of_referenceAddAtomN_result
          fuel s hEvalCorePres hPair hs

private theorem p4_removeatom_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s s' : Session} {space fact : Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicStatefulN (fuel + 1) s (.apply "remove-atom" [space, fact]) =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  case h_1 =>
    rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    exact
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_result
        fuel hEvalCorePres hEvalCallablePres hPeTTa hs
  case h_2 =>
    split at h
    case h_1 =>
      rename_i _ _ _ out1 hPre
      split at hPre
      case h_1 =>
        rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        exact
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN_result
            fuel hEvalCorePres hStateE hs
      case h_2 =>
        have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        exact
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN_result
            fuel hEvalCorePres hIntrinsicPres hPre hs
    case h_2 =>
      have hPair := Option.some.inj h
      exact
        compiledConsistent_of_referenceRemoveAtomN_result
          fuel s hEvalCorePres hPair hs

private theorem p4_apply_fallback_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicApplyFallbackN fuel s ctor args =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact
    compiledConsistent_of_referenceIntrinsicApplyFallbackN_result
      fuel hEvalCorePres hEvalForRulePres h hs

private theorem p4_apply_branch_preserves
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    {s s' : Session} {ctor : String} {args : List Pattern} {out : List Pattern}
    (h :
      referenceIntrinsicApplyFallbackN fuel s ctor args =
        some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  exact
    p4_apply_fallback_preserves
      fuel hEvalCorePres hEvalForRulePres h hs

set_option maxHeartbeats 800000 in
private theorem compiledConsistent_of_referenceIntrinsicStatefulN_apply_step
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {ctor : String} {args : List Pattern} {s' : Session} {out : List Pattern}
    (h : referenceIntrinsicStatefulN (fuel + 1) s (.apply ctor args) = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have h0 := h
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    exact
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_result
        fuel hEvalCorePres hEvalCallablePres hPeTTa hs
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        exact
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN_result
            fuel hEvalCorePres hStateE hs
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        exact
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN_result
            fuel hEvalCorePres hIntrinsicPres hPre hs
    ·
      by_cases hProgn : ctor = "progn"
      · subst hProgn
        simp at h
        exact compiledConsistent_of_stateEq_conj h hs
      · by_cases hProg1 : ctor = "prog1"
        · subst hProg1
          simp at h
          exact compiledConsistent_of_stateEq_conj h hs
        · by_cases hExpr : ctor = "Expr"
          · subst hExpr
            exact
              p4_expr_branch_preserves
                fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                (h := by simpa using h0) hs
          ·
            cases args with
            | nil =>
                by_cases hCut : ctor = "cut"
                · subst hCut
                  simp at h
                  exact compiledConsistent_of_stateEq_conj h hs
                ·
                  have hFallback :
                      referenceIntrinsicApplyFallbackN fuel s ctor [] = some (s', out) := by
                    simpa [hCut] using h
                  exact
                    p4_apply_branch_preserves
                      fuel hEvalCorePres hEvalForRulePres hFallback hs
            | cons a rest =>
                cases rest with
                | nil =>
                    by_cases hRemoveAll : ctor = "remove-all-atoms"
                    · subst hRemoveAll
                      simp at h
                      exact
                        compiledConsistent_of_referenceRemoveAllAtomsN_conj
                          fuel s hEvalCorePres h.1 h.2 hs
                    · by_cases hRemoveAllBang : ctor = "remove-all-atoms!"
                      · subst hRemoveAllBang
                        simp at h
                        exact
                          compiledConsistent_of_referenceRemoveAllAtomsN_conj
                            fuel s hEvalCorePres h.1 h.2 hs
                      · by_cases hGetAtoms : ctor = "get-atoms"
                        · subst hGetAtoms
                          simp [intrinsicGetAtomsResultWithEval, spaceOpsInterfaceWithEval] at h
                          exact
                            compiledConsistent_of_referenceGetAtomsN_conj
                              fuel s h.1 h.2 hs
                        · by_cases hGetAtomsBang : ctor = "get-atoms!"
                          · subst hGetAtomsBang
                            simp [intrinsicGetAtomsResultWithEval, spaceOpsInterfaceWithEval] at h
                            exact
                              compiledConsistent_of_referenceGetAtomsN_conj
                                fuel s h.1 h.2 hs
                          · by_cases hPredicate : ctor = "Predicate"
                            · subst hPredicate
                              simp at h
                              exact compiledConsistent_of_stateEq_conj h hs
                            · by_cases hSucceeds : ctor = "succeedsPredicate"
                              · subst hSucceeds
                                cases hDec : decodePredicateSpacePattern? s a with
                                | none =>
                                    simp [hDec] at h
                                    exact compiledConsistent_of_stateEq_conj h hs
                                | some sp =>
                                    by_cases hEmpty : (findBindingsInSpace s sp.1 sp.2).isEmpty = true
                                    · simp [hDec, hEmpty] at h
                                      exact compiledConsistent_of_stateEq_conj h hs
                                    · simp [hDec, hEmpty] at h
                                      exact compiledConsistent_of_stateEq_conj h hs
                              · by_cases hAddTR : ctor = "add-translator-rule!"
                                · subst hAddTR
                                  simp at h
                                  exact compiledConsistent_of_translatorRuleHeadsState_conj h hs
                                · by_cases hRemoveTR : ctor = "remove-translator-rule!"
                                  · subst hRemoveTR
                                    simp at h
                                    exact compiledConsistent_of_translatorRuleHeadsState_conj h hs
                                  · by_cases hOnce : ctor = "once"
                                    · subst hOnce
                                      exact
                                        p4_once_branch_preserves
                                          fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                          (h := by simpa using h0) hs
                                    · by_cases hNop : ctor = "nop"
                                      · subst hNop
                                        exact
                                          p4_nop_branch_preserves
                                            fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                            (h := by simpa using h0) hs
                                      · by_cases hCatch1 : ctor = "catch"
                                        · subst hCatch1
                                          exact
                                            p4_catch1_branch_preserves
                                              fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                              (h := by simpa using h0) hs
                                        · by_cases hMsort : ctor = "msort"
                                          · subst hMsort
                                            exact
                                              p4_msort_branch_preserves
                                                fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                                (h := by simpa using h0) hs
                                          · by_cases hSuperpose : ctor = "superpose"
                                            · subst hSuperpose
                                              simp at h
                                              exact
                                                compiledConsistent_of_evalCoreState_conj
                                                  fuel hEvalCorePres h hs
                                            · by_cases hHide : ctor = "hide"
                                              · subst hHide
                                                simp at h
                                                exact
                                                  compiledConsistent_of_evalCoreState_conj
                                                    fuel hEvalCorePres h hs
                                              · by_cases hCollapse : ctor = "collapse"
                                                · subst hCollapse
                                                  simp at h
                                                  exact
                                                    compiledConsistent_of_evalCoreState_conj
                                                      fuel hEvalCorePres h hs
                                                · by_cases hTranslate : ctor = "translatePredicate"
                                                  · subst hTranslate
                                                    simp at h
                                                    exact
                                                      compiledConsistent_of_evalCoreState_conj
                                                        fuel hEvalCorePres h hs
                                                  · by_cases hRepr : ctor = "repr"
                                                    · subst hRepr
                                                      exact
                                                        p4_repr_branch_preserves
                                                          fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                                          (h := by simpa using h0) hs
                                                    · by_cases hAtomOf : ctor = "atom-of"
                                                      · subst hAtomOf
                                                        exact
                                                          p4_atomof_branch_preserves
                                                            fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                                            (h := by simpa using h0) hs
                                                      ·
                                                        have hFallback :
                                                            referenceIntrinsicApplyFallbackN fuel s ctor [a] =
                                                              some (s', out) := by
                                                          simpa [hRemoveAll, hRemoveAllBang,
                                                            hGetAtoms, hGetAtomsBang, hPredicate,
                                                            hSucceeds, hAddTR, hRemoveTR, hOnce,
                                                            hNop, hCatch1, hMsort, hSuperpose,
                                                            hHide, hCollapse, hTranslate, hRepr,
                                                            hAtomOf] using h
                                                        exact
                                                          p4_apply_branch_preserves
                                                            fuel hEvalCorePres hEvalForRulePres hFallback hs
                | cons b rest2 =>
                    cases rest2 with
                    | nil =>
                        by_cases hAddBang : ctor = "add-atom!"
                        · subst hAddBang
                          exact
                            p4_addatom_bang_branch_preserves
                              fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                              (h := by simpa using h0) hs
                        · by_cases hRemoveBang : ctor = "remove-atom!"
                          · subst hRemoveBang
                            exact
                              p4_removeatom_bang_branch_preserves
                                fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                (h := by simpa using h0) hs
                          · by_cases hAdd : ctor = "add-atom"
                            · subst hAdd
                              exact
                                p4_addatom_branch_preserves
                                  fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                  (h := by simpa using h0) hs
                            · by_cases hRemove : ctor = "remove-atom"
                              · subst hRemove
                                exact
                                  p4_removeatom_branch_preserves
                                    fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                    (h := by simpa using h0) hs
                              · by_cases hMatch : ctor = "match"
                                · subst hMatch
                                  exact
                                    p4_match2_branch_preserves
                                      fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                      (h := by simpa using h0) hs
                                · by_cases hCase : ctor = "case"
                                  · subst hCase
                                    exact
                                      p4_case_branch_preserves
                                        fuel hEvalCorePres hEvalCallablePres hEvalForRulePres
                                        hIntrinsicPres (h := by simpa using h0) hs
                                  · by_cases hForall : ctor = "forall"
                                    · subst hForall
                                      exact
                                        p4_forall_branch_preserves
                                          fuel hEvalCorePres hEvalCallablePres hEvalForRulePres
                                          hIntrinsicPres (h := by simpa using h0) hs
                                    · by_cases hFind : ctor = "find"
                                      · subst hFind
                                        by_cases hEmpty : (findBindingsInSpace s a b).isEmpty = true
                                        · simp [hEmpty] at h
                                          exact compiledConsistent_of_stateEq_conj h hs
                                        · simp [hEmpty] at h
                                          exact compiledConsistent_of_stateEq_conj h hs
                                      · by_cases hNewVS : ctor = "new-atom-vectorspace"
                                        · subst hNewVS
                                          cases hName : vectorSpaceName? a with
                                          | none =>
                                              simp [hName] at h
                                              exact compiledConsistent_of_stateEq_conj h hs
                                          | some name =>
                                              cases hDim : intOfPattern? b with
                                              | none =>
                                                  simp [hName, hDim] at h
                                                  exact compiledConsistent_of_stateEq_conj h hs
                                              | some dimI =>
                                                  by_cases hLe : dimI <= 0
                                                  · simp [hName, hDim, hLe] at h
                                                    exact compiledConsistent_of_stateEq_conj h hs
                                                  · simp [hName, hDim, hLe] at h
                                                    exact compiledConsistent_of_vectorSpaceState_conj h hs
                                        · by_cases hAddSRI : ctor = "add-atom-SRI"
                                          · subst hAddSRI
                                            cases hName : vectorSpaceName? a with
                                            | none =>
                                                simp [hName] at h
                                                exact compiledConsistent_of_stateEq_conj h hs
                                            | some name =>
                                                cases hVS : lookupVectorSpace? s name with
                                                | none =>
                                                    simp [hName, hVS] at h
                                                    exact compiledConsistent_of_stateEq_conj h hs
                                                | some vs =>
                                                    simp [hName, hVS] at h
                                                    exact compiledConsistent_of_vectorSpaceState_conj h hs
                                          · by_cases hSpace : ctor = "space"
                                            · subst hSpace
                                              simp at h
                                              exact
                                                compiledConsistent_of_evalCoreChainState_conj
                                                  fuel hEvalCorePres h hs
                                            · by_cases hIf2 : ctor = "if"
                                              · subst hIf2
                                                simp at h
                                                exact
                                                  compiledConsistent_of_evalCoreChainState_conj
                                                    fuel hEvalCorePres h hs
                                              · by_cases hLetStar : ctor = "let*"
                                                · subst hLetStar
                                                  simp at h
                                                  exact
                                                    compiledConsistent_of_evalCoreState_conj
                                                      fuel hEvalCorePres h hs
                                                ·
                                                  have hFallback :
                                                      referenceIntrinsicApplyFallbackN fuel s ctor [a, b] =
                                                        some (s', out) := by
                                                    simpa [hAddBang, hRemoveBang, hAdd, hRemove,
                                                      hMatch, hCase, hForall, hFind, hNewVS,
                                                      hAddSRI, hSpace, hIf2, hLetStar] using h
                                                  exact
                                                    p4_apply_branch_preserves
                                                      fuel hEvalCorePres hEvalForRulePres hFallback hs
                    | cons c rest3 =>
                        cases rest3 with
                        | nil =>
                            by_cases hMatch : ctor = "match"
                            · subst hMatch
                              exact
                                p4_match3_branch_preserves
                                  fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
                                  (h := by simpa using h0) hs
                            · by_cases hFoldall : ctor = "foldall"
                              · subst hFoldall
                                exact
                                  p4_foldall_branch_preserves
                                    fuel hEvalCorePres hEvalCallablePres hEvalForRulePres
                                    hIntrinsicPres (h := by simpa using h0) hs
                              · by_cases hAddVec : ctor = "add-atom-vector"
                                · subst hAddVec
                                  cases hName : vectorSpaceName? a with
                                  | none =>
                                      simp [hName] at h
                                      exact compiledConsistent_of_stateEq_conj h hs
                                  | some name =>
                                      cases hVec : vectorOfPattern? c with
                                      | none =>
                                          simp [hName, hVec] at h
                                          exact compiledConsistent_of_stateEq_conj h hs
                                      | some vec =>
                                          cases hVS : lookupVectorSpace? s name with
                                          | none =>
                                              simp [hName, hVec, hVS] at h
                                              exact compiledConsistent_of_stateEq_conj h hs
                                          | some vs =>
                                              simp [hName, hVec, hVS] at h
                                              exact compiledConsistent_of_vectorSpaceState_conj h hs
                                · by_cases hMatchK : ctor = "match-k"
                                  · subst hMatchK
                                    cases hK : intOfPattern? a with
                                    | none =>
                                        simp [hK] at h
                                        exact compiledConsistent_of_stateEq_conj h hs
                                    | some kI =>
                                        cases hName : vectorSpaceName? b with
                                        | none =>
                                            simp [hK, hName] at h
                                            exact compiledConsistent_of_stateEq_conj h hs
                                        | some name =>
                                            cases hVec : vectorOfPattern? c with
                                            | none =>
                                                simp [hK, hName, hVec] at h
                                                exact compiledConsistent_of_stateEq_conj h hs
                                            | some qv =>
                                                cases hVS : lookupVectorSpace? s name with
                                                | none =>
                                                    simp [hK, hName, hVec, hVS] at h
                                                    exact compiledConsistent_of_stateEq_conj h hs
                                                | some vs =>
                                                    simp [hK, hName, hVec, hVS] at h
                                                    exact compiledConsistent_of_stateEq_conj h hs
                                  · by_cases hMatchSri : ctor = "match-sri"
                                    · subst hMatchSri
                                      cases hK : intOfPattern? a with
                                      | none =>
                                          simp [hK] at h
                                          exact compiledConsistent_of_stateEq_conj h hs
                                      | some kI =>
                                          cases hName : vectorSpaceName? b with
                                          | none =>
                                              simp [hK, hName] at h
                                              exact compiledConsistent_of_stateEq_conj h hs
                                          | some name =>
                                              cases hVS : lookupVectorSpace? s name with
                                              | none =>
                                                  simp [hK, hName, hVS] at h
                                                  exact compiledConsistent_of_stateEq_conj h hs
                                              | some vs =>
                                                  simp [hK, hName, hVS] at h
                                                  exact compiledConsistent_of_stateEq_conj h hs
                                    · by_cases hMatchSRI : ctor = "match-SRI"
                                      · subst hMatchSRI
                                        cases hK : intOfPattern? a with
                                        | none =>
                                            simp [hK] at h
                                            exact compiledConsistent_of_stateEq_conj h hs
                                        | some kI =>
                                            cases hName : vectorSpaceName? b with
                                            | none =>
                                                simp [hK, hName] at h
                                                exact compiledConsistent_of_stateEq_conj h hs
                                            | some name =>
                                                cases hVS : lookupVectorSpace? s name with
                                                | none =>
                                                    simp [hK, hName, hVS] at h
                                                    exact compiledConsistent_of_stateEq_conj h hs
                                                | some vs =>
                                                    simp [hK, hName, hVS] at h
                                                    exact compiledConsistent_of_stateEq_conj h hs
                                      · by_cases hCatch3 : ctor = "catch"
                                        · subst hCatch3
                                          simp at h
                                          exact
                                            compiledConsistent_of_evalCoreChainState_conj
                                              fuel hEvalCorePres h hs
                                        · by_cases hIf3 : ctor = "if"
                                          · subst hIf3
                                            simp at h
                                            exact
                                              compiledConsistent_of_evalCoreChainState_conj
                                                fuel hEvalCorePres h hs
                                          · by_cases hLet : ctor = "let"
                                            · subst hLet
                                              simp at h
                                              exact
                                                compiledConsistent_of_evalCoreChainState_conj
                                                  fuel hEvalCorePres h hs
                                            ·
                                              have hFallback :
                                                  referenceIntrinsicApplyFallbackN fuel s ctor [a, b, c] =
                                                    some (s', out) := by
                                                simpa [hMatch, hFoldall, hAddVec, hMatchK,
                                                  hMatchSri, hMatchSRI, hCatch3, hIf3, hLet] using h
                                              exact
                                                p4_apply_branch_preserves
                                                  fuel hEvalCorePres hEvalForRulePres hFallback hs
                        | cons d rest4 =>
                            have hFallback :
                                referenceIntrinsicApplyFallbackN fuel s ctor (a :: b :: c :: d :: rest4) =
                                  some (s', out) := by
                              simpa using h
                            exact
                              p4_apply_branch_preserves
                                fuel hEvalCorePres hEvalForRulePres hFallback hs

private theorem compiledConsistent_of_referenceIntrinsicStatefulN_nonapply_step
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {term : Pattern} {s' : Session} {out : List Pattern}
    (hNotApply : ∀ ctor args, term ≠ .apply ctor args)
    (h : referenceIntrinsicStatefulN (fuel + 1) s term = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceIntrinsicStatefulN at h
  simp only [] at h
  split at h
  · rename_i _ out1 hPeTTa
    have hout : out1 = (s', out) := Option.some.inj h
    subst hout
    exact
      compiledConsistent_of_referencePettaCoreEvalIntrinsicN_result
        fuel hEvalCorePres hEvalCallablePres hPeTTa hs
  · split at h
    · rename_i _ _ _ out1 hPre
      split at hPre
      · rename_i out2 hStateE
        have hout : out2 = (s', out) :=
          (Option.some.inj hPre).trans (Option.some.inj h)
        subst hout
        exact
          compiledConsistent_of_referenceStateEffectsEvalIntrinsicN_result
            fuel hEvalCorePres hStateE hs
      · have hout : out1 = (s', out) := Option.some.inj h
        subst hout
        exact
          compiledConsistent_of_referenceStreamOpsEvalIntrinsicN_result
            fuel hEvalCorePres hIntrinsicPres hPre hs
    ·
      cases term with
      | fvar x =>
          simp at h
      | bvar n =>
          simp at h
      | lambda body =>
          simp at h
      | multiLambda n body =>
          simp at h
      | subst body repl =>
          simp at h
      | collection ct elems rest =>
          simp at h
      | apply ctor args =>
          exact False.elim (hNotApply ctor args rfl)

private theorem compiledConsistent_of_referenceIntrinsicStatefulN_step
    (fuel : Nat)
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1)
    (hEvalCallablePres :
      ∀ (s : Session) (fn : Pattern) (args : List Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1)
    (hEvalForRulePres :
      ∀ (s : Session) (expr : Pattern),
        CompiledConsistent s →
        CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        referenceIntrinsicStatefulN fuel s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {term : Pattern} {s' : Session} {out : List Pattern}
    (h : referenceIntrinsicStatefulN (fuel + 1) s term = some (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  cases term with
  | fvar x =>
      exact
        compiledConsistent_of_referenceIntrinsicStatefulN_nonapply_step
          fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
          (fun ctor args hEq => by cases hEq) h hs
  | bvar n =>
      exact
        compiledConsistent_of_referenceIntrinsicStatefulN_nonapply_step
          fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
          (fun ctor args hEq => by cases hEq) h hs
  | lambda body =>
      exact
        compiledConsistent_of_referenceIntrinsicStatefulN_nonapply_step
          fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
          (fun ctor args hEq => by cases hEq) h hs
  | multiLambda n body =>
      exact
        compiledConsistent_of_referenceIntrinsicStatefulN_nonapply_step
          fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
          (fun ctor args hEq => by cases hEq) h hs
  | subst body repl =>
      exact
        compiledConsistent_of_referenceIntrinsicStatefulN_nonapply_step
          fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
          (fun ctor args hEq => by cases hEq) h hs
  | collection ct elems rest =>
      exact
        compiledConsistent_of_referenceIntrinsicStatefulN_nonapply_step
          fuel hEvalCorePres hEvalCallablePres hIntrinsicPres
          (fun ctor args hEq => by cases hEq) h hs
  | apply ctor args =>
      exact
        compiledConsistent_of_referenceIntrinsicStatefulN_apply_step
          fuel hEvalCorePres hEvalCallablePres hEvalForRulePres hIntrinsicPres h hs


-- Joint fuel-induction: all four ...N functions preserve CompiledConsistent simultaneously.
-- Each (fuel+1) case delegates entirely to level (fuel), so the four claims close from the IH.
set_option maxHeartbeats 800000 in
private theorem refNPres : ∀ fuel, RefNPres fuel
  | 0 =>
      { callable := by
          intro s fn args hs
          simp [referenceEvalCallableApplyN]
          simpa using hs
        evalCore := by
          intro s term hs
          simpa [referenceEvalWithStateCoreN] using hs
        evalForRule := by
          intro s expr hs
          simp [referenceEvalForRuleEnumerationN]
          simpa using hs
        intrinsic := by
          intro s term s' out h hs
          simp [referenceIntrinsicStatefulN] at h }
  | fuel + 1 =>
      let ih := refNPres fuel
      { callable :=
          compiledConsistent_of_referenceEvalCallableApplyN_step fuel
            ih.evalCore ih.evalForRule ih.callable
        evalCore :=
          compiledConsistent_of_referenceEvalWithStateCoreN_step fuel
            ih.intrinsic
        evalForRule :=
          compiledConsistent_of_referenceEvalForRuleEnumerationN_step fuel
            ih.evalCore ih.intrinsic
        intrinsic := by
          intro s term s' out h hs
          exact
            compiledConsistent_of_referenceIntrinsicStatefulN_step fuel
              ih.evalCore ih.callable ih.evalForRule ih.intrinsic h hs }

private theorem refN_preservation_bundle (fuel : Nat) :
    (∀ (s : Session) (fn : Pattern) (args : List Pattern),
       CompiledConsistent s →
       CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1) ∧
    (∀ (s : Session) (term : Pattern),
       CompiledConsistent s →
       CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1) ∧
    (∀ (s : Session) (expr : Pattern),
       CompiledConsistent s →
       CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1) ∧
    (∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
       referenceIntrinsicStatefulN fuel s term = some (s', out) →
       CompiledConsistent s →
       CompiledConsistent s') := by
  let h := refNPres fuel
  exact ⟨h.callable, h.evalCore, h.evalForRule, h.intrinsic⟩

theorem compiledConsistent_of_referenceIntrinsicStatefulN
    (fuel : Nat) {s : Session} {term : Pattern} {s' : Session} {out : List Pattern}
    (h : referenceIntrinsicStatefulN fuel s term = some (s', out))
    (hs : CompiledConsistent s) : CompiledConsistent s' :=
  (refN_preservation_bundle fuel).2.2.2 s term s' out h hs

theorem compiledConsistent_of_referenceEvalWithStateCoreN
    (fuel : Nat) (s : Session) (term : Pattern) (hs : CompiledConsistent s) :
    CompiledConsistent (referenceEvalWithStateCoreN fuel s term).1 :=
  (refN_preservation_bundle fuel).2.1 s term hs

theorem compiledConsistent_of_referenceEvalForRuleEnumerationN
    (fuel : Nat) (s : Session) (expr : Pattern) (hs : CompiledConsistent s) :
    CompiledConsistent (referenceEvalForRuleEnumerationN fuel s expr).1 :=
  (refN_preservation_bundle fuel).2.2.1 s expr hs

theorem compiledConsistent_of_referenceEvalCallableApplyN
    (fuel : Nat) (s : Session) (fn : Pattern) (args : List Pattern)
    (hs : CompiledConsistent s) :
    CompiledConsistent (referenceEvalCallableApplyN fuel s fn args).1 :=
  (refN_preservation_bundle fuel).1 s fn args hs

-- Stage 3b.2: Preservation on F-kernel `.done` results.

/-- If `faithfulEvalWithStateCoreF` returns `.done (s', out)`, then `s'` is `CompiledConsistent`. -/
theorem faithfulEvalWithStateCoreF_preserves
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone : faithfulEvalWithStateCoreF fuel s term = .done (s', out))
    (hs : CompiledConsistent s) : CompiledConsistent s' := by
  cases fuel with
  | zero => simp [faithfulEvalWithStateCoreF] at hdone
  | succ n =>
      simp only [faithfulEvalWithStateCoreF] at hdone
      have hN : referenceEvalWithStateCoreN (n + 1) s term = (s', out) :=
        FuelResult.done.inj hdone
      have hpres := compiledConsistent_of_referenceEvalWithStateCoreN (n + 1) s term hs
      rw [hN] at hpres
      exact hpres

/-- If `faithfulIntrinsicStatefulF` returns `.done (some (s', out))`, then `s'` is `CompiledConsistent`. -/
theorem faithfulIntrinsicStatefulF_preserves
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone : faithfulIntrinsicStatefulF fuel s term = .done (some (s', out)))
    (hs : CompiledConsistent s) : CompiledConsistent s' := by
  cases fuel with
  | zero => simp [faithfulIntrinsicStatefulF] at hdone
  | succ n =>
      simp only [faithfulIntrinsicStatefulF] at hdone
      have hN : referenceIntrinsicStatefulN (n + 1) s term = some (s', out) :=
        FuelResult.done.inj hdone
      exact compiledConsistent_of_referenceIntrinsicStatefulN (n + 1) hN hs

/-- If `faithfulEvalCallableApplyF` returns `.done (s', out)`, then `s'` is `CompiledConsistent`. -/
theorem faithfulEvalCallableApplyF_preserves
    (fuel : Nat) (s : Session) (callable : Pattern) (args : List Pattern)
    (hdone : faithfulEvalCallableApplyF fuel s callable args = .done (s', out))
    (hs : CompiledConsistent s) : CompiledConsistent s' := by
  cases fuel with
  | zero => simp [faithfulEvalCallableApplyF] at hdone
  | succ n =>
      simp only [faithfulEvalCallableApplyF] at hdone
      have hN : referenceEvalCallableApplyN (n + 1) s callable args = (s', out) :=
        FuelResult.done.inj hdone
      have hpres := compiledConsistent_of_referenceEvalCallableApplyN (n + 1) s callable args hs
      rw [hN] at hpres
      exact hpres

/-- Public fuel-indexed faithful reference evaluator.
    Unlike `evalWithStateCoreN`, this makes fuel exhaustion explicit via `FuelResult`. -/
def evalWithStateCoreF (fuel : Nat) (s : Session) (term : Pattern) :
    FuelResult (Session × List Pattern) :=
  faithfulEvalWithStateCoreF fuel s term

/-- Public fuel-indexed faithful reference intrinsic evaluator.
    Unlike `intrinsicStatefulN`, this makes fuel exhaustion explicit via `FuelResult`. -/
def intrinsicStatefulF (fuel : Nat) (s : Session) (term : Pattern) :
    FuelResult (Option (Session × List Pattern)) :=
  faithfulIntrinsicStatefulF fuel s term

/-- `.done` from the public faithful evaluator agrees with the N-kernel evaluator. -/
theorem evalWithStateCoreF_done_eq_N
    (fuel : Nat) (s : Session) (term : Pattern) (res : Session × List Pattern)
    (hdone : evalWithStateCoreF fuel s term = .done res) :
    referenceEvalWithStateCoreN fuel s term = res := by
  exact faithfulEvalWithStateCoreF_done_eq_N fuel s term res hdone

/-- `.done` from the public faithful intrinsic evaluator agrees with the N-kernel intrinsic evaluator. -/
theorem intrinsicStatefulF_done_eq_N
    (fuel : Nat) (s : Session) (term : Pattern) (r : Option (Session × List Pattern))
    (hdone : intrinsicStatefulF fuel s term = .done r) :
    referenceIntrinsicStatefulN fuel s term = r := by
  exact faithfulIntrinsicStatefulF_done_eq_N fuel s term r hdone

/-- Successful faithful evaluation preserves session well-formedness. -/
theorem evalWithStateCoreF_preserves
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone : evalWithStateCoreF fuel s term = .done (s', out))
    (hs : WF s) :
    WF s' := by
  exact faithfulEvalWithStateCoreF_preserves fuel s term hdone hs

/-- Successful faithful intrinsic evaluation preserves session well-formedness. -/
theorem intrinsicStatefulF_preserves
    (fuel : Nat) (s : Session) (term : Pattern)
    (hdone : intrinsicStatefulF fuel s term = .done (some (s', out)))
    (hs : WF s) :
    WF s' := by
  exact faithfulIntrinsicStatefulF_preserves fuel s term hdone hs

/-- Public fuel-indexed reference evaluator (thin wrapper over the private mutual-block def). -/
def evalWithStateCoreN (fuel : Nat) (s : Session) (term : Pattern) :
    Session × List Pattern :=
  referenceEvalWithStateCoreN fuel s term

/-- Public wrapper for the fuel-indexed `intrinsicStateful` in the reference evaluator. -/
def referenceIntrinsicStatefulNPub (fuel : Nat) (s : Session) (term : Pattern) :
    Option (Session × List Pattern) :=
  referenceIntrinsicStatefulN fuel s term

/-- Public wrapper for the fuel-indexed `runNestedEffects` in the reference evaluator. -/
def referenceRunNestedEffectsNPub (fuel : Nat) (s : Session)
    (isRoot parentCallable : Bool) (term : Pattern) : Session × Pattern × Bool :=
  referenceRunNestedEffectsN fuel s isRoot parentCallable term

/-- The named concrete `ReferenceEval.Interface` used by `referenceEvalWithStateCoreN`.
    This is the canonical proof-facing interface: bridge predicates and simulation theorems
    should be stated in terms of this interface, not the copied `referenceRunNestedEffectsN`.
    See GPT-5.4 Pro Option E rationale. -/
def referenceEvalInterfaceN (fuel : Nat) :
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.Interface Session := {
  maxNodes := fun s => s.maxNodes
  maxSteps := fun s => s.maxSteps
  runNestedEffects := fun s isRoot p term => referenceRunNestedEffectsN fuel s isRoot p term
  intrinsicStateful := fun s term => referenceIntrinsicStatefulN fuel s term
  isEagerCallableHead := isEagerCallableHead
  step := step
  enqueueNext := enqueueNext
  insertUnique := insertUnique
  dedupPatterns := dedupPatterns
}

-- ─── @[simp] field projection lemmas ─────────────────────────────────────────

@[simp] theorem referenceEvalInterfaceN_maxNodes (fuel : Nat) :
    (referenceEvalInterfaceN fuel).maxNodes = fun s => s.maxNodes := rfl

@[simp] theorem referenceEvalInterfaceN_maxSteps (fuel : Nat) :
    (referenceEvalInterfaceN fuel).maxSteps = fun s => s.maxSteps := rfl

@[simp] theorem referenceEvalInterfaceN_intrinsicStateful (fuel : Nat) (s : Session) (term : Pattern) :
    (referenceEvalInterfaceN fuel).intrinsicStateful s term =
      referenceIntrinsicStatefulNPub fuel s term := rfl

@[simp] theorem referenceEvalInterfaceN_step (fuel : Nat) :
    (referenceEvalInterfaceN fuel).step = step := rfl

@[simp] theorem referenceEvalInterfaceN_enqueueNext (fuel : Nat) :
    (referenceEvalInterfaceN fuel).enqueueNext = enqueueNext := rfl

/-- `evalWithStateCoreN (fuel+1)` equals `evalWithStateCore` applied to the named interface. -/
theorem evalWithStateCoreN_succ (fuel : Nat) (s : Session) (term : Pattern) :
    evalWithStateCoreN (fuel + 1) s term =
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore
        (referenceEvalInterfaceN fuel) s term := by
  show referenceEvalWithStateCoreN (fuel + 1) s term = _
  unfold referenceEvalWithStateCoreN
  rfl

-- ─── Concrete unchanged-branch theorem ───────────────────────────────────────

/-- When `runNestedEffects` is passthrough, `intrinsicStateful` returns `none`,
    and `step` returns `[]`, the fuel-indexed evaluator returns `(s, [term])`.
    Thin wrapper over abstract `ReferenceEval.evalWithStateCore_unchanged`. -/
theorem evalWithStateCoreN_unchanged
    (fuel : Nat) (s : Session) (term : Pattern)
    (hNodes : s.maxNodes ≥ 1)
    (hSteps : 0 < s.maxSteps)
    (hRNE : Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
        (referenceEvalInterfaceN fuel) s true false term = (s, term, false))
    (hIntr : (referenceEvalInterfaceN fuel).intrinsicStateful s term = none)
    (hStep : step s term = []) :
    evalWithStateCoreN (fuel + 1) s term = (s, [term]) := by
  simp only [evalWithStateCoreN_succ]
  exact Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore_unchanged
    (referenceEvalInterfaceN fuel) s term hNodes hSteps hRNE hIntr hStep

/-- When `runNestedEffects` is passthrough, `intrinsicStateful` returns `none`,
    and `step` returns a non-empty `reducts`, the fuel-indexed evaluator one-steps to
    processing the reducts through the work-queue at depth 1.
    This is the ref-evaluator side of the directIntrinsic branch. -/
theorem evalWithStateCoreN_step_nonempty
    (fuel : Nat) (s : Session) (term : Pattern)
    (hNodes : s.maxNodes ≥ 1)
    (hSteps : 0 < s.maxSteps)
    (hRNE : Algorithms.MeTTa.Simple.Backend.ReferenceEval.runNestedEffects
        (referenceEvalInterfaceN fuel) s true false term = (s, term, false))
    (hIntr : (referenceEvalInterfaceN fuel).intrinsicStateful s term = none)
    (reducts : List Pattern)
    (hStep : step s term = reducts)
    (hNonempty : reducts.isEmpty = false) :
    evalWithStateCoreN (fuel + 1) s term =
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful
        (referenceEvalInterfaceN fuel) s (s.maxNodes - 1)
        ((referenceEvalInterfaceN fuel).enqueueNext [] 1 reducts) [] := by
  simp only [evalWithStateCoreN_succ]
  -- Unfold evalWithStateCore → evalAuxStateful with maxNodes fuel
  unfold Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore
  -- Use the one-step lemma at depth 0
  obtain ⟨n, hN⟩ : ∃ n, (referenceEvalInterfaceN fuel).maxNodes s = n + 1 :=
    ⟨s.maxNodes - 1, by simp [referenceEvalInterfaceN]; omega⟩
  simp only [hN]
  rw [Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalAuxStateful_step_of_intrinsicNone
    (referenceEvalInterfaceN fuel) s s term term false 0 [] [] n
    hRNE (by simp [referenceEvalInterfaceN]; exact hSteps) hIntr]
  -- The LHS has `have reducts := iface.step s term; if reducts.isEmpty ...`
  -- Substitute iface.step = step, then step s term = reducts, then reducts.isEmpty = false
  simp only [referenceEvalInterfaceN_step, hStep, hNonempty,
    referenceEvalInterfaceN_enqueueNext, Bool.false_eq_true, ite_false]
  -- Now: evalAuxStateful ... s n (enqueueNext [] (0+1) reducts) [] = ... s (s.maxNodes-1) (enqueueNext [] 1 reducts) []
  have hNEq : n = s.maxNodes - 1 := by simp [referenceEvalInterfaceN] at hN; omega
  subst hNEq
  simp

-- ─── R-2: intrinsicStatefulN_none for builtin terms under StrictContext-like conditions ──
-- This is NOT a free hypothesis — it is derived from noOverlap + argsIrreducible + builtin.

/-- The combined set of heads handled by all three evalIntrinsic dispatchers AND
    the ~50-head match inside `referenceIntrinsicStatefulN`. Arithmetic builtins
    (`+`, `-`, `*`, `<`, etc.) are NOT in this set. -/
private def intrinsicStatefulSpecialHeads : List String :=
  -- PeTTaCore.evalIntrinsic heads:
  Algorithms.MeTTa.Simple.Semantics.PeTTaCore.evalIntrinsicSpecialHeads ++
  -- StateEffects.evalIntrinsic heads:
  Algorithms.MeTTa.Simple.Semantics.StateEffects.evalIntrinsicSpecialHeads ++
  -- StreamOps.evalIntrinsic heads:
  Algorithms.MeTTa.Simple.Semantics.StreamOps.evalIntrinsicSpecialHeads ++
  -- Heads from the ~50-branch match in referenceIntrinsicStatefulN:
  ["add-atom", "add-atom!", "remove-atom", "remove-atom!",
   "remove-all-atoms", "remove-all-atoms!", "get-atoms", "get-atoms!",
   "match", "case", "foldall", "forall",
   "cut", "Predicate", "find", "succeedsPredicate",
   "add-translator-rule!", "remove-translator-rule!",
   "new-atom-vectorspace", "add-atom-vector", "add-atom-SRI",
   "match-k", "match-sri", "match-SRI",
   "once", "nop", "catch", "msort", "superpose", "hide", "space",
   "collapse", "translatePredicate", "if", "let", "let*",
   "progn", "prog1", "Expr", "repr", "atom-of"]

-- ─── Generic foldl identity lemma (GPT-5.4 Pro Package A) ────────────────────

private theorem foldl_eq_init_of_forall_eq_self
    {α β : Type} (xs : List β) (f : α → β → α) (init : α)
    (h : ∀ x ∈ xs, ∀ acc, f acc x = acc) :
    xs.foldl f init = init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    have hx : f init x = init := h x (by simp) init
    simp [List.foldl, hx]
    apply ih
    intro y hy acc
    exact h y (by simp [hy]) acc

/-- For builtin ctors not in the intrinsicStateful special-head set, with args that are
    step-irreducible, under noOverlap, `referenceIntrinsicStatefulN` returns `none`.
    This is NOT a free hypothesis — it is derived from session conditions.

    Proof traces through: PeTTaCore.evalIntrinsic → StateEffects.evalIntrinsic →
    StreamOps.evalIntrinsic → ~50-head match → referenceIntrinsicApplyFallbackN →
    referenceIntrinsicApplyDispatchTailN, all returning `none` for non-special builtins. -/
theorem referenceIntrinsicStatefulN_none_of_builtin_strict
    (fuel : Nat) (s : Session) (ctor : String) (argsV : List Pattern)
    (hNotSpecial : ctor ∉ intrinsicStatefulSpecialHeads)
    (hNoCompat : Algorithms.MeTTa.Simple.Semantics.Dispatch.compatFunctionHeadRewrite
        { rewrites := fun s => s.bundle.language.rewrites
          premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
          eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          normalizePattern := normalizeDollarVars
          dedupBindings := dedupBindings }
        s (.apply ctor argsV) = (s, []))
    (hNoConstraint : Algorithms.MeTTa.Simple.Semantics.Dispatch.hasCompatHeadConstraintRule
        { rewrites := fun s => s.bundle.language.rewrites
          premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
          eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          normalizePattern := normalizeDollarVars
          dedupBindings := dedupBindings }
        s ctor argsV.length = false)
    (hIrreducible : ∀ a ∈ argsV,
        (match referenceIntrinsicStatefulN fuel s a with
         | some (_sA, outA) => if outA.isEmpty then step s a else outA
         | none => step s a).filter (· != a) = [])
    (hNoPartialArity :
        match builtinPartialMinArity? ctor with
        | some minArity => argsV.length ≥ minArity
        | none => True)
    (hNoArityPartial :
        ¬((rewriteAritiesForHead s ctor).any (· > argsV.length) = true ∧
          !(rewriteAritiesForHead s ctor).any (· == argsV.length) ∧
          !argsV.isEmpty)) :
    referenceIntrinsicStatefulN (fuel + 1) s (.apply ctor argsV) = none := by
  simp only [intrinsicStatefulSpecialHeads, List.mem_append, List.mem_cons, List.not_mem_nil,
    not_or, not_false_eq_true] at hNotSpecial
  -- The first simp destructured hNotSpecial into nested conjunctions.
  -- Extract memberships for the three evalIntrinsic modules.
  -- After simp, hNotSpecial has shape: ((¬∈PC ∧ ¬∈SE) ∧ ¬∈SO) ∧ (¬= heads...)
  -- But the sub-list memberships are still in ¬∈ form, not destructured.
  -- hNotSpecial : ((¬∈PC ∧ ¬∈SE) ∧ ¬∈SO) ∧ (¬= direct heads...)
  obtain ⟨⟨⟨hPC_not, hSE_not⟩, hSO_not⟩, hMatchHeads⟩ := hNotSpecial
  -- Unfold one level
  unfold referenceIntrinsicStatefulN
  -- Layer 1: PeTTaCore.evalIntrinsic returns none
  simp only [Semantics.PeTTaCore.evalIntrinsic_none_of_nonSpecial _ s ctor argsV hPC_not]
  -- Layer 2: StateEffects.evalIntrinsic returns none
  simp only [Semantics.StateEffects.evalIntrinsic_none_of_nonSpecial _ s ctor argsV hSE_not]
  -- Layer 3: StreamOps.evalIntrinsic returns none
  simp only [Semantics.StreamOps.evalIntrinsic_none_of_nonSpecial _ s ctor argsV hSO_not]
  -- Now preIntrinsic = none. The ~50-head match + referenceIntrinsicApplyFallbackN remain.
  -- Use a single simp_all that handles everything:
  -- 1. The ~50-head match (hMatchHeads contradicts each specific head)
  -- 2. referenceIntrinsicApplyFallbackN / referenceIntrinsicApplyDispatchTailN unfolding
  -- 3. hNoCompat, hNoConstraint, hIrreducible, hNoPartialArity, hNoArityPartial all applied
  -- Give simp_all large heartbeat budget for the ~50 branches + foldl simplification.
  -- Do NOT use simp_all for the fallback — it normalizes terms in ways that break
  -- later rw/simp steps. Instead, use simp_all ONLY for the ~50-head match,
  -- then handle the fallback manually.
  simp_all
  -- After simp_all: goal is referenceIntrinsicApplyFallbackN fuel s ctor argsV = none
  -- GPT-5.4 Pro Package A (Response #4): close the foldl + arity tail
  have hFilterNilOfAllEq :
      ∀ {base : Pattern} {xs : List Pattern},
        (∀ x, x ∈ xs → x = base) → xs.filter (fun x => x != base) = [] := by
    intro base xs hEq
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx : x = base := hEq x (by simp)
      have hxs : ∀ y, y ∈ xs → y = base := fun y hy => hEq y (by simp [hy])
      simp [hx, ih hxs]
  let redAt : Nat → List Pattern := fun i =>
    match referenceIntrinsicStatefulN fuel s (argsV[i]?.getD (Pattern.apply "" [])) with
    | some (_sA, outA) =>
        if outA = [] then s.step (argsV[i]?.getD (Pattern.apply "" [])) else outA
    | none => s.step (argsV[i]?.getD (Pattern.apply "" []))
  let branchAt : Nat → List Pattern := fun i =>
    List.map (fun a' => Pattern.apply ctor (List.take i argsV ++ a' :: List.drop (i + 1) argsV))
      (List.filter (fun a' => a' != argsV[i]?.getD (Pattern.apply "" [])) (redAt i))
  have hBranchNil : ∀ i ∈ List.range argsV.length, branchAt i = [] := by
    intro i hi
    have hiLt : i < argsV.length := by simpa using List.mem_range.mp hi
    have hiMem : argsV[i]?.getD (Pattern.apply "" []) ∈ argsV := by simp [hiLt]
    have hAll : ∀ a₂, a₂ ∈ redAt i → a₂ = argsV[i]?.getD (Pattern.apply "" []) := by
      intro a₂ ha₂; simpa [redAt] using (hIrreducible (argsV[i]?.getD (Pattern.apply "" [])) hiMem a₂ ha₂)
    simp [branchAt, hFilterNilOfAllEq hAll]
  -- GPT-5.4 Pro #2 approach: prove hDispatchNone separately, then close.
  have hArityGuardFalse :
      (((s.rewriteAritiesForHead ctor).any (fun n => decide (n > argsV.length)) &&
        !((s.rewriteAritiesForHead ctor).any (fun n => n == argsV.length)) &&
        !argsV.isEmpty) = false) := by
    by_cases hEmpty : argsV = []
    · simp [hEmpty]
    · by_cases hHasLarger :
        (s.rewriteAritiesForHead ctor).any (fun n => decide (n > argsV.length)) = true
      · by_cases hHasExact :
          (s.rewriteAritiesForHead ctor).any (fun n => n == argsV.length) = true
        · simp [hHasLarger, hHasExact]
        · have hHasLarger' := hHasLarger
          rw [List.any_eq_true] at hHasLarger'
          obtain ⟨x, hxMem, hxGt⟩ := hHasLarger'
          have hxLt : argsV.length < x := by simpa using hxGt
          have hNoExact' := hHasExact
          rw [List.any_eq_true, not_exists] at hNoExact'
          have hNoExact : ∀ y, y ∈ s.rewriteAritiesForHead ctor → ¬ y = argsV.length := by
            intro y hy hyEq
            exact hNoExact' y ⟨hy, by simpa [hyEq]⟩
          exact False.elim (hEmpty (hNoArityPartial x hxMem hxLt hNoExact))
      · simp [hHasLarger]
  have hDispatchNone :
      referenceIntrinsicApplyDispatchTailN fuel
        { rewrites := fun s => s.bundle.language.rewrites
          premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
          eval := fun s term => referenceEvalWithStateCoreN fuel s term
          evalForRuleEnumeration := fun s expr => referenceEvalForRuleEnumerationN fuel s expr
          applyBindings := applyBindingsCompat
          matchPattern := matchPatternMeTTa
          normalizePattern := normalizeDollarVars
          dedupBindings := dedupBindings }
        s ctor argsV = none := by
    unfold referenceIntrinsicApplyDispatchTailN
    -- After unfold + simp [hNoCompat, hNoConstraint], the foldl was reduced to map/flatten.
    -- hFoldlNil talks about foldl, so use branchAt-based hFlat instead.
    have hFlat : (List.map branchAt (List.range argsV.length)).flatten = [] := by
      rw [List.flatten_eq_nil_iff]
      intro l hl
      rw [List.mem_map] at hl
      obtain ⟨i, hi, rfl⟩ := hl
      exact hBranchNil i hi
    simp [hNoCompat, hNoConstraint, hFlat, hArityGuardFalse, branchAt, redAt]
  show referenceIntrinsicApplyFallbackN fuel s ctor argsV = none
  unfold referenceIntrinsicApplyFallbackN
  split
  · rename_i minA hMinA
    have hGe : argsV.length ≥ minA := by simp [hMinA] at hNoPartialArity; exact hNoPartialArity
    have hNotLt : ¬ argsV.length < minA := Nat.not_lt_of_ge hGe
    simpa [hNotLt, hDispatchNone]
  · simpa [hDispatchNone]


/-- Unconditional session-WF preservation for the fuel-indexed evaluator. -/
theorem evalWithStateCoreN_preserves
    (fuel : Nat) (s : Session) (term : Pattern) (hs : WF s) :
    WF (evalWithStateCoreN fuel s term).1 :=
  compiledConsistent_of_referenceEvalWithStateCoreN fuel s term hs

/-- The `DeterministicEval.Interface` used by the N-kernel deterministic evaluator.
    Exposed for the DeterministicBridge proof layer. -/
def detEvalInterface (outerFuel : Nat) :
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.Interface Session :=
  mkDeterministicEvalInterface
    (fun s' t => evalWithStateCoreN outerFuel s' t)
    (fun s' fn args => referenceEvalCallableApplyN outerFuel s' fn args)

theorem detEvalInterface_eq_standalone (outerFuel : Nat) (s : Session) (detFuel : Nat)
    (term : Pattern) :
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval
      (detEvalInterface outerFuel) s detFuel term =
    referenceEvalDeterministicCoreNStandalone outerFuel s detFuel term := by
  unfold detEvalInterface evalWithStateCoreN referenceEvalDeterministicCoreNStandalone
  rfl

/-- Fuel-indexed total reference intrinsic evaluator (no `partial def`, no `sorry`).
    Returns `none` when the term is not an intrinsic or when fuel is exhausted.
    Unconditionally preserves `WF` on `some` outputs. -/
def intrinsicStatefulN (fuel : Nat) (s : Session) (term : Pattern) :
    Option (Session × List Pattern) :=
  referenceIntrinsicStatefulN fuel s term

/-- Unconditional session-WF preservation for `intrinsicStatefulN` on `some` results. -/
theorem intrinsicStatefulN_preserves
    (fuel : Nat) {s : Session} {term : Pattern}
    {s' : Session} {out : List Pattern}
    (h : intrinsicStatefulN fuel s term = some (s', out))
    (hs : WF s) : WF s' :=
  compiledConsistent_of_referenceIntrinsicStatefulN fuel h hs

/-- At positive fuel, the faithful evaluator is definitionally just the explicit-status
    wrapper around the total N-kernel evaluator. -/
theorem evalWithStateCoreF_eq_done_of_pos
    (fuel : Nat) (s : Session) (term : Pattern)
    (hFuel : 0 < fuel) :
    evalWithStateCoreF fuel s term = .done (evalWithStateCoreN fuel s term) := by
  cases fuel with
  | zero =>
      cases Nat.not_lt_zero 0 hFuel
  | succ n =>
      rfl

/-- At positive fuel, the faithful intrinsic evaluator is definitionally just the
    explicit-status wrapper around the total N-kernel intrinsic evaluator. -/
theorem intrinsicStatefulF_eq_done_of_pos
    (fuel : Nat) (s : Session) (term : Pattern)
    (hFuel : 0 < fuel) :
    intrinsicStatefulF fuel s term = .done (intrinsicStatefulN fuel s term) := by
  cases fuel with
  | zero =>
      cases Nat.not_lt_zero 0 hFuel
  | succ n =>
      rfl

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
    (hEval : referenceEvalDeterministicCore s fuel term = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.DeterministicEval.eval_preserves
      deterministicEvalInterface CompiledConsistent
      (deterministicEvalInterface_preservation hEvalCorePres hEvalCallablePres)
      s fuel term hs
  have hPresRef : CompiledConsistent (referenceEvalDeterministicCore s fuel term).1 := by
    simpa [referenceEvalDeterministicCore] using hPres
  have hState : (referenceEvalDeterministicCore s fuel term).1 = s' := by
    exact congrArg Prod.fst hEval
  simpa [hState] using hPresRef

private theorem compiledConsistent_of_referenceEvalWithStateCore
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    (s : Session) (term : Pattern)
    (hs : CompiledConsistent s) :
    CompiledConsistent (referenceEvalWithStateCore s term).1 := by
  have hPres :
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.Preservation
        referenceEvalInterface CompiledConsistent := by
    have hIntrinsicPresRef :
        ∀ {s : Session} {term : Pattern} {s' : Session} {out : List Pattern},
          referenceEvalInterface.intrinsicStateful s term = some (s', out) →
          CompiledConsistent s →
          CompiledConsistent s' := by
      intro s term s' out hIntr hs
      simpa [referenceEvalInterface] using hIntrinsicPres s term s' out hIntr hs
    exact
      Algorithms.MeTTa.Simple.Backend.ReferenceEval.preservation_of_intrinsicStateful
        referenceEvalInterface CompiledConsistent hIntrinsicPresRef
  simpa [referenceEvalWithStateCore, referenceEvalInterface] using
    Algorithms.MeTTa.Simple.Backend.ReferenceEval.evalWithStateCore_preserves
      referenceEvalInterface CompiledConsistent hPres s term hs

private def referenceEvalForRuleEnumeration (s : Session) (expr : Pattern) :
    Session × List Pattern :=
  match intrinsicStateful s expr with
  | some (s1, out) =>
      let out' := if out.isEmpty then [expr] else out
      (s1, out')
  | none =>
      let (s1, out0) := referenceEvalWithStateCore s expr
      let out := if out0.isEmpty then [expr] else out0
      (s1, out)

private theorem compiledConsistent_of_referenceEvalForRuleEnumeration
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {expr : Pattern} {s' : Session} {out : List Pattern}
    (hEval : referenceEvalForRuleEnumeration s expr = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold referenceEvalForRuleEnumeration at hEval
  cases hIntr : intrinsicStateful s expr with
  | none =>
      simp [hIntr] at hEval
      have hPres : CompiledConsistent (referenceEvalWithStateCore s expr).1 :=
        compiledConsistent_of_referenceEvalWithStateCore hIntrinsicPres s expr hs
      have hState : (referenceEvalWithStateCore s expr).1 = s' := hEval.1
      simpa [hState] using hPres
  | some res =>
      rcases res with ⟨s1, out0⟩
      simp [hIntr] at hEval
      have hPres : CompiledConsistent s1 :=
        hIntrinsicPres s expr s1 out0 hIntr hs
      have hState : s1 = s' := hEval.1
      simpa [hState] using hPres

private def proofEvalForRuleEnumeration (s : Session) (expr : Pattern) :
    Session × List Pattern :=
  match intrinsicStateful s expr with
  | some (s1, out) =>
      let out' := if out.isEmpty then [expr] else out
      (s1, out')
  | none =>
      let (s1, out0) := evalWithStateCore s expr
      let out := if out0.isEmpty then [expr] else out0
      (s1, out)

private theorem compiledConsistent_of_proofEvalForRuleEnumeration
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {expr : Pattern} {s' : Session} {out : List Pattern}
    (hEval : proofEvalForRuleEnumeration s expr = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  unfold proofEvalForRuleEnumeration at hEval
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

private def dispatchInterface :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
  rewrites := fun s => s.bundle.language.rewrites
  premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
  eval := evalWithStateCore
  evalForRuleEnumeration := proofEvalForRuleEnumeration
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
  normalizePattern := normalizeDollarVars
  dedupBindings := dedupBindings
}

private theorem dispatchInterface_preservation
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.Preservation
      dispatchInterface CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    evalForRuleEnumeration_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (evalWithStateCore s term).1 :=
      hEvalCorePres s term hs
    have hState : (evalWithStateCore s term).1 = s' := by
      simpa [dispatchInterface] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s expr s' out hEval hs
    exact compiledConsistent_of_proofEvalForRuleEnumeration hEvalCorePres hIntrinsicPres hEval hs

private theorem compiledConsistent_of_enumerateCallByRules
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {expr : Pattern} {s' : Session} {out : List Pattern}
    (hEnum :
      Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
        dispatchInterface s expr = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules_preserves
      dispatchInterface CompiledConsistent
      (dispatchInterface_preservation hEvalCorePres hIntrinsicPres) s expr hs
  simpa [hEnum] using hPres

private theorem compiledConsistent_of_refineCallableOut
    (hEvalCorePres :
      ∀ (s : Session) (term : Pattern),
        CompiledConsistent s →
        CompiledConsistent (evalWithStateCore s term).1)
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {expr : Pattern} {baseOut : List Pattern} {s' : Session} {out : List Pattern}
    (hRefine :
      Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
        dispatchInterface s expr baseOut = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration_preserves
      dispatchInterface CompiledConsistent
      (dispatchInterface_preservation hEvalCorePres hIntrinsicPres) s expr baseOut hs
  simpa [hRefine] using hPres

private def referenceDispatchInterface :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.Interface Session := {
  rewrites := fun s => s.bundle.language.rewrites
  premiseFreeRulesForHeadArity := premiseFreeRulesForHeadArity
  eval := referenceEvalWithStateCore
  evalForRuleEnumeration := referenceEvalForRuleEnumeration
  applyBindings := applyBindingsCompat
  matchPattern := matchPatternMeTTa
  normalizePattern := normalizeDollarVars
  dedupBindings := dedupBindings
}

private def referenceEvalCallableApply (s : Session)
    (callable : Pattern) (args : List Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Semantics.Dispatch.evalCallableApply
    referenceDispatchInterface s callable args

private theorem referenceDispatchInterface_preservation
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s') :
    Algorithms.MeTTa.Simple.Semantics.Dispatch.Preservation
      referenceDispatchInterface CompiledConsistent := by
  refine {
    eval_preserves := ?_,
    evalForRuleEnumeration_preserves := ?_
  }
  · intro s term s' out hEval hs
    have hPres : CompiledConsistent (referenceEvalWithStateCore s term).1 :=
      compiledConsistent_of_referenceEvalWithStateCore hIntrinsicPres s term hs
    have hState : (referenceEvalWithStateCore s term).1 = s' := by
      simpa [referenceDispatchInterface] using congrArg Prod.fst hEval
    simpa [hState] using hPres
  · intro s expr s' out hEval hs
    exact compiledConsistent_of_referenceEvalForRuleEnumeration hIntrinsicPres hEval hs

private theorem compiledConsistent_of_referenceEnumerateCallByRules
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {expr : Pattern} {s' : Session} {out : List Pattern}
    (hEnum :
      Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules
        referenceDispatchInterface s expr = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.Dispatch.enumerateCallByRules_preserves
      referenceDispatchInterface CompiledConsistent
      (referenceDispatchInterface_preservation hIntrinsicPres) s expr hs
  simpa [hEnum] using hPres

private theorem compiledConsistent_of_referenceRefineCallableOut
    (hIntrinsicPres :
      ∀ (s : Session) (term : Pattern) (s' : Session) (out : List Pattern),
        intrinsicStateful s term = some (s', out) →
        CompiledConsistent s →
        CompiledConsistent s')
    {s : Session} {expr : Pattern} {baseOut : List Pattern} {s' : Session} {out : List Pattern}
    (hRefine :
      Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration
        referenceDispatchInterface s expr baseOut = (s', out))
    (hs : CompiledConsistent s) :
    CompiledConsistent s' := by
  have hPres :=
    Algorithms.MeTTa.Simple.Semantics.Dispatch.refineCallableOutWithArgEnumeration_preserves
      referenceDispatchInterface CompiledConsistent
      (referenceDispatchInterface_preservation hIntrinsicPres) s expr baseOut hs
  simpa [hRefine] using hPres

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

private def noDeterministicReducerOverlap (s : Session) : Bool :=
  Algorithms.MeTTa.Simple.Backend.SessionDeterministic.noDeterministicReducerOverlap
    deterministicSearchInterface s

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
  noDeterministicReducerOverlap := noDeterministicReducerOverlap
  noCoreBuiltinOverrides := fun s => s.coreBuiltinsUnmodified
  evalDeterministicCore := fun s detFuel term =>
    referenceEvalDeterministicCoreNStandalone (referenceProofFuel s) s detFuel term
  evalWithStateCore := fun s term => referenceEvalWithStateCoreN (referenceProofFuel s) s term
  isResolvedDeterministicResult :=
    Algorithms.MeTTa.Simple.Semantics.DeterministicStrategy.isResolvedDeterministicResult
  acceptUnchangedDeterministic := acceptUnchangedDeterministic
}

/-- When `optimizedBackendInterface.noDeterministicReducerOverlap s = true`,
    every rewrite rule satisfies `ruleDisjointFromBuiltins`. -/
theorem noOverlap_implies_disjoint_rules (s : Session)
    (h : optimizedBackendInterface.noDeterministicReducerOverlap s = true) :
    ∀ r ∈ s.bundle.language.rewrites,
      Algorithms.MeTTa.Simple.Backend.SessionDeterministic.ruleDisjointFromBuiltins r = true := by
  simp only [optimizedBackendInterface, noDeterministicReducerOverlap,
    Algorithms.MeTTa.Simple.Backend.SessionDeterministic.noDeterministicReducerOverlap,
    deterministicSearchInterface] at h
  exact List.all_eq_true.mp h

def evalWithState (s : Session) (term : Pattern) : Session × List Pattern :=
  Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState optimizedBackendInterface s term

theorem evalWithState_eq_optimizedBackend
    (s : Session) (term : Pattern) :
    evalWithState s term =
      Algorithms.MeTTa.Simple.Backend.OptimizedEval.evalWithState
        optimizedBackendInterface s term := by
  rfl

theorem optimizedBackendInterface_evalWithStateCore_eq_N
    (s : Session) (term : Pattern) :
    optimizedBackendInterface.evalWithStateCore s term =
      evalWithStateCoreN (referenceProofFuel s) s term := by
  rfl

theorem evalWithState_eq_reference_of_guard_failure
    (s : Session) (term : Pattern)
    (hFail :
      optimizedBackendInterface.shouldUseDeterministicInStrict term = false ∨
      optimizedBackendInterface.hasDeterministicBlockingRewriteBodies s = true ∨
      optimizedBackendInterface.hasMultipleRootRuleChoices s term = true ∨
      optimizedBackendInterface.noDeterministicReducerOverlap s = false ∨
      optimizedBackendInterface.noCoreBuiltinOverrides s = false ∨
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
        optimizedBackendInterface.noDeterministicReducerOverlap s = true →
        optimizedBackendInterface.noCoreBuiltinOverrides s = true →
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

-- REMOVED (truth audit 2026-03-17): 3 theorems deleted here:
--   evalWithState_eq_reference_of_deterministic_agreement_raw_guard
--   compiledConsistent_evalWithState_of_reference_and_deterministic_agreement
--   compiledConsistent_applyStmt_eval_of_reference_and_deterministic_agreement
-- hAgreeRaw was confirmed false (3rd falsity vector: translateCall + reducible args).
-- Replaced by pointwise FastPathEq in Backend/SessionRefinement.lean.
-- The guard-failure theorem (evalWithState_eq_reference_of_guard_failure) is retained above.
-- The generic evalWithState_eq_reference_of_deterministic_agreement is retained (it correctly
-- takes hAgree as a parameter — the caller must provide a true agreement hypothesis).
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
      let s1 :=
        if rel.startsWith "intrinsic:" then
          { s0 with coreBuiltinsUnmodified := false }
        else
          s0
      let s' := withMessage s1 s!"added builtin fact {rel}/{tuple.length}"
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
  | .import _space _path =>
      let s0 := noteApplied s
      let s' := withMessage s0 s!"import directive recorded (not yet implemented)"
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
  | .defineRule lhs rhs _premises =>
      let rule : RewriteRule := {
        name := mkRuleName s
        typeContext := []
        premises := []  -- TODO: convert Pattern premises to Premise type
        left := lhs
        right := rhs
      }
      let rules' := s.bundle.language.rewrites ++ [rule]
      let bundle' : SpecBundle := {
        s.bundle with language := { s.bundle.language with rewrites := rules' }
      }
      let s0 := noteApplied (withBundleCompiled s bundle')
      let s' := withMessage s0 s!"loaded rule {rule.name} via defineRule"
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
