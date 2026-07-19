/-
# Cross-runtime fixtures for Pure typed-hole refinement

This executable renders the frozen DTTBench-31 statement encodings, legal
state transitions, and named positive/negative traces.  The caller supplies
fresh source hashes; `check` rejects byte-level artifact drift.
-/

import Mettapedia.GSLT.LanguageDef.Pure.DTTBench31
import Mettapedia.GSLT.LanguageDef.Pure.Refinement

namespace Mettapedia.GSLT.LanguageDef.PureFixtures

open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureDTTBench31
open Mettapedia.GSLT.LanguageDef.PureRefinement

private def jsonEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c => c.toString

private def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonEscapeChar) ++ "\""

private def jsonBool (value : Bool) : String :=
  if value then "true" else "false"

private def jsonArray (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def renderNatArray (values : List Nat) : String :=
  jsonArray (values.map toString)

private def renderOptionNat : Option Nat → String
  | none => "null"
  | some value => toString value

private def renderOptionString : Option String → String
  | none => "null"
  | some value => jsonString value

private def actionName : Action → String
  | .selectHole _ => "select_hole"
  | .selectBoundHead _ => "select_bound_head"
  | .createDependentSpine _ => "create_dependent_spine"
  | .finish => "finish"

private def actionArgument? : Action → Option Nat
  | .selectHole hole => some hole
  | .selectBoundHead index => some index
  | .createDependentSpine arity => some arity
  | .finish => none

private def renderAction (action : Action) : String :=
  "{" ++
    "\"kind\":" ++ jsonString (actionName action) ++ "," ++
    "\"argument\":" ++ renderOptionNat (actionArgument? action) ++
  "}"

private def phaseName : Core → String
  | .needHole .. => "need_hole"
  | .needHead .. => "need_head"
  | .needSpine .. => "need_spine"
  | .done .. => "done"
  | .finished .. => "finished"

private def coreContextLength : Core → Nat
  | .needHole _ context _ _ => context.length
  | .needHead _ context _ _ => context.length
  | .needSpine _ context _ _ _ _ => context.length
  | .done _ => 0
  | .finished _ => 0

private def coreTarget? : Core → Option Expr
  | .needHole _ _ target _ => some target
  | .needHead _ _ target _ => some target
  | .needSpine _ _ target _ _ _ => some target
  | .done _ => none
  | .finished _ => none

private def coreSelectedHead? : Core → Option Nat
  | .needSpine _ _ _ _ head _ => some head
  | _ => none

private def coreSpineLength? : Core → Option Nat
  | .needSpine _ _ _ _ _ headType => some headType.piArity
  | _ => none

private def legalActions (goal : Expr) (state : State) : List Action :=
  (rawActions state.core).filter fun action => actionLegal goal state action

private def renderState (goal : Expr) (state : State) : String :=
  let targetCode := match coreTarget? state.core with
    | none => "null"
    | some target => renderNatArray target.encode
  "{" ++
    "\"phase\":" ++ jsonString (phaseName state.core) ++ "," ++
    "\"tokens_emitted\":" ++ toString state.tokensEmitted ++ "," ++
    "\"max_len\":" ++ toString state.maxLen ++ "," ++
    "\"hole_count\":" ++ toString state.core.holes.length ++ "," ++
    "\"context_length\":" ++ toString (coreContextLength state.core) ++ "," ++
    "\"target_code\":" ++ targetCode ++ "," ++
    "\"selected_head\":" ++ renderOptionNat (coreSelectedHead? state.core) ++ "," ++
    "\"computed_spine_length\":" ++ renderOptionNat (coreSpineLength? state.core) ++ "," ++
    "\"legal_actions\":" ++ jsonArray ((legalActions goal state).map renderAction) ++
  "}"

/-! ## Small semantic fixtures exercising every policy-visible phase -/

/-- `A : Type, x : A ⊢ x : A`. -/
def identityGoal : Expr :=
  pure_type% ((A : Type) → (x : A) → A)

def identityTerm : Nf :=
  .lam .sort (.lam (.bvar 0) (.head 0 []))

def identityTrace : List Action := encode identityTerm

/-- `A, P, x, h ⊢ h x : P x`, exercising dependent substitution. -/
def dependentGoal : Expr :=
  pure_type% (
    (A : Type) → (P : (a : A) → Type) → (x : A) →
      (h : (a : A) → P a) → P x
  )

def dependentTerm : Nf :=
  .lam .sort
    (.lam fixtureFamily
      (.lam (.bvar 1)
        (.lam fixtureHeadType (.head 0 [.head 1 []]))))

def dependentTrace : List Action := encode dependentTerm

/-- A nested binder where a stale index for `x` would instead capture `B`. -/
def captureGoal : Expr :=
  pure_type% ((A : Type) → (x : A) → (B : Type) → A)

theorem identityTerm_typed : HasType [] identityTerm identityGoal := by
  apply inferNf_sound
  rfl

theorem dependentTerm_typed : HasType [] dependentTerm dependentGoal := by
  apply inferNf_sound
  norm_num [inferNf, inferNfFuel, inferSpineFuel, dependentTerm, dependentGoal,
    fixtureFamily, fixtureHeadType, Nf.weight, Nf.listWeight, Nf.erase,
    ctxLookup, ctxLookupAux, Expr.lift, Expr.subst0, Expr.subst, Expr.atomic]

theorem identityTrace_accepted :
    rawRun identityGoal identityTrace (prepare 0 [] identityGoal []) =
      some (.finished identityTerm) :=
  rawRun_encode identityTerm_typed

theorem dependentTrace_accepted :
    rawRun dependentGoal dependentTrace (prepare 0 [] dependentGoal []) =
      some (.finished dependentTerm) :=
  rawRun_encode dependentTerm_typed

structure TraceFixture where
  name : String
  goal : Expr
  maxLen : Nat
  actions : List Action
  expectedAccepted : Bool
  negativeClass : Option String := none

def traceFixtures : List TraceFixture :=
  [ { name := "identity_positive"
      goal := identityGoal
      maxLen := identityTrace.length
      actions := identityTrace
      expectedAccepted := true }
  , { name := "dependent_substitution_positive"
      goal := dependentGoal
      maxLen := dependentTrace.length
      actions := dependentTrace
      expectedAccepted := true }
  , { name := "wrong_de_bruijn_index"
      goal := identityGoal
      maxLen := 8
      actions := [.selectHole 0, .selectBoundHead 99]
      expectedAccepted := false
      negativeClass := some "wrong_de_bruijn_index" }
  , { name := "wrong_spine_length"
      goal := dependentGoal
      maxLen := 12
      actions := [.selectHole 0, .selectBoundHead 0, .createDependentSpine 0]
      expectedAccepted := false
      negativeClass := some "wrong_spine_length" }
  , { name := "capture_scope_shift"
      goal := captureGoal
      maxLen := 8
      actions := [.selectHole 0, .selectBoundHead 0,
        .createDependentSpine 0, .finish]
      expectedAccepted := false
      negativeClass := some "capture" }
  , { name := "swapped_dependent_argument"
      goal := dependentGoal
      maxLen := 16
      actions := [.selectHole 0, .selectBoundHead 0, .createDependentSpine 1,
        .selectHole 0, .selectBoundHead 2, .createDependentSpine 1,
        .selectHole 0, .selectBoundHead 1, .createDependentSpine 0, .finish]
      expectedAccepted := false
      negativeClass := some "swapped_dependent_arguments" }
  , { name := "premature_finish"
      goal := identityGoal
      maxLen := 4
      actions := [.finish]
      expectedAccepted := false
      negativeClass := some "premature_finish" }
  ]

private def traceAccepted (fixture : TraceFixture) : Bool :=
  match (pureRoot fixture.goal).run fixture.actions
      ((pureRoot fixture.goal).initial fixture.maxLen) with
  | some finalState => finalState.core.isFinished
  | none => false

private def firstRejectedAt (goal : Expr) :
    List Action → State → Nat → Option Nat
  | [], _, _ => none
  | action :: rest, state, index =>
      match step? goal state action with
      | none => some index
      | some next => firstRejectedAt goal rest next (index + 1)

private def renderTraceFixture (fixture : TraceFixture) : String :=
  let initialState := (pureRoot fixture.goal).initial fixture.maxLen
  let decoded := (pureRoot fixture.goal).decode fixture.actions |>.isSome
  "{" ++
    "\"kind\":\"trace\"," ++
    "\"name\":" ++ jsonString fixture.name ++ "," ++
    "\"negative_class\":" ++ renderOptionString fixture.negativeClass ++ "," ++
    "\"goal_code\":" ++ renderNatArray fixture.goal.encode ++ "," ++
    "\"max_len\":" ++ toString fixture.maxLen ++ "," ++
    "\"actions\":" ++ jsonArray (fixture.actions.map renderAction) ++ "," ++
    "\"expected_accepted\":" ++ jsonBool fixture.expectedAccepted ++ "," ++
    "\"accepted\":" ++ jsonBool (traceAccepted fixture) ++ "," ++
    "\"decoded\":" ++ jsonBool decoded ++ "," ++
    "\"first_rejected_at\":" ++
      renderOptionNat (firstRejectedAt fixture.goal fixture.actions initialState 0) ++
  "}"

structure TransitionFixture where
  traceName : String
  goal : Expr
  stepIndex : Nat
  state : State
  action : Action
  next : State

private def collectTransitions (traceName : String) (goal : Expr) :
    List Action → State → Nat → List TransitionFixture
  | [], _, _ => []
  | action :: rest, state, index =>
      match step? goal state action with
      | none => []
      | some next =>
          { traceName := traceName, goal := goal, stepIndex := index,
            state := state, action := action, next := next } ::
          collectTransitions traceName goal rest next (index + 1)

def transitionFixtures : List TransitionFixture :=
  collectTransitions "identity_positive" identityGoal identityTrace
      ((pureRoot identityGoal).initial identityTrace.length) 0 ++
    collectTransitions "dependent_substitution_positive" dependentGoal dependentTrace
      ((pureRoot dependentGoal).initial dependentTrace.length) 0

private def renderTransitionFixture (fixture : TransitionFixture) : String :=
  "{" ++
    "\"kind\":\"transition\"," ++
    "\"trace_name\":" ++ jsonString fixture.traceName ++ "," ++
    "\"step\":" ++ toString fixture.stepIndex ++ "," ++
    "\"state\":" ++ renderState fixture.goal fixture.state ++ "," ++
    "\"action\":" ++ renderAction fixture.action ++ "," ++
    "\"next_state\":" ++ renderState fixture.goal fixture.next ++
  "}"

private def renderStatement (statement : Statement) : String :=
  let roundTrips := Expr.decode statement.goal.encode == some statement.goal
  "{" ++
    "\"kind\":\"statement\"," ++
    "\"group\":" ++ jsonString statement.group ++ "," ++
    "\"name\":" ++ jsonString statement.name ++ "," ++
    "\"source_path\":" ++ jsonString statement.sourcePath ++ "," ++
    "\"source_sha256\":" ++ jsonString statement.sourceSha256 ++ "," ++
    "\"canonical_path\":" ++ jsonString statement.canonicalPath ++ "," ++
    "\"canonical_sha256\":" ++ jsonString statement.canonicalSha256 ++ "," ++
    "\"normalized_type_sha256\":" ++ jsonString statement.normalizedTypeSha256 ++ "," ++
    "\"goal_code\":" ++ renderNatArray statement.goal.encode ++ "," ++
    "\"well_scoped\":" ++ jsonBool (statement.goal.wellScoped 0) ++ "," ++
    "\"roundtrip\":" ++ jsonBool roundTrips ++
  "}"

structure SourcePin where
  path : String
  sha256 : String

private def renderSourcePin (source : SourcePin) : String :=
  "{" ++
    "\"path\":" ++ jsonString source.path ++ "," ++
    "\"sha256\":" ++ jsonString source.sha256 ++
  "}"

private def metaFixture (sources : List SourcePin) : String :=
  "{" ++
    "\"kind\":\"meta\"," ++
    "\"schema\":\"gslt.pure.refinement.parity.v1\"," ++
    "\"generator_sha256\":" ++ jsonString generatorSha256 ++ "," ++
    "\"statement_rows\":" ++ toString statements.length ++ "," ++
    "\"transition_rows\":" ++ toString transitionFixtures.length ++ "," ++
    "\"trace_rows\":" ++ toString traceFixtures.length ++ "," ++
    "\"action_kinds\":[\"select_hole\",\"select_bound_head\"," ++
      "\"create_dependent_spine\",\"finish\"]," ++
    "\"lean_sources\":" ++ jsonArray (sources.map renderSourcePin) ++
  "}"

def renderFixtures (sources : List SourcePin) : String :=
  String.intercalate "\n"
    (metaFixture sources ::
      statements.map renderStatement ++
      transitionFixtures.map renderTransitionFixture ++
      traceFixtures.map renderTraceFixture) ++ "\n"

/-! ## Lean-side canaries for every named mutation class -/

example : dependentTrace.length = 7 := by decide

example : (traceFixtures.filter fun fixture => fixture.expectedAccepted).length = 2 := by
  decide

example : (traceFixtures.filter fun fixture => !fixture.expectedAccepted).length = 5 := by
  decide

private def isLowerHex (character : Char) : Bool :=
  ('0' ≤ character && character ≤ '9') ||
    ('a' ≤ character && character ≤ 'f')

private def validSha256 (digest : String) : Bool :=
  digest.length == 64 && digest.toList.all isLowerHex

private def sourcePins (hashes : List String) : List SourcePin :=
  (List.zip
    [ "Mettapedia/lean/mettapedia/Mettapedia/GSLT/LanguageDef/RefinementInterface.lean"
    , "Mettapedia/lean/mettapedia/Mettapedia/GSLT/LanguageDef/Pure/Statics.lean"
    , "Mettapedia/lean/mettapedia/Mettapedia/GSLT/LanguageDef/Pure/Refinement.lean"
    , "Mettapedia/lean/mettapedia/Mettapedia/GSLT/LanguageDef/Pure/Encoding.lean"
    , "Mettapedia/lean/mettapedia/Mettapedia/GSLT/LanguageDef/Pure/DTTBench31.lean"
    , "Mettapedia/lean/mettapedia/Mettapedia/GSLT/LanguageDef/Pure/Fixtures.lean"
    ] hashes).map fun (path, sha256) => { path := path, sha256 := sha256 }

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [interfaceSha, staticsSha, refinementSha, encodingSha, statementsSha,
      fixturesSha, mode, outputPath] =>
      let hashes :=
        [interfaceSha, staticsSha, refinementSha, encodingSha, statementsSha, fixturesSha]
      if !(hashes.all validSha256) then
        IO.eprintln "invalid source SHA-256 (expected six 64-digit lowercase hex values)"
        pure 1
      else
        let expected := renderFixtures (sourcePins hashes)
        match mode with
        | "write" =>
            IO.FS.writeFile outputPath expected
            IO.println s!"wrote {expected.toUTF8.size} bytes to {outputPath}"
            pure 0
        | "check" =>
            let actual ← IO.FS.readFile outputPath
            if actual == expected then
              IO.println s!"Pure refinement parity OK: {outputPath}"
              pure 0
            else
              IO.eprintln "Pure refinement parity artifact is stale"
              pure 1
        | _ =>
            IO.eprintln "mode must be write or check"
            pure 1
  | _ =>
      IO.eprintln (
        "usage: PureFixtures <interface-sha> <statics-sha> <refinement-sha> <encoding-sha> " ++
        "<statements-sha> <fixtures-sha> (write|check) <output.jsonl>")
      pure 1

end Mettapedia.GSLT.LanguageDef.PureFixtures

def main (arguments : List String) : IO UInt32 :=
  Mettapedia.GSLT.LanguageDef.PureFixtures.main arguments
