/-
# Atomic Pure refinement parity fixtures

Schema v2 persists only `Refine(hole, head)` actions.  Claimed spine lengths
and claimed terminality are audit attestations, not policy actions.  Every row
is translated from the v1 Lean fixtures and replayed by the atomic checker.
-/

import Mettapedia.GSLT.LanguageDef.Pure.AtomicRefinement
import Mettapedia.GSLT.LanguageDef.Pure.DTTBench31

namespace Mettapedia.GSLT.LanguageDef.PureAtomicFixtures

open Mettapedia.GSLT.LanguageDef.AtomicRefinement
open Mettapedia.GSLT.LanguageDef.Pure
open Mettapedia.GSLT.LanguageDef.PureAtomicRefinement
open Mettapedia.GSLT.LanguageDef.PureDTTBench31
open Mettapedia.GSLT.LanguageDef.PureRefinement

/-! ## Proven v1-to-v2 translation -/

/-- The frozen seven-row v1 input, copied without semantic reinterpretation. -/
structure V1TraceFixture where
  name : String
  goal : Expr
  maxLen : Nat
  actions : List Action
  expectedAccepted : Bool
  negativeClass : Option String := none

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

def dependentLegacyTrace : List Action :=
  PureRefinement.encode dependentTerm

def captureGoal : Expr :=
  pure_type% ((A : Type) → (x : A) → (B : Type) → A)

def v1TraceFixtures : List V1TraceFixture :=
  [ { name := "identity_positive"
      goal := PureRefinement.identityGoal
      maxLen := PureRefinement.identityTrace.length
      actions := PureRefinement.identityTrace
      expectedAccepted := true }
  , { name := "dependent_substitution_positive"
      goal := dependentGoal
      maxLen := dependentLegacyTrace.length
      actions := dependentLegacyTrace
      expectedAccepted := true }
  , { name := "wrong_de_bruijn_index"
      goal := PureRefinement.identityGoal
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
      goal := PureRefinement.identityGoal
      maxLen := 4
      actions := [.finish]
      expectedAccepted := false
      negativeClass := some "premature_finish" }
  ]

/-- Atomic actions plus separately checked elaborator-effect attestations. -/
structure Translation where
  actions : List AtomicAction
  claimedSpineLengths : List (Option Nat)
  claimedTerminal : Bool
  deriving DecidableEq, Repr

/--
Syntax-total translator for the seven frozen v1 fixtures.  A complete
hole/head/spine triple becomes one atomic action with an effect attestation;
the malformed two-event de Bruijn fixture becomes one action without an
effect attestation; finish becomes terminality claimed on the resulting state.
-/
def translateV1Syntax? : List Action → Option Translation
  | [] => some ⟨[], [], false⟩
  | [.finish] => some ⟨[], [], true⟩
  | .selectHole hole :: .selectBoundHead head ::
      .createDependentSpine arity :: rest => do
      let tail ← translateV1Syntax? rest
      pure
        ⟨⟨hole, head⟩ :: tail.actions,
          some arity :: tail.claimedSpineLengths,
          tail.claimedTerminal⟩
  | [.selectHole hole, .selectBoundHead head] =>
      some ⟨[⟨hole, head⟩], [none], false⟩
  | _ => none

theorem translateV1Syntax?_lengths {legacy : List Action} {translation : Translation}
    (htranslate : translateV1Syntax? legacy = some translation) :
    translation.claimedSpineLengths.length = translation.actions.length := by
  induction legacy using translateV1Syntax?.induct generalizing translation with
  | case1 => simp [translateV1Syntax?] at htranslate; subst translation; rfl
  | case2 => simp [translateV1Syntax?] at htranslate; subst translation; rfl
  | case3 hole head arity rest ih =>
      simp only [translateV1Syntax?] at htranslate
      cases htail : translateV1Syntax? rest with
      | none => simp [htail] at htranslate
      | some tail =>
          simp [htail] at htranslate
          subst translation
          simp [ih htail]
  | case4 hole head =>
      simp [translateV1Syntax?] at htranslate
      subst translation
      rfl
  | case5 legacy hshape => simp [translateV1Syntax?] at htranslate

/-- The strict translator is the proved accepted-trace compression from T1. -/
def translateAccepted? (goal : Expr) (legacy : List Action) :
    Option (List AtomicAction) :=
  compressAccepted? goal legacy

theorem translateAccepted_roundTrip {goal : Expr} {legacy : List Action}
    {atomic : List AtomicAction}
    (htranslate : translateAccepted? goal legacy = some atomic) :
    expandAccepted? goal atomic = some legacy :=
  expandAccepted?_compressAccepted htranslate

/-! ## Executable claim replay -/

def computedSpineLength? (core : Core) (action : AtomicAction) : Option Nat := do
  let forced ← forcedLegacyActions? core action
  match forced with
  | [.selectHole _, .selectBoundHead _, .createDependentSpine arity] => some arity
  | _ => none

structure ReplayResult where
  state : State
  completed : Bool
  firstRejectedAt : Option Nat
  deriving Repr

def replayFrom (goal : Expr) :
    List AtomicAction → List (Option Nat) → State → Nat → ReplayResult
  | [], [], state, _ => ⟨state, true, none⟩
  | action :: rest, claim :: claims, state, index =>
      let claimMatches :=
        match claim with
        | none => true
        | some claimed => computedSpineLength? state.core action == some claimed
      if !claimMatches then
        ⟨state, false, some index⟩
      else
        match PureAtomicRefinement.step? goal state action with
        | none => ⟨state, false, some index⟩
        | some next => replayFrom goal rest claims next (index + 1)
  | _, _, state, index => ⟨state, false, some index⟩

def atomicBudget (legacyMaxLen : Nat) (translation : Translation) : Nat :=
  max translation.actions.length ((legacyMaxLen - 1) / 3)

def replay (goal : Expr) (maxRefinements : Nat) (translation : Translation) :
    ReplayResult :=
  replayFrom goal translation.actions translation.claimedSpineLengths
    (atomicInitial goal maxRefinements) 0

def accepted (goal : Expr) (maxRefinements : Nat) (translation : Translation) : Bool :=
  let result := replay goal maxRefinements translation
  result.completed && translation.claimedTerminal &&
    decide (coreTerminal goal result.state.core)

def firstRejectedAt (goal : Expr) (maxRefinements : Nat)
    (translation : Translation) : Option Nat :=
  let result := replay goal maxRefinements translation
  match result.firstRejectedAt with
  | some index => some index
  | none =>
      if result.completed && translation.claimedTerminal &&
          decide (coreTerminal goal result.state.core) then
        none
      else
        some translation.actions.length

structure AtomicTraceFixture where
  name : String
  goal : Expr
  maxRefinements : Nat
  translation : Translation
  expectedAccepted : Bool
  negativeClass : Option String
  deriving Repr

def translateFixture? (fixture : V1TraceFixture) : Option AtomicTraceFixture := do
  let translation ← translateV1Syntax? fixture.actions
  pure
    { name := fixture.name
      goal := fixture.goal
      maxRefinements := atomicBudget fixture.maxLen translation
      translation := translation
      expectedAccepted := fixture.expectedAccepted
      negativeClass := fixture.negativeClass }

def atomicTraceFixtures : List AtomicTraceFixture :=
  v1TraceFixtures.filterMap translateFixture?

theorem all_v1_fixtures_translate : atomicTraceFixtures.length = 7 := by
  decide

def translatedFixtureExpectationsHold : Bool :=
  atomicTraceFixtures.all fun fixture =>
    accepted fixture.goal fixture.maxRefinements fixture.translation ==
      fixture.expectedAccepted

theorem translated_negative_classes_survive :
    (atomicTraceFixtures.filter fun fixture => !fixture.expectedAccepted).length = 5 := by
  decide

/-! ## Atomic transition fixtures -/

structure TransitionFixture where
  traceName : String
  goal : Expr
  maxRefinements : Nat
  stepIndex : Nat
  state : State
  action : AtomicAction
  claimedSpineLength : Option Nat
  next : State
  deriving Repr

def collectTransitions (traceName : String) (goal : Expr) (maxRefinements : Nat) :
    List AtomicAction → List (Option Nat) → State → Nat → List TransitionFixture
  | action :: rest, claim :: claims, state, index =>
      if claim.isSome &&
          computedSpineLength? state.core action != claim then
        []
      else
        match PureAtomicRefinement.step? goal state action with
        | none => []
        | some next =>
            { traceName := traceName
              goal := goal
              maxRefinements := maxRefinements
              stepIndex := index
              state := state
              action := action
              claimedSpineLength := claim
              next := next } ::
            collectTransitions traceName goal maxRefinements rest claims next (index + 1)
  | _, _, _, _ => []

def transitionFixtures : List TransitionFixture :=
  atomicTraceFixtures.filter (fun fixture => fixture.expectedAccepted) |>.flatMap
    fun fixture =>
      collectTransitions fixture.name fixture.goal fixture.maxRefinements
        fixture.translation.actions fixture.translation.claimedSpineLengths
        (atomicInitial fixture.goal fixture.maxRefinements) 0

def atomicTransitionCountOK : Bool := transitionFixtures.length == 3

/-! ## Deterministic JSONL rendering -/

private def jsonEscapeChar : Char → String
  | '"' => "\\\""
  | '\\' => "\\\\"
  | '\n' => "\\n"
  | '\r' => "\\r"
  | '\t' => "\\t"
  | c => c.toString

private def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonEscapeChar) ++ "\""

private def jsonBool (value : Bool) : String := if value then "true" else "false"

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

private def renderAction (action : AtomicAction) : String :=
  "{" ++
    "\"kind\":\"refine\"," ++
    "\"hole\":" ++ toString action.hole ++ "," ++
    "\"head\":" ++ toString action.head ++
  "}"

private def renderEffectClaim (step : Nat) (claim : Option Nat) : Option String :=
  claim.map fun arity =>
    "{" ++
      "\"step\":" ++ toString step ++ "," ++
      "\"claimed_spine_length\":" ++ toString arity ++
    "}"

private def renderEffectClaims : Nat → List (Option Nat) → List String
  | _, [] => []
  | index, claim :: rest =>
      match renderEffectClaim index claim with
      | none => renderEffectClaims (index + 1) rest
      | some rendered => rendered :: renderEffectClaims (index + 1) rest

private def phaseName : Core → String
  | .needHole .. => "need_hole"
  | .needHead .. => "internal_need_head"
  | .needSpine .. => "internal_need_spine"
  | .done .. => "done"
  | .finished .. => "legacy_finished"

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

private def renderState (goal : Expr) (maxRefinements : Nat) (state : State) : String :=
  let targetCode := match coreTarget? state.core with
    | none => "null"
    | some target => renderNatArray target.encode
  let root := pureAtomicRoot goal
  "{" ++
    "\"phase\":" ++ jsonString (phaseName state.core) ++ "," ++
    "\"refinements_emitted\":" ++ toString (state.tokensEmitted / 3) ++ "," ++
    "\"max_refinements\":" ++ toString maxRefinements ++ "," ++
    "\"open_holes\":" ++ renderNatArray (root.holes state) ++ "," ++
    "\"context_length\":" ++ toString (coreContextLength state.core) ++ "," ++
    "\"target_code\":" ++ targetCode ++ "," ++
    "\"legal_actions\":" ++
      jsonArray ((root.legalActions state).map renderAction) ++
  "}"

private def renderTransition (fixture : TransitionFixture) : String :=
  "{" ++
    "\"kind\":\"transition\"," ++
    "\"trace_name\":" ++ jsonString fixture.traceName ++ "," ++
    "\"step\":" ++ toString fixture.stepIndex ++ "," ++
    "\"state\":" ++ renderState fixture.goal fixture.maxRefinements fixture.state ++ "," ++
    "\"action\":" ++ renderAction fixture.action ++ "," ++
    "\"claimed_effect\":{" ++
      "\"spine_length\":" ++ renderOptionNat fixture.claimedSpineLength ++ "}," ++
    "\"next_state\":" ++ renderState fixture.goal fixture.maxRefinements fixture.next ++
  "}"

private def renderTrace (fixture : AtomicTraceFixture) : String :=
  let effectClaims := renderEffectClaims 0 fixture.translation.claimedSpineLengths
  let isAccepted := accepted fixture.goal fixture.maxRefinements fixture.translation
  "{" ++
    "\"kind\":\"trace\"," ++
    "\"name\":" ++ jsonString fixture.name ++ "," ++
    "\"negative_class\":" ++ renderOptionString fixture.negativeClass ++ "," ++
    "\"goal_code\":" ++ renderNatArray fixture.goal.encode ++ "," ++
    "\"max_refinements\":" ++ toString fixture.maxRefinements ++ "," ++
    "\"actions\":" ++ jsonArray (fixture.translation.actions.map renderAction) ++ "," ++
    "\"effect_claims\":" ++ jsonArray effectClaims ++ "," ++
    "\"claimed_terminal\":" ++ jsonBool fixture.translation.claimedTerminal ++ "," ++
    "\"expected_accepted\":" ++ jsonBool fixture.expectedAccepted ++ "," ++
    "\"accepted\":" ++ jsonBool isAccepted ++ "," ++
    "\"decoded\":" ++ jsonBool
      (isAccepted && (PureAtomicRefinement.decode fixture.goal
        fixture.translation.actions).isSome) ++ "," ++
    "\"first_rejected_at\":" ++
      renderOptionNat (firstRejectedAt fixture.goal fixture.maxRefinements
        fixture.translation) ++
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

private def metaFixture (sources : List SourcePin) (fixtureGeneratorSha : String) : String :=
  "{" ++
    "\"kind\":\"meta\"," ++
    "\"schema\":\"gslt.pure.atomic_refinement.parity.v2\"," ++
    "\"schema_version\":2," ++
    "\"supersedes\":\"gslt.pure.refinement.parity.v1\"," ++
    "\"generator_sha256\":" ++ jsonString generatorSha256 ++ "," ++
    "\"fixture_generator_sha256\":" ++ jsonString fixtureGeneratorSha ++ "," ++
    "\"statement_rows\":" ++ toString statements.length ++ "," ++
    "\"transition_rows\":" ++ toString transitionFixtures.length ++ "," ++
    "\"trace_rows\":" ++ toString atomicTraceFixtures.length ++ "," ++
    "\"action_kinds\":[\"refine\"]," ++
    "\"action_fields\":[\"hole\",\"head\"]," ++
    "\"attestation_fields\":[\"claimed_spine_length\",\"claimed_terminal\"]," ++
    "\"lean_sources\":" ++ jsonArray (sources.map renderSourcePin) ++
  "}"

def renderFixtures (sources : List SourcePin) (fixtureGeneratorSha : String) : String :=
  String.intercalate "\n"
    (metaFixture sources fixtureGeneratorSha ::
      statements.map renderStatement ++
      transitionFixtures.map renderTransition ++
      atomicTraceFixtures.map renderTrace) ++ "\n"

private def isLowerHex (character : Char) : Bool :=
  ('0' ≤ character && character ≤ '9') ||
    ('a' ≤ character && character ≤ 'f')

private def validSha256 (digest : String) : Bool :=
  digest.length == 64 && digest.toList.all isLowerHex

private def sourcePaths : List String :=
  [ "Mettapedia/GSLT/LanguageDef/RefinementInterface.lean"
  , "Mettapedia/GSLT/LanguageDef/AtomicRefinement.lean"
  , "Mettapedia/GSLT/LanguageDef/Pure/Statics.lean"
  , "Mettapedia/GSLT/LanguageDef/Pure/Refinement.lean"
  , "Mettapedia/GSLT/LanguageDef/Pure/AtomicRefinement.lean"
  , "Mettapedia/GSLT/LanguageDef/Pure/Encoding.lean"
  , "Mettapedia/GSLT/LanguageDef/Pure/DTTBench31.lean"
  , "Mettapedia/GSLT/LanguageDef/Pure/Fixtures.lean"
  , "Mettapedia/GSLT/LanguageDef/Pure/AtomicFixtures.lean"
  , "Mettapedia/GSLT/LanguageDef/Pure/AtomicFixturesMain.lean"
  ]

private def sourcePins (hashes : List String) : List SourcePin :=
  (List.zip sourcePaths hashes).map fun (path, sha256) => ⟨path, sha256⟩

def main (arguments : List String) : IO UInt32 := do
  if arguments.length != sourcePaths.length + 2 then
    IO.eprintln "usage: PureAtomicFixtures <ten source sha256s> (write|check) <output.jsonl>"
    return 1
  let hashes := arguments.take sourcePaths.length
  let mode := arguments[sourcePaths.length]!
  let outputPath := arguments[sourcePaths.length + 1]!
  if !(hashes.all validSha256) then
    IO.eprintln "invalid source SHA-256"
    return 1
  if !translatedFixtureExpectationsHold then
    IO.eprintln "translated v1 trace expectations failed under the atomic checker"
    return 2
  if !atomicTransitionCountOK then
    IO.eprintln "unexpected atomic transition count"
    return 3
  let fixtureGeneratorSha := hashes.getLast!
  let expected := renderFixtures (sourcePins hashes) fixtureGeneratorSha
  match mode with
  | "write" =>
      IO.FS.writeFile outputPath expected
      IO.println s!"wrote {expected.toUTF8.size} bytes to {outputPath}"
      pure 0
  | "check" =>
      let actual ← IO.FS.readFile outputPath
      if actual == expected then
        IO.println s!"Pure atomic refinement parity OK: {outputPath}"
        pure 0
      else
        IO.eprintln "Pure atomic refinement parity artifact is stale"
        pure 1
  | _ =>
      IO.eprintln "mode must be write or check"
      pure 1

#print axioms translateV1Syntax?_lengths
#print axioms translateAccepted_roundTrip
#print axioms all_v1_fixtures_translate
#print axioms translated_negative_classes_survive

end Mettapedia.GSLT.LanguageDef.PureAtomicFixtures
