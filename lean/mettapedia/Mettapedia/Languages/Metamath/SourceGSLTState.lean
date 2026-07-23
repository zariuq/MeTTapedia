import Mettapedia.Languages.Metamath.SourceGSLTOperations
import Mettapedia.Languages.Metamath.SourceInferenceProjection

/-!
# Source-owned scoped state for Metamath GSLT operations

The source grammar determines which proof-relevant operation occurs.  This
module gives the local environment operations their source-owned state
semantics.  It does not use the `mm-lean4` runtime database.

The state keeps global object identities separately from the active frame.
Closing a scope therefore removes active hypotheses and disjointness
conditions without making their labels reusable.  Assertion frames are
trimmed from the active source frame according to the Metamath mandatory
hypothesis law.

Proof checking and include resolution are deliberately separate indexed
stages.  They consume the same `SourceOperation` identities, but are not
mistaken for local declaration updates.
-/

namespace Mettapedia.Languages.Metamath.SourceGSLTState

open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceSideConditions
open Mettapedia.Languages.Metamath.SourceGSLTOperations
open Mettapedia.Languages.Metamath.SourceInferenceProjection

deriving instance DecidableEq for HypothesisView
deriving instance DecidableEq for SourceAssertion

/-! ## Scoped source carrier -/

/-- A block boundary remembers the active-frame prefix lengths.  Global
declarations, used labels, and assertions are intentionally not rolled back. -/
structure ScopeBoundary where
  activeHypothesisLength : Nat
  activeDistinctLength : Nat
deriving DecidableEq, Repr

/-- Source-owned database state before projection to an indexed checker. -/
structure SourceState where
  declaredConstants : List String
  declaredVariables : List String
  usedLabels : List String
  activeHypotheses : List HypothesisView
  activeDistinctVariables : List (String × String)
  assertions : List SourceAssertion
  scopes : List ScopeBoundary
  pendingBlockCompletions : Nat
deriving DecidableEq

def initialState : SourceState :=
  { declaredConstants := []
    declaredVariables := []
    usedLabels := []
    activeHypotheses := []
    activeDistinctVariables := []
    assertions := []
    scopes := []
    pendingBlockCompletions := 0 }

def SourceState.activeFloatingVariables (state : SourceState) : List String :=
  floatingVariableNames state.activeHypotheses

/-- Disjointness conditions without two active floating hypotheses cannot
affect proof execution.  They remain in source state, but are absent from the
proof-facing caller frame until both endpoints are active. -/
def SourceState.proofDistinctVariables
    (state : SourceState) : List (String × String) :=
  state.activeDistinctVariables.filter fun pair =>
    state.activeFloatingVariables.contains pair.1 &&
      state.activeFloatingVariables.contains pair.2

def SourceState.callerFrame (state : SourceState) : SourceFrame :=
  { distinctVariables := state.proofDistinctVariables
    hypothesisLabels := state.activeHypotheses.map HypothesisView.label }

/-- Projection used by the already verified indexed proof calculus. -/
def SourceState.toSourcePrefix (state : SourceState) : SourcePrefix :=
  { declaredConstants := state.declaredConstants
    declaredVariables := state.declaredVariables
    callerFrame := state.callerFrame
    activeHypotheses := state.activeHypotheses
    assertions := state.assertions }

private def validRuleLabel (label : String) : Bool :=
  label != "" && !(label.startsWith reservedRulePrefix)

private def boundaryValid (state : SourceState)
    (boundary : ScopeBoundary) : Bool :=
  boundary.activeHypothesisLength ≤ state.activeHypotheses.length &&
    boundary.activeDistinctLength ≤ state.activeDistinctVariables.length

/-- Complete local state invariant.  In particular, the object namespace is
global even when hypotheses leave the active frame. -/
def sourceStateValid (state : SourceState) : Bool :=
  let objectNames :=
    state.declaredConstants ++ state.declaredVariables ++ state.usedLabels
  sourcePrefixValid state.toSourcePrefix &&
    state.usedLabels.all validRuleLabel &&
    state.usedLabels.eraseDups.length == state.usedLabels.length &&
    (state.activeHypotheses.map HypothesisView.label).all
      state.usedLabels.contains &&
    (state.assertions.map SourceAssertion.label).all
      state.usedLabels.contains &&
    objectNames.eraseDups.length == objectNames.length &&
    (state.activeDistinctVariables.all fun pair =>
      decide (pair.1 < pair.2) &&
        state.declaredVariables.contains pair.1 &&
        state.declaredVariables.contains pair.2) &&
    state.scopes.all (boundaryValid state)

def sourceStateComplete (state : SourceState) : Bool :=
  sourceStateValid state &&
    state.scopes.isEmpty &&
    state.pendingBlockCompletions == 0

theorem sourcePrefixValid_of_sourceStateValid
    (state : SourceState) (valid : sourceStateValid state = true) :
    sourcePrefixValid state.toSourcePrefix = true := by
  simp only [sourceStateValid, Bool.and_eq_true] at valid
  aesop

private def acceptUpdate (before after : SourceState) :
    Option SourceState := do
  guard (sourceStateValid before)
  guard (sourceStateValid after)
  pure after

private def readyForLocalUpdate (state : SourceState) : Bool :=
  state.pendingBlockCompletions == 0

/-! ## Mandatory-frame construction -/

private def variablesInFormula
    (formula : ConstantHeadedFormula) : List String :=
  taggedVariableNames formula.body

private def variablesInEssentialHypotheses :
    List HypothesisView → List String
  | [] => []
  | .floating _ _ _ :: hypotheses =>
      variablesInEssentialHypotheses hypotheses
  | .essential _ formula :: hypotheses =>
      variablesInFormula formula ++
        variablesInEssentialHypotheses hypotheses

def mandatoryVariableNames (state : SourceState)
    (formula : ConstantHeadedFormula) : List String :=
  (variablesInFormula formula ++
      variablesInEssentialHypotheses state.activeHypotheses).eraseDups

private def mandatoryHypothesis
    (variableNames : List String) : HypothesisView → Bool
  | .floating _ _ variableName => variableNames.contains variableName
  | .essential _ _ => true

def mandatoryHypotheses (state : SourceState)
    (formula : ConstantHeadedFormula) : List HypothesisView :=
  let variableNames := mandatoryVariableNames state formula
  state.activeHypotheses.filter (mandatoryHypothesis variableNames)

def mandatoryFrame (state : SourceState)
    (formula : ConstantHeadedFormula) : SourceFrame :=
  let variableNames := mandatoryVariableNames state formula
  let hypotheses := mandatoryHypotheses state formula
  { distinctVariables :=
      state.activeDistinctVariables.filter fun pair =>
        variableNames.contains pair.1 && variableNames.contains pair.2
    hypothesisLabels := hypotheses.map HypothesisView.label }

def sourceAssertion (state : SourceState) (label : String)
    (formula : ConstantHeadedFormula) : SourceAssertion :=
  { label
    formula
    frame := mandatoryFrame state formula
    hypotheses := mandatoryHypotheses state formula }

/-! ## Executable local effects -/

def openScope? (state : SourceState) : Option SourceState := do
  guard (readyForLocalUpdate state)
  acceptUpdate state
    { state with
      scopes :=
        { activeHypothesisLength := state.activeHypotheses.length
          activeDistinctLength := state.activeDistinctVariables.length } ::
          state.scopes }

def closeScope? (state : SourceState) : Option SourceState := do
  guard (readyForLocalUpdate state)
  let boundary ← state.scopes.head?
  acceptUpdate state
    { state with
      activeHypotheses :=
        state.activeHypotheses.take boundary.activeHypothesisLength
      activeDistinctVariables :=
        state.activeDistinctVariables.take boundary.activeDistinctLength
      scopes := state.scopes.tail
      pendingBlockCompletions := state.pendingBlockCompletions + 1 }

def completeBlock? (state : SourceState) : Option SourceState := do
  guard (sourceStateValid state)
  guard (state.pendingBlockCompletions > 0)
  let after :=
    { state with
      pendingBlockCompletions := state.pendingBlockCompletions - 1 }
  guard (sourceStateValid after)
  pure after

def declareConstants? (state : SourceState)
    (names : List String) : Option SourceState := do
  guard (readyForLocalUpdate state)
  guard (!names.isEmpty)
  guard state.scopes.isEmpty
  acceptUpdate state
    { state with
      declaredConstants := state.declaredConstants ++ names }

private def addVariable (variableNames : List String)
    (name : String) : List String :=
  if variableNames.contains name then
    variableNames
  else
    variableNames ++ [name]

def declareVariables? (state : SourceState)
    (names : List String) : Option SourceState := do
  guard (readyForLocalUpdate state)
  guard (!names.isEmpty)
  acceptUpdate state
    { state with
      declaredVariables := names.foldl addVariable state.declaredVariables }

private def canonicalPair (left right : String) : String × String :=
  if left < right then (left, right) else (right, left)

private def pairsWith (left : String) : List String → List (String × String)
  | [] => []
  | right :: rest => canonicalPair left right :: pairsWith left rest

def allDistinctPairs : List String → List (String × String)
  | [] => []
  | first :: rest => pairsWith first rest ++ allDistinctPairs rest

def declareDisjoint? (state : SourceState)
    (names : List String) : Option SourceState := do
  guard (readyForLocalUpdate state)
  guard (2 ≤ names.length)
  guard (names.eraseDups.length == names.length)
  guard (names.all state.declaredVariables.contains)
  acceptUpdate state
    { state with
      activeDistinctVariables :=
        state.activeDistinctVariables ++ allDistinctPairs names }

def declareFloating? (state : SourceState)
    (label typecode variableName : String) : Option SourceState := do
  guard (readyForLocalUpdate state)
  let hypothesis := HypothesisView.floating label typecode variableName
  acceptUpdate state
    { state with
      usedLabels := state.usedLabels ++ [label]
      activeHypotheses := state.activeHypotheses ++ [hypothesis] }

def declareEssential? (state : SourceState)
    (label : String) (formula : ConstantHeadedFormula) :
    Option SourceState := do
  guard (readyForLocalUpdate state)
  let hypothesis := HypothesisView.essential label formula
  acceptUpdate state
    { state with
      usedLabels := state.usedLabels ++ [label]
      activeHypotheses := state.activeHypotheses ++ [hypothesis] }

def insertAssertion? (state : SourceState)
    (label : String) (formula : ConstantHeadedFormula) :
    Option SourceState := do
  guard (readyForLocalUpdate state)
  let assertion := sourceAssertion state label formula
  acceptUpdate state
    { state with
      usedLabels := state.usedLabels ++ [label]
      assertions := state.assertions ++ [assertion] }

def declareAxiom? (state : SourceState)
    (label : String) (formula : ConstantHeadedFormula) :
    Option SourceState :=
  insertAssertion? state label formula

theorem insertAssertion?_eq_some_shape
    {state after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (inserted : insertAssertion? state label formula = some after) :
    after.assertions =
        state.assertions ++ [sourceAssertion state label formula] ∧
      after.usedLabels = state.usedLabels ++ [label] := by
  simp [insertAssertion?, acceptUpdate] at inserted
  rcases inserted with ⟨_, _, _, rfl⟩
  exact ⟨rfl, rfl⟩

/-! ## Exact operation-indexed local relation -/

/-- Typed payloads for the nine local environment operations.  Proof
verification and source resolution have distinct relations because they carry
proof and nested-source evidence, respectively. -/
inductive LocalPayload where
  | openScope
  | closeScope
  | declareConstants (names : List String)
  | declareVariables (names : List String)
  | declareDisjoint (names : List String)
  | declareFloating (label typecode variableName : String)
  | declareEssential (label : String) (formula : ConstantHeadedFormula)
  | declareAxiom (label : String) (formula : ConstantHeadedFormula)
  | completeBlock

def LocalPayload.operation : LocalPayload → SourceOperation
  | .openScope => .openScope
  | .closeScope => .closeScope
  | .declareConstants _ => .declareConstants
  | .declareVariables _ => .declareVariables
  | .declareDisjoint _ => .declareDisjoint
  | .declareFloating _ _ _ => .declareFloating
  | .declareEssential _ _ => .declareEssential
  | .declareAxiom _ _ => .declareAxiom
  | .completeBlock => .completeBlock

def applyLocalPayload? (payload : LocalPayload)
    (state : SourceState) : Option SourceState :=
  match payload with
  | .openScope => openScope? state
  | .closeScope => closeScope? state
  | .declareConstants names => declareConstants? state names
  | .declareVariables names => declareVariables? state names
  | .declareDisjoint names => declareDisjoint? state names
  | .declareFloating label typecode variableName =>
      declareFloating? state label typecode variableName
  | .declareEssential label formula =>
      declareEssential? state label formula
  | .declareAxiom label formula =>
      declareAxiom? state label formula
  | .completeBlock => completeBlock? state

/-- A local transition is indexed by the exact operation identity selected by
the source grammar occurrence. -/
structure LocalStep (operation : SourceOperation)
    (before after : SourceState) : Type where
  payload : LocalPayload
  operation_eq : payload.operation = operation
  applied : applyLocalPayload? payload before = some after

def localOperations : List SourceOperation :=
  [.openScope, .closeScope, .declareConstants, .declareVariables,
   .declareDisjoint, .declareFloating, .declareEssential, .declareAxiom,
   .completeBlock]

theorem localOperation_count : localOperations.length = 9 := by
  decide

/-- The local layer cannot accidentally absorb theorem checking or include
resolution. -/
theorem nonlocalOperations_absent :
    SourceOperation.checkTheoremNormal ∉ localOperations ∧
      SourceOperation.checkTheoremCompressed ∉ localOperations ∧
      SourceOperation.resolveInclude ∉ localOperations := by
  simp [localOperations]

/-! ## Positive and negative executable witnesses -/

private def declarationsState : SourceState :=
  { initialState with
    declaredConstants := ["wff"]
    declaredVariables := ["x", "y"] }

/-- Appendix E permits a disjoint declaration before the corresponding
floating hypotheses.  The source state retains it while the proof-facing
frame omits it until both floats are active. -/
theorem disjointBeforeFloating_admitted :
    ∃ state,
      declareDisjoint? declarationsState ["x", "y"] = some state ∧
        state.activeDistinctVariables = [("x", "y")] ∧
        state.proofDistinctVariables = [] := by
  refine ⟨{ declarationsState with
      activeDistinctVariables := [("x", "y")] }, ?_⟩
  decide

/-- Closing and completing a block restores the active frame but preserves a
label in the global object namespace. -/
theorem scopedLabel_notReusable :
    let floated :=
      { declarationsState with
        usedLabels := ["wx"]
        activeHypotheses := [.floating "wx" "wff" "x"] }
    ∃ opened closed completed,
      openScope? floated = some opened ∧
      closeScope? opened = some closed ∧
      completeBlock? closed = some completed ∧
      completed.activeHypotheses = floated.activeHypotheses ∧
      declareFloating? completed "wx" "wff" "y" = none := by
  dsimp
  refine ⟨
    { declarationsState with
      usedLabels := ["wx"]
      activeHypotheses := [.floating "wx" "wff" "x"]
      scopes := [{ activeHypothesisLength := 1
                   activeDistinctLength := 0 }] },
    { declarationsState with
      usedLabels := ["wx"]
      activeHypotheses := [.floating "wx" "wff" "x"]
      pendingBlockCompletions := 1 },
    { declarationsState with
      usedLabels := ["wx"]
      activeHypotheses := [.floating "wx" "wff" "x"] },
    ?_⟩
  decide

/-- A source occurrence cannot be reinterpreted under a different local
operation identity. -/
theorem localStep_operation_exact
    {operation : SourceOperation} {before after : SourceState}
    (step : LocalStep operation before after) :
    step.payload.operation = operation :=
  step.operation_eq

end Mettapedia.Languages.Metamath.SourceGSLTState
