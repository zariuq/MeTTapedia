import Mettapedia.Languages.Metamath.SourceGSLTOperations
import Mettapedia.Languages.Metamath.SourceInferenceProjection
import Mettapedia.Languages.Metamath.InferenceProjectionInvariants

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

## Declared reading: hoisted declarations ([MM §4.2.10] Frames Revisited)

The gates implement the book's hoisted-database image — "we collect all
constant and variable (`$c` and `$v`) declarations in the database,
ignoring duplicate declarations of the same variable in different
scopes" — exactly as `mm-lean4` does, not the raw [MM §4.2.8] scoping of
declarations themselves:

* variables are never deactivated by `closeScope?`, and redeclaring an
  already-declared variable is a silent no-op (`addVariable`), where raw
  [MM §4.1.3]/[MM §4.2.8] would reject an active redeclaration;
* the [MM §4.1.3] rule that the typecode a `$f` assigns to a variable is
  global across scopes is not enforced here — nor by `mm-lean4`, whose
  float-uniqueness check also inspects only the active frame;
* token-charset legality ([MM §4.1.1]) is owned by the parser lane; the
  gates accept any globally fresh string, and `validRuleLabel` checks
  only nonemptiness and the (book-unreachable, `$`-headed) reserved
  rule-namespace prefix.

Label retention across scope exit is the book's own rule (the global
label-uniqueness sentence of [MM §4.1.3]); the hyps/`$d` rollback with
retained global names matches `mm-lean4`'s single global object map with
frame truncation.
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

/-- Every globally occupied source name.  Unlike `toSourcePrefix`, this keeps
labels of hypotheses that have left the active frame, because Metamath never
makes such labels reusable after a scope closes. -/
def SourceState.objectNames (state : SourceState) : List String :=
  state.declaredConstants ++ state.declaredVariables ++ state.usedLabels

private def validRuleLabel (label : String) : Bool :=
  label != "" && !(label.startsWith reservedRulePrefix)

private def boundaryValid (state : SourceState)
    (boundary : ScopeBoundary) : Bool :=
  boundary.activeHypothesisLength ≤ state.activeHypotheses.length &&
    boundary.activeDistinctLength ≤ state.activeDistinctVariables.length

/-- Complete local state invariant.  In particular, the object namespace is
global even when hypotheses leave the active frame. -/
def sourceStateValid (state : SourceState) : Bool :=
  sourcePrefixValid state.toSourcePrefix &&
    state.usedLabels.all validRuleLabel &&
    state.usedLabels.eraseDups.length == state.usedLabels.length &&
    (state.activeHypotheses.map HypothesisView.label).all
      state.usedLabels.contains &&
    (state.assertions.map SourceAssertion.label).all
      state.usedLabels.contains &&
    state.objectNames.eraseDups.length == state.objectNames.length &&
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

/-- The executable global-namespace check exposes ordinary list uniqueness. -/
theorem objectNames_nodup_of_sourceStateValid
    (state : SourceState) (valid : sourceStateValid state = true) :
    state.objectNames.Nodup := by
  apply nodup_of_eraseDups_length_eq
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

/-! ## [MM §4.2.7] Mandatory projection ignores optional support

An extended proof-site frame may contain fresh floating hypotheses and
disjoint-variable conditions for dummy variables.  Stored assertions expose
only their mandatory projection.  The following lemmas state that boundary on
the source-owned carrier itself, before any translation to `mm-lean4`.
-/

private theorem variablesInEssentialHypotheses_append_floating
    (hypotheses : List HypothesisView) (label typecode variableName : String) :
    variablesInEssentialHypotheses
        (hypotheses ++ [.floating label typecode variableName]) =
      variablesInEssentialHypotheses hypotheses := by
  induction hypotheses with
  | nil => rfl
  | cons hypothesis hypotheses ih =>
      cases hypothesis <;>
        simp [variablesInEssentialHypotheses, ih]

/-- Appending a floating hypothesis never changes which variable names occur
in the assertion formula or its active essential hypotheses. -/
theorem mandatoryVariableNames_append_floating
    (state : SourceState) (formula : ConstantHeadedFormula)
    (label typecode variableName : String) :
    mandatoryVariableNames
        { state with
          activeHypotheses :=
            state.activeHypotheses ++
              [.floating label typecode variableName] }
        formula =
      mandatoryVariableNames state formula := by
  simp only [mandatoryVariableNames]
  rw [variablesInEssentialHypotheses_append_floating]

/-- A genuinely optional floating hypothesis is absent from the mandatory
hypothesis projection. -/
theorem mandatoryHypotheses_append_optional_floating
    (state : SourceState) (formula : ConstantHeadedFormula)
    (label typecode variableName : String)
    (hoptional : variableName ∉ mandatoryVariableNames state formula) :
    mandatoryHypotheses
        { state with
          activeHypotheses :=
            state.activeHypotheses ++
              [.floating label typecode variableName] }
        formula =
      mandatoryHypotheses state formula := by
  unfold mandatoryHypotheses
  rw [mandatoryVariableNames_append_floating]
  simp [mandatoryHypothesis, hoptional]

/-- Negative calibration of the selector: if the variable is mandatory, the
same appended floating hypothesis is retained.  Operational source validity
normally prevents appending a second active `$f` for such a variable; this
lemma pins the projection branch independently of that admission check. -/
theorem mandatoryHypotheses_append_mandatory_floating
    (state : SourceState) (formula : ConstantHeadedFormula)
    (label typecode variableName : String)
    (hmandatory : variableName ∈ mandatoryVariableNames state formula) :
    mandatoryHypotheses
        { state with
          activeHypotheses :=
            state.activeHypotheses ++
              [.floating label typecode variableName] }
        formula =
      mandatoryHypotheses state formula ++
        [.floating label typecode variableName] := by
  unfold mandatoryHypotheses
  rw [mandatoryVariableNames_append_floating]
  simp [mandatoryHypothesis, hmandatory]

/-- An optional floating hypothesis does not change the stored mandatory
frame. -/
theorem mandatoryFrame_append_optional_floating
    (state : SourceState) (formula : ConstantHeadedFormula)
    (label typecode variableName : String)
    (hoptional : variableName ∉ mandatoryVariableNames state formula) :
    mandatoryFrame
        { state with
          activeHypotheses :=
            state.activeHypotheses ++
              [.floating label typecode variableName] }
        formula =
      mandatoryFrame state formula := by
  unfold mandatoryFrame
  rw [mandatoryVariableNames_append_floating]
  rw [mandatoryHypotheses_append_optional_floating _ _ _ _ _ hoptional]

/-- A `$d` pair is optional for an assertion when at least one endpoint is not
a mandatory variable.  Such a pair is absent from the stored mandatory frame.
-/
theorem mandatoryFrame_append_optional_distinct
    (state : SourceState) (formula : ConstantHeadedFormula)
    (left right : String)
    (hoptional :
      left ∉ mandatoryVariableNames state formula ∨
        right ∉ mandatoryVariableNames state formula) :
    mandatoryFrame
        { state with
          activeDistinctVariables :=
            state.activeDistinctVariables ++ [(left, right)] }
        formula =
      mandatoryFrame state formula := by
  have hvariables :
      mandatoryVariableNames
          { state with
            activeDistinctVariables :=
              state.activeDistinctVariables ++ [(left, right)] }
          formula =
        mandatoryVariableNames state formula := rfl
  have hhypotheses :
      mandatoryHypotheses
          { state with
            activeDistinctVariables :=
              state.activeDistinctVariables ++ [(left, right)] }
          formula =
        mandatoryHypotheses state formula := rfl
  unfold mandatoryFrame
  rw [hvariables, hhypotheses]
  rcases hoptional with hleft | hright
  · simp [hleft]
  · simp [hright]

/-- A whole `$d` declaration may introduce several pairwise conditions at
once.  If every introduced pair has an optional endpoint, the complete batch
is absent from the stored mandatory frame. -/
theorem mandatoryFrame_append_optional_distincts
    (state : SourceState) (formula : ConstantHeadedFormula)
    (pairs : List (String × String))
    (hoptional : ∀ pair ∈ pairs,
      pair.1 ∉ mandatoryVariableNames state formula ∨
        pair.2 ∉ mandatoryVariableNames state formula) :
    mandatoryFrame
        { state with
          activeDistinctVariables := state.activeDistinctVariables ++ pairs }
        formula =
      mandatoryFrame state formula := by
  have hvariables :
      mandatoryVariableNames
          { state with
            activeDistinctVariables := state.activeDistinctVariables ++ pairs }
          formula =
        mandatoryVariableNames state formula := rfl
  have hhypotheses :
      mandatoryHypotheses
          { state with
            activeDistinctVariables := state.activeDistinctVariables ++ pairs }
          formula =
        mandatoryHypotheses state formula := rfl
  unfold mandatoryFrame
  rw [hvariables, hhypotheses]
  simp only
  rw [List.filter_append]
  have hempty :
      pairs.filter (fun pair =>
        (mandatoryVariableNames state formula).contains pair.1 &&
          (mandatoryVariableNames state formula).contains pair.2) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro pair hpair
    rcases hoptional pair hpair with hleft | hright
    · simp [hleft]
    · simp [hright]
  rw [hempty, List.append_nil]

/-- Positive calibration of the `$d` selector: a pair whose two endpoints are
mandatory is retained by the projection. -/
theorem mandatoryFrame_append_mandatory_distinct
    (state : SourceState) (formula : ConstantHeadedFormula)
    (left right : String)
    (hleft : left ∈ mandatoryVariableNames state formula)
    (hright : right ∈ mandatoryVariableNames state formula) :
    (mandatoryFrame
        { state with
          activeDistinctVariables :=
            state.activeDistinctVariables ++ [(left, right)] }
        formula).distinctVariables =
      (mandatoryFrame state formula).distinctVariables ++ [(left, right)] := by
  have hvariables :
      mandatoryVariableNames
          { state with
            activeDistinctVariables :=
              state.activeDistinctVariables ++ [(left, right)] }
          formula =
        mandatoryVariableNames state formula := rfl
  unfold mandatoryFrame
  rw [hvariables]
  simp [hleft, hright]

/-- [MM §4.2.7] The source-owned assertion stored after adjoining an optional
floating hypothesis is exactly the assertion that would have been stored
before it. -/
theorem sourceAssertion_append_optional_floating
    (state : SourceState) (assertionLabel : String)
    (formula : ConstantHeadedFormula) (label typecode variableName : String)
    (hoptional : variableName ∉ mandatoryVariableNames state formula) :
    sourceAssertion
        { state with
          activeHypotheses :=
            state.activeHypotheses ++
              [.floating label typecode variableName] }
        assertionLabel formula =
      sourceAssertion state assertionLabel formula := by
  unfold sourceAssertion
  rw [mandatoryFrame_append_optional_floating
      state formula label typecode variableName hoptional]
  rw [mandatoryHypotheses_append_optional_floating
      state formula label typecode variableName hoptional]

/-- [MM §4.2.7] The source-owned assertion stored after adjoining an optional
disjoint-variable pair is exactly the assertion that would have been stored
before it. -/
theorem sourceAssertion_append_optional_distinct
    (state : SourceState) (assertionLabel : String)
    (formula : ConstantHeadedFormula) (left right : String)
    (hoptional :
      left ∉ mandatoryVariableNames state formula ∨
        right ∉ mandatoryVariableNames state formula) :
    sourceAssertion
        { state with
          activeDistinctVariables :=
            state.activeDistinctVariables ++ [(left, right)] }
        assertionLabel formula =
      sourceAssertion state assertionLabel formula := by
  unfold sourceAssertion
  rw [mandatoryFrame_append_optional_distinct
    state formula left right hoptional]
  have hhypotheses :
      mandatoryHypotheses
          { state with
            activeDistinctVariables :=
              state.activeDistinctVariables ++ [(left, right)] }
          formula =
        mandatoryHypotheses state formula := rfl
  rw [hhypotheses]

/-- [MM §4.2.7] Batch form for an authored `$d` statement: if all newly
generated pairs are optional for the assertion, its stored source projection
is unchanged. -/
theorem sourceAssertion_append_optional_distincts
    (state : SourceState) (assertionLabel : String)
    (formula : ConstantHeadedFormula) (pairs : List (String × String))
    (hoptional : ∀ pair ∈ pairs,
      pair.1 ∉ mandatoryVariableNames state formula ∨
        pair.2 ∉ mandatoryVariableNames state formula) :
    sourceAssertion
        { state with
          activeDistinctVariables := state.activeDistinctVariables ++ pairs }
        assertionLabel formula =
      sourceAssertion state assertionLabel formula := by
  unfold sourceAssertion
  rw [mandatoryFrame_append_optional_distincts
    state formula pairs hoptional]
  have hhypotheses :
      mandatoryHypotheses
          { state with
            activeDistinctVariables := state.activeDistinctVariables ++ pairs }
          formula =
        mandatoryHypotheses state formula := rfl
  rw [hhypotheses]

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

/-- An accepted source `$d` operation whose generated pairs are all optional
for a later assertion leaves that assertion's stored mandatory projection
unchanged. -/
theorem declareDisjoint?_sourceAssertion_eq_of_optional
    {state after : SourceState} {names : List String}
    {assertionLabel : String} {formula : ConstantHeadedFormula}
    (declared : declareDisjoint? state names = some after)
    (hoptional : ∀ pair ∈ allDistinctPairs names,
      pair.1 ∉ mandatoryVariableNames state formula ∨
        pair.2 ∉ mandatoryVariableNames state formula) :
    sourceAssertion after assertionLabel formula =
      sourceAssertion state assertionLabel formula := by
  simp [declareDisjoint?, acceptUpdate] at declared
  rcases declared with ⟨_, _, _, _, _, _, rfl⟩
  exact sourceAssertion_append_optional_distincts
    state assertionLabel formula (allDistinctPairs names) hoptional

def declareFloating? (state : SourceState)
    (label typecode variableName : String) : Option SourceState := do
  guard (readyForLocalUpdate state)
  let hypothesis := HypothesisView.floating label typecode variableName
  acceptUpdate state
    { state with
      usedLabels := state.usedLabels ++ [label]
      activeHypotheses := state.activeHypotheses ++ [hypothesis] }

/-- An accepted source `$f` operation for a variable outside a later
assertion's mandatory support leaves the stored assertion exactly unchanged.
This connects the pure projection lemma to the actual GSLT state transition.
-/
theorem declareFloating?_sourceAssertion_eq_of_optional
    {state after : SourceState} {label typecode variableName : String}
    {assertionLabel : String} {formula : ConstantHeadedFormula}
    (declared :
      declareFloating? state label typecode variableName = some after)
    (hoptional : variableName ∉ mandatoryVariableNames state formula) :
    sourceAssertion after assertionLabel formula =
      sourceAssertion state assertionLabel formula := by
  simp [declareFloating?, acceptUpdate] at declared
  rcases declared with ⟨_, _, _, rfl⟩
  exact sourceAssertion_append_optional_floating
    state assertionLabel formula label typecode variableName hoptional

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

/-- Successful source insertion proves that the assertion label was absent
from the complete global namespace, including labels retired by scope exit. -/
theorem insertAssertion?_label_fresh
    {state after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (inserted : insertAssertion? state label formula = some after) :
    label ∉ state.objectNames := by
  simp [insertAssertion?, acceptUpdate] at inserted
  rcases inserted with ⟨_, _, afterValid, rfl⟩
  have namesNodup :=
    objectNames_nodup_of_sourceStateValid
      { state with
        usedLabels := state.usedLabels ++ [label]
        assertions := state.assertions ++
          [sourceAssertion state label formula] }
      afterValid
  have appendedNodup : (state.objectNames ++ [label]).Nodup := by
    simpa [SourceState.objectNames, List.append_assoc] using namesNodup
  intro member
  have cross := (List.nodup_append.mp appendedNodup).2.2
  exact cross label member label (by simp) rfl

/-- Source assertion insertion extends the global namespace by exactly its
authored label. -/
theorem insertAssertion?_objectNames
    {state after : SourceState} {label : String}
    {formula : ConstantHeadedFormula}
    (inserted : insertAssertion? state label formula = some after) :
    after.objectNames = state.objectNames ++ [label] := by
  simp [insertAssertion?, acceptUpdate] at inserted
  rcases inserted with ⟨_, _, _, rfl⟩
  simp [SourceState.objectNames, List.append_assoc]

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


/-! ## Acceptance inversion

Public characterizations of the accepted declaration operations, for
consumers outside this module (the gate internals stay private; these
expose exactly the accepted successor's shape and the validity facts the
gate guarantees). -/

/-- Inversion for an accepted singleton `$v` declaration. -/
theorem declareVariables?_singleton_inv {state after : SourceState}
    {variableName : String}
    (h : declareVariables? state [variableName] = some after) :
    sourceStateValid state = true ∧
      sourceStateValid after = true ∧
      after =
        { state with
          declaredVariables :=
            if variableName ∈ state.declaredVariables then
              state.declaredVariables
            else state.declaredVariables ++ [variableName] } := by
  simp [declareVariables?, acceptUpdate, addVariable] at h
  obtain ⟨hready, hbefore, hafter, hshape⟩ := h
  exact ⟨hbefore, hshape ▸ hafter, hshape.symm⟩

/-- Inversion for an accepted `$f` declaration. -/
theorem declareFloating?_inv {state after : SourceState}
    {label typecode variableName : String}
    (h : declareFloating? state label typecode variableName = some after) :
    sourceStateValid state = true ∧
      sourceStateValid after = true ∧
      after =
        { state with
          usedLabels := state.usedLabels ++ [label]
          activeHypotheses := state.activeHypotheses ++
            [HypothesisView.floating label typecode variableName] } := by
  simp [declareFloating?, acceptUpdate] at h
  obtain ⟨hready, hbefore, hafter, hshape⟩ := h
  exact ⟨hbefore, hshape ▸ hafter, hshape.symm⟩


/-! ## Acceptance existence

Sufficient freshness conditions under which the declaration gates accept.
Validity of the updated state is proved, not assumed. -/

/-- Converse executable-uniqueness bridge. -/
theorem eraseDups_length_eq_of_nodup :
    (values : List String) → values.Nodup →
      values.eraseDups.length = values.length
  | [], _ => rfl
  | value :: values, hnodup => by
      rw [List.eraseDups_cons]
      simp only [List.length_cons]
      have hhead : value ∉ values := (List.nodup_cons.mp hnodup).1
      have htail : values.Nodup := (List.nodup_cons.mp hnodup).2
      have hfilter :
          (values.filter fun candidate => !candidate == value) = values := by
        apply List.filter_eq_self.mpr
        intro candidate hmem
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne, ne_eq]
        intro heq
        exact hhead (heq ▸ hmem)
      rw [hfilter, eraseDups_length_eq_of_nodup values htail]

/-- The executable uniqueness test survives appending one fresh name. -/
theorem eraseDups_length_append_fresh {values : List String}
    {name : String}
    (hlen : values.eraseDups.length = values.length)
    (hfresh : name ∉ values) :
    (values ++ [name]).eraseDups.length = (values ++ [name]).length := by
  apply eraseDups_length_eq_of_nodup
  have hnodup := nodup_of_eraseDups_length_eq values hlen
  exact List.Nodup.append hnodup (List.nodup_singleton name)
    (fun a ha hax => hfresh ((List.mem_singleton.mp hax) ▸ ha))

/-- Declaration respect is monotone in the declared-variable list. -/
theorem formulaSymbolsRespectDeclarations_mono_vars
    {declaredConstants declaredVariables declaredVariables' : List String}
    (hsub : ∀ v ∈ declaredVariables, v ∈ declaredVariables')
    {formula : ConstantHeadedFormula}
    (h : formulaSymbolsRespectDeclarations declaredConstants
      declaredVariables formula = true) :
    formulaSymbolsRespectDeclarations declaredConstants
      declaredVariables' formula = true := by
  unfold formulaSymbolsRespectDeclarations at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun symbol hmem => ?_⟩
  have := h.2 symbol hmem
  cases symbol with
  | const constantName => exact this
  | var variableName =>
      simp only [List.contains_iff_mem] at this ⊢
      exact hsub _ this

/-- Assertion validity is monotone in the declared-variable list. -/
theorem sourceAssertionValid_mono_vars
    {declaredConstants declaredVariables declaredVariables' : List String}
    (hsub : ∀ v ∈ declaredVariables, v ∈ declaredVariables')
    {assertion : SourceAssertion}
    (h : sourceAssertionValid declaredConstants declaredVariables
      assertion = true) :
    sourceAssertionValid declaredConstants declaredVariables'
      assertion = true := by
  unfold sourceAssertionValid at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true] at h ⊢
  obtain ⟨⟨⟨hframe, hformula⟩, hhyps⟩, hassert⟩ := h
  exact ⟨⟨⟨hframe, hformula⟩,
    fun hyp hmem => formulaSymbolsRespectDeclarations_mono_vars hsub
      (hhyps hyp hmem)⟩,
    formulaSymbolsRespectDeclarations_mono_vars hsub hassert⟩

/-- `$v` acceptance from validity, readiness, and global freshness. -/
theorem declareVariables?_accepts (state : SourceState)
    (variableName : String)
    (hvalid : sourceStateValid state = true)
    (hready : state.pendingBlockCompletions = 0)
    (hfresh : variableName ∉ state.objectNames) :
    declareVariables? state [variableName] =
      some { state with
        declaredVariables :=
          state.declaredVariables ++ [variableName] } := by
  have hfreshConsts : variableName ∉ state.declaredConstants := fun h =>
    hfresh (by simp [SourceState.objectNames, h])
  have hfreshVars : variableName ∉ state.declaredVariables := fun h =>
    hfresh (by simp [SourceState.objectNames, h])
  have hsub : ∀ v ∈ state.declaredVariables,
      v ∈ state.declaredVariables ++ [variableName] :=
    fun v hv => List.mem_append_left _ hv
  have hvalidAfter :
      sourceStateValid
        { state with
          declaredVariables :=
            state.declaredVariables ++ [variableName] } = true := by
    unfold sourceStateValid at hvalid ⊢
    simp only [Bool.and_eq_true] at hvalid ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨hprefix, hlabelsOk⟩, hlabelsNodup⟩, hactiveSub⟩,
      hassertSub⟩, hobjNodup⟩, hdv⟩, hscopes⟩ := hvalid
    refine ⟨⟨⟨⟨⟨⟨⟨?_, hlabelsOk⟩, hlabelsNodup⟩, hactiveSub⟩,
      hassertSub⟩, ?_⟩, ?_⟩, ?_⟩
    · -- prefix validity
      unfold sourcePrefixValid at hprefix ⊢
      simp only [Bool.and_eq_true] at hprefix ⊢
      obtain ⟨⟨⟨⟨⟨⟨hconstsN, hvarsN⟩, hdisj⟩, hframe⟩, hhyps⟩,
        hasserts⟩, hlabels⟩ := hprefix
      refine ⟨⟨⟨⟨⟨⟨hconstsN, ?_⟩, ?_⟩, hframe⟩, ?_⟩, ?_⟩, hlabels⟩
      · -- variables stay duplicate-free
        have hold : state.declaredVariables.eraseDups.length =
            state.declaredVariables.length :=
          beq_iff_eq.mp (by
            simpa [SourceState.toSourcePrefix] using hvarsN)
        have hnew := eraseDups_length_append_fresh hold hfreshVars
        simp [SourceState.toSourcePrefix, hnew]
      · -- constants remain disjoint from variables
        simp only [SourceState.toSourcePrefix,
          List.all_eq_true] at hdisj ⊢
        intro constant hmem
        have hold : constant ∉ state.declaredVariables := by
          have := hdisj constant hmem
          simpa [List.contains_iff_mem] using this
        have hnotx : constant ≠ variableName :=
          fun h => hfreshConsts (h ▸ hmem)
        simp [List.mem_append, hold, hnotx]
      · -- hypothesis formulas respect the grown declarations
        simp only [SourceState.toSourcePrefix, List.all_eq_true,
          Function.comp] at hhyps ⊢
        intro hyp hmem
        exact formulaSymbolsRespectDeclarations_mono_vars hsub
          (hhyps hyp hmem)
      · -- stored assertions respect the grown declarations
        simp only [SourceState.toSourcePrefix,
          List.all_eq_true] at hasserts ⊢
        intro assertion hmem
        exact sourceAssertionValid_mono_vars hsub (hasserts assertion hmem)
    · -- the global namespace stays duplicate-free
      have holdN := nodup_of_eraseDups_length_eq _ (beq_iff_eq.mp hobjNodup)
      have holdN' : (state.declaredConstants ++
          (state.declaredVariables ++ state.usedLabels)).Nodup := by
        simpa [SourceState.objectNames, List.append_assoc] using holdN
      obtain ⟨hconstsN', hvarsLabelsN, hdisjC⟩ :=
        List.nodup_append.mp holdN'
      obtain ⟨hvarsN', hlabelsN', hdisjVL⟩ :=
        List.nodup_append.mp hvarsLabelsN
      have hfreshLabels : variableName ∉ state.usedLabels := fun h =>
        hfresh (by simp [SourceState.objectNames, h])
      have hnewN : (state.declaredConstants ++
          ((state.declaredVariables ++ [variableName]) ++
            state.usedLabels)).Nodup := by
        refine List.nodup_append.mpr ⟨hconstsN',
          List.nodup_append.mpr ⟨?_, hlabelsN', ?_⟩, ?_⟩
        · exact List.Nodup.append hvarsN' (List.nodup_singleton _)
            (fun a ha hax =>
              hfreshVars ((List.mem_singleton.mp hax) ▸ ha))
        · intro a ha b hb heq
          subst heq
          rcases List.mem_append.mp ha with hv | hx
          · exact hdisjVL a hv a hb rfl
          · exact hfreshLabels ((List.mem_singleton.mp hx) ▸ hb)
        · intro a ha b hb heq
          subst heq
          rcases List.mem_append.mp hb with hvx | hl
          · rcases List.mem_append.mp hvx with hv | hx
            · exact hdisjC a ha a (List.mem_append_left _ hv) rfl
            · exact hfreshConsts
                ((List.mem_singleton.mp hx) ▸ ha)
          · exact hdisjC a ha a (List.mem_append_right _ hl) rfl
      have := eraseDups_length_eq_of_nodup _ hnewN
      simp only [SourceState.objectNames, List.append_assoc]
      simpa using this
    · -- distinctness endpoints remain declared
      simp only [List.all_eq_true, Bool.and_eq_true] at hdv ⊢
      intro pair hmem
      obtain ⟨⟨horder, h1⟩, h2⟩ := hdv pair hmem
      refine ⟨⟨horder, ?_⟩, ?_⟩ <;>
        simp only [List.contains_iff_mem, List.mem_append] at * <;>
        [exact Or.inl h1; exact Or.inl h2]
    · -- scope boundaries reference untouched lengths
      simpa [boundaryValid] using hscopes
  unfold declareVariables?
  simp [guard, readyForLocalUpdate, hready, acceptUpdate, hvalid,
    addVariable, hfreshVars]
  rw [← hready]
  exact hvalidAfter


/-- Floating-variable names distribute over an appended floating
hypothesis. -/
theorem floatingVariableNames_append_floating
    (hypotheses : List HypothesisView)
    (label typecode variableName : String) :
    floatingVariableNames
        (hypotheses ++ [HypothesisView.floating label typecode
          variableName]) =
      floatingVariableNames hypotheses ++ [variableName] := by
  simp [floatingVariableNames, List.filterMap_append,
    HypothesisView.floatingVariable?]

/-- Prefix scoping survives appending a floating hypothesis: essentials
only ever consult the variables available before them. -/
theorem hypothesesPrefixScopedFrom_append_floating :
    ∀ (available : List String) (hypotheses : List HypothesisView)
      (label typecode variableName : String),
      hypothesesPrefixScopedFrom available hypotheses = true →
      hypothesesPrefixScopedFrom available
        (hypotheses ++ [HypothesisView.floating label typecode
          variableName]) = true
  | available, [], _, _, _, _ => rfl
  | available, .floating l t v :: hypotheses, label, typecode,
      variableName, h => by
      simp only [List.cons_append, hypothesesPrefixScopedFrom] at h ⊢
      exact hypothesesPrefixScopedFrom_append_floating _ hypotheses
        label typecode variableName h
  | available, .essential l formula :: hypotheses, label, typecode,
      variableName, h => by
      simp only [List.cons_append, hypothesesPrefixScopedFrom,
        Bool.and_eq_true] at h ⊢
      exact ⟨h.1, hypothesesPrefixScopedFrom_append_floating _ hypotheses
        label typecode variableName h.2⟩

/-- Frame respect survives a grown floating list for a formula whose
constants are declared, because declared constants can never collide
with the (declared) new variable. -/
theorem formulaSymbolsRespectFrame_extend
    {floatingVariables : List String} {variableName : String}
    {declaredConstants declaredVariables : List String}
    (hdisj : ∀ c ∈ declaredConstants, c ∉ declaredVariables)
    (hvar : variableName ∈ declaredVariables)
    {formula : ConstantHeadedFormula}
    (hdecl : formulaSymbolsRespectDeclarations declaredConstants
      declaredVariables formula = true)
    (hframe : formulaSymbolsRespectFrame floatingVariables
      formula = true) :
    formulaSymbolsRespectFrame
      (floatingVariables ++ [variableName]) formula = true := by
  unfold formulaSymbolsRespectFrame at hframe ⊢
  unfold formulaSymbolsRespectDeclarations at hdecl
  simp only [List.all_eq_true, Bool.and_eq_true] at hframe hdecl ⊢
  intro symbol hmem
  have hf := hframe symbol hmem
  have hd := hdecl.2 symbol hmem
  cases symbol with
  | var v =>
      have hv : v ∈ floatingVariables := by
        simpa [symbolRespectsFrame, List.contains_iff_mem] using hf
      simp [symbolRespectsFrame, List.mem_append, hv]
  | const c =>
      have hfc : c ∉ floatingVariables := by
        simpa [symbolRespectsFrame, List.contains_iff_mem] using hf
      have hdc : c ∈ declaredConstants := by
        simpa [List.contains_iff_mem] using hd
      have hcx : c ≠ variableName := fun heq =>
        hdisj c hdc (heq ▸ hvar)
      simp [symbolRespectsFrame, List.mem_append, hfc, hcx]

/-- `$f` acceptance from validity, readiness, freshness of the label,
declaredness of the variable and typecode, and absence of a prior active
float for the variable. -/
theorem declareFloating?_accepts (state : SourceState)
    (label typecode variableName : String)
    (hvalid : sourceStateValid state = true)
    (hready : state.pendingBlockCompletions = 0)
    (hlabelFresh : label ∉ state.objectNames)
    (hlabelNonempty : label ≠ "")
    (hlabelPrefix : ¬ label.startsWith reservedRulePrefix = true)
    (hvarDeclared : variableName ∈ state.declaredVariables)
    (hvarNoFloat : variableName ∉ state.activeFloatingVariables)
    (htype : typecode ∈ state.declaredConstants) :
    declareFloating? state label typecode variableName =
      some { state with
        usedLabels := state.usedLabels ++ [label]
        activeHypotheses := state.activeHypotheses ++
          [HypothesisView.floating label typecode variableName] } := by
  have hlabelLabels : label ∉ state.usedLabels := fun h =>
    hlabelFresh (by simp [SourceState.objectNames, h])
  have hvalidLabel : validRuleLabel label = true := by
    unfold validRuleLabel
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    exact ⟨hlabelNonempty, Bool.eq_false_iff.mpr hlabelPrefix⟩
  have hvalidAfter :
      sourceStateValid
        { state with
          usedLabels := state.usedLabels ++ [label]
          activeHypotheses := state.activeHypotheses ++
            [HypothesisView.floating label typecode variableName] } =
        true := by
    unfold sourceStateValid at hvalid ⊢
    simp only [Bool.and_eq_true] at hvalid ⊢
    obtain ⟨⟨⟨⟨⟨⟨⟨hprefix, hlabelsOk⟩, hlabelsNodup⟩, hactiveSub⟩,
      hassertSub⟩, hobjNodup⟩, hdv⟩, hscopes⟩ := hvalid
    have hdisjCV : ∀ c ∈ state.declaredConstants,
        c ∉ state.declaredVariables := by
      have hp := hprefix
      unfold sourcePrefixValid at hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hdisj⟩, -⟩, -⟩, -⟩, -⟩ := hp
      simp only [SourceState.toSourcePrefix, List.all_eq_true] at hdisj
      intro c hc
      have := hdisj c hc
      simpa [List.contains_iff_mem] using this
    refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- prefix validity
      unfold sourcePrefixValid at hprefix ⊢
      simp only [Bool.and_eq_true] at hprefix ⊢
      obtain ⟨⟨⟨⟨⟨⟨hconstsN, hvarsN⟩, hdisj⟩, hframe⟩, hhyps⟩,
        hasserts⟩, hlabels⟩ := hprefix
      refine ⟨⟨⟨⟨⟨⟨hconstsN, hvarsN⟩, hdisj⟩, ?_⟩, ?_⟩,
        hasserts⟩, ?_⟩
      · -- frame validity over the grown hypotheses
        unfold sourceFrameValid at hframe ⊢
        simp only [Bool.and_eq_true] at hframe ⊢
        obtain ⟨⟨⟨⟨⟨huniqueL, huniqueF⟩, hscoped⟩, hsync⟩,
          hrespect⟩, hdvv⟩ := hframe
        refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
        · -- unique labels
          unfold hasUniqueLabels at huniqueL ⊢
          simp only [SourceState.toSourcePrefix, List.map_append,
            List.map_cons, List.map_nil] at huniqueL ⊢
          have hfreshHyp : label ∉
              state.activeHypotheses.map HypothesisView.label := by
            intro hmem
            apply hlabelLabels
            simp only [List.all_eq_true] at hactiveSub
            have := hactiveSub label (by simpa using hmem)
            simpa [List.contains_iff_mem] using this
          have := eraseDups_length_append_fresh
            (beq_iff_eq.mp huniqueL) hfreshHyp
          simpa [HypothesisView.label] using this
        · -- unique floating variables
          unfold hasUniqueFloatingVariables at huniqueF ⊢
          simp only [SourceState.toSourcePrefix] at huniqueF ⊢
          rw [floatingVariableNames_append_floating]
          have := eraseDups_length_append_fresh
            (beq_iff_eq.mp huniqueF)
            (by simpa [SourceState.activeFloatingVariables]
              using hvarNoFloat)
          simpa using this
        · -- prefix scoping
          simp only [SourceState.toSourcePrefix] at hscoped ⊢
          exact hypothesesPrefixScopedFrom_append_floating _ _ _ _ _
            hscoped
        · -- label synchronization with the derived caller frame
          simp [SourceState.toSourcePrefix, SourceState.callerFrame]
        · -- per-hypothesis frame respect over grown floats
          simp only [SourceState.toSourcePrefix, List.all_eq_true,
            Function.comp] at hrespect ⊢
          intro hyp hmem
          rw [floatingVariableNames_append_floating]
          rcases List.mem_append.mp hmem with hold | hnew
          · have hdecl : formulaSymbolsRespectDeclarations
                state.declaredConstants state.declaredVariables
                hyp.formula = true := by
              simp only [SourceState.toSourcePrefix, List.all_eq_true,
                Function.comp] at hhyps
              exact hhyps hyp hold
            exact formulaSymbolsRespectFrame_extend hdisjCV hvarDeclared
              hdecl (hrespect hyp hold)
          · rcases List.mem_singleton.mp hnew with rfl
            simp [HypothesisView.formula, formulaSymbolsRespectFrame,
              symbolRespectsFrame, List.mem_append]
        · -- disjointness data valid over grown floats
          unfold sourceFrameDVValid at hdvv ⊢
          simp only [SourceState.toSourcePrefix, SourceState.callerFrame,
            List.all_eq_true, Bool.and_eq_true] at hdvv ⊢
          intro pair hmem
          have hfilter := List.of_mem_filter hmem
          simp only [Bool.and_eq_true] at hfilter
          have hstored := List.mem_of_mem_filter hmem
          have horder : decide (pair.1 < pair.2) = true := by
            simp only [List.all_eq_true, Bool.and_eq_true] at hdv
            exact ((hdv pair hstored).1).1
          exact ⟨⟨horder, hfilter.1⟩, hfilter.2⟩
      · -- hypothesis formulas respect declarations
        simp only [SourceState.toSourcePrefix, List.all_eq_true,
          Function.comp] at hhyps ⊢
        intro hyp hmem
        rcases List.mem_append.mp hmem with hold | hnew
        · exact hhyps hyp hold
        · rcases List.mem_singleton.mp hnew with rfl
          simp [HypothesisView.formula,
            formulaSymbolsRespectDeclarations, htype, hvarDeclared]
      · -- rule labels remain valid and duplicate-free
        unfold sourceRuleLabelsValid at hlabels ⊢
        simp only [Bool.and_eq_true] at hlabels ⊢
        obtain ⟨hall, hnodupL⟩ := hlabels
        constructor
        · simp only [sourcePrefixRuleLabels, SourceState.toSourcePrefix,
            List.map_append, List.map_cons, List.map_nil,
            List.all_eq_true] at hall ⊢
          intro l hmem
          simp only [List.mem_append, List.mem_singleton] at hmem
          rcases hmem with (hh | rfl) | ha
          · exact hall l (List.mem_append_left _ hh)
          · simpa [validRuleLabel] using hvalidLabel
          · exact hall l (List.mem_append_right _ ha)
        · -- duplicate-freedom with the label inserted mid-list
          have holdN := nodup_of_eraseDups_length_eq _
            (beq_iff_eq.mp hnodupL)
          simp only [sourcePrefixRuleLabels,
            SourceState.toSourcePrefix] at holdN ⊢
          obtain ⟨hhN, haN, hdisjHA⟩ := List.nodup_append.mp holdN
          have hfreshH : label ∉
              state.activeHypotheses.map HypothesisView.label := by
            intro hmem
            apply hlabelLabels
            simp only [List.all_eq_true] at hactiveSub
            have := hactiveSub label hmem
            simpa [List.contains_iff_mem] using this
          have hfreshA : label ∉
              state.assertions.map SourceAssertion.label := by
            intro hmem
            apply hlabelLabels
            simp only [List.all_eq_true] at hassertSub
            have := hassertSub label hmem
            simpa [List.contains_iff_mem] using this
          have hnewN :
              ((state.activeHypotheses.map HypothesisView.label ++
                  [label]) ++
                state.assertions.map SourceAssertion.label).Nodup := by
            refine List.nodup_append.mpr ⟨?_, haN, ?_⟩
            · exact List.Nodup.append hhN (List.nodup_singleton _)
                (fun a ha hax =>
                  hfreshH ((List.mem_singleton.mp hax) ▸ ha))
            · intro a ha b hb heq
              subst heq
              rcases List.mem_append.mp ha with hh | hx
              · exact hdisjHA a hh a hb rfl
              · exact hfreshA ((List.mem_singleton.mp hx) ▸ hb)
          have := eraseDups_length_eq_of_nodup _ hnewN
          simp only [List.map_append, List.map_cons, List.map_nil]
          simpa [HypothesisView.label, List.append_assoc] using this
    · -- every used label remains a valid rule label
      simp only [List.all_eq_true] at hlabelsOk ⊢
      intro l hmem
      rcases List.mem_append.mp hmem with hold | hnew
      · exact hlabelsOk l hold
      · rcases List.mem_singleton.mp hnew with rfl
        exact hvalidLabel
    · -- used labels stay duplicate-free
      exact beq_iff_eq.mpr (eraseDups_length_append_fresh
        (beq_iff_eq.mp hlabelsNodup) hlabelLabels)
    · -- active hypothesis labels remain used
      simp only [List.all_eq_true, List.map_append, List.map_cons,
        List.map_nil] at hactiveSub ⊢
      intro l hmem
      simp only [List.contains_iff_mem, List.mem_append,
        List.mem_singleton] at *
      rcases hmem with hold | rfl
      · exact Or.inl (hactiveSub l hold)
      · exact Or.inr rfl
    · -- assertion labels remain used
      simp only [List.all_eq_true] at hassertSub ⊢
      intro l hmem
      have := hassertSub l hmem
      simp only [List.contains_iff_mem, List.mem_append] at this ⊢
      exact Or.inl this
    · -- the global namespace stays duplicate-free
      have := eraseDups_length_append_fresh
        (beq_iff_eq.mp hobjNodup) hlabelFresh
      simp only [SourceState.objectNames, List.append_assoc] at this ⊢
      simpa using this
    · -- distinctness endpoints unchanged
      exact hdv
    · -- scope boundaries: hypothesis count only grows
      simp only [List.all_eq_true] at hscopes ⊢
      intro boundary hmem
      have := hscopes boundary hmem
      simp only [boundaryValid, Bool.and_eq_true,
        decide_eq_true_eq, List.length_append] at this ⊢
      exact ⟨Nat.le_trans this.1 (Nat.le_add_right _ _), this.2⟩
  unfold declareFloating?
  simp [guard, readyForLocalUpdate, hready, acceptUpdate, hvalid]
  rw [← hready]
  exact hvalidAfter

/-! ## Uniform acceptance-validity (for the raw-source composition)

Every local operation and the assertion insertion funnel through
`acceptUpdate` (or, for `completeBlock?`, guard validity directly), so
any accepted successor is valid.  Stated here because `acceptUpdate` is
private; the composition fold consumes only these public facts. -/

private theorem bind_guard_some {c : Prop} [Decidable c] {α : Type _}
    {rest : Option α} {a : α}
    (h : (do guard c; rest) = some a) : c ∧ rest = some a := by
  by_cases hc : c
  · refine ⟨hc, ?_⟩
    simpa [guard, hc] using h
  · simp [guard, hc] at h

private theorem bind_some_inv {α β : Type _} {o : Option β}
    {f : β → Option α} {a : α}
    (h : (o >>= f) = some a) : ∃ b, o = some b ∧ f b = some a := by
  cases ho : o with
  | none => rw [ho] at h; exact nomatch h
  | some b => rw [ho] at h; exact ⟨b, rfl, h⟩

private theorem acceptUpdate_valid {before next after : SourceState}
    (h : acceptUpdate before next = some after) :
    sourceStateValid after = true := by
  unfold acceptUpdate at h
  obtain ⟨-, h⟩ := bind_guard_some h
  obtain ⟨hnext, h⟩ := bind_guard_some h
  cases Option.some.inj h
  exact hnext

theorem insertAssertion?_valid {state after : SourceState}
    {label : String} {formula : ConstantHeadedFormula}
    (h : insertAssertion? state label formula = some after) :
    sourceStateValid after = true := by
  unfold insertAssertion? at h
  obtain ⟨-, h⟩ := bind_guard_some h
  exact acceptUpdate_valid h

/-- Every accepted local payload application yields a valid state. -/
theorem applyLocalPayload?_valid {payload : LocalPayload}
    {state after : SourceState}
    (h : applyLocalPayload? payload state = some after) :
    sourceStateValid after = true := by
  cases payload with
  | openScope =>
      unfold applyLocalPayload? openScope? at h
      obtain ⟨-, h⟩ := bind_guard_some h
      exact acceptUpdate_valid h
  | closeScope =>
      unfold applyLocalPayload? closeScope? at h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨boundary, -, h⟩ := bind_some_inv h
      exact acceptUpdate_valid h
  | declareConstants names =>
      unfold applyLocalPayload? declareConstants? at h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨-, h⟩ := bind_guard_some h
      exact acceptUpdate_valid h
  | declareVariables names =>
      unfold applyLocalPayload? declareVariables? at h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨-, h⟩ := bind_guard_some h
      exact acceptUpdate_valid h
  | declareDisjoint names =>
      unfold applyLocalPayload? declareDisjoint? at h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨-, h⟩ := bind_guard_some h
      exact acceptUpdate_valid h
  | declareFloating label typecode variableName =>
      unfold applyLocalPayload? declareFloating? at h
      obtain ⟨-, h⟩ := bind_guard_some h
      exact acceptUpdate_valid h
  | declareEssential label formula =>
      unfold applyLocalPayload? declareEssential? at h
      obtain ⟨-, h⟩ := bind_guard_some h
      exact acceptUpdate_valid h
  | declareAxiom label formula =>
      unfold applyLocalPayload? declareAxiom? at h
      exact insertAssertion?_valid h
  | completeBlock =>
      unfold applyLocalPayload? completeBlock? at h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨-, h⟩ := bind_guard_some h
      obtain ⟨hafter, h⟩ := bind_guard_some h
      cases Option.some.inj h
      exact hafter

/-- The empty source state is valid (fold seed). -/
theorem initialState_valid : sourceStateValid initialState = true := by
  decide

end Mettapedia.Languages.Metamath.SourceGSLTState
