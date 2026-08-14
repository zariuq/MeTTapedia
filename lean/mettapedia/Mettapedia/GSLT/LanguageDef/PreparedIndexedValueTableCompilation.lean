import Mettapedia.GSLT.Core.Composition

/-!
# Prepared indexed-value table compilation

An authored action may carry an immutable finite value segment before a later
indexed instruction stream.  A generated recognizer can then materialize that
segment once as an ordered random-access table.  Each decoded index observes
the same value occurrence as the source list lookup; duplicates remain
distinct positions and an out-of-range index still returns no value.

The recognizer depends only on local input shape and lifetime.  It requires one
unambiguous immutable-values/indexed-stream boundary, distinct roles, no
mutation of the selected value role, and a call-local region.  Unsupported,
ambiguous, mutable, or escaping shapes fail closed.
-/

namespace Mettapedia.GSLT.LanguageDef.PreparedIndexedValueTableCompilation

universe uRole uValue

/-- Structural input modes visible in an authored action signature. -/
inductive InputSegment (Role : Type uRole) where
  | scalar (role : Role)
  | immutableValues (role : Role)
  | mutableValues (role : Role)
  | indexedStream (role : Role)
  deriving DecidableEq, Repr

/-- Lifetime supplied by the generated effect/storage analysis. -/
inductive Region where
  | callLocal
  | retained
  deriving DecidableEq, Repr

/-- The source-side shape inspected by the recognizer. -/
structure ActionShape (Role : Type uRole) where
  inputs : List (InputSegment Role)
  region : Region
  deriving DecidableEq, Repr

/-- One potential immutable-header/indexed-stream boundary. -/
structure Candidate (Role : Type uRole) where
  headerRole : Role
  codeRole : Role
  deriving DecidableEq, Repr

/-- Enumerate adjacent structural boundaries without assigning semantics to
any other input mode. -/
def candidates : List (InputSegment Role) → List (Candidate Role)
  | .immutableValues headerRole :: .indexedStream codeRole :: rest =>
      { headerRole, codeRole } ::
        candidates (.indexedStream codeRole :: rest)
  | _ :: second :: rest => candidates (second :: rest)
  | _ => []

def mutates [DecidableEq Role]
    (inputs : List (InputSegment Role)) (role : Role) : Bool :=
  inputs.any fun
    | .mutableValues mutated => decide (mutated = role)
    | _ => false

/-- Persistent generated product of successful structural recognition. -/
structure Plan (Role : Type uRole) where
  headerRole : Role
  codeRole : Role
  deriving DecidableEq, Repr

/-- The executable recognizer accepts exactly one safe local boundary. -/
def recognize [DecidableEq Role] (shape : ActionShape Role) :
    Option (Plan Role) :=
  match candidates shape.inputs with
  | [candidate] =>
      if candidate.headerRole = candidate.codeRole ||
          mutates shape.inputs candidate.headerRole ||
          shape.region != .callLocal then
        none
      else
        some
          { headerRole := candidate.headerRole
            codeRole := candidate.codeRole }
  | _ => none

/-- Source action: the selected immutable header and its decoded requests. -/
structure SourceProgram (Role : Type uRole) (Value : Type uValue) where
  shape : ActionShape Role
  values : List Value
  requests : List Nat

/-- Generated artifact: the same occurrences in a contiguous indexed table. -/
structure Artifact (Role : Type uRole) (Value : Type uValue) where
  plan : Plan Role
  values : Array Value
  requests : List Nat

def sourceLookup (values : List Value) (index : Nat) : Option Value :=
  values[index]?

def preparedLookup (values : Array Value) (index : Nat) : Option Value :=
  values[index]?

def runSource (source : SourceProgram Role Value) : List (Option Value) :=
  source.requests.map (sourceLookup source.values)

def runArtifact (artifact : Artifact Role Value) : List (Option Value) :=
  artifact.requests.map (preparedLookup artifact.values)

def compile (plan : Plan Role) (source : SourceProgram Role Value) :
    Artifact Role Value :=
  { plan, values := source.values.toArray, requests := source.requests }

/-- Array lowering preserves exact index observations, including duplicate
occurrences and failed bounds checks. -/
theorem preparedLookup_toArray (values : List Value) (index : Nat) :
    preparedLookup values.toArray index = sourceLookup values index := by
  simp [preparedLookup, sourceLookup]

theorem runArtifact_compile (plan : Plan Role)
    (source : SourceProgram Role Value) :
    runArtifact (compile plan source) = runSource source := by
  simp [runArtifact, runSource, compile, preparedLookup_toArray]

/-! ## Immutable dictionary plus append-only saved suffix -/

/-- The source semantics observes one logical index space: immutable prepared
values first, then values saved during the current execution. -/
def sourceSplitLookup (prepared : List Value) (saved : List Saved)
    (index : Nat) : Option (Sum Value Saved) :=
  (prepared.map Sum.inl ++ saved.map Sum.inr)[index]?

/-- The compiled representation keeps the two lifetimes in separate dense
tables and selects the suffix only after subtracting the immutable prefix
length. -/
def preparedSplitLookup (prepared : Array Value) (saved : Array Saved)
    (index : Nat) : Option (Sum Value Saved) :=
  if index < prepared.size then
    (prepared[index]?).map Sum.inl
  else
    (saved[index - prepared.size]?).map Sum.inr

/-- Splitting an immutable dictionary from its append-only saved-result suffix
preserves every in-range and out-of-range lookup exactly. -/
theorem preparedSplitLookup_toArray
    (prepared : List Value) (saved : List Saved) (index : Nat) :
    preparedSplitLookup prepared.toArray saved.toArray index =
      sourceSplitLookup prepared saved index := by
  by_cases inside : index < prepared.length
  · have insideArray : index < prepared.toArray.size := by
      simpa using inside
    rw [preparedSplitLookup, if_pos insideArray]
    simp only [sourceSplitLookup]
    rw [List.getElem?_append_left]
    · simp
    · simpa using inside
  · have after : prepared.length ≤ index := Nat.le_of_not_gt inside
    have outsideArray : ¬index < prepared.toArray.size := by
      simpa using inside
    rw [preparedSplitLookup, if_neg outsideArray]
    simp only [sourceSplitLookup]
    rw [List.getElem?_append_right]
    · simp only [List.length_map]
      simp
    · simpa using after

/-- Successfully admitted source paired with its replayable recognizer
certificate. -/
structure AdmittedProgram (Role : Type uRole) (Value : Type uValue)
    [DecidableEq Role] where
  source : SourceProgram Role Value
  plan : Plan Role
  accepted : recognize source.shape = some plan

def admit? [DecidableEq Role] (source : SourceProgram Role Value) :
    Option (AdmittedProgram Role Value) :=
  match accepted : recognize source.shape with
  | none => none
  | some plan => some { source, plan, accepted }

/-- Prepared indexed values are a composable exact realization. -/
def preparedIndexedValueRealization [DecidableEq Role] :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedProgram Role Value) (Artifact Role Value)
      (List (Option Value)) where
  compile := fun _ admitted => compile admitted.plan admitted.source
  observeSource := fun _ admitted => runSource admitted.source
  observeArtifact := fun _ artifact => runArtifact artifact
  adequate := by
    intro _ admitted
    exact runArtifact_compile admitted.plan admitted.source

/-! ## Cost certificate -/

/-- Number of source-list cells inspected by one indexed lookup. -/
def sourceLookupCost : List Value → Nat → Nat
  | [], _ => 0
  | _ :: _, 0 => 1
  | _ :: values, index + 1 => 1 + sourceLookupCost values index

/-- A prepared table performs at most one bounds-checked indexed access. -/
def preparedLookupCost (values : List Value) (index : Nat) : Nat :=
  if index < values.length then 1 else 0

theorem preparedLookupCost_le_sourceLookupCost
    (values : List Value) (index : Nat) :
    preparedLookupCost values index ≤ sourceLookupCost values index := by
  cases values with
  | nil => simp [preparedLookupCost, sourceLookupCost]
  | cons value values =>
      cases index with
      | zero => simp [preparedLookupCost, sourceLookupCost]
      | succ index =>
          simp only [preparedLookupCost, sourceLookupCost,
            List.length_cons, Nat.succ_lt_succ_iff]
          split <;> omega

def sourceRunCost (source : SourceProgram Role Value) : Nat :=
  (source.requests.map (sourceLookupCost source.values)).sum

def preparedRunCost (source : SourceProgram Role Value) : Nat :=
  (source.requests.map (preparedLookupCost source.values)).sum

theorem preparedRunCost_le_sourceRunCost
    (source : SourceProgram Role Value) :
    preparedRunCost source ≤ sourceRunCost source := by
  unfold preparedRunCost sourceRunCost
  induction source.requests with
  | nil => simp
  | cons request requests inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (preparedLookupCost_le_sourceLookupCost source.values request)
        inductionHypothesis

/-! ## Independent witnesses and rejection boundary -/

private inductive ParserRole where
  | state | actionTable | opcode
  deriving DecidableEq, Repr

private def parserProgram : SourceProgram ParserRole String :=
  { shape :=
      { inputs := [.scalar .state, .immutableValues .actionTable,
          .indexedStream .opcode]
        region := .callLocal }
    values := ["shift", "reduce", "accept"]
    requests := [1, 0, 3] }

/-- Parser action tables instantiate the same local property. -/
example : (admit? parserProgram).isSome = true := by
  decide

example :
    let admitted := (admit? parserProgram).get (by decide)
    runArtifact
        (preparedIndexedValueRealization.compile () admitted) =
      [some "reduce", some "shift", none] := by
  decide

private inductive ProcessRole where
  | channel | continuationTable | continuationIndex
  deriving DecidableEq, Repr

private def processProgram : SourceProgram ProcessRole Nat :=
  { shape :=
      { inputs := [.scalar .channel,
          .immutableValues .continuationTable,
          .indexedStream .continuationIndex]
        region := .callLocal }
    values := [11, 23, 11]
    requests := [0, 2] }

/-- A process scheduler preserves two equal payload occurrences at distinct
continuation indices. -/
example :
    let admitted := (admit? processProgram).get (by decide)
    runArtifact
        (preparedIndexedValueRealization.compile () admitted) =
      [some 11, some 11] := by
  decide

/-- A deeper lookup exhibits strict improvement in the local inspection
model. -/
example : preparedLookupCost processProgram.values 2 = 1 ∧
    sourceLookupCost processProgram.values 2 = 3 := by
  decide

private def mutableProgram : SourceProgram ParserRole String :=
  { parserProgram with
    shape :=
      { inputs := [.immutableValues .actionTable,
          .mutableValues .actionTable, .indexedStream .opcode]
        region := .callLocal } }

/-- Mutation of the selected header role fails admission. -/
example : (admit? mutableProgram).isSome = false := by
  decide

private def escapingProgram : SourceProgram ProcessRole Nat :=
  { processProgram with shape := { processProgram.shape with
      region := .retained } }

/-- A table whose references may outlive the call is not admitted. -/
example : (admit? escapingProgram).isSome = false := by
  decide

private def ambiguousProgram : SourceProgram ParserRole String :=
  { parserProgram with
    shape :=
      { inputs := [.immutableValues .actionTable,
          .indexedStream .opcode, .immutableValues .actionTable,
          .indexedStream .state]
        region := .callLocal } }

/-- Multiple candidate boundaries are rejected rather than selected by an
unstated priority rule. -/
example : (admit? ambiguousProgram).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.PreparedIndexedValueTableCompilation
