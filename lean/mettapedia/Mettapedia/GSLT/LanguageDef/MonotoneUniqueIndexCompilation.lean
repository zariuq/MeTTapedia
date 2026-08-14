import Mettapedia.GSLT.Core.Composition
import Mettapedia.Util.LinearHash
import Std.Data.HashMap.Lemmas

/-!
# Monotone unique-key index compilation

An authored table whose finite key carrier is fixed, whose only effects are
fresh insertion and lookup, and whose concrete keys are duplicate-free can be
compiled from linear association-list lookup to an immutable hash index.

The recognizer is deliberately local.  It does not infer uniqueness from a
name such as `label`, nor does it accept overwrite or deletion.  Duplicate
freedom is checked by the shared hash-indexed validator and retained as an
admission certificate.  The compiled realization preserves exact lookup
results and the number of admitted entries.

The cost result below counts abstract dictionary operations.  It does not
claim that open addressing performs one physical probe: collision and growth
accounting belong to the concrete realization refinement.
-/

namespace Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

/-- Effects declared locally for the table selected by storage analysis. -/
inductive Effect where
  | lookup
  | insertFresh
  | overwrite
  | erase
  deriving DecidableEq, Repr

/-- The portion of a generated table description inspected by this pass. -/
structure TableShape where
  keyBits : Nat
  effects : List Effect
  deriving DecidableEq, Repr

/-- Persistent certificate payload emitted by successful recognition. -/
structure Plan where
  keyBits : Nat
  effects : List Effect
  deriving DecidableEq, Repr

def effectSupported : Effect → Bool
  | .lookup | .insertFresh => true
  | .overwrite | .erase => false

/-- Admit precisely 32-bit tables that are populated by fresh insertion and
subsequently queried, without mutation or deletion. -/
def recognize (shape : TableShape) : Option Plan :=
  if shape.keyBits == 32 &&
      shape.effects.contains .insertFresh &&
      shape.effects.contains .lookup &&
      shape.effects.all effectSupported then
    some { keyBits := shape.keyBits, effects := shape.effects }
  else
    none

/-- Source table and its observations before index construction. -/
structure SourceProgram (Key Value : Type) where
  shape : TableShape
  entries : List (Key × Value)
  queries : List Key

/-- The clear source specification scans entries in authored order. -/
def sourceLookup [BEq Key] (query : Key) :
    List (Key × Value) → Option Value
  | [] => none
  | (key, value) :: rest =>
      if key == query then some value else sourceLookup query rest

/-- Insert the tail first so the first authored occurrence would win.  An
admitted program contains no duplicates, but this definition keeps lookup
adequacy independent of that side condition. -/
def compileIndex [BEq Key] [Hashable Key] :
    List (Key × Value) → Std.HashMap Key Value
  | [] => {}
  | (key, value) :: rest => (compileIndex rest).insert key value

theorem lookup_compileIndex [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (entries : List (Key × Value)) (query : Key) :
    (compileIndex entries)[query]? = sourceLookup query entries := by
  induction entries with
  | nil => simp [compileIndex, sourceLookup]
  | cons entry entries inductionHypothesis =>
      rcases entry with ⟨key, value⟩
      rw [compileIndex, Std.HashMap.getElem?_insert, inductionHypothesis]
      rfl

theorem contains_compileIndex [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (entries : List (Key × Value)) (query : Key) :
    (compileIndex entries).contains query =
      (entries.map Prod.fst).contains query := by
  induction entries with
  | nil => simp [compileIndex]
  | cons entry entries inductionHypothesis =>
      rcases entry with ⟨key, value⟩
      rw [compileIndex, Std.HashMap.contains_insert, inductionHypothesis]
      simp only [List.map_cons, List.contains_cons]
      rw [Bool.beq_comm]

/-- Duplicate-free source keys occupy exactly one compiled slot each. -/
theorem size_compileIndex_of_nodup [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (entries : List (Key × Value))
    (distinct : (entries.map Prod.fst).Nodup) :
    (compileIndex entries).size = entries.length := by
  induction entries with
  | nil => simp [compileIndex]
  | cons entry entries inductionHypothesis =>
      rcases entry with ⟨key, value⟩
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      rw [compileIndex, Std.HashMap.size_insert]
      have notMem : ¬key ∈ compileIndex entries := by
        rw [Std.HashMap.mem_iff_contains, contains_compileIndex]
        simpa [List.contains_iff_mem] using absent
      simp [notMem, inductionHypothesis tailDistinct]

/-- Generated physical artifact.  The concrete C refinement realizes this
map with an append-only open-addressed table and rejects duplicate insertion. -/
structure Artifact (Key Value : Type)
    [BEq Key] [Hashable Key] where
  plan : Plan
  index : Std.HashMap Key Value
  queries : List Key

def runSource [BEq Key] (source : SourceProgram Key Value) :
    List (Option Value) :=
  source.queries.map fun query => sourceLookup query source.entries

def runArtifact [BEq Key] [Hashable Key]
    (artifact : Artifact Key Value) : List (Option Value) :=
  artifact.queries.map fun query => artifact.index[query]?

/-! ## Call-local reset and reuse -/

/-- One call builds a duplicate-rejecting finite index and observes it only
through exact lookup results. -/
structure IndexCall (Key Value : Type) where
  entries : List (Key × Value)
  queries : List Key

/-- Abstract physical state: logical entries are separated from retained
capacity, which is invisible to lookup. -/
structure ReusableIndexState (Key Value : Type)
    [BEq Key] [Hashable Key] where
  index : Std.HashMap Key Value
  retainedCapacity : Nat

def emptyReusableIndexState [BEq Key] [Hashable Key] :
    ReusableIndexState Key Value where
  index := {}
  retainedCapacity := 0

/-- Reset removes every logical entry while preserving physical capacity. -/
def resetReusableIndexState [BEq Key] [Hashable Key]
    (state : ReusableIndexState Key Value) :
    ReusableIndexState Key Value where
  index := {}
  retainedCapacity := state.retainedCapacity

def fillReusableIndexState [BEq Key] [Hashable Key]
    (state : ReusableIndexState Key Value)
    (entries : List (Key × Value)) : ReusableIndexState Key Value where
  index := compileIndex entries
  retainedCapacity := max state.retainedCapacity entries.length

def observeIndexCall [BEq Key]
    (call : IndexCall Key Value) : List (Option Value) :=
  call.queries.map fun query => sourceLookup query call.entries

def executeFreshIndexCalls [BEq Key]
    (calls : List (IndexCall Key Value)) : List (List (Option Value)) :=
  calls.map observeIndexCall

def executeReusableIndexCallsFrom [BEq Key] [Hashable Key] :
    List (IndexCall Key Value) → ReusableIndexState Key Value →
      List (List (Option Value)) × ReusableIndexState Key Value
  | [], state => ([], state)
  | call :: calls, state =>
      let completed := fillReusableIndexState
        (resetReusableIndexState state) call.entries
      let observations := call.queries.map fun query => completed.index[query]?
      let tail := executeReusableIndexCallsFrom calls
        (resetReusableIndexState completed)
      (observations :: tail.1, tail.2)

def executeReusableIndexCalls [BEq Key] [Hashable Key]
    (calls : List (IndexCall Key Value)) :
    List (List (Option Value)) × ReusableIndexState Key Value :=
  executeReusableIndexCallsFrom calls emptyReusableIndexState

/-- Reset-and-reuse has exactly the fresh lookup observations for every call;
no entry from an earlier call remains visible. -/
theorem executeReusableIndexCallsFrom_observations
    [BEq Key] [Hashable Key] [LawfulBEq Key] [LawfulHashable Key]
    (calls : List (IndexCall Key Value))
    (state : ReusableIndexState Key Value) :
    (executeReusableIndexCallsFrom calls state).1 =
      executeFreshIndexCalls calls := by
  induction calls generalizing state with
  | nil => rfl
  | cons call calls inductionHypothesis =>
      simp only [executeReusableIndexCallsFrom, executeFreshIndexCalls,
        List.map_cons]
      rw [show
        (call.queries.map fun query =>
          (fillReusableIndexState
            (resetReusableIndexState state) call.entries).index[query]?) =
          observeIndexCall call by
            simp [fillReusableIndexState, lookup_compileIndex,
              observeIndexCall]]
      rw [inductionHypothesis]
      rfl

theorem executeReusableIndexCalls_observations
    [BEq Key] [Hashable Key] [LawfulBEq Key] [LawfulHashable Key]
    (calls : List (IndexCall Key Value)) :
    (executeReusableIndexCalls calls).1 = executeFreshIndexCalls calls := by
  exact executeReusableIndexCallsFrom_observations calls
    emptyReusableIndexState

/-- Retained capacity is monotone even though every logical index is reset. -/
theorem executeReusableIndexCallsFrom_capacity_mono
    [BEq Key] [Hashable Key]
    (calls : List (IndexCall Key Value))
    (state : ReusableIndexState Key Value) :
    state.retainedCapacity ≤
      (executeReusableIndexCallsFrom calls state).2.retainedCapacity := by
  induction calls generalizing state with
  | nil => simp [executeReusableIndexCallsFrom]
  | cons call calls inductionHypothesis =>
      have tail := inductionHypothesis
        (resetReusableIndexState
          (fillReusableIndexState
            (resetReusableIndexState state) call.entries))
      simp only [resetReusableIndexState, fillReusableIndexState] at tail
      simp only [executeReusableIndexCallsFrom]
      exact Nat.le_trans
        (Nat.le_max_left state.retainedCapacity call.entries.length) tail

def compile [BEq Key] [Hashable Key] (plan : Plan)
    (source : SourceProgram Key Value) : Artifact Key Value :=
  { plan, index := compileIndex source.entries, queries := source.queries }

theorem runArtifact_compile [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (plan : Plan) (source : SourceProgram Key Value) :
    runArtifact (compile plan source) = runSource source := by
  simp [runArtifact, runSource, compile, lookup_compileIndex]

/-- A source program paired with replayable shape and uniqueness evidence. -/
structure AdmittedProgram (Key Value : Type)
    [BEq Key] [Hashable Key] where
  source : SourceProgram Key Value
  plan : Plan
  shapeAccepted : recognize source.shape = some plan
  keysDistinct :
    Mettapedia.Util.LinearHash.allDistinct
      (source.entries.map fun entry => entry.1) = true

def certify? [BEq Key] [Hashable Key]
    (source : SourceProgram Key Value) :
    Option (AdmittedProgram Key Value) :=
  match shapeAccepted : recognize source.shape with
  | none => none
  | some plan =>
      if keysDistinct : Mettapedia.Util.LinearHash.allDistinct
          (source.entries.map fun entry => entry.1) = true then
        some { source, plan, shapeAccepted, keysDistinct }
      else
        none

/-- The executable uniqueness check carries the ordinary `Nodup` invariant
needed by the semantic cardinality theorem. -/
theorem admitted_keys_nodup [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (admitted : AdmittedProgram Key Value) :
    (admitted.source.entries.map fun entry => entry.1).Nodup :=
  (Mettapedia.Util.LinearHash.allDistinct_eq_true_iff
    (admitted.source.entries.map fun entry => entry.1)).mp admitted.keysDistinct

/-- Compilation preserves every source observation. -/
def monotoneUniqueIndexRealization [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key] :
    Mettapedia.GSLT.SimpleRealization
      (AdmittedProgram Key Value) (Artifact Key Value)
      (List (Option Value)) where
  compile := fun _ admitted => compile admitted.plan admitted.source
  observeSource := fun _ admitted => runSource admitted.source
  observeArtifact := fun _ artifact => runArtifact artifact
  adequate := by
    intro _ admitted
    exact runArtifact_compile admitted.plan admitted.source

/-- The generated table contains neither dropped nor duplicate entries. -/
theorem compiled_size [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (admitted : AdmittedProgram Key Value) :
    (compile admitted.plan admitted.source).index.size =
      admitted.source.entries.length := by
  exact size_compileIndex_of_nodup admitted.source.entries
    (admitted_keys_nodup admitted)

/-! ## Abstract operation-cost certificate -/

/-- Association-list cells inspected by one source lookup. -/
def sourceLookupCost [BEq Key] (query : Key) :
    List (Key × Value) → Nat
  | [] => 0
  | (key, _) :: rest =>
      if key == query then 1 else 1 + sourceLookupCost query rest

/-- One abstract dictionary operation for a nonempty compiled table. -/
def indexedLookupOperationCost (entries : List (Key × Value)) : Nat :=
  if entries.isEmpty then 0 else 1

theorem indexedLookupOperationCost_le_sourceLookupCost [BEq Key]
    (entries : List (Key × Value)) (query : Key) :
    indexedLookupOperationCost entries ≤ sourceLookupCost query entries := by
  cases entries with
  | nil => simp [indexedLookupOperationCost, sourceLookupCost]
  | cons entry entries =>
      rcases entry with ⟨key, value⟩
      simp only [indexedLookupOperationCost, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, sourceLookupCost]
      split <;> omega

def sourceRunCost [BEq Key] (source : SourceProgram Key Value) : Nat :=
  (source.queries.map fun query =>
    sourceLookupCost query source.entries).sum

def indexedRunOperationCost (source : SourceProgram Key Value) : Nat :=
  (source.queries.map fun _ =>
    indexedLookupOperationCost source.entries).sum

theorem indexedRunOperationCost_le_sourceRunCost [BEq Key]
    (source : SourceProgram Key Value) :
    indexedRunOperationCost source ≤ sourceRunCost source := by
  unfold indexedRunOperationCost sourceRunCost
  induction source.queries with
  | nil => simp
  | cons query queries inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add
        (indexedLookupOperationCost_le_sourceLookupCost
          source.entries query)
        inductionHypothesis

/-! ## Independent witnesses and fail-closed boundary -/

private def admittedShape : TableShape :=
  { keyBits := 32, effects := [.insertFresh, .lookup] }

private def admittedPlan : Plan :=
  { keyBits := 32, effects := [.insertFresh, .lookup] }

/-- A generated parser can index immutable production identifiers. -/
private def grammarProgram : SourceProgram String Nat :=
  { shape := admittedShape
    entries := [("term", 7), ("expression", 11), ("document", 19)]
    queries := ["expression", "missing", "term"] }

example : (certify? grammarProgram).isSome = true := by
  simp [certify?, grammarProgram, admittedShape, recognize, effectSupported,
    Mettapedia.Util.LinearHash.allDistinct_eq_eraseDupsLength]
  decide

example :
    runArtifact (compile admittedPlan grammarProgram) =
      [some 11, none, some 7] := by
  rw [runArtifact_compile]
  decide

/-- A rule engine can index immutable rule identifiers with the same pass. -/
private def inferenceProgram : SourceProgram Nat String :=
  { shape := admittedShape
    entries := [(17, "premise"), (29, "eliminate"), (43, "introduce")]
    queries := [43, 17, 5] }

example :
    runArtifact (compile admittedPlan inferenceProgram) =
      [some "introduce", some "premise", none] := by
  rw [runArtifact_compile]
  decide

/-- The abstract operation model is strictly cheaper for a later key. -/
example : indexedLookupOperationCost inferenceProgram.entries = 1 ∧
    sourceLookupCost 43 inferenceProgram.entries = 3 := by
  decide

private def duplicateProgram : SourceProgram String Nat :=
  { grammarProgram with entries := [("term", 7), ("term", 99)] }

/-- Duplicate insertion is rejected rather than silently overwriting. -/
example : (certify? duplicateProgram).isSome = false := by
  simp [certify?, duplicateProgram, grammarProgram, admittedShape, recognize,
    effectSupported,
    Mettapedia.Util.LinearHash.allDistinct_eq_eraseDupsLength]
  decide

private def wideCarrierProgram : SourceProgram Nat String :=
  { inferenceProgram with shape :=
      { keyBits := 64, effects := [.insertFresh, .lookup] } }

/-- A carrier not implemented by this concrete pass is not admitted. -/
example : (certify? wideCarrierProgram).isSome = false := by
  decide

private def overwriteProgram : SourceProgram Nat String :=
  { inferenceProgram with shape :=
      { keyBits := 32, effects := [.insertFresh, .lookup, .overwrite] } }

/-- Mutable replacement falls outside the monotone-table theorem. -/
example : (certify? overwriteProgram).isSome = false := by
  decide

private def eraseProgram : SourceProgram String Nat :=
  { grammarProgram with shape :=
      { keyBits := 32, effects := [.insertFresh, .lookup, .erase] } }

/-- Deletion falls outside the monotone-table theorem. -/
example : (certify? eraseProgram).isSome = false := by
  decide

private def lookupOnlyProgram : SourceProgram String Nat :=
  { grammarProgram with shape := { keyBits := 32, effects := [.lookup] } }

/-- Both construction and observation must be locally visible to this pass. -/
example : (certify? lookupOnlyProgram).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
