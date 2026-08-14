import Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

/-!
# Canonical value-ID query compilation

A generated relational machine commonly interns immutable values once and
stores only their canonical IDs in table rows.  A later row-to-row query may
still lower a source-column ID back to its value and perform an exact lookup in
the same interning table.  This module isolates the generic optimization:
retain the already-canonical ID, while leaving dynamically supplied values on
the ordinary lookup path.

The local recognizer is the operand constructor itself.  The semantic license
is the canonical-table round trip.  No hash or numeric ID is treated as
semantic equality: the round-trip law says that the exact value lookup owns
that judgment.  A physical implementation must additionally validate the raw
column and ID bounds before entering the typed model.
-/

namespace Mettapedia.GSLT.LanguageDef.CanonicalValueIdQueryCompilation

universe uId uValue uObservation

variable {Id : Type uId} {Value : Type uValue}
  {Observation : Type uObservation}

/-- Exact value table used by an interned relational store. -/
structure CanonicalTable (Id : Type uId) (Value : Type uValue) where
  decode : Id → Value
  find? : Value → Option Id
  find_decode : ∀ id, find? (decode id) = some id

/-- A value operand is dynamic encoded data, an immutable plan literal, or an
already-interned column of a source row. -/
inductive Operand (Value : Type uValue) where
  | encoded (value : Value)
  | literal (value : Value)
  | sourceColumn (column : Nat)
  deriving DecidableEq, Repr

/-- Decidable local recognizer for the direct-ID fragment. -/
def directColumn? : Operand Value → Option Nat
  | .encoded _ => none
  | .literal _ => none
  | .sourceColumn column => some column

theorem directColumn?_eq_some_iff (operand : Operand Value) (column : Nat) :
    directColumn? operand = some column ↔
      operand = .sourceColumn column := by
  cases operand <;> simp [directColumn?]

/-- Reference interpretation: even a source column is decoded and looked up
again, matching a bytes-oriented implementation. -/
def resolveReference (table : CanonicalTable Id Value)
    (sourceRow : List Id) : Operand Value → Option Id
  | .encoded value => table.find? value
  | .literal value => table.find? value
  | .sourceColumn column => do
      let id ← sourceRow[column]?
      table.find? (table.decode id)

/-- Compiled interpretation: preserve an admitted source-column ID directly. -/
def resolveCompiled (table : CanonicalTable Id Value)
    (sourceRow : List Id) : Operand Value → Option Id
  | .encoded value => table.find? value
  | .literal value => table.find? value
  | .sourceColumn column => sourceRow[column]?

/-- The canonical round trip licenses direct source-column resolution. -/
theorem resolveCompiled_eq_resolveReference
    (table : CanonicalTable Id Value) (sourceRow : List Id)
    (operand : Operand Value) :
    resolveCompiled table sourceRow operand =
      resolveReference table sourceRow operand := by
  cases operand with
  | encoded value => rfl
  | literal value => rfl
  | sourceColumn column =>
      simp [resolveCompiled, resolveReference, table.find_decode]

/-- Resolve a mixed row left-to-right, failing closed on any absent dynamic
value or source column. -/
def resolveRow
    (resolve : Operand Value → Option Id) :
    List (Operand Value) → Option (List Id)
  | [] => some []
  | operand :: operands => do
      let id ← resolve operand
      let ids ← resolveRow resolve operands
      pure (id :: ids)

/-- Mixed direct and dynamic operands construct exactly the reference row. -/
theorem resolveRow_compiled_eq_reference
    (table : CanonicalTable Id Value) (sourceRow : List Id)
    (operands : List (Operand Value)) :
    resolveRow (resolveCompiled table sourceRow) operands =
      resolveRow (resolveReference table sourceRow) operands := by
  induction operands with
  | nil => rfl
  | cons operand operands inductionHypothesis =>
      simp only [resolveRow]
      rw [resolveCompiled_eq_resolveReference table sourceRow operand]
      rw [inductionHypothesis]

/-- Any exact-table consumer observes the same result after direct-ID
compilation.  Candidate selection, membership, copying, and receipt projection
are all instances of `observe`. -/
theorem observe_compiled_eq_reference
    (table : CanonicalTable Id Value) (sourceRow : List Id)
    (operands : List (Operand Value))
    (observe : List Id → Observation) :
    (resolveRow (resolveCompiled table sourceRow) operands).map observe =
      (resolveRow (resolveReference table sourceRow) operands).map observe := by
  rw [resolveRow_compiled_eq_reference]

/-! ## Prepared immutable literals -/

/-- Run-local companion for one generated operand.  Only an immutable literal
may carry a cached canonical ID.  `cacheCorrect` is the exact-table
certificate checked when the companion is prepared. -/
structure PreparedOperand
    (table : CanonicalTable Id Value) where
  operand : Operand Value
  cachedLiteral : Option Id
  cacheCorrect : cachedLiteral =
    match operand with
    | .literal value => table.find? value
    | _ => none

/-- Executable local recognizer and compiler for immutable literal operands. -/
def prepareOperand (table : CanonicalTable Id Value)
    (operand : Operand Value) : PreparedOperand table where
  operand := operand
  cachedLiteral :=
    match operand with
    | .literal value => table.find? value
    | _ => none
  cacheCorrect := rfl

/-- Prepared execution reads an admitted literal ID directly.  Dynamic values
and source columns retain their respective exact-lookup and direct-ID paths. -/
def resolvePrepared (table : CanonicalTable Id Value)
    (sourceRow : List Id) (prepared : PreparedOperand table) : Option Id :=
  match prepared.operand with
  | .encoded value => table.find? value
  | .literal _ => prepared.cachedLiteral
  | .sourceColumn column => sourceRow[column]?

theorem resolvePrepared_eq_reference
    (table : CanonicalTable Id Value) (sourceRow : List Id)
    (prepared : PreparedOperand table) :
    resolvePrepared table sourceRow prepared =
      resolveReference table sourceRow prepared.operand := by
  rcases prepared with ⟨operand, cached, correct⟩
  cases operand with
  | encoded value => rfl
  | literal value => simpa [resolvePrepared, resolveReference] using correct
  | sourceColumn column =>
      simp [resolvePrepared, resolveReference, table.find_decode]

/-- Resolve a precompiled operand row left-to-right. -/
def resolvePreparedRow (table : CanonicalTable Id Value)
    (sourceRow : List Id) : List (PreparedOperand table) → Option (List Id)
  | [] => some []
  | prepared :: rest => do
      let id ← resolvePrepared table sourceRow prepared
      let ids ← resolvePreparedRow table sourceRow rest
      pure (id :: ids)

/-- Preparing every immutable literal once preserves the complete mixed row. -/
theorem resolvePreparedRow_eq_reference
    (table : CanonicalTable Id Value) (sourceRow : List Id)
    (prepared : List (PreparedOperand table)) :
    resolvePreparedRow table sourceRow prepared =
      resolveRow (resolveReference table sourceRow)
        (prepared.map PreparedOperand.operand) := by
  induction prepared with
  | nil => rfl
  | cons operand rest inductionHypothesis =>
      simp only [resolvePreparedRow, List.map_cons, resolveRow]
      rw [resolvePrepared_eq_reference, inductionHypothesis]

/-- Any downstream exact-table observation is unchanged by the prepared
literal companion. -/
theorem observe_preparedRow_eq_reference
    (table : CanonicalTable Id Value) (sourceRow : List Id)
    (prepared : List (PreparedOperand table))
    (observe : List Id → Observation) :
    (resolvePreparedRow table sourceRow prepared).map observe =
      (resolveRow (resolveReference table sourceRow)
        (prepared.map PreparedOperand.operand)).map observe := by
  rw [resolvePreparedRow_eq_reference]

/-! ## Step-local positive occurrence cache -/

/-- Fresh resolution of one dynamically supplied occurrence value. -/
def resolveOccurrenceFresh (table : CanonicalTable Id Value)
    (values : List Value) (index : Nat) : Option Id :=
  match values.drop index with
  | [] => none
  | value :: _ => table.find? value

/-- A step-local cache records only successful canonical-ID resolutions.
`none` means "not cached", never "known absent".  This distinction permits
the exact table to grow between two actions in the same operation. -/
abbrev PositiveIdCache (Id : Type uId) := Nat → Option Id

/-- An empty step begins with no claims about the exact table. -/
def emptyPositiveIdCache : PositiveIdCache Id := fun _ => none

/-- Every positive cache entry must replay the current table's exact lookup. -/
def PositiveIdCache.Sound (table : CanonicalTable Id Value)
    (values : List Value) (cache : PositiveIdCache Id) : Prop :=
  ∀ index id, cache index = some id →
    resolveOccurrenceFresh table values index = some id

theorem emptyPositiveIdCache_sound
    (table : CanonicalTable Id Value) (values : List Value) :
    (emptyPositiveIdCache : PositiveIdCache Id).Sound table values := by
  intro index id cached
  simp [emptyPositiveIdCache] at cached

/-- Use a positive cache hit directly and retain exact lookup on every miss. -/
def resolveOccurrenceCached (table : CanonicalTable Id Value)
    (values : List Value) (cache : PositiveIdCache Id)
    (index : Nat) : Option Id :=
  match cache index with
  | some id => some id
  | none => resolveOccurrenceFresh table values index

theorem resolveOccurrenceCached_eq_fresh
    (table : CanonicalTable Id Value) (values : List Value)
    (cache : PositiveIdCache Id) (sound : cache.Sound table values)
    (index : Nat) :
    resolveOccurrenceCached table values cache index =
      resolveOccurrenceFresh table values index := by
  cases present : cache index with
  | none => simp [resolveOccurrenceCached, present]
  | some id =>
      simpa [resolveOccurrenceCached, present] using
        (sound index id present).symm

/-- Resolve an ordered request stream, failing closed on either a missing
occurrence index or an exact-table miss. -/
def resolveOccurrenceRequests
    (resolve : Nat → Option Id) : List Nat → Option (List Id)
  | [] => some []
  | index :: indices => do
      let id ← resolve index
      let ids ← resolveOccurrenceRequests resolve indices
      pure (id :: ids)

theorem resolveOccurrenceRequests_cached_eq_fresh
    (table : CanonicalTable Id Value) (values : List Value)
    (cache : PositiveIdCache Id) (sound : cache.Sound table values)
    (indices : List Nat) :
    resolveOccurrenceRequests
        (resolveOccurrenceCached table values cache) indices =
      resolveOccurrenceRequests
        (resolveOccurrenceFresh table values) indices := by
  induction indices with
  | nil => rfl
  | cons index indices inductionHypothesis =>
      simp only [resolveOccurrenceRequests]
      rw [resolveOccurrenceCached_eq_fresh table values cache sound index]
      rw [inductionHypothesis]

theorem observe_occurrenceRequests_cached_eq_fresh
    (table : CanonicalTable Id Value) (values : List Value)
    (cache : PositiveIdCache Id) (sound : cache.Sound table values)
    (indices : List Nat) (observe : List Id → Observation) :
    (resolveOccurrenceRequests
        (resolveOccurrenceCached table values cache) indices).map observe =
      (resolveOccurrenceRequests
        (resolveOccurrenceFresh table values) indices).map observe := by
  rw [resolveOccurrenceRequests_cached_eq_fresh
    table values cache sound indices]

/-- Remember a successful lookup.  An absent lookup leaves the cache
unchanged, which is the critical rule for a table that may grow later. -/
def rememberPositive (cache : PositiveIdCache Id) (index : Nat) :
    Option Id → PositiveIdCache Id
  | some id => Function.update cache index (some id)
  | none => cache

@[simp] theorem rememberPositive_none
    (cache : PositiveIdCache Id) (index : Nat) :
    rememberPositive cache index none = cache := rfl

@[simp] theorem rememberPositive_same_some
    (cache : PositiveIdCache Id) (index : Nat) (id : Id) :
    rememberPositive cache index (some id) index = some id := by
  simp [rememberPositive]

/-- Exact lookup followed by positive-only insertion preserves cache
soundness. -/
theorem rememberFresh_sound
    (table : CanonicalTable Id Value) (values : List Value)
    (cache : PositiveIdCache Id) (sound : cache.Sound table values)
    (index : Nat) :
    (rememberPositive cache index
      (resolveOccurrenceFresh table values index)).Sound table values := by
  intro query id cached
  cases found : resolveOccurrenceFresh table values index with
  | none =>
      exact sound query id (by simpa [rememberPositive, found] using cached)
  | some foundId =>
      by_cases same : query = index
      · subst query
        have equal : id = foundId := by
          exact (by simpa [rememberPositive, found] using cached :
            foundId = id).symm
        subst id
        exact found
      · exact sound query id (by
          simpa [rememberPositive, found, same] using cached)

/-- Append-only growth is expressed by preservation of every previously
successful exact lookup needed by this occurrence. -/
def LookupStableOn (oldTable newTable : CanonicalTable Id Value)
    (values : List Value) : Prop :=
  ∀ index id,
    resolveOccurrenceFresh oldTable values index = some id →
      resolveOccurrenceFresh newTable values index = some id

theorem PositiveIdCache.Sound.mono
    (oldTable newTable : CanonicalTable Id Value) (values : List Value)
    (cache : PositiveIdCache Id) (sound : cache.Sound oldTable values)
    (stable : LookupStableOn oldTable newTable values) :
    cache.Sound newTable values := by
  intro index id cached
  exact stable index id (sound index id cached)

/-! ### Lookup cost -/

/-- A fresh dynamic occurrence performs one exact-table lookup. -/
def occurrenceFreshLookupCost (_index : Nat) : Nat := 1

/-- A positive hit performs no exact-table lookup; a miss performs one. -/
def occurrenceCachedLookupCost
    (cache : PositiveIdCache Id) (index : Nat) : Nat :=
  if (cache index).isSome then 0 else 1

theorem occurrenceCachedLookupCost_le_fresh
    (cache : PositiveIdCache Id) (index : Nat) :
    occurrenceCachedLookupCost cache index ≤
      occurrenceFreshLookupCost index := by
  cases present : cache index <;>
    simp [occurrenceCachedLookupCost, occurrenceFreshLookupCost, present]

theorem occurrenceRememberedLookupCost_eq_zero
    (table : CanonicalTable Id Value) (values : List Value)
    (cache : PositiveIdCache Id) (index : Nat) (id : Id)
    (found : resolveOccurrenceFresh table values index = some id) :
    occurrenceCachedLookupCost
        (rememberPositive cache index
          (resolveOccurrenceFresh table values index)) index = 0 := by
  simp [occurrenceCachedLookupCost, found]

/-- Repeated fresh resolution performs one exact lookup per request. -/
def repeatedOccurrenceFreshLookups (requests : Nat) : Nat := requests

/-- Positive-only caching performs one lookup for a nonempty repetition of
the same present occurrence and then reuses its canonical ID. -/
def repeatedOccurrenceCachedLookups (requests : Nat) : Nat :=
  if requests = 0 then 0 else 1

theorem repeatedOccurrenceCachedLookups_le_fresh (requests : Nat) :
    repeatedOccurrenceCachedLookups requests ≤
      repeatedOccurrenceFreshLookups requests := by
  cases requests <;>
    simp [repeatedOccurrenceCachedLookups,
      repeatedOccurrenceFreshLookups]

theorem repeatedOccurrenceCachedLookups_lt_fresh
    (requests : Nat) (repeated : 2 ≤ requests) :
    repeatedOccurrenceCachedLookups requests <
      repeatedOccurrenceFreshLookups requests := by
  have nonzero : requests ≠ 0 := by omega
  simp [repeatedOccurrenceCachedLookups,
    repeatedOccurrenceFreshLookups, nonzero]
  omega

/-! ## Physical bounds validation -/

/-- Raw `u32`-style IDs enter the typed carrier only after both the column and
the value ID are in range. -/
def resolvePhysicalSourceColumn?
    (valueCount : Nat) (sourceRow : List Nat) (column : Nat) : Option Nat := do
  let id ← sourceRow[column]?
  if id < valueCount then some id else none

theorem resolvePhysicalSourceColumn?_sound
    (valueCount : Nat) (sourceRow : List Nat) (column id : Nat)
    (accepted :
      resolvePhysicalSourceColumn? valueCount sourceRow column = some id) :
    sourceRow[column]? = some id ∧ id < valueCount := by
  cases present : sourceRow[column]? with
  | none => simp [resolvePhysicalSourceColumn?, present] at accepted
  | some found =>
      by_cases bounded : found < valueCount
      · simp [resolvePhysicalSourceColumn?, present, bounded] at accepted
        subst id
        exact ⟨rfl, bounded⟩
      · simp [resolvePhysicalSourceColumn?, present, bounded] at accepted

theorem resolvePhysicalSourceColumn?_complete
    (valueCount : Nat) (sourceRow : List Nat) (column id : Nat)
    (present : sourceRow[column]? = some id) (bounded : id < valueCount) :
    resolvePhysicalSourceColumn? valueCount sourceRow column = some id := by
  simp [resolvePhysicalSourceColumn?, present, bounded]

/-! ## Abstract operation cost -/

/-- Reference cost counts a source-column decode and exact re-lookup. -/
def referenceResolutionCost : Operand Value → Nat
  | .encoded _ => 1
  | .literal _ => 1
  | .sourceColumn _ => 2

/-- Compiled cost counts one dynamic lookup or one checked direct read. -/
def compiledResolutionCost : Operand Value → Nat
  | .encoded _ => 1
  | .literal _ => 1
  | .sourceColumn _ => 1

theorem compiledResolutionCost_le_referenceResolutionCost
    (operand : Operand Value) :
    compiledResolutionCost operand ≤ referenceResolutionCost operand := by
  cases operand <;> simp [compiledResolutionCost, referenceResolutionCost]

theorem sourceColumn_compiledResolutionCost_lt_referenceResolutionCost
    (column : Nat) :
    compiledResolutionCost (Operand.sourceColumn column : Operand Value) <
      referenceResolutionCost
        (Operand.sourceColumn column : Operand Value) := by
  simp [compiledResolutionCost, referenceResolutionCost]

/-- Repeated execution performs one exact value-table lookup per immutable
literal occurrence in the reference machine. -/
def repeatedLiteralReferenceLookups (executions : Nat) : Nat := executions

/-- A prepared literal performs one exact lookup for a nonempty run and then
reuses the certified ID. -/
def repeatedLiteralPreparedLookups (executions : Nat) : Nat :=
  if executions = 0 then 0 else 1

theorem repeatedLiteralPreparedLookups_le_reference
    (executions : Nat) :
    repeatedLiteralPreparedLookups executions ≤
      repeatedLiteralReferenceLookups executions := by
  cases executions <;>
    simp [repeatedLiteralPreparedLookups,
      repeatedLiteralReferenceLookups]

theorem repeatedLiteralPreparedLookups_lt_reference
    (executions : Nat) (repeated : 2 ≤ executions) :
    repeatedLiteralPreparedLookups executions <
      repeatedLiteralReferenceLookups executions := by
  have nonzero : executions ≠ 0 := by omega
  simp [repeatedLiteralPreparedLookups,
    repeatedLiteralReferenceLookups, nonzero]
  omega

/-! ## Independent proof-row and equation-row witnesses -/

inductive WitnessValue where
  | assertion
  | hypothesis
  | equationHead
  | equationBody
  | hornClause
  | missing
  deriving DecidableEq, Repr

inductive WitnessId where
  | assertionId
  | hypothesisId
  | equationHeadId
  | equationBodyId
  | hornClauseId
  deriving DecidableEq, Repr

def witnessDecode : WitnessId → WitnessValue
  | .assertionId => .assertion
  | .hypothesisId => .hypothesis
  | .equationHeadId => .equationHead
  | .equationBodyId => .equationBody
  | .hornClauseId => .hornClause

def witnessFind? : WitnessValue → Option WitnessId
  | .assertion => some .assertionId
  | .hypothesis => some .hypothesisId
  | .equationHead => some .equationHeadId
  | .equationBody => some .equationBodyId
  | .hornClause => some .hornClauseId
  | .missing => none

def witnessTable : CanonicalTable WitnessId WitnessValue where
  decode := witnessDecode
  find? := witnessFind?
  find_decode := by intro id; cases id <;> rfl

/-- A Metamath-shaped assertion/hypothesis row uses both a direct source
column and an encoded value. -/
example :
    resolveRow
      (resolveCompiled witnessTable [.assertionId, .hypothesisId])
      [.sourceColumn 0, .encoded .hypothesis] =
        some [.assertionId, .hypothesisId] := by decide

/-- A MeTTa-shaped equation row preserves both canonical source columns. -/
example :
    resolveRow
      (resolveCompiled witnessTable [.equationHeadId, .equationBodyId])
      [.sourceColumn 0, .sourceColumn 1] =
        some [.equationHeadId, .equationBodyId] := by decide

/-- A MeTTa equation plan prepares its immutable head symbol once. -/
example :
    resolvePrepared witnessTable []
      (prepareOperand witnessTable (.literal .equationHead)) =
        some .equationHeadId := by decide

/-- A finite Horn plan uses the same immutable-literal preparation without
sharing Metamath or MeTTa syntax. -/
example :
    resolvePrepared witnessTable []
      (prepareOperand witnessTable (.literal .hornClause)) =
        some .hornClauseId := by decide

/-- A Metamath-shaped operation resolves one label once and reuses its
positive ID across later generated actions. -/
example :
    let values : List WitnessValue := [.assertion, .hypothesis]
    let cache := rememberPositive
      (emptyPositiveIdCache : PositiveIdCache WitnessId) 0
      (resolveOccurrenceFresh witnessTable values 0)
    resolveOccurrenceRequests
      (resolveOccurrenceCached witnessTable values cache) [0, 0] =
        some [.assertionId, .assertionId] := by decide

/-- A MeTTa equation operation uses the same step-local carrier for a dynamic
equation argument. -/
example :
    let values : List WitnessValue := [.equationHead, .equationBody]
    let cache := rememberPositive
      (emptyPositiveIdCache : PositiveIdCache WitnessId) 1
      (resolveOccurrenceFresh witnessTable values 1)
    resolveOccurrenceCached witnessTable values cache 1 =
      some .equationBodyId := by decide

/-- A finite-Horn operation is an independent witness of the same positive
occurrence cache. -/
example :
    let values : List WitnessValue := [.hornClause]
    let cache := rememberPositive
      (emptyPositiveIdCache : PositiveIdCache WitnessId) 0
      (resolveOccurrenceFresh witnessTable values 0)
    resolveOccurrenceCached witnessTable values cache 0 =
      some .hornClauseId := by decide

/-- A missing occurrence is not memoized as a negative table fact. -/
example :
    let cache := rememberPositive
      (emptyPositiveIdCache : PositiveIdCache WitnessId) 1
      (resolveOccurrenceFresh witnessTable [.assertion] 1)
    cache 1 = none := by decide

/-- A missing source column fails closed. -/
example :
    resolveCompiled witnessTable [.assertionId]
      (.sourceColumn 1) = none := by decide

/-- A raw value ID outside the physical table is rejected before entering the
typed canonical carrier. -/
example : resolvePhysicalSourceColumn? 4 [4] 0 = none := by decide

/-- A literal absent from the certified exact table fails closed. -/
example :
    resolvePrepared witnessTable []
      (prepareOperand witnessTable (.literal .missing)) = none := by decide

end Mettapedia.GSLT.LanguageDef.CanonicalValueIdQueryCompilation
