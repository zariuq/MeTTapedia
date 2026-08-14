import Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

/-!
# Demand-synchronized derived index compilation

An append-and-rollback rule machine need not update a derived lookup index for
every speculative fresh insertion.  The logical entry sequence remains
authoritative.  The index records the length of the prefix it represents and
is synchronized only when a lookup observes a longer logical sequence.

The recognizer is phrased over effects rather than guest vocabulary.  It
admits fresh insertion, lookup, and suffix rollback, while rejecting overwrite
and arbitrary deletion.  The semantic model below proves that demand lookup
is exact for every lagging prefix and that an unobserved append followed by
rollback restores the prior indexed state without index maintenance.
-/

namespace Mettapedia.GSLT.LanguageDef.DemandSynchronizedIndexCompilation

open Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation

inductive Effect where
  | lookup
  | insertFresh
  | rollbackSuffix
  | overwrite
  | eraseArbitrary
  deriving DecidableEq, Repr

structure Shape where
  keyBits : Nat
  effects : List Effect
  deriving DecidableEq, Repr

structure Plan where
  keyBits : Nat
  effects : List Effect
  deriving DecidableEq, Repr

def supported : Effect → Bool
  | .lookup | .insertFresh | .rollbackSuffix => true
  | .overwrite | .eraseArbitrary => false

/-- Admit a finite-key environment exactly when its updates are fresh appends
and suffix rollback and its derived table is observed through lookup. -/
def recognize? (shape : Shape) : Option Plan :=
  if shape.keyBits == 32 &&
      shape.effects.contains .lookup &&
      shape.effects.contains .insertFresh &&
      shape.effects.contains .rollbackSuffix &&
      shape.effects.all supported then
    some { keyBits := shape.keyBits, effects := shape.effects }
  else
    none

/-- Logical entries plus the length of the prefix represented by the derived
index.  The index itself is denoted by `compileIndex (entries.take syncedLen)`;
there is no unproved representation field. -/
structure LaggingState (Key Value : Type) where
  entries : List (Key × Value)
  syncedLen : Nat
  syncedLen_le : syncedLen ≤ entries.length

def indexedPrefix (state : LaggingState Key Value) : List (Key × Value) :=
  state.entries.take state.syncedLen

def derivedIndex [BEq Key] [Hashable Key]
    (state : LaggingState Key Value) : Std.HashMap Key Value :=
  compileIndex (indexedPrefix state)

/-- A fresh append changes authoritative state but deliberately leaves the
derived prefix certificate unchanged. -/
def appendLazy (state : LaggingState Key Value) (entry : Key × Value) :
    LaggingState Key Value where
  entries := state.entries ++ [entry]
  syncedLen := state.syncedLen
  syncedLen_le := by
    exact Nat.le_trans state.syncedLen_le (by simp)

/-- Suffix rollback truncates both the logical sequence and, if necessary,
the represented prefix. -/
def rollbackSuffix (state : LaggingState Key Value) (length : Nat) :
    LaggingState Key Value where
  entries := state.entries.take length
  syncedLen := min state.syncedLen length
  syncedLen_le := by
    rw [List.length_take]
    by_cases inside : length ≤ state.entries.length
    · rw [Nat.min_eq_left inside]
      exact Nat.min_le_right _ _
    · have outside : state.entries.length ≤ length := Nat.le_of_not_ge inside
      rw [Nat.min_eq_right outside]
      exact Nat.le_trans (Nat.min_le_left _ _) state.syncedLen_le

/-- Synchronization extends the represented prefix to the complete logical
sequence. -/
def synchronize (state : LaggingState Key Value) :
    LaggingState Key Value where
  entries := state.entries
  syncedLen := state.entries.length
  syncedLen_le := Nat.le_refl _

/-- A lookup is the demand point: synchronize, then query the exact derived
index. -/
def demandLookup [BEq Key] [Hashable Key]
    (state : LaggingState Key Value) (query : Key) : Option Value :=
  (derivedIndex (synchronize state))[query]?

/-- Demand synchronization preserves the authoritative association-list
observation for every possible lagging prefix. -/
theorem demandLookup_eq_sourceLookup [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (state : LaggingState Key Value) (query : Key) :
    demandLookup state query = sourceLookup query state.entries := by
  simp [demandLookup, derivedIndex, indexedPrefix, synchronize,
    lookup_compileIndex]

/-- A lazy append followed by demand observes exactly the extended source
environment. -/
theorem demandLookup_appendLazy [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (state : LaggingState Key Value) (entry : Key × Value) (query : Key) :
    demandLookup (appendLazy state entry) query =
      sourceLookup query (state.entries ++ [entry]) := by
  exact demandLookup_eq_sourceLookup (appendLazy state entry) query

/-- Rolling an unobserved fresh append back to the old logical length restores
both the logical sequence and its prefix certificate. -/
theorem rollback_unobserved_append
    (state : LaggingState Key Value) (entry : Key × Value) :
    rollbackSuffix (appendLazy state entry) state.entries.length = state := by
  cases state with
  | mk entries syncedLen syncedLen_le =>
      simp [rollbackSuffix, appendLazy,
        Nat.min_eq_left syncedLen_le]

/-- Lookup after any suffix rollback remains exact; the truncated prefix may
lag, but the demand point repairs it before observation. -/
theorem demandLookup_rollbackSuffix [BEq Key] [Hashable Key]
    [LawfulBEq Key] [LawfulHashable Key]
    (state : LaggingState Key Value) (length : Nat) (query : Key) :
    demandLookup (rollbackSuffix state length) query =
      sourceLookup query (state.entries.take length) := by
  exact demandLookup_eq_sourceLookup (rollbackSuffix state length) query

/-! ## Abstract maintenance cost -/

/-- Eager maintenance performs one derived insertion and one derived removal
for an append that is rolled back before any lookup. -/
def eagerUnobservedAppendRollbackCost : Nat := 2

/-- Demand maintenance performs no derived operation when rollback precedes
the next lookup. -/
def lazyUnobservedAppendRollbackCost : Nat := 0

theorem lazy_unobserved_strictly_cheaper :
    lazyUnobservedAppendRollbackCost < eagerUnobservedAppendRollbackCost := by
  decide

/-! ## Independent witnesses and rejecting controls -/

private def parserShape : Shape :=
  { keyBits := 32
    effects := [.insertFresh, .lookup, .rollbackSuffix] }

private def proofSubstitutionShape : Shape :=
  { keyBits := 32
    effects := [.lookup, .insertFresh, .rollbackSuffix] }

example : (recognize? parserShape).isSome = true := by decide

example : (recognize? proofSubstitutionShape).isSome = true := by decide

private def parserState : LaggingState String Nat where
  entries := [("term", 7)]
  syncedLen := 0
  syncedLen_le := by decide

private def proofState : LaggingState Nat String where
  entries := [(3, "formula")]
  syncedLen := 0
  syncedLen_le := by decide

example : demandLookup parserState "term" = some 7 := by
  rw [demandLookup_eq_sourceLookup]
  rfl

example : demandLookup proofState 3 = some "formula" := by
  rw [demandLookup_eq_sourceLookup]
  rfl

/-- Overwrite invalidates the stable-prefix theorem and is rejected. -/
example :
    (recognize?
      { keyBits := 32
        effects := [.insertFresh, .lookup, .rollbackSuffix, .overwrite] }).isSome =
      false := by decide

/-- Arbitrary erasure is not suffix rollback and is rejected. -/
example :
    (recognize?
      { keyBits := 32
        effects := [.insertFresh, .lookup, .eraseArbitrary] }).isSome = false := by
  decide

end Mettapedia.GSLT.LanguageDef.DemandSynchronizedIndexCompilation
