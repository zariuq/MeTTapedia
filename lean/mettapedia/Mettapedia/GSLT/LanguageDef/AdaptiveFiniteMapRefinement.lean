import Mathlib.Data.List.Basic
import Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation

/-!
# Adaptive finite-map refinement

This module separates the meaning of a finite key map and an occurrence bag
from an allocation-sensitive representation which stores zero and one element
inline and promotes to an external collection only when a second distinct key
or occurrence arrives.

The representation is generic in keys and values.  In particular, it does not
depend on a MeTTa dialect, a search strategy, or the syntax of discrimination
coordinates.  Its exactness theorems connect it to the abstract bucket index
used by `FiniteRuleIndexCompilation`, including source order and multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AdaptiveFiniteMapRefinement

universe uKey uValue uRule uResult

variable {Key : Type uKey} {Value : Type uValue}

/-! ## Logical finite maps -/

/-- First-match lookup in the authoritative association-list meaning. -/
def lookupEntries [DecidableEq Key] (query : Key) :
    List (Key × Value) → Option Value
  | [] => none
  | (key, value) :: rest =>
      if query = key then some value else lookupEntries query rest

/-- Add a previously absent key, leaving an existing binding unchanged. -/
def logicalEnsure [DecidableEq Key]
    (key : Key) (value : Value) (entries : List (Key × Value)) :
    List (Key × Value) :=
  if (lookupEntries key entries).isSome then entries
  else entries ++ [(key, value)]

@[simp] theorem logicalEnsure_of_present [DecidableEq Key]
    (key : Key) (value : Value) (entries : List (Key × Value))
    (present : (lookupEntries key entries).isSome = true) :
    logicalEnsure key value entries = entries := by
  simp [logicalEnsure, present]

@[simp] theorem logicalEnsure_of_absent [DecidableEq Key]
    (key : Key) (value : Value) (entries : List (Key × Value))
    (absent : (lookupEntries key entries).isSome = false) :
    logicalEnsure key value entries = entries ++ [(key, value)] := by
  simp [logicalEnsure, absent]

/-! ## Inline-zero/one finite-map realization -/

/-- A physical finite-map shape.  `many` is deliberately abstract about the
concrete external map: a vector, hash table, radix table, or trie node may
realize the same authoritative entry sequence. -/
inductive AdaptiveKeyMap (Key : Type uKey) (Value : Type uValue) where
  | empty
  | singleton (key : Key) (value : Value)
  | many (entries : List (Key × Value))
deriving DecidableEq, Repr

namespace AdaptiveKeyMap

/-- Erase the allocation shape to its authoritative finite-map meaning. -/
def entries : AdaptiveKeyMap Key Value → List (Key × Value)
  | .empty => []
  | .singleton key value => [(key, value)]
  | .many stored => stored

/-- Direct physical lookup, without defining the implementation by erasure. -/
def lookup [DecidableEq Key] (query : Key) :
    AdaptiveKeyMap Key Value → Option Value
  | .empty => none
  | .singleton key value =>
      if query = key then some value else none
  | .many stored => lookupEntries query stored

/-- Canonical packing uses no external collection for zero or one entry. -/
def pack : List (Key × Value) → AdaptiveKeyMap Key Value
  | [] => .empty
  | [entry] => .singleton entry.1 entry.2
  | first :: second :: rest => .many (first :: second :: rest)

/-- Number of external collection blocks in the abstract allocation model. -/
def sideBlocks : AdaptiveKeyMap Key Value → Nat
  | .empty | .singleton _ _ => 0
  | .many _ => 1

/-- Fetch an existing value or install a supplied value for an absent key. -/
def ensure [DecidableEq Key]
    (key : Key) (value : Value) :
    AdaptiveKeyMap Key Value → AdaptiveKeyMap Key Value
  | .empty => .singleton key value
  | .singleton stored old =>
      if key = stored then .singleton stored old
      else .many [(stored, old), (key, value)]
  | .many stored =>
      if (lookupEntries key stored).isSome then .many stored
      else .many (stored ++ [(key, value)])

/-- Physical lookup has exactly the association-list meaning. -/
theorem lookup_eq_lookupEntries [DecidableEq Key]
    (query : Key) (map : AdaptiveKeyMap Key Value) :
    lookup query map = lookupEntries query map.entries := by
  cases map <;> rfl

/-- Packing changes only allocation shape. -/
@[simp] theorem entries_pack (stored : List (Key × Value)) :
    (pack stored).entries = stored := by
  cases stored with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second tail => rfl

/-- Lookup commutes with canonical packing. -/
@[simp] theorem lookup_pack [DecidableEq Key]
    (query : Key) (stored : List (Key × Value)) :
    lookup query (pack stored) = lookupEntries query stored := by
  rw [lookup_eq_lookupEntries, entries_pack]

/-- Any observer of lookup results is natural across packing. -/
theorem observe_pack [DecidableEq Key]
    {Result : Type uResult} (observe : Option Value → Result) (query : Key)
    (stored : List (Key × Value)) :
    observe (lookup query (pack stored)) =
      observe (lookupEntries query stored) := by
  rw [lookup_pack]

/-- The allocation-sensitive `ensure` operation refines logical insertion
without overwriting an existing value. -/
theorem entries_ensure [DecidableEq Key]
    (key : Key) (value : Value) (map : AdaptiveKeyMap Key Value) :
    (ensure key value map).entries =
      logicalEnsure key value map.entries := by
  cases map with
  | empty => simp [ensure, entries, logicalEnsure, lookupEntries]
  | singleton stored old =>
      by_cases same : key = stored
      · simp [ensure, entries, logicalEnsure, lookupEntries, same]
      · simp [ensure, entries, logicalEnsure, lookupEntries, same]
  | many stored =>
      by_cases present : (lookupEntries key stored).isSome = true
      · simp [ensure, entries, logicalEnsure, present]
      · have absent : (lookupEntries key stored).isSome = false := by
          cases valuePresent : (lookupEntries key stored).isSome <;>
            simp_all
        simp [ensure, entries, logicalEnsure, absent]

/-- Lookup after a physical ensure is therefore exactly lookup after the
authoritative logical ensure. -/
theorem lookup_ensure_exact [DecidableEq Key]
    (query key : Key) (value : Value)
    (map : AdaptiveKeyMap Key Value) :
    lookup query (ensure key value map) =
      lookupEntries query (logicalEnsure key value map.entries) := by
  rw [lookup_eq_lookupEntries, entries_ensure]

/-! ### Shape and overwrite canaries -/

example :
    ensure 7 "first" (empty : AdaptiveKeyMap Nat String) =
      singleton 7 "first" := by
  rfl

example :
    ensure 8 "second" (singleton 7 "first") =
      many [(7, "first"), (8, "second")] := by
  decide

/-- Re-ensuring an existing key neither overwrites it nor promotes it. -/
example :
    ensure 7 "replacement" (singleton 7 "first") =
      singleton 7 "first" := by
  decide

/-- A missing lookup remains observably absent. -/
example :
    lookup 9 (singleton 7 "first") = none := by
  decide

end AdaptiveKeyMap

/-! ## Inline-zero/one occurrence bags -/

/-- Occurrences are a bag with stable enumeration order; duplicates are data. -/
inductive AdaptiveOccurrenceBag (Occurrence : Type uValue) where
  | empty
  | singleton (occurrence : Occurrence)
  | many (occurrences : List Occurrence)
deriving DecidableEq, Repr

namespace AdaptiveOccurrenceBag

/-- Direct observation of every stored occurrence. -/
def observe : AdaptiveOccurrenceBag Value → List Value
  | .empty => []
  | .singleton occurrence => [occurrence]
  | .many occurrences => occurrences

/-- Append one occurrence, promoting only on the second occurrence. -/
def push (occurrence : Value) :
    AdaptiveOccurrenceBag Value → AdaptiveOccurrenceBag Value
  | .empty => .singleton occurrence
  | .singleton first => .many [first, occurrence]
  | .many occurrences => .many (occurrences ++ [occurrence])

/-- Number of external occurrence-vector blocks in the allocation model. -/
def sideBlocks : AdaptiveOccurrenceBag Value → Nat
  | .empty | .singleton _ => 0
  | .many _ => 1

/-- Promotion preserves exact occurrence order and multiplicity. -/
@[simp] theorem observe_push (occurrence : Value)
    (bag : AdaptiveOccurrenceBag Value) :
    observe (push occurrence bag) = observe bag ++ [occurrence] := by
  cases bag <;> simp [push, observe]

/-- The first occurrence requires no side block. -/
example :
    sideBlocks (push 5 (empty : AdaptiveOccurrenceBag Nat)) = 0 := by
  rfl

/-- The second occurrence promotes exactly once. -/
example :
    sideBlocks (push 7 (singleton 5)) = 1 := by
  rfl

/-- Duplicate occurrences survive promotion. -/
example :
    observe (push 5 (singleton 5)) = [5, 5] := by
  rfl

/-- A set-like replacement would be observably wrong. -/
example :
    observe (push 5 (singleton 5)) ≠ [5] := by
  decide

end AdaptiveOccurrenceBag

/-! ## Bridge to certified finite rule indexing -/

namespace BucketBridge

open Mettapedia.GSLT.LanguageDef.FiniteRuleIndexCompilation

variable {Rule : Type uRule}

/-- Physically adaptive storage for the abstract compiled bucket index. -/
abbrev AdaptiveBucketIndex (Key : Type uKey) (Rule : Type uRule) :=
  AdaptiveKeyMap Key (List Rule)

/-- Lower an abstract bucket index into its canonical adaptive shape. -/
def fromBucketIndex (index : BucketIndex Key Rule) :
    AdaptiveBucketIndex Key Rule :=
  AdaptiveKeyMap.pack index

/-- Direct adaptive-bucket lookup. -/
def lookup [DecidableEq Key] (query : Key)
    (index : AdaptiveBucketIndex Key Rule) : List Rule :=
  (AdaptiveKeyMap.lookup query index).getD []

theorem lookupEntries_eq_bucketLookup [DecidableEq Key]
    (query : Key) (index : BucketIndex Key Rule) :
    (lookupEntries query index).getD [] =
      FiniteRuleIndexCompilation.lookup query index := by
  induction index with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      obtain ⟨key, rules⟩ := entry
      by_cases same : query = key
      · simp [lookupEntries, FiniteRuleIndexCompilation.lookup, same]
      · simp [lookupEntries, FiniteRuleIndexCompilation.lookup, same,
          inductionHypothesis]

/-- Adaptive lowering preserves exact bucket lookup. -/
theorem lookup_fromBucketIndex [DecidableEq Key]
    (query : Key) (index : BucketIndex Key Rule) :
    lookup query (fromBucketIndex index) =
      FiniteRuleIndexCompilation.lookup query index := by
  unfold lookup fromBucketIndex
  rw [AdaptiveKeyMap.lookup_pack]
  exact lookupEntries_eq_bucketLookup query index

/-- Adaptive lowering of an admitted program preserves the source scan,
including source order and duplicate rule occurrences. -/
theorem lookup_admitted_eq_sourceCandidates [DecidableEq Key]
    (keyOf? : Rule → Option Key)
    (program : AdmittedProgram Key Rule keyOf?) (query : Key) :
    lookup query (fromBucketIndex program.compiled) =
      sourceCandidates keyOf? program.source query := by
  rw [lookup_fromBucketIndex]
  exact lookup_compile?_eq_sourceCandidates keyOf? program.source
    program.compiled program.compile_eq query

/-- Observers cannot distinguish the adaptive lowering from the abstract
compiled bucket index. -/
theorem observer_naturality [DecidableEq Key]
    {Result : Type uResult} (observe : List Rule → Result)
    (query : Key) (index : BucketIndex Key Rule) :
    observe (lookup query (fromBucketIndex index)) =
      observe (FiniteRuleIndexCompilation.lookup query index) := by
  rw [lookup_fromBucketIndex]

/-! ### Cross-domain and rejection canaries -/

private inductive Pattern where
  | application (head : String) (arity : Nat)
  | dynamic
deriving DecidableEq

private structure RuleExample where
  name : String
  pattern : Pattern
deriving DecidableEq

private def keyOf? (rule : RuleExample) : Option (String × Nat) :=
  match rule.pattern with
  | .application head arity => some (head, arity)
  | .dynamic => none

private def source : List RuleExample :=
  [{ name := "edge-left", pattern := .application "edge" 2 },
   { name := "node", pattern := .application "node" 1 },
   { name := "edge-right", pattern := .application "edge" 2 }]

/-- A two-key program promotes to external storage while retaining both edge
occurrences in authored order. -/
example :
    ∃ program : AdmittedProgram (String × Nat) RuleExample keyOf?,
      lookup ("edge", 2) (fromBucketIndex program.compiled) =
        [source[0], source[2]] := by
  refine ⟨{
    source := source
    compiled := [(("edge", 2), [source[0], source[2]]),
      (("node", 1), [source[1]])]
    compile_eq := ?_ }, ?_⟩
  · decide
  · decide

/-- A source with no key is still rejected before physical lowering. -/
example :
    (admitProgram keyOf?
      [{ name := "unknown", pattern := .dynamic }]).isNone = true := by
  decide

end BucketBridge

#print axioms AdaptiveKeyMap.lookup_eq_lookupEntries
#print axioms AdaptiveKeyMap.entries_ensure
#print axioms AdaptiveKeyMap.lookup_ensure_exact
#print axioms AdaptiveOccurrenceBag.observe_push
#print axioms BucketBridge.lookup_fromBucketIndex
#print axioms BucketBridge.lookup_admitted_eq_sourceCandidates
#print axioms BucketBridge.observer_naturality

end Mettapedia.GSLT.LanguageDef.AdaptiveFiniteMapRefinement
