import Mettapedia.Languages.MeTTa.PrimeNeedReferenceSemantics
import Mathlib.Tactic

/-!
# Persistent bounded index for Prime Need heaps

The reference Need heap deliberately exposes an extensional finite-map view
and a persistent semantic update spine.  A native snapshot may additionally
carry this immutable radix index from stable cell keys to the newest frame.
The index is derived: lookup agrees with the semantic heap, while the update
spine remains the authority for lineage, ancestry, promotion, and replay.

Keys have exactly sixteen hexadecimal digits, matching an internal 64-bit
cell key.  Every successful indexed lookup therefore follows at most sixteen
edges and examines one terminal node.  Updates path-copy the same bounded
route, so sibling snapshots share all unaffected subtries.
-/

namespace Mettapedia.Languages.MeTTa.PrimeNeedHeapIndex

open PrimeNeedReference

abbrev Digit := Fin 16

/-- A 64-bit internal key represented without hashing or collisions. -/
abbrev Key := { path : List Digit // path.length = 16 }

/-- A persistent radix trie.  `value` permits the generic list-key proofs;
Prime's fixed-width keys place values only at depth sixteen. -/
inductive Trie (α : Type*) where
  | node (value : Option α) (children : Digit → Option (Trie α))

namespace Trie

variable {α : Type*}

def empty : Trie α :=
  .node none (fun _ => none)

def lookup : Trie α → List Digit → Option α
  | .node value _, [] => value
  | .node _ children, digit :: rest =>
      match children digit with
      | none => none
      | some child => child.lookup rest

def insert : Trie α → List Digit → α → Trie α
  | .node _ children, [], value =>
      .node (some value) children
  | .node here children, digit :: rest, value =>
      let child := (children digit).getD empty
      .node here
        (Function.update children digit
          (some (child.insert rest value)))

@[simp] theorem lookup_empty (path : List Digit) :
    (empty : Trie α).lookup path = none := by
  cases path <;> rfl

@[simp] theorem lookup_insert_self
    (trie : Trie α) (path : List Digit) (value : α) :
    (trie.insert path value).lookup path = some value := by
  induction path generalizing trie with
  | nil =>
      cases trie
      rfl
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          simp only [insert, lookup, Function.update_self]
          exact ih _

theorem lookup_insert_other
    (trie : Trie α) {inserted queried : List Digit} (value : α)
    (hDifferent : queried ≠ inserted) :
    (trie.insert inserted value).lookup queried = trie.lookup queried := by
  induction inserted generalizing trie queried with
  | nil =>
      cases queried with
      | nil => exact False.elim (hDifferent rfl)
      | cons digit rest =>
          cases trie
          rfl
  | cons insertedDigit insertedRest ih =>
      cases queried with
      | nil =>
          cases trie
          rfl
      | cons queriedDigit queriedRest =>
          cases trie with
          | node here children =>
              by_cases hDigit : queriedDigit = insertedDigit
              · subst queriedDigit
                have hRest : queriedRest ≠ insertedRest := by
                  intro hEqual
                  exact hDifferent (congrArg (List.cons insertedDigit) hEqual)
                cases hChild : children insertedDigit with
                | none =>
                    simp [insert, lookup, hChild, ih empty hRest]
                | some child =>
                    simp [insert, lookup, hChild, ih child hRest]
              · simp [insert, lookup, Function.update, hDigit]

/-- Lookup work counts node examinations and can stop at an absent child. -/
def lookupSteps : Trie α → List Digit → Nat
  | .node _ _, [] => 1
  | .node _ children, digit :: rest =>
      1 +
        match children digit with
        | none => 0
        | some child => child.lookupSteps rest

theorem lookupSteps_le (trie : Trie α) (path : List Digit) :
    trie.lookupSteps path ≤ path.length + 1 := by
  induction path generalizing trie with
  | nil =>
      cases trie
      simp [lookupSteps]
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          cases hChild : children digit with
          | none => simp [lookupSteps, hChild]
          | some child =>
              simp only [lookupSteps, hChild, List.length_cons]
              have hBound := ih child
              omega

theorem lookupSteps_insert_self
    (trie : Trie α) (path : List Digit) (value : α) :
    (trie.insert path value).lookupSteps path = path.length + 1 := by
  induction path generalizing trie with
  | nil =>
      cases trie
      rfl
  | cons digit rest ih =>
      cases trie with
      | node here children =>
          simp only [insert, lookupSteps, Function.update_self,
            List.length_cons]
          rw [ih]
          omega

def lookupKey (trie : Trie α) (key : Key) : Option α :=
  trie.lookup key.1

def insertKey (trie : Trie α) (key : Key) (value : α) : Trie α :=
  trie.insert key.1 value

@[simp] theorem lookupKey_insert_self
    (trie : Trie α) (key : Key) (value : α) :
    (trie.insertKey key value).lookupKey key = some value :=
  lookup_insert_self trie key.1 value

theorem lookupKey_insert_other
    (trie : Trie α) {inserted queried : Key} (value : α)
    (hDifferent : queried ≠ inserted) :
    (trie.insertKey inserted value).lookupKey queried =
      trie.lookupKey queried := by
  apply lookup_insert_other
  intro hPaths
  exact hDifferent (Subtype.ext hPaths)

theorem lookupKey_steps_le (trie : Trie α) (key : Key) :
    trie.lookupSteps key.1 ≤ 17 := by
  simpa [key.2] using lookupSteps_le trie key.1

theorem lookupKey_insert_steps
    (trie : Trie α) (key : Key) (value : α) :
    (trie.insertKey key value).lookupSteps key.1 = 17 := by
  simpa [insertKey, key.2] using lookupSteps_insert_self trie key.1 value

end Trie

section HeapRefinement

variable {Origin Value StableFault : Type*}

/-- The native key assignment must be injective within one heap session. -/
def Consistent
    (keyOf : CellId → Key)
    (heap : Heap Origin Value StableFault)
    (index : Trie (CellRecord Origin Value StableFault)) : Prop :=
  ∀ cell, index.lookupKey (keyOf cell) = heap.lookup cell

theorem lookup_refines
    {keyOf : CellId → Key}
    {heap : Heap Origin Value StableFault}
    {index : Trie (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap index)
    (cell : CellId) :
    index.lookupKey (keyOf cell) = heap.lookup cell :=
  consistent cell

theorem setKnownCache_preserves_consistency
    {keyOf : CellId → Key}
    (keyInjective : Function.Injective keyOf)
    {heap : Heap Origin Value StableFault}
    {index : Trie (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap index)
    (cell : CellId) (record : CellRecord Origin Value StableFault)
    (state : Cache Value StableFault) :
    Consistent keyOf
      (heap.setKnownCache cell record state)
      (index.insertKey (keyOf cell) { record with cache := state }) := by
  intro other
  by_cases hCell : other = cell
  · subst other
    simp
  · rw [Trie.lookupKey_insert_other]
    · rw [Heap.setKnownCache_preserves_other _ _ _ hCell]
      exact consistent other
    · exact fun hKey => hCell (keyInjective hKey)

theorem allocate_preserves_consistency
    {keyOf : CellId → Key}
    (keyInjective : Function.Injective keyOf)
    {heap next : Heap Origin Value StableFault}
    {index : Trie (CellRecord Origin Value StableFault)}
    (consistent : Consistent keyOf heap index)
    {cell : CellId} {origin : Origin}
    (allocated : heap.allocate? cell origin = some next) :
    Consistent keyOf next
      (index.insertKey (keyOf cell)
        { origin := origin, cache := Cache.suspended }) := by
  intro other
  by_cases hCell : other = cell
  · subst other
    rw [Trie.lookupKey_insert_self]
    exact (Heap.allocate?_lookup_same allocated).symm
  · rw [Trie.lookupKey_insert_other]
    · rw [Heap.allocate?_preserves_other allocated hCell]
      exact consistent other
    · exact fun hKey => hCell (keyInjective hKey)

end HeapRefinement

end Mettapedia.Languages.MeTTa.PrimeNeedHeapIndex
