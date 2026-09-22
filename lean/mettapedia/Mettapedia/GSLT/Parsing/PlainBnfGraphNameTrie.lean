import Mathlib.Data.List.Basic

/-!
# Sparse character-trie operations for BNF graph names

Names are scalar lists; terminal payloads may have any type. Edges are searched by structural equality
in their stored order. Insertion updates the first matching edge, or appends a
new edge, and retains an existing terminal payload. The separate `put`
operation replaces that payload while preserving the same edge discipline.
These factor the lookup/first-insertion operations in
`plain_bnf_graph_index_v1.metta` and the discovery source's overwrite operation.

Only decidable scalar equality is required. The default natural-number
instance remains available for reader-produced names; the same operations and
proofs also cover signed Integer keys admitted by the structured grammar API.
No normalization, Unicode check, or change of the runtime wire is performed.

The theorem concerns these independent finite algorithms. It does not claim
an authored-rule execution bridge, generated-program correspondence, a runtime
speedup, or an optimal trie representation.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGraphNameTrie

abbrev Name := List Nat

inductive Trie (Payload : Type u) (Scalar : Type := Nat) where
  | empty
  | node (value : Option Payload) (edges : List (Scalar × Trie Payload Scalar))
  deriving Repr

variable {Payload : Type u} {Scalar : Type}

def valueAt : Trie Payload Scalar → Option Payload
  | .empty => none
  | .node value _ => value

def edgesOf : Trie Payload Scalar → List (Scalar × Trie Payload Scalar)
  | .empty => []
  | .node _ edges => edges

variable [DecidableEq Scalar]

def childFor (scalar : Scalar) : List (Scalar × Trie Payload Scalar) → Trie Payload Scalar
  | [] => .empty
  | (stored, child) :: rest => if scalar = stored then child else childFor scalar rest

def updateChild (scalar : Scalar) (update : Trie Payload Scalar → Trie Payload Scalar) :
    List (Scalar × Trie Payload Scalar) → List (Scalar × Trie Payload Scalar)
  | [] => [(scalar, update .empty)]
  | (stored, child) :: rest =>
      if scalar = stored then (stored, update child) :: rest
      else (stored, child) :: updateChild scalar update rest

def lookup : List Scalar → Trie Payload Scalar → Option Payload
  | [], trie => valueAt trie
  | scalar :: rest, trie => lookup rest (childFor scalar (edgesOf trie))

def insertFirst : List Scalar → Payload → Trie Payload Scalar → Trie Payload Scalar
  | [], value, trie => .node ((valueAt trie).or (some value)) (edgesOf trie)
  | scalar :: rest, value, trie =>
      .node (valueAt trie) (updateChild scalar (insertFirst rest value) (edgesOf trie))

/-- Replace the terminal value, retaining every nonselected edge and payload.
Unlike `insertFirst`, this is the overwrite used for reverse-reference buckets. -/
def put : List Scalar → Payload → Trie Payload Scalar → Trie Payload Scalar
  | [], value, trie => .node (some value) (edgesOf trie)
  | scalar :: rest, value, trie =>
      .node (valueAt trie) (updateChild scalar (put rest value) (edgesOf trie))

@[simp] theorem lookup_empty (name : List Scalar) :
    lookup name (.empty : Trie Payload Scalar) = none := by
  induction name with
  | nil => rfl
  | cons scalar rest ih => exact ih

/-- One source edge is updated: the first equal scalar, or a fresh appended
edge. No uniqueness or ordering assumption on the edge list is required. -/
theorem childFor_updateChild (query scalar : Scalar)
    (update : Trie Payload Scalar → Trie Payload Scalar)
    (edges : List (Scalar × Trie Payload Scalar)) :
    childFor query (updateChild scalar update edges) =
      if query = scalar then update (childFor scalar edges) else childFor query edges := by
  induction edges with
  | nil => simp [updateChild, childFor]
  | cons edge rest ih =>
      rcases edge with ⟨stored, child⟩
      by_cases insertedHere : scalar = stored
      · subst stored
        by_cases sameQuery : query = scalar <;> simp [updateChild, childFor, sameQuery]
      · by_cases queryHere : query = stored
        · subst query
          simp [updateChild, childFor, insertedHere, Ne.symm insertedHere]
        · simp [updateChild, childFor, insertedHere, queryHere, ih]

/-- Full-key first-binding insertion: an existing payload keeps authority,
while every other key has precisely its former lookup result. -/
theorem lookup_insertFirst (key : List Scalar) (value : Payload) (query : List Scalar)
    (trie : Trie Payload Scalar) :
    lookup query (insertFirst key value trie) =
      if query = key then (lookup key trie).or (some value) else lookup query trie := by
  induction key generalizing trie query with
  | nil =>
      cases query with
      | nil => simp [lookup, insertFirst, valueAt]
      | cons scalar rest => simp [lookup, insertFirst, edgesOf]
  | cons scalar rest ih =>
      cases query with
      | nil => simp [lookup, insertFirst, valueAt]
      | cons queryHead queryRest =>
          simp only [lookup, insertFirst, edgesOf, childFor_updateChild]
          by_cases sameHead : queryHead = scalar
          · subst queryHead
            simp only [↓reduceIte, ih, List.cons.injEq, true_and]
          · simp [sameHead]

theorem lookup_inserted (key : List Scalar) (value : Payload) (trie : Trie Payload Scalar) :
    lookup key (insertFirst key value trie) = (lookup key trie).or (some value) := by
  simp [lookup_insertFirst]

/-- Overwrite changes exactly the selected full-key lookup. This includes
tries with repeated edges: lookup and update both select the first equal edge. -/
theorem lookup_put (key : List Scalar) (value : Payload) (query : List Scalar)
    (trie : Trie Payload Scalar) :
    lookup query (put key value trie) =
      if query = key then some value else lookup query trie := by
  induction key generalizing trie query with
  | nil =>
      cases query with
      | nil => simp [lookup, put, valueAt]
      | cons scalar rest => simp [lookup, put, edgesOf]
  | cons scalar rest ih =>
      cases query with
      | nil => simp [lookup, put, valueAt]
      | cons queryHead queryRest =>
          simp only [lookup, put, edgesOf, childFor_updateChild]
          by_cases sameHead : queryHead = scalar
          · subst queryHead
            simp only [↓reduceIte, ih, List.cons.injEq, true_and]
          · simp [sameHead]

theorem lookup_put_same (key : List Scalar) (value : Payload) (trie : Trie Payload Scalar) :
    lookup key (put key value trie) = some value := by
  simp [lookup_put]

theorem lookup_put_other (key : List Scalar) (value : Payload) (query : List Scalar)
    (trie : Trie Payload Scalar) (different : query ≠ key) :
    lookup query (put key value trie) = lookup query trie := by
  simp [lookup_put, different]

theorem lookup_other (key : List Scalar) (value : Payload) (query : List Scalar)
    (trie : Trie Payload Scalar)
    (different : query ≠ key) :
    lookup query (insertFirst key value trie) = lookup query trie := by
  simp [lookup_insertFirst, different]

theorem duplicate_keeps_first_payload (key : List Scalar) (oldValue newValue : Payload)
    (trie : Trie Payload Scalar)
    (found : lookup key trie = some oldValue) :
    lookup key (insertFirst key newValue trie) = some oldValue := by
  simp [lookup_insertFirst, found]

theorem missing_key_is_inserted (key : List Scalar) (value : Payload) (trie : Trie Payload Scalar)
    (missing : lookup key trie = none) : lookup key (insertFirst key value trie) = some value := by
  simp [lookup_insertFirst, missing]

def seed : List (List Scalar) → Trie (List Scalar) Scalar → Trie (List Scalar) Scalar
  | [], trie => trie
  | name :: rest, trie => seed rest (insertFirst name name trie)

/-- The graph wrapper stores each discovered name as its own payload. -/
theorem seed_lookup (names : List (List Scalar)) (query : List Scalar)
    (trie : Trie (List Scalar) Scalar) :
    lookup query (seed names trie) =
      (lookup query trie).or (if query ∈ names then some query else none) := by
  induction names generalizing trie with
  | nil => simp [seed]
  | cons name rest ih =>
      rw [seed, ih, lookup_insertFirst]
      by_cases same : query = name
      · subst query
        cases lookup name trie <;> simp
      · simp [same]

theorem lookup_seed_empty (names : List (List Scalar)) (query : List Scalar) :
    lookup query (seed names .empty) = if query ∈ names then some query else none := by
  simp [seed_lookup]

private def prefixPair : Trie Name :=
  insertFirst [97, 98] [2] (insertFirst [97] [1] .empty)

theorem prefix_and_extension_are_distinct :
    lookup [97] prefixPair = some [1] ∧ lookup [97, 98] prefixPair = some [2] := by decide

theorem absent_prefix_does_not_borrow_extension :
    lookup [97] (insertFirst [97, 98] [2] .empty) = none := by decide

theorem absent_extension_does_not_borrow_prefix :
    lookup [97, 98] (insertFirst [97] [1] .empty) = none := by decide

theorem duplicate_payload_is_not_replaced :
    lookup [97] (insertFirst [97] [9] prefixPair) = some [1] := by decide

theorem unrelated_name_stays_missing : lookup [98] prefixPair = none := by decide

theorem empty_name_and_nonempty_name_are_distinct :
    lookup [] (insertFirst [97] [2] (insertFirst [] [1] .empty)) = some [1] ∧
      lookup [97] (insertFirst [97] [2] (insertFirst [] [1] .empty)) = some [2] := by decide

theorem duplicate_edges_observe_the_first_child :
    lookup [97] (.node none [(97, .node (some [1]) []), (97, .node (some [2]) [])]) = some [1] ∧
      lookup [97] (insertFirst [97] [9]
        (.node none [(97, .node (some [1]) []), (97, .node (some [2]) [])])) = some [1] := by decide

/-- Integer admission does not identify negative, zero and positive keys. -/
theorem signed_names_are_distinct :
    let trie : Trie String Int := insertFirst [-1] "negative"
      (insertFirst [0] "zero" (insertFirst [1] "positive" .empty))
    lookup [-1] trie = some "negative" ∧ lookup [0] trie = some "zero" ∧
      lookup [1] trie = some "positive" := by decide

theorem signed_duplicate_keeps_first :
    lookup [-1, 97] (insertFirst [-1, 97] "later"
      (insertFirst [-1, 97] "first" (.empty : Trie String Int))) = some "first" := by decide

/-- Taking absolute values would change the admitted structured-key semantics. -/
theorem erasing_sign_changes_lookup :
    lookup [-1] (insertFirst [1] "positive" (.empty : Trie String Int)) = none ∧
      lookup (([-1] : List Int).map Int.natAbs)
        (insertFirst [1] "positive" (.empty : Trie String)) = some "positive" := by decide

end Mettapedia.GSLT.Parsing.PlainBnfGraphNameTrie
