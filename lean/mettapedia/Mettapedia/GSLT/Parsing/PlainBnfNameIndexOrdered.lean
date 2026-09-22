import Mettapedia.GSLT.Parsing.PlainBnfNameIndex
import Mathlib.Data.Nat.Basic

/-!
# Ordered first-binding semantics of the declaration-name index

The specification here is an independently recursive ordered association list.
The two/three-tree insertion preserves its exact bindings, not merely its key
set. Search agreement requires strictly ordered keys; equal leaf depth alone
does not justify pruning a subtree. These are auxiliary map laws, not a claim
that a source program or generated runtime has already been verified.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfNameIndex

universe uK uV
variable {Key : Type uK} {Value : Type uV} [LinearOrder Key]

def BindingOrder (left right : Key × Value) : Prop := left.1 < right.1

def Ordered (tree : Tree Key Value) : Prop := (bindings tree).Pairwise BindingOrder

def listLookup (key : Key) : List (Key × Value) → Option Value
  | [] => none
  | (stored, value) :: tail =>
      if key = stored then some value else listLookup key tail

def insertBindingFirst (key : Key) (value : Value) : List (Key × Value) → List (Key × Value)
  | [] => [(key, value)]
  | (stored, oldValue) :: tail =>
      if key = stored then (stored, oldValue) :: tail
      else if key < stored then (key, value) :: (stored, oldValue) :: tail
      else (stored, oldValue) :: insertBindingFirst key value tail

theorem ordered_split {left right : List (Key × Value)} {key : Key} {value : Value}
    (ordered : (left ++ (key, value) :: right).Pairwise BindingOrder) :
    left.Pairwise BindingOrder ∧ right.Pairwise BindingOrder ∧
      (∀ pair ∈ left, pair.1 < key) ∧ (∀ pair ∈ right, key < pair.1) := by
  rcases List.pairwise_append.mp ordered with ⟨before, after, cross⟩
  rcases List.pairwise_cons.mp after with ⟨rootBefore, tailOrdered⟩
  exact ⟨before, tailOrdered,
    fun pair member => cross pair member (key, value) (by simp), rootBefore⟩

theorem insertBindingFirst_after (key : Key) (value : Value)
    (left right : List (Key × Value))
    (before : ∀ pair ∈ left, pair.1 < key) :
    insertBindingFirst key value (left ++ right) =
      left ++ insertBindingFirst key value right := by
  induction left with
  | nil => rfl
  | cons pair tail ih =>
      rcases pair with ⟨stored, oldValue⟩
      have less : stored < key := before (stored, oldValue) (by simp)
      have tailBefore : ∀ pair ∈ tail, pair.1 < key :=
        fun pair member => before pair (by simp [member])
      simp only [List.cons_append, insertBindingFirst,
        if_neg (ne_of_gt less), if_neg (not_lt_of_ge (le_of_lt less))]
      rw [ih tailBefore]

theorem insertBindingFirst_before (key : Key) (value : Value)
    (left right : List (Key × Value)) (stored : Key) (oldValue : Value)
    (less : key < stored) :
    insertBindingFirst key value (left ++ (stored, oldValue) :: right) =
      insertBindingFirst key value left ++ (stored, oldValue) :: right := by
  induction left with
  | nil => simp [insertBindingFirst, ne_of_lt less, less]
  | cons pair tail ih =>
      rcases pair with ⟨head, headValue⟩
      simp only [List.cons_append, insertBindingFirst]
      split_ifs with equal headLess
      · rfl
      · rfl
      · simp only [List.cons_append, ih]

theorem insertBindingFirst_pivot (key : Key) (value : Value)
    (left right : List (Key × Value)) (stored : Key) (oldValue : Value)
    (before : ∀ pair ∈ left, pair.1 < stored) :
    insertBindingFirst key value (left ++ (stored, oldValue) :: right) =
      if key = stored then left ++ (stored, oldValue) :: right
      else if key < stored then insertBindingFirst key value left ++ (stored, oldValue) :: right
      else left ++ (stored, oldValue) :: insertBindingFirst key value right := by
  by_cases equal : key = stored
  · subst key
    rw [insertBindingFirst_after stored value left _ before]
    simp [insertBindingFirst]
  · by_cases less : key < stored
    · simp only [if_neg equal, if_pos less]
      exact insertBindingFirst_before key value left right stored oldValue less
    · have greater : stored < key := lt_of_le_of_ne (le_of_not_gt less) (Ne.symm equal)
      have leftBefore : ∀ pair ∈ left, pair.1 < key :=
        fun pair member => lt_trans (before pair member) greater
      rw [insertBindingFirst_after key value left _ leftBefore]
      simp only [insertBindingFirst, if_neg equal, if_neg less]

theorem insertWalk_bindings (key : Key) (value : Value) (tree : Tree Key Value)
    (ordered : Ordered tree) :
    resultBindings (insertWalk key value tree) =
      insertBindingFirst key value (bindings tree) := by
  induction tree with
  | empty => rfl
  | two left stored oldValue right leftIH rightIH =>
      obtain ⟨leftOrder, rightOrder, before, _⟩ := ordered_split ordered
      rw [bindings, insertBindingFirst_pivot key value _ _ stored oldValue before]
      simp only [insertWalk]
      split_ifs
      · rfl
      · rw [bindings_twoLeft, leftIH leftOrder]
      · rw [bindings_twoRight, rightIH rightOrder]
  | three left first firstValue middle second secondValue right leftIH middleIH rightIH =>
      obtain ⟨leftOrder, restOrder, beforeFirst, _⟩ := ordered_split ordered
      obtain ⟨middleOrder, rightOrder, beforeSecond, _⟩ := ordered_split restOrder
      rw [bindings, insertBindingFirst_pivot key value _ _ first firstValue beforeFirst]
      simp only [insertWalk]
      by_cases equal : key = first
      · simp only [if_pos equal]
        rfl
      · by_cases less : key < first
        · simp only [if_neg equal, if_pos less]
          rw [bindings_threeLeft, leftIH leftOrder]
        · simp only [if_neg equal, if_neg less]
          rw [insertBindingFirst_pivot key value _ _ second secondValue beforeSecond]
          split_ifs
          · rfl
          · rw [bindings_threeMiddle, middleIH middleOrder]
          · rw [bindings_threeRight, rightIH rightOrder]

theorem insertFirst_bindings (key : Key) (value : Value) (tree : Tree Key Value)
    (ordered : Ordered tree) :
    bindings (insertFirst key value tree) =
      insertBindingFirst key value (bindings tree) := by
  rw [insertFirst, bindings_finish, insertWalk_bindings key value tree ordered]

theorem mem_insertBindingFirst (key : Key) (value : Value) (rows : List (Key × Value))
    {pair : Key × Value} (member : pair ∈ insertBindingFirst key value rows) :
    pair = (key, value) ∨ pair ∈ rows := by
  induction rows with
  | nil => exact Or.inl (by simpa [insertBindingFirst] using member)
  | cons head tail ih =>
      rcases head with ⟨stored, oldValue⟩
      simp only [insertBindingFirst] at member
      split_ifs at member with equal less
      · exact Or.inr member
      · rcases List.mem_cons.mp member with fresh | old
        · exact Or.inl fresh
        · exact Or.inr old
      · rcases List.mem_cons.mp member with head | rest
        · exact Or.inr (List.mem_cons.mpr (Or.inl head))
        · rcases ih rest with fresh | old
          · exact Or.inl fresh
          · exact Or.inr (List.mem_cons.mpr (Or.inr old))

theorem insertBindingFirst_ordered (key : Key) (value : Value) (rows : List (Key × Value))
    (ordered : rows.Pairwise BindingOrder) :
    (insertBindingFirst key value rows).Pairwise BindingOrder := by
  induction rows with
  | nil => simp [insertBindingFirst]
  | cons head tail ih =>
      rcases head with ⟨stored, oldValue⟩
      rcases List.pairwise_cons.mp ordered with ⟨before, tailOrder⟩
      simp only [insertBindingFirst]
      split_ifs with equal less
      · exact ordered
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ordered⟩
        intro pair member
        rcases List.mem_cons.mp member with head | rest
        · subst pair
          exact less
        · exact lt_trans less (before pair rest)
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ih tailOrder⟩
        intro pair member
        rcases mem_insertBindingFirst key value tail member with fresh | old
        · subst pair
          exact lt_of_le_of_ne (le_of_not_gt less) (Ne.symm equal)
        · exact before pair old

theorem insertFirst_ordered (key : Key) (value : Value) (tree : Tree Key Value)
    (ordered : Ordered tree) : Ordered (insertFirst key value tree) := by
  unfold Ordered
  rw [insertFirst_bindings key value tree ordered]
  exact insertBindingFirst_ordered key value (bindings tree) ordered

theorem listLookup_append (key : Key) (left right : List (Key × Value)) :
    listLookup key (left ++ right) =
      match listLookup key left with
      | some value => some value
      | none => listLookup key right := by
  induction left with
  | nil => rfl
  | cons pair tail ih =>
      rcases pair with ⟨stored, value⟩
      simp only [List.cons_append, listLookup]
      split_ifs
      · rfl
      · exact ih

theorem listLookup_none (key : Key) (rows : List (Key × Value))
    (absent : ∀ pair ∈ rows, key ≠ pair.1) : listLookup key rows = none := by
  induction rows with
  | nil => rfl
  | cons pair tail ih =>
      rcases pair with ⟨stored, value⟩
      have unequal : key ≠ stored := absent (stored, value) (by simp)
      have tailAbsent : ∀ pair ∈ tail, key ≠ pair.1 :=
        fun pair member => absent pair (List.mem_cons_of_mem _ member)
      simp only [listLookup, if_neg unequal, ih tailAbsent]

theorem listLookup_pivot (key : Key) (left right : List (Key × Value))
    (stored : Key) (value : Value)
    (before : ∀ pair ∈ left, pair.1 < stored)
    (after : ∀ pair ∈ right, stored < pair.1) :
    listLookup key (left ++ (stored, value) :: right) =
      if key = stored then some value
      else if key < stored then listLookup key left else listLookup key right := by
  rw [listLookup_append]
  by_cases equal : key = stored
  · subst key
    have absent := listLookup_none stored left
      (fun pair member => ne_of_gt (before pair member))
    simp [absent, listLookup]
  · by_cases less : key < stored
    · have absent := listLookup_none key right
        (fun pair member => ne_of_lt (lt_trans less (after pair member)))
      simp only [listLookup, if_neg equal, if_pos less, absent]
      cases listLookup key left <;> rfl
    · have greater : stored < key := lt_of_le_of_ne (le_of_not_gt less) (Ne.symm equal)
      have absent := listLookup_none key left
        (fun pair member => ne_of_gt (lt_trans (before pair member) greater))
      simp only [listLookup, if_neg equal, if_neg less, absent]

/-- Search returns precisely the payload in the independent in-order map.
Unlike duplicate retention, this property needs the key-order invariant. -/
theorem lookup_eq_listLookup (key : Key) (tree : Tree Key Value) (ordered : Ordered tree) :
    lookup key tree = listLookup key (bindings tree) := by
  induction tree with
  | empty => rfl
  | two left stored value right leftIH rightIH =>
      obtain ⟨leftOrder, rightOrder, before, after⟩ := ordered_split ordered
      rw [bindings, listLookup_pivot key _ _ stored value before after]
      simp only [lookup]
      split_ifs
      · rfl
      · exact leftIH leftOrder
      · exact rightIH rightOrder
  | three left first firstValue middle second secondValue right leftIH middleIH rightIH =>
      obtain ⟨leftOrder, restOrder, beforeFirst, afterFirst⟩ := ordered_split ordered
      obtain ⟨middleOrder, rightOrder, beforeSecond, afterSecond⟩ := ordered_split restOrder
      rw [bindings, listLookup_pivot key _ _ first firstValue beforeFirst afterFirst,
        listLookup_pivot key _ _ second secondValue beforeSecond afterSecond]
      simp only [lookup]
      split_ifs
      · rfl
      · exact leftIH leftOrder
      · rfl
      · exact middleIH middleOrder
      · exact rightIH rightOrder

theorem listLookup_insertBindingFirst (query key : Key) (value : Value)
    (rows : List (Key × Value)) (ordered : rows.Pairwise BindingOrder) :
    listLookup query (insertBindingFirst key value rows) =
      if query = key then some ((listLookup key rows).getD value) else listLookup query rows := by
  induction rows with
  | nil => simp [insertBindingFirst, listLookup]
  | cons head tail ih =>
      rcases head with ⟨stored, oldValue⟩
      rcases List.pairwise_cons.mp ordered with ⟨before, tailOrder⟩
      by_cases equal : key = stored
      · subst key
        simp only [insertBindingFirst, listLookup]
        by_cases queryEqual : query = stored
        · simp [listLookup, queryEqual]
        · simp [listLookup, queryEqual]
      · by_cases less : key < stored
        · have tailAbsent : listLookup key tail = none :=
            listLookup_none key tail
              (fun pair member => ne_of_lt (lt_trans less (before pair member)))
          simp only [insertBindingFirst, if_neg equal, if_pos less, listLookup, tailAbsent]
          by_cases queryEqual : query = key
          · simp [queryEqual]
          · simp only [if_neg queryEqual]
        · simp only [insertBindingFirst, if_neg equal, if_neg less, listLookup]
          by_cases queryEqual : query = stored
          · subst query
            simp [Ne.symm equal]
          · simp only [if_neg queryEqual, ih tailOrder]

/-- Insertion modifies exactly the queried binding when it was missing; all
other payloads are unchanged and a prior payload always has authority. -/
theorem lookup_insertFirst (query key : Key) (value : Value) (tree : Tree Key Value)
    (ordered : Ordered tree) :
    lookup query (insertFirst key value tree) =
      if query = key then some ((lookup key tree).getD value) else lookup query tree := by
  rw [lookup_eq_listLookup query _ (insertFirst_ordered key value tree ordered),
    insertFirst_bindings key value tree ordered,
    listLookup_insertBindingFirst query key value (bindings tree) ordered,
    lookup_eq_listLookup key tree ordered, lookup_eq_listLookup query tree ordered]

/-- This branch is the freshness fact used by an indexed declaration collector. -/
theorem lookup_insert_missing (key : Key) (value : Value) (tree : Tree Key Value)
    (ordered : Ordered tree) (missing : lookup key tree = none) :
    lookup key (insertFirst key value tree) = some value := by
  simp [lookup_insertFirst key key value tree ordered, missing]

theorem lookup_insert_other (query key : Key) (value : Value) (tree : Tree Key Value)
    (ordered : Ordered tree) (different : query ≠ key) :
    lookup query (insertFirst key value tree) = lookup query tree := by
  simp [lookup_insertFirst query key value tree ordered, different]

section Controls

private def firstBindings : Tree Nat String :=
  insertFirst 2 "two" (insertFirst 1 "one" (insertFirst 3 "three" .empty))

example : bindings firstBindings = [(1, "one"), (2, "two"), (3, "three")] := by decide

example : lookup 2 (insertFirst 2 "replacement" firstBindings) = some "two" := by decide

example : lookup 4 firstBindings = none := by decide

private def balancedButUnordered : Tree Nat String :=
  .two (.two .empty 3 "three" .empty) 2 "two" (.two .empty 1 "one" .empty)

example : Balanced balancedButUnordered 2 := by
  exact .two 2 "two" (.two 3 "three" .empty .empty) (.two 1 "one" .empty .empty)

/-- Balanced shape does not license ordered search: the key is present in the
in-order data, but search correctly has no guarantee on a malformed map. -/
example : lookup 3 balancedButUnordered = none ∧
    listLookup 3 (bindings balancedButUnordered) = some "three" := by decide

end Controls

end Mettapedia.GSLT.Parsing.PlainBnfNameIndex
