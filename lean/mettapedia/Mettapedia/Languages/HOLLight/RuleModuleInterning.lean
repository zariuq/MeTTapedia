import Mettapedia.Languages.HOLLight.RuleModuleComparisonLaws

/-!
# Interning stores: equal read-backs are the same node

The native HOL Light kernel represents names, types and terms by interned (hash-consed) objects.
A name is an id in a table of byte strings (`hk_name_intern`).  A type or a term is a pointer to a
node made only by the interning constructors `hk_ty_var`, `hk_ty_app`, `hk_tm_var`, `hk_tm_const`,
`hk_tm_comb` and `hk_tm_abs` (the last two through `node_term`).  Each of them first looks for a
node of the same kind with the same fields, children compared by pointer, and returns it if there
is one; only otherwise does it allocate a new node.  When the HOL Light kernel rule module runs on
this representation, its equality judgments on names, types and terms compare ids and pointers.
This file proves the law behind that: in an interning store, the trees that two nodes read back
as are equal exactly when the two nodes are the same node.

* The model.  A store (`Store`) is a list of nodes; node `i` is the `i`-th, a label and the ids of
  its children.  `readback s i` reads node `i` back as a `Tree`, by recursion on ids: a child that
  is not an earlier node, and an id out of range, read as the leaf `junk`.
* The invariant (`Interning`): every child of a node is an earlier node (the store is built
  bottom-up), and two nodes with equal contents are the same node (the store interns).
* The law (`interning_eq_iff`): under the invariant, for ids in range,
  `readback s i = readback s j ↔ i = j`.
* Interning (`intern`): the id of the node with the given contents if there is one, otherwise the
  contents appended and their new id.  It preserves the invariant when the new node's children are
  in range (`interning_intern`), returns an id in range that names a node with the given contents
  (`getElem?_intern`), whose read-back is the label over the read-backs of the children
  (`readback_intern`), and leaves the read-backs of existing ids unchanged
  (`readback_intern_of_lt`).  Interning the same contents twice changes nothing
  (`intern_intern`).  Every run of interning operations, each with its children in range, gives
  an interning store (`interning_run`, and `interning_run_nil` from the empty store).
* Comparisons and equality judgments: a comparison of trees whose `eq` outcome means equality
  answers `eq` on two read-backs exactly when the ids are equal (`cmp_readback_eq_iff`), and an
  equality flag computed on ids is the one computed on read-backs (`decide_eq_readback`,
  `decide_eq_cmp_readback`).
* Instances: names (`names_eq_iff`; `nameStore_eq_iff` for every store of names built by
  interning), and HOL types and terms in one store (`hol_interning_eq_iff`, with the six
  constructors `tyVar`, `tyApp`, `tmVar`, `tmConst`, `tmComb`, `tmAbs`).
* Each hypothesis of the law is needed (`interning_eq_iff_needs_injective`,
  `interning_eq_iff_needs_kids_lt`, `interning_eq_iff_needs_range`).
* The id tables.  The module maps ids to cells by binary tries (`Trie`, `Table`, and the rules
  `trieGet`, `trieSet`, `tableGet`, `tablePut`, `tableSet`, `tableNext`, `emptyTable`); the native
  code uses arrays (`NTable`).  The read-back of an array (`IsReadback`) is the trie whose nodes
  are the union of the digit paths of the stored ids, a stored id's own node holding its cell and
  every other node `c-none`.  It exists (`isReadback_rbTrie`) and is unique
  (`IsReadback.unique`), and every table operation commutes with it (`trieGet_rbTrie`,
  `trieSet_rbTrie`, `rbTrie_nil`, `tableGet_readback`, `tablePut_readback`, `tableSet_readback`,
  `tableNext_readback`, `emptyTable_readback`).  The shape is part of the read-back
  (`tBad_ne_rbTrie`), and numerals must be canonical (`tableSet_readback_needs_canon`).
* The binding of the equality judgments.  The module's comparisons answer `eq` exactly on equal
  arguments (`cmpType_eq_iff`, `cmpTypes_eq_iff`, `cmpLeaf_eq_iff`, `cmpTerm_eq_iff`), so
  `"ty-eq"`, `"tm-eq"`, `"tms-eq"` answer `yes` exactly on equal arguments (`tyEq_eq_yes_iff`,
  `tmEq_eq_yes_iff`, `tmsEq_eq_yes_iff`).  Read-back trees decode to the module's types and terms
  (`decodeTy`, `decodeTerm`), injectively on the trees accepted (`decodeTy_injective`,
  `decodeTerm_injective`).  In an interning store, `"ty-eq"`, `"tm-eq"` on decoded nodes and
  `"str-eq"` on names answer `yes` exactly on the same node (`tyEq_binding`, `tmEq_binding`,
  `strEq_binding`).
* Names held as ids.  With an interning table of names, a store whose labels hold name ids
  interns exactly when the store with the names resolved to bytes does, and reads back alike
  (`hol_names_as_ids`, from `interning_relabel_iff` and `readback_relabel`).

How the model matches the native kernel, and what it leaves out.

* The lookups compare the kind and the fields of a node after a filter on a hash computed from
  those fields, so equal contents always pass the filter and a collision of hashes only costs a
  full comparison.  The model looks a node up by equality of its contents, which is what the
  lookups decide; the probing of the hash table is not modelled.
* `TY_APP` and `CONST` nodes carry a declaration, compared by pointer.  The module's types and
  constants are syntactic and get exactly one declaration per name, so a label carries the name
  instead.  The labels of `HolLabel` carry names as byte strings where the native nodes carry
  name ids (`HolLabelId`); the two models agree because the names are interned too
  (`hol_names_as_ids`).
* A `COMB` or `ABS` node records its type, but its identity is its two children, and the type is a
  function of them: the range of the function's type for `hk_tm_comb`, the function type of the
  variable's and the body's types for `hk_tm_abs` (interned first).  The module's application and
  abstraction carry no type either.
* Ids are allocation ranks: id `i` is the `i`-th node made.  Name ids start at 1 in the native
  table, at 0 here.  The collector, which frees unreachable nodes and rebuilds the tables from the
  marked ones, is not modelled; nor are refusals (mismatched types, an abstraction over a
  non-variable, depth and environment limits, failed allocation), which make no node.
* The native id tables are updated in place, and each carries a version so that an operation on
  a value older than the last update is refused.  The theorems treat tables as values, which the
  arrays refine when no table value is used after an update made from it.  Versions, the range of
  ids that fit an immediate, and the conversion of a table in module form into an array are not
  modelled.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModuleInterning

universe u v

/-! ## Trees -/

/-- A tree: a label and the list of its subtrees. -/
inductive Tree (L : Type u) : Type u
  | node : L → List (Tree L) → Tree L
  deriving Repr

namespace Tree

variable {L : Type u} [DecidableEq L]

mutual

/-- Equality of trees is decidable.  The recursion is structural, so `decide` evaluates it. -/
def decEq : (a b : Tree L) → Decidable (a = b)
  | .node a as, .node b bs =>
    if h : a = b then
      match decEqList as bs with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse fun e => h' (Tree.node.inj e).2
    else isFalse fun e => h (Tree.node.inj e).1
termination_by structural a => a

/-- Equality of lists of trees is decidable. -/
def decEqList : (as bs : List (Tree L)) → Decidable (as = bs)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse nofun
  | _ :: _, [] => isFalse nofun
  | a :: as, b :: bs =>
    match decEq a b, decEqList as bs with
    | isTrue h, isTrue h' => isTrue (h ▸ h' ▸ rfl)
    | isFalse h, _ => isFalse fun e => h (List.cons.inj e).1
    | _, isFalse h' => isFalse fun e => h' (List.cons.inj e).2
termination_by structural as => as

end

instance : DecidableEq (Tree L) := decEq

end Tree

/-! ## Stores and read-back -/

/-- A node of a store: a label and the ids of its children. -/
@[ext] structure Node (L : Type u) : Type u where
  /-- The kind of the node with its fields other than the children. -/
  label : L
  /-- The ids of the children, in order. -/
  kids : List Nat
  deriving DecidableEq, Repr

/-- A store: node `i` is the `i`-th element of the list. -/
abbrev Store (L : Type u) : Type u := List (Node L)

section Readback

variable {L : Type u} [Inhabited L]

/-- The junk leaf.  An id that names no node reads as it, and so does a child that is not an
earlier node; under the invariant, neither is reached from a node in range. -/
def junk : Tree L := .node default []

/-- The tree of node `i` of `s`, its children read in `ts`, the trees of the earlier nodes. -/
def treeAt (s : Store L) (i : Nat) (ts : List (Tree L)) : Tree L :=
  match s[i]? with
  | none => junk
  | some n => .node n.label (n.kids.map fun k => ts.getD k junk)

/-- The read-backs of the nodes `0, …, i - 1`: recursion on ids, each node read from the read-backs
of the nodes before it. -/
def readbacks (s : Store L) : Nat → List (Tree L)
  | 0 => []
  | i + 1 => readbacks s i ++ [treeAt s i (readbacks s i)]

/-- **Read-back** of node `i` of `s` as a tree. -/
def readback (s : Store L) (i : Nat) : Tree L :=
  treeAt s i (readbacks s i)

theorem readbacks_succ (s : Store L) (i : Nat) :
    readbacks s (i + 1) = readbacks s i ++ [readback s i] := rfl

@[simp] theorem length_readbacks (s : Store L) (i : Nat) : (readbacks s i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [readbacks_succ, List.length_append, ih]; rfl

theorem getElem?_readbacks (s : Store L) (i k : Nat) :
    (readbacks s i)[k]? = if k < i then some (readback s k) else none := by
  induction i with
  | zero => simp [readbacks]
  | succ i ih =>
    rw [readbacks_succ]
    rcases Nat.lt_trichotomy k i with h | rfl | h
    · rw [List.getElem?_append_left (by simpa using h), ih, if_pos h, if_pos (by omega)]
    · rw [List.getElem?_append_right (by simp), if_pos (by omega)]
      simp
    · rw [List.getElem?_append_right (by simp; omega), if_neg (by omega)]
      simp
      omega

theorem getD_readbacks (s : Store L) (i k : Nat) :
    (readbacks s i).getD k junk = if k < i then readback s k else junk := by
  rw [List.getD_eq_getElem?_getD, getElem?_readbacks]
  split <;> rfl

/-- **Read-back, recursion on ids.**  A node in range reads as its label over the read-backs of its
children; a child that is not an earlier node reads as `junk`. -/
theorem readback_of_lt {s : Store L} {i : Nat} (hi : i < s.length) :
    readback s i =
      .node s[i].label (s[i].kids.map fun k => if k < i then readback s k else junk) := by
  rw [readback, treeAt, List.getElem?_eq_getElem hi]
  simp only [getD_readbacks]

/-- An id out of range reads as `junk`. -/
theorem readback_of_length_le {s : Store L} {i : Nat} (hi : s.length ≤ i) :
    readback s i = junk := by
  simp only [readback, treeAt, List.getElem?_eq_none hi]

/-- A node in range whose children are earlier nodes reads as its label over the read-backs of its
children. -/
theorem readback_eq_node {s : Store L} {i : Nat} (hi : i < s.length)
    (h : ∀ k ∈ s[i].kids, k < i) :
    readback s i = .node s[i].label (s[i].kids.map (readback s)) := by
  rw [readback_of_lt hi, List.map_congr_left fun k hk => if_pos (h k hk)]

theorem treeAt_append {s : Store L} (t : Store L) {i : Nat} (hi : i < s.length)
    (ts : List (Tree L)) : treeAt (s ++ t) i ts = treeAt s i ts := by
  simp only [treeAt, List.getElem?_append_left hi]

theorem readbacks_append (s t : Store L) :
    ∀ i, i ≤ s.length → readbacks (s ++ t) i = readbacks s i
  | 0, _ => rfl
  | i + 1, h => by
    show readbacks (s ++ t) i ++ [treeAt (s ++ t) i (readbacks (s ++ t) i)] =
      readbacks s i ++ [treeAt s i (readbacks s i)]
    rw [readbacks_append s t i (by omega), treeAt_append t (show i < s.length by omega)]

/-- Appending nodes leaves the read-backs of existing ids unchanged. -/
theorem readback_append {s : Store L} (t : Store L) {i : Nat} (hi : i < s.length) :
    readback (s ++ t) i = readback s i := by
  rw [readback, readbacks_append s t i (Nat.le_of_lt hi), treeAt_append t hi, readback]

/-- Extending a store leaves the read-backs of existing ids unchanged. -/
theorem readback_of_prefix {s t : Store L} (h : s <+: t) {i : Nat} (hi : i < s.length) :
    readback t i = readback s i := by
  obtain ⟨u, rfl⟩ := h
  exact readback_append u hi

end Readback

/-! ## The invariant -/

section Invariant

variable {L : Type u}

/-- **The store invariant.** -/
structure Interning (s : Store L) : Prop where
  /-- Every child of node `i` is an earlier node: the store is built bottom-up. -/
  kids_lt : ∀ (i : Nat) (hi : i < s.length), ∀ k ∈ s[i].kids, k < i
  /-- Two nodes with equal contents are the same node: the store interns. -/
  injective : ∀ (i : Nat) (hi : i < s.length) (j : Nat) (hj : j < s.length), s[i] = s[j] → i = j

theorem interning_iff (s : Store L) :
    Interning s ↔ (∀ (i : Nat) (hi : i < s.length), ∀ k ∈ (s[i]'hi).kids, k < i) ∧
      ∀ (i : Nat) (hi : i < s.length) (j : Nat) (hj : j < s.length), s[i]'hi = s[j]'hj → i = j :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

instance Interning.decidable [DecidableEq L] (s : Store L) : Decidable (Interning s) :=
  decidable_of_iff _ (interning_iff s).symm

/-- The empty store is an interning store. -/
theorem interning_nil : Interning ([] : Store L) :=
  ⟨fun _ hi => absurd hi (Nat.not_lt_zero _), fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

theorem getElem_append_singleton {α : Type u} (s : List α) (a : α) {i : Nat}
    (hi : i < (s ++ [a]).length) : (s ++ [a])[i] = if h : i < s.length then s[i] else a := by
  rw [List.getElem_append]
  split
  · rfl
  · exact List.getElem_singleton _

/-- Appending a node whose contents are new and whose children are in range keeps the
invariant. -/
theorem interning_append {s : Store L} (hs : Interning s) {n : Node L}
    (hn : ∀ k ∈ n.kids, k < s.length) (hns : n ∉ s) : Interning (s ++ [n]) := by
  constructor
  · intro i hi k hk
    rw [getElem_append_singleton] at hk
    split at hk
    · exact hs.kids_lt i ‹_› k hk
    · have := hn k hk
      simp only [List.length_append, List.length_singleton] at hi
      omega
  · intro i hi j hj hij
    simp only [List.length_append, List.length_singleton] at hi hj
    rw [getElem_append_singleton, getElem_append_singleton] at hij
    split at hij <;> split at hij
    · exact hs.injective i ‹_› j ‹_› hij
    · exact absurd (hij ▸ List.getElem_mem ‹_›) hns
    · exact absurd (hij.symm ▸ List.getElem_mem ‹_›) hns
    · omega

end Invariant

/-! ## The law -/

/-- Two lists with equal images under `f` are equal when `f` separates their elements. -/
theorem eq_of_map_eq {α : Type u} {β : Type v} {f : α → β} :
    ∀ {l₁ l₂ : List α}, (∀ a ∈ l₁, ∀ b ∈ l₂, f a = f b → a = b) → l₁.map f = l₂.map f → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (by simp)
  | _ :: _, [], _, h => absurd h (by simp)
  | a :: l₁, b :: l₂, hf, h => by
    rw [List.map_cons, List.map_cons, List.cons.injEq] at h
    rw [hf a List.mem_cons_self b List.mem_cons_self h.1,
      eq_of_map_eq (fun x hx y hy => hf x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
        h.2]

section Law

variable {L : Type u} [Inhabited L]

/-- The law, by induction on a bound `m` of `i + j`. -/
theorem eq_of_readback_eq {s : Store L} (hs : Interning s) :
    ∀ m i j, i + j < m → i < s.length → j < s.length → readback s i = readback s j → i = j
  | 0, _, _, hm, _, _, _ => absurd hm (Nat.not_lt_zero _)
  | m + 1, i, j, hm, hi, hj, h => by
    rw [readback_eq_node hi (hs.kids_lt i hi), readback_eq_node hj (hs.kids_lt j hj)] at h
    obtain ⟨hl, hk⟩ := Tree.node.inj h
    refine hs.injective i hi j hj (Node.ext hl (eq_of_map_eq (fun a ha b hb hab => ?_) hk))
    have ha' := hs.kids_lt i hi a ha
    have hb' := hs.kids_lt j hj b hb
    exact eq_of_readback_eq hs m a b (by omega) (by omega) (by omega) hab

/-- **Interning.**  In an interning store, two nodes in range have equal read-backs exactly when
they are the same node. -/
theorem interning_eq_iff {s : Store L} (hs : Interning s) {i j : Nat} (hi : i < s.length)
    (hj : j < s.length) : readback s i = readback s j ↔ i = j :=
  ⟨eq_of_readback_eq hs (i + j + 1) i j (Nat.lt_succ_self _) hi hj, fun h => h ▸ rfl⟩

end Law

/-! ## The interning operation -/

section Intern

variable {L : Type u} [DecidableEq L]

/-- **Interning** the contents `n` into the store `s`: the id of the node with contents `n` if
there is one, and the store unchanged; otherwise `n` appended, and its id. -/
def intern (s : Store L) (n : Node L) : Store L × Nat :=
  match s.idxOf? n with
  | some i => (s, i)
  | none => (s ++ [n], s.length)

theorem intern_of_idxOf?_eq_some {s : Store L} {n : Node L} {i : Nat} (h : s.idxOf? n = some i) :
    intern s n = (s, i) := by
  simp only [intern, h]

theorem intern_of_not_mem {s : Store L} {n : Node L} (h : n ∉ s) :
    intern s n = (s ++ [n], s.length) := by
  simp only [intern, List.idxOf?_eq_none_iff.mpr h]

/-- The lookup finds a node with the given contents. -/
theorem getElem?_of_idxOf?_eq_some {s : Store L} {n : Node L} {i : Nat}
    (h : s.idxOf? n = some i) : s[i]? = some n := by
  induction s generalizing i with
  | nil => exact absurd h nofun
  | cons x xs ih =>
    rw [List.idxOf?_cons] at h
    split at h
    · rename_i hx
      cases h
      rw [List.getElem?_cons_zero, beq_iff_eq.mp hx]
    · obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.getElem?_cons_succ]
      exact ih hj

/-- New contents appended to a store are found at the end. -/
theorem idxOf?_append_singleton {s : Store L} {n : Node L} (h : n ∉ s) :
    (s ++ [n]).idxOf? n = some s.length := by
  induction s with
  | nil => simp
  | cons x xs ih =>
    have hx : ¬ (x == n) = true := fun e => h (beq_iff_eq.mp e ▸ List.mem_cons_self)
    rw [List.cons_append, List.idxOf?_cons, if_neg hx,
      ih fun e => h (List.mem_cons_of_mem _ e)]
    rfl

/-- Interning extends the store. -/
theorem prefix_intern (s : Store L) (n : Node L) : s <+: (intern s n).1 := by
  cases h : s.idxOf? n with
  | some i => rw [intern_of_idxOf?_eq_some h]; exact List.prefix_refl s
  | none => rw [intern_of_not_mem (List.idxOf?_eq_none_iff.mp h)]; exact List.prefix_append s [n]

/-- The returned id is in range and names a node with the given contents. -/
theorem getElem?_intern (s : Store L) (n : Node L) : (intern s n).1[(intern s n).2]? = some n := by
  cases h : s.idxOf? n with
  | some i =>
    rw [intern_of_idxOf?_eq_some h]
    exact getElem?_of_idxOf?_eq_some h
  | none =>
    rw [intern_of_not_mem (List.idxOf?_eq_none_iff.mp h)]
    exact List.getElem?_concat_length

theorem lt_length_intern (s : Store L) (n : Node L) : (intern s n).2 < (intern s n).1.length :=
  (List.getElem?_eq_some_iff.mp (getElem?_intern s n)).1

/-- **Interning keeps the invariant** when the new node's children are in range. -/
theorem interning_intern {s : Store L} (hs : Interning s) {n : Node L}
    (hn : ∀ k ∈ n.kids, k < s.length) : Interning (intern s n).1 := by
  cases h : s.idxOf? n with
  | some i => rw [intern_of_idxOf?_eq_some h]; exact hs
  | none =>
    have hns : n ∉ s := List.idxOf?_eq_none_iff.mp h
    rw [intern_of_not_mem hns]
    exact interning_append hs hn hns

/-- **Read-back of the result**: the label over the read-backs of the children. -/
theorem readback_intern [Inhabited L] {s : Store L} (hs : Interning s) {n : Node L}
    (hn : ∀ k ∈ n.kids, k < s.length) :
    readback (intern s n).1 (intern s n).2 = .node n.label (n.kids.map (readback s)) := by
  cases h : s.idxOf? n with
  | some i =>
    obtain ⟨hi, hsi⟩ := List.getElem?_eq_some_iff.mp (getElem?_of_idxOf?_eq_some h)
    rw [intern_of_idxOf?_eq_some h]
    show readback s i = _
    rw [readback_eq_node hi (hs.kids_lt i hi), hsi]
  | none =>
    rw [intern_of_not_mem (List.idxOf?_eq_none_iff.mp h)]
    show readback (s ++ [n]) s.length = _
    rw [readback_of_lt (by simp), List.getElem_concat_length rfl]
    congr 1
    exact List.map_congr_left fun k hk => by rw [if_pos (hn k hk), readback_append _ (hn k hk)]

/-- Interning leaves the read-backs of existing ids unchanged. -/
theorem readback_intern_of_lt [Inhabited L] (s : Store L) (n : Node L) {i : Nat}
    (hi : i < s.length) : readback (intern s n).1 i = readback s i :=
  readback_of_prefix (prefix_intern s n) hi

/-- Interning the same contents twice gives the same id and the same store. -/
theorem intern_intern (s : Store L) (n : Node L) : intern (intern s n).1 n = intern s n := by
  cases h : s.idxOf? n with
  | some i => rw [intern_of_idxOf?_eq_some h]; exact intern_of_idxOf?_eq_some h
  | none =>
    have hns : n ∉ s := List.idxOf?_eq_none_iff.mp h
    rw [intern_of_not_mem hns]
    exact intern_of_idxOf?_eq_some (idxOf?_append_singleton hns)

/-! ### Runs -/

/-- Interning the contents `ops` in order, starting from the store `s`: the final store. -/
def run (s : Store L) : List (Node L) → Store L
  | [] => s
  | n :: ns => run (intern s n).1 ns

/-- A run extends the store it starts from. -/
theorem prefix_run (s : Store L) : ∀ ops : List (Node L), s <+: run s ops
  | [] => List.prefix_refl s
  | n :: ns => (prefix_intern s n).trans (prefix_run _ ns)

/-- Every node of a run's store was in the initial store or among the interned contents. -/
theorem mem_run {s : Store L} {ops : List (Node L)} {x : Node L} (hx : x ∈ run s ops) :
    x ∈ s ∨ x ∈ ops := by
  induction ops generalizing s with
  | nil => exact .inl hx
  | cons n ns ih =>
    rcases ih hx with h | h
    · cases hn : s.idxOf? n with
      | some i => rw [intern_of_idxOf?_eq_some hn] at h; exact .inl h
      | none =>
        rw [intern_of_not_mem (List.idxOf?_eq_none_iff.mp hn), List.mem_append,
          List.mem_singleton] at h
        rcases h with h | rfl
        · exact .inl h
        · exact .inr List.mem_cons_self
    · exact .inr (List.mem_cons_of_mem _ h)

/-- **Every run.**  Interning contents in order, starting from an interning store, each with its
children in range of the store it is interned into, gives an interning store. -/
theorem interning_run {s : Store L} (hs : Interning s) {ops : List (Node L)}
    (hops : ∀ m (hm : m < ops.length), ∀ k ∈ ops[m].kids, k < (run s (ops.take m)).length) :
    Interning (run s ops) := by
  induction ops generalizing s with
  | nil => exact hs
  | cons n ns ih =>
    have h₀ : ∀ k ∈ n.kids, k < s.length := hops 0 (by simp)
    refine ih (interning_intern hs h₀) fun m hm k hk => ?_
    have := hops (m + 1) (by simp only [List.length_cons]; omega) k (by simpa using hk)
    simpa [run] using this

/-- **Every run from the empty store.** -/
theorem interning_run_nil {ops : List (Node L)}
    (hops : ∀ m (hm : m < ops.length), ∀ k ∈ ops[m].kids, k < (run [] (ops.take m)).length) :
    Interning (run [] ops) :=
  interning_run interning_nil hops

end Intern

/-! ## Comparisons and equality judgments -/

section Comparison

variable {L : Type u} [Inhabited L]

/-- **Comparison.**  A comparison of trees whose `eq` outcome means equality answers `eq` on the
read-backs of two nodes in range of an interning store exactly when they are the same node. -/
theorem cmp_readback_eq_iff {s : Store L} (hs : Interning s) (cmp : Tree L → Tree L → Ordering)
    (hcmp : ∀ a b, cmp a b = .eq ↔ a = b) {i j : Nat} (hi : i < s.length) (hj : j < s.length) :
    cmp (readback s i) (readback s j) = .eq ↔ i = j :=
  (hcmp _ _).trans (interning_eq_iff hs hi hj)

/-- **Equality judgment.**  The flag computed by equality of ids is the flag computed by equality
of read-backs. -/
theorem decide_eq_readback [DecidableEq L] {s : Store L} (hs : Interning s) {i j : Nat}
    (hi : i < s.length) (hj : j < s.length) :
    decide (i = j) = decide (readback s i = readback s j) :=
  decide_eq_decide.mpr (interning_eq_iff hs hi hj).symm

/-- **Equality judgment through a comparison.**  The flag computed by equality of ids is the flag
`cmp a b = eq` computed on the read-backs. -/
theorem decide_eq_cmp_readback {s : Store L} (hs : Interning s)
    (cmp : Tree L → Tree L → Ordering) (hcmp : ∀ a b, cmp a b = .eq ↔ a = b) {i j : Nat}
    (hi : i < s.length) (hj : j < s.length) :
    decide (i = j) = decide (cmp (readback s i) (readback s j) = .eq) :=
  decide_eq_decide.mpr (cmp_readback_eq_iff hs cmp hcmp hi hj).symm

end Comparison

/-! ## Names -/

/-- A name as `hk_name_intern` stores it: its bytes, a node with no children. -/
def nameNode (b : List UInt8) : Node (List UInt8) := ⟨b, []⟩

/-- **Names.**  In an interning store, two names in range have equal bytes exactly when they have
the same id. -/
theorem names_eq_iff {s : Store (List UInt8)} (hs : Interning s) {i j : Nat} (hi : i < s.length)
    (hj : j < s.length) (hi₀ : s[i].kids = []) (hj₀ : s[j].kids = []) :
    s[i].label = s[j].label ↔ i = j := by
  have h₁ := readback_eq_node hi (by simp [hi₀])
  have h₂ := readback_eq_node hj (by simp [hj₀])
  rw [hi₀, List.map_nil] at h₁
  rw [hj₀, List.map_nil] at h₂
  rw [← interning_eq_iff hs hi hj, h₁, h₂]
  exact ⟨fun h => h ▸ rfl, fun h => (Tree.node.inj h).1⟩

/-- The store of names built by interning the byte strings `bs` in order, from the empty
store. -/
def nameStore (bs : List (List UInt8)) : Store (List UInt8) := run [] (bs.map nameNode)

/-- A store of names has no children anywhere. -/
theorem kids_nameStore (bs : List (List UInt8)) {i : Nat} (hi : i < (nameStore bs).length) :
    (nameStore bs)[i].kids = [] := by
  rcases mem_run (List.getElem_mem hi) with h | h
  · exact absurd h List.not_mem_nil
  · obtain ⟨b, -, hb⟩ := List.mem_map.mp h
    rw [← hb]
    rfl

/-- Every store of names built by interning is an interning store. -/
theorem interning_nameStore (bs : List (List UInt8)) : Interning (nameStore bs) :=
  interning_run_nil fun m hm k hk => by
    simp only [List.getElem_map, nameNode, List.not_mem_nil] at hk

/-- **Names, every run.**  In a store of names built by interning, two ids in range name equal bytes
exactly when they are equal. -/
theorem nameStore_eq_iff (bs : List (List UInt8)) {i j : Nat} (hi : i < (nameStore bs).length)
    (hj : j < (nameStore bs).length) :
    (nameStore bs)[i].label = (nameStore bs)[j].label ↔ i = j :=
  names_eq_iff (interning_nameStore bs) hi hj (kids_nameStore bs hi) (kids_nameStore bs hj)

/-! ## HOL types and terms -/

/-- The label of a node of the native kernel's tables of types and terms. -/
inductive HolLabel
  /-- `HOL_TY_VAR`: a type variable; no children. -/
  | tyvar (name : List UInt8)
  /-- `HOL_TY_APP`: a type operator; the children are its arguments. -/
  | tyapp (name : List UInt8)
  /-- `HOL_TM_VAR`: a variable; the child is its type. -/
  | var (name : List UInt8)
  /-- `HOL_TM_CONST`: a constant; the child is its type. -/
  | const (name : List UInt8)
  /-- `HOL_TM_COMB`: an application; the children are the function and the argument. -/
  | comb
  /-- `HOL_TM_ABS`: an abstraction; the children are the variable and the body. -/
  | abs
  deriving DecidableEq, Repr, Inhabited

/-- `hk_ty_var`. -/
def tyVar (s : Store HolLabel) (name : List UInt8) : Store HolLabel × Nat :=
  intern s ⟨.tyvar name, []⟩

/-- `hk_ty_app`. -/
def tyApp (s : Store HolLabel) (name : List UInt8) (args : List Nat) : Store HolLabel × Nat :=
  intern s ⟨.tyapp name, args⟩

/-- `hk_tm_var`. -/
def tmVar (s : Store HolLabel) (name : List UInt8) (ty : Nat) : Store HolLabel × Nat :=
  intern s ⟨.var name, [ty]⟩

/-- `hk_tm_const`. -/
def tmConst (s : Store HolLabel) (name : List UInt8) (ty : Nat) : Store HolLabel × Nat :=
  intern s ⟨.const name, [ty]⟩

/-- `hk_tm_comb`: `node_term` with kind `HOL_TM_COMB`. -/
def tmComb (s : Store HolLabel) (f x : Nat) : Store HolLabel × Nat :=
  intern s ⟨.comb, [f, x]⟩

/-- `hk_tm_abs`: `node_term` with kind `HOL_TM_ABS`. -/
def tmAbs (s : Store HolLabel) (v b : Nat) : Store HolLabel × Nat :=
  intern s ⟨.abs, [v, b]⟩

/-- **HOL types and terms.**  In an interning store of types and terms, two nodes in range read
back as the same type or term exactly when they are the same node. -/
theorem hol_interning_eq_iff {s : Store HolLabel} (hs : Interning s) {i j : Nat}
    (hi : i < s.length) (hj : j < s.length) : readback s i = readback s j ↔ i = j :=
  interning_eq_iff hs hi hj

/-! ## The id tables

The module keeps tables from ids to cells: a binary trie keyed by the digits of the id, least
significant first, and the next free id.  The native tables are arrays updated in place.  Below,
the module's rules are transcribed one Lean equation per rule (`cn` is the cell `c-none`, the
other cells are left abstract); the native array is a list of optional cells (`none`: no cell was
ever stored there) with the next id; and its read-back is the trie characterized by
`IsReadback`: its nodes are the union of the digit paths of the stored ids, a stored id's own node
holds its cell, and every other node holds `c-none`.  That trie exists (`isReadback_rbTrie`) and
is unique (`IsReadback.unique`), and the module's operations commute with the read-back
(`trieGet_rbTrie`, `trieSet_rbTrie`, `rbTrie_nil`, `tableGet_readback`, `tablePut_readback`,
`tableSet_readback`, `tableNext_readback`, `emptyTable_readback`).  Numerals are read
canonically (`enc`), as the native code reads its naturals. -/

section Tables

open RuleModulePrimitives

/-- Sort `Trie` of the module, over a sort `C` of cells. -/
inductive Trie (C : Type u) : Type u
  | tleaf
  | tnode (c : C) (t0 t1 : Trie C)
  deriving DecidableEq, Repr

/-- Sort `Table` of the module: `table(next, t)`. -/
structure Table (C : Type u) : Type u where
  next : BNat
  trie : Trie C
  deriving DecidableEq, Repr

variable {C : Type u}

/-! ### The rules -/

/-- `"trie-get-*"`. -/
def trieGet (cn : C) : Trie C → BNat → C
  | .tleaf, _ => cn                                    -- "trie-get-leaf"
  | .tnode c _ _, .nz => c                             -- "trie-get-z"
  | .tnode _ t0 _, .nb0 n =>                           -- "trie-get-0"
    let r := trieGet cn t0 n
    r
  | .tnode _ _ t1, .nb1 n =>                           -- "trie-get-1"
    let r := trieGet cn t1 n
    r

/-- `"trie-set-*"`. -/
def trieSet (cn : C) : Trie C → BNat → C → Trie C
  | .tleaf, .nz, c => .tnode c .tleaf .tleaf           -- "trie-set-leaf-z"
  | .tleaf, .nb0 n, c =>                               -- "trie-set-leaf-0"
    let t := trieSet cn .tleaf n c
    .tnode cn t .tleaf
  | .tleaf, .nb1 n, c =>                               -- "trie-set-leaf-1"
    let t := trieSet cn .tleaf n c
    .tnode cn .tleaf t
  | .tnode _ t0 t1, .nz, c => .tnode c t0 t1           -- "trie-set-node-z"
  | .tnode c0 t0 t1, .nb0 n, c =>                      -- "trie-set-node-0"
    let t := trieSet cn t0 n c
    .tnode c0 t t1
  | .tnode c0 t0 t1, .nb1 n, c =>                      -- "trie-set-node-1"
    let t := trieSet cn t1 n c
    .tnode c0 t0 t

/-- `"table-get"`. -/
def tableGet (cn : C) : Table C → BNat → C
  | ⟨_, t⟩, n =>
    let r := trieGet cn t n
    r

/-- `"table-put"`. -/
def tablePut (cn : C) : Table C → C → Table C
  | ⟨next, t⟩, c =>
    let t2 := trieSet cn t next c
    let n2 := natInc next
    ⟨n2, t2⟩

/-- `"table-set"`. -/
def tableSet (cn : C) : Table C → BNat → C → Table C
  | ⟨next, t⟩, n, c =>
    let t2 := trieSet cn t n c
    ⟨next, t2⟩

/-- `"table-next"`. -/
def tableNext : Table C → BNat
  | ⟨next, _⟩ => next

/-- `"empty-table"`. -/
def emptyTable : Table C := ⟨.nz, .tleaf⟩

/-! ### Nodes and paths -/

/-- The digit path of `k` is a prefix of the digit path of `m`. -/
inductive PathPrefix : BNat → BNat → Prop
  | nz (m : BNat) : PathPrefix .nz m
  | nb0 {k m : BNat} : PathPrefix k m → PathPrefix (.nb0 k) (.nb0 m)
  | nb1 {k m : BNat} : PathPrefix k m → PathPrefix (.nb1 k) (.nb1 m)

/-- `t.Has k`: the trie `t` has a node at the digit path of `k`. -/
inductive Trie.Has : Trie C → BNat → Prop
  | nz {c : C} {t0 t1 : Trie C} : Has (.tnode c t0 t1) .nz
  | nb0 {c : C} {t0 t1 : Trie C} {k : BNat} : Has t0 k → Has (.tnode c t0 t1) (.nb0 k)
  | nb1 {c : C} {t0 t1 : Trie C} {k : BNat} : Has t1 k → Has (.tnode c t0 t1) (.nb1 k)

@[simp] theorem Trie.not_has_tleaf (k : BNat) : ¬ (Trie.tleaf : Trie C).Has k := nofun

@[simp] theorem Trie.has_tnode_nz {c : C} {t0 t1 : Trie C} : (Trie.tnode c t0 t1).Has .nz := .nz

@[simp] theorem Trie.has_tnode_nb0 {c : C} {t0 t1 : Trie C} {k : BNat} :
    (Trie.tnode c t0 t1).Has (.nb0 k) ↔ t0.Has k :=
  ⟨fun | .nb0 h => h, .nb0⟩

@[simp] theorem Trie.has_tnode_nb1 {c : C} {t0 t1 : Trie C} {k : BNat} :
    (Trie.tnode c t0 t1).Has (.nb1 k) ↔ t1.Has k :=
  ⟨fun | .nb1 h => h, .nb1⟩

@[simp] theorem pathPrefix_nz (m : BNat) : PathPrefix .nz m := .nz m

theorem pathPrefix_refl : ∀ k : BNat, PathPrefix k k
  | .nz => .nz _
  | .nb0 k => .nb0 (pathPrefix_refl k)
  | .nb1 k => .nb1 (pathPrefix_refl k)

@[simp] theorem pathPrefix_nb0_iff {k : BNat} {m : BNat} :
    PathPrefix (.nb0 k) m ↔ ∃ m', m = .nb0 m' ∧ PathPrefix k m' :=
  ⟨fun | .nb0 h => ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ .nb0 h⟩

@[simp] theorem pathPrefix_nb1_iff {k : BNat} {m : BNat} :
    PathPrefix (.nb1 k) m ↔ ∃ m', m = .nb1 m' ∧ PathPrefix k m' :=
  ⟨fun | .nb1 h => ⟨_, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ .nb1 h⟩

/-- `"trie-get"` after `"trie-set"`: the cell set at its own key, the old answer elsewhere. -/
theorem trieGet_trieSet (cn : C) (t : Trie C) (k k' : BNat) (c : C) :
    trieGet cn (trieSet cn t k c) k' = if k' = k then c else trieGet cn t k' := by
  induction k generalizing t k' with
  | nz => cases t <;> cases k' <;> simp [trieSet, trieGet]
  | nb0 n ih => cases t <;> cases k' <;> simp [trieSet, trieGet, ih]
  | nb1 n ih => cases t <;> cases k' <;> simp [trieSet, trieGet, ih]

/-- The nodes after `"trie-set"`: the old ones and the path of the key. -/
theorem has_trieSet (cn : C) (t : Trie C) (k k' : BNat) (c : C) :
    (trieSet cn t k c).Has k' ↔ t.Has k' ∨ PathPrefix k' k := by
  induction k generalizing t k' with
  | nz => cases t <;> cases k' <;> simp [trieSet]
  | nb0 n ih => cases t <;> cases k' <;> simp [trieSet, ih]
  | nb1 n ih => cases t <;> cases k' <;> simp [trieSet, ih]

/-- Two tries with the same nodes and the same answers are equal. -/
theorem Trie.ext_has_get (cn : C) :
    ∀ {t t' : Trie C}, (∀ k, t.Has k ↔ t'.Has k) → (∀ k, trieGet cn t k = trieGet cn t' k) →
      t = t'
  | .tleaf, .tleaf, _, _ => rfl
  | .tleaf, .tnode _ _ _, h, _ => absurd ((h .nz).mpr .nz) (Trie.not_has_tleaf _)
  | .tnode _ _ _, .tleaf, h, _ => absurd ((h .nz).mp .nz) (Trie.not_has_tleaf _)
  | .tnode c t0 t1, .tnode c' t0' t1', h, g => by
    have hc : c = c' := g .nz
    have h0 : t0 = t0' := Trie.ext_has_get cn
      (fun k => by simpa using h (.nb0 k)) (fun k => g (.nb0 k))
    have h1 : t1 = t1' := Trie.ext_has_get cn
      (fun k => by simpa using h (.nb1 k)) (fun k => g (.nb1 k))
    rw [hc, h0, h1]

/-! ### The native tables and their read-back -/

/-- A native table: its cells by id, `none` where no cell was ever stored, and the next id. -/
structure NTable (C : Type u) : Type u where
  cells : List (Option C)
  next : Nat
  deriving DecidableEq, Repr

/-- `tab_store`: store a cell at an id, the array growing with empty slots as needed. -/
def store : List (Option C) → Nat → C → List (Option C)
  | [], 0, c => [some c]
  | [], i + 1, c => none :: store [] i c
  | _ :: xs, 0, c => some c :: xs
  | x :: xs, i + 1, c => x :: store xs i c

/-- `holb_table_get`: the cell stored at the id, `c-none` where there is none. -/
def NTable.get (cn : C) (t : NTable C) (i : Nat) : C := (t.cells[i]?.join).getD cn

/-- `holb_table_put`: store at the next id, and advance it. -/
def NTable.put (t : NTable C) (c : C) : NTable C := ⟨store t.cells t.next c, t.next + 1⟩

/-- `holb_table_set`: store at the given id. -/
def NTable.set (t : NTable C) (i : Nat) (c : C) : NTable C := ⟨store t.cells i c, t.next⟩

/-- `holb_empty_table`. -/
def NTable.empty : NTable C := ⟨[], 0⟩

/-- **The read-back of the cells to a trie.**  Its nodes are the union of the digit paths of the
stored ids; a stored id's own node holds its cell; every other node holds `c-none`. -/
structure IsReadback (cn : C) (cells : List (Option C)) (t : Trie C) : Prop where
  /-- The nodes are the prefixes of the digit paths of the stored ids. -/
  has_iff : ∀ k, t.Has k ↔ ∃ i c, cells[i]?.join = some c ∧ PathPrefix k (enc i)
  /-- The node of an id holds the cell stored there, `c-none` if there is none. -/
  get_enc : ∀ i, trieGet cn t (enc i) = (cells[i]?.join).getD cn
  /-- A path that is no id holds `c-none`. -/
  get_of_not_canon : ∀ k, ¬ Canon k → trieGet cn t k = cn

/-- The read-back is unique. -/
theorem IsReadback.unique {cn : C} {cells : List (Option C)} {t t' : Trie C}
    (h : IsReadback cn cells t) (h' : IsReadback cn cells t') : t = t' :=
  Trie.ext_has_get cn (fun k => (h.has_iff k).trans (h'.has_iff k).symm) fun k => by
    by_cases hk : Canon k
    · rw [← enc_val hk, h.get_enc, h'.get_enc]
    · rw [h.get_of_not_canon k hk, h'.get_of_not_canon k hk]

theorem enc_injective {i j : Nat} (h : enc i = enc j) : i = j := by
  rw [← val_enc i, h, val_enc]

theorem join_getElem?_store :
    ∀ (cells : List (Option C)) (i : Nat) (c : C) (j : Nat),
      ((store cells i c)[j]?).join = if j = i then some c else (cells[j]?).join
  | [], 0, _, 0 => rfl
  | [], 0, _, _ + 1 => rfl
  | _ :: _, 0, _, 0 => rfl
  | _ :: _, 0, _, _ + 1 => rfl
  | [], _ + 1, _, 0 => rfl
  | _ :: _, _ + 1, _, 0 => rfl
  | [], i + 1, c, j + 1 => by
    show ((store [] i c)[j]?).join = _
    rw [join_getElem?_store [] i c j]
    by_cases h : j = i
    · rw [if_pos h, if_pos (congrArg (· + 1) h)]
    · rw [if_neg h, if_neg (fun e => h (Nat.succ.inj e))]
      rfl
  | _ :: xs, i + 1, c, j + 1 => by
    show ((store xs i c)[j]?).join = _
    rw [join_getElem?_store xs i c j]
    by_cases h : j = i
    · rw [if_pos h, if_pos (congrArg (· + 1) h)]
    · rw [if_neg h, if_neg (fun e => h (Nat.succ.inj e))]
      rfl

theorem store_length (cells : List (Option C)) (c : C) :
    store cells cells.length c = cells ++ [some c] := by
  induction cells with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons, store, ih, List.cons_append]

theorem join_getElem?_append_none (cells : List (Option C)) (j : Nat) :
    ((cells ++ [none])[j]?).join = (cells[j]?).join := by
  rcases Nat.lt_or_ge j cells.length with h | h
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right h, List.getElem?_eq_none h]
    cases j - cells.length <;> rfl

theorem isReadback_nil (cn : C) : IsReadback cn [] .tleaf :=
  ⟨fun k => by simp, fun i => by simp [trieGet], fun k _ => by simp [trieGet]⟩

theorem IsReadback.append_none {cn : C} {cells : List (Option C)} {t : Trie C}
    (h : IsReadback cn cells t) : IsReadback cn (cells ++ [none]) t :=
  ⟨by simpa only [join_getElem?_append_none] using h.has_iff,
    by simpa only [join_getElem?_append_none] using h.get_enc, h.get_of_not_canon⟩

/-- `"trie-set"` at an id turns the read-back of the cells into the read-back of the cells with
that id stored. -/
theorem IsReadback.trieSet {cn : C} {cells : List (Option C)} {t : Trie C}
    (h : IsReadback cn cells t) (i : Nat) (c : C) :
    IsReadback cn (store cells i c) (trieSet cn t (enc i) c) where
  has_iff k := by
    rw [has_trieSet, h.has_iff]
    simp only [join_getElem?_store]
    constructor
    · rintro (⟨j, c', hj, hk⟩ | hk)
      · by_cases hji : j = i
        · exact ⟨i, c, by simp, hji ▸ hk⟩
        · exact ⟨j, c', by simp [hji, hj], hk⟩
      · exact ⟨i, c, by simp, hk⟩
    · rintro ⟨j, c', hj, hk⟩
      by_cases hji : j = i
      · exact .inr (hji ▸ hk)
      · exact .inl ⟨j, c', by simpa [hji] using hj, hk⟩
  get_enc j := by
    rw [trieGet_trieSet, h.get_enc, join_getElem?_store]
    by_cases hji : j = i
    · simp [hji]
    · have hne : enc j ≠ enc i := fun e => hji (enc_injective e)
      simp [hji, hne]
  get_of_not_canon k hk := by
    have hne : k ≠ enc i := fun e => hk (e ▸ canon_enc i)
    rw [trieGet_trieSet, if_neg hne, h.get_of_not_canon k hk]

/-- The trie of the cells listed last first: each stored cell `"trie-set"` at its id. -/
def rbRev (cn : C) : List (Option C) → Trie C
  | [] => .tleaf
  | none :: r => rbRev cn r
  | some c :: r => trieSet cn (rbRev cn r) (enc r.length) c

/-- The trie of the cells (`tab_trie`). -/
def rbTrie (cn : C) (cells : List (Option C)) : Trie C := rbRev cn cells.reverse

theorem isReadback_rbRev (cn : C) : ∀ r : List (Option C), IsReadback cn r.reverse (rbRev cn r)
  | [] => isReadback_nil cn
  | none :: r => by
    rw [List.reverse_cons]
    exact (isReadback_rbRev cn r).append_none
  | some c :: r => by
    rw [List.reverse_cons, ← store_length, List.length_reverse]
    exact (isReadback_rbRev cn r).trieSet r.length c

/-- **The read-back exists**: `rbTrie` builds it. -/
theorem isReadback_rbTrie (cn : C) (cells : List (Option C)) :
    IsReadback cn cells (rbTrie cn cells) := by
  have h := isReadback_rbRev cn cells.reverse
  rwa [List.reverse_reverse] at h

/-- `holr_table_readback`: the table as module data. -/
def NTable.readback (cn : C) (t : NTable C) : Table C := ⟨enc t.next, rbTrie cn t.cells⟩

/-! ### The operations commute with the read-back -/

/-- **`"trie-get"`** on the read-back is the native lookup. -/
theorem trieGet_rbTrie (cn : C) (cells : List (Option C)) (i : Nat) :
    trieGet cn (rbTrie cn cells) (enc i) = (cells[i]?.join).getD cn :=
  (isReadback_rbTrie cn cells).get_enc i

/-- **`"trie-set"`** on the read-back is the read-back of the native store. -/
theorem trieSet_rbTrie (cn : C) (cells : List (Option C)) (i : Nat) (c : C) :
    trieSet cn (rbTrie cn cells) (enc i) c = rbTrie cn (store cells i c) :=
  ((isReadback_rbTrie cn cells).trieSet i c).unique (isReadback_rbTrie cn _)

/-- The read-back of the empty array is `tleaf`. -/
theorem rbTrie_nil (cn : C) : rbTrie cn ([] : List (Option C)) = .tleaf := rfl

/-- **`"table-get"`** commutes with the read-back. -/
theorem tableGet_readback (cn : C) (t : NTable C) (i : Nat) :
    tableGet cn (t.readback cn) (enc i) = t.get cn i :=
  trieGet_rbTrie cn t.cells i

/-- **`"table-put"`** commutes with the read-back. -/
theorem tablePut_readback (cn : C) (t : NTable C) (c : C) :
    tablePut cn (t.readback cn) c = (t.put c).readback cn := by
  show (⟨natInc (enc t.next), trieSet cn (rbTrie cn t.cells) (enc t.next) c⟩ : Table C) =
    ⟨enc (t.next + 1), rbTrie cn (store t.cells t.next c)⟩
  rw [trieSet_rbTrie, enc_succ]

/-- **`"table-set"`** commutes with the read-back. -/
theorem tableSet_readback (cn : C) (t : NTable C) (i : Nat) (c : C) :
    tableSet cn (t.readback cn) (enc i) c = (t.set i c).readback cn := by
  show (⟨enc t.next, trieSet cn (rbTrie cn t.cells) (enc i) c⟩ : Table C) =
    ⟨enc t.next, rbTrie cn (store t.cells i c)⟩
  rw [trieSet_rbTrie]

/-- **`"table-next"`** commutes with the read-back. -/
theorem tableNext_readback (cn : C) (t : NTable C) : tableNext (t.readback cn) = enc t.next :=
  rfl

/-- **`"empty-table"`** is the read-back of the empty native table. -/
theorem emptyTable_readback (cn : C) : (NTable.empty : NTable C).readback cn = emptyTable :=
  rfl

end Tables

/-! ## Binding the module's equality judgments

The module's equality judgments `"str-eq"`, `"ty-eq"`, `"tm-eq"` ask whether a structural
comparison answers `eq`.  The comparisons answer `eq` exactly on equal arguments (`cmpType_eq_iff`,
`cmpTypes_eq_iff`, `cmpLeaf_eq_iff`, `cmpTerm_eq_iff`, and `cmpStr_eq_eq_iff` of the primitives),
so each judgment answers `yes` exactly on equal arguments (`tyEq_eq_yes_iff`, `tmEq_eq_yes_iff`,
`tmsEq_eq_yes_iff`).  A read-back tree of the store of types and terms is decoded as a type
(`decodeTy`) or a term (`decodeTerm`) of the module, names going from bytes to the module's
names by `encodeStr`; every tree the decoding accepts is the tree of its decoding
(`eq_treeOfTy`, `eq_treeOfTerm`), so the decoding is injective on them (`decodeTy_injective`,
`decodeTerm_injective`).  Together with the law of interning stores, the judgments on the decoded
nodes answer `yes` exactly when the nodes are the same node (`tyEq_binding`, `tmEq_binding`,
`strEq_binding`). -/

section Binding

open RuleModulePrimitives RuleModuleComparisonLaws

/-! ### Equality judgments answer `yes` exactly on equal arguments -/

theorem then_eq_eq_iff {o p : RuleModulePrimitives.Ord} : o.then p = .eq ↔ o = .eq ∧ p = .eq := by
  cases o <;> cases p <;> decide

theorem ordIsEq_eq_yes_iff {o : RuleModulePrimitives.Ord} : ordIsEq o = .yes ↔ o = .eq := by
  cases o <;> decide

theorem cmpTypeK_eq_then (o : RuleModulePrimitives.Ord) (a b : Tys) :
    cmpTypeK o a b = o.then (cmpTypes a b) := by
  cases o <;> rfl

theorem cmpTypesK_eq_then (o : RuleModulePrimitives.Ord) (a b : Tys) :
    cmpTypesK o a b = o.then (cmpTypes a b) := by
  cases o <;> rfl

theorem cmpLeafK_eq_then (o : RuleModulePrimitives.Ord) (a b : Ty) :
    cmpLeafK o a b = o.then (cmpType a b) := by
  cases o <;> rfl

theorem cmpTermK_eq_then (o : RuleModulePrimitives.Ord) (a b : Term) :
    cmpTermK o a b = o.then (cmpTerm a b) := by
  cases o <;> rfl

mutual

/-- `"cmp-type"` answers `eq` exactly on equal types. -/
theorem cmpType_eq_iff : ∀ a b : Ty, cmpType a b = .eq ↔ a = b
  | .Tyvar x, .Tyvar y => by
    rw [show cmpType (.Tyvar x) (.Tyvar y) = cmpStr x y from rfl, cmpStr_eq_eq_iff, Ty.Tyvar.injEq]
  | .Tyvar _, .Tyapp _ _ => ⟨nofun, nofun⟩
  | .Tyapp _ _, .Tyvar _ => ⟨nofun, nofun⟩
  | .Tyapp n1 a1, .Tyapp n2 a2 => by
    rw [cmpType_Tyapp_Tyapp, cmpTypeK_eq_then, then_eq_eq_iff, cmpStr_eq_eq_iff,
      cmpTypes_eq_iff a1 a2, Ty.Tyapp.injEq]
termination_by structural a => a

/-- `"cmp-types"` answers `eq` exactly on equal lists of types. -/
theorem cmpTypes_eq_iff : ∀ l m : Tys, cmpTypes l m = .eq ↔ l = m
  | .tynil, .tynil => ⟨fun _ => rfl, fun _ => rfl⟩
  | .tynil, .tycons _ _ => ⟨nofun, nofun⟩
  | .tycons _ _, .tynil => ⟨nofun, nofun⟩
  | .tycons x xs, .tycons y ys => by
    rw [cmpTypes_tycons_tycons, cmpTypesK_eq_then, then_eq_eq_iff, cmpType_eq_iff x y,
      cmpTypes_eq_iff xs ys, Tys.tycons.injEq]
termination_by structural l => l

end

/-- `"ty-eq"` answers `yes` exactly on equal types. -/
theorem tyEq_eq_yes_iff (a b : Ty) : tyEq a b = .yes ↔ a = b :=
  ordIsEq_eq_yes_iff.trans (cmpType_eq_iff a b)

/-- `"cmp-leaf"` answers `eq` exactly on equal names with equal types. -/
theorem cmpLeaf_eq_iff (n1 : Str) (t1 : Ty) (n2 : Str) (t2 : Ty) :
    cmpLeaf n1 t1 n2 t2 = .eq ↔ n1 = n2 ∧ t1 = t2 := by
  show cmpLeafK (cmpStr n1 n2) t1 t2 = .eq ↔ _
  rw [cmpLeafK_eq_then, then_eq_eq_iff, cmpStr_eq_eq_iff, cmpType_eq_iff]

/-- `"cmp-term"` answers `eq` exactly on equal terms. -/
theorem cmpTerm_eq_iff : ∀ a b : Term, cmpTerm a b = .eq ↔ a = b
  | .Var n1 t1, .Var n2 t2 => by
    rw [show cmpTerm (.Var n1 t1) (.Var n2 t2) = cmpLeaf n1 t1 n2 t2 from rfl, cmpLeaf_eq_iff,
      Term.Var.injEq]
  | .Const n1 t1, .Const n2 t2 => by
    rw [show cmpTerm (.Const n1 t1) (.Const n2 t2) = cmpLeaf n1 t1 n2 t2 from rfl, cmpLeaf_eq_iff,
      Term.Const.injEq]
  | .Comb f1 x1, .Comb f2 x2 => by
    rw [cmpTerm_Comb_Comb, cmpTermK_eq_then, then_eq_eq_iff, cmpTerm_eq_iff f1 f2,
      cmpTerm_eq_iff x1 x2, Term.Comb.injEq]
  | .Abs v1 b1, .Abs v2 b2 => by
    rw [cmpTerm_Abs_Abs, cmpTermK_eq_then, then_eq_eq_iff, cmpTerm_eq_iff v1 v2,
      cmpTerm_eq_iff b1 b2, Term.Abs.injEq]
  | .Var _ _, .Const _ _ | .Var _ _, .Comb _ _ | .Var _ _, .Abs _ _
  | .Const _ _, .Var _ _ | .Const _ _, .Comb _ _ | .Const _ _, .Abs _ _
  | .Comb _ _, .Var _ _ | .Comb _ _, .Const _ _ | .Comb _ _, .Abs _ _
  | .Abs _ _, .Var _ _ | .Abs _ _, .Const _ _ | .Abs _ _, .Comb _ _ => ⟨nofun, nofun⟩
termination_by structural a => a

/-- `"tm-eq"` answers `yes` exactly on equal terms. -/
theorem tmEq_eq_yes_iff (a b : Term) : tmEq a b = .yes ↔ a = b :=
  ordIsEq_eq_yes_iff.trans (cmpTerm_eq_iff a b)

/-- `"tms-eq"` answers `yes` exactly on equal lists of terms. -/
theorem tmsEq_eq_yes_iff : ∀ l m : Tms, tmsEq l m = .yes ↔ l = m
  | .tmnil, .tmnil => ⟨fun _ => rfl, fun _ => rfl⟩
  | .tmnil, .tmcons _ _ => ⟨nofun, nofun⟩
  | .tmcons _ _, .tmnil => ⟨nofun, nofun⟩
  | .tmcons x xs, .tmcons y ys => by
    rw [tmsEq_tmcons_tmcons, Tms.tmcons.injEq, ← tmEq_eq_yes_iff x y, ← tmsEq_eq_yes_iff xs ys]
    cases tmEq x y with
    | no => exact ⟨nofun, fun h => nomatch h.1⟩
    | yes => exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
termination_by structural l => l

/-! ### Decoding read-backs as the module's types and terms -/

mutual

/-- A read-back tree as a type of the module, if it is one. -/
def decodeTy : Tree HolLabel → Option Ty
  | .node (.tyvar n) [] => some (.Tyvar (encodeStr n))
  | .node (.tyapp n) args =>
    match decodeTys args with
    | some xs => some (.Tyapp (encodeStr n) xs)
    | none => none
  | _ => none
termination_by structural t => t

/-- A list of read-back trees as a list of types, if they all are types. -/
def decodeTys : List (Tree HolLabel) → Option Tys
  | [] => some .tynil
  | a :: as =>
    match decodeTy a, decodeTys as with
    | some x, some xs => some (.tycons x xs)
    | _, _ => none
termination_by structural l => l

end

mutual

/-- A read-back tree as a term of the module, if it is one. -/
def decodeTerm : Tree HolLabel → Option Term
  | .node (.var n) [ty] => (decodeTy ty).map (.Var (encodeStr n))
  | .node (.const n) [ty] => (decodeTy ty).map (.Const (encodeStr n))
  | .node .comb kids =>
    match decodeTerms kids with
    | some [f, x] => some (.Comb f x)
    | _ => none
  | .node .abs kids =>
    match decodeTerms kids with
    | some [v, b] => some (.Abs v b)
    | _ => none
  | _ => none
termination_by structural t => t

/-- A list of read-back trees as a list of terms, if they all are terms. -/
def decodeTerms : List (Tree HolLabel) → Option (List Term)
  | [] => some []
  | a :: as =>
    match decodeTerm a, decodeTerms as with
    | some x, some xs => some (x :: xs)
    | _, _ => none
termination_by structural l => l

end

mutual

/-- The tree of a type of the module. -/
def treeOfTy : Ty → Tree HolLabel
  | .Tyvar n => .node (.tyvar (decodeStr n)) []
  | .Tyapp n args => .node (.tyapp (decodeStr n)) (treeOfTys args)
termination_by structural t => t

/-- The trees of a list of types. -/
def treeOfTys : Tys → List (Tree HolLabel)
  | .tynil => []
  | .tycons x xs => treeOfTy x :: treeOfTys xs
termination_by structural l => l

end

/-- The tree of a term of the module. -/
def treeOfTerm : Term → Tree HolLabel
  | .Var n ty => .node (.var (decodeStr n)) [treeOfTy ty]
  | .Const n ty => .node (.const (decodeStr n)) [treeOfTy ty]
  | .Comb f x => .node .comb [treeOfTerm f, treeOfTerm x]
  | .Abs v b => .node .abs [treeOfTerm v, treeOfTerm b]

mutual

/-- Every type is decoded from its tree. -/
theorem decodeTy_treeOfTy : ∀ x : Ty, decodeTy (treeOfTy x) = some x
  | .Tyvar n => by
    show some (Ty.Tyvar (encodeStr (decodeStr n))) = _
    rw [encodeStr_decodeStr]
  | .Tyapp n args => by
    show (match decodeTys (treeOfTys args) with
      | some xs => some (Ty.Tyapp (encodeStr (decodeStr n)) xs)
      | none => none) = _
    rw [decodeTys_treeOfTys args, encodeStr_decodeStr]
termination_by structural x => x

theorem decodeTys_treeOfTys : ∀ xs : Tys, decodeTys (treeOfTys xs) = some xs
  | .tynil => rfl
  | .tycons x xs => by
    show (match decodeTy (treeOfTy x), decodeTys (treeOfTys xs) with
      | some x, some xs => some (Tys.tycons x xs)
      | _, _ => none) = _
    rw [decodeTy_treeOfTy x, decodeTys_treeOfTys xs]
termination_by structural xs => xs

end

/-- Every term is decoded from its tree. -/
theorem decodeTerm_treeOfTerm : ∀ x : Term, decodeTerm (treeOfTerm x) = some x
  | .Var n ty => by
    show (decodeTy (treeOfTy ty)).map (Term.Var (encodeStr (decodeStr n))) = _
    rw [decodeTy_treeOfTy, encodeStr_decodeStr]
    rfl
  | .Const n ty => by
    show (decodeTy (treeOfTy ty)).map (Term.Const (encodeStr (decodeStr n))) = _
    rw [decodeTy_treeOfTy, encodeStr_decodeStr]
    rfl
  | .Comb f x => by
    simp only [treeOfTerm, decodeTerm, decodeTerms, decodeTerm_treeOfTerm f,
      decodeTerm_treeOfTerm x]
  | .Abs v b => by
    simp only [treeOfTerm, decodeTerm, decodeTerms, decodeTerm_treeOfTerm v,
      decodeTerm_treeOfTerm b]

mutual

/-- A tree accepted as a type is the tree of its decoding. -/
theorem eq_treeOfTy : ∀ (a : Tree HolLabel) {x : Ty}, decodeTy a = some x → a = treeOfTy x
  | .node (.tyvar n) [], x, h => by
    simp only [decodeTy, Option.some.injEq] at h
    subst h
    simp only [treeOfTy, decodeStr_encodeStr]
  | .node (.tyvar _) (_ :: _), _, h => by simp [decodeTy] at h
  | .node (.tyapp n) args, x, h => by
    simp only [decodeTy] at h
    split at h
    · rename_i xs hxs
      simp only [Option.some.injEq] at h
      subst h
      rw [treeOfTy, decodeStr_encodeStr, ← eq_treeOfTys args hxs]
    · exact absurd h nofun
  | .node (.var _) _, _, h => by simp [decodeTy] at h
  | .node (.const _) _, _, h => by simp [decodeTy] at h
  | .node .comb _, _, h => by simp [decodeTy] at h
  | .node .abs _, _, h => by simp [decodeTy] at h
termination_by structural a => a

/-- Trees accepted as a list of types are the trees of its decoding. -/
theorem eq_treeOfTys : ∀ (as : List (Tree HolLabel)) {xs : Tys}, decodeTys as = some xs →
    as = treeOfTys xs
  | [], xs, h => by
    simp only [decodeTys, Option.some.injEq] at h
    subst h
    rfl
  | a :: as, xs, h => by
    simp only [decodeTys] at h
    split at h
    · rename_i x xs' hx hxs
      simp only [Option.some.injEq] at h
      subst h
      rw [treeOfTys, ← eq_treeOfTy a hx, ← eq_treeOfTys as hxs]
    · exact absurd h nofun
termination_by structural as => as

end

mutual

/-- A tree accepted as a term is the tree of its decoding. -/
theorem eq_treeOfTerm : ∀ (a : Tree HolLabel) {x : Term}, decodeTerm a = some x → a = treeOfTerm x
  | .node (.var n) [ty], x, h => by
    simp only [decodeTerm, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [treeOfTerm, decodeStr_encodeStr, ← eq_treeOfTy ty ht]
  | .node (.const n) [ty], x, h => by
    simp only [decodeTerm, Option.map_eq_some_iff] at h
    obtain ⟨t, ht, rfl⟩ := h
    rw [treeOfTerm, decodeStr_encodeStr, ← eq_treeOfTy ty ht]
  | .node .comb kids, x, h => by
    simp only [decodeTerm] at h
    split at h
    · rename_i f y hk
      simp only [Option.some.injEq] at h
      subst h
      rw [eq_treeOfTerms kids hk]
      rfl
    · exact absurd h nofun
  | .node .abs kids, x, h => by
    simp only [decodeTerm] at h
    split at h
    · rename_i v b hk
      simp only [Option.some.injEq] at h
      subst h
      rw [eq_treeOfTerms kids hk]
      rfl
    · exact absurd h nofun
  | .node (.var _) [], _, h | .node (.var _) (_ :: _ :: _), _, h
  | .node (.const _) [], _, h | .node (.const _) (_ :: _ :: _), _, h
  | .node (.tyvar _) _, _, h | .node (.tyapp _) _, _, h => by simp [decodeTerm] at h
termination_by structural a => a

/-- Trees accepted as a list of terms are the trees of its decoding. -/
theorem eq_treeOfTerms : ∀ (as : List (Tree HolLabel)) {xs : List Term}, decodeTerms as = some xs →
    as = xs.map treeOfTerm
  | [], xs, h => by
    simp only [decodeTerms, Option.some.injEq] at h
    subst h
    rfl
  | a :: as, xs, h => by
    simp only [decodeTerms] at h
    split at h
    · rename_i x xs' hx hxs
      simp only [Option.some.injEq] at h
      subst h
      rw [List.map_cons, ← eq_treeOfTerm a hx, ← eq_treeOfTerms as hxs]
    · exact absurd h nofun
termination_by structural as => as

end

/-- The decoding of types is injective on the trees it accepts. -/
theorem decodeTy_injective {a b : Tree HolLabel} {x : Ty} (ha : decodeTy a = some x)
    (hb : decodeTy b = some x) : a = b :=
  (eq_treeOfTy a ha).trans (eq_treeOfTy b hb).symm

/-- The decoding of terms is injective on the trees it accepts. -/
theorem decodeTerm_injective {a b : Tree HolLabel} {x : Term} (ha : decodeTerm a = some x)
    (hb : decodeTerm b = some x) : a = b :=
  (eq_treeOfTerm a ha).trans (eq_treeOfTerm b hb).symm

/-! ### The binding theorems -/

/-- **`hl:ty-eq` binding.**  In an interning store of types and terms, `"ty-eq"` on the types that
two nodes in range decode to answers `yes` exactly when the nodes are the same node. -/
theorem tyEq_binding {s : Store HolLabel} (hs : Interning s) {i j : Nat} (hi : i < s.length)
    (hj : j < s.length) {a b : Ty} (ha : decodeTy (readback s i) = some a)
    (hb : decodeTy (readback s j) = some b) : tyEq a b = .yes ↔ i = j := by
  rw [tyEq_eq_yes_iff, ← hol_interning_eq_iff hs hi hj]
  constructor
  · rintro rfl
    exact decodeTy_injective ha hb
  · intro h
    rw [h, hb] at ha
    exact (Option.some.inj ha).symm

/-- **`hl:tm-eq` binding.**  In an interning store of types and terms, `"tm-eq"` on the terms that
two nodes in range decode to answers `yes` exactly when the nodes are the same node. -/
theorem tmEq_binding {s : Store HolLabel} (hs : Interning s) {i j : Nat} (hi : i < s.length)
    (hj : j < s.length) {a b : Term} (ha : decodeTerm (readback s i) = some a)
    (hb : decodeTerm (readback s j) = some b) : tmEq a b = .yes ↔ i = j := by
  rw [tmEq_eq_yes_iff, ← hol_interning_eq_iff hs hi hj]
  constructor
  · rintro rfl
    exact decodeTerm_injective ha hb
  · intro h
    rw [h, hb] at ha
    exact (Option.some.inj ha).symm

/-- **`hl:str-eq` binding.**  In an interning store of names, `"str-eq"` on the module's names of
two names in range answers `yes` exactly when they have the same id. -/
theorem strEq_binding {s : Store (List UInt8)} (hs : Interning s) {i j : Nat} (hi : i < s.length)
    (hj : j < s.length) (hi₀ : s[i].kids = []) (hj₀ : s[j].kids = []) :
    strEq (encodeStr s[i].label) (encodeStr s[j].label) = .yes ↔ i = j := by
  rw [strEq_refines, decodeStr_encodeStr, decodeStr_encodeStr]
  exact names_eq_iff hs hi hj hi₀ hj₀

end Binding

/-! ## Names held as ids

The native nodes of types and terms hold names as ids into the table of names, where the labels
above hold the bytes.  Relabeling a store by a map that separates its labels keeps the invariant
(`interning_relabel`), and read-back commutes with relabeling (`readback_relabel`).  Resolving the
name ids of the native labels (`HolLabelId`) in an interning table of names separates labels whose
ids are in range (`resolve_eq_iff`), so the store with names as ids and the store with names as
bytes intern alike and read back alike (`hol_names_as_ids`). -/

section NamesAsIds

/-- A node with its label mapped by `f`. -/
def Node.relabel {L : Type u} {M : Type v} (f : L → M) (n : Node L) : Node M := ⟨f n.label, n.kids⟩

mutual

/-- A tree with its labels mapped by `f`. -/
def Tree.map {L : Type u} {M : Type v} (f : L → M) : Tree L → Tree M
  | .node l ts => .node (f l) (Tree.mapList f ts)
termination_by structural t => t

/-- Trees with their labels mapped by `f`. -/
def Tree.mapList {L : Type u} {M : Type v} (f : L → M) : List (Tree L) → List (Tree M)
  | [] => []
  | t :: ts => Tree.map f t :: Tree.mapList f ts
termination_by structural ts => ts

end

theorem Tree.mapList_eq_map {L : Type u} {M : Type v} (f : L → M) :
    ∀ ts : List (Tree L), Tree.mapList f ts = ts.map (Tree.map f)
  | [] => rfl
  | t :: ts => by rw [Tree.mapList, Tree.mapList_eq_map f ts, List.map_cons]

theorem Tree.map_node {L : Type u} {M : Type v} (f : L → M) (l : L) (ts : List (Tree L)) :
    Tree.map f (.node l ts) = .node (f l) (ts.map (Tree.map f)) := by
  rw [Tree.map, Tree.mapList_eq_map]

/-- Relabeling by a map that separates the labels of the store keeps the invariant. -/
theorem interning_relabel {L : Type u} {M : Type v} {s : Store L} (hs : Interning s) {f : L → M}
    (hf : ∀ (i : Nat) (hi : i < s.length) (j : Nat) (hj : j < s.length),
      f (s[i]'hi).label = f (s[j]'hj).label → (s[i]'hi).label = (s[j]'hj).label) :
    Interning (s.map (Node.relabel f)) := by
  constructor
  · intro i hi k hk
    simp only [List.getElem_map, Node.relabel] at hk
    exact hs.kids_lt i (by simpa using hi) k hk
  · intro i hi j hj hij
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map, Node.relabel, Node.mk.injEq] at hij
    exact hs.injective i hi j hj (Node.ext (hf i hi j hj hij.1) hij.2)

/-- A store whose relabeling interns interns, whatever the map. -/
theorem interning_of_relabel {L : Type u} {M : Type v} {s : Store L} {f : L → M}
    (h : Interning (s.map (Node.relabel f))) : Interning s := by
  constructor
  · intro i hi k hk
    have := h.kids_lt i (by simpa using hi) k
    simp only [List.getElem_map, Node.relabel] at this
    exact this hk
  · intro i hi j hj hij
    exact h.injective i (by simpa using hi) j (by simpa using hj)
      (by simp only [List.getElem_map, hij])

/-- Relabeling by a map that separates the labels of the store neither makes nor breaks the
invariant. -/
theorem interning_relabel_iff {L : Type u} {M : Type v} {s : Store L} {f : L → M}
    (hf : ∀ (i : Nat) (hi : i < s.length) (j : Nat) (hj : j < s.length),
      f (s[i]'hi).label = f (s[j]'hj).label → (s[i]'hi).label = (s[j]'hj).label) :
    Interning (s.map (Node.relabel f)) ↔ Interning s :=
  ⟨interning_of_relabel, fun hs => interning_relabel hs hf⟩

/-- Read-back commutes with relabeling, for a store built bottom-up. -/
theorem readback_relabel {L : Type u} {M : Type v} [Inhabited L] [Inhabited M] {s : Store L}
    (hk : ∀ (i : Nat) (hi : i < s.length), ∀ k ∈ (s[i]'hi).kids, k < i) (f : L → M) :
    ∀ m i, i < m → i < s.length →
      readback (s.map (Node.relabel f)) i = Tree.map f (readback s i)
  | 0, _, hm, _ => absurd hm (Nat.not_lt_zero _)
  | m + 1, i, hm, hi => by
    have hi' : i < (s.map (Node.relabel f)).length := by simpa using hi
    have hk' : ∀ k ∈ ((s.map (Node.relabel f))[i]'hi').kids, k < i := by
      simpa [Node.relabel] using hk i hi
    rw [readback_eq_node hi' hk', readback_eq_node hi (hk i hi), Tree.map_node, List.map_map]
    simp only [List.getElem_map, Node.relabel]
    congr 1
    exact List.map_congr_left fun k hkk =>
      readback_relabel hk f m k (by have := hk i hi k hkk; omega) (by have := hk i hi k hkk; omega)

/-- The label of a native node of a type or a term, holding names as ids into the table of
names, as the native nodes do. -/
inductive HolLabelId
  /-- `HOL_TY_VAR`, with the id of its name. -/
  | tyvar (name : Nat)
  /-- `HOL_TY_APP`, with the id of its operator's name. -/
  | tyapp (name : Nat)
  /-- `HOL_TM_VAR`, with the id of its name. -/
  | var (name : Nat)
  /-- `HOL_TM_CONST`, with the id of its name. -/
  | const (name : Nat)
  /-- `HOL_TM_COMB`. -/
  | comb
  /-- `HOL_TM_ABS`. -/
  | abs
  deriving DecidableEq, Repr, Inhabited

/-- The name id a label holds, if it holds one. -/
def HolLabelId.nameId : HolLabelId → Option Nat
  | .tyvar n | .tyapp n | .var n | .const n => some n
  | .comb | .abs => none

/-- The bytes of the name with id `n` in the table of names `ns`. -/
def nameBytes (ns : Store (List UInt8)) (n : Nat) : List UInt8 := (ns[n]?.map Node.label).getD []

/-- A label with its name id resolved to the name's bytes. -/
def resolve (ns : Store (List UInt8)) : HolLabelId → HolLabel
  | .tyvar n => .tyvar (nameBytes ns n)
  | .tyapp n => .tyapp (nameBytes ns n)
  | .var n => .var (nameBytes ns n)
  | .const n => .const (nameBytes ns n)
  | .comb => .comb
  | .abs => .abs

/-- In an interning table of names, two names in range have equal bytes exactly when they have the
same id. -/
theorem nameBytes_eq_iff {ns : Store (List UInt8)} (hns : Interning ns)
    (hleaf : ∀ x ∈ ns, x.kids = []) {n m : Nat} (hn : n < ns.length) (hm : m < ns.length) :
    nameBytes ns n = nameBytes ns m ↔ n = m := by
  simp only [nameBytes, List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hm, Option.map_some,
    Option.getD_some]
  exact names_eq_iff hns hn hm (hleaf _ (List.getElem_mem hn)) (hleaf _ (List.getElem_mem hm))

/-- Resolving in an interning table of names separates labels whose name ids are in range. -/
theorem resolve_eq_iff {ns : Store (List UInt8)} (hns : Interning ns)
    (hleaf : ∀ x ∈ ns, x.kids = []) {a b : HolLabelId} (ha : ∀ n ∈ a.nameId, n < ns.length)
    (hb : ∀ n ∈ b.nameId, n < ns.length) : resolve ns a = resolve ns b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  cases a <;> cases b <;> simp only [resolve, HolLabel.tyvar.injEq, HolLabel.tyapp.injEq,
    HolLabel.var.injEq, HolLabel.const.injEq, HolLabelId.tyvar.injEq, HolLabelId.tyapp.injEq,
    HolLabelId.var.injEq, HolLabelId.const.injEq, reduceCtorEq] at h ⊢
  all_goals first
    | rfl
    | exact (nameBytes_eq_iff hns hleaf (ha _ rfl) (hb _ rfl)).mp h

/-- **Names held as ids.**  Given an interning table of names, a store of types and terms with
names as ids in range interns exactly when the store with the names resolved to bytes does, and,
when it does, the two read back alike. -/
theorem hol_names_as_ids {ns : Store (List UInt8)} (hns : Interning ns)
    (hleaf : ∀ x ∈ ns, x.kids = []) {s : Store HolLabelId}
    (hnames : ∀ x ∈ s, ∀ n ∈ x.label.nameId, n < ns.length) :
    (Interning (s.map (Node.relabel (resolve ns))) ↔ Interning s) ∧
      (Interning s → ∀ i, i < s.length →
        readback (s.map (Node.relabel (resolve ns))) i = Tree.map (resolve ns) (readback s i)) :=
  ⟨interning_relabel_iff fun _ hi _ hj h =>
      (resolve_eq_iff hns hleaf (hnames _ (List.getElem_mem hi))
        (hnames _ (List.getElem_mem hj))).mp h,
    fun hs i hi => readback_relabel hs.kids_lt _ (i + 1) i (Nat.lt_succ_self i) hi⟩

end NamesAsIds

/-! ## Examples -/

namespace Examples

/-! ### A store over numeric labels -/

/-- Two leaves and a node over them. -/
def ops₁ : List (Node Nat) := [⟨1, []⟩, ⟨2, []⟩, ⟨3, [0, 1]⟩]

/-- The store `ops₁` builds. -/
def s₁ : Store Nat := run [] ops₁

example : s₁ = [⟨1, []⟩, ⟨2, []⟩, ⟨3, [0, 1]⟩] := by decide
-- Every operation of `ops₁` has its children in range, so the store interns (`interning_run_nil`);
-- `decide` confirms it on the store itself.
example : Interning s₁ := interning_run_nil (by decide)
example : Interning s₁ := by decide
example : readback s₁ 2 = .node 3 [.node 1 [], .node 2 []] := rfl

-- Interning existing contents returns their id and leaves the store unchanged.
example : intern s₁ ⟨3, [0, 1]⟩ = (s₁, 2) := by decide
-- Interning the same new contents twice gives the same id.
example : (intern s₁ ⟨4, [2]⟩).2 = 3 := by decide
example : intern (intern s₁ ⟨4, [2]⟩).1 ⟨4, [2]⟩ = intern s₁ ⟨4, [2]⟩ := by decide

-- Different contents (the children swapped) get a different id and read back differently.
example : (intern s₁ ⟨3, [1, 0]⟩).2 = 3 := by decide
example : readback (intern s₁ ⟨3, [1, 0]⟩).1 3 ≠ readback (intern s₁ ⟨3, [1, 0]⟩).1 2 := by
  decide
example : readback (intern s₁ ⟨3, [1, 0]⟩).1 3 = .node 3 [.node 2 [], .node 1 []] := rfl

/-! ### Stores that break the invariant -/

/-- Two nodes with equal contents: the store does not intern. -/
def dup : Store Nat := [⟨7, []⟩, ⟨7, []⟩]

example : ¬ Interning dup := by decide
-- Every child is earlier (there are none), yet two different ids read back alike.
example : ∀ i (hi : i < dup.length), ∀ k ∈ dup[i].kids, k < i := by decide
example : readback dup 0 = readback dup 1 := by decide

/-- Each node's only child is itself: the contents differ, but no child is an earlier node. -/
def loops : Store Nat := [⟨7, [0]⟩, ⟨7, [1]⟩]

example : ¬ Interning loops := by decide
example : ∀ i (hi : i < loops.length) j (hj : j < loops.length), loops[i] = loops[j] → i = j := by
  decide
example : readback loops 0 = readback loops 1 := by decide

/-- A child that is a later node. -/
def forward : Store Nat := [⟨7, [1]⟩, ⟨8, []⟩]

example : ¬ Interning forward := by decide

-- Interning contents whose child is not in range breaks the invariant.
example : ¬ Interning (intern ([] : Store Nat) ⟨7, [0]⟩).1 := by decide

-- An id out of range reads as `junk`, which can be the read-back of a node in range.
example : readback ([⟨0, []⟩] : Store Nat) 0 = readback ([⟨0, []⟩] : Store Nat) 1 := by decide

/-! ### A comparison whose `eq` outcome means equality -/

mutual

/-- Comparison of trees with numeric labels: the labels, then the subtrees lexicographically, a
shorter list first. -/
def treeCmp : Tree Nat → Tree Nat → Ordering
  | .node a as, .node b bs => (compare a b).then (treesCmp as bs)
termination_by structural t => t

/-- Lexicographic comparison of lists of trees. -/
def treesCmp : List (Tree Nat) → List (Tree Nat) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (treeCmp a b).then (treesCmp as bs)
termination_by structural l => l

end

mutual

theorem treeCmp_eq_iff : ∀ a b : Tree Nat, treeCmp a b = .eq ↔ a = b
  | .node a as, .node b bs => by
    rw [treeCmp, Ordering.then_eq_eq, Nat.compare_eq_eq, treesCmp_eq_iff as bs]
    exact ⟨fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl, fun h => Tree.node.inj h⟩
termination_by structural a => a

theorem treesCmp_eq_iff : ∀ as bs : List (Tree Nat), treesCmp as bs = .eq ↔ as = bs
  | [], [] => by simp [treesCmp]
  | [], _ :: _ => by simp [treesCmp]
  | _ :: _, [] => by simp [treesCmp]
  | a :: as, b :: bs => by
    rw [treesCmp, Ordering.then_eq_eq, treeCmp_eq_iff a b, treesCmp_eq_iff as bs, List.cons.injEq]
termination_by structural as => as

end

example : treeCmp (readback s₁ 0) (readback s₁ 2) = .lt := by decide
-- The comparison answers `eq` on the read-backs of ids `0` and `2` exactly when `0 = 2`, so not.
example : treeCmp (readback s₁ 0) (readback s₁ 2) = .eq ↔ 0 = 2 :=
  cmp_readback_eq_iff (by decide) treeCmp treeCmp_eq_iff (by decide) (by decide)
example : treeCmp (readback s₁ 0) (readback s₁ 2) ≠ .eq := fun h =>
  absurd ((cmp_readback_eq_iff (by decide) treeCmp treeCmp_eq_iff (by decide) (by decide)).mp h)
    (by decide : (0 : Nat) ≠ 2)
example : decide ((0 : Nat) = 2) = decide (treeCmp (readback s₁ 0) (readback s₁ 2) = .eq) :=
  decide_eq_cmp_readback (by decide) treeCmp treeCmp_eq_iff (by decide) (by decide)
example : decide ((1 : Nat) = 1) = decide (readback s₁ 1 = readback s₁ 1) :=
  decide_eq_readback (by decide) (by decide) (by decide)

/-! ### Names -/

/-- The bytes of `A`. -/
def bA : List UInt8 := [0x41]
/-- The bytes of `B`. -/
def bB : List UInt8 := [0x42]
/-- The bytes of `f`. -/
def bF : List UInt8 := [0x66]
/-- The bytes of `x`. -/
def bX : List UInt8 := [0x78]
/-- The bytes of `bool`. -/
def bBool : List UInt8 := [0x62, 0x6f, 0x6f, 0x6c]
/-- The bytes of `fun`. -/
def bFun : List UInt8 := [0x66, 0x75, 0x6e]

-- `bool`, `fun`, `bool`: the second `bool` gets the id of the first.
example : nameStore [bBool, bFun, bBool] = [nameNode bBool, nameNode bFun] := by decide
example : (intern (nameStore [bBool, bFun]) (nameNode bBool)).2 = 0 := by decide
-- A new name gets a new id.
example : (intern (nameStore [bBool, bFun]) (nameNode bA)).2 = 2 := by decide
-- Different ids, different bytes, by `nameStore_eq_iff`.
example : (nameStore [bBool, bFun, bBool])[0].label ≠ (nameStore [bBool, bFun, bBool])[1].label :=
  fun h => absurd ((nameStore_eq_iff _ (by decide) (by decide)).mp h) (by decide)

/-! ### HOL types and terms -/

/-- A run of the native constructors.  Ids: `0` the type variable `A`; `1` `bool`; `2` `A -> bool`;
`3` `x:A`; `4` `A -> A` (made by `hk_tm_abs` before the abstraction); `5` `λx. x`;
`6` `f:A -> bool`; `7` `f x`; then `A -> bool` again (no new node); `8` `B`; `9` `x:B`. -/
def holOps : List (Node HolLabel) :=
  [⟨.tyvar bA, []⟩, ⟨.tyapp bBool, []⟩, ⟨.tyapp bFun, [0, 1]⟩, ⟨.var bX, [0]⟩,
    ⟨.tyapp bFun, [0, 0]⟩, ⟨.abs, [3, 3]⟩, ⟨.var bF, [2]⟩, ⟨.comb, [6, 3]⟩,
    ⟨.tyapp bFun, [0, 1]⟩, ⟨.tyvar bB, []⟩, ⟨.var bX, [8]⟩]

/-- The store `holOps` builds. -/
def holStore : Store HolLabel := run [] holOps

example : holStore.length = 10 := by decide
example : Interning holStore := interning_run_nil (by decide)

-- `A -> bool` once more: the same id, the same store.
example : tyApp holStore bFun [0, 1] = (holStore, 2) := by decide
-- `x:A` and `x:B` differ only in their types: different ids, different read-backs.
example : (tmVar holStore bX 0).2 = 3 ∧ (tmVar holStore bX 8).2 = 9 := by decide
example : readback holStore 3 ≠ readback holStore 9 := by decide
example : ¬ (readback holStore 3 = readback holStore 9) :=
  fun h => absurd ((hol_interning_eq_iff (by decide) (by decide) (by decide)).mp h) (by decide)
-- `λx. x` reads back with the variable's type and no type of its own.
example : readback holStore 5 =
    .node .abs [.node (.var bX) [.node (.tyvar bA) []], .node (.var bX) [.node (.tyvar bA) []]] :=
  rfl
-- A new application `f x` built again: the same id.
example : (tmComb holStore 6 3).2 = 7 := by decide
-- A constant `f:A -> bool` is not the variable `f:A -> bool`.
example : (tmConst holStore bF 2).2 = 10 := by decide
-- An abstraction over `x:B`: a new node.
example : (tmAbs holStore 9 9).2 = 10 := by decide
example : (tyVar holStore bB).2 = 8 := by decide

/-! ### Id tables -/

open RuleModulePrimitives (enc val)

/-- The module's cells, with objects abstracted to numbers. -/
inductive Cell
  | cNone
  | cOk (o : Nat)
  | cFailed
  | cDropped
  deriving DecidableEq, Repr

/-- Two cells put into the empty native table, at ids `0` and `1`. -/
def tab₁ : NTable Cell := (NTable.empty.put (.cOk 7)).put (.cOk 8)

example : tab₁ = ⟨[some (.cOk 7), some (.cOk 8)], 2⟩ := rfl
example : tab₁.readback .cNone =
    ⟨enc 2, .tnode (.cOk 7) .tleaf (.tnode (.cOk 8) .tleaf .tleaf)⟩ := by decide
-- The module's rules, run from `"empty-table"`, build the read-back.
example : tablePut .cNone (tablePut .cNone emptyTable (.cOk 7)) (.cOk 8) = tab₁.readback .cNone := by
  decide
example : tableGet .cNone (tab₁.readback .cNone) (enc 1) = .cOk 8 := by decide
example : tab₁.get .cNone 1 = .cOk 8 := rfl
example : tableGet .cNone (tab₁.readback .cNone) (enc 5) = .cNone := by decide
example : tab₁.get .cNone 5 = .cNone := rfl
example : tableNext (tab₁.readback .cNone) = enc 2 := rfl

/-- Id `4` set: its digit path is `0, 0, 1`, and the nodes at `0` and `0, 0`, no ids, hold
`c-none`. -/
def tab₂ : NTable Cell := tab₁.set 4 .cFailed

example : tab₂.cells = [some (.cOk 7), some (.cOk 8), none, none, some .cFailed] := rfl
example : tab₂.readback .cNone =
    ⟨enc 2, .tnode (.cOk 7)
      (.tnode .cNone (.tnode .cNone .tleaf (.tnode .cFailed .tleaf .tleaf)) .tleaf)
      (.tnode (.cOk 8) .tleaf .tleaf)⟩ := by decide
example : tableSet .cNone (tab₁.readback .cNone) (enc 4) .cFailed = tab₂.readback .cNone := by
  decide
-- The slots grown on the way read as `c-none`.
example : tab₂.get .cNone 2 = .cNone ∧ tab₂.get .cNone 3 = .cNone := ⟨rfl, rfl⟩
-- Setting a stored id overwrites its cell in place.
example : (tab₂.set 1 .cDropped).cells =
    [some (.cOk 7), some .cDropped, none, none, some .cFailed] := rfl
example : tableSet .cNone (tab₂.readback .cNone) (enc 1) .cDropped =
    (tab₂.set 1 .cDropped).readback .cNone := by decide

-- A stored `c-none` is not the absence of a cell: both tables answer `c-none` at every id, but
-- the stored cell has a node.
example : ∀ i, (⟨[some .cNone], 1⟩ : NTable Cell).get .cNone i =
    (⟨[none], 1⟩ : NTable Cell).get .cNone i := by
  intro i
  cases i <;> rfl
example : rbTrie .cNone [some Cell.cNone] = .tnode .cNone .tleaf .tleaf := by decide
example : rbTrie .cNone [(none : Option Cell)] = .tleaf := rfl

/-- A node at the path `0`, which is no id, with no id below it. -/
def tBad : Trie Cell := .tnode .cNone (.tnode .cNone .tleaf .tleaf) .tleaf

-- It answers `c-none` everywhere, as `tleaf` does (yet it is no read-back:
-- `tBad_ne_rbTrie`).
example : ∀ k, trieGet .cNone tBad k = trieGet .cNone .tleaf k := by
  intro k
  cases k with
  | nz => rfl
  | nb0 k => cases k <;> rfl
  | nb1 k => rfl

/-! ### The binding of the equality judgments -/

section BindingExamples

open RuleModulePrimitives RuleModuleComparisonLaws

/-- The module's type `A -> bool`. -/
def tyAtoBool : Ty :=
  .Tyapp (encodeStr bFun) (.tycons (.Tyvar (encodeStr bA))
    (.tycons (.Tyapp (encodeStr bBool) .tynil) .tynil))

/-- The module's term `λx. x`, with `x:A`. -/
def tmIdA : Term := .Abs (.Var (encodeStr bX) (.Tyvar (encodeStr bA)))
  (.Var (encodeStr bX) (.Tyvar (encodeStr bA)))

-- Node 2 of `holStore` decodes to `A -> bool`, and is the tree of that type.
example : decodeTy (readback holStore 2) = some tyAtoBool := by decide
example : readback holStore 2 = treeOfTy tyAtoBool := by decide
-- Node 5 decodes to `λx. x`.
example : decodeTerm (readback holStore 5) = some tmIdA := by decide
-- A type node is no term, a term node is no type.
example : decodeTerm (readback holStore 2) = none := by decide
example : decodeTy (readback holStore 3) = none := by decide
-- Trees of the wrong shape are not accepted: a type variable with a child, an application with
-- one child.
example : decodeTy (.node (.tyvar bA) [.node (.tyvar bA) []]) = none := by decide
example : decodeTerm (.node .comb [.node (.var bX) [.node (.tyvar bA) []]]) = none := by decide

-- `"ty-eq"` on node 2 and itself: `yes`, as the binding says.
example : tyEq tyAtoBool tyAtoBool = .yes ↔ 2 = 2 :=
  tyEq_binding (s := holStore) (by decide) (by decide) (by decide) (by decide) (by decide)
example : tyEq tyAtoBool tyAtoBool = .yes := by decide
-- `"ty-eq"` on nodes 0 (`A`) and 8 (`B`): `no`, which the binding derives from `0 ≠ 8`.
example : tyEq (.Tyvar (encodeStr bA)) (.Tyvar (encodeStr bB)) ≠ .yes := fun h =>
  absurd ((tyEq_binding (s := holStore) (i := 0) (j := 8) (by decide) (by decide) (by decide)
    (by decide) (by decide)).mp h) (by decide)
example : tyEq (.Tyvar (encodeStr bA)) (.Tyvar (encodeStr bB)) = .no := by decide

-- `"tm-eq"` on node 5 (`λx. x`) and itself: `yes`.
example : tmEq tmIdA tmIdA = .yes ↔ 5 = 5 :=
  tmEq_binding (s := holStore) (by decide) (by decide) (by decide) (by decide) (by decide)
-- `"tm-eq"` on nodes 3 (`x:A`) and 9 (`x:B`): `no`, from `3 ≠ 9`.
example : tmEq (.Var (encodeStr bX) (.Tyvar (encodeStr bA)))
    (.Var (encodeStr bX) (.Tyvar (encodeStr bB))) ≠ .yes := fun h =>
  absurd ((tmEq_binding (s := holStore) (i := 3) (j := 9) (by decide) (by decide) (by decide)
    (by decide) (by decide)).mp h) (by decide)
example : tmEq (.Var (encodeStr bX) (.Tyvar (encodeStr bA)))
    (.Var (encodeStr bX) (.Tyvar (encodeStr bB))) = .no := by decide

-- `"str-eq"` on the names `bool` (id 0) and `fun` (id 1): `no`, from `0 ≠ 1`.
example : strEq (encodeStr bBool) (encodeStr bFun) ≠ .yes := fun h =>
  absurd ((strEq_binding (s := nameStore [bBool, bFun]) (i := 0) (j := 1)
    (interning_nameStore _) (by decide) (by decide) (by decide) (by decide)).mp h) (by decide)
example : strEq (encodeStr bBool) (encodeStr bFun) = .no := by decide

/-- A store of types that does not intern: `A` twice. -/
def holDup : Store HolLabel := [⟨.tyvar bA, []⟩, ⟨.tyvar bA, []⟩]

-- Without the invariant the binding fails: two different ids decode to equal types, and
-- `"ty-eq"` answers `yes`.
example : ¬ Interning holDup := by decide
example : decodeTy (readback holDup 0) = some (.Tyvar (encodeStr bA)) ∧
    decodeTy (readback holDup 1) = some (.Tyvar (encodeStr bA)) ∧
    tyEq (.Tyvar (encodeStr bA)) (.Tyvar (encodeStr bA)) = .yes ∧ (0 : Nat) ≠ 1 := by decide

-- The converse laws on the module's own data.
example : cmpType tyAtoBool (.Tyvar (encodeStr bA)) ≠ .eq := fun h =>
  absurd ((cmpType_eq_iff _ _).mp h) (by decide)
example : tmsEq (.tmcons tmIdA .tmnil) (.tmcons tmIdA .tmnil) = .yes := by decide
example : tmsEq (.tmcons tmIdA .tmnil) .tmnil ≠ .yes := fun h =>
  absurd ((tmsEq_eq_yes_iff _ _).mp h) (by decide)

end BindingExamples

/-! ### Names held as ids -/

/-- A table of names: ids `0` `A`, `1` `bool`, `2` `fun`, `3` `x`, `4` `f`, `5` `B`. -/
def names₁ : Store (List UInt8) := nameStore [bA, bBool, bFun, bX, bF, bB]

/-- The run of `holOps` with names as ids into `names₁`, as the native nodes hold them. -/
def holIdOps : List (Node HolLabelId) :=
  [⟨.tyvar 0, []⟩, ⟨.tyapp 1, []⟩, ⟨.tyapp 2, [0, 1]⟩, ⟨.var 3, [0]⟩,
    ⟨.tyapp 2, [0, 0]⟩, ⟨.abs, [3, 3]⟩, ⟨.var 4, [2]⟩, ⟨.comb, [6, 3]⟩,
    ⟨.tyapp 2, [0, 1]⟩, ⟨.tyvar 5, []⟩, ⟨.var 3, [8]⟩]

/-- The store `holIdOps` builds. -/
def holIdStore : Store HolLabelId := run [] holIdOps

-- Resolving the ids gives the store with names as bytes.
example : holIdStore.map (Node.relabel (resolve names₁)) = holStore := by decide
example : Interning holIdStore := by decide
-- By `hol_names_as_ids`, it interns because the store with ids does, and reads back alike.
example : Interning (holIdStore.map (Node.relabel (resolve names₁))) :=
  (hol_names_as_ids (interning_nameStore _) (by decide) (by decide)).1.mpr (by decide)
example : readback (holIdStore.map (Node.relabel (resolve names₁))) 5 =
    Tree.map (resolve names₁) (readback holIdStore 5) :=
  (hol_names_as_ids (interning_nameStore _) (by decide) (by decide)).2 (by decide) 5 (by decide)
example : Tree.map (resolve names₁) (readback holIdStore 5) = readback holStore 5 := by decide

/-- A table of names that does not intern: `A` under ids `0` and `1`. -/
def namesDup : Store (List UInt8) := [nameNode bA, nameNode bA]

/-- Two type variables with different name ids. -/
def tyvars₂ : Store HolLabelId := [⟨.tyvar 0, []⟩, ⟨.tyvar 1, []⟩]

-- The store with ids interns, but resolving in a table that does not intern merges the two
-- nodes: the table of names must intern.
example : Interning tyvars₂ := by decide
example : ¬ Interning namesDup := by decide
example : ¬ Interning (tyvars₂.map (Node.relabel (resolve namesDup))) := by decide
-- Name ids out of range resolve to no name's bytes, and merge too: the ids must be in range.
example : ¬ Interning
    (([⟨.tyvar 7, []⟩, ⟨.tyvar 8, []⟩] : Store HolLabelId).map (Node.relabel (resolve names₁))) := by
  decide

end Examples

/-! ## Each hypothesis of the law is needed -/

/-- Without injectivity, two different ids can read back alike (`Examples.dup`). -/
theorem interning_eq_iff_needs_injective :
    ¬ ∀ s : Store Nat, (∀ (i : Nat) (hi : i < s.length), ∀ k ∈ (s[i]'hi).kids, k < i) →
      ∀ i j, i < s.length → j < s.length → readback s i = readback s j → i = j :=
  fun h => absurd (h Examples.dup (by decide) 0 1 (by decide) (by decide) (by decide)) (by decide)

/-- Without the children being earlier nodes, two different ids can read back alike
(`Examples.loops`). -/
theorem interning_eq_iff_needs_kids_lt :
    ¬ ∀ s : Store Nat,
      (∀ (i : Nat) (hi : i < s.length) (j : Nat) (hj : j < s.length), s[i]'hi = s[j]'hj → i = j) →
      ∀ i j, i < s.length → j < s.length → readback s i = readback s j → i = j :=
  fun h => absurd (h Examples.loops (by decide) 0 1 (by decide) (by decide) (by decide)) (by decide)

/-- Without the ids in range, an id out of range can read back as a node in range. -/
theorem interning_eq_iff_needs_range :
    ¬ ∀ s : Store Nat, Interning s → ∀ i j, readback s i = readback s j → i = j :=
  fun h => absurd (h [⟨0, []⟩] (by decide) 0 1 (by decide)) (by decide)

/-! ## The read-back of a table has a fixed shape, and numerals must be canonical -/

open RuleModulePrimitives in
/-- The shape matters: `Examples.tBad` answers like `tleaf` but is the read-back of no array, since
its node at the path `0` lies on the path of no stored id. -/
theorem tBad_ne_rbTrie (cells : List (Option Examples.Cell)) :
    rbTrie .cNone cells ≠ Examples.tBad := by
  intro h
  have hr := isReadback_rbTrie Examples.Cell.cNone cells
  rw [h] at hr
  obtain ⟨i, c, hi, hp⟩ := (hr.has_iff (.nb0 .nz)).mp (by simp [Examples.tBad])
  obtain ⟨m, hm, -⟩ := pathPrefix_nb0_iff.mp hp
  have hn : Examples.tBad.Has (enc i) := (hr.has_iff (enc i)).mpr ⟨i, c, hi, pathPrefix_refl _⟩
  have hc := canon_enc i
  rw [hm] at hn hc
  have hmz := (canon_nb0_iff.mp hc).2
  simp only [Examples.tBad, Trie.has_tnode_nb0] at hn
  cases m with
  | nz => exact hmz rfl
  | nb0 m => simp at hn
  | nb1 m => simp at hn

open RuleModulePrimitives in
/-- Numerals must be canonical: `nb0 nz` has the value `0`, but `"table-set"` at it puts the cell
at the node of the path `0`, which is no id. -/
theorem tableSet_readback_needs_canon :
    tableSet Examples.Cell.cNone ((NTable.empty : NTable Examples.Cell).readback .cNone)
        (.nb0 .nz) (.cOk 1) ≠
      ((NTable.empty : NTable Examples.Cell).set (val (.nb0 .nz)) (.cOk 1)).readback .cNone := by
  decide

end Mettapedia.Languages.HOLLight.RuleModuleInterning

#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.readback_of_lt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.readback_eq_node
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.readback_of_prefix
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_intern
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.getElem?_intern
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.readback_intern
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.readback_intern_of_lt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.intern_intern
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_run
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_run_nil
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.cmp_readback_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.decide_eq_readback
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.decide_eq_cmp_readback
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.names_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.nameStore_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.hol_interning_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_eq_iff_needs_injective
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_eq_iff_needs_kids_lt
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_eq_iff_needs_range
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.trieGet_trieSet
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.has_trieSet
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.IsReadback.unique
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.isReadback_rbTrie
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.trieGet_rbTrie
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.trieSet_rbTrie
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.rbTrie_nil
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tableGet_readback
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tablePut_readback
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tableSet_readback
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tableNext_readback
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.emptyTable_readback
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tBad_ne_rbTrie
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tableSet_readback_needs_canon
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.cmpType_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.cmpTypes_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.cmpLeaf_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.cmpTerm_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tyEq_eq_yes_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tmEq_eq_yes_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tmsEq_eq_yes_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.decodeTy_treeOfTy
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.decodeTerm_treeOfTerm
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.eq_treeOfTy
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.eq_treeOfTerm
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.decodeTy_injective
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.decodeTerm_injective
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tyEq_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.tmEq_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.strEq_binding
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_relabel
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.interning_relabel_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.readback_relabel
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.nameBytes_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.resolve_eq_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleInterning.hol_names_as_ids
