import Mettapedia.Languages.HOLLight.RuleModuleInterning

/-!
# Caches of the rule-module runtime: the interning store's front cache, reading and writing atoms

The rule modules compiled to C, and the glue that runs them inside CeTTa, keep three caches that
the rules know nothing of.  Each is sound when it changes no answer; this file models each and
proves it.

* **The interning store's front cache** (`rc_intern_node`, `front_clear`).  The store is the one of
  `RuleModuleInterning` (`Store`, `intern`: a node looked up by its contents, appended on a miss).
  In front of it a direct-mapped cache of the nodes of at most three children (`Front`,
  `FrontEntry`: a slot per hash, holding the constructor, the children, the hash and the node) is
  consulted first; it answers when the hit check passes (`hits`: at most three children, and the
  hash, the constructor, the number of children and every child equal), and it is filled on a
  table hit and on an insert (`internFront`; the hash and the slot are any functions).  Under the
  invariant that every entry holds a node of the store with exactly its key's contents (`FrontOK`),
  in a store whose nodes are distinct (`Injective`, given by the store invariant `Interning` and
  kept by `intern`: `injective_intern`), a hit answers the node the table answers
  (`frontHit_sound`, `internFront_answer`), the fills keep the invariant (`frontOK_internFront`),
  and a clear establishes it for whatever store a collection or a freeing leaves
  (`frontOK_empty`).  So every run of calls and collections answers with the cache exactly as
  without it, and leaves the same store (`runFront_eq`).
* **Reading atoms** (`rcm_value`, `rcm_same`, `rcm_seen_get`, `rcm_seen_put`).  An atom is a finite
  tree of symbols, integers, other atoms and expressions, an expression with the structural hash
  CeTTa keeps for it, if any (`Atom`); its module data forget the kept hashes (`Data`, `Atom.data`).
  The read is a function of the module data (`read`, `readKids`: a handle `(TAG:handle N)` a lookup
  of the held values; otherwise a constructor's symbol, checked for existence, sort and arity, over
  its children read at their sorts and built by `rc_construct`; each failure an error, the first
  one met ending the read).  `rcm_same` (`same`) is sound: when it answers `true` the atoms are
  equal module data (`same_sound`), hence read as one value (`read_of_same`); its identity test
  changes no answer (`same_refl`); and when the kept hashes agree with a structural hash, its
  pruning test never separates equal atoms (`KeptOK`, `same_complete`).  With the reuse table
  (`readSeen`), a constructor without children is built at once; an atom with a kept hash for which
  the table holds an atom the same, of the same sort, is that atom's value (`GetOK`: whichever such
  entry the probe meets; `seenFind` is one such lookup); otherwise it is read as before and kept.
  Under the table's invariant (`SeenOK`: every entry's value is what its atom reads as at its sort)
  it gives the same value, or the same error, as the read without the table, and keeps the
  invariant (`readSeen_agrees`, `readSeen_eq`); a call starts with an empty table.
* **Writing values as atoms** (`rcm_atom_of`, `rcm_shown_get`, `rcm_shown_put`).  The atom written
  for a value without sharing (`Writes`) is its constructor, from the view (`rc_view`), over the
  atoms of its children at their sorts, or `:unreadable`; there is one (`Writes.functional`).  With
  sharing (`WritesS`), an interned value written before in the result is that atom, and the atom of
  an interned value with children is kept (or not, when the table cannot grow).  When the view of
  an interned value reads its node whatever the sort asked (`InternedView`), every atom written
  with sharing is the atom written without it, and the table keeps its invariant (`ShownOK`,
  `WritesS.sound`), and conversely (`Writes.shared`); for a result (`rcm_atom`, the table empty at
  its start) the two are one atom (`writesS_iff`, `writesS_unique`).  This needs no assumption on
  identity: a table keyed by the value's word answers the atom of that word.  What
  `interning_eq_iff` adds is that nothing is missed: in an interning store a value is in a table
  keyed by values exactly when a value equal to it as module data is (`shown_by_identity`), so
  sharing by identity shares every repeated value.

What the models leave out.

* The front cache.  The table's hashing and probing (the lookup by contents is `intern`), the
  collector (a collection is an operation that leaves some store whose nodes are distinct, after
  which the cache is clear), the memo slots of the nodes, and `rc_intern_bytes` and
  `rc_intern_nullary` (which do not use the front cache) are not modelled.  Children are node ids,
  as in the store's model.
* Reading.  An expression's kept hash is a field of the atom; that CeTTa keeps an atom's structural
  hash is what `KeptOK` states, and is needed only for the pruning test never to separate equal
  atoms, not for soundness.  Other atoms (variables, grounded values other than integers) are
  compared by equality, as CeTTa's `atom_eq` is trusted to.  The table's open addressing,
  generations and growth are not modelled (`get` may answer any entry that passes the test, or
  none).  `rcm_value` does not check `rc_construct`'s result for a constructor without children,
  which never fails; the model treats it as for the others.
* Writing.  Values are words with a view; that `rc_view` reads an interned node whatever the sort
  asked is read off the generated code.  The arrays of the C (`kids[16]` filled by `rc_view`,
  `e[17]` given to `atom_expr` with `n + 1` elements) are not modelled; nothing on this path bounds
  a constructor's arity at sixteen, as `rcm_value` does when reading.

Notes for proving here: the mutually inductive judgments and the nested types are handled by
mutual structural recursion (term-mode `match` with every index as a pattern); after a case split
on a scrutinee, `dsimp only` reduces the matches before the next split.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.RuleModuleCaches

open RuleModuleInterning

universe u v

/-! ## The front cache of the interning store (`rc_intern_node`, `front_clear`) -/

section Front

variable {L : Type u} [DecidableEq L]

/-- The store's nodes are distinct: equal contents are one node (the second half of the store
invariant, `Interning.injective`). -/
def Injective (s : Store L) : Prop :=
  ∀ (i : Nat) (hi : i < s.length) (j : Nat) (hj : j < s.length), s[i] = s[j] → i = j

omit [DecidableEq L] in
theorem injective_of_interning {s : Store L} (hs : Interning s) : Injective s := hs.injective

/-- Interning keeps the store's nodes distinct (whatever the children). -/
theorem injective_intern {s : Store L} (hs : Injective s) (n : Node L) : Injective (intern s n).1 := by
  cases h : s.idxOf? n with
  | some i => rw [intern_of_idxOf?_eq_some h]; exact hs
  | none =>
    have hns : n ∉ s := List.idxOf?_eq_none_iff.mp h
    rw [intern_of_not_mem hns]
    intro i hi j hj hij
    simp only [List.length_append, List.length_singleton] at hi hj
    rw [getElem_append_singleton, getElem_append_singleton] at hij
    split at hij <;> split at hij
    · exact hs i ‹_› j ‹_› hij
    · exact absurd (hij ▸ List.getElem_mem ‹_›) hns
    · exact absurd (hij.symm ▸ List.getElem_mem ‹_›) hns
    · omega

/-- In a store whose nodes are distinct, the lookup by contents finds the one node with those
contents. -/
theorem idxOf?_of_getElem? {s : Store L} (hs : Injective s) {i : Nat} {n : Node L}
    (h : s[i]? = some n) : s.idxOf? n = some i := by
  obtain ⟨hi, hsi⟩ := List.getElem?_eq_some_iff.mp h
  cases hj : s.idxOf? n with
  | none => exact absurd (hsi ▸ List.getElem_mem hi) (List.idxOf?_eq_none_iff.mp hj)
  | some j =>
    obtain ⟨hjl, hsj⟩ := List.getElem?_eq_some_iff.mp (getElem?_of_idxOf?_eq_some hj)
    rw [hs j hjl i hi (hsj.trans hsi.symm)]

/-- An entry of the front cache (`FrontEntry`): its key (the constructor and the children), the
hash, and the node. -/
structure FrontEntry (L : Type u) : Type u where
  /-- The constructor (`f->c`). -/
  label : L
  /-- The children (`f->k[0 .. f->n)`). -/
  kids : List Nat
  /-- The hash (`f->h`). -/
  hash : Nat
  /-- The node (`f->x`). -/
  node : Nat

/-- The front cache: each slot's entry, or none (`f->x == NULL`). -/
abbrev Front (L : Type u) : Type u := Nat → Option (FrontEntry L)

/-- `front_clear`: every slot empty. -/
def Front.empty : Front L := fun _ => none

/-- A slot filled. -/
def Front.set (fr : Front L) (k : Nat) (e : FrontEntry L) : Front L :=
  fun j => if j = k then some e else fr j

/-- The hit check of `rc_intern_node`: at most three children, and the entry's hash, constructor,
number of children and every child equal to the call's. -/
def hits (h : Nat) (n : Node L) (e : FrontEntry L) : Bool :=
  decide (n.kids.length ≤ 3) && decide (e.hash = h) && decide (e.label = n.label) &&
    decide (e.kids = n.kids)

/-- The node the front cache answers for the contents `n` of hash `h` at slot `k`, if it hits. -/
def frontHit (fr : Front L) (k h : Nat) (n : Node L) : Option Nat :=
  match fr k with
  | some e => if hits h n e then some e.node else none
  | none => none

/-- **`rc_intern_node` with the front cache**: the contents' hash and its slot; a hit answers the
entry's node; otherwise the table answers (`intern`: the node with these contents, or a new node
appended), and the slot is filled with the contents and that node when there are at most three
children (both on a table hit and on an insert).  The hash and the slot are any functions (`hash`:
`hash_node`, `slot`: its top bits). -/
def internFront (hash : Node L → Nat) (slot : Nat → Nat) (fr : Front L) (s : Store L)
    (n : Node L) : Front L × Store L × Nat :=
  match frontHit fr (slot (hash n)) (hash n) n with
  | some i => (fr, s, i)
  | none =>
    ((if n.kids.length ≤ 3 then fr.set (slot (hash n)) ⟨n.label, n.kids, hash n, (intern s n).2⟩
      else fr), (intern s n).1, (intern s n).2)

/-- **The front cache's invariant**: every entry holds a node of the store with exactly its key's
contents. -/
def FrontOK (fr : Front L) (s : Store L) : Prop :=
  ∀ k e, fr k = some e → s[e.node]? = some ⟨e.label, e.kids⟩

omit [DecidableEq L] in
/-- A cleared cache keeps the invariant with every store: `front_clear` makes the cache sound
again after `rc_intern_collect` and `rc_intern_free` change the store. -/
theorem frontOK_empty (s : Store L) : FrontOK Front.empty s := fun _ _ h => nomatch h

/-- A hit answers a node with exactly the call's contents. -/
theorem frontHit_sound {fr : Front L} {s : Store L} (hf : FrontOK fr s) {k h : Nat} {n : Node L}
    {i : Nat} (hhit : frontHit fr k h n = some i) : s[i]? = some n := by
  unfold frontHit at hhit
  split at hhit
  · rename_i e he
    split at hhit
    · rename_i hh
      cases hhit
      simp only [hits, Bool.and_eq_true, decide_eq_true_eq] at hh
      obtain ⟨⟨⟨_, _⟩, hl⟩, hk⟩ := hh
      rw [hf k e he, hl, hk]
    · cases hhit
  · cases hhit

/-- **The front cache changes no answer**: with the cache, `rc_intern_node` answers with the store
and the node the table answers without it. -/
theorem internFront_answer (hash : Node L → Nat) (slot : Nat → Nat) {fr : Front L} {s : Store L}
    (hf : FrontOK fr s) (hs : Injective s) (n : Node L) :
    (internFront hash slot fr s n).2 = intern s n := by
  unfold internFront
  cases hhit : frontHit fr (slot (hash n)) (hash n) n with
  | none => rfl
  | some i =>
    show (s, i) = intern s n
    rw [intern_of_idxOf?_eq_some (idxOf?_of_getElem? hs (frontHit_sound hf hhit))]

/-- The fills keep the invariant: after a call, every entry still holds a node of the store with
exactly its key's contents. -/
theorem frontOK_internFront (hash : Node L → Nat) (slot : Nat → Nat) {fr : Front L} {s : Store L}
    (hf : FrontOK fr s) (n : Node L) :
    FrontOK (internFront hash slot fr s n).1 (internFront hash slot fr s n).2.1 := by
  unfold internFront
  cases hhit : frontHit fr (slot (hash n)) (hash n) n with
  | some i => exact hf
  | none =>
    have hold : FrontOK fr (intern s n).1 := by
      intro k e he
      have h := hf k e he
      obtain ⟨t, ht⟩ := prefix_intern s n
      rw [← ht, List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
      exact h
    show FrontOK (if n.kids.length ≤ 3 then _ else fr) (intern s n).1
    split
    · intro k e he
      unfold Front.set at he
      split at he
      · cases he
        exact getElem?_intern s n
      · exact hold k e he
    · exact hold

/-- What happens to the store between calls: contents interned (`rc_intern_node`), or a collection
or freeing of the store (`rc_intern_collect`, `rc_intern_free`), which leaves the store `s'` (the
collector itself is not modelled) and clears the front cache. -/
inductive Op (L : Type u) : Type u
  /-- `rc_intern_node` of the contents. -/
  | intern (n : Node L)
  /-- A collection or freeing, leaving the store `s'`. -/
  | collect (s' : Store L)

/-- The calls answered without the front cache: the final store and the nodes answered. -/
def runPlain : Store L → List (Op L) → Store L × List Nat
  | s, [] => (s, [])
  | s, .intern n :: ops =>
    ((runPlain (intern s n).1 ops).1, (intern s n).2 :: (runPlain (intern s n).1 ops).2)
  | _, .collect s' :: ops => runPlain s' ops

/-- The calls answered with the front cache, cleared at every collection. -/
def runFront (hash : Node L → Nat) (slot : Nat → Nat) :
    Front L → Store L → List (Op L) → Store L × List Nat
  | _, s, [] => (s, [])
  | fr, s, .intern n :: ops =>
    ((runFront hash slot (internFront hash slot fr s n).1 (internFront hash slot fr s n).2.1 ops).1,
      (internFront hash slot fr s n).2.2 ::
        (runFront hash slot (internFront hash slot fr s n).1 (internFront hash slot fr s n).2.1
          ops).2)
  | _, _, .collect s' :: ops => runFront hash slot Front.empty s' ops

/-- **Every run**: from a cache that keeps its invariant and a store whose nodes are distinct, with
collections that leave stores whose nodes are distinct, the front cache answers every call with the
node the store answers without it, and leaves the same store. -/
theorem runFront_eq (hash : Node L → Nat) (slot : Nat → Nat) :
    ∀ (ops : List (Op L)) {fr : Front L} {s : Store L}, FrontOK fr s → Injective s →
      (∀ s', Op.collect s' ∈ ops → Injective s') → runFront hash slot fr s ops = runPlain s ops
  | [], _, _, _, _, _ => rfl
  | .intern n :: ops, fr, s, hf, hs, hc => by
    have hx := internFront_answer hash slot hf hs n
    have h1 : (internFront hash slot fr s n).2.1 = (intern s n).1 := congrArg Prod.fst hx
    have h2 : (internFront hash slot fr s n).2.2 = (intern s n).2 := congrArg Prod.snd hx
    have ih := runFront_eq hash slot ops (frontOK_internFront hash slot hf n)
      (by rw [h1]; exact injective_intern hs n) (fun s' h => hc s' (List.mem_cons_of_mem _ h))
    rw [h1] at ih
    simp only [runFront, runPlain, h1, h2, ih]
  | .collect s' :: ops, _, _, _, _, hc => by
    simp only [runFront, runPlain]
    exact runFront_eq hash slot ops (frontOK_empty s') (hc s' List.mem_cons_self)
      (fun s'' h => hc s'' (List.mem_cons_of_mem _ h))

/-- From an empty store, interning only. -/
theorem runFront_eq_nil (hash : Node L → Nat) (slot : Nat → Nat) (ops : List (Op L))
    (hc : ∀ s', Op.collect s' ∈ ops → Injective s') :
    runFront hash slot Front.empty [] ops = runPlain [] ops :=
  runFront_eq hash slot ops (frontOK_empty []) (fun _ hi => absurd hi (Nat.not_lt_zero _)) hc

end Front

/-! ## Reading atoms (`rcm_value`, `rcm_same`, `rcm_seen_get`, `rcm_seen_put`) -/

section Read

/-- An atom as the glue reads it: a symbol, an integer, another atom (a variable or a grounded
value other than an integer, compared by CeTTa's equality), or an expression with the structural
hash CeTTa keeps for it (`none`: none kept, the C's `0`). -/
inductive Atom (Sym O : Type) : Type
  /-- A symbol. -/
  | sym (s : Sym)
  /-- An integer. -/
  | int (i : Int)
  /-- Another atom. -/
  | other (o : O)
  /-- An expression, with the hash kept for it. -/
  | expr (kept : Option Nat) (es : List (Atom Sym O))

/-- The module data of an atom: its symbols, numbers and shape. -/
inductive Data (Sym O : Type) : Type
  /-- A symbol. -/
  | sym (s : Sym)
  /-- An integer. -/
  | int (i : Int)
  /-- Another atom. -/
  | other (o : O)
  /-- An expression. -/
  | expr (es : List (Data Sym O))

variable {Sym O C S V : Type}

mutual

/-- The module data of an atom: the atom without its kept hashes. -/
def Atom.data : Atom Sym O → Data Sym O
  | .sym s => .sym s
  | .int i => .int i
  | .other o => .other o
  | .expr _ es => .expr (Atom.dataList es)

/-- `Atom.data` on a list. -/
def Atom.dataList : List (Atom Sym O) → List (Data Sym O)
  | [] => []
  | a :: as => a.data :: Atom.dataList as

end

@[simp] theorem Atom.data_sym (s : Sym) : (Atom.sym s : Atom Sym O).data = .sym s := by
  rw [Atom.data]

@[simp] theorem Atom.data_expr (k : Option Nat) (es : List (Atom Sym O)) :
    (Atom.expr k es).data = .expr (Atom.dataList es) := by
  rw [Atom.data]

@[simp] theorem Atom.dataList_nil : Atom.dataList ([] : List (Atom Sym O)) = [] := by
  rw [Atom.dataList]

@[simp] theorem Atom.dataList_cons (a : Atom Sym O) (as : List (Atom Sym O)) :
    Atom.dataList (a :: as) = a.data :: Atom.dataList as := by
  rw [Atom.dataList]

theorem Atom.length_dataList : ∀ as : List (Atom Sym O), (Atom.dataList as).length = as.length
  | [] => by simp
  | a :: as => by simp [Atom.length_dataList as]

/-! ### `rcm_same` -/

/-- The pruning test of `rcm_same`: both kept hashes known and different. -/
def prune : Option Nat → Option Nat → Bool
  | some a, some b => decide (a ≠ b)
  | _, _ => false

variable [DecidableEq Sym] [DecidableEq O]

mutual

/-- `rcm_same`: two atoms read alike as module data.  Symbols by their ids, integers by value, other
atoms by CeTTa's equality; expressions of the same length, unless both have kept hashes and they
differ, element by element, the first difference ending it.  (The C first answers `true` on one
object, `a == b`; that answer is the one computed here, `same_refl`.) -/
def same : Atom Sym O → Atom Sym O → Bool
  | .sym s, .sym s' => decide (s = s')
  | .int i, .int j => decide (i = j)
  | .other o, .other o' => decide (o = o')
  | .expr ka es, .expr kb fs => decide (es.length = fs.length) && !prune ka kb && sameList es fs
  | .sym _, .int _ => false
  | .sym _, .other _ => false
  | .sym _, .expr _ _ => false
  | .int _, .sym _ => false
  | .int _, .other _ => false
  | .int _, .expr _ _ => false
  | .other _, .sym _ => false
  | .other _, .int _ => false
  | .other _, .expr _ _ => false
  | .expr _ _, .sym _ => false
  | .expr _ _, .int _ => false
  | .expr _ _, .other _ => false

/-- `rcm_same` on the elements of two expressions. -/
def sameList : List (Atom Sym O) → List (Atom Sym O) → Bool
  | [], [] => true
  | a :: as, b :: bs => same a b && sameList as bs
  | [], _ :: _ => false
  | _ :: _, [] => false

end

mutual

/-- `rcm_same` answers `true` on one atom: the C's identity test changes no answer. -/
theorem same_refl : ∀ a : Atom Sym O, same a a = true
  | .sym s => by simp [same]
  | .int i => by simp [same]
  | .other o => by simp [same]
  | .expr k es => by
    have h := sameList_refl es
    cases k <;> simp [same, prune, h]

theorem sameList_refl : ∀ as : List (Atom Sym O), sameList as as = true
  | [] => by simp [sameList]
  | a :: as => by simp [sameList, same_refl a, sameList_refl as]

end

mutual

/-- **`rcm_same` is sound**: when it answers `true`, the two atoms are equal module data. -/
theorem same_sound : ∀ {a b : Atom Sym O}, same a b = true → a.data = b.data
  | .sym s, .sym s', h => by simp only [same, decide_eq_true_eq] at h; rw [h]
  | .int i, .int j, h => by simp only [same, decide_eq_true_eq] at h; rw [h]
  | .other o, .other o', h => by simp only [same, decide_eq_true_eq] at h; rw [h]
  | .expr ka es, .expr kb fs, h => by
    simp only [same, Bool.and_eq_true] at h
    rw [Atom.data_expr, Atom.data_expr, sameList_sound h.2]
  | .sym _, .int _, h => nomatch h
  | .sym _, .other _, h => nomatch h
  | .sym _, .expr _ _, h => nomatch h
  | .int _, .sym _, h => nomatch h
  | .int _, .other _, h => nomatch h
  | .int _, .expr _ _, h => nomatch h
  | .other _, .sym _, h => nomatch h
  | .other _, .int _, h => nomatch h
  | .other _, .expr _ _, h => nomatch h
  | .expr _ _, .sym _, h => nomatch h
  | .expr _ _, .int _, h => nomatch h
  | .expr _ _, .other _, h => nomatch h

theorem sameList_sound : ∀ {as bs : List (Atom Sym O)}, sameList as bs = true →
    Atom.dataList as = Atom.dataList bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [sameList, Bool.and_eq_true] at h
    rw [Atom.dataList_cons, Atom.dataList_cons, same_sound h.1, sameList_sound h.2]
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

end

/-- The kept hashes of an atom agree with a structural hash of its module data, at every
expression it holds (CeTTa keeps the structural hash; only this agreement is used). -/
inductive KeptOK (hash : Data Sym O → Nat) : Atom Sym O → Prop
  /-- A symbol. -/
  | sym (s : Sym) : KeptOK hash (.sym s)
  /-- An integer. -/
  | int (i : Int) : KeptOK hash (.int i)
  /-- Another atom. -/
  | other (o : O) : KeptOK hash (.other o)
  /-- An expression: its kept hash, if any, is the hash of its data, and so for its elements. -/
  | expr (k : Option Nat) (es : List (Atom Sym O)) :
      (∀ h, k = some h → h = hash (.expr (Atom.dataList es))) → (∀ a ∈ es, KeptOK hash a) →
        KeptOK hash (.expr k es)

mutual

/-- **The pruning test never separates equal atoms**: when the kept hashes agree with a structural
hash, `rcm_same` answers `true` on equal module data. -/
theorem same_complete {hash : Data Sym O → Nat} :
    ∀ {a b : Atom Sym O}, KeptOK hash a → KeptOK hash b → a.data = b.data → same a b = true
  | .sym s, .sym s', _, _, h => by simp only [Atom.data_sym, Data.sym.injEq] at h; simp [same, h]
  | .int i, .int j, _, _, h => by
    simp only [Atom.data, Data.int.injEq] at h
    simp [same, h]
  | .other o, .other o', _, _, h => by
    simp only [Atom.data, Data.other.injEq] at h
    simp [same, h]
  | .expr ka es, .expr kb fs, .expr _ _ hka hes, .expr _ _ hkb hfs, h => by
    simp only [Atom.data_expr, Data.expr.injEq] at h
    have hlen : es.length = fs.length := by
      rw [← Atom.length_dataList es, ← Atom.length_dataList fs, h]
    have hp : prune ka kb = false := by
      cases ka with
      | none => rfl
      | some a =>
        cases kb with
        | none => rfl
        | some b =>
          have ha := hka a rfl
          have hb := hkb b rfl
          rw [h] at ha
          simp [prune, ha, hb]
    simp [same, hlen, hp, sameList_complete hes hfs h]
  | .sym _, .int _, _, _, h => by simp [Atom.data] at h
  | .sym _, .other _, _, _, h => by simp [Atom.data] at h
  | .sym _, .expr _ _, _, _, h => by simp [Atom.data] at h
  | .int _, .sym _, _, _, h => by simp [Atom.data] at h
  | .int _, .other _, _, _, h => by simp [Atom.data] at h
  | .int _, .expr _ _, _, _, h => by simp [Atom.data] at h
  | .other _, .sym _, _, _, h => by simp [Atom.data] at h
  | .other _, .int _, _, _, h => by simp [Atom.data] at h
  | .other _, .expr _ _, _, _, h => by simp [Atom.data] at h
  | .expr _ _, .sym _, _, _, h => by simp [Atom.data] at h
  | .expr _ _, .int _, _, _, h => by simp [Atom.data] at h
  | .expr _ _, .other _, _, _, h => by simp [Atom.data] at h

theorem sameList_complete {hash : Data Sym O → Nat} :
    ∀ {as bs : List (Atom Sym O)}, (∀ a ∈ as, KeptOK hash a) → (∀ b ∈ bs, KeptOK hash b) →
      Atom.dataList as = Atom.dataList bs → sameList as bs = true
  | [], [], _, _, _ => rfl
  | a :: as, b :: bs, ha, hb, h => by
    simp only [Atom.dataList_cons, List.cons.injEq] at h
    simp only [sameList, Bool.and_eq_true]
    exact ⟨same_complete (ha a List.mem_cons_self) (hb b List.mem_cons_self) h.1,
      sameList_complete (fun x hx => ha x (List.mem_cons_of_mem _ hx))
        (fun x hx => hb x (List.mem_cons_of_mem _ hx)) h.2⟩
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

end

/-! ### The read -/

/-- What reading needs of the module and of the call: the signature (`rcm_ctor_of`,
`rc_ctor_judgment`, `rc_ctor_sort`, `rc_ctor_arity`, `rc_ctor_asort`), the handle symbol, the held
values (a valid handle's sort and value; `none` for a stale one), and the builder (`rc_construct`;
`none` where the representation cannot build the value). -/
structure ReadEnv (Sym C S V : Type) where
  /-- The constructor a symbol names. -/
  ctorOf : Sym → Option C
  /-- Whether a constructor is a judgment. -/
  isJudgment : C → Bool
  /-- A constructor's sort. -/
  sortOf : C → S
  /-- A constructor's number of children. -/
  arity : C → Nat
  /-- The sort of a constructor's child. -/
  argSort : C → Nat → S
  /-- `TAG:handle`. -/
  handleSym : Sym
  /-- The held values. -/
  held : Nat → Option (S × V)
  /-- The builder. -/
  construct : C → List V → Option V

/-- How reading fails: the input errors of `rcm_value` (`rcm_input_error`), and `build`, the
refinement violation of a value the representation cannot build. -/
inductive ReadErr (Sym C S : Type) : Type
  /-- `a handle names a natural number`. -/
  | handleNotNat
  /-- `stale handle`. -/
  | staleHandle (h : Nat)
  /-- `handle ... holds a value of sort ..., not ...`. -/
  | handleSort (h : Nat) (held sort : S)
  /-- `not module data (a constructor application expected)`. -/
  | notData
  /-- `unknown constructor`. -/
  | unknownCtor (s : Sym)
  /-- `... is not a constructor of sort ...`. -/
  | notOfSort (c : C) (sort : S)
  /-- `... takes ... arguments, given ...`. -/
  | arity (c : C) (given : Nat)
  /-- `a constructor the representation cannot build`. -/
  | build

/-- What `rcm_handle_index` sees in an expression of a symbol and its elements. -/
inductive HandleRes : Type
  /-- Not a handle (`-1`). -/
  | notHandle
  /-- A handle whose number is not a natural number (`-2`). -/
  | bad
  /-- A handle and its index. -/
  | index (h : Nat)

/-- `rcm_handle_index` of `(sy kids ...)`: a handle is `(TAG:handle N)`, `N` a natural number. -/
def handleOf (hs sy : Sym) : List (Data Sym O) → HandleRes
  | [.int i] => if sy = hs then (if 0 ≤ i then .index i.toNat else .bad) else .notHandle
  | [.sym _] => if sy = hs then .bad else .notHandle
  | [.other _] => if sy = hs then .bad else .notHandle
  | [.expr _] => if sy = hs then .bad else .notHandle
  | [] => .notHandle
  | _ :: _ :: _ => .notHandle

variable [DecidableEq S]

/-- A handle's value, of the sort asked. -/
def readHandle (E : ReadEnv Sym C S V) (h : Nat) (sort : S) : Except (ReadErr Sym C S) V :=
  match E.held h with
  | none => .error (.staleHandle h)
  | some (s, v) => if s = sort then .ok v else .error (.handleSort h s sort)

/-- The checks of `rcm_value` on a constructor's symbol with `n` children, at a sort. -/
def ctorCheck (E : ReadEnv Sym C S V) (sy : Sym) (n : Nat) (sort : S) :
    Except (ReadErr Sym C S) C :=
  match E.ctorOf sy with
  | none => .error (.unknownCtor sy)
  | some c =>
    if E.isJudgment c = true ∨ E.sortOf c ≠ sort then .error (.notOfSort c sort)
    else if n ≠ E.arity c then .error (.arity c n)
    else .ok c

/-- `rc_construct`. -/
def buildV (E : ReadEnv Sym C S V) (c : C) (vs : List V) : Except (ReadErr Sym C S) V :=
  match E.construct c vs with
  | none => .error .build
  | some v => .ok v

mutual

/-- **The read without the reuse table**: module data of a sort to a value (`rcm_value` without
`rcm_seen_get`), a function of the module data. -/
def read (E : ReadEnv Sym C S V) : Data Sym O → S → Except (ReadErr Sym C S) V
  | .sym sy, sort =>
    match ctorCheck E sy 0 sort with
    | .error e => .error e
    | .ok c => buildV E c []
  | .expr (.sym sy :: kids), sort =>
    match handleOf E.handleSym sy kids with
    | .bad => .error .handleNotNat
    | .index h => readHandle E h sort
    | .notHandle =>
      match ctorCheck E sy kids.length sort with
      | .error e => .error e
      | .ok c =>
        match readKids E c 0 kids with
        | .error e => .error e
        | .ok vs => buildV E c vs
  | .int _, _ => .error .notData
  | .other _, _ => .error .notData
  | .expr [], _ => .error .notData
  | .expr (.int _ :: _), _ => .error .notData
  | .expr (.other _ :: _), _ => .error .notData
  | .expr (.expr _ :: _), _ => .error .notData

/-- The children, in order, each of its sort; the first failure ends the reading. -/
def readKids (E : ReadEnv Sym C S V) (c : C) :
    Nat → List (Data Sym O) → Except (ReadErr Sym C S) (List V)
  | _, [] => .ok []
  | i, k :: ks =>
    match read E k (E.argSort c i) with
    | .error e => .error e
    | .ok v =>
      match readKids E c (i + 1) ks with
      | .error e => .error e
      | .ok vs => .ok (v :: vs)

end

/-- An entry of the reuse table (`RcmSeen`): the atom read, its kept hash, its sort, its value. -/
structure SeenEntry (Sym O S V : Type) where
  /-- The atom. -/
  atom : Atom Sym O
  /-- Its kept hash. -/
  hash : Nat
  /-- Its sort. -/
  sort : S
  /-- Its value. -/
  val : V

/-- The reuse table of a call. -/
abbrev Seen (Sym O S V : Type) := List (SeenEntry Sym O S V)

/-- What `rcm_seen_get` may answer: the value of an entry with the hash and the sort asked, whose
atom `rcm_same` says is the atom read (whichever such entry the probe meets first). -/
def GetOK (get : Seen Sym O S V → Atom Sym O → Nat → S → Option V) : Prop :=
  ∀ seen x h sort v, get seen x h sort = some v →
    ∃ e ∈ seen, e.hash = h ∧ e.sort = sort ∧ same e.atom x = true ∧ e.val = v

/-- `rcm_seen_put`: the atom kept with its value, when it has a kept hash. -/
def putSeen (k : Option Nat) (x : Atom Sym O) (sort : S) (v : V) (seen : Seen Sym O S V) :
    Seen Sym O S V :=
  match k with
  | some h => seen ++ [⟨x, h, sort, v⟩]
  | none => seen

mutual

/-- **The read with the reuse table** (`rcm_value`): a handle or a constructor's symbol checked as
before; a constructor without children built at once; otherwise, when the atom has a kept hash and
the table holds an atom the same (`get`), that atom's value; otherwise the children read in order,
the value built, and kept in the table with the atom when it has a kept hash. -/
def readSeen (E : ReadEnv Sym C S V) (get : Seen Sym O S V → Atom Sym O → Nat → S → Option V) :
    Atom Sym O → S → Seen Sym O S V → Except (ReadErr Sym C S) (V × Seen Sym O S V)
  | .sym sy, sort, seen =>
    match ctorCheck E sy 0 sort with
    | .error e => .error e
    | .ok c =>
      match buildV E c [] with
      | .error e => .error e
      | .ok v => .ok (v, seen)
  | .expr k (.sym sy :: kids), sort, seen =>
    match handleOf E.handleSym sy (Atom.dataList kids) with
    | .bad => .error .handleNotNat
    | .index h =>
      match readHandle E h sort with
      | .error e => .error e
      | .ok v => .ok (v, seen)
    | .notHandle =>
      match ctorCheck E sy kids.length sort with
      | .error e => .error e
      | .ok c =>
        if kids = [] then
          match buildV E c [] with
          | .error e => .error e
          | .ok v => .ok (v, seen)
        else
          match k.bind (fun h => get seen (.expr k (.sym sy :: kids)) h sort) with
          | some v => .ok (v, seen)
          | none =>
            match readKidsSeen E get c 0 kids seen with
            | .error e => .error e
            | .ok (vs, seen') =>
              match buildV E c vs with
              | .error e => .error e
              | .ok v => .ok (v, putSeen k (.expr k (.sym sy :: kids)) sort v seen')
  | .int _, _, _ => .error .notData
  | .other _, _, _ => .error .notData
  | .expr _ [], _, _ => .error .notData
  | .expr _ (.int _ :: _), _, _ => .error .notData
  | .expr _ (.other _ :: _), _, _ => .error .notData
  | .expr _ (.expr _ _ :: _), _, _ => .error .notData

/-- The children with the reuse table, in order. -/
def readKidsSeen (E : ReadEnv Sym C S V) (get : Seen Sym O S V → Atom Sym O → Nat → S → Option V)
    (c : C) : Nat → List (Atom Sym O) → Seen Sym O S V →
      Except (ReadErr Sym C S) (List V × Seen Sym O S V)
  | _, [], seen => .ok ([], seen)
  | i, a :: as, seen =>
    match readSeen E get a (E.argSort c i) seen with
    | .error e => .error e
    | .ok (v, seen') =>
      match readKidsSeen E get c (i + 1) as seen' with
      | .error e => .error e
      | .ok (vs, seen'') => .ok (v :: vs, seen'')

end

/-- **The reuse table's invariant**: every entry's value is what its atom reads as at its sort. -/
def SeenOK (E : ReadEnv Sym C S V) (seen : Seen Sym O S V) : Prop :=
  ∀ e ∈ seen, read E e.atom.data e.sort = .ok e.val

/-- A result with the table agrees with a result without it: the same value (and an invariant
table), or the same error. -/
def Agrees {α : Type} (E : ReadEnv Sym C S V) (r : Except (ReadErr Sym C S) (α × Seen Sym O S V))
    (r₀ : Except (ReadErr Sym C S) α) : Prop :=
  match r with
  | .ok (v, seen') => r₀ = .ok v ∧ SeenOK E seen'
  | .error e => r₀ = .error e

omit [DecidableEq O] in
theorem Agrees.map_fst {α : Type} {E : ReadEnv Sym C S V}
    {r : Except (ReadErr Sym C S) (α × Seen Sym O S V)} {r₀ : Except (ReadErr Sym C S) α}
    (h : Agrees E r r₀) : r.map Prod.fst = r₀ := by
  cases r with
  | error e => exact h.symm
  | ok p => obtain ⟨v, seen'⟩ := p; exact h.1.symm

/-- A hit of the reuse table answers what the atom reads as. -/
theorem seenHit_read {E : ReadEnv Sym C S V} {get : Seen Sym O S V → Atom Sym O → Nat → S → Option V}
    (hget : GetOK get) {seen : Seen Sym O S V} (hok : SeenOK E seen) {x : Atom Sym O} {h : Nat}
    {sort : S} {v : V} (hg : get seen x h sort = some v) : read E x.data sort = .ok v := by
  obtain ⟨e, he, _, hs, hsame, hv⟩ := hget seen x h sort v hg
  rw [← same_sound hsame, ← hs, ← hv]
  exact hok e he

mutual

/-- **Reading with the reuse table gives what reading without it gives**: the same value, or the
same error. -/
theorem readSeen_agrees (E : ReadEnv Sym C S V)
    {get : Seen Sym O S V → Atom Sym O → Nat → S → Option V} (hget : GetOK get) :
    ∀ (x : Atom Sym O) (sort : S) (seen : Seen Sym O S V), SeenOK E seen →
      Agrees E (readSeen E get x sort seen) (read E x.data sort)
  | .sym sy, sort, seen, hok => by
    simp only [readSeen, Atom.data_sym, read]
    cases ctorCheck E sy 0 sort with
    | error e => exact rfl
    | ok c =>
      dsimp only
      cases buildV E c [] with
      | error e => exact rfl
      | ok v => exact ⟨rfl, hok⟩
  | .expr k (.sym sy :: kids), sort, seen, hok => by
    simp only [readSeen, Atom.data_expr, Atom.dataList_cons, Atom.data_sym, read,
      Atom.length_dataList]
    cases hh : handleOf E.handleSym sy (Atom.dataList kids) with
    | bad => exact rfl
    | index h =>
      dsimp only
      cases readHandle E h sort with
      | error e => exact rfl
      | ok v => exact ⟨rfl, hok⟩
    | notHandle =>
      dsimp only
      cases hc : ctorCheck E sy kids.length sort with
      | error e => exact rfl
      | ok c =>
        dsimp only
        by_cases hk : kids = []
        · subst hk
          rw [if_pos rfl]
          simp only [Atom.dataList_nil, readKids]
          cases buildV E c [] with
          | error e => exact rfl
          | ok v => exact ⟨rfl, hok⟩
        · rw [if_neg hk]
          have hrec := readKidsSeen_agrees E hget c 0 kids seen hok
          cases hg : k.bind (fun h => get seen (.expr k (.sym sy :: kids)) h sort) with
          | some v =>
            dsimp only
            refine ⟨?_, hok⟩
            obtain ⟨h, _, hgv⟩ := Option.bind_eq_some_iff.mp hg
            have hr := seenHit_read hget hok hgv
            simp only [Atom.data_expr, Atom.dataList_cons, Atom.data_sym, read, hh, hc,
              Atom.length_dataList] at hr
            exact hr
          | none =>
            dsimp only
            cases hks : readKidsSeen E get c 0 kids seen with
            | error e =>
              rw [hks] at hrec
              have hr : readKids E c 0 (Atom.dataList kids) = .error e := hrec
              rw [hr]
              exact rfl
            | ok p =>
              obtain ⟨vs, seen'⟩ := p
              rw [hks] at hrec
              obtain ⟨hvs, hok'⟩ := hrec
              rw [hvs]
              dsimp only
              cases hb : buildV E c vs with
              | error e => exact rfl
              | ok v =>
                refine ⟨rfl, ?_⟩
                cases k with
                | none => exact hok'
                | some h =>
                  intro e he
                  rcases List.mem_append.mp he with he | he
                  · exact hok' e he
                  · rw [List.mem_singleton] at he
                    subst he
                    show read E (Atom.expr (some h) (.sym sy :: kids)).data sort = .ok v
                    simp only [Atom.data_expr, Atom.dataList_cons, Atom.data_sym, read, hh, hc,
                      Atom.length_dataList, hvs]
                    exact hb
  | .int _, _, _, _ => rfl
  | .other _, _, _, _ => rfl
  | .expr _ [], _, _, _ => rfl
  | .expr _ (.int _ :: _), _, _, _ => rfl
  | .expr _ (.other _ :: _), _, _, _ => rfl
  | .expr _ (.expr _ _ :: _), _, _, _ => rfl

theorem readKidsSeen_agrees (E : ReadEnv Sym C S V)
    {get : Seen Sym O S V → Atom Sym O → Nat → S → Option V} (hget : GetOK get) :
    ∀ (c : C) (i : Nat) (kids : List (Atom Sym O)) (seen : Seen Sym O S V), SeenOK E seen →
      Agrees E (readKidsSeen E get c i kids seen) (readKids E c i (Atom.dataList kids))
  | _, _, [], seen, hok => ⟨rfl, hok⟩
  | c, i, a :: as, seen, hok => by
    simp only [readKidsSeen, Atom.dataList_cons, readKids]
    have h₁ := readSeen_agrees E hget a (E.argSort c i) seen hok
    cases hr : readSeen E get a (E.argSort c i) seen with
    | error e =>
      rw [hr] at h₁
      have h₁' : read E a.data (E.argSort c i) = .error e := h₁
      rw [h₁']
      exact rfl
    | ok p =>
      obtain ⟨v, seen'⟩ := p
      rw [hr] at h₁
      obtain ⟨hv, hok'⟩ := h₁
      rw [hv]
      dsimp only
      have h₂ := readKidsSeen_agrees E hget c (i + 1) as seen' hok'
      cases hrs : readKidsSeen E get c (i + 1) as seen' with
      | error e =>
        rw [hrs] at h₂
        have h₂' : readKids E c (i + 1) (Atom.dataList as) = .error e := h₂
        rw [h₂']
        exact rfl
      | ok q =>
        obtain ⟨vs, seen''⟩ := q
        rw [hrs] at h₂
        obtain ⟨hvs, hok''⟩ := h₂
        rw [hvs]
        exact ⟨rfl, hok''⟩

end

/-- **The reuse table changes no value and no error**: in a call, reading every argument with the
table (empty at the call's start) gives what reading each without it gives. -/
theorem readSeen_eq (E : ReadEnv Sym C S V)
    {get : Seen Sym O S V → Atom Sym O → Nat → S → Option V} (hget : GetOK get)
    (x : Atom Sym O) (sort : S) {seen : Seen Sym O S V} (hok : SeenOK E seen) :
    (readSeen E get x sort seen).map Prod.fst = read E x.data sort :=
  (readSeen_agrees E hget x sort seen hok).map_fst

/-- Two atoms that `rcm_same` says are the same read as the same value, at every sort. -/
theorem read_of_same (E : ReadEnv Sym C S V) {a b : Atom Sym O} (h : same a b = true) (sort : S) :
    read E a.data sort = read E b.data sort := by
  rw [same_sound h]

/-- A lookup by the first entry that matches (`rcm_seen_get`'s probe meets some matching entry
first; any such choice is allowed by `GetOK`). -/
def seenFind (seen : Seen Sym O S V) (x : Atom Sym O) (h : Nat) (sort : S) : Option V :=
  (seen.find? fun e => decide (e.hash = h) && decide (e.sort = sort) && same e.atom x).map (·.val)

theorem seenFind_getOK : GetOK (seenFind (Sym := Sym) (O := O) (S := S) (V := V)) := by
  intro seen x h sort v hv
  simp only [seenFind, Option.map_eq_some_iff] at hv
  obtain ⟨e, he, rfl⟩ := hv
  have hp := List.find?_some he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨e, List.mem_of_find?_eq_some he, hp.1.1, hp.1.2, hp.2, rfl⟩

end Read

/-! ## Writing values as atoms with sharing (`rcm_atom_of`, `rcm_shown_get`, `rcm_shown_put`) -/

section Write

variable {W C S : Type} [DecidableEq W]

/-- What writing needs of the module: the view of a value at a sort (`rc_view`: its constructor and
children; `none` where it cannot be read), the children's sorts (`rc_ctor_asort`), and which values
are interned (`rc_sort_rep[sort] == RC_REP_INTERN && RC_IS_FOREIGN(t)`). -/
structure WriteEnv (W C S : Type) where
  /-- `rc_view`. -/
  view : S → W → Option (C × List W)
  /-- The sort of a constructor's child. -/
  argSort : C → Nat → S
  /-- Whether a value of a sort is an interned node. -/
  interned : S → W → Bool

/-- An atom as the glue writes it: `(CTOR KID ...)` (a constructor without children as `(CTOR)`), or
the symbol `:unreadable`. -/
inductive Out (C : Type) : Type
  /-- `:unreadable`. -/
  | unreadable
  /-- A constructor over its children's atoms. -/
  | app (c : C) (kids : List (Out C))

mutual

/-- **The atom written for a value without sharing**: its constructor over the atoms of its
children, each at its sort. -/
inductive Writes (E : WriteEnv W C S) : S → W → Out C → Prop
  /-- A value that cannot be read. -/
  | unreadable {s : S} {t : W} : E.view s t = none → Writes E s t .unreadable
  /-- A constructor and its children. -/
  | app {s : S} {t : W} {c : C} {ks : List W} {xs : List (Out C)} :
      E.view s t = some (c, ks) → WritesKids E c 0 ks xs → Writes E s t (.app c xs)

/-- The children's atoms, in order. -/
inductive WritesKids (E : WriteEnv W C S) : C → Nat → List W → List (Out C) → Prop
  /-- No more children. -/
  | nil {c : C} {i : Nat} : WritesKids E c i [] []
  /-- A child at its sort, then the rest. -/
  | cons {c : C} {i : Nat} {k : W} {ks : List W} {x : Out C} {xs : List (Out C)} :
      Writes E (E.argSort c i) k x → WritesKids E c (i + 1) ks xs → WritesKids E c i (k :: ks) (x :: xs)

end

omit [DecidableEq W] in
mutual

/-- One atom is written for a value: the view is a function. -/
theorem Writes.functional {E : WriteEnv W C S} :
    ∀ {s : S} {t : W} {x x' : Out C}, Writes E s t x → Writes E s t x' → x = x'
  | _, _, _, _, .unreadable _, .unreadable _ => rfl
  | _, _, _, _, .unreadable h, .app h' _ => by rw [h] at h'; cases h'
  | _, _, _, _, .app h _, .unreadable h' => by rw [h] at h'; cases h'
  | _, _, _, _, .app h hk, .app h' hk' => by
    rw [h] at h'
    cases h'
    rw [WritesKids.functional hk hk']

theorem WritesKids.functional {E : WriteEnv W C S} :
    ∀ {c : C} {i : Nat} {ks : List W} {xs xs' : List (Out C)},
      WritesKids E c i ks xs → WritesKids E c i ks xs' → xs = xs'
  | _, _, _, _, _, .nil, .nil => rfl
  | _, _, _, _, _, .cons h hk, .cons h' hk' => by
    rw [Writes.functional h h', WritesKids.functional hk hk']

end

omit [DecidableEq W] in
/-- The atom written for a value depends on its sort only through its view. -/
theorem Writes.resort {E : WriteEnv W C S} {s s' : S} {t : W} {x : Out C} (h : Writes E s t x)
    (hv : E.view s t = E.view s' t) : Writes E s' t x := by
  cases h with
  | unreadable h => exact .unreadable (hv ▸ h)
  | app h hk => exact .app (hv ▸ h) hk

/-- `rcm_shown_get`: the atom written before for a value, by identity of the value. -/
def shownGet : List (W × Out C) → W → Option (Out C)
  | [], _ => none
  | (v, x) :: rest, t => if v = t then some x else shownGet rest t

theorem mem_of_shownGet : ∀ {tbl : List (W × Out C)} {t : W} {x : Out C},
    shownGet tbl t = some x → (t, x) ∈ tbl
  | [], _, _, h => nomatch h
  | (v, y) :: rest, t, x, h => by
    unfold shownGet at h
    split at h
    · rename_i hv
      cases h
      subst hv
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_shownGet h)

mutual

/-- **The atom written with sharing** (`rcm_atom_of`): an interned value written before in the result
is that atom; otherwise its constructor over its children's atoms, kept for the value when it is
interned and has children (`rcm_shown_put`, which keeps nothing when its table cannot grow). -/
inductive WritesS (E : WriteEnv W C S) :
    List (W × Out C) → S → W → Out C → List (W × Out C) → Prop
  /-- An interned value written before. -/
  | shown {tbl : List (W × Out C)} {s : S} {t : W} {x : Out C} :
      E.interned s t = true → shownGet tbl t = some x → WritesS E tbl s t x tbl
  /-- A value not written before (or not interned) that cannot be read. -/
  | unreadable {tbl : List (W × Out C)} {s : S} {t : W} :
      (E.interned s t = true → shownGet tbl t = none) → E.view s t = none →
        WritesS E tbl s t .unreadable tbl
  /-- A value not written before (or not interned): its atom, kept for an interned value with
  children. -/
  | appPut {tbl : List (W × Out C)} {s : S} {t : W} {c : C} {ks : List W} {xs : List (Out C)}
      {tbl' : List (W × Out C)} :
      (E.interned s t = true → shownGet tbl t = none) → E.view s t = some (c, ks) →
        WritesKidsS E tbl c 0 ks xs tbl' → E.interned s t = true → ks ≠ [] →
          WritesS E tbl s t (.app c xs) ((t, .app c xs) :: tbl')
  /-- ... or not kept. -/
  | appKeep {tbl : List (W × Out C)} {s : S} {t : W} {c : C} {ks : List W} {xs : List (Out C)}
      {tbl' : List (W × Out C)} :
      (E.interned s t = true → shownGet tbl t = none) → E.view s t = some (c, ks) →
        WritesKidsS E tbl c 0 ks xs tbl' → WritesS E tbl s t (.app c xs) tbl'

/-- The children with sharing, in order, the table passed along. -/
inductive WritesKidsS (E : WriteEnv W C S) :
    List (W × Out C) → C → Nat → List W → List (Out C) → List (W × Out C) → Prop
  /-- No more children. -/
  | nil {tbl : List (W × Out C)} {c : C} {i : Nat} : WritesKidsS E tbl c i [] [] tbl
  /-- A child at its sort, then the rest. -/
  | cons {tbl : List (W × Out C)} {c : C} {i : Nat} {k : W} {ks : List W} {x : Out C}
      {xs : List (Out C)} {tbl' tbl'' : List (W × Out C)} :
      WritesS E tbl (E.argSort c i) k x tbl' → WritesKidsS E tbl' c (i + 1) ks xs tbl'' →
        WritesKidsS E tbl c i (k :: ks) (x :: xs) tbl''

end

/-- **The sharing table's invariant**: every atom kept is the atom written for its value, at a sort
where the value is interned. -/
def ShownOK (E : WriteEnv W C S) (tbl : List (W × Out C)) : Prop :=
  ∀ t x, (t, x) ∈ tbl → ∃ s, E.interned s t = true ∧ Writes E s t x

/-- The view of an interned value reads the node whatever the sort asked (`RC_TAG_intern`,
`RC_KID_intern`). -/
def InternedView (E : WriteEnv W C S) : Prop :=
  ∀ s s' t, E.interned s t = true → E.interned s' t = true → E.view s t = E.view s' t

mutual

/-- **Sharing writes the atom written without it**, and keeps the table's invariant. -/
theorem WritesS.sound {E : WriteEnv W C S} (hv : InternedView E) :
    ∀ {tbl : List (W × Out C)} {s : S} {t : W} {x : Out C} {tbl' : List (W × Out C)},
      ShownOK E tbl → WritesS E tbl s t x tbl' → Writes E s t x ∧ ShownOK E tbl'
  | _, _, _, _, _, hok, .shown hi hg => by
    obtain ⟨s₀, hi₀, hw⟩ := hok _ _ (mem_of_shownGet hg)
    exact ⟨hw.resort (hv _ _ _ hi₀ hi), hok⟩
  | _, _, _, _, _, hok, .unreadable _ h => ⟨.unreadable h, hok⟩
  | _, s, t, _, _, hok, .appPut _ h hk hi _ => by
    obtain ⟨hw, hok'⟩ := WritesKidsS.sound hv hok hk
    refine ⟨.app h hw, ?_⟩
    intro t' x' hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      exact ⟨s, hi, .app h hw⟩
    · exact hok' t' x' hm
  | _, _, _, _, _, hok, .appKeep _ h hk => by
    obtain ⟨hw, hok'⟩ := WritesKidsS.sound hv hok hk
    exact ⟨.app h hw, hok'⟩

theorem WritesKidsS.sound {E : WriteEnv W C S} (hv : InternedView E) :
    ∀ {tbl : List (W × Out C)} {c : C} {i : Nat} {ks : List W} {xs : List (Out C)}
      {tbl' : List (W × Out C)},
      ShownOK E tbl → WritesKidsS E tbl c i ks xs tbl' → WritesKids E c i ks xs ∧ ShownOK E tbl'
  | _, _, _, _, _, _, hok, .nil => ⟨.nil, hok⟩
  | _, _, _, _, _, _, hok, .cons h hk => by
    obtain ⟨hw, hok₁⟩ := WritesS.sound hv hok h
    obtain ⟨hws, hok₂⟩ := WritesKidsS.sound hv hok₁ hk
    exact ⟨.cons hw hws, hok₂⟩

end

mutual

/-- Conversely, the atom written without sharing is written with it, from any table that keeps the
invariant. -/
theorem Writes.shared {E : WriteEnv W C S} (hv : InternedView E) :
    ∀ {s : S} {t : W} {x : Out C}, Writes E s t x →
      ∀ tbl : List (W × Out C), ShownOK E tbl → ∃ tbl', WritesS E tbl s t x tbl'
  | s, t, x, hw, tbl, hok => by
    by_cases hshown : E.interned s t = true ∧ ∃ x', shownGet tbl t = some x'
    · obtain ⟨hi, x', hg⟩ := hshown
      obtain ⟨s₀, hi₀, hw'⟩ := hok _ _ (mem_of_shownGet hg)
      have : x' = x := Writes.functional (hw'.resort (hv _ _ _ hi₀ hi)) hw
      subst this
      exact ⟨tbl, .shown hi hg⟩
    · have hmiss : E.interned s t = true → shownGet tbl t = none := by
        intro hi
        cases hg : shownGet tbl t with
        | none => rfl
        | some x' => exact absurd ⟨hi, x', hg⟩ hshown
      match hw with
      | .unreadable h => exact ⟨tbl, .unreadable hmiss h⟩
      | .app h hk =>
        obtain ⟨tbl', hk'⟩ := WritesKids.shared hv hk tbl hok
        exact ⟨tbl', .appKeep hmiss h hk'⟩

theorem WritesKids.shared {E : WriteEnv W C S} (hv : InternedView E) :
    ∀ {c : C} {i : Nat} {ks : List W} {xs : List (Out C)}, WritesKids E c i ks xs →
      ∀ tbl : List (W × Out C), ShownOK E tbl → ∃ tbl', WritesKidsS E tbl c i ks xs tbl'
  | _, _, _, _, .nil, tbl, _ => ⟨tbl, .nil⟩
  | _, _, _, _, .cons h hk, tbl, hok => by
    obtain ⟨tbl₁, h₁⟩ := Writes.shared hv h tbl hok
    have hok₁ := (WritesS.sound hv hok h₁).2
    obtain ⟨tbl₂, h₂⟩ := WritesKids.shared hv hk tbl₁ hok₁
    exact ⟨tbl₂, .cons h₁ h₂⟩

end

/-- **Sharing changes only identity, not structure**: for a result (the table empty at its start,
`rcm_atom`), the atoms written with sharing are exactly the atom written without it. -/
theorem writesS_iff {E : WriteEnv W C S} (hv : InternedView E) {s : S} {t : W} {x : Out C} :
    (∃ tbl', WritesS E [] s t x tbl') ↔ Writes E s t x :=
  ⟨fun ⟨_, h⟩ => (WritesS.sound hv (fun _ _ h => by simp at h) h).1,
    fun h => Writes.shared hv h [] (fun _ _ h => by simp at h)⟩

/-- One atom: every atom written with sharing is the atom written without it. -/
theorem writesS_unique {E : WriteEnv W C S} (hv : InternedView E) {s : S} {t : W} {x x' : Out C}
    {tbl : List (W × Out C)} (h : WritesS E [] s t x tbl) (h' : Writes E s t x') : x = x' :=
  Writes.functional ((WritesS.sound hv (fun _ _ h => by simp at h) h).1) h'

end Write

/-! ### Identity of interned values is equality of their module data -/

section Identity

variable {L : Type u} [Inhabited L] {X : Type v}

/-- **Sharing by identity finds every equal value**: in an interning store, a value is in a table
keyed by values exactly when a value equal to it as module data (its read-back) is
(`interning_eq_iff`), so the table of the atoms written shares every repeated value. -/
theorem shown_by_identity {s : Store L} (hs : Interning s) (tbl : List (Nat × X))
    (hkeys : ∀ p ∈ tbl, p.1 < s.length) {i : Nat} (hi : i < s.length) :
    (∃ x, (i, x) ∈ tbl) ↔ ∃ j x, (j, x) ∈ tbl ∧ readback s j = readback s i := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨i, x, hx, rfl⟩
  · rintro ⟨j, x, hx, hj⟩
    have hjl : j < s.length := hkeys (j, x) hx
    rw [(interning_eq_iff hs hjl hi).mp hj] at hx
    exact ⟨x, hx⟩

end Identity

/-! ## Examples -/

section Examples

/-! ### The front cache -/

/-- A store of two leaves. -/
def exStore : Store Bool := [⟨true, []⟩, ⟨false, []⟩]

/-- Calls, a collection, and calls again; every contents hashed to one slot, so entries replace each
other. -/
def exOps : List (Op Bool) :=
  [.intern ⟨true, []⟩, .intern ⟨false, []⟩, .intern ⟨true, []⟩, .intern ⟨true, [0, 1]⟩,
    .intern ⟨true, [0, 1]⟩, .collect [⟨false, []⟩], .intern ⟨true, []⟩, .intern ⟨false, []⟩]

/-- With the cache, the run answers as without it. -/
example : runFront (fun _ => 0) (fun _ => 0) Front.empty [] exOps = runPlain [] exOps := by decide
example : (runPlain [] exOps).2 = [0, 1, 0, 2, 2, 1, 0] := by decide

/-- An entry that holds another node than its key's contents breaks the answer: the `true` leaf
answered with node `1`, the `false` leaf. -/
example : (internFront (fun _ => 0) (fun _ => 0) (Front.empty.set 0 ⟨true, [], 0, 1⟩) exStore
    ⟨true, []⟩).2.2 = 1 := by decide
example : (intern exStore ⟨true, []⟩).2 = 0 := by decide
example : ¬ FrontOK (Front.empty.set 0 ⟨true, [], 0, 1⟩) exStore := by
  intro h
  have := h 0 ⟨true, [], 0, 1⟩ (by simp [Front.set])
  simp [exStore] at this

/-- Without the clear, an entry kept across a collection answers a node the collection replaced:
the store `[true]` collected to `[false]`, and the `true` leaf answered with node `0`. -/
example : (internFront (fun _ => 0) (fun _ => 0) (Front.empty.set 0 ⟨true, [], 0, 0⟩)
    [⟨false, []⟩] ⟨true, []⟩).2.2 = 0 := by decide
example : (intern [⟨false, []⟩] ⟨true, []⟩).2 = 1 := by decide

/-! ### Reading atoms -/

/-- A module: the constructors `pair` (`0`, of sort `0`, two children of sort `1`), `f` (`1`, of sort
`1`, one child of sort `1`), `a` (`2`) and `b` (`3`), leaves of sort `1`, named by the symbols `10`,
`11`, `12`, `13`; handles are `(99 N)`, handle `0` holding the leaf `a`; values are trees. -/
def exRead : ReadEnv Nat Nat Nat (Tree Nat) where
  ctorOf
    | 10 => some 0
    | 11 => some 1
    | 12 => some 2
    | 13 => some 3
    | _ => none
  isJudgment _ := false
  sortOf c := if c = 0 then 0 else 1
  arity
    | 0 => 2
    | 1 => 1
    | _ => 0
  argSort _ _ := 1
  handleSym := 99
  held
    | 0 => some (1, .node 2 [])
    | _ => none
  construct c vs := some (.node c vs)

/-- `(pair (f a) (f a))`, both `(f a)` with the same kept hash. -/
def exAtom : Atom Nat Unit :=
  .expr (some 5) [.sym 10, .expr (some 6) [.sym 11, .sym 12], .expr (some 6) [.sym 11, .sym 12]]

/-- Read without the table. -/
example : read exRead exAtom.data 0 =
    .ok (.node 0 [.node 1 [.node 2 []], .node 1 [.node 2 []]]) := rfl

/-- Read with the table: the same value; the second `(f a)` is the first's (two entries kept). -/
example : (readSeen exRead seenFind exAtom 0 []).map Prod.fst =
    .ok (.node 0 [.node 1 [.node 2 []], .node 1 [.node 2 []]]) := rfl
example : (readSeen exRead seenFind exAtom 0 []).map (·.2.length) = .ok 2 := rfl

/-- A handle reads as its value; the same error with and without the table. -/
example : read exRead (Atom.expr none [.sym 11, .expr none [.sym 99, .int 0]] : Atom Nat Unit).data 1 =
    .ok (.node 1 [.node 2 []]) := rfl
example : (readSeen exRead seenFind
    (.expr (some 1) [.sym 10, .expr (some 6) [.sym 11, .sym 12], .expr (some 6) [.sym 11, .sym 14]] :
      Atom Nat Unit) 0 []).map Prod.fst = .error (.unknownCtor 14) := rfl
example : read exRead (Atom.expr (some 1)
    [.sym 10, .expr (some 6) [.sym 11, .sym 12], .expr (some 6) [.sym 11, .sym 14]] : Atom Nat Unit).data
      0 = .error (.unknownCtor 14) := rfl

/-- A lookup that skips `rcm_same` (the hash and the sort only) reuses `(f a)` for `(f b)`, whose
kept hash collides: a different value. -/
def badGet (seen : Seen Nat Unit Nat (Tree Nat)) (_ : Atom Nat Unit) (h : Nat) (sort : Nat) :
    Option (Tree Nat) :=
  (seen.find? fun e => decide (e.hash = h) && decide (e.sort = sort)).map (·.val)

example : (readSeen exRead badGet
    (.expr (some 5) [.sym 10, .expr (some 6) [.sym 11, .sym 12], .expr (some 6) [.sym 11, .sym 13]] :
      Atom Nat Unit) 0 []).map Prod.fst =
    .ok (.node 0 [.node 1 [.node 2 []], .node 1 [.node 2 []]]) := rfl
example : read exRead (Atom.expr (some 5)
    [.sym 10, .expr (some 6) [.sym 11, .sym 12], .expr (some 6) [.sym 11, .sym 13]] : Atom Nat Unit).data
      0 = .ok (.node 0 [.node 1 [.node 2 []], .node 1 [.node 3 []]]) := rfl

/-- `rcm_same`: equal data with one hash kept is the same; kept hashes that disagree with equal data
(no structural hash could keep them) separate it. -/
example : same (Atom.expr (some 1) [.sym 0] : Atom Nat Unit) (.expr none [.sym 0]) = true := by
  decide
example : same (Atom.expr (some 1) [.sym 0] : Atom Nat Unit) (.expr (some 2) [.sym 0]) = false := by
  decide
example : same (Atom.sym 0 : Atom Nat Unit) (.int 0) = false := by decide

/-! ### Writing atoms -/

/-- Values `0` (the leaf `2`), `1` (`1` over `0`), `2` (`0` over `1` twice), all interned. -/
def exWrite : WriteEnv Nat Nat Unit where
  view _ t := match t with
    | 0 => some (2, [])
    | 1 => some (1, [0])
    | 2 => some (0, [1, 1])
    | _ => none
  argSort _ _ := ()
  interned _ t := decide (t ≤ 2)

/-- Value `2` written with sharing: the second `1` is the atom written for the first; the atom is
the one written without sharing. -/
example : WritesS exWrite [] () 2 (.app 0 [.app 1 [.app 2 []], .app 1 [.app 2 []]])
    [(2, .app 0 [.app 1 [.app 2 []], .app 1 [.app 2 []]]), (1, .app 1 [.app 2 []])] := by
  have h₀ : WritesS exWrite [] () 0 (.app 2 []) [] := .appKeep (fun _ => rfl) rfl .nil
  have h₁ : WritesS exWrite [] () 1 (.app 1 [.app 2 []]) [(1, .app 1 [.app 2 []])] :=
    .appPut (fun _ => rfl) rfl (.cons h₀ .nil) rfl (by simp)
  have h₁' : WritesS exWrite [(1, .app 1 [.app 2 []])] () 1 (.app 1 [.app 2 []])
      [(1, .app 1 [.app 2 []])] := .shown rfl rfl
  exact .appPut (fun _ => rfl) rfl (.cons h₁ (.cons h₁' .nil)) rfl (by simp)

example : Writes exWrite () 2 (.app 0 [.app 1 [.app 2 []], .app 1 [.app 2 []]]) :=
  .app rfl (.cons (.app rfl (.cons (.app rfl .nil) .nil))
    (.cons (.app rfl (.cons (.app rfl .nil) .nil)) .nil))

/-- A table that keeps a wrong atom for `1` writes another atom. -/
example : WritesS exWrite [(1, .unreadable)] () 2 (.app 0 [.unreadable, .unreadable])
    [(1, .unreadable)] :=
  .appKeep (fun _ => rfl) rfl (.cons (.shown rfl rfl) (.cons (.shown rfl rfl) .nil))
example : ¬ ShownOK exWrite [(1, .unreadable)] := by
  intro h
  obtain ⟨_, _, hw⟩ := h 1 .unreadable List.mem_cons_self
  cases hw with
  | unreadable hv => cases hv

/-- Sharing needs the view of an interned value to be one: a value read differently at two sorts
(`5` as `0` over `7` at `true`, as `1` over `7` at `false`) shares the atom of the other sort. -/
def exTwoViews : WriteEnv Nat Nat Bool where
  view s t := match s, t with
    | true, 5 => some (0, [7])
    | false, 5 => some (1, [7])
    | _, 7 => some (2, [])
    | _, _ => none
  argSort _ _ := true
  interned _ _ := true

example : WritesS exTwoViews [(5, .app 0 [.app 2 []])] false 5 (.app 0 [.app 2 []])
    [(5, .app 0 [.app 2 []])] := .shown rfl rfl
example : Writes exTwoViews false 5 (.app 1 [.app 2 []]) := .app rfl (.cons (.app rfl .nil) .nil)
example : ¬ InternedView exTwoViews := fun h => by
  have := h true false 5 rfl rfl
  simp [exTwoViews] at this

end Examples

end Mettapedia.Languages.HOLLight.RuleModuleCaches

/-! ## Axioms -/

#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.injective_intern
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.idxOf?_of_getElem?
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.frontOK_empty
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.frontHit_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.internFront_answer
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.frontOK_internFront
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.runFront_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.runFront_eq_nil
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.same_refl
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.same_sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.same_complete
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.seenHit_read
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.readSeen_agrees
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.readKidsSeen_agrees
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.readSeen_eq
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.read_of_same
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.seenFind_getOK
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.Writes.functional
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.Writes.resort
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.WritesS.sound
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.Writes.shared
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.writesS_iff
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.writesS_unique
#print axioms Mettapedia.Languages.HOLLight.RuleModuleCaches.shown_by_identity
