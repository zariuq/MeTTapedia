import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-!
# Persistent sets: both versions stay valid, at the cost of one path

The other way to give `insert` its value semantics is to never write a cell that a version can
reach, and to share everything else. A set of bit strings is kept as a binary trie in a heap of
nodes (`Trie`): each node says whether the key that ends there is present and points to its two
children. PathMap keeps its paths the same way, over bytes instead of bits.

`Trie.insert` copies the nodes on the path of the new key and points the copies at the old nodes
off the path (path copying).

* `insert_mem_new`: the new version holds the old keys and the new one.
* `insert_mem_old`: every old version still holds exactly what it held: an insert writes only
  fresh cells (`insert_agree`).
* `insert_next`: an insert allocates exactly `length key + 1` nodes. For keys of `n` bits, drawn
  from a universe of `2 ^ n`, that is `n + 1`: logarithmic in the size of the universe.
* Positive control (`Controls.two_versions`): inserting `[false]` into the version holding
  `[true]` gives a version holding both, while the old version still holds only `[true]`; the two
  versions share the node of `[true]` (`Controls.shared_node`).
* Negative control (`Controls.overwrite_breaks_old`): writing the new root's node over the old
  root, which an in-place update would do, makes the old version hold `[false]` too.

What is left out here, and what Perceus does: reuse each node on the path that no other node or
root references, and copy from the first shared node down. `Reuse` proves the condition for one
cell; the trie is where it applies node by node.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.ValuesAndLocations.Persistent

/-- A node: whether the key that ends here is present, and its two children. -/
structure Node where
  present : Bool
  child : Bool → Option ℕ

/-- The node of nothing: no key, no children. -/
def Node.empty : Node := ⟨false, fun _ => none⟩

/-- A heap of nodes, allocated from a counter. -/
structure Trie where
  cell : ℕ → Option Node
  next : ℕ

namespace Trie

/-- The node a reference names; the empty node for none. -/
def node (t : Trie) (p : Option ℕ) : Node := (p.bind t.cell).getD Node.empty

/-- **Membership** of a key in the version rooted at `p`. -/
def mem (t : Trie) : Option ℕ → List Bool → Bool
  | p, [] => (t.node p).present
  | p, b :: bs => t.mem ((t.node p).child b) bs

/-- Allocate a node: it goes to `next`. -/
def alloc (t : Trie) (n : Node) : Trie × ℕ :=
  (⟨Function.update t.cell t.next (some n), t.next + 1⟩, t.next)

/-- **Insert by path copying.** One new node for each node on the key's path; every node off the
path is shared with the version rooted at `p`. The result is the new heap and the new root. -/
def insert (t : Trie) (p : Option ℕ) : List Bool → Trie × ℕ
  | [] => t.alloc ⟨true, (t.node p).child⟩
  | b :: bs =>
      let r := t.insert ((t.node p).child b) bs
      r.1.alloc ⟨(t.node p).present, Function.update (t.node p).child b (some r.2)⟩

/-- Every node lies below `next`, and its children below it. -/
def Closed (t : Trie) : Prop :=
  ∀ p n, t.cell p = some n → p < t.next ∧ ∀ b q, n.child b = some q → q < p

/-- A reference below `next` (or none). -/
def Below (t : Trie) (p : Option ℕ) : Prop := ∀ q, p = some q → q < t.next

/-- `t'` keeps every node of `t`. -/
def Agree (t t' : Trie) : Prop := t.next ≤ t'.next ∧ ∀ q, q < t.next → t'.cell q = t.cell q

theorem Agree.refl (t : Trie) : Agree t t := ⟨le_rfl, fun _ _ => rfl⟩

theorem Agree.trans {t₁ t₂ t₃ : Trie} (a : Agree t₁ t₂) (b : Agree t₂ t₃) : Agree t₁ t₃ :=
  ⟨a.1.trans b.1, fun q lt => (b.2 q (lt_of_lt_of_le lt a.1)).trans (a.2 q lt)⟩

theorem Below.mono {t t' : Trie} {p : Option ℕ} (below : t.Below p) (le : t.next ≤ t'.next) :
    t'.Below p := fun q hq => lt_of_lt_of_le (below q hq) le

theorem below_none (t : Trie) : t.Below none := fun _ h => by cases h

theorem node_agree {t t' : Trie} {p : Option ℕ} (agree : Agree t t') (below : t.Below p) :
    t'.node p = t.node p := by
  cases p with
  | none => rfl
  | some q => simp [node, agree.2 q (below q rfl)]

/-- A child of a node below `next` is below `next`. -/
theorem child_below {t : Trie} (closed : t.Closed) {p : Option ℕ} (below : t.Below p) (b : Bool) :
    t.Below ((t.node p).child b) := by
  intro c hc
  cases p with
  | none => simp [node, Node.empty] at hc
  | some q =>
      cases hq : t.cell q with
      | none => simp [node, hq, Node.empty] at hc
      | some n =>
          simp only [node, Option.bind_some, hq, Option.getD_some] at hc
          exact lt_trans ((closed q n hq).2 b c hc) (below q rfl)

/-- **The frame law of versions**: a heap that keeps every node of `t` gives every version of `t`
the same keys. -/
theorem mem_agree {t t' : Trie} (closed : t.Closed) (agree : Agree t t') :
    ∀ (k : List Bool) {p : Option ℕ}, t.Below p → t'.mem p k = t.mem p k
  | [], p, below => by simp [mem, node_agree agree below]
  | b :: bs, p, below => by
      simp only [mem, node_agree agree below]
      exact mem_agree closed agree bs (child_below closed below b)

theorem alloc_agree (t : Trie) (n : Node) : Agree t (t.alloc n).1 :=
  ⟨Nat.le_succ _, fun q lt => by simp [alloc, Function.update_of_ne lt.ne]⟩

theorem alloc_closed {t : Trie} (closed : t.Closed) {n : Node}
    (children : ∀ b q, n.child b = some q → q < t.next) : (t.alloc n).1.Closed := by
  intro p m hp
  simp only [alloc] at hp ⊢
  by_cases same : p = t.next
  · subst same
    rw [Function.update_self] at hp
    obtain rfl := Option.some.inj hp
    exact ⟨Nat.lt_succ_self _, children⟩
  · rw [Function.update_of_ne same] at hp
    exact ⟨Nat.lt_succ_of_lt (closed p m hp).1, (closed p m hp).2⟩

@[simp] theorem alloc_next (t : Trie) (n : Node) : (t.alloc n).1.next = t.next + 1 := rfl

@[simp] theorem alloc_root (t : Trie) (n : Node) : (t.alloc n).2 = t.next := rfl

theorem alloc_node_root (t : Trie) (n : Node) : (t.alloc n).1.node (some t.next) = n := by
  simp [alloc, node]

/-- **Cost**: an insert allocates one node per level of its key, and one for the key's end. -/
theorem insert_next (t : Trie) (p : Option ℕ) : ∀ k : List Bool,
    (t.insert p k).1.next = t.next + k.length + 1
  | [] => by simp [insert]
  | b :: bs => by
      simp only [insert, alloc_next, List.length_cons]
      rw [insert_next t _ bs]
      omega

/-- The new root is the last node allocated. -/
theorem insert_root (t : Trie) (p : Option ℕ) : ∀ k : List Bool,
    (t.insert p k).2 + 1 = (t.insert p k).1.next
  | [] => by simp [insert]
  | b :: bs => by simp [insert]

/-- **An insert writes only fresh cells.** -/
theorem insert_agree (t : Trie) : ∀ (k : List Bool) (p : Option ℕ), Agree t (t.insert p k).1
  | [], _ => alloc_agree t _
  | _ :: bs, _ => (insert_agree t bs _).trans (alloc_agree _ _)

theorem insert_closed {t : Trie} (closed : t.Closed) :
    ∀ (k : List Bool) {p : Option ℕ}, t.Below p → (t.insert p k).1.Closed
  | [], p, below => by
      refine alloc_closed closed fun b q hq => ?_
      exact child_below closed below b q hq
  | b :: bs, p, below => by
      have agree := insert_agree t bs ((t.node p).child b)
      have closed₁ := insert_closed closed bs (child_below closed below b)
      refine alloc_closed closed₁ fun b' q hq => ?_
      dsimp only at hq
      by_cases same : b' = b
      · subst same
        rw [Function.update_self] at hq
        obtain rfl := Option.some.inj hq
        have := insert_root t ((t.node p).child b') bs
        omega
      · rw [Function.update_of_ne same] at hq
        exact lt_of_lt_of_le (child_below closed below b' q hq) agree.1

/-- **The new version holds the old keys and the new key.** -/
theorem insert_mem_new {t : Trie} (closed : t.Closed) :
    ∀ (k : List Bool) {p : Option ℕ}, t.Below p → ∀ k' : List Bool,
      (t.insert p k).1.mem (some (t.insert p k).2) k' = (decide (k' = k) || t.mem p k')
  | [], p, below, k' => by
      cases k' with
      | nil => simp [insert, mem, alloc_root, alloc_node_root]
      | cons b' bs' =>
          simp only [insert, mem, alloc_root, alloc_node_root, List.cons_ne_nil, decide_false,
            Bool.false_or]
          exact mem_agree closed (alloc_agree t _) bs' (child_below closed below b')
  | b :: bs, p, below, k' => by
      have agree₁ := insert_agree t bs ((t.node p).child b)
      have closed₁ := insert_closed closed bs (child_below closed below b)
      have ih := insert_mem_new closed bs (child_below closed below b)
      cases k' with
      | nil => simp [insert, mem, alloc_root, alloc_node_root]
      | cons b' bs' =>
          simp only [insert, mem, alloc_root, alloc_node_root]
          by_cases same : b' = b
          · subst same
            rw [Function.update_self]
            have rootBelow : (t.insert ((t.node p).child b') bs).1.Below
                (some (t.insert ((t.node p).child b') bs).2) := by
              intro q hq
              obtain rfl := Option.some.inj hq
              have := insert_root t ((t.node p).child b') bs
              omega
            rw [mem_agree closed₁ (alloc_agree _ _) bs' rootBelow, ih bs']
            simp
          · rw [Function.update_of_ne same]
            have offPath := child_below closed below b'
            rw [mem_agree closed₁ (alloc_agree _ _) bs' (offPath.mono agree₁.1),
              mem_agree closed agree₁ bs' offPath]
            simp [same]

/-- **Every old version still holds exactly what it held.** -/
theorem insert_mem_old {t : Trie} (closed : t.Closed) (k : List Bool) (p : Option ℕ)
    {q : Option ℕ} (below : t.Below q) (k' : List Bool) :
    (t.insert p k).1.mem q k' = t.mem q k' :=
  mem_agree closed (insert_agree t k p) k' below

end Trie

/-! ## Controls -/

namespace Controls

open Trie

/-- The empty heap. -/
def empty₀ : Trie := ⟨fun _ => none, 0⟩

/-- Version A: `{[true]}`. -/
def versionA : Trie × ℕ := empty₀.insert none [true]

/-- Version B: `A` with `[false]` added. -/
def versionB : Trie × ℕ := versionA.1.insert (some versionA.2) [false]

/-- **Two versions.** B holds both keys; A still holds only `[true]`; B cost two nodes. -/
theorem two_versions :
    versionB.1.mem (some versionB.2) [true] = true ∧
      versionB.1.mem (some versionB.2) [false] = true ∧
      versionB.1.mem (some versionA.2) [true] = true ∧
      versionB.1.mem (some versionA.2) [false] = false ∧
      versionB.1.next = versionA.1.next + 2 := by
  decide

/-- **Structural sharing**: both versions reach the node of `[true]` through one cell. -/
theorem shared_node :
    (versionB.1.node (some versionB.2)).child true = (versionB.1.node (some versionA.2)).child true ∧
      (versionB.1.node (some versionB.2)).child true ≠ none := by
  decide

/-- What an in-place update would leave: the new root's node written over the old root. -/
def overwritten : Trie :=
  ⟨Function.update versionB.1.cell versionA.2 (versionB.1.cell versionB.2), versionB.1.next⟩

/-- **Negative control**: overwriting the old root makes version A hold `[false]`. -/
theorem overwrite_breaks_old : overwritten.mem (some versionA.2) [false] = true := by decide

end Controls

end Mettapedia.SetTheory.ValuesAndLocations.Persistent
