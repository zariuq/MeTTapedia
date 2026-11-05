import Mettapedia.GSLT.LanguageDef.Collections.Layouts
import Mathlib.Tactic.Ring

/-!
# A persistent list layout: small arrays, a skew-binary forest of blocks, deltas

The layout has three constants (`Params`): small lists of at most `small`
elements are one flat array; longer lists are a front array of fewer than
`block` elements followed by a skew-binary forest of full blocks of `block`
elements; and at most `deltas` one-element prepends are held as deltas before
they are folded into the front (`Body`).

A tree of rank `r` is a full block before two trees of rank `r - 1`, read in
that order; at rank `0` it is one block. Its rank is its type index, so every
tree is complete by construction and holds `block * treeBlocks r` elements,
`treeBlocks r = 2 ^ (r + 1) - 1` (`Tree.length_toList`, `treeBlocks_add_one`).

* **The abstraction.** A value means its elements with its terminal. Prepend,
  head, tail, indexing and known length are specified through it for every
  value, whatever its shape (`skew`), so every observation of the abstraction
  factors through it and agrees with every other layout of the same list
  (`Layouts.Layout.agree`). Folding deltas and pushing blocks into the forest
  keep the elements (`Body.elements_fold`, `elements_settle`).
* **The shape invariants** (`Valid`): small arrays hold at most `small`
  elements; a front holds fewer than `block`; the ranks of a forest increase
  strictly except that the first two may be equal (`SkewRanks`); a chain of
  deltas has at most `deltas` links and ends in a long list. Prepend and tail
  preserve them (`valid_cons`, `valid_tail`). A value is immutable, so a
  prepend made by any holder of a shared value, any number of times, keeps
  them as well.

The costs of these operations are a separate model (`SkewLayoutCost`); nothing
here concerns memory, ownership or lifetimes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.SkewLayout

open Layouts (Terminal Abstract Layout)

universe u v

/-- The three constants of the layout. -/
structure Params where
  /-- Lists of at most this many elements are one flat array. -/
  small : ℕ
  /-- The number of elements in a block. -/
  block : ℕ
  block_pos : 0 < block
  /-- The most one-element prepends held as deltas before they are folded. -/
  deltas : ℕ

/-- The number of blocks in a complete tree of rank `r`. -/
def treeBlocks : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 * treeBlocks r + 1

theorem treeBlocks_add_one : ∀ r, treeBlocks r + 1 = 2 ^ (r + 1)
  | 0 => rfl
  | r + 1 => by
      rw [treeBlocks, pow_succ, ← treeBlocks_add_one r]
      omega

theorem one_le_treeBlocks (r : ℕ) : 1 ≤ treeBlocks r := by
  cases r <;> simp [treeBlocks]

/-- A full block of exactly `n` elements. -/
abbrev Block (A : Type u) (n : ℕ) := {xs : List A // xs.length = n}

/-- A complete tree of rank `r`: one block at rank `0`; at rank `r + 1`, a
block before two trees of rank `r`. -/
inductive Tree (A : Type u) (n : ℕ) : ℕ → Type u
  | leaf (block : Block A n) : Tree A n 0
  | node {r : ℕ} (block : Block A n) (left right : Tree A n r) : Tree A n (r + 1)

namespace Tree

variable {A : Type u} {n : ℕ}

/-- The elements of a tree: its block, then its left tree, then its right. -/
def toList : {r : ℕ} → Tree A n r → List A
  | _, .leaf b => b.val
  | _, .node b left right => b.val ++ (left.toList ++ right.toList)

theorem length_toList : ∀ {r : ℕ} (t : Tree A n r), t.toList.length = n * treeBlocks r
  | _, .leaf b => by simp [toList, b.property, treeBlocks]
  | _, .node b left right => by
      simp only [toList, List.length_append, b.property, length_toList left, length_toList right,
        treeBlocks]
      ring

/-- The block at the root. -/
def root : {r : ℕ} → Tree A n r → Block A n
  | _, .leaf b => b
  | _, .node b _ _ => b

theorem toList_eq_root_append : ∀ {r : ℕ} (t : Tree A n r), ∃ rest, t.toList = t.root.val ++ rest
  | _, .leaf b => ⟨[], by simp [toList, root]⟩
  | _, .node b left right => ⟨left.toList ++ right.toList, rfl⟩

/-- The element at an index: in the root block, else in the left tree, else
in the right tree, whose sizes the ranks give. -/
def get? : {r : ℕ} → Tree A n r → ℕ → Option A
  | _, .leaf b, i => b.val[i]?
  | _, .node (r := r) b left right, i =>
      if i < n then b.val[i]?
      else if i - n < n * treeBlocks r then left.get? (i - n)
      else right.get? (i - n - n * treeBlocks r)

theorem get?_eq : ∀ {r : ℕ} (t : Tree A n r) (i : ℕ), t.get? i = t.toList[i]?
  | _, .leaf b, i => rfl
  | _, .node (r := r) b left right, i => by
      simp only [get?, toList]
      by_cases inRoot : i < n
      · rw [if_pos inRoot, List.getElem?_append_left (by rw [b.property]; exact inRoot)]
      · rw [if_neg inRoot, List.getElem?_append_right (by rw [b.property]; omega), b.property]
        by_cases inLeft : i - n < n * treeBlocks r
        · rw [if_pos inLeft, get?_eq left,
            List.getElem?_append_left (by rw [length_toList]; exact inLeft)]
        · rw [if_neg inLeft, get?_eq right,
            List.getElem?_append_right (by rw [length_toList]; omega), length_toList]

/-- Reading a tree through an equation of ranks changes nothing. -/
theorem toList_cast {r s : ℕ} (same : r = s) (t : Tree A n r) : (same ▸ t).toList = t.toList := by
  subst same
  rfl

end Tree

/-- A forest: trees with their ranks, read in order. -/
abbrev Forest (A : Type u) (n : ℕ) := List (Σ r, Tree A n r)

namespace Forest

variable {A : Type u} {n : ℕ}

def toList : Forest A n → List A
  | [] => []
  | d :: ds => d.2.toList ++ toList ds

def ranks (ds : Forest A n) : List ℕ := ds.map Sigma.fst

/-- The number of blocks in a forest. -/
def blocks (ds : Forest A n) : ℕ := (ds.ranks.map treeBlocks).sum

theorem length_toList : ∀ ds : Forest A n, (toList ds).length = n * blocks ds
  | [] => by simp [toList, blocks, ranks]
  | d :: ds => by
      simp only [toList, List.length_append, Tree.length_toList, length_toList ds, blocks, ranks,
        List.map_cons, List.sum_cons]
      ring

/-- The element at an index: in the first tree that reaches it. -/
def get? : Forest A n → ℕ → Option A
  | [], _ => none
  | ⟨r, t⟩ :: ds, i => if i < n * treeBlocks r then t.get? i else get? ds (i - n * treeBlocks r)

theorem get?_eq : ∀ (ds : Forest A n) (i : ℕ), get? ds i = (toList ds)[i]?
  | [], _ => rfl
  | ⟨r, t⟩ :: ds, i => by
      simp only [get?, toList]
      by_cases inTree : i < n * treeBlocks r
      · rw [if_pos inTree, Tree.get?_eq, List.getElem?_append_left (by rw [Tree.length_toList]; exact inTree)]
      · rw [if_neg inTree, get?_eq ds, List.getElem?_append_right (by rw [Tree.length_toList]; omega),
          Tree.length_toList]

/-- **Skew-binary insertion of a full block**: when the first two trees have
equal rank they become the children of the block; otherwise the block is a
new tree of rank `0`. One link at most. -/
def link (b : Block A n) : Forest A n → Forest A n
  | [] => [⟨0, .leaf b⟩]
  | [d] => [⟨0, .leaf b⟩, d]
  | ⟨r₁, t₁⟩ :: ⟨r₂, t₂⟩ :: rest =>
      if same : r₁ = r₂ then ⟨r₂ + 1, .node b (same ▸ t₁) t₂⟩ :: rest
      else ⟨0, .leaf b⟩ :: ⟨r₁, t₁⟩ :: ⟨r₂, t₂⟩ :: rest

theorem toList_link (b : Block A n) : ∀ ds : Forest A n, toList (link b ds) = b.val ++ toList ds
  | [] => by simp [link, toList, Tree.toList]
  | [d] => by simp [link, toList, Tree.toList]
  | ⟨r₁, t₁⟩ :: ⟨r₂, t₂⟩ :: rest => by
      simp only [link]
      split
      · next same => simp [toList, Tree.toList, Tree.toList_cast]
      · simp [toList, Tree.toList]

end Forest

/-! ## Skew ranks -/

/-- The ranks of a skew-binary forest: strictly increasing, except that the
first two may be equal. -/
def SkewRanks : List ℕ → Prop
  | r₁ :: r₂ :: rest => r₁ ≤ r₂ ∧ (r₂ :: rest).Pairwise (· < ·)
  | _ => True

instance : DecidablePred SkewRanks := fun ranks =>
  match ranks with
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | _ :: _ :: _ => inferInstanceAs (Decidable (_ ∧ _))

theorem skewRanks_tail {r : ℕ} {rest : List ℕ} (skew : SkewRanks (r :: rest)) : SkewRanks rest := by
  match rest, skew with
  | [], _ => trivial
  | [_], _ => trivial
  | r₂ :: r₃ :: rest, ⟨_, increasing⟩ =>
      obtain ⟨below, later⟩ := List.pairwise_cons.mp increasing
      exact ⟨Nat.le_of_lt (below r₃ List.mem_cons_self), later⟩

/-- Every rank after the first two is above the first. -/
theorem skewRanks_lt {r : ℕ} {rest : List ℕ} (skew : SkewRanks (r :: rest)) :
    ∀ s ∈ rest.drop 1, r < s := by
  match rest, skew with
  | [], _ => simp
  | [_], _ => simp
  | r₂ :: r₃ :: rest, ⟨first, increasing⟩ =>
      intro s member
      have above := (List.pairwise_cons.mp increasing).1 s member
      omega

theorem skewRanks_link {A : Type u} {n : ℕ} (b : Block A n) :
    ∀ ds : Forest A n, SkewRanks ds.ranks → SkewRanks (Forest.link b ds).ranks
  | [], _ => trivial
  | [⟨r, t⟩], _ => ⟨Nat.zero_le r, List.pairwise_singleton _ _⟩
  | ⟨r₁, t₁⟩ :: ⟨r₂, t₂⟩ :: rest, skew => by
      obtain ⟨first, increasing⟩ := skew
      simp only [Forest.link]
      split
      · next same =>
          subst same
          simp only [Forest.ranks, List.map_cons]
          match rest, increasing with
          | [], _ => trivial
          | ⟨r₃, t₃⟩ :: rest, increasing =>
              obtain ⟨below, later⟩ := List.pairwise_cons.mp increasing
              exact ⟨below r₃ List.mem_cons_self, later⟩
      · next different =>
          refine ⟨Nat.zero_le r₁, List.pairwise_cons.mpr ⟨?_, increasing⟩⟩
          intro s member
          have strict : r₁ < r₂ := Nat.lt_of_le_of_ne first different
          rcases List.mem_cons.mp member with rfl | later
          · exact strict
          · exact strict.trans ((List.pairwise_cons.mp increasing).1 s later)

/-! ## Values -/

/-- The shape of a list's elements: a small flat array, a front array before
a forest of full blocks, or a one-element delta before the rest. -/
inductive Body (A : Type u) (n : ℕ) where
  | small (elements : List A)
  | packed (front : List A) (forest : Forest A n)
  | delta (head : A) (rest : Body A n)

namespace Body

variable {A : Type u} {n : ℕ}

/-- The elements, in order. -/
def elements : Body A n → List A
  | .small xs => xs
  | .packed front forest => front ++ forest.toList
  | .delta x rest => x :: rest.elements

/-- The number of deltas before the base. -/
def depth : Body A n → ℕ
  | .delta _ rest => rest.depth + 1
  | _ => 0

/-- A long list: a front with a forest, or deltas before one. -/
def IsLong : Body A n → Prop
  | .small _ => False
  | _ => True

/-- The element at an index. -/
def nth : Body A n → ℕ → Option A
  | .small xs, i => xs[i]?
  | .packed front forest, i => if i < front.length then front[i]? else forest.get? (i - front.length)
  | .delta x _, 0 => some x
  | .delta _ rest, i + 1 => rest.nth i

def knownLength : Body A n → ℕ
  | .small xs => xs.length
  | .packed front forest => front.length + n * forest.blocks
  | .delta _ rest => rest.knownLength + 1

def head : Body A n → Option A
  | .small xs => xs.head?
  | .packed (x :: _) _ => some x
  | .packed [] [] => none
  | .packed [] (d :: _) => d.2.root.val.head?
  | .delta x _ => some x

/-- The tail: a suffix of a flat array, or the root block's suffix with the
root's children put in front of the forest. -/
def tail : Body A n → Option (Body A n)
  | .small [] => none
  | .small (_ :: xs) => some (.small xs)
  | .packed (_ :: front) forest => some (.packed front forest)
  | .packed [] [] => none
  | .packed [] (⟨_, .leaf b⟩ :: forest) => some (.packed b.val.tail forest)
  | .packed [] (⟨_, .node (r := r) b left right⟩ :: forest) =>
      some (.packed b.val.tail (⟨r, left⟩ :: ⟨r, right⟩ :: forest))
  | .delta _ rest => some rest

theorem nth_eq : ∀ (body : Body A n) (i : ℕ), body.nth i = body.elements[i]?
  | .small _, _ => rfl
  | .packed front forest, i => by
      simp only [nth, elements]
      by_cases inFront : i < front.length
      · rw [if_pos inFront, List.getElem?_append_left inFront]
      · rw [if_neg inFront, Forest.get?_eq, List.getElem?_append_right (by omega)]
  | .delta _ _, 0 => rfl
  | .delta _ rest, i + 1 => by rw [nth, nth_eq rest i]; rfl

theorem knownLength_eq : ∀ body : Body A n, body.knownLength = body.elements.length
  | .small _ => rfl
  | .packed front forest => by simp [knownLength, elements, Forest.length_toList]
  | .delta _ rest => by simp [knownLength, elements, knownLength_eq rest]

theorem head_eq (positive : 0 < n) : ∀ body : Body A n, body.head = body.elements.head?
  | .small _ => rfl
  | .packed (_ :: _) _ => rfl
  | .packed [] [] => rfl
  | .packed [] (⟨r, t⟩ :: forest) => by
      obtain ⟨rest, same⟩ := t.toList_eq_root_append
      have nonempty : t.root.val ≠ [] := by
        intro empty
        have := t.root.property
        rw [empty] at this
        simp at this
        omega
      obtain ⟨y, ys, split⟩ := List.exists_cons_of_ne_nil nonempty
      simp only [head, elements, Forest.toList, List.nil_append, same, split, List.cons_append,
        List.head?_cons]
  | .delta _ _ => rfl

theorem tail_eq (positive : 0 < n) : ∀ body : Body A n,
    (body.tail).map elements = body.elements.tail?
  | .small [] => rfl
  | .small (_ :: _) => rfl
  | .packed (_ :: _) _ => rfl
  | .packed [] [] => rfl
  | .packed [] (⟨_, .leaf b⟩ :: forest) => by
      have nonempty : b.val ≠ [] := by
        intro empty
        have := b.property
        rw [empty] at this
        simp at this
        omega
      obtain ⟨y, ys, split⟩ := List.exists_cons_of_ne_nil nonempty
      simp [tail, elements, Forest.toList, Tree.toList, split]
  | .packed [] (⟨_, .node b left right⟩ :: forest) => by
      have nonempty : b.val ≠ [] := by
        intro empty
        have := b.property
        rw [empty] at this
        simp at this
        omega
      obtain ⟨y, ys, split⟩ := List.exists_cons_of_ne_nil nonempty
      simp [tail, elements, Forest.toList, Tree.toList, split]
  | .delta _ _ => rfl

end Body

/-! ## Prepend -/

section Prepend

variable {A : Type u} (P : Params)

/-- The block of the last `block` elements of an array that has them. -/
def lastBlock (front : List A) (enough : P.block ≤ front.length) : Block A P.block :=
  ⟨front.drop (front.length - P.block), by simp [List.length_drop]; omega⟩

/-- Push full blocks from the end of a front onto the forest, at most `fuel`
of them, until fewer than `block` elements remain. -/
def settleWith : ℕ → List A → Forest A P.block → List A × Forest A P.block
  | 0, front, forest => (front, forest)
  | fuel + 1, front, forest =>
      if enough : P.block ≤ front.length then
        settleWith fuel (front.take (front.length - P.block)) (Forest.link (lastBlock P front enough) forest)
      else (front, forest)

/-- Settle a front: every full block at its end goes into the forest. -/
def settle (front : List A) (forest : Forest A P.block) : List A × Forest A P.block :=
  settleWith P front.length front forest

theorem elements_settleWith : ∀ (fuel : ℕ) (front : List A) (forest : Forest A P.block),
    (settleWith P fuel front forest).1 ++ (settleWith P fuel front forest).2.toList =
      front ++ forest.toList
  | 0, _, _ => rfl
  | fuel + 1, front, forest => by
      simp only [settleWith]
      split
      · next enough =>
          rw [elements_settleWith fuel, Forest.toList_link, lastBlock, ← List.append_assoc,
            List.take_append_drop]
      · rfl

theorem elements_settle (front : List A) (forest : Forest A P.block) :
    (settle P front forest).1 ++ (settle P front forest).2.toList = front ++ forest.toList :=
  elements_settleWith P _ front forest

theorem front_settleWith : ∀ (fuel : ℕ) (front : List A) (forest : Forest A P.block),
    front.length ≤ fuel → (settleWith P fuel front forest).1.length < P.block
  | 0, front, forest, bounded => by
      have : front.length = 0 := by omega
      simpa [settleWith, this] using P.block_pos
  | fuel + 1, front, forest, bounded => by
      simp only [settleWith]
      split
      · next enough =>
          apply front_settleWith fuel
          simp only [List.length_take]
          have := P.block_pos
          omega
      · next short => exact Nat.lt_of_not_le short

theorem front_settle (front : List A) (forest : Forest A P.block) :
    (settle P front forest).1.length < P.block :=
  front_settleWith P _ front forest (Nat.le_refl _)

theorem skewRanks_settleWith : ∀ (fuel : ℕ) (front : List A) (forest : Forest A P.block),
    SkewRanks forest.ranks → SkewRanks (settleWith P fuel front forest).2.ranks
  | 0, _, _, skew => skew
  | fuel + 1, front, forest, skew => by
      simp only [settleWith]
      split
      · exact skewRanks_settleWith fuel _ _ (skewRanks_link _ forest skew)
      · exact skew

theorem skewRanks_settle (front : List A) (forest : Forest A P.block) (skew : SkewRanks forest.ranks) :
    SkewRanks (settle P front forest).2.ranks :=
  skewRanks_settleWith P _ front forest skew

/-- Fold elements before a body into its front: the deltas are read off one by
one, and the front with them is settled. -/
def fold : List A → Body A P.block → Body A P.block
  | ys, .small xs => .packed (settle P (ys ++ xs) []).1 (settle P (ys ++ xs) []).2
  | ys, .packed front forest => .packed (settle P (ys ++ front) forest).1 (settle P (ys ++ front) forest).2
  | ys, .delta x rest => fold (ys ++ [x]) rest

/-- **Prepend.** A small array within its bound takes the element; otherwise
a long list takes a delta while it has fewer than `deltas`, and else its
deltas and the element are folded into its front. -/
def cons (x : A) : Body A P.block → Body A P.block
  | .small xs => if xs.length < P.small then .small (x :: xs) else fold P [x] (.small xs)
  | .packed front forest =>
      if (Body.packed front forest : Body A P.block).depth < P.deltas then .delta x (.packed front forest)
      else fold P [x] (.packed front forest)
  | .delta y rest =>
      if (Body.delta y rest).depth < P.deltas then .delta x (.delta y rest)
      else fold P [x] (.delta y rest)

theorem Body.elements_fold : ∀ (ys : List A) (body : Body A P.block),
    (fold P ys body).elements = ys ++ body.elements
  | ys, .small xs => by
      simp only [fold, Body.elements]
      rw [elements_settle]
      simp [Forest.toList]
  | ys, .packed front forest => by
      simp only [fold, Body.elements]
      rw [elements_settle, List.append_assoc]
  | ys, .delta x rest => by
      rw [fold, Body.elements_fold (ys ++ [x]) rest]
      simp [Body.elements]

theorem Body.elements_cons (x : A) (body : Body A P.block) :
    (cons P x body).elements = x :: body.elements := by
  cases body with
  | small xs =>
      simp only [cons]
      split
      · rfl
      · rw [Body.elements_fold]; rfl
  | packed front forest =>
      simp only [cons]
      split
      · rfl
      · rw [Body.elements_fold]; rfl
  | delta y rest =>
      simp only [cons]
      split
      · rfl
      · rw [Body.elements_fold]; rfl

end Prepend

/-! ## The layout -/

/-- **The skew layout** with constants `P`: a value is a body with a terminal. -/
def skew {A : Type u} {V : Type v} (P : Params) : Layout.{u, v, max u v} A V where
  Carrier := Body A P.block × Terminal A V
  abs value := (value.1.elements, value.2)
  cons x value := (cons P x value.1, value.2)
  head value := value.1.head
  tail value := value.1.tail.map fun body => (body, value.2)
  nth value i := value.1.nth i
  knownLength value := value.1.knownLength
  abs_cons x value := by simp [Body.elements_cons]
  head_spec value := Body.head_eq P.block_pos value.1
  tail_spec value := by
    obtain ⟨body, terminal⟩ := value
    change (body.tail.map fun rest => (rest, terminal)).map (fun value => (value.1.elements, value.2)) =
      body.elements.tail?.map fun rest => (rest, terminal)
    rw [← Body.tail_eq P.block_pos body, Option.map_map, Option.map_map]
    rfl
  nth_spec value i := Body.nth_eq value.1 i
  knownLength_spec value := Body.knownLength_eq value.1

/-! ## The shape invariants -/

/-- **The shape invariants.** -/
def Valid {A : Type u} (P : Params) : Body A P.block → Prop
  | .small xs => xs.length ≤ P.small
  | .packed front forest => front.length < P.block ∧ SkewRanks forest.ranks
  | .delta _ rest => rest.depth < P.deltas ∧ rest.IsLong ∧ Valid P rest

section Invariants

variable {A : Type u} (P : Params)

theorem valid_fold : ∀ (ys : List A) (body : Body A P.block), body.IsLong → Valid P body →
    Valid P (fold P ys body)
  | _, .small _, long, _ => long.elim
  | ys, .packed front forest, _, ⟨_, skew⟩ => ⟨front_settle P _ _, skewRanks_settle P _ _ skew⟩
  | ys, .delta x rest, _, ⟨_, long, valid⟩ => by
      rw [fold]
      exact valid_fold (ys ++ [x]) rest long valid

theorem valid_fold_small (ys xs : List A) : Valid P (fold P ys (.small xs)) :=
  ⟨front_settle P _ _, skewRanks_settle P _ _ trivial⟩

/-- **Prepend preserves the invariants**, whoever holds the value. -/
theorem valid_cons (x : A) (body : Body A P.block) (valid : Valid P body) : Valid P (cons P x body) := by
  cases body with
  | small xs =>
      simp only [cons]
      split
      · next room => exact Nat.succ_le_of_lt room
      · exact valid_fold_small P _ _
  | packed front forest =>
      simp only [cons]
      split
      · next room => exact ⟨room, trivial, valid⟩
      · exact valid_fold P _ _ trivial valid
  | delta y rest =>
      simp only [cons]
      split
      · next room => exact ⟨room, trivial, valid⟩
      · exact valid_fold P _ _ trivial valid

/-- **Tail preserves the invariants.** -/
theorem valid_tail : ∀ {body rest : Body A P.block}, Valid P body → body.tail = some rest → Valid P rest
  | .small (_ :: xs), _, valid, taken => by
      cases taken
      exact Nat.le_of_succ_le valid
  | .packed (_ :: front) forest, _, ⟨short, skew⟩, taken => by
      cases taken
      exact ⟨Nat.lt_of_succ_lt short, skew⟩
  | .packed [] (⟨_, .leaf b⟩ :: forest), _, ⟨_, skew⟩, taken => by
      cases taken
      refine ⟨?_, skewRanks_tail skew⟩
      have := P.block_pos
      simp only [List.length_tail, b.property]
      omega
  | .packed [] (⟨_, .node (r := r) b left right⟩ :: forest), _, ⟨_, skew⟩, taken => by
      cases taken
      have := P.block_pos
      refine ⟨by simp only [List.length_tail, b.property]; omega, ?_⟩
      simp only [Forest.ranks, List.map_cons]
      refine ⟨Nat.le_refl r, List.pairwise_cons.mpr ⟨?_, ?_⟩⟩
      · intro s member
        have above : r + 1 ≤ s := by
          match forest, skew with
          | ⟨r₂, _⟩ :: forest, ⟨first, increasing⟩ =>
              simp only [List.map_cons, List.mem_cons] at member first increasing
              rcases member with rfl | later
              · exact first
              · exact first.trans (Nat.le_of_lt ((List.pairwise_cons.mp increasing).1 s later))
        omega
      · match forest, skew with
        | [], _ => exact List.Pairwise.nil
        | ⟨r₂, _⟩ :: forest, ⟨_, increasing⟩ => exact increasing
  | .delta _ rest, _, ⟨_, _, valid⟩, taken => by
      cases taken
      exact valid

/-- The empty list is valid. -/
theorem valid_empty : Valid P (.small [] : Body A P.block) := Nat.zero_le _

end Invariants

end Mettapedia.GSLT.LanguageDef.Collections.SkewLayout
