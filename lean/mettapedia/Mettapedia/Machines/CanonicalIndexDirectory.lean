import Mathlib.Tactic

/-!
# Complete keys and balanced search for relation indexes

The directory key keeps head, arity, index kind and every path coordinate.
Its encoding is injective; a fixed-width tag is not its equality criterion.
A balanced search tree reads at most its height of such complete keys. Its
height grows logarithmically in its node count, independently of key collisions.

Native rotations, deletion, key-width conversion and storage ownership still
need correspondence controls. A key comparison may inspect its whole path;
the height bound does not make variable-width comparisons constant-time.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CanonicalIndexDirectory

structure Key where
  head : ℕ
  arity : ℕ
  kind : ℕ
  path : List ℕ
  deriving DecidableEq

def Key.code (key : Key) : List ℕ :=
  key.head :: key.arity :: key.kind :: key.path.length :: key.path

theorem Key.code_injective : Function.Injective Key.code := by
  intro a b same
  cases a with | mk ah aa ak ap =>
    cases b with | mk bh ba bk bp =>
      simp only [Key.code, List.cons.injEq] at same
      obtain ⟨rfl, rfl, rfl, _, rfl⟩ := same
      rfl

inductive Tree (K V : Type) where
  | empty
  | node (left : Tree K V) (key : K) (value : V) (right : Tree K V)

variable {K V : Type}

def Tree.height : Tree K V → ℕ
  | .empty => 0
  | .node left _ _ right => max left.height right.height + 1

def Tree.size : Tree K V → ℕ
  | .empty => 0
  | .node left _ _ right => left.size + right.size + 1

def Tree.balanced : Tree K V → Prop
  | .empty => True
  | .node left _ _ right => left.balanced ∧ right.balanced ∧
      left.height ≤ right.height + 1 ∧ right.height ≤ left.height + 1

def Tree.contains (tree : Tree K V) (key : K) (value : V) : Prop :=
  match tree with
  | .empty => False
  | .node left k v right => (key = k ∧ value = v) ∨
      left.contains key value ∨ right.contains key value

variable [LinearOrder K]

def Tree.ordered : Tree K V → Prop
  | .empty => True
  | .node left key _ right => left.ordered ∧ right.ordered ∧
      (∀ k v, left.contains k v → k < key) ∧
      (∀ k v, right.contains k v → key < k)

def Tree.lookup : Tree K V → K → Option V
  | .empty, _ => none
  | .node left key value right, wanted =>
      if wanted = key then some value
      else if wanted < key then left.lookup wanted else right.lookup wanted

def Tree.probes : Tree K V → K → ℕ
  | .empty, _ => 0
  | .node left key _ right, wanted =>
      if wanted = key then 1
      else if wanted < key then left.probes wanted + 1
      else right.probes wanted + 1

theorem Tree.lookup_correct (tree : Tree K V) (ordered : tree.ordered)
    (key : K) (value : V) : tree.lookup key = some value ↔ tree.contains key value := by
  induction tree with
  | empty => simp [lookup, contains]
  | node left k v right ihl ihr =>
    obtain ⟨ol, or_, below, above⟩ := ordered
    by_cases equal : key = k
    · subst key
      have notLeft : ¬left.contains k value := fun h => lt_irrefl k (below k value h)
      have notRight : ¬right.contains k value := fun h => lt_irrefl k (above k value h)
      simp [lookup, contains, notLeft, notRight, eq_comm]
    · by_cases less : key < k
      · rw [lookup, if_neg equal, if_pos less, ihl ol]
        constructor
        · intro h; exact Or.inr (Or.inl h)
        · rintro (⟨h, _⟩ | hl | hr)
          · exact False.elim (equal h)
          · exact hl
          · exact False.elim (lt_asymm less (above key value hr))
      · have greater : k < key := lt_of_le_of_ne (le_of_not_gt less) (Ne.symm equal)
        rw [lookup, if_neg equal, if_neg less, ihr or_]
        constructor
        · intro h; exact Or.inr (Or.inr h)
        · rintro (⟨h, _⟩ | hl | hr)
          · exact False.elim (equal h)
          · exact False.elim (lt_asymm greater (below key value hl))
          · exact hr

theorem Tree.probes_le_height (tree : Tree K V) (key : K) :
    tree.probes key ≤ tree.height := by
  induction tree with
  | empty => rfl
  | node left k v right ihl ihr =>
    simp only [probes, height]
    split_ifs
    · omega
    · exact Nat.add_le_add_right (ihl.trans (Nat.le_max_left ..)) 1
    · exact Nat.add_le_add_right (ihr.trans (Nat.le_max_right ..)) 1

omit [LinearOrder K] in
theorem Tree.height_bound (tree : Tree K V) (balanced : tree.balanced) :
    2 ^ (tree.height / 2) ≤ tree.size + 1 := by
  induction tree with
  | empty => simp [height, size]
  | node left key value right ihl ihr =>
    obtain ⟨bl, br, nearL, nearR⟩ := balanced
    have lowL := Nat.min_le_left left.height right.height
    have lowR := Nat.min_le_right left.height right.height
    have half : (max left.height right.height + 1) / 2 ≤
        min left.height right.height / 2 + 1 := by omega
    have pl : 2 ^ (min left.height right.height / 2) ≤ left.size + 1 :=
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (Nat.div_le_div_right lowL)).trans (ihl bl)
    have pr : 2 ^ (min left.height right.height / 2) ≤ right.size + 1 :=
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
        (Nat.div_le_div_right lowR)).trans (ihr br)
    simp only [height, size]
    calc 2 ^ ((max left.height right.height + 1) / 2)
        ≤ 2 ^ (min left.height right.height / 2 + 1) :=
          Nat.pow_le_pow_right (by decide) half
      _ = 2 * 2 ^ (min left.height right.height / 2) := by rw [pow_succ]; omega
      _ ≤ left.size + right.size + 1 + 1 := by omega

example : (Tree.node (.node .empty (1 : ℕ) 7 .empty) 2 8 .empty).lookup 1 = some 7 := by
  decide

example : (Tree.node (.node .empty (1 : ℕ) 7 .empty) 2 8 .empty).lookup 3 = none := by
  decide

end Mettapedia.Machines.CanonicalIndexDirectory
