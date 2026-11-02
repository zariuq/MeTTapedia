import Mathlib.Tactic

/-!
# Views of hash-consed terms: one node per path, or one per distinct subterm

A hash-consed store gives each distinct term one id, and stores an expression's
children before the expression, so a child's id is smaller than its parent's.  A
term that shares a subterm, such as `(pair x x)`, stores that subterm once.

A *view* reads a stored term back as a tree of nodes without decoding it for
keeps.  Built by plain recursion over the children, a view makes one node per
*path* through the term: its cost is the term's tree size, which is exponential
in the depth when subterms are shared.  `(pair x x)` nested `n` times has
`2 ^ n - 1` expression paths but only `n` distinct expressions.

A build that remembers, by id, the nodes it has already made costs one node per
distinct expression it reaches, never more than the number of ids up to the
root, and it reads back the same tree.

This file proves:
* `pathViews_doubling`: the plain build makes `2 ^ n - 1` nodes on the doubling
  family;
* `remember_spec`: from a coherent, closed cache, the remembering build returns
  the term's tree, leaves a coherent, closed cache holding the term's
  expressions, and makes one node for each of them it had not made before;
* `remember_empty`: from an empty cache it returns the tree and costs
  `(reach s i).card`, which `reach_card_le` bounds by `i + 1`;
* `doubling_views`: on the doubling family the plain build makes `2 ^ n - 1`
  nodes and the remembering build `n`, reading the same tree.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.SharedViewCost

/-- A stored node: a leaf (a symbol, a number or a variable, named by a code), or
an expression over the ids of its children. -/
inductive Node where
  | leaf : Nat → Node
  | expr : List Nat → Node

/-- A hash-consed store: every child of an expression carries a smaller id. -/
structure Store where
  node : Nat → Node
  children_lt : ∀ i cs, node i = .expr cs → ∀ c ∈ cs, c < i

/-- A term read back as a tree. -/
inductive Tree where
  | leaf : Nat → Tree
  | expr : List Tree → Tree

/-- The tree an id denotes. -/
def tree (s : Store) (i : Nat) : Tree :=
  match _h : s.node i with
  | .leaf a => .leaf a
  | .expr cs => .expr (cs.attach.map fun c => tree s c.1)
termination_by i
decreasing_by exact s.children_lt i cs _h c.1 c.2

/-- The nodes a plain view build makes for `i`: one expression node for each
path through the term. -/
def pathViews (s : Store) (i : Nat) : Nat :=
  match h : s.node i with
  | .leaf _ => 0
  | .expr cs => (cs.attach.map fun c => pathViews s c.1).sum + 1
termination_by i
decreasing_by exact s.children_lt i cs h c.1 c.2

/-- The union of a family of finite sets over a list. -/
def unionOf {α : Type} (l : List α) (f : α → Finset Nat) : Finset Nat :=
  (l.map f).foldr (· ∪ ·) ∅

theorem mem_unionOf {α : Type} (l : List α) (f : α → Finset Nat) (j : Nat) :
    j ∈ unionOf l f ↔ ∃ a ∈ l, j ∈ f a := by
  induction l with
  | nil => simp [unionOf]
  | cons a l ih =>
    simp only [unionOf, List.map_cons, List.foldr_cons, Finset.mem_union] at ih ⊢
    rw [ih]
    simp

theorem unionOf_cons {α : Type} (a : α) (l : List α) (f : α → Finset Nat) :
    unionOf (a :: l) f = f a ∪ unionOf l f := rfl

/-- The expressions reachable from `i`, `i` included when it is one. -/
def reach (s : Store) (i : Nat) : Finset Nat :=
  match _h : s.node i with
  | .leaf _ => ∅
  | .expr cs => insert i (unionOf cs.attach fun c => reach s c.1)
termination_by i
decreasing_by exact s.children_lt i cs _h c.1 c.2

/-! ## Unfolding by the shape of the node -/

theorem tree_leaf (s : Store) (i a : Nat) (h : s.node i = .leaf a) :
    tree s i = .leaf a := by
  rw [tree]; split
  · rename_i a' h'; rw [h] at h'; cases h'; rfl
  · rename_i cs h'; rw [h] at h'; cases h'

theorem tree_expr (s : Store) (i : Nat) (cs : List Nat) (h : s.node i = .expr cs) :
    tree s i = .expr (cs.attach.map fun c => tree s c.1) := by
  rw [tree]; split
  · rename_i a h'; rw [h] at h'; cases h'
  · rename_i cs' h'; rw [h] at h'; cases h'; rfl

theorem pathViews_expr (s : Store) (i : Nat) (cs : List Nat) (h : s.node i = .expr cs) :
    pathViews s i = (cs.map fun c => pathViews s c).sum + 1 := by
  rw [pathViews]; split
  · rename_i a h'; rw [h] at h'; cases h'
  · rename_i cs' h'; rw [h] at h'; cases h'
    rw [List.attach_map_val (f := fun c => pathViews s c)]

theorem reach_leaf (s : Store) (i a : Nat) (h : s.node i = .leaf a) : reach s i = ∅ := by
  rw [reach]; split
  · rfl
  · rename_i cs h'; rw [h] at h'; cases h'

theorem reach_expr (s : Store) (i : Nat) (cs : List Nat) (h : s.node i = .expr cs) :
    reach s i = insert i (unionOf cs.attach fun c => reach s c.1) := by
  rw [reach]; split
  · rename_i a h'; rw [h] at h'; cases h'
  · rename_i cs' h'; rw [h] at h'; cases h'; rfl

/-! ## What a term reaches -/

/-- Every expression a term reaches has an id at most the term's. -/
theorem reach_le (s : Store) : ∀ i, ∀ j ∈ reach s i, j ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hj
    cases hn : s.node i with
    | leaf a => rw [reach_leaf s i a hn] at hj; simp at hj
    | expr cs =>
      rw [reach_expr s i cs hn, Finset.mem_insert, mem_unionOf] at hj
      rcases hj with rfl | ⟨c, _, hc⟩
      · exact le_refl _
      · have hlt := s.children_lt i cs hn c.1 c.2
        exact le_trans (ih c.1 hlt j hc) hlt.le

/-- What a reached expression reaches is reached. -/
theorem reach_trans (s : Store) : ∀ i, ∀ j ∈ reach s i, reach s j ⊆ reach s i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j hj
    cases hn : s.node i with
    | leaf a => rw [reach_leaf s i a hn] at hj; simp at hj
    | expr cs =>
      have hj' := hj
      rw [reach_expr s i cs hn, Finset.mem_insert, mem_unionOf] at hj'
      rcases hj' with rfl | ⟨c, hcmem, hc⟩
      · exact le_refl _
      · intro k hk
        have hlt := s.children_lt i cs hn c.1 c.2
        have hk' := ih c.1 hlt j hc hk
        rw [reach_expr s i cs hn, Finset.mem_insert, mem_unionOf]
        exact Or.inr ⟨c, hcmem, hk'⟩

theorem reach_card_le (s : Store) (i : Nat) : (reach s i).card ≤ i + 1 := by
  have hsub : reach s i ⊆ Finset.range (i + 1) := by
    intro j hj
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (reach_le s i j hj)
  simpa using Finset.card_le_card hsub

/-! ## The remembering build -/

/-- A view cache: the ids whose nodes exist, and the node made for each. -/
structure Cache where
  keys : Finset Nat
  view : Nat → Tree

/-- A cache is coherent when each remembered node is the tree of its id, and
closed when it holds what each remembered id reaches. -/
def Inv (s : Store) (m : Cache) : Prop :=
  (∀ j ∈ m.keys, m.view j = tree s j) ∧ (∀ j ∈ m.keys, reach s j ⊆ m.keys)

/-- The remembering build: the tree read for `i`, the cache afterwards, and the
nodes made.  A remembered id costs nothing; a new expression costs one node
after its children are built, the cache threaded from child to child. -/
def remember (s : Store) (i : Nat) (m : Cache) : Tree × Cache × Nat :=
  if i ∈ m.keys then (m.view i, m, 0) else
  match h : s.node i with
  | .leaf a => (.leaf a, m, 0)
  | .expr cs =>
    let built := cs.attach.foldl
      (fun (acc : List Tree × Cache × Nat) (c : {c // c ∈ cs}) =>
        let r := remember s c.1 acc.2.1
        (acc.1 ++ [r.1], r.2.1, acc.2.2 + r.2.2)) ([], m, 0)
    (.expr built.1,
      ⟨insert i built.2.1.keys, Function.update built.2.1.view i (.expr built.1)⟩,
      built.2.2 + 1)
termination_by i
decreasing_by exact s.children_lt i cs h c.1 c.2

/-- What the remembering build guarantees for `i` from cache `m`. -/
def Spec (s : Store) (i : Nat) (m : Cache) (r : Tree × Cache × Nat) : Prop :=
  r.1 = tree s i ∧ Inv s r.2.1 ∧ r.2.1.keys = m.keys ∪ reach s i ∧
    r.2.2 = (reach s i \ m.keys).card

theorem remember_hit (s : Store) (i : Nat) (m : Cache) (hi : i ∈ m.keys) :
    remember s i m = (m.view i, m, 0) := by
  rw [remember, if_pos hi]

theorem remember_leaf (s : Store) (i a : Nat) (m : Cache) (hi : i ∉ m.keys)
    (h : s.node i = .leaf a) : remember s i m = (.leaf a, m, 0) := by
  rw [remember, if_neg hi]; split
  · rename_i a' h'; rw [h] at h'; cases h'; rfl
  · rename_i cs h'; rw [h] at h'; cases h'

/-- One child's build adds its reach to the keys; counting the new keys of a
union child by child. -/
theorem card_sdiff_union (X Y K : Finset Nat) :
    ((X ∪ Y) \ K).card = (X \ K).card + (Y \ (K ∪ X)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext j; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  · rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_sdiff, Finset.mem_union] at h1 h2; tauto

/-- Building the children one after another, from any accumulator. -/
theorem fold_children (s : Store) (cs : List Nat)
    (ih : ∀ c ∈ cs, ∀ m, Inv s m → Spec s c m (remember s c m)) :
    ∀ (l : List {c // c ∈ cs}) (ts : List Tree) (m : Cache) (k : Nat), Inv s m →
      let r := l.foldl
        (fun (acc : List Tree × Cache × Nat) (c : {c // c ∈ cs}) =>
          let r := remember s c.1 acc.2.1
          (acc.1 ++ [r.1], r.2.1, acc.2.2 + r.2.2)) (ts, m, k)
      r.1 = ts ++ l.map (fun c => tree s c.1) ∧ Inv s r.2.1 ∧
        r.2.1.keys = m.keys ∪ unionOf l (fun c => reach s c.1) ∧
        r.2.2 = k + (unionOf l (fun c => reach s c.1) \ m.keys).card := by
  intro l
  induction l with
  | nil =>
    intro ts m k hm
    simp [unionOf, hm]
  | cons a l ihl =>
    intro ts m k hm
    obtain ⟨h1, h2, h3, h4⟩ := ih a.1 a.2 m hm
    obtain ⟨g1, g2, g3, g4⟩ := ihl (ts ++ [(remember s a.1 m).1])
      (remember s a.1 m).2.1 (k + (remember s a.1 m).2.2) h2
    simp only [List.foldl_cons]
    refine ⟨?_, g2, ?_, ?_⟩
    · rw [g1, h1]; simp
    · rw [g3, h3, unionOf_cons, Finset.union_assoc]
    · rw [g4, h4, h3, unionOf_cons, card_sdiff_union]; ring

theorem remember_spec (s : Store) : ∀ i m, Inv s m → Spec s i m (remember s i m) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro m hm
    by_cases hi : i ∈ m.keys
    · rw [remember_hit s i m hi]
      have hsub : reach s i ⊆ m.keys := hm.2 i hi
      refine ⟨hm.1 i hi, hm, ?_, ?_⟩
      · exact (Finset.union_eq_left.mpr hsub).symm
      · simp [Finset.sdiff_eq_empty_iff_subset.mpr hsub]
    · cases hn : s.node i with
      | leaf a =>
        rw [remember_leaf s i a m hi hn]
        refine ⟨(tree_leaf s i a hn).symm, hm, ?_, ?_⟩
        · simp [reach_leaf s i a hn]
        · simp [reach_leaf s i a hn]
      | expr cs =>
        have hih : ∀ c ∈ cs, ∀ m, Inv s m → Spec s c m (remember s c m) :=
          fun c hc m hm => ih c (s.children_lt i cs hn c hc) m hm
        obtain ⟨f1, f2, f3, f4⟩ := fold_children s cs hih cs.attach [] m 0 hm
        set U := unionOf cs.attach fun c => reach s c.1 with hU
        have hiU : i ∉ U := by
          intro hmem
          rw [hU, mem_unionOf] at hmem
          obtain ⟨c, _, hc⟩ := hmem
          have := reach_le s c.1 i hc
          have := s.children_lt i cs hn c.1 c.2
          omega
        have hreach : reach s i = insert i U := reach_expr s i cs hn
        rw [remember, if_neg hi]
        split
        · rename_i a h'; rw [hn] at h'; cases h'
        · rename_i cs' h'
          rw [hn] at h'; cases h'
          dsimp only at f1 f2 f3 f4 ⊢
          rw [List.nil_append] at f1
          refine ⟨?_, ⟨?_, ?_⟩, ?_, ?_⟩
          · rw [f1, tree_expr s i cs hn]
          · intro j hj
            dsimp only at hj ⊢
            rw [Finset.mem_insert] at hj
            by_cases hji : j = i
            · rw [hji, Function.update_self, f1, tree_expr s i cs hn]
            · rw [Function.update_of_ne hji]
              exact f2.1 j (hj.resolve_left hji)
          · intro j hj
            dsimp only at hj ⊢
            rw [Finset.mem_insert] at hj
            by_cases hji : j = i
            · rw [hji, hreach, f3]
              intro k hk
              rw [Finset.mem_insert] at hk ⊢
              rcases hk with hk | hk
              · exact Or.inl hk
              · exact Or.inr (Finset.mem_union_right _ hk)
            · exact (f2.2 j (hj.resolve_left hji)).trans (Finset.subset_insert _ _)
          · rw [f3, hreach]
            ext j; simp only [Finset.mem_insert, Finset.mem_union]; tauto
          · rw [f4, hreach, Finset.insert_sdiff_of_notMem _ hi,
              Finset.card_insert_of_notMem]
            · ring
            · intro hmem; exact hiU (Finset.mem_sdiff.mp hmem).1

/-- From an empty cache, the remembering build reads the term's tree and makes
one node per distinct expression the term reaches. -/
theorem remember_empty (s : Store) (i : Nat) (v : Nat → Tree) :
    (remember s i ⟨∅, v⟩).1 = tree s i ∧
      (remember s i ⟨∅, v⟩).2.2 = (reach s i).card := by
  have hinv : Inv s ⟨∅, v⟩ := ⟨by simp, by simp⟩
  obtain ⟨h1, _, _, h4⟩ := remember_spec s i ⟨∅, v⟩ hinv
  exact ⟨h1, by simpa using h4⟩

/-! ## The doubling family -/

/-- The doubling family: id `0` is a leaf, id `k + 1` is `(pair k k)`. -/
def doubling : Store where
  node
    | 0 => .leaf 0
    | k + 1 => .expr [k, k]
  children_lt := by
    intro i cs h c hc
    cases i with
    | zero => simp at h
    | succ k =>
      simp only [Node.expr.injEq] at h
      subst h
      simp at hc
      omega

theorem doubling_succ (k : Nat) : doubling.node (k + 1) = .expr [k, k] := rfl

theorem pathViews_doubling (n : Nat) : pathViews doubling n = 2 ^ n - 1 := by
  induction n with
  | zero => simp [pathViews, doubling]
  | succ k ih =>
    rw [pathViews_expr doubling (k + 1) [k, k] (doubling_succ k)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, ih]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem reach_doubling (n : Nat) : reach doubling n = Finset.Icc 1 n := by
  induction n with
  | zero => rw [reach_leaf doubling 0 0 rfl]; rfl
  | succ k ih =>
    rw [reach_expr doubling (k + 1) [k, k] (doubling_succ k)]
    ext j
    simp only [Finset.mem_insert, mem_unionOf, Finset.mem_Icc]
    constructor
    · rintro (rfl | ⟨c, hc, hj⟩)
      · omega
      · have hc' := c.2
        simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hc'
        rw [hc', ih, Finset.mem_Icc] at hj
        omega
    · intro hj
      by_cases hjk : j = k + 1
      · exact Or.inl hjk
      · refine Or.inr ⟨⟨k, by simp⟩, List.mem_attach _ _, ?_⟩
        rw [ih, Finset.mem_Icc]
        omega

/-- On the doubling family the plain build makes `2 ^ n - 1` nodes and the
remembering build `n`, and both read the same tree. -/
theorem doubling_views (n : Nat) (v : Nat → Tree) :
    pathViews doubling n = 2 ^ n - 1 ∧
      (remember doubling n ⟨∅, v⟩).1 = tree doubling n ∧
      (remember doubling n ⟨∅, v⟩).2.2 = n := by
  obtain ⟨h1, h2⟩ := remember_empty doubling n v
  refine ⟨pathViews_doubling n, h1, ?_⟩
  rw [h2, reach_doubling, Nat.card_Icc]
  omega

end Mettapedia.Machines.SharedViewCost
