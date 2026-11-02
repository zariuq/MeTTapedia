import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Shifts

/-!
# Shared terms: a store of nodes with shifts on edges

A **store** is a list of nodes; a node's id is its position. A node is either the variable with
index `0` or a head with its fields, and each field names its child by a **reference** `⟨k, i⟩`:
"node `i`, with every free index moved up by `k`". The number `k` is the **shift on the edge**.
So one stored node can stand for many trees that differ by a shift. Example: `λ. (0 1)` and
`λ. (0 2)` are one node `L`, referenced as `⟨0, L⟩` and `⟨1, L⟩`.

* `unfold St r` is the tree a reference stands for (`unfold_eq`, `unfold_shift`).
* **Old references keep their meaning as the store grows** (`unfold_prefix`): stores only grow,
  by appending nodes whose children are already there (`Topo`).

## Canonical placement and pointer equality

Shifts on edges make sharing possible, and also make one tree representable in several ways:
`idx 1` is `⟨1, var⟩`, but a store could also hold a node for it. Pointer equality needs one
representation per tree. A store is **canonical** (`Canonical`) when

* it holds no node twice (hash-consing),
* every node it holds is **tight**: closed, or using its own index `0` (`Tight`), so that no shift
  can be pulled out of it, and
* a reference to a closed node carries shift `0` (`CanonRef`).

Then **two canonical references stand for the same tree exactly when they are equal**
(`unfold_eq_iff`). Trees have no bound names, so this is "alpha-equivalent terms are one node,
with one shift".
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

/-- A reference to a stored node, with a shift on the edge: `⟨k, i⟩` stands for the tree of node
`i` with every free index moved up by `k`. -/
structure Ref where
  shift : ℕ
  id : ℕ
  deriving DecidableEq, Repr

/-- A stored node: the variable with index `0`, or a head with its fields, each a binder count
and a child reference. -/
inductive Node (Head : Type) where
  | var
  | node (head : Head) (fields : List (ℕ × Ref))
  deriving DecidableEq, Repr

/-- A store: the nodes made so far, in order; a node's id is its position. -/
abbrev Store (Head : Type) := List (Node Head)

variable {Head : Type}

namespace Node

/-- The children of a node. -/
def children : Node Head → List Ref
  | .var => []
  | .node _ fields => fields.map Prod.snd

@[simp] theorem children_var : (Node.var : Node Head).children = [] := rfl

@[simp] theorem children_node (head : Head) (fields : List (ℕ × Ref)) :
    (Node.node head fields).children = fields.map Prod.snd := rfl

end Node

/-! ## Unfolding -/

/-- The fields of a node, each child read through `g`. -/
def fieldsOf (g : Ref → Term Head) : List (ℕ × Ref) → Fields Head
  | [] => .nil
  | (d, r) :: rest => .cons d (g r) (fieldsOf g rest)

/-- The tree of a node, its children read through `g`. -/
def Node.tree (g : Ref → Term Head) : Node Head → Term Head
  | .var => .idx 0
  | .node head fields => .node head (fieldsOf g fields)

theorem fieldsOf_congr {g g' : Ref → Term Head} :
    ∀ {fields : List (ℕ × Ref)}, (∀ p ∈ fields, g p.2 = g' p.2) → fieldsOf g fields = fieldsOf g' fields
  | [], _ => rfl
  | (d, r) :: rest, same => by
      simp only [fieldsOf]
      rw [same (d, r) (by simp), fieldsOf_congr (fun p mem => same p (by simp [mem]))]

theorem Node.tree_congr {g g' : Ref → Term Head} {n : Node Head}
    (same : ∀ r ∈ n.children, g r = g' r) : n.tree g = n.tree g' := by
  cases n with
  | var => rfl
  | node head fields =>
      simp only [Node.tree]
      rw [fieldsOf_congr (fun p mem => same p.2 (by simpa using ⟨p.1, mem⟩))]

/-- Different children give different fields: `fieldsOf` is injective where `g` is. -/
theorem fieldsOf_inj {g : Ref → Term Head} :
    ∀ {fs fs' : List (ℕ × Ref)}, fieldsOf g fs = fieldsOf g fs' →
      (∀ a ∈ fs, ∀ b ∈ fs', g a.2 = g b.2 → a.2 = b.2) → fs = fs'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [fieldsOf] at h
  | _ :: _, [], h, _ => by simp [fieldsOf] at h
  | (d, r) :: rest, (d', r') :: rest', h, inj => by
      simp only [fieldsOf, Fields.cons.injEq] at h
      obtain ⟨hd, hg, hrest⟩ := h
      have hr : r = r' := inj (d, r) (by simp) (d', r') (by simp) hg
      rw [hd, hr, fieldsOf_inj hrest (fun a ha b hb => inj a (by simp [ha]) b (by simp [hb]))]

/-- Unfold a reference, walking at most `fuel` nodes deep. -/
def unfoldF (St : Store Head) : ℕ → Ref → Term Head
  | 0, _ => .idx 0
  | fuel + 1, r => Term.lift 0 r.shift ((St[r.id]?.map (Node.tree (unfoldF St fuel))).getD (.idx 0))

/-- A store is **topological** when every child of a node was stored before it. -/
def Topo (St : Store Head) : Prop :=
  ∀ (i : ℕ) (n : Node Head), St[i]? = some n → ∀ r ∈ n.children, r.id < i

/-- **The tree a reference stands for.** -/
def unfold (St : Store Head) (r : Ref) : Term Head := unfoldF St (r.id + 1) r

theorem unfoldF_fuel {St : Store Head} (topo : Topo St) :
    ∀ (fuel fuel' : ℕ) (r : Ref), r.id < fuel → r.id < fuel' → unfoldF St fuel r = unfoldF St fuel' r
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, fuel' + 1, r, h, h' => by
      simp only [unfoldF]
      congr 1
      cases hn : St[r.id]? with
      | none => rfl
      | some n =>
          simp only [Option.map_some, Option.getD_some]
          exact Node.tree_congr fun c mem =>
            unfoldF_fuel topo fuel fuel' c (by have := topo _ _ hn c mem; omega)
              (by have := topo _ _ hn c mem; omega)

/-- With enough fuel, the walk is the unfolding. -/
theorem unfoldF_eq_unfold {St : Store Head} (topo : Topo St) {fuel : ℕ} {r : Ref}
    (enough : r.id < fuel) : unfoldF St fuel r = unfold St r :=
  unfoldF_fuel topo fuel (r.id + 1) r enough (Nat.lt_succ_self _)

/-- The tree of the node at an id, its children unfolded. -/
def nodeTree (St : Store Head) (i : ℕ) : Term Head :=
  (St[i]?.map (Node.tree (unfold St))).getD (.idx 0)

theorem nodeTree_some {St : Store Head} {i : ℕ} {n : Node Head} (h : St[i]? = some n) :
    nodeTree St i = n.tree (unfold St) := by
  simp [nodeTree, h]

/-- **Unfolding a reference**: the tree of its node, shifted by the shift on the edge. -/
theorem unfold_eq {St : Store Head} (topo : Topo St) (r : Ref) :
    unfold St r = Term.lift 0 r.shift (nodeTree St r.id) := by
  simp only [unfold, unfoldF, nodeTree]
  congr 1
  cases hn : St[r.id]? with
  | none => rfl
  | some n =>
      simp only [Option.map_some, Option.getD_some]
      exact Node.tree_congr fun c mem => unfoldF_eq_unfold topo (topo _ _ hn c mem)

/-- A reference with no shift stands for its node's tree. -/
theorem unfold_zero {St : Store Head} (topo : Topo St) (i : ℕ) :
    unfold St ⟨0, i⟩ = nodeTree St i := by
  rw [unfold_eq topo]; exact lift_zero 0 _

/-- **The shift on an edge is a shift of the tree.** -/
theorem unfold_shift {St : Store Head} (topo : Topo St) (k i : ℕ) :
    unfold St ⟨k, i⟩ = Term.lift 0 k (nodeTree St i) := unfold_eq topo _

/-! ## Stores only grow -/

theorem unfoldF_append {St : Store Head} (topo : Topo St) (extra : Store Head) :
    ∀ (fuel : ℕ) (r : Ref), r.id < St.length → unfoldF (St ++ extra) fuel r = unfoldF St fuel r
  | 0, _, _ => rfl
  | fuel + 1, r, valid => by
      simp only [unfoldF, List.getElem?_append_left valid]
      congr 1
      cases hn : St[r.id]? with
      | none => rfl
      | some n =>
          simp only [Option.map_some, Option.getD_some]
          exact Node.tree_congr fun c mem =>
            unfoldF_append topo extra fuel c (by have := topo _ _ hn c mem; omega)

/-- **Old references keep their meaning as the store grows.** -/
theorem unfold_prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St') {r : Ref}
    (valid : r.id < St.length) : unfold St' r = unfold St r := by
  obtain ⟨extra, rfl⟩ := grow
  exact unfoldF_append topo extra _ r valid

theorem getElem?_prefix {St St' : Store Head} (grow : St <+: St') {i : ℕ} (valid : i < St.length) :
    St'[i]? = St[i]? := by
  obtain ⟨extra, rfl⟩ := grow
  exact List.getElem?_append_left valid

theorem nodeTree_prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St') {i : ℕ}
    (valid : i < St.length) : nodeTree St' i = nodeTree St i := by
  unfold nodeTree
  rw [getElem?_prefix grow valid]
  cases hn : St[i]? with
  | none => rfl
  | some n =>
      simp only [Option.map_some, Option.getD_some]
      exact Node.tree_congr fun c mem =>
        unfold_prefix topo grow (by have := topo _ _ hn c mem; have := valid; omega)

theorem Topo.prefix {St St' : Store Head} (topo : Topo St') (grow : St <+: St') : Topo St := by
  obtain ⟨extra, rfl⟩ := grow
  intro i n hn r mem
  have valid : i < St.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hn
    cases hn
  exact topo i n (by rw [List.getElem?_append_left valid]; exact hn) r mem

/-! ## Canonical stores and pointer equality -/

/-- **A canonical reference**: it points into the store, and it carries no shift when its node is
closed (shifting a closed tree changes nothing, so a shift there would be a second spelling). -/
structure CanonRef (St : Store Head) (r : Ref) : Prop where
  valid : r.id < St.length
  noShift : Closed (nodeTree St r.id) → r.shift = 0

/-- **A canonical store**: topological, hash-consed (no node twice), every child reference
canonical, and every node tight. -/
structure Canonical (St : Store Head) : Prop where
  topo : Topo St
  nodup : St.Nodup
  childrenCanon : ∀ (i : ℕ) (n : Node Head), St[i]? = some n → ∀ r ∈ n.children, CanonRef St r
  tight : ∀ i < St.length, Tight (nodeTree St i)

theorem CanonRef.prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St') {r : Ref}
    (canon : CanonRef St r) : CanonRef St' r where
  valid := lt_of_lt_of_le canon.valid grow.length_le
  noShift := by rw [nodeTree_prefix topo grow canon.valid]; exact canon.noShift

/-- The shift of a canonical reference to an open node is the least free index of its tree. -/
theorem above_unfold_of_open {St : Store Head} (canon : Canonical St) {r : Ref}
    (valid : r.id < St.length) (open_ : ¬ Closed (nodeTree St r.id)) :
    above 0 (unfold St r) = some r.shift := by
  rw [unfold_eq canon.topo]
  exact above_lift_tight (canon.tight _ valid) open_ r.shift

theorem closed_unfold_iff {St : Store Head} (topo : Topo St) (r : Ref) :
    Closed (unfold St r) ↔ Closed (nodeTree St r.id) := by
  rw [unfold_eq topo]; exact closed_lift_zero_iff _ _

/-- Two canonical references with one tree have one shift and one node tree. -/
theorem shift_and_tree_of_unfold_eq {St : Store Head} (canon : Canonical St) {r r' : Ref}
    (hr : CanonRef St r) (hr' : CanonRef St r') (same : unfold St r = unfold St r') :
    r.shift = r'.shift ∧ nodeTree St r.id = nodeTree St r'.id := by
  have topo := canon.topo
  by_cases closed : Closed (nodeTree St r.id)
  · have closed' : Closed (nodeTree St r'.id) := by
      rw [← closed_unfold_iff topo, ← same, closed_unfold_iff topo]; exact closed
    have s := hr.noShift closed
    have s' := hr'.noShift closed'
    refine ⟨s.trans s'.symm, ?_⟩
    rw [unfold_eq topo, unfold_eq topo, s, s', lift_zero, lift_zero] at same
    exact same
  · have open' : ¬ Closed (nodeTree St r'.id) := by
      rw [← closed_unfold_iff topo, ← same, closed_unfold_iff topo]; exact closed
    have a := above_unfold_of_open canon hr.valid closed
    have a' := above_unfold_of_open canon hr'.valid open'
    rw [same, a'] at a
    have s : r.shift = r'.shift := (Option.some.inj a).symm
    refine ⟨s, ?_⟩
    rw [unfold_eq topo, unfold_eq topo, s] at same
    exact lift_injective 0 _ _ _ same

/-- Equal nodes in a hash-consed store have one id. -/
theorem id_eq_of_getElem?_eq {St : Store Head} (nodup : St.Nodup) {i j : ℕ} {n : Node Head}
    (hi : St[i]? = some n) (hj : St[j]? = some n) : i = j := by
  obtain ⟨vi, ei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨vj, ej⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj_iff nodup).mp (ei.trans ej.symm)

theorem eq_of_unfold_eq_aux {St : Store Head} (canon : Canonical St) :
    ∀ (s : ℕ) (r r' : Ref), r.id + r'.id < s → CanonRef St r → CanonRef St r' →
      unfold St r = unfold St r' → r = r'
  | 0, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | s + 1, r, r', bound, hr, hr', same => by
      obtain ⟨shiftEq, treeEq⟩ := shift_and_tree_of_unfold_eq canon hr hr' same
      obtain ⟨n, hn⟩ : ∃ n, St[r.id]? = some n :=
        Option.isSome_iff_exists.mp (by simp [hr.valid])
      obtain ⟨n', hn'⟩ : ∃ n', St[r'.id]? = some n' :=
        Option.isSome_iff_exists.mp (by simp [hr'.valid])
      rw [nodeTree_some hn, nodeTree_some hn'] at treeEq
      have nodeEq : n = n' := by
        cases n with
        | var =>
            cases n' with
            | var => rfl
            | node _ _ => simp [Node.tree] at treeEq
        | node head fields =>
            cases n' with
            | var => simp [Node.tree] at treeEq
            | node head' fields' =>
                simp only [Node.tree, Term.node.injEq] at treeEq
                obtain ⟨hh, hf⟩ := treeEq
                rw [hh, fieldsOf_inj hf (fun a ha b hb e => ?_)]
                have ca := canon.childrenCanon _ _ hn a.2 (by simpa using ⟨a.1, ha⟩)
                have cb := canon.childrenCanon _ _ hn' b.2 (by simpa using ⟨b.1, hb⟩)
                have la := canon.topo _ _ hn a.2 (by simpa using ⟨a.1, ha⟩)
                have lb := canon.topo _ _ hn' b.2 (by simpa using ⟨b.1, hb⟩)
                exact eq_of_unfold_eq_aux canon s a.2 b.2 (by omega) ca cb e
      subst nodeEq
      have idEq := id_eq_of_getElem?_eq canon.nodup hn hn'
      cases r; cases r'
      simp_all

/-- **Pointer equality is tree equality.** In a canonical store, two canonical references stand
for the same tree exactly when they are the same reference. -/
theorem unfold_eq_iff {St : Store Head} (canon : Canonical St) {r r' : Ref} (hr : CanonRef St r)
    (hr' : CanonRef St r') : unfold St r = unfold St r' ↔ r = r' :=
  ⟨eq_of_unfold_eq_aux canon (r.id + r'.id + 1) r r' (Nat.lt_succ_self _) hr hr',
    fun e => e ▸ rfl⟩

/-! ## Interning -/

/-- **Interning** a node: its id if the store holds it, else the store with it appended. -/
def intern (St : Store Head) (n : Node Head) [DecidableEq Head] : Store Head × ℕ :=
  match St.findIdx? (fun m => decide (m = n)) with
  | some i => (St, i)
  | none => (St ++ [n], St.length)

section Intern

variable [DecidableEq Head]

theorem intern_spec (St : Store Head) (n : Node Head) :
    (St <+: (intern St n).1) ∧ (intern St n).1[(intern St n).2]? = some n ∧
      ((∃ i, (intern St n).1 = St ∧ (intern St n).2 = i ∧ St[i]? = some n) ∨
        (n ∉ St ∧ (intern St n).1 = St ++ [n] ∧ (intern St n).2 = St.length)) := by
  unfold intern
  split
  · rename_i i found
    obtain ⟨bound, same, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
    have e : St[i] = n := of_decide_eq_true same
    have got : St[i]? = some n := List.getElem?_eq_some_iff.mpr ⟨bound, e⟩
    exact ⟨List.prefix_refl St, got, Or.inl ⟨i, rfl, rfl, got⟩⟩
  · rename_i none_found
    have notMem : n ∉ St := by
      intro mem
      obtain ⟨i, bound, e⟩ := List.getElem_of_mem mem
      have := List.findIdx?_eq_none_iff.mp none_found (St[i]) (List.getElem_mem bound)
      simp [e] at this
    refine ⟨List.prefix_append St [n], by simp, Or.inr ⟨notMem, rfl, rfl⟩⟩

theorem intern_prefix (St : Store Head) (n : Node Head) : St <+: (intern St n).1 :=
  (intern_spec St n).1

theorem intern_get (St : Store Head) (n : Node Head) :
    (intern St n).1[(intern St n).2]? = some n :=
  (intern_spec St n).2.1

theorem intern_valid (St : Store Head) (n : Node Head) :
    (intern St n).2 < (intern St n).1.length := by
  have := intern_get St n
  exact (List.getElem?_eq_some_iff.mp this).1

/-- Interning keeps a store canonical, when the node's children are canonical and its tree is
tight. -/
theorem intern_canonical {St : Store Head} (canon : Canonical St) {n : Node Head}
    (kids : ∀ r ∈ n.children, CanonRef St r) (tight : Tight (n.tree (unfold St))) :
    Canonical (intern St n).1 := by
  rcases (intern_spec St n).2.2 with ⟨i, same, _, _⟩ | ⟨notMem, appended, _⟩
  · rw [same]; exact canon
  · rw [appended]
    have topoNew : Topo (St ++ [n]) := by
      intro i m hm r mem
      by_cases old : i < St.length
      · rw [List.getElem?_append_left old] at hm
        exact canon.topo i m hm r mem
      · have eq : i = St.length := by
          have := (List.getElem?_eq_some_iff.mp hm).1
          simp at this; omega
        subst eq
        rw [List.getElem?_append_right (le_refl _)] at hm
        simp at hm
        subst hm
        rw [show St.length = St.length from rfl]
        exact (kids r mem).valid
    have grow : St <+: St ++ [n] := List.prefix_append St [n]
    refine ⟨topoNew, ?_, ?_, ?_⟩
    · exact List.nodup_append.mpr ⟨canon.nodup, List.nodup_singleton n,
        fun a ha b hb e => by simp at hb; subst hb; subst e; exact notMem ha⟩
    · intro i m hm r mem
      by_cases old : i < St.length
      · rw [List.getElem?_append_left old] at hm
        exact (canon.childrenCanon i m hm r mem).prefix canon.topo grow
      · have eq : i = St.length := by
          have := (List.getElem?_eq_some_iff.mp hm).1
          simp at this; omega
        subst eq
        rw [List.getElem?_append_right (le_refl _)] at hm
        simp at hm
        subst hm
        exact (kids r mem).prefix canon.topo grow
    · intro i bound
      by_cases old : i < St.length
      · rw [nodeTree_prefix canon.topo grow old]; exact canon.tight i old
      · have eq : i = St.length := by simp at bound; omega
        subst eq
        rw [nodeTree_some (by simp : (St ++ [n])[St.length]? = some n)]
        rw [Node.tree_congr (g' := unfold St) fun r mem =>
          unfold_prefix canon.topo grow (kids r mem).valid]
        exact tight

end Intern

/-- The empty store is canonical. -/
theorem canonical_nil : Canonical ([] : Store Head) where
  topo := fun i n h => by simp at h
  nodup := List.nodup_nil
  childrenCanon := fun i n h => by simp at h
  tight := fun i h => by simp at h

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms
