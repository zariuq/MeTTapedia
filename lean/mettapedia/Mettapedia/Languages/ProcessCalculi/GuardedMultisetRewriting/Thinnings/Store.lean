import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.CTerm

/-!
# A shared store of thinned nodes

A **store** is a list of nodes; a node's id is its position. A node is the variable, or a head with
its **support size** `n` and its fields; each field is a binder count `d` and an **edge** to a child:
a reference `⟨e, c⟩` whose thinning `e` places the child's support among the field's `d + n`
variables. A **reference** `⟨θ, i⟩` from outside the store does the same for a whole term: `θ`
places node `i`'s support in the surrounding scope.

Example: `(x z)` and `(x y)` in the scope `x, y, z` (innermost `z`) are one stored node, the
application of the outer to the inner of two variables, referenced as `⟨[true, false, true], a⟩`
and `⟨[false, true, true], a⟩` (`SharingControls` in `Build`). A node is the term's co-de-Bruijn
form, so it does not depend on where its variables sit in the scope.

* `nodeC St i` is node `i`'s co-de-Bruijn term; `unfold St r` is the binding tree a reference stands
  for (`unfold_eq`). **Old references keep their meaning as the store grows** (`unfold_prefix`).
* A store is **canonical** (`Canonical`) when it is topological (children first), holds no node
  twice, and every node is relevant: each edge is an exact thinning into `d + n` keeping the
  child's support, and the fields together use each of the node's `n` variables. A reference is
  canonical (`CanonRef`) when its thinning is trimmed and keeps the node's support.
* In a canonical store every node's term is relevant (`nodeC_ok`) and distinct nodes have distinct
  terms (`nodeC_inj`). So **two canonical references stand for the same tree exactly when they are
  equal** (`unfold_eq_iff`): alpha-equivalence is one comparison of references.
* Interning a relevant node keeps the store canonical (`intern_canonical`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Thin

/-- A reference to a stored node, with a thinning on the edge: `⟨θ, i⟩` stands for node `i`'s term,
its support placed in the surrounding scope by `θ`. -/
structure Ref where
  thin : Thin
  id : ℕ
  deriving DecidableEq, Repr

/-- A stored node: the variable, or a head with its support size and its fields, each a binder
count and an edge to a child. -/
inductive Node (Head : Type) where
  | var
  | node (head : Head) (scope : ℕ) (fields : List (ℕ × Ref))
  deriving DecidableEq, Repr

/-- A store: the nodes made so far, in order; a node's id is its position. -/
abbrev Store (Head : Type) := List (Node Head)

variable {Head : Type}

namespace Node

/-- The children of a node. -/
def children : Node Head → List Ref
  | .var => []
  | .node _ _ fields => fields.map Prod.snd

@[simp] theorem children_var : (Node.var : Node Head).children = [] := rfl

@[simp] theorem children_node (h : Head) (n : ℕ) (fs : List (ℕ × Ref)) :
    (Node.node h n fs).children = fs.map Prod.snd := rfl

end Node

/-- The support size of a stored node: `1` for the variable, the stored size for a node. -/
def supp (St : Store Head) (i : ℕ) : ℕ :=
  match St[i]? with
  | some .var => 1
  | some (.node _ n _) => n
  | none => 0

/-! ## The co-de-Bruijn term of a node -/

/-- The co-de-Bruijn fields of a stored node, each child read through `g`. -/
def cfieldsOf (g : ℕ → CTerm Head) (fs : List (ℕ × Ref)) : CFields Head :=
  CFields.ofList (fs.map fun x => (x.1, x.2.thin, g x.2.id))

/-- The co-de-Bruijn term of a stored node, its children read through `g`. -/
def Node.cterm (g : ℕ → CTerm Head) : Node Head → CTerm Head
  | .var => .var
  | .node h n fs => .node h n (cfieldsOf g fs)

theorem cfieldsOf_congr {g g' : ℕ → CTerm Head} :
    ∀ {fs : List (ℕ × Ref)}, (∀ x ∈ fs, g x.2.id = g' x.2.id) → cfieldsOf g fs = cfieldsOf g' fs
  | [], _ => rfl
  | x :: fs, same => by
      simp only [cfieldsOf, List.map_cons, CFields.ofList] at *
      rw [same x (by simp)]
      have := cfieldsOf_congr (fs := fs) fun y m => same y (by simp [m])
      simp only [cfieldsOf] at this
      rw [this]

theorem Node.cterm_congr {g g' : ℕ → CTerm Head} {nd : Node Head}
    (same : ∀ r ∈ nd.children, g r.id = g' r.id) : nd.cterm g = nd.cterm g' := by
  cases nd with
  | var => rfl
  | node h n fs =>
      simp only [Node.cterm]
      rw [cfieldsOf_congr fun x m => same x.2 (by simpa using ⟨x.1, m⟩)]

/-- Different children give different fields: `cfieldsOf` is injective where `g` is. -/
theorem cfieldsOf_inj {g : ℕ → CTerm Head} :
    ∀ {fs fs' : List (ℕ × Ref)}, cfieldsOf g fs = cfieldsOf g fs' →
      (∀ a ∈ fs, ∀ b ∈ fs', g a.2.id = g b.2.id → a.2.id = b.2.id) → fs = fs'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp [cfieldsOf, CFields.ofList] at h
  | _ :: _, [], h, _ => by simp [cfieldsOf, CFields.ofList] at h
  | (d, r) :: rest, (d', r') :: rest', h, inj => by
      simp only [cfieldsOf, List.map_cons, CFields.ofList, CFields.cons.injEq] at h
      obtain ⟨hd, ht, hg, hrest⟩ := h
      have hid : r.id = r'.id := inj (d, r) (by simp) (d', r') (by simp) hg
      have hr : r = r' := by cases r; cases r'; simp_all
      rw [hd, hr, cfieldsOf_inj (fs := rest) (fs' := rest') hrest
        (fun a ha b hb e => inj a (by simp [ha]) b (by simp [hb]) e)]

/-- The co-de-Bruijn term of node `i`, walking at most `fuel` nodes deep. -/
def nodeCF (St : Store Head) : ℕ → ℕ → CTerm Head
  | 0, _ => .var
  | fuel + 1, i => ((St[i]?).map (Node.cterm (nodeCF St fuel))).getD .var

/-- A store is **topological** when every child of a node was stored before it. -/
def Topo (St : Store Head) : Prop :=
  ∀ (i : ℕ) (nd : Node Head), St[i]? = some nd → ∀ r ∈ nd.children, r.id < i

/-- **The co-de-Bruijn term of a stored node.** -/
def nodeC (St : Store Head) (i : ℕ) : CTerm Head := nodeCF St (i + 1) i

theorem nodeCF_fuel {St : Store Head} (topo : Topo St) :
    ∀ (fuel fuel' i : ℕ), i < fuel → i < fuel' → nodeCF St fuel i = nodeCF St fuel' i
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, fuel' + 1, i, h, h' => by
      simp only [nodeCF]
      cases hn : St[i]? with
      | none => rfl
      | some nd =>
          simp only [Option.map_some, Option.getD_some]
          exact Node.cterm_congr fun c mem =>
            nodeCF_fuel topo fuel fuel' c.id (by have := topo _ _ hn c mem; omega)
              (by have := topo _ _ hn c mem; omega)

/-- **Unfolding a node one level**: its co-de-Bruijn term, its children's terms inside. -/
theorem nodeC_eq {St : Store Head} (topo : Topo St) (i : ℕ) :
    nodeC St i = ((St[i]?).map (Node.cterm (nodeC St))).getD .var := by
  simp only [nodeC, nodeCF]
  cases hn : St[i]? with
  | none => rfl
  | some nd =>
      simp only [Option.map_some, Option.getD_some]
      exact Node.cterm_congr fun c mem =>
        nodeCF_fuel topo i (c.id + 1) c.id (topo _ _ hn c mem) (Nat.lt_succ_self _)

theorem nodeC_some {St : Store Head} (topo : Topo St) {i : ℕ} {nd : Node Head}
    (h : St[i]? = some nd) : nodeC St i = nd.cterm (nodeC St) := by
  rw [nodeC_eq topo, h]; rfl

/-! ## What references stand for -/

/-- The thing a reference stands for: its thinning and its node's co-de-Bruijn term. -/
def unfoldC (St : Store Head) (r : Ref) : Thing Head := (r.thin, nodeC St r.id)

/-- **The binding tree a reference stands for.** -/
def unfold (St : Store Head) (r : Ref) : Term Head := decode (unfoldC St r)

/-- The binding tree of a stored node, over its support. -/
def nodeTree (St : Store Head) (i : ℕ) : Term Head := (nodeC St i).toTree

/-- **A reference stands for its node's tree, renamed along the reference's thinning.** -/
theorem unfold_eq (St : Store Head) (r : Ref) : unfold St r = rename r.thin (nodeTree St r.id) := rfl

/-! ## Stores only grow -/

theorem getElem?_prefix {St St' : Store Head} (grow : St <+: St') {i : ℕ} (valid : i < St.length) :
    St'[i]? = St[i]? := by
  obtain ⟨extra, rfl⟩ := grow
  exact List.getElem?_append_left valid

theorem nodeCF_append {St : Store Head} (topo : Topo St) (extra : Store Head) :
    ∀ (fuel i : ℕ), i < St.length → nodeCF (St ++ extra) fuel i = nodeCF St fuel i
  | 0, _, _ => rfl
  | fuel + 1, i, valid => by
      simp only [nodeCF, List.getElem?_append_left valid]
      cases hn : St[i]? with
      | none => rfl
      | some nd =>
          simp only [Option.map_some, Option.getD_some]
          exact Node.cterm_congr fun c mem =>
            nodeCF_append topo extra fuel c.id (by have := topo _ _ hn c mem; omega)

/-- **Old nodes keep their terms as the store grows.** -/
theorem nodeC_prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St') {i : ℕ}
    (valid : i < St.length) : nodeC St' i = nodeC St i := by
  obtain ⟨extra, rfl⟩ := grow
  exact nodeCF_append topo extra _ i valid

/-- **Old references keep their meaning as the store grows.** -/
theorem unfold_prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St') {r : Ref}
    (valid : r.id < St.length) : unfold St' r = unfold St r := by
  simp only [unfold, unfoldC, nodeC_prefix topo grow valid]

theorem unfoldC_prefix {St St' : Store Head} (topo : Topo St) (grow : St <+: St') {r : Ref}
    (valid : r.id < St.length) : unfoldC St' r = unfoldC St r := by
  simp only [unfoldC, nodeC_prefix topo grow valid]

theorem supp_prefix {St St' : Store Head} (grow : St <+: St') {i : ℕ} (valid : i < St.length) :
    supp St' i = supp St i := by
  simp only [supp, getElem?_prefix grow valid]

theorem Topo.prefix {St St' : Store Head} (topo : Topo St') (grow : St <+: St') : Topo St := by
  obtain ⟨extra, rfl⟩ := grow
  intro i nd hn r mem
  have valid : i < St.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hn
    cases hn
  exact topo i nd (by rw [List.getElem?_append_left valid]; exact hn) r mem

/-! ## Canonical stores -/

/-- **A relevant node** over a store: each edge is an exact thinning into the field's `d + n`
variables keeping its child's support, and the fields together use each of the node's `n`
variables. -/
def NodeOk (St : Store Head) (nd : Node Head) : Prop :=
  ∀ h n fs, nd = .node h n fs →
    (∀ x ∈ fs, x.2.id < St.length ∧ x.2.thin.length = x.1 + n ∧ ones x.2.thin = supp St x.2.id) ∧
      bors (fs.map fun x => back x.1 x.2.thin) = idn n

/-- **A canonical store**: topological, hash-consed (no node twice), and every node relevant. -/
structure Canonical (St : Store Head) : Prop where
  topo : Topo St
  nodup : St.Nodup
  nodes : ∀ (i : ℕ) (nd : Node Head), St[i]? = some nd → NodeOk St nd

/-- **A canonical reference**: it points into the store, its thinning is trimmed, and it keeps
exactly the node's support. -/
structure CanonRef (St : Store Head) (r : Ref) : Prop where
  valid : r.id < St.length
  trim : trimmed r.thin = true
  ones_eq : ones r.thin = supp St r.id

theorem NodeOk.prefix {St St' : Store Head} (grow : St <+: St') {nd : Node Head}
    (ok : NodeOk St nd) : NodeOk St' nd := by
  intro h n fs e
  obtain ⟨edges, cover⟩ := ok h n fs e
  refine ⟨fun x m => ?_, cover⟩
  obtain ⟨valid, len, ones_eq⟩ := edges x m
  exact ⟨lt_of_lt_of_le valid grow.length_le, len, by rw [supp_prefix grow valid]; exact ones_eq⟩

theorem CanonRef.prefix {St St' : Store Head} (grow : St <+: St') {r : Ref} (canon : CanonRef St r) :
    CanonRef St' r where
  valid := lt_of_lt_of_le canon.valid grow.length_le
  trim := canon.trim
  ones_eq := by rw [supp_prefix grow canon.valid]; exact canon.ones_eq

theorem nodeC_var {St : Store Head} (topo : Topo St) {i : ℕ} (h : St[i]? = some .var) :
    nodeC St i = .var := by
  rw [nodeC_some topo h]; rfl

theorem nodeC_node {St : Store Head} (topo : Topo St) {i : ℕ} {hd : Head} {n : ℕ}
    {fs : List (ℕ × Ref)} (h : St[i]? = some (.node hd n fs)) :
    nodeC St i = .node hd n (cfieldsOf (nodeC St) fs) := by
  rw [nodeC_some topo h]; rfl

/-- **Every node of a canonical store is relevant at its support.** -/
theorem nodeC_ok {St : Store Head} (canon : Canonical St) :
    ∀ i, i < St.length → (nodeC St i).ok (supp St i) = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
      intro valid
      obtain ⟨nd, hn⟩ : ∃ nd, St[i]? = some nd :=
        Option.isSome_iff_exists.mp (by simp [valid])
      cases nd with
      | var =>
          rw [nodeC_var canon.topo hn]
          simp [supp, hn]
      | node hd n fs =>
          rw [nodeC_node canon.topo hn]
          have suppEq : supp St i = n := by simp [supp, hn]
          obtain ⟨edges, cover⟩ := canon.nodes i _ hn hd n fs rfl
          simp only [suppEq, CTerm.ok_node, decide_true, Bool.true_and, Bool.and_eq_true]
          refine ⟨ok_ofList _ fun y my => ?_, ?_⟩
          · obtain ⟨x, mx, rfl⟩ := List.mem_map.mp my
            obtain ⟨xv, len, ones_eq⟩ := edges x mx
            refine ⟨len, ?_⟩
            rw [ones_eq]
            exact ih x.2.id (canon.topo i _ hn x.2 (by simpa using ⟨x.1, mx⟩)) xv
          · simp only [CFields.covers, cfieldsOf, outer_ofList, List.map_map, decide_eq_true_eq]
            exact cover

/-- Equal nodes in a hash-consed store have one id. -/
theorem id_eq_of_getElem?_eq {St : Store Head} (nodup : St.Nodup) {i j : ℕ} {nd : Node Head}
    (hi : St[i]? = some nd) (hj : St[j]? = some nd) : i = j := by
  obtain ⟨vi, ei⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨vj, ej⟩ := List.getElem?_eq_some_iff.mp hj
  exact (List.Nodup.getElem_inj_iff nodup).mp (ei.trans ej.symm)

theorem nodeC_inj_aux {St : Store Head} (canon : Canonical St) :
    ∀ (s i j : ℕ), i + j < s → i < St.length → j < St.length → nodeC St i = nodeC St j → i = j
  | 0, _, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | s + 1, i, j, bound, vi, vj, same => by
      obtain ⟨nd, hn⟩ : ∃ nd, St[i]? = some nd := Option.isSome_iff_exists.mp (by simp [vi])
      obtain ⟨nd', hn'⟩ : ∃ nd', St[j]? = some nd' := Option.isSome_iff_exists.mp (by simp [vj])
      rw [nodeC_some canon.topo hn, nodeC_some canon.topo hn'] at same
      have ndEq : nd = nd' := by
        cases nd with
        | var =>
            cases nd' with
            | var => rfl
            | node _ _ _ => simp [Node.cterm] at same
        | node hd n fs =>
            cases nd' with
            | var => simp [Node.cterm] at same
            | node hd' n' fs' =>
                simp only [Node.cterm, CTerm.node.injEq] at same
                obtain ⟨rfl, rfl, hf⟩ := same
                rw [cfieldsOf_inj hf fun a ha b hb e => ?_]
                have la := canon.topo _ _ hn a.2 (by simpa using ⟨a.1, ha⟩)
                have lb := canon.topo _ _ hn' b.2 (by simpa using ⟨b.1, hb⟩)
                exact nodeC_inj_aux canon s a.2.id b.2.id (by omega) (by omega) (by omega) e
      subst ndEq
      exact id_eq_of_getElem?_eq canon.nodup hn hn'

/-- **Distinct nodes of a canonical store have distinct terms.** -/
theorem nodeC_inj {St : Store Head} (canon : Canonical St) {i j : ℕ} (vi : i < St.length)
    (vj : j < St.length) (same : nodeC St i = nodeC St j) : i = j :=
  nodeC_inj_aux canon (i + j + 1) i j (Nat.lt_succ_self _) vi vj same

/-- A canonical reference stands for a canonical thing. -/
theorem canon_unfoldC {St : Store Head} (canon : Canonical St) {r : Ref} (hr : CanonRef St r) :
    Canon (unfoldC St r) :=
  ⟨hr.trim, by simp only [unfoldC]; rw [hr.ones_eq]; exact nodeC_ok canon r.id hr.valid⟩

/-- **Pointer equality is tree equality.** In a canonical store, two canonical references stand
for the same tree exactly when they are the same reference. -/
theorem unfold_eq_iff {St : Store Head} (canon : Canonical St) {r r' : Ref} (hr : CanonRef St r)
    (hr' : CanonRef St r') : unfold St r = unfold St r' ↔ r = r' := by
  constructor
  · intro e
    have same := decode_inj (canon_unfoldC canon hr) (canon_unfoldC canon hr') e
    simp only [unfoldC, Prod.mk.injEq] at same
    have := nodeC_inj canon hr.valid hr'.valid same.2
    cases r; cases r'
    simp_all
  · rintro rfl; rfl

/-- **The support of a term is read off its reference**: the free variables of what a canonical
reference stands for are exactly the kept positions of its thinning. -/
theorem freeAt_unfold {St : Store Head} (canon : Canonical St) {r : Ref} (hr : CanonRef St r)
    (i : ℕ) : freeAt (unfold St r) i = bit r.thin i :=
  freeAt_decode (canon_unfoldC canon hr) i

/-! ## Interning -/

/-- **Interning** a node: its id if the store holds it, else the store with it appended. -/
def intern [DecidableEq Head] (St : Store Head) (nd : Node Head) : Store Head × ℕ :=
  match St.findIdx? (fun m => decide (m = nd)) with
  | some i => (St, i)
  | none => (St ++ [nd], St.length)

section Intern

variable [DecidableEq Head]

theorem intern_spec (St : Store Head) (nd : Node Head) :
    (St <+: (intern St nd).1) ∧ (intern St nd).1[(intern St nd).2]? = some nd ∧
      ((∃ i, (intern St nd).1 = St ∧ (intern St nd).2 = i ∧ St[i]? = some nd) ∨
        (nd ∉ St ∧ (intern St nd).1 = St ++ [nd] ∧ (intern St nd).2 = St.length)) := by
  unfold intern
  split
  · rename_i i found
    obtain ⟨bound, same, _⟩ := List.findIdx?_eq_some_iff_getElem.mp found
    have e : St[i] = nd := of_decide_eq_true same
    have got : St[i]? = some nd := List.getElem?_eq_some_iff.mpr ⟨bound, e⟩
    exact ⟨List.prefix_refl St, got, Or.inl ⟨i, rfl, rfl, got⟩⟩
  · rename_i none_found
    have notMem : nd ∉ St := by
      intro mem
      obtain ⟨i, bound, e⟩ := List.getElem_of_mem mem
      have := List.findIdx?_eq_none_iff.mp none_found (St[i]) (List.getElem_mem bound)
      simp [e] at this
    refine ⟨List.prefix_append St [nd], by simp, Or.inr ⟨notMem, rfl, rfl⟩⟩

theorem intern_prefix (St : Store Head) (nd : Node Head) : St <+: (intern St nd).1 :=
  (intern_spec St nd).1

theorem intern_get (St : Store Head) (nd : Node Head) :
    (intern St nd).1[(intern St nd).2]? = some nd :=
  (intern_spec St nd).2.1

theorem intern_valid (St : Store Head) (nd : Node Head) :
    (intern St nd).2 < (intern St nd).1.length := by
  have := intern_get St nd
  exact (List.getElem?_eq_some_iff.mp this).1

/-- **Interning allocates at most one node.** -/
theorem intern_length_le (St : Store Head) (nd : Node Head) :
    (intern St nd).1.length ≤ St.length + 1 := by
  rcases (intern_spec St nd).2.2 with ⟨_, same, _, _⟩ | ⟨_, appended, _⟩
  · rw [same]; omega
  · rw [appended]; simp

/-- **Interning a relevant node keeps the store canonical.** -/
theorem intern_canonical {St : Store Head} (canon : Canonical St) {nd : Node Head}
    (ok : NodeOk St nd) : Canonical (intern St nd).1 := by
  rcases (intern_spec St nd).2.2 with ⟨i, same, _, _⟩ | ⟨notMem, appended, _⟩
  · rw [same]; exact canon
  · rw [appended]
    have grow : St <+: St ++ [nd] := List.prefix_append St [nd]
    have topoNew : Topo (St ++ [nd]) := by
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
        cases nd with
        | var => simp at mem
        | node h n fs =>
            simp only [Node.children_node, List.mem_map] at mem
            obtain ⟨x, mx, rfl⟩ := mem
            exact ((ok h n fs rfl).1 x mx).1
    refine ⟨topoNew, ?_, ?_⟩
    · exact List.nodup_append.mpr ⟨canon.nodup, List.nodup_singleton nd,
        fun a ha b hb e => by simp at hb; subst hb; subst e; exact notMem ha⟩
    · intro i m hm
      by_cases old : i < St.length
      · rw [List.getElem?_append_left old] at hm
        exact (canon.nodes i m hm).prefix grow
      · have eq : i = St.length := by
          have := (List.getElem?_eq_some_iff.mp hm).1
          simp at this; omega
        subst eq
        rw [List.getElem?_append_right (le_refl _)] at hm
        simp at hm
        subst hm
        exact ok.prefix grow

end Intern

/-- The empty store is canonical. -/
theorem canonical_nil : Canonical ([] : Store Head) where
  topo := fun i n h => by simp at h
  nodup := List.nodup_nil
  nodes := fun i n h => by simp at h

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
