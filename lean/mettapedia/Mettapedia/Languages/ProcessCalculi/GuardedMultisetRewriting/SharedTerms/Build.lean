import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Store

/-!
# Building shared terms in a canonical store

Every operation here takes a store and returns a larger one with a reference; the old store is a
prefix of the new one, so every old reference keeps its meaning (`unfold_prefix`).

* `aboveRef St c r`: the least free index past `c` of the tree `r` stands for, read off the store
  (`aboveRef_eq`). For a canonical reference to an open node and `c ≤` its shift it needs no walk:
  the answer is the shift minus `c`.
* `lowerRef St c m r`: the reference for `lower c m (unfold St r)` (`lowerRef_spec`). Where the
  shift on the edge already clears the cutoff it only subtracts from the shift.
* `mkNode St head fields`: the canonical reference for `node head fields`
  (`mkNode_spec`). When the new node would skip its own index `0` (its least free index `m` is
  positive), it stores the node lowered by `m` and puts `m` on the edge: this is where shifts are
  pulled up so that every stored node is tight.
* `encode St t`: the canonical reference for any tree (`encode_spec`).

Together with `Store.unfold_eq_iff`: **two trees are equal exactly when encoding them in one store
gives one reference** (`encode_eq_iff`).

Example (`SharingControls`): `λ. (0 1)` and `λ. (0 2)` share their binder node; the second is the
first with shift `1` on the edge.

**Shifts, not thinnings.** Edges carry shifts. Building a binder whose body skips the next outer
variable stores the body first and then its lowered copy, so bottom-up building can leave an unused
node (`SharingControls.t2_garbage`). Thinnings on edges, which record exactly which outer variables a
child uses, would build without that copy; they are the comparison to measure later.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

variable {Head : Type}

/-! ## Trees: least free indices past a shift, lowering closed trees -/

theorem above_lift_zero_le {c k : ℕ} (le : c ≤ k) (t : Term Head) :
    above c (Term.lift 0 k t) = (above 0 t).map (fun j => j + k - c) := by
  apply (above_isLeast c _).unique
  have spec := above_isLeast 0 t
  simp only [zero_add] at spec
  cases h : above 0 t with
  | none =>
      rw [h] at spec
      intro j f
      obtain ⟨_, g⟩ := (freeAt_lift_zero k t (c + j)).mp f
      exact spec (c + j - k) g
  | some j0 =>
      rw [h] at spec
      refine ⟨?_, ?_⟩
      · show freeAt (Term.lift 0 k t) (c + (j0 + k - c)) = true
        refine (freeAt_lift_zero k t _).mpr ⟨by omega, ?_⟩
        rw [show c + (j0 + k - c) - k = j0 by omega]
        exact spec.1
      · intro j' f
        obtain ⟨_, g⟩ := (freeAt_lift_zero k t (c + j')).mp f
        have := spec.2 (c + j' - k) g
        show j0 + k - c ≤ j'
        omega

theorem above_lift_zero_ge {c k : ℕ} (le : k ≤ c) (t : Term Head) :
    above c (Term.lift 0 k t) = above (c - k) t := by
  apply (above_isLeast c _).unique
  refine (above_isLeast (c - k) t).congr fun j => ?_
  rw [freeAt_lift_zero]
  constructor
  · intro f; exact ⟨by omega, by rwa [show c + j - k = c - k + j by omega]⟩
  · rintro ⟨_, f⟩; rwa [show c + j - k = c - k + j by omega] at f

theorem lower_of_closed {t : Term Head} (closed : Closed t) (c m : ℕ) : lower c m t = t := by
  conv_lhs => rw [← lift_of_closed closed c m]
  exact lower_lift c m t

theorem fieldsFreeAt_fieldsOf (u : Ref → Term Head) :
    ∀ (fields : List (ℕ × Ref)) (i : ℕ),
      fieldsFreeAt (fieldsOf u fields) i = true ↔ ∃ x ∈ fields, freeAt (u x.2) (i + x.1) = true
  | [], i => by simp [fieldsOf]
  | (d, r) :: rest, i => by
      simp only [fieldsOf, fieldsFreeAt_cons, Bool.or_eq_true, List.mem_cons]
      rw [fieldsFreeAt_fieldsOf u rest i]
      constructor
      · rintro (f | ⟨x, mem, f⟩)
        · exact ⟨(d, r), Or.inl rfl, f⟩
        · exact ⟨x, Or.inr mem, f⟩
      · rintro ⟨x, (rfl | mem), f⟩
        · exact Or.inl f
        · exact Or.inr ⟨x, mem, f⟩

/-! ## Least free indices, read off the store -/

/-- The least free index past `c` of a node's fields, from that of each child. -/
def listAbove (g : ℕ → Ref → Option ℕ) (c : ℕ) : List (ℕ × Ref) → Option ℕ
  | [] => none
  | (d, r) :: rest => omin (g (c + d) r) (listAbove g c rest)

theorem listAbove_eq {g : ℕ → Ref → Option ℕ} {u : Ref → Term Head} :
    ∀ {fields : List (ℕ × Ref)}, (∀ x ∈ fields, ∀ c, g c x.2 = above c (u x.2)) →
      ∀ c, listAbove g c fields = fieldsAbove c (fieldsOf u fields)
  | [], _, _ => rfl
  | (d, r) :: rest, same, c => by
      simp only [listAbove, fieldsOf, fieldsAbove]
      rw [same (d, r) (by simp) (c + d), listAbove_eq (fun x mem => same x (by simp [mem])) c]

/-- The least free index past `c` of the tree of node `i`, its children read through `g`. -/
def nodeAbove (St : Store Head) (g : ℕ → Ref → Option ℕ) (i c : ℕ) : Option ℕ :=
  match St[i]? with
  | some (.node _ fields) => listAbove g c fields
  | _ => if c = 0 then some 0 else none

/-- `aboveF St fuel c r`: the least free index past `c` of `unfold St r`, walking at most `fuel`
nodes deep. -/
def aboveF (St : Store Head) : ℕ → ℕ → Ref → Option ℕ
  | 0, _, _ => none
  | fuel + 1, c, r =>
      if c ≤ r.shift then (nodeAbove St (aboveF St fuel) r.id 0).map (fun j => j + r.shift - c)
      else nodeAbove St (aboveF St fuel) r.id (c - r.shift)

theorem nodeTree_of_not_node {St : Store Head} {i : ℕ}
    (h : ∀ head fields, St[i]? ≠ some (.node head fields)) : nodeTree St i = .idx 0 := by
  unfold nodeTree
  cases hn : St[i]? with
  | none => rfl
  | some n =>
      cases n with
      | var => rfl
      | node head fields => exact absurd hn (h head fields)

theorem aboveF_eq {St : Store Head} (topo : Topo St) :
    ∀ (fuel c : ℕ) (r : Ref), r.id < fuel → aboveF St fuel c r = above c (unfold St r)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, c, r, h => by
      have inner : ∀ c', nodeAbove St (aboveF St fuel) r.id c' = above c' (nodeTree St r.id) := by
        intro c'
        unfold nodeAbove
        cases hn : St[r.id]? with
        | none =>
            rw [nodeTree_of_not_node (by intro _ _ e; rw [hn] at e; cases e)]
            by_cases z : c' = 0 <;> simp [above, z]
        | some n =>
            cases n with
            | var =>
                rw [nodeTree_of_not_node (by intro _ _ e; rw [hn] at e; cases e)]
                by_cases z : c' = 0 <;> simp [above, z]
            | node head fields =>
                simp only
                rw [nodeTree_some hn]
                simp only [Node.tree, above]
                exact listAbove_eq (fun x mem c'' => aboveF_eq topo fuel c'' x.2
                  (by have := topo _ _ hn x.2 (by simpa using ⟨x.1, mem⟩); omega)) c'
      simp only [aboveF]
      rw [inner 0, inner (c - r.shift), unfold_eq topo]
      by_cases le : c ≤ r.shift
      · rw [if_pos le, above_lift_zero_le le]
      · rw [if_neg le, above_lift_zero_ge (by omega)]

/-- The least free index past `c` of the tree a reference stands for. -/
def aboveRef (St : Store Head) (c : ℕ) (r : Ref) : Option ℕ := aboveF St (r.id + 1) c r

theorem aboveRef_eq {St : Store Head} (topo : Topo St) (c : ℕ) (r : Ref) :
    aboveRef St c r = above c (unfold St r) :=
  aboveF_eq topo _ c r (Nat.lt_succ_self _)

theorem aboveRef_node_none_iff {St : Store Head} (topo : Topo St) (i : ℕ) :
    aboveRef St 0 ⟨0, i⟩ = none ↔ Closed (nodeTree St i) := by
  rw [aboveRef_eq topo, unfold_zero topo, closed_iff_above_zero]

/-! ## Rebuilding fields, generically -/

/-- Rebuild a node's fields through `g`, which may grow the store; each child is visited at the
cutoff past its field's binders. -/
def mapFields (g : Store Head → ℕ → Ref → Store Head × Ref) :
    Store Head → ℕ → List (ℕ × Ref) → Store Head × List (ℕ × Ref)
  | St, _, [] => (St, [])
  | St, c, (d, r) :: rest =>
      let first := g St (c + d) r
      let others := mapFields g first.1 c rest
      (others.1, (d, first.2) :: others.2)

/-- **Rebuilding fields is correct when rebuilding each child is.** `g` computes `F` on the trees
of canonical references meeting `ok` and `pre`; then `mapFields g` computes `Fm`, the field form of
`F`, and keeps the store canonical. -/
theorem mapFields_spec [DecidableEq Head]
    (g : Store Head → ℕ → Ref → Store Head × Ref)
    (F : ℕ → Term Head → Term Head) (Fm : ℕ → Fields Head → Fields Head)
    (Fm_nil : ∀ c, Fm c .nil = .nil)
    (Fm_cons : ∀ c d t rest, Fm c (.cons d t rest) = .cons d (F (c + d) t) (Fm c rest))
    (ok : Ref → Prop) (pre : ℕ → Term Head → Prop) (base : Store Head)
    (hg : ∀ St c r, base <+: St → Canonical St → CanonRef St r → ok r → pre c (unfold St r) →
        St <+: (g St c r).1 ∧ Canonical (g St c r).1 ∧ CanonRef (g St c r).1 (g St c r).2 ∧
          unfold (g St c r).1 (g St c r).2 = F c (unfold St r)) :
    ∀ (fields : List (ℕ × Ref)) (St : Store Head) (c : ℕ), base <+: St → Canonical St →
      (∀ x ∈ fields, CanonRef St x.2) → (∀ x ∈ fields, ok x.2) →
      (∀ x ∈ fields, pre (c + x.1) (unfold St x.2)) →
      St <+: (mapFields g St c fields).1 ∧ Canonical (mapFields g St c fields).1 ∧
        (∀ x ∈ (mapFields g St c fields).2, CanonRef (mapFields g St c fields).1 x.2) ∧
        fieldsOf (unfold (mapFields g St c fields).1) (mapFields g St c fields).2 =
          Fm c (fieldsOf (unfold St) fields)
  | [], St, c, _, canon, _, _, _ => by
      refine ⟨List.prefix_refl St, canon, by simp [mapFields], ?_⟩
      simp [mapFields, fieldsOf, Fm_nil]
  | (d, r) :: rest, St, c, hb, canon, kids, oks, pres => by
      have hr : CanonRef St r := kids (d, r) (by simp)
      obtain ⟨grow1, canon1, cr1, eq1⟩ := hg St (c + d) r hb canon hr (oks (d, r) (by simp))
        (pres (d, r) (by simp))
      set first := g St (c + d) r with hfirst
      have kids1 : ∀ x ∈ rest, CanonRef first.1 x.2 :=
        fun x mem => (kids x (by simp [mem])).prefix canon.topo grow1
      have pres1 : ∀ x ∈ rest, pre (c + x.1) (unfold first.1 x.2) := by
        intro x mem
        rw [unfold_prefix canon.topo grow1 (kids x (by simp [mem])).valid]
        exact pres x (by simp [mem])
      obtain ⟨grow2, canon2, cr2, eq2⟩ := mapFields_spec g F Fm Fm_nil Fm_cons ok pre base hg rest first.1 c
        (hb.trans grow1) canon1 kids1 (fun x mem => oks x (by simp [mem])) pres1
      set others := mapFields g first.1 c rest with hothers
      refine ⟨grow1.trans grow2, canon2, ?_, ?_⟩
      · intro x mem
        simp only [mapFields, List.mem_cons] at mem
        rcases mem with rfl | mem
        · exact cr1.prefix canon1.topo grow2
        · exact cr2 x mem
      · simp only [mapFields, fieldsOf, Fm_cons]
        rw [unfold_prefix canon1.topo grow2 cr1.valid, eq1]
        congr 1
        rw [eq2]
        congr 1
        exact fieldsOf_congr fun x mem =>
          unfold_prefix canon.topo grow1 (kids x (by simp [mem])).valid

/-! ## Lowering -/

/-- `lowerF fuel St c m r`: a reference for `lower c m (unfold St r)`. -/
def lowerF [DecidableEq Head] : ℕ → Store Head → ℕ → ℕ → Ref → Store Head × Ref
  | 0, St, _, _, r => (St, r)
  | fuel + 1, St, c, m, r =>
      if aboveRef St 0 ⟨0, r.id⟩ = none then (St, r)
      else if c ≤ r.shift then (St, ⟨r.shift - m, r.id⟩)
      else match St[r.id]? with
        | some (.node head fields) =>
            let res := mapFields (fun St' c' r' => lowerF fuel St' c' m r') St (c - r.shift) fields
            let got := intern res.1 (.node head res.2)
            (got.1, ⟨r.shift, got.2⟩)
        | _ => (St, r)

/-- The gap condition of `lower c m` on a tree. -/
def Gap (m c : ℕ) (t : Term Head) : Prop := ∀ j < m, freeAt t (c + j) = false

theorem gap_of_lift {m c k : ℕ} {t : Term Head} (le : k ≤ c)
    (gap : Gap m c (Term.lift 0 k t)) : Gap m (c - k) t := by
  intro j lt
  cases f : freeAt t (c - k + j)
  · rfl
  · have := (freeAt_lift_zero k t (c + j)).mpr ⟨by omega, by rwa [show c + j - k = c - k + j by omega]⟩
    rw [gap j lt] at this; cases this

theorem gap_fields {m c : ℕ} {u : Ref → Term Head} {head : Head} {fields : List (ℕ × Ref)}
    (gap : Gap m c (.node head (fieldsOf u fields))) : ∀ x ∈ fields, Gap m (c + x.1) (u x.2) := by
  intro x mem j lt
  cases f : freeAt (u x.2) (c + x.1 + j)
  · rfl
  · have := (fieldsFreeAt_fieldsOf u fields (c + j)).mpr
      ⟨x, mem, by rwa [show c + j + x.1 = c + x.1 + j by omega]⟩
    have g := gap j lt
    rw [freeAt_node] at g
    rw [g] at this; cases this

theorem lowerF_spec [DecidableEq Head] : ∀ (fuel : ℕ) (St : Store Head) (c m : ℕ) (r : Ref),
    Canonical St → CanonRef St r → r.id < fuel → Gap m c (unfold St r) →
    St <+: (lowerF fuel St c m r).1 ∧ Canonical (lowerF fuel St c m r).1 ∧
      CanonRef (lowerF fuel St c m r).1 (lowerF fuel St c m r).2 ∧
      unfold (lowerF fuel St c m r).1 (lowerF fuel St c m r).2 = lower c m (unfold St r)
  | 0, _, _, _, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, St, c, m, r, canon, hr, h, gap => by
      have topo := canon.topo
      set T := nodeTree St r.id with hT
      have unfoldR : unfold St r = Term.lift 0 r.shift T := unfold_eq topo r
      simp only [lowerF]
      by_cases closedTest : aboveRef St 0 ⟨0, r.id⟩ = none
      · rw [if_pos closedTest]
        have closed : Closed T := (aboveRef_node_none_iff topo r.id).mp closedTest
        refine ⟨List.prefix_refl St, canon, hr, ?_⟩
        rw [unfoldR, lift_of_closed closed, lower_of_closed closed]
      · rw [if_neg closedTest]
        have open_ : ¬ Closed T := fun c' => closedTest ((aboveRef_node_none_iff topo r.id).mpr c')
        have uses : freeAt T 0 = true := (canon.tight r.id hr.valid).resolve_left open_
        have canonOpen : ∀ (St' : Store Head) (k i : ℕ), Canonical St' → i < St'.length →
            ¬ Closed (nodeTree St' i) → CanonRef St' ⟨k, i⟩ :=
          fun St' k i _ valid op => ⟨valid, fun cl => absurd cl op⟩
        by_cases far : c ≤ r.shift
        · rw [if_pos far]
          have big : c + m ≤ r.shift := by
            by_contra small
            have f := (freeAt_lift_zero r.shift T r.shift).mpr ⟨le_refl _, by simpa using uses⟩
            rw [← unfoldR] at f
            have := gap (r.shift - c) (by omega)
            rw [show c + (r.shift - c) = r.shift by omega, f] at this
            cases this
          refine ⟨List.prefix_refl St, canon, canonOpen St _ _ canon hr.valid open_, ?_⟩
          rw [unfold_eq topo, unfoldR]
          have := lower_lift_ge 0 c r.shift m big T
          simpa using this.symm
        · rw [if_neg far]
          have gapT : Gap m (c - r.shift) T := gap_of_lift (by omega) (unfoldR ▸ gap)
          cases hn : St[r.id]? with
          | none =>
              simp only
              have : T = .idx 0 := by
                rw [hT]; exact nodeTree_of_not_node (by intro _ _ e; rw [hn] at e; cases e)
              refine ⟨List.prefix_refl St, canon, hr, ?_⟩
              rw [unfoldR, this]
              simp [Term.lift, lower]
              omega
          | some n =>
              cases n with
              | var =>
                  simp only
                  have : T = .idx 0 := by
                    rw [hT]; exact nodeTree_of_not_node (by intro _ _ e; rw [hn] at e; cases e)
                  refine ⟨List.prefix_refl St, canon, hr, ?_⟩
                  rw [unfoldR, this]
                  simp [Term.lift, lower]
                  omega
              | node head fields =>
                  simp only
                  have treeT : T = .node head (fieldsOf (unfold St) fields) := by
                    rw [hT, nodeTree_some hn]; rfl
                  have kids : ∀ x ∈ fields, CanonRef St x.2 := fun x mem =>
                    canon.childrenCanon _ _ hn x.2 (by simpa using ⟨x.1, mem⟩)
                  have below : ∀ x ∈ fields, x.2.id < fuel := fun x mem => by
                    have := canon.topo _ _ hn x.2 (by simpa using ⟨x.1, mem⟩); omega
                  have pres : ∀ x ∈ fields, Gap m (c - r.shift + x.1) (unfold St x.2) :=
                    gap_fields (treeT ▸ gapT)
                  obtain ⟨grow1, canon1, kids1, eq1⟩ := mapFields_spec
                    (fun St' c' r' => lowerF fuel St' c' m r') (fun c' t => lower c' m t)
                    (fun c' fs => fieldsLower c' m fs) (fun _ => rfl) (fun _ _ _ _ => rfl)
                    (fun x => x.id < fuel) (fun c' t => Gap m c' t) []
                    (fun St' c' r' _ canon' hr' ok' pre' => lowerF_spec fuel St' c' m r' canon' hr' ok' pre')
                    fields St (c - r.shift) (List.nil_prefix) canon kids below pres
                  set res := mapFields (fun St' c' r' => lowerF fuel St' c' m r') St (c - r.shift)
                    fields with hres
                  have newTree : (Node.node head res.2).tree (unfold res.1) =
                      lower (c - r.shift) m T := by
                    simp only [Node.tree]
                    rw [eq1, treeT]; rfl
                  have tightNew : Tight ((Node.node head res.2).tree (unfold res.1)) := by
                    right
                    rw [newTree]
                    exact (freeAt_lower gapT 0).mpr (Or.inl ⟨by omega, uses⟩)
                  have canon2 := intern_canonical canon1 (n := .node head res.2)
                    (fun x mem => by
                      simp only [Node.children_node, List.mem_map] at mem
                      obtain ⟨y, ymem, rfl⟩ := mem
                      exact kids1 y ymem) tightNew
                  have grow2 := intern_prefix res.1 (.node head res.2)
                  have valid2 := intern_valid res.1 (.node head res.2)
                  have tree2 : nodeTree (intern res.1 (.node head res.2)).1
                      (intern res.1 (.node head res.2)).2 = lower (c - r.shift) m T := by
                    rw [nodeTree_some (intern_get res.1 _), ← newTree]
                    exact Node.tree_congr fun x mem => by
                      simp only [Node.children_node, List.mem_map] at mem
                      obtain ⟨y, ymem, rfl⟩ := mem
                      exact unfold_prefix canon1.topo grow2 (kids1 y ymem).valid
                  have open2 : ¬ Closed (nodeTree (intern res.1 (.node head res.2)).1
                      (intern res.1 (.node head res.2)).2) := by
                    rw [tree2]; intro cl
                    have := cl 0
                    rw [(freeAt_lower gapT 0).mpr (Or.inl ⟨by omega, uses⟩)] at this
                    cases this
                  refine ⟨grow1.trans grow2, canon2, canonOpen _ _ _ canon2 valid2 open2, ?_⟩
                  rw [unfold_eq canon2.topo, tree2, unfoldR]
                  have := lower_lift_lt 0 c r.shift m (by omega) T (fun j lt => by simpa using gapT j lt)
                  simpa using this.symm

/-- A reference for `lower c m (unfold St r)`. -/
def lowerRef [DecidableEq Head] (St : Store Head) (c m : ℕ) (r : Ref) : Store Head × Ref :=
  lowerF (r.id + 1) St c m r

theorem lowerRef_spec [DecidableEq Head] {St : Store Head} {c m : ℕ} {r : Ref}
    (canon : Canonical St) (hr : CanonRef St r) (gap : Gap m c (unfold St r)) :
    St <+: (lowerRef St c m r).1 ∧ Canonical (lowerRef St c m r).1 ∧
      CanonRef (lowerRef St c m r).1 (lowerRef St c m r).2 ∧
      unfold (lowerRef St c m r).1 (lowerRef St c m r).2 = lower c m (unfold St r) :=
  lowerF_spec _ St c m r canon hr (Nat.lt_succ_self _) gap

/-! ## Making a node: pulling the shift up -/

/-- **The canonical reference for a node** whose tree is
`node head (fieldsOf (unfold St) fields)`. When that tree skips indices `0, …, m - 1` (its least
free index is `m > 0`), the stored node is the tree lowered by `m`, and the edge carries `m`. -/
def mkNode [DecidableEq Head] (St : Store Head) (head : Head) (fields : List (ℕ × Ref)) :
    Store Head × Ref :=
  match listAbove (aboveRef St) 0 fields with
  | some (m + 1) =>
      let res := mapFields (fun St' c r => lowerRef St' c (m + 1) r) St 0 fields
      let got := intern res.1 (.node head res.2)
      (got.1, ⟨m + 1, got.2⟩)
  | _ =>
      let got := intern St (.node head fields)
      (got.1, ⟨0, got.2⟩)

/-- Interning a node whose tree is tight, with no shift on the edge. -/
theorem intern_plain_spec [DecidableEq Head] {St : Store Head} (canon : Canonical St) (head : Head)
    {fields : List (ℕ × Ref)} (kids : ∀ x ∈ fields, CanonRef St x.2)
    (tight : Tight (Term.node head (fieldsOf (unfold St) fields))) :
    St <+: (intern St (.node head fields)).1 ∧ Canonical (intern St (.node head fields)).1 ∧
      CanonRef (intern St (.node head fields)).1 ⟨0, (intern St (.node head fields)).2⟩ ∧
      unfold (intern St (.node head fields)).1 ⟨0, (intern St (.node head fields)).2⟩ =
        .node head (fieldsOf (unfold St) fields) := by
  have kids' : ∀ r ∈ (Node.node head fields).children, CanonRef St r := by
    intro r mem
    simp only [Node.children_node, List.mem_map] at mem
    obtain ⟨y, ymem, rfl⟩ := mem
    exact kids y ymem
  have canon2 := intern_canonical canon kids' tight
  have grow := intern_prefix St (.node head fields)
  have tree2 : nodeTree (intern St (.node head fields)).1 (intern St (.node head fields)).2 =
      .node head (fieldsOf (unfold St) fields) := by
    rw [nodeTree_some (intern_get St _)]
    simp only [Node.tree]
    congr 1
    exact fieldsOf_congr fun x mem => unfold_prefix canon.topo grow (kids x mem).valid
  refine ⟨grow, canon2, ⟨intern_valid St _, fun _ => rfl⟩, ?_⟩
  rw [unfold_zero canon2.topo, tree2]

/-- **`mkNode` is correct**: it keeps the store canonical and its reference stands for the node. -/
theorem mkNode_spec [DecidableEq Head] {St : Store Head} (canon : Canonical St) (head : Head)
    {fields : List (ℕ × Ref)} (kids : ∀ x ∈ fields, CanonRef St x.2) :
    St <+: (mkNode St head fields).1 ∧ Canonical (mkNode St head fields).1 ∧
      CanonRef (mkNode St head fields).1 (mkNode St head fields).2 ∧
      unfold (mkNode St head fields).1 (mkNode St head fields).2 =
        .node head (fieldsOf (unfold St) fields) := by
  have topo := canon.topo
  set T : Term Head := .node head (fieldsOf (unfold St) fields) with hT
  have hA : listAbove (aboveRef St) 0 fields = above 0 T := by
    rw [hT]; simp only [above]
    exact listAbove_eq (fun x _ c => aboveRef_eq topo c x.2) 0
  unfold mkNode
  rw [hA]
  rcases h : above 0 T with _ | _ | m
  · exact intern_plain_spec canon head kids (Or.inl ((closed_iff_above_zero T).mpr h))
  · have spec := above_isLeast 0 T
    rw [h] at spec
    exact intern_plain_spec canon head kids (Or.inr (by simpa using spec.1 : freeAt T 0 = true))
  · simp only
    obtain ⟨back, uses⟩ := tighten h
    have gapT : Gap (m + 1) 0 T := by
      have spec := above_isLeast 0 T
      rw [h] at spec
      intro j lt
      cases f : freeAt T (0 + j)
      · rfl
      · exact absurd (spec.2 j f) (by omega)
    obtain ⟨grow1, canon1, kids1, eq1⟩ := mapFields_spec
      (fun St' c r => lowerRef St' c (m + 1) r) (fun c t => lower c (m + 1) t)
      (fun c fs => fieldsLower c (m + 1) fs) (fun _ => rfl) (fun _ _ _ _ => rfl)
      (fun _ => True) (fun c t => Gap (m + 1) c t) []
      (fun St' c r _ canon' hr' _ pre' => lowerRef_spec canon' hr' pre')
      fields St 0 (List.nil_prefix) canon kids (fun _ _ => trivial) (gap_fields (hT ▸ gapT))
    set res := mapFields (fun St' c r => lowerRef St' c (m + 1) r) St 0 fields with hres
    have newTree : Term.node head (fieldsOf (unfold res.1) res.2) = lower 0 (m + 1) T := by
      rw [eq1, hT]; rfl
    obtain ⟨grow2, canon2, cr2, eq2⟩ := intern_plain_spec canon1 head kids1
      (by rw [newTree]; exact Or.inr uses)
    refine ⟨grow1.trans grow2, canon2, ?_, ?_⟩
    · refine ⟨cr2.valid, fun cl => ?_⟩
      have : Closed (unfold (intern res.1 (.node head res.2)).1
          ⟨0, (intern res.1 (.node head res.2)).2⟩) := by
        rw [unfold_zero canon2.topo]; exact cl
      rw [eq2, newTree] at this
      have := this 0
      rw [uses] at this; cases this
    · rw [unfold_shift canon2.topo, ← unfold_zero canon2.topo, eq2, newTree, back]

/-! ## Encoding trees -/

mutual

/-- **The canonical reference for a tree**, built bottom-up. -/
def encode [DecidableEq Head] : Store Head → Term Head → Store Head × Ref
  | St, .idx n =>
      let got := intern St .var
      (got.1, ⟨n, got.2⟩)
  | St, .node head fields =>
      let res := encodeFields St fields
      mkNode res.1 head res.2

def encodeFields [DecidableEq Head] : Store Head → Fields Head → Store Head × List (ℕ × Ref)
  | St, .nil => (St, [])
  | St, .cons d t rest =>
      let first := encode St t
      let others := encodeFields first.1 rest
      (others.1, (d, first.2) :: others.2)

end

mutual

/-- **Encoding is correct**: the store stays canonical and the reference stands for the tree. -/
theorem encode_spec [DecidableEq Head] (St : Store Head) (canon : Canonical St) (t : Term Head) :
    St <+: (encode St t).1 ∧ Canonical (encode St t).1 ∧ CanonRef (encode St t).1 (encode St t).2 ∧
      unfold (encode St t).1 (encode St t).2 = t := by
  cases t with
  | idx n =>
      simp only [encode]
      have canon2 := intern_canonical canon (n := (.var : Node Head)) (by simp)
        (Or.inr (by simp [Node.tree]))
      have tree2 : nodeTree (intern St (.var : Node Head)).1 (intern St (.var : Node Head)).2 =
          .idx 0 := by
        rw [nodeTree_some (intern_get St _)]; rfl
      refine ⟨intern_prefix St _, canon2, ⟨intern_valid St _, fun cl => ?_⟩, ?_⟩
      · rw [tree2] at cl
        have := cl 0
        simp at this
      · rw [unfold_shift canon2.topo, tree2]
        simp [Term.lift]
  | node head fields =>
      simp only [encode]
      obtain ⟨grow1, canon1, kids1, eq1⟩ := encodeFields_spec St canon fields
      obtain ⟨grow2, canon2, cr2, eq2⟩ := mkNode_spec canon1 head kids1
      exact ⟨grow1.trans grow2, canon2, cr2, by rw [eq2, eq1]⟩

theorem encodeFields_spec [DecidableEq Head] (St : Store Head) (canon : Canonical St)
    (fields : Fields Head) :
    St <+: (encodeFields St fields).1 ∧ Canonical (encodeFields St fields).1 ∧
      (∀ x ∈ (encodeFields St fields).2, CanonRef (encodeFields St fields).1 x.2) ∧
      fieldsOf (unfold (encodeFields St fields).1) (encodeFields St fields).2 = fields := by
  cases fields with
  | nil => exact ⟨List.prefix_refl St, canon, by simp [encodeFields], rfl⟩
  | cons d t rest =>
      simp only [encodeFields]
      obtain ⟨grow1, canon1, cr1, eq1⟩ := encode_spec St canon t
      obtain ⟨grow2, canon2, kids2, eq2⟩ := encodeFields_spec (encode St t).1 canon1 rest
      refine ⟨grow1.trans grow2, canon2, ?_, ?_⟩
      · intro x mem
        simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · exact cr1.prefix canon1.topo grow2
        · exact kids2 x mem
      · simp only [fieldsOf]
        rw [unfold_prefix canon1.topo grow2 cr1.valid, eq1, eq2]

end

/-- **Two trees are equal exactly when encoding them into one store gives one reference.** Trees
carry no bound names, so this is alpha-equivalence decided by pointer equality. -/
theorem encode_eq_iff [DecidableEq Head] {St : Store Head} (canon : Canonical St) (s t : Term Head) :
    s = t ↔ (encode St s).2 = (encode (encode St s).1 t).2 := by
  obtain ⟨grow1, canon1, cr1, eq1⟩ := encode_spec St canon s
  obtain ⟨grow2, canon2, cr2, eq2⟩ := encode_spec (encode St s).1 canon1 t
  rw [← unfold_eq_iff canon2 (cr1.prefix canon1.topo grow2) cr2, eq2,
    unfold_prefix canon1.topo grow2 cr1.valid, eq1]

/-! ## Controls -/

namespace SharingControls

/-- Two heads: a binder over one field, and application with two plain fields. -/
inductive H where
  | lam
  | app
  deriving DecidableEq, Repr

def lam (b : Term H) : Term H := .node .lam (.cons 1 b .nil)

def app (f x : Term H) : Term H := .node .app (.cons 0 f (.cons 0 x .nil))

/-- `λ. (0 1)`: tight, it uses the root's index `0`. -/
def t1 : Term H := lam (app (.idx 0) (.idx 1))

/-- `λ. (0 2)`: the same body one binder further out. -/
def t2 : Term H := lam (app (.idx 0) (.idx 2))

/-- Positive: `t1` is stored as three nodes (the variable, the application, the binder), referenced
with no shift. -/
theorem t1_stored : (encode [] t1).1.length = 3 ∧ (encode [] t1).2.shift = 0 := by decide +kernel

/-- Positive: `t2` is the node of `t1` with shift `1` on the edge. -/
theorem t2_shares_t1 :
    (encode (encode [] t1).1 t2).2 = ⟨1, (encode [] t1).2.id⟩ := by decide +kernel

/-- The price of building bottom-up: `t2`'s body `(0 2)` was stored before the binder showed that
it must be lowered, so one node of the store is unused. -/
theorem t2_garbage : (encode (encode [] t1).1 t2).1.length = 4 := by decide +kernel

/-- Negative: `λ. (0 1)` and `λ. (0 0)` are different trees, and encoding gives different
references. -/
theorem different_trees_different_refs :
    (encode [] t1).2 ≠ (encode (encode [] t1).1 (lam (app (.idx 0) (.idx 0)))).2 := by decide +kernel

end SharingControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms
