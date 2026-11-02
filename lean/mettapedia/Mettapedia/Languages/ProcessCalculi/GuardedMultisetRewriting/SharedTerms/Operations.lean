import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms.Build

/-!
# Operations on shared terms: shift, lift, open, view

Each operation works on references and the store, and computes exactly the tree operation on what
the references stand for. These are the operations a step uses: taking a stored term apart to
match it (`view`), moving a term under binders (`shiftRef`, `liftRef`), and opening a binder with
a value (`openRef`).

* **Shifting past the root allocates nothing** (`shiftRef_spec`): it adds to the shift on the edge,
  or leaves a closed node alone. This is what shifts on edges buy.
* **Lifting past a cutoff** (`liftRef_spec`) is the same addition when the edge's shift already
  clears the cutoff; otherwise it rebuilds the nodes on the way to the indices it moves.
* **Opening a binder shifts the value** (`openRef_spec`): `openRef St d v b` stands for
  `instantiateAt d (unfold St v) (unfold St b)`, which puts the value under the binders it crosses
  with a shift on the edge. This is the shifting `open` the tier-0 kernel lacks (its `t0:open-at`
  substitutes without shifting).
* **Viewing a reference** (`view_spec`) gives its head and fields, the edge's shift pushed into
  the fields, or the index it stands for.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT

variable {Head : Type}

/-! ## Shifting past the root -/

/-- **Shift a reference by `a`**: add `a` to the shift on the edge; a closed node takes no
shift. -/
def shiftRef (St : Store Head) (a : ℕ) (r : Ref) : Ref :=
  if aboveRef St 0 ⟨0, r.id⟩ = none then r else ⟨r.shift + a, r.id⟩

theorem not_closed_of_test {St : Store Head} (topo : Topo St) {i : ℕ}
    (test : ¬ aboveRef St 0 ⟨0, i⟩ = none) : ¬ Closed (nodeTree St i) :=
  fun c => test ((aboveRef_node_none_iff topo i).mpr c)

/-- **Shifting allocates nothing and is the tree's shift.** -/
theorem shiftRef_spec {St : Store Head} (canon : Canonical St) {r : Ref} (hr : CanonRef St r)
    (a : ℕ) :
    CanonRef St (shiftRef St a r) ∧ unfold St (shiftRef St a r) = Term.lift 0 a (unfold St r) := by
  unfold shiftRef
  by_cases closedTest : aboveRef St 0 ⟨0, r.id⟩ = none
  · rw [if_pos closedTest]
    have closed := (aboveRef_node_none_iff canon.topo r.id).mp closedTest
    refine ⟨hr, ?_⟩
    rw [unfold_eq canon.topo, lift_of_closed closed, lift_of_closed closed]
  · rw [if_neg closedTest]
    have open_ := not_closed_of_test canon.topo closedTest
    refine ⟨⟨hr.valid, fun c => absurd c open_⟩, ?_⟩
    rw [unfold_shift canon.topo, unfold_eq canon.topo, lift_lift_zero]

/-! ## Lifting past a cutoff -/

/-- `liftF fuel St c a r`: a reference for `lift c a (unfold St r)`. -/
def liftF [DecidableEq Head] : ℕ → Store Head → ℕ → ℕ → Ref → Store Head × Ref
  | 0, St, _, _, r => (St, r)
  | fuel + 1, St, c, a, r =>
      if aboveRef St 0 ⟨0, r.id⟩ = none then (St, r)
      else if c ≤ r.shift then (St, ⟨r.shift + a, r.id⟩)
      else match St[r.id]? with
        | some (.node head fields) =>
            let res := mapFields (fun St' c' r' => liftF fuel St' c' a r') St (c - r.shift) fields
            let made := mkNode res.1 head res.2
            (made.1, shiftRef made.1 r.shift made.2)
        | _ => (St, r)

theorem tree_of_not_node {St : Store Head} {i : ℕ}
    (h : ∀ (head : Head) fields, St[i]? ≠ some (.node head fields)) : nodeTree St i = .idx 0 :=
  nodeTree_of_not_node h

theorem liftF_spec [DecidableEq Head] : ∀ (fuel : ℕ) (St : Store Head) (c a : ℕ) (r : Ref),
    Canonical St → CanonRef St r → r.id < fuel →
    St <+: (liftF fuel St c a r).1 ∧ Canonical (liftF fuel St c a r).1 ∧
      CanonRef (liftF fuel St c a r).1 (liftF fuel St c a r).2 ∧
      unfold (liftF fuel St c a r).1 (liftF fuel St c a r).2 = Term.lift c a (unfold St r)
  | 0, _, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, St, c, a, r, canon, hr, h => by
      have topo := canon.topo
      set T := nodeTree St r.id with hT
      have unfoldR : unfold St r = Term.lift 0 r.shift T := unfold_eq topo r
      simp only [liftF]
      by_cases closedTest : aboveRef St 0 ⟨0, r.id⟩ = none
      · rw [if_pos closedTest]
        have closed : Closed T := (aboveRef_node_none_iff topo r.id).mp closedTest
        refine ⟨List.prefix_refl St, canon, hr, ?_⟩
        rw [unfoldR, lift_of_closed closed, lift_of_closed closed]
      · rw [if_neg closedTest]
        have open_ : ¬ Closed T := not_closed_of_test topo closedTest
        by_cases far : c ≤ r.shift
        · rw [if_pos far]
          refine ⟨List.prefix_refl St, canon, ⟨hr.valid, fun cl => absurd cl open_⟩, ?_⟩
          rw [unfold_shift topo, unfoldR, lift_lift_le a r.shift (Nat.zero_le c) (by omega) T]
        · rw [if_neg far]
          have commute : Term.lift c a (Term.lift 0 r.shift T) =
              Term.lift 0 r.shift (Term.lift (c - r.shift) a T) := by
            have := lift_comm a r.shift (c := 0) (c' := c - r.shift) (Nat.zero_le _) T
            rwa [show c - r.shift + r.shift = c by omega] at this
          cases hn : St[r.id]? with
          | none =>
              simp only
              have : T = .idx 0 := by
                rw [hT]; exact tree_of_not_node (by intro _ _ e; rw [hn] at e; cases e)
              refine ⟨List.prefix_refl St, canon, hr, ?_⟩
              rw [unfoldR, commute, this]
              have pos : 0 < c - r.shift := by omega
              simp [Term.lift, pos]
          | some n =>
              cases n with
              | var =>
                  simp only
                  have : T = .idx 0 := by
                    rw [hT]; exact tree_of_not_node (by intro _ _ e; rw [hn] at e; cases e)
                  refine ⟨List.prefix_refl St, canon, hr, ?_⟩
                  rw [unfoldR, commute, this]
                  have pos : 0 < c - r.shift := by omega
                  simp [Term.lift, pos]
              | node head fields =>
                  simp only
                  have treeT : T = .node head (fieldsOf (unfold St) fields) := by
                    rw [hT, nodeTree_some hn]; rfl
                  have kids : ∀ x ∈ fields, CanonRef St x.2 := fun x mem =>
                    canon.childrenCanon _ _ hn x.2 (by simpa using ⟨x.1, mem⟩)
                  have below : ∀ x ∈ fields, x.2.id < fuel := fun x mem => by
                    have := canon.topo _ _ hn x.2 (by simpa using ⟨x.1, mem⟩); omega
                  obtain ⟨grow1, canon1, kids1, eq1⟩ := mapFields_spec
                    (fun St' c' r' => liftF fuel St' c' a r') (fun c' t => Term.lift c' a t)
                    (fun c' fs => Term.Fields.lift c' a fs) (fun _ => rfl) (fun _ _ _ _ => rfl)
                    (fun x => x.id < fuel) (fun _ _ => True) []
                    (fun St' c' r' _ canon' hr' ok' _ => liftF_spec fuel St' c' a r' canon' hr' ok')
                    fields St (c - r.shift) List.nil_prefix canon kids below (fun _ _ => trivial)
                  set res := mapFields (fun St' c' r' => liftF fuel St' c' a r') St (c - r.shift)
                    fields with hres
                  obtain ⟨grow2, canon2, cr2, eq2⟩ := mkNode_spec canon1 head kids1
                  obtain ⟨cr3, eq3⟩ := shiftRef_spec canon2 cr2 r.shift
                  refine ⟨grow1.trans grow2, canon2, cr3, ?_⟩
                  rw [eq3, eq2, eq1, unfoldR, commute, treeT]
                  rfl

/-- A reference for `lift c a (unfold St r)`. -/
def liftRef [DecidableEq Head] (St : Store Head) (c a : ℕ) (r : Ref) : Store Head × Ref :=
  liftF (r.id + 1) St c a r

theorem liftRef_spec [DecidableEq Head] {St : Store Head} (canon : Canonical St) {r : Ref}
    (hr : CanonRef St r) (c a : ℕ) :
    St <+: (liftRef St c a r).1 ∧ Canonical (liftRef St c a r).1 ∧
      CanonRef (liftRef St c a r).1 (liftRef St c a r).2 ∧
      unfold (liftRef St c a r).1 (liftRef St c a r).2 = Term.lift c a (unfold St r) :=
  liftF_spec _ St c a r canon hr (Nat.lt_succ_self _)

/-! ## Opening a binder -/

/-- `openF fuel St d v r`: a reference for `instantiateAt d (unfold St v) (unfold St r)`: index
`d` of the body becomes the value, shifted under the binders it crosses. -/
def openF [DecidableEq Head] : ℕ → Store Head → ℕ → Ref → Ref → Store Head × Ref
  | 0, St, _, _, r => (St, r)
  | fuel + 1, St, d, v, r =>
      if aboveRef St 0 ⟨0, r.id⟩ = none then (St, r)
      else if d < r.shift then (St, ⟨r.shift - 1, r.id⟩)
      else match St[r.id]? with
        | some (.node head fields) =>
            let res := mapFields (fun St' c' r' => openF fuel St' c' v r') St (d - r.shift) fields
            let made := mkNode res.1 head res.2
            (made.1, shiftRef made.1 r.shift made.2)
        | _ => if d = r.shift then (St, shiftRef St r.shift v) else (St, r)

theorem openF_spec [DecidableEq Head] : ∀ (fuel : ℕ) (St : Store Head) (d : ℕ) (v r : Ref),
    Canonical St → CanonRef St v → CanonRef St r → r.id < fuel →
    St <+: (openF fuel St d v r).1 ∧ Canonical (openF fuel St d v r).1 ∧
      CanonRef (openF fuel St d v r).1 (openF fuel St d v r).2 ∧
      unfold (openF fuel St d v r).1 (openF fuel St d v r).2 =
        Term.instantiateAt d (unfold St v) (unfold St r)
  | 0, _, _, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, St, d, v, r, canon, hv, hr, h => by
      have topo := canon.topo
      set T := nodeTree St r.id with hT
      set V := unfold St v with hV
      have unfoldR : unfold St r = Term.lift 0 r.shift T := unfold_eq topo r
      simp only [openF]
      by_cases closedTest : aboveRef St 0 ⟨0, r.id⟩ = none
      · rw [if_pos closedTest]
        have closed : Closed T := (aboveRef_node_none_iff topo r.id).mp closedTest
        refine ⟨List.prefix_refl St, canon, hr, ?_⟩
        rw [unfoldR, lift_of_closed closed, instantiateAt_of_closed closed]
      · rw [if_neg closedTest]
        have open_ : ¬ Closed T := not_closed_of_test topo closedTest
        by_cases jumped : d < r.shift
        · rw [if_pos jumped]
          refine ⟨List.prefix_refl St, canon, ⟨hr.valid, fun cl => absurd cl open_⟩, ?_⟩
          rw [unfold_shift topo, unfoldR]
          have := instantiateAt_lift_gt V 0 d r.shift jumped T
          simpa using this.symm
        · rw [if_neg jumped]
          have inside : Term.instantiateAt d V (Term.lift 0 r.shift T) =
              Term.lift 0 r.shift (Term.instantiateAt (d - r.shift) V T) := by
            have := instantiateAt_lift_le V 0 d r.shift (by omega) T
            simpa using this
          have varCase : T = .idx 0 →
              St <+: (if d = r.shift then (St, shiftRef St r.shift v) else (St, r)).1 ∧
              Canonical (if d = r.shift then (St, shiftRef St r.shift v) else (St, r)).1 ∧
              CanonRef (if d = r.shift then (St, shiftRef St r.shift v) else (St, r)).1
                (if d = r.shift then (St, shiftRef St r.shift v) else (St, r)).2 ∧
              unfold (if d = r.shift then (St, shiftRef St r.shift v) else (St, r)).1
                (if d = r.shift then (St, shiftRef St r.shift v) else (St, r)).2 =
                Term.instantiateAt d V (unfold St r) := by
            intro isVar
            by_cases same : d = r.shift
            · rw [if_pos same]
              obtain ⟨cr, eq⟩ := shiftRef_spec canon hv r.shift
              refine ⟨List.prefix_refl St, canon, cr, ?_⟩
              rw [eq, unfoldR, inside, isVar, same]
              simp [Term.instantiateAt, lift_zero, hV]
            · rw [if_neg same]
              refine ⟨List.prefix_refl St, canon, hr, ?_⟩
              rw [unfoldR, inside, isVar]
              have pos : 0 < d - r.shift := by omega
              simp [Term.instantiateAt, pos]
          cases hn : St[r.id]? with
          | none =>
              simp only
              exact varCase (by rw [hT]; exact tree_of_not_node (by intro _ _ e; rw [hn] at e; cases e))
          | some n =>
              cases n with
              | var =>
                  simp only
                  exact varCase (by rw [hT]; exact tree_of_not_node (by intro _ _ e; rw [hn] at e; cases e))
              | node head fields =>
                  simp only
                  have treeT : T = .node head (fieldsOf (unfold St) fields) := by
                    rw [hT, nodeTree_some hn]; rfl
                  have kids : ∀ x ∈ fields, CanonRef St x.2 := fun x mem =>
                    canon.childrenCanon _ _ hn x.2 (by simpa using ⟨x.1, mem⟩)
                  have below : ∀ x ∈ fields, x.2.id < fuel := fun x mem => by
                    have := canon.topo _ _ hn x.2 (by simpa using ⟨x.1, mem⟩); omega
                  obtain ⟨grow1, canon1, kids1, eq1⟩ := mapFields_spec
                    (fun St' c' r' => openF fuel St' c' v r') (fun c' t => Term.instantiateAt c' V t)
                    (fun c' fs => Term.Fields.instantiateAt c' V fs) (fun _ => rfl)
                    (fun _ _ _ _ => rfl) (fun x => x.id < fuel) (fun _ _ => True) St
                    (fun St' c' r' grow' canon' hr' ok' _ => by
                      have := openF_spec fuel St' c' v r' canon' (hv.prefix canon.topo grow') hr' ok'
                      rwa [unfold_prefix canon.topo grow' hv.valid] at this)
                    fields St (d - r.shift) (List.prefix_refl St) canon kids below
                    (fun _ _ => trivial)
                  set res := mapFields (fun St' c' r' => openF fuel St' c' v r') St (d - r.shift)
                    fields with hres
                  obtain ⟨grow2, canon2, cr2, eq2⟩ := mkNode_spec canon1 head kids1
                  obtain ⟨cr3, eq3⟩ := shiftRef_spec canon2 cr2 r.shift
                  refine ⟨grow1.trans grow2, canon2, cr3, ?_⟩
                  rw [eq3, eq2, eq1, unfoldR, inside, treeT]
                  rfl

/-- **Open a binder**: a reference for `instantiateAt d (unfold St v) (unfold St b)`. -/
def openRef [DecidableEq Head] (St : Store Head) (d : ℕ) (v b : Ref) : Store Head × Ref :=
  openF (b.id + 1) St d v b

theorem openRef_spec [DecidableEq Head] {St : Store Head} (canon : Canonical St) {v b : Ref}
    (hv : CanonRef St v) (hb : CanonRef St b) (d : ℕ) :
    St <+: (openRef St d v b).1 ∧ Canonical (openRef St d v b).1 ∧
      CanonRef (openRef St d v b).1 (openRef St d v b).2 ∧
      unfold (openRef St d v b).1 (openRef St d v b).2 =
        Term.instantiateAt d (unfold St v) (unfold St b) :=
  openF_spec _ St d v b canon hv hb (Nat.lt_succ_self _)

/-! ## Viewing a reference -/

/-- What a reference stands for, one level deep: an index, or a head with its fields. -/
inductive View (Head : Type) where
  | idx (n : ℕ)
  | node (head : Head) (fields : List (ℕ × Ref))

/-- **View a reference**: the edge's shift is pushed into the fields. -/
def view [DecidableEq Head] (St : Store Head) (r : Ref) : Store Head × View Head :=
  match St[r.id]? with
  | some (.node head fields) =>
      let res := mapFields (fun St' c x => liftRef St' c r.shift x) St 0 fields
      (res.1, .node head res.2)
  | _ => (St, .idx r.shift)

/-- What a view says about the tree. -/
def View.Shows (St : Store Head) (t : Term Head) : View Head → Prop
  | .idx n => t = .idx n
  | .node head fields => (∀ x ∈ fields, CanonRef St x.2) ∧ t = .node head (fieldsOf (unfold St) fields)

/-- **A view shows the tree, one level deep.** -/
theorem view_spec [DecidableEq Head] {St : Store Head} (canon : Canonical St) (r : Ref) :
    St <+: (view St r).1 ∧ Canonical (view St r).1 ∧ (view St r).2.Shows (view St r).1 (unfold St r) := by
  have topo := canon.topo
  have unfoldR : unfold St r = Term.lift 0 r.shift (nodeTree St r.id) := unfold_eq topo r
  unfold view
  cases hn : St[r.id]? with
  | none =>
      refine ⟨List.prefix_refl St, canon, ?_⟩
      show unfold St r = .idx r.shift
      rw [unfoldR, tree_of_not_node (by intro _ _ e; rw [hn] at e; cases e)]
      simp [Term.lift]
  | some n =>
      cases n with
      | var =>
          refine ⟨List.prefix_refl St, canon, ?_⟩
          show unfold St r = .idx r.shift
          rw [unfoldR, tree_of_not_node (by intro _ _ e; rw [hn] at e; cases e)]
          simp [Term.lift]
      | node head fields =>
          simp only
          have kids : ∀ x ∈ fields, CanonRef St x.2 := fun x mem =>
            canon.childrenCanon _ _ hn x.2 (by simpa using ⟨x.1, mem⟩)
          obtain ⟨grow1, canon1, kids1, eq1⟩ := mapFields_spec
            (fun St' c x => liftRef St' c r.shift x) (fun c t => Term.lift c r.shift t)
            (fun c fs => Term.Fields.lift c r.shift fs) (fun _ => rfl) (fun _ _ _ _ => rfl)
            (fun _ => True) (fun _ _ => True) []
            (fun St' c x _ canon' hx _ _ => liftRef_spec canon' hx c r.shift)
            fields St 0 List.nil_prefix canon kids (fun _ _ => trivial) (fun _ _ => trivial)
          refine ⟨grow1, canon1, kids1, ?_⟩
          rw [eq1, unfoldR, nodeTree_some hn]
          rfl

/-! ## Controls -/

namespace OperationControls

open SharingControls

/-- The body `(0 1)`: two free indices. -/
def body : Term H := app (.idx 0) (.idx 1)

/-- The store holding `idx 5` and then the body. -/
def St₀ : Store H := (encode (encode [] (.idx 5 : Term H)).1 body).1

def v₀ : Ref := (encode [] (.idx 5 : Term H)).2

def b₀ : Ref := (encode (encode [] (.idx 5 : Term H)).1 body).2

/-- Positive: opening index `0` of `(0 1)` with `5` gives `(5 0)`, and the result is the same
reference as encoding `(5 0)` directly: the opened term is shared with the stored one. -/
theorem open_example :
    (openRef St₀ 0 v₀ b₀).2 = (encode (openRef St₀ 0 v₀ b₀).1 (app (.idx 5) (.idx 0))).2 := by
  decide +kernel

/-- Positive: shifting the body by `3` changes only the edge: `(3 4)` is the body's node with
shift `3`. -/
theorem shift_example : shiftRef St₀ 3 b₀ = ⟨3, b₀.id⟩ := by decide +kernel

/-- Negative: the shifted body is not the body. -/
theorem shift_moves : shiftRef St₀ 3 b₀ ≠ b₀ := by decide +kernel

end OperationControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.SharedTerms
