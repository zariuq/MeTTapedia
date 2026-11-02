import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Build

/-!
# Operations on shared terms: weaken, view, open

Each operation works on references and the store, and computes exactly the tree operation on what
the references stand for.

* **Weakening is free** (`weakenRef_spec`): renaming what a reference stands for along any thinning
  of the surrounding scope only composes the reference's thinning. The store is not read or
  written. Shifting past the root, shifting under binders (`liftRef_spec`, which is `Term.lift c a`
  for every cutoff `c`), and moving variables apart are all this one operation.
* **Viewing is free** (`view_spec`): a reference's head and fields, each field's reference
  composed with the reference's thinning under the field's binders. Nothing is allocated, so
  matching (`Matching`) reads the store and never writes it.
* **Opening a binder** (`openRef_spec`): `openRef St d v b` stands for
  `instantiateAt d (unfold St v) (unfold St b)`; the value is shifted past the binders it crosses
  by weakening it. This is the shifting `open` the tier-0 kernel asked for (M7).
  **Cost**: a subterm that does not use the opened variable is not visited; the variable is only
  erased from its reference's thinning (`openRef_unused`). The walk enters only fields whose
  reference keeps the variable, and each node it rebuilds is one `mkNode`, which allocates at most
  one node (`mkNode_length_le`). So **opening allocates at most one node per node of the body on
  a path to an occurrence of the opened variable** (`openRef_length_le`, counted by `occNodes`).
  Shared subterms reached along several such paths are rebuilt once per path; memoizing by
  (node, thinning, depth) would bound the work by the number of distinct such triples.
* **Relevance is read off references** (`freeAt_placed`): the free variables of what a reference
  or an edge stands for are the kept positions of its thinning; an edge's first `d` bits say which
  of its `d` bound variables the body uses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Thin

variable {Head : Type}

/-! ## References placed in the store -/

/-- A reference is **placed** in the store when it points into it and keeps its node's support:
canonical references and the edges of stored nodes are placed. -/
structure Placed (St : Store Head) (r : Ref) : Prop where
  valid : r.id < St.length
  ones_eq : ones r.thin = supp St r.id

theorem CanonRef.placed {St : Store Head} {r : Ref} (hr : CanonRef St r) : Placed St r :=
  ⟨hr.valid, hr.ones_eq⟩

theorem Placed.prefix {St St' : Store Head} (grow : St <+: St') {r : Ref} (p : Placed St r) :
    Placed St' r :=
  ⟨lt_of_lt_of_le p.valid grow.length_le, by rw [supp_prefix grow p.valid]; exact p.ones_eq⟩

/-- The node of a placed reference is relevant at what the reference keeps. -/
theorem Placed.ok {St : Store Head} (canon : Canonical St) {r : Ref} (p : Placed St r) :
    (nodeC St r.id).ok (ones r.thin) = true := by
  rw [p.ones_eq]; exact nodeC_ok canon r.id p.valid

/-- An edge of a stored node is placed. -/
theorem placed_of_edge {St : Store Head} (canon : Canonical St) {i : ℕ} {hd : Head} {n : ℕ}
    {fs : List (ℕ × Ref)} (hn : St[i]? = some (.node hd n fs)) {x : ℕ × Ref} (mem : x ∈ fs) :
    Placed St x.2 := by
  obtain ⟨v, -, o⟩ := (canon.nodes i _ hn hd n fs rfl).1 x mem
  exact ⟨v, o⟩

/-! ## Weakening -/

/-- **Weaken a reference** along a thinning `ρ` of the surrounding scope: compose its thinning with
`ρ`, cut after the node's support. -/
def weakenRef (ρ : Thin) (r : Ref) : Ref := ⟨cut (ones r.thin) (comp r.thin ρ), r.id⟩

/-- **Weakening is free and correct**: it touches no store, gives a canonical reference, and
stands for the renamed tree. -/
theorem weakenRef_spec {St : Store Head} (canon : Canonical St) {r : Ref} (p : Placed St r)
    (ρ : Thin) :
    CanonRef St (weakenRef ρ r) ∧ unfold St (weakenRef ρ r) = rename ρ (unfold St r) := by
  have le := ones_le_ones_comp r.thin ρ
  refine ⟨⟨p.valid, trimmed_cut le, by simp only [weakenRef]; rw [ones_cut le]; exact p.ones_eq⟩, ?_⟩
  have rel := CTerm.relevant_toTree _ _ (p.ok canon)
  simp only [unfold, decode, unfoldC, weakenRef]
  rw [rename_comp]
  exact rename_congr_relevant rel fun j lt => sel_cut _ lt

/-- **Lifting under binders is weakening**: `Term.lift c a` at any cutoff, with no allocation. -/
def liftRef (c a : ℕ) (r : Ref) : Ref := weakenRef (keepN c (dropN a [])) r

theorem liftRef_spec {St : Store Head} (canon : Canonical St) {r : Ref} (p : Placed St r) (c a : ℕ) :
    CanonRef St (liftRef c a r) ∧ unfold St (liftRef c a r) = Term.lift c a (unfold St r) := by
  rw [lift_eq_rename]; exact weakenRef_spec canon p _

/-! ## Viewing a reference -/

/-- What a reference stands for, one level deep: a variable, or a head with its fields. -/
inductive View (Head : Type) where
  | idx (n : ℕ)
  | node (head : Head) (fields : List (ℕ × Ref))

/-- **View a reference**: each field's reference is the edge, weakened by the reference's thinning
under the field's binders. Nothing is allocated. -/
def view (St : Store Head) (r : Ref) : View Head :=
  match St[r.id]? with
  | some (.node h _ fs) => .node h (fs.map fun x => (x.1, weakenRef (keepN x.1 r.thin) x.2))
  | _ => .idx (sel r.thin 0)

/-- Binding-tree fields from references. -/
def fieldsOfRefs (St : Store Head) : List (ℕ × Ref) → Fields Head
  | [] => .nil
  | (d, r) :: rest => .cons d (unfold St r) (fieldsOfRefs St rest)

theorem fieldsOfRefs_congr {St St' : Store Head} :
    ∀ {fs : List (ℕ × Ref)}, (∀ x ∈ fs, unfold St x.2 = unfold St' x.2) →
      fieldsOfRefs St fs = fieldsOfRefs St' fs
  | [], _ => rfl
  | (d, r) :: rest, same => by
      simp only [fieldsOfRefs]
      rw [same (d, r) (by simp), fieldsOfRefs_congr fun x m => same x (by simp [m])]

theorem fieldsOfRefs_eq_fieldsOfThings (St : Store Head) :
    ∀ fs : List (ℕ × Ref), fieldsOfRefs St fs = fieldsOfThings (fs.map fun x => (x.1, unfoldC St x.2))
  | [] => rfl
  | (d, r) :: rest => by simp [fieldsOfRefs, fieldsOfThings, unfold, fieldsOfRefs_eq_fieldsOfThings St rest]

/-- What a view says about the tree. -/
def View.Shows (St : Store Head) (t : Term Head) : View Head → Prop
  | .idx n => t = .idx n
  | .node h fs => (∀ x ∈ fs, CanonRef St x.2) ∧ t = .node h (fieldsOfRefs St fs)

/-- The fields of a stored node seen through a reference's thinning: each edge's tree, renamed
under its binders. -/
def edgeFields (St : Store Head) (θ : Thin) : List (ℕ × Ref) → Fields Head
  | [] => .nil
  | (d, e) :: rest => .cons d (rename (keepN d θ) (unfold St e)) (edgeFields St θ rest)

/-- The tree of a reference to a stored node with fields: its edges' trees, renamed under their
binders. -/
theorem unfold_node {St : Store Head} (canon : Canonical St) {r : Ref} {h : Head} {n : ℕ}
    {fs : List (ℕ × Ref)} (hn : St[r.id]? = some (.node h n fs)) :
    unfold St r = .node h (edgeFields St r.thin fs) := by
  rw [unfold_eq, nodeTree, nodeC_node canon.topo hn]
  simp only [CTerm.toTree_node, rename_node]
  congr 1
  clear hn
  induction fs with
  | nil => simp [cfieldsOf, CFields.ofList, edgeFields]
  | cons x fs ih =>
      obtain ⟨d, e⟩ := x
      simp only [cfieldsOf, List.map_cons, CFields.ofList, CFields.toFields_cons, renameFields_cons,
        edgeFields] at ih ⊢
      rw [ih]
      rfl

/-- **A view shows the tree, one level deep**, and allocates nothing. -/
theorem view_spec {St : Store Head} (canon : Canonical St) (r : Ref) :
    (view St r).Shows St (unfold St r) := by
  unfold view
  cases hn : St[r.id]? with
  | none =>
      show unfold St r = .idx (sel r.thin 0)
      rw [unfold_eq, nodeTree, nodeC_eq canon.topo, hn]
      simp
  | some nd =>
      cases nd with
      | var =>
          show unfold St r = .idx (sel r.thin 0)
          rw [unfold_eq, nodeTree, nodeC_var canon.topo hn]
          simp
      | node h n fs =>
          refine ⟨fun x m => ?_, ?_⟩
          · obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
            exact (weakenRef_spec canon (placed_of_edge canon hn my) _).1
          · rw [unfold_node canon hn]
            congr 1
            have : ∀ l : List (ℕ × Ref), (∀ x ∈ l, Placed St x.2) →
                edgeFields St r.thin l =
                  fieldsOfRefs St (l.map fun x => (x.1, weakenRef (keepN x.1 r.thin) x.2)) := by
              intro l hl
              induction l with
              | nil => rfl
              | cons x l ih =>
                  obtain ⟨d, e⟩ := x
                  simp only [edgeFields, List.map_cons, fieldsOfRefs]
                  rw [ih fun y m => hl y (by simp [m]),
                    (weakenRef_spec canon (hl (d, e) (by simp)) _).2]
            exact this fs fun x m => placed_of_edge canon hn m

/-! ## Rebuilding fields, generically -/

/-- Rebuild a list of fields through `g`, which may grow the store; each field is visited at the
depth past its binders. -/
def mapFields (g : Store Head → ℕ → Ref → Store Head × Ref) :
    Store Head → ℕ → List (ℕ × Ref) → Store Head × List (ℕ × Ref)
  | St, _, [] => (St, [])
  | St, c, (d, r) :: rest =>
      let first := g St (c + d) r
      let others := mapFields g first.1 c rest
      (others.1, (d, first.2) :: others.2)

/-- **Rebuilding fields is correct when rebuilding each field is.** -/
theorem mapFields_spec (g : Store Head → ℕ → Ref → Store Head × Ref) (F : ℕ → Term Head → Term Head)
    (Fm : ℕ → Fields Head → Fields Head) (Fm_nil : ∀ c, Fm c .nil = .nil)
    (Fm_cons : ∀ c d t rest, Fm c (.cons d t rest) = .cons d (F (c + d) t) (Fm c rest))
    (ok : Ref → Prop) (base : Store Head)
    (hg : ∀ St c r, base <+: St → Canonical St → CanonRef St r → ok r →
        St <+: (g St c r).1 ∧ Canonical (g St c r).1 ∧ CanonRef (g St c r).1 (g St c r).2 ∧
          unfold (g St c r).1 (g St c r).2 = F c (unfold St r)) :
    ∀ (fs : List (ℕ × Ref)) (St : Store Head) (c : ℕ), base <+: St → Canonical St →
      (∀ x ∈ fs, CanonRef St x.2) → (∀ x ∈ fs, ok x.2) →
      St <+: (mapFields g St c fs).1 ∧ Canonical (mapFields g St c fs).1 ∧
        (∀ x ∈ (mapFields g St c fs).2, CanonRef (mapFields g St c fs).1 x.2) ∧
        fieldsOfRefs (mapFields g St c fs).1 (mapFields g St c fs).2 = Fm c (fieldsOfRefs St fs)
  | [], St, c, _, canon, _, _ => by
      refine ⟨List.prefix_refl St, canon, by simp [mapFields], ?_⟩
      simp [mapFields, fieldsOfRefs, Fm_nil]
  | (d, r) :: rest, St, c, hb, canon, kids, oks => by
      have hr : CanonRef St r := kids (d, r) (by simp)
      obtain ⟨grow1, canon1, cr1, eq1⟩ := hg St (c + d) r hb canon hr (oks (d, r) (by simp))
      have kids1 : ∀ x ∈ rest, CanonRef (g St (c + d) r).1 x.2 :=
        fun x mem => (kids x (by simp [mem])).prefix grow1
      obtain ⟨grow2, canon2, cr2, eq2⟩ := mapFields_spec g F Fm Fm_nil Fm_cons ok base hg rest
        (g St (c + d) r).1 c (hb.trans grow1) canon1 kids1 (fun x mem => oks x (by simp [mem]))
      refine ⟨grow1.trans grow2, canon2, ?_, ?_⟩
      · intro x mem
        simp only [mapFields, List.mem_cons] at mem
        rcases mem with rfl | mem
        · exact cr1.prefix grow2
        · exact cr2 x mem
      · simp only [mapFields, fieldsOfRefs, Fm_cons]
        rw [unfold_prefix canon1.topo grow2 cr1.valid, eq1, eq2,
          fieldsOfRefs_congr fun x mem => unfold_prefix canon.topo grow1 (kids x (by simp [mem])).valid]

/-! ## Opening a binder -/

/-- `openF fuel St d v b`: a reference for `instantiateAt d (unfold St v) (unfold St b)`. -/
def openF [DecidableEq Head] : ℕ → Store Head → ℕ → Ref → Ref → Store Head × Ref
  | 0, St, _, _, b => (St, b)
  | fuel + 1, St, d, v, b =>
      if bit b.thin d = false then (St, ⟨erase d b.thin, b.id⟩)
      else match St[b.id]? with
        | some (.node h _ fs) =>
            let res := mapFields (fun St' d' x => openF fuel St' d' v x) St d
              (fs.map fun x => (x.1, weakenRef (keepN x.1 b.thin) x.2))
            mkNode res.1 h res.2
        | _ => (St, weakenRef (dropN d []) v)

/-- `mkNode`'s reference stands for the node over its fields' trees. -/
theorem mkNode_unfold [DecidableEq Head] {St : Store Head} (canon : Canonical St) (h : Head)
    {fs : List (ℕ × Ref)} (kids : ∀ x ∈ fs, CanonRef St x.2) :
    unfold (mkNode St h fs).1 (mkNode St h fs).2 = .node h (fieldsOfRefs St fs) := by
  obtain ⟨-, -, -, eq⟩ := mkNode_spec canon h kids
  rw [unfold, eq, (mkNodeR_spec h fun x m => ?_).2, fieldsOfRefs_eq_fieldsOfThings]
  obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
  exact canon_unfoldC canon (kids y my)

theorem openF_spec [DecidableEq Head] : ∀ (fuel : ℕ) (St : Store Head) (d : ℕ) (v b : Ref),
    Canonical St → CanonRef St v → CanonRef St b → b.id < fuel →
    St <+: (openF fuel St d v b).1 ∧ Canonical (openF fuel St d v b).1 ∧
      CanonRef (openF fuel St d v b).1 (openF fuel St d v b).2 ∧
      unfold (openF fuel St d v b).1 (openF fuel St d v b).2 =
        Term.instantiateAt d (unfold St v) (unfold St b)
  | 0, _, _, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, St, d, v, b, canon, hv, hb, h => by
      have rel := CTerm.relevant_toTree _ _ (hb.placed.ok canon)
      simp only [openF]
      by_cases unused : bit b.thin d = false
      · rw [if_pos unused]
        refine ⟨List.prefix_refl St, canon, ⟨hb.valid, trimmed_erase hb.trim unused, ?_⟩, ?_⟩
        · simp only; rw [ones_erase unused]; exact hb.ones_eq
        · simp only [unfold, decode, unfoldC]
          exact (instantiateAt_rename_unused rel unused _).symm
      · rw [if_neg unused]
        have used : bit b.thin d = true := by simpa using unused
        have varCase : nodeC St b.id = .var →
            St <+: St ∧ Canonical St ∧ CanonRef St (weakenRef (dropN d []) v) ∧
              unfold St (weakenRef (dropN d []) v) = Term.instantiateAt d (unfold St v) (unfold St b) := by
          intro isVar
          have ones1 : ones b.thin = 1 := by
            have := hb.placed.ok canon
            rw [isVar, CTerm.ok_var, decide_eq_true_eq] at this
            exact this
          obtain ⟨j, lt, sj⟩ := exists_sel_of_bit used
          have j0 : j = 0 := by omega
          subst j0
          obtain ⟨cr, eq⟩ := weakenRef_spec canon hv.placed (dropN d [])
          refine ⟨List.prefix_refl St, canon, cr, ?_⟩
          rw [eq, unfold_eq St b, nodeTree, isVar, CTerm.toTree_var, instantiateAt_rename_var sj]
        cases hn : St[b.id]? with
        | none =>
            simp only
            exact varCase (by rw [nodeC_eq canon.topo, hn]; rfl)
        | some nd =>
            cases nd with
            | var =>
                simp only
                exact varCase (nodeC_var canon.topo hn)
            | node hd n fs =>
                simp only
                have edges : ∀ x ∈ fs, Placed St x.2 := fun x m => placed_of_edge canon hn m
                have below : ∀ x ∈ fs, x.2.id < fuel := fun x m => by
                  have := canon.topo _ _ hn x.2 (by simpa using ⟨x.1, m⟩); omega
                set fs' := fs.map fun x => (x.1, weakenRef (keepN x.1 b.thin) x.2) with hfs'
                have kids : ∀ x ∈ fs', CanonRef St x.2 := fun x m => by
                  obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
                  exact (weakenRef_spec canon (edges y my) _).1
                have oks : ∀ x ∈ fs', x.2.id < fuel := fun x m => by
                  obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
                  exact below y my
                obtain ⟨grow1, canon1, kids1, eq1⟩ := mapFields_spec
                  (fun St' d' x => openF fuel St' d' v x) (fun c t => Term.instantiateAt c (unfold St v) t)
                  (fun c fs => Term.Fields.instantiateAt c (unfold St v) fs) (fun _ => rfl)
                  (fun _ _ _ _ => rfl) (fun x => x.id < fuel) St
                  (fun St' c x grow' canon' hx ok' => by
                    have := openF_spec fuel St' c v x canon' (hv.prefix grow') hx ok'
                    rwa [unfold_prefix canon.topo grow' hv.valid] at this)
                  fs' St d (List.prefix_refl St) canon kids oks
                obtain ⟨grow2, canon2, cr2, -⟩ := mkNode_spec canon1 hd kids1
                refine ⟨grow1.trans grow2, canon2, cr2, ?_⟩
                rw [mkNode_unfold canon1 hd kids1, eq1]
                have shows := view_spec canon b
                simp only [view, hn] at shows
                rw [shows.2]
                rfl

/-- **Open a binder**: a reference for `instantiateAt d (unfold St v) (unfold St b)`. -/
def openRef [DecidableEq Head] (St : Store Head) (d : ℕ) (v b : Ref) : Store Head × Ref :=
  openF (b.id + 1) St d v b

/-- **Opening is correct**: the store grows and stays canonical, and the reference stands for the
opened tree, the value shifted past the binders it crosses. -/
theorem openRef_spec [DecidableEq Head] {St : Store Head} (canon : Canonical St) {v b : Ref}
    (hv : CanonRef St v) (hb : CanonRef St b) (d : ℕ) :
    St <+: (openRef St d v b).1 ∧ Canonical (openRef St d v b).1 ∧
      CanonRef (openRef St d v b).1 (openRef St d v b).2 ∧
      unfold (openRef St d v b).1 (openRef St d v b).2 =
        Term.instantiateAt d (unfold St v) (unfold St b) :=
  openF_spec _ St d v b canon hv hb (Nat.lt_succ_self _)

/-- **Opening a variable the body does not use costs one bit operation**: the store is unchanged,
the node is the same, and only the variable's position is erased from the reference's thinning. -/
theorem openRef_unused [DecidableEq Head] (St : Store Head) (d : ℕ) (v b : Ref)
    (unused : bit b.thin d = false) : openRef St d v b = (St, ⟨erase d b.thin, b.id⟩) := by
  simp [openRef, openF, unused]

/-- Opening a closed body changes nothing. -/
theorem openRef_closed [DecidableEq Head] (St : Store Head) (d : ℕ) (v : Ref) (i : ℕ) :
    openRef St d v ⟨[], i⟩ = (St, ⟨[], i⟩) := by
  simp [openRef_unused St d v ⟨[], i⟩ (by simp)]

/-! ## The cost of opening -/

mutual

/-- `occNodes d t`: the nodes of `t` on a path from its root to an occurrence of the free variable
`d`, counted once per path. A subtree in which `d` is not free counts nothing. -/
def occNodes : ℕ → Term Head → ℕ
  | _, .idx _ => 0
  | d, .node _ fs => if fieldsFreeAt fs d then occNodesFields d fs + 1 else 0

def occNodesFields : ℕ → Fields Head → ℕ
  | _, .nil => 0
  | d, .cons k t rest => occNodes (d + k) t + occNodesFields d rest

end

theorem occNodesFields_fieldsOfRefs (St : Store Head) (d : ℕ) :
    ∀ l : List (ℕ × Ref),
      occNodesFields d (fieldsOfRefs St l) = (l.map fun x => occNodes (d + x.1) (unfold St x.2)).sum
  | [] => by simp [fieldsOfRefs, occNodesFields]
  | (k, r) :: rest => by
      simp [fieldsOfRefs, occNodesFields, occNodesFields_fieldsOfRefs St d rest]

/-- Rebuilding fields grows the store by at most the sum of what rebuilding each field may add. -/
theorem mapFields_length_le (g : Store Head → ℕ → Ref → Store Head × Ref)
    (B : ℕ → Term Head → ℕ) (ok : Ref → Prop) (base : Store Head)
    (hg : ∀ St c r, base <+: St → Canonical St → CanonRef St r → ok r →
        St <+: (g St c r).1 ∧ Canonical (g St c r).1 ∧
          (g St c r).1.length ≤ St.length + B c (unfold St r)) :
    ∀ (fs : List (ℕ × Ref)) (St : Store Head) (c : ℕ), base <+: St → Canonical St →
      (∀ x ∈ fs, CanonRef St x.2) → (∀ x ∈ fs, ok x.2) →
      (mapFields g St c fs).1.length ≤ St.length + (fs.map fun x => B (c + x.1) (unfold St x.2)).sum
  | [], St, c, _, _, _, _ => by simp [mapFields]
  | (d, r) :: rest, St, c, hb, canon, kids, oks => by
      have hr : CanonRef St r := kids (d, r) (by simp)
      obtain ⟨grow1, canon1, len1⟩ := hg St (c + d) r hb canon hr (oks (d, r) (by simp))
      have kids1 : ∀ x ∈ rest, CanonRef (g St (c + d) r).1 x.2 :=
        fun x mem => (kids x (by simp [mem])).prefix grow1
      have len2 := mapFields_length_le g B ok base hg rest (g St (c + d) r).1 c (hb.trans grow1)
        canon1 kids1 (fun x mem => oks x (by simp [mem]))
      have same : (rest.map fun x => B (c + x.1) (unfold (g St (c + d) r).1 x.2)) =
          rest.map fun x => B (c + x.1) (unfold St x.2) :=
        List.map_congr_left fun x mem => by
          rw [unfold_prefix canon.topo grow1 (kids x (by simp [mem])).valid]
      rw [same] at len2
      simp only [mapFields, List.map_cons, List.sum_cons]
      omega

theorem openF_length_le [DecidableEq Head] : ∀ (fuel : ℕ) (St : Store Head) (d : ℕ) (v b : Ref),
    Canonical St → CanonRef St v → CanonRef St b → b.id < fuel →
    (openF fuel St d v b).1.length ≤ St.length + occNodes d (unfold St b)
  | 0, _, _, _, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, St, d, v, b, canon, hv, hb, h => by
      simp only [openF]
      by_cases unused : bit b.thin d = false
      · rw [if_pos unused]; simp
      · rw [if_neg unused]
        have used : bit b.thin d = true := by simpa using unused
        cases hn : St[b.id]? with
        | none => simp
        | some nd =>
            cases nd with
            | var => simp
            | node hd n fs =>
                simp only
                have edges : ∀ x ∈ fs, Placed St x.2 := fun x m => placed_of_edge canon hn m
                have below : ∀ x ∈ fs, x.2.id < fuel := fun x m => by
                  have := canon.topo _ _ hn x.2 (by simpa using ⟨x.1, m⟩); omega
                set fs' := fs.map fun x => (x.1, weakenRef (keepN x.1 b.thin) x.2) with hfs'
                have kids : ∀ x ∈ fs', CanonRef St x.2 := fun x m => by
                  obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
                  exact (weakenRef_spec canon (edges y my) _).1
                have oks : ∀ x ∈ fs', x.2.id < fuel := fun x m => by
                  obtain ⟨y, my, rfl⟩ := List.mem_map.mp m
                  exact below y my
                have len1 := mapFields_length_le (fun St' d' x => openF fuel St' d' v x)
                  (fun c t => occNodes c t) (fun x => x.id < fuel) St
                  (fun St' c x grow' canon' hx ok' => by
                    have hv' := hv.prefix grow'
                    obtain ⟨g1, c1, -, -⟩ := openF_spec fuel St' c v x canon' hv' hx ok'
                    exact ⟨g1, c1, openF_length_le fuel St' c v x canon' hv' hx ok'⟩)
                  fs' St d (List.prefix_refl St) canon kids oks
                have len2 := mkNode_length_le
                  (mapFields (fun St' d' x => openF fuel St' d' v x) St d fs').1 hd
                  (mapFields (fun St' d' x => openF fuel St' d' v x) St d fs').2
                have shows := view_spec canon b
                simp only [view, hn] at shows
                have free : freeAt (unfold St b) d = true := by rw [freeAt_unfold canon hb]; exact used
                rw [shows.2] at free ⊢
                simp only [freeAt_node] at free
                simp only [occNodes, free, if_true, occNodesFields_fieldsOfRefs]
                rw [← hfs']
                omega

/-- **The cost of opening**: opening variable `d` of `b` allocates at most one node for each node
of `b`'s tree on a path from its root to an occurrence of `d` (`occNodes`). Subterms in which `d`
is not free cost nothing; when `d` is not free in `b` at all, nothing is allocated. -/
theorem openRef_length_le [DecidableEq Head] {St : Store Head} (canon : Canonical St) {v b : Ref}
    (hv : CanonRef St v) (hb : CanonRef St b) (d : ℕ) :
    (openRef St d v b).1.length ≤ St.length + occNodes d (unfold St b) :=
  openF_length_le _ St d v b canon hv hb (Nat.lt_succ_self _)

/-! ## Relevance read off references and edges -/

/-- **The free variables of what a placed reference stands for are the kept positions of its
thinning.** For an edge of a stored node, the first `d` bits say exactly which of the field's `d`
bound variables its body uses: a vacuous binder is visible at the binder, with no walk. -/
theorem freeAt_placed {St : Store Head} (canon : Canonical St) {r : Ref} (p : Placed St r) (i : ℕ) :
    freeAt (unfold St r) i = bit r.thin i :=
  freeAt_rename_relevant (CTerm.relevant_toTree _ _ (p.ok canon)) i

/-! ## Controls -/

namespace OperationControls

open SharingControls

/-- The body `(0 1)`: two free variables. -/
def body : Term H := app (.idx 0) (.idx 1)

/-- The store holding `idx 5`, then the body. -/
def St₀ : Store H := (encodeR (encodeR [] (.idx 5 : Term H)).1 body).1

def v₀ : Ref := (encodeR [] (.idx 5 : Term H)).2

def b₀ : Ref := (encodeR (encodeR [] (.idx 5 : Term H)).1 body).2

/-- Positive: opening variable `0` of `(0 1)` with `5` gives `(5 0)`, and the result is the same
reference as encoding `(5 0)` directly. -/
theorem open_example :
    (openRef St₀ 0 v₀ b₀).2 = (encodeR (openRef St₀ 0 v₀ b₀).1 (app (.idx 5) (.idx 0))).2 := by
  decide +kernel

/-- Positive: opening variable `3`, which the body does not use, only edits the thinning: the
body's variable `1` moves down past nothing, since `3` is above it, and the store is unchanged. -/
theorem open_unused_example : openRef St₀ 3 v₀ b₀ = (St₀, b₀) := by decide +kernel

/-- Positive: weakening the body by any thinning edits only its reference. -/
theorem weaken_example : weakenRef [false, true, false, true] b₀ = ⟨[false, true, false, true], b₀.id⟩ := by
  decide +kernel

/-- Negative: the weakened body is not the body. -/
theorem weaken_moves : weakenRef [false, true] b₀ ≠ b₀ := by decide +kernel

end OperationControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
