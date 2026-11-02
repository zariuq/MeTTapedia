import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Store

/-!
# Building shared terms in a canonical store

Every operation takes a store and returns a larger one with a reference; the old store is a
prefix of the new one, so every old reference keeps its meaning (`unfold_prefix`).

* `mkNode St h fields`: the canonical reference for the node `h` over the fields' references
  (`mkNode_spec`). It computes the node's support as the union of the children's outer variables,
  each edge by pulling back along it, and interns **one** node: it does not visit the children
  (`mkNode_length_le`). It is the store form of the smart constructor `mkNodeR`.
* `encodeR St t`: the canonical reference for any tree; it stands for the tree's code
  (`encodeR_spec`). **Two trees are equal exactly when encoding them into one store gives one
  reference** (`encodeR_eq_iff`).

**Sharing does not depend on the context.** A stored node is a term's co-de-Bruijn form: the
term with its free variables numbered densely in order. So any two places in the store (canonical
references, or edges of stored nodes) point to one node exactly when their trees have the same
code (`same_node_iff`), in particular when one tree is a renaming of the other along a thinning
(`renamed_one_node`): weakened, placed under more binders, or with its variables at other
positions of the scope, in the same order. **A closed subterm is one node wherever it occurs**
(`closed_one_node`).

Examples (`SharingControls`): `λ. (0 1)` and `λ. (0 2)` are one node with nothing left unused
(the shifts store leaves one unused node here); `(x z)` and `(x y)` are one node; `(x z)` and
`(z x)` are two.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Thin

variable {Head : Type}

/-! ## Covers made by the smart constructor -/

/-- **The edges of the smart constructor cover the union**: reading each field's outer variables
in the union of all of them, every variable of the union is used by some field. -/
theorem bors_back_edges (fs : List (ℕ × Thin)) :
    bors (fs.map fun x => back x.1 (edge x.1 (bors (fs.map fun x => back x.1 x.2)) x.2)) =
      idn (ones (bors (fs.map fun x => back x.1 x.2))) := by
  set U := bors (fs.map fun x => back x.1 x.2) with hU
  refine bors_eq_idn (fun θ m => ?_) (fun j lt => ?_) (fun e => ?_)
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp m
    simp [back_edge]
  · have hb := (bit_sel lt).1
    rw [hU, bit_bors] at hb
    obtain ⟨φ, mφ, hφ⟩ := hb
    obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mφ
    refine ⟨back x.1 (edge x.1 U x.2), List.mem_map.mpr ⟨x, mx, rfl⟩, ?_⟩
    rw [back_edge, bit_pull _ lt]
    exact hφ
  · have : fs = [] := by simpa using e
    subst this
    simp [hU, bors]

theorem sub_bors {l : List (ℕ × Thin)} {x : ℕ × Thin} (mem : x ∈ l) :
    Sub (back x.1 x.2) (bors (l.map fun x => back x.1 x.2)) := by
  intro i hi
  rw [bit_bors]
  exact ⟨_, List.mem_map_of_mem mem, hi⟩

/-! ## Making a node -/

/-- **The canonical reference for a node** over the fields' canonical references: the support is
the union of the children's outer variables; each edge is the child's thinning with its outer
bits read in that union. One node is interned; the children are not visited. -/
def mkNode [DecidableEq Head] (St : Store Head) (h : Head) (fs : List (ℕ × Ref)) : Store Head × Ref :=
  let U := bors (fs.map fun x => back x.1 x.2.thin)
  let got := intern St (.node h (ones U) (fs.map fun x => (x.1, ⟨edge x.1 U x.2.thin, x.2.id⟩)))
  (got.1, ⟨U, got.2⟩)

/-- **Making a node allocates at most one node.** -/
theorem mkNode_length_le [DecidableEq Head] (St : Store Head) (h : Head) (fs : List (ℕ × Ref)) :
    (mkNode St h fs).1.length ≤ St.length + 1 :=
  intern_length_le _ _

/-- **`mkNode` is correct**: it keeps the store canonical, and its reference stands for the smart
constructor's thing over the fields' things. -/
theorem mkNode_spec [DecidableEq Head] {St : Store Head} (canon : Canonical St) (h : Head)
    {fs : List (ℕ × Ref)} (kids : ∀ x ∈ fs, CanonRef St x.2) :
    St <+: (mkNode St h fs).1 ∧ Canonical (mkNode St h fs).1 ∧
      CanonRef (mkNode St h fs).1 (mkNode St h fs).2 ∧
      unfoldC (mkNode St h fs).1 (mkNode St h fs).2 = mkNodeR h (fs.map fun x => (x.1, unfoldC St x.2)) := by
  simp only [mkNode]
  set U := bors (fs.map fun x => back x.1 x.2.thin) with hU
  set nd : Node Head := .node h (ones U) (fs.map fun x => (x.1, ⟨edge x.1 U x.2.thin, x.2.id⟩)) with hnd
  have pairs : (fs.map fun x => (x.1, x.2.thin)).map (fun x => back x.1 x.2) =
      fs.map fun x => back x.1 x.2.thin := by simp [Function.comp]
  have subs : ∀ x ∈ fs, Sub (back x.1 x.2.thin) U := by
    intro x mx
    have := sub_bors (l := fs.map fun x => (x.1, x.2.thin)) (List.mem_map_of_mem mx)
    rwa [pairs] at this
  have ok : NodeOk St nd := by
    intro h' n' fs' e
    simp only [hnd, Node.node.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    refine ⟨fun y my => ?_, ?_⟩
    · obtain ⟨x, mx, rfl⟩ := List.mem_map.mp my
      exact ⟨(kids x mx).valid, length_edge _ _ _, by rw [ones_edge (subs x mx)]; exact (kids x mx).ones_eq⟩
    · have := bors_back_edges (fs.map fun x => (x.1, x.2.thin))
      simp only [List.map_map, Function.comp_def] at this ⊢
      exact this
  have canon2 := intern_canonical canon ok
  have grow := intern_prefix St nd
  have got := intern_get St nd
  refine ⟨grow, canon2, ⟨intern_valid St nd, ?_, ?_⟩, ?_⟩
  · exact trimmed_bors fun θ m => by
      obtain ⟨x, mx, rfl⟩ := List.mem_map.mp m
      exact trimmed_back (kids x mx).trim _
  · show ones U = supp (intern St nd).1 (intern St nd).2
    unfold supp
    rw [got]
  · have got' : (intern St nd).1[(intern St nd).2]? =
        some (.node h (ones U) (fs.map fun x => (x.1, ⟨edge x.1 U x.2.thin, x.2.id⟩))) := got
    have supportEq : supportOf (fs.map fun x => (x.1, unfoldC St x.2)) = U := by
      simp [supportOf, unfoldC, hU, Function.comp_def]
    show (U, nodeC (intern St nd).1 (intern St nd).2) = mkNodeR h (fs.map fun x => (x.1, unfoldC St x.2))
    rw [mkNodeR, supportEq, nodeC_node canon2.topo got']
    congr 2
    simp only [cfieldsOf, List.map_map, Function.comp_def, unfoldC]
    congr 1
    refine List.map_congr_left fun x mx => ?_
    rw [nodeC_prefix canon.topo grow (kids x mx).valid]

/-! ## Encoding trees -/

mutual

/-- **The canonical reference for a tree**, built bottom-up. -/
def encodeR [DecidableEq Head] : Store Head → Term Head → Store Head × Ref
  | St, .idx k =>
      let got := intern St .var
      (got.1, ⟨dropN k [true], got.2⟩)
  | St, .node h fs =>
      let res := encodeFieldsR St fs
      mkNode res.1 h res.2

def encodeFieldsR [DecidableEq Head] : Store Head → Fields Head → Store Head × List (ℕ × Ref)
  | St, .nil => (St, [])
  | St, .cons d t rest =>
      let first := encodeR St t
      let others := encodeFieldsR first.1 rest
      (others.1, (d, first.2) :: others.2)

end

theorem nodeOk_var (St : Store Head) : NodeOk St .var := by
  intro h n fs e; cases e

mutual

/-- **Encoding is correct**: the store stays canonical and the reference stands for the tree's
code. -/
theorem encodeR_spec [DecidableEq Head] (St : Store Head) (canon : Canonical St) (t : Term Head) :
    St <+: (encodeR St t).1 ∧ Canonical (encodeR St t).1 ∧ CanonRef (encodeR St t).1 (encodeR St t).2 ∧
      unfoldC (encodeR St t).1 (encodeR St t).2 = encode t := by
  cases t with
  | idx k =>
      simp only [encodeR]
      have canon2 := intern_canonical canon (nodeOk_var St)
      have got := intern_get St (.var : Node Head)
      refine ⟨intern_prefix St _, canon2, ⟨intern_valid St _, trimmed_dropN_true k, ?_⟩, ?_⟩
      · simp [supp, got]
      · simp [unfoldC, encode, varR, nodeC_var canon2.topo got]
  | node h fs =>
      simp only [encodeR]
      obtain ⟨grow1, canon1, kids1, eq1⟩ := encodeFieldsR_spec St canon fs
      obtain ⟨grow2, canon2, cr2, eq2⟩ := mkNode_spec canon1 h kids1
      exact ⟨grow1.trans grow2, canon2, cr2, by rw [eq2, eq1]; rfl⟩

theorem encodeFieldsR_spec [DecidableEq Head] (St : Store Head) (canon : Canonical St)
    (fs : Fields Head) :
    St <+: (encodeFieldsR St fs).1 ∧ Canonical (encodeFieldsR St fs).1 ∧
      (∀ x ∈ (encodeFieldsR St fs).2, CanonRef (encodeFieldsR St fs).1 x.2) ∧
      (encodeFieldsR St fs).2.map (fun x => (x.1, unfoldC (encodeFieldsR St fs).1 x.2)) =
        encodeFields fs := by
  cases fs with
  | nil => exact ⟨List.prefix_refl St, canon, by simp [encodeFieldsR], by simp [encodeFieldsR, encodeFields]⟩
  | cons d t rest =>
      simp only [encodeFieldsR]
      obtain ⟨grow1, canon1, cr1, eq1⟩ := encodeR_spec St canon t
      obtain ⟨grow2, canon2, kids2, eq2⟩ := encodeFieldsR_spec (encodeR St t).1 canon1 rest
      refine ⟨grow1.trans grow2, canon2, ?_, ?_⟩
      · intro x mem
        simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · exact cr1.prefix grow2
        · exact kids2 x mem
      · simp only [List.map_cons, encodeFields]
        rw [unfoldC_prefix canon1.topo grow2 cr1.valid, eq1, eq2]

end

/-- **What `encodeR` returns stands for the tree.** -/
theorem encodeR_unfold [DecidableEq Head] {St : Store Head} (canon : Canonical St) (t : Term Head) :
    unfold (encodeR St t).1 (encodeR St t).2 = t := by
  rw [unfold, (encodeR_spec St canon t).2.2.2]
  exact (encode_spec t).2

/-- **Two trees are equal exactly when encoding them into one store gives one reference.** Trees
carry no bound names, so this is alpha-equivalence decided by pointer equality. -/
theorem encodeR_eq_iff [DecidableEq Head] {St : Store Head} (canon : Canonical St) (s t : Term Head) :
    s = t ↔ (encodeR St s).2 = (encodeR (encodeR St s).1 t).2 := by
  obtain ⟨grow1, canon1, cr1, -⟩ := encodeR_spec St canon s
  obtain ⟨grow2, canon2, cr2, -⟩ := encodeR_spec (encodeR St s).1 canon1 t
  rw [← unfold_eq_iff canon2 (cr1.prefix grow2) cr2, encodeR_unfold canon1,
    unfold_prefix canon1.topo grow2 cr1.valid, encodeR_unfold canon]

/-! ## Sharing does not depend on the context -/

/-- `x` **occurs** in the store: it is a canonical reference, or an edge of a stored node. -/
def Occurs (St : Store Head) (x : Ref) : Prop :=
  CanonRef St x ∨ ∃ (i : ℕ) (hd : Head) (n : ℕ) (fs : List (ℕ × Ref)) (d : ℕ),
    St[i]? = some (.node hd n fs) ∧ (d, x) ∈ fs

theorem Occurs.valid {St : Store Head} (canon : Canonical St) {x : Ref} (occ : Occurs St x) :
    x.id < St.length ∧ ones x.thin = supp St x.id := by
  rcases occ with cr | ⟨i, hd, n, fs, d, hn, mem⟩
  · exact ⟨cr.valid, cr.ones_eq⟩
  · obtain ⟨v, -, o⟩ := (canon.nodes i _ hn hd n fs rfl).1 (d, x) mem
    exact ⟨v, o⟩

/-- A composite keeps at least the variables of its first thinning. -/
theorem ones_le_ones_comp (θ φ : Thin) : ones θ ≤ ones (comp θ φ) := by
  induction φ generalizing θ with
  | nil => simp
  | cons b φ ih =>
      cases b with
      | false => simpa using ih θ
      | true =>
          cases θ with
          | nil => simp
          | cons a θ => cases a <;> simp [ih θ]

/-- **The code of a renamed relevant term**: its thinning, cut after the term's support, and the
term itself. -/
theorem encode_rename {θ : Thin} {c : CTerm Head} (ok : c.ok (ones θ) = true) :
    encode (rename θ c.toTree) = (cut (ones θ) θ, c) := by
  have rel := CTerm.relevant_toTree c _ ok
  have same : rename θ c.toTree = decode (cut (ones θ) θ, c) := by
    simp only [decode]
    exact rename_congr_relevant rel fun j lt => (sel_cut θ lt).symm
  rw [same]
  exact encode_decode ⟨trimmed_cut (le_refl _), by simp only; rw [ones_cut (le_refl _)]; exact ok⟩

/-- **The node of an occurrence is the code of its tree.** -/
theorem code_unfold {St : Store Head} (canon : Canonical St) {x : Ref} (occ : Occurs St x) :
    (encode (unfold St x)).2 = nodeC St x.id := by
  obtain ⟨valid, onesEq⟩ := occ.valid canon
  have ok := nodeC_ok canon x.id valid
  rw [← onesEq] at ok
  simp only [unfold, decode, unfoldC]
  rw [encode_rename ok]

/-- **Two occurrences share a node exactly when their trees have one code.** -/
theorem same_node_iff {St : Store Head} (canon : Canonical St) {x x' : Ref} (occ : Occurs St x)
    (occ' : Occurs St x') : x.id = x'.id ↔ (encode (unfold St x)).2 = (encode (unfold St x')).2 := by
  rw [code_unfold canon occ, code_unfold canon occ']
  constructor
  · intro e; rw [e]
  · exact nodeC_inj canon (occ.valid canon).1 (occ'.valid canon).1

/-- **A term and any renaming of it are one node**: wherever two occurrences stand for trees
that differ by a thinning (more binders around, a weakening, the variables at other positions of
the scope in the same order), they point to the same node. -/
theorem renamed_one_node {St : Store Head} (canon : Canonical St) {x x' : Ref} (occ : Occurs St x)
    (occ' : Occurs St x') {ρ : Thin} (renamed : unfold St x' = rename ρ (unfold St x)) : x'.id = x.id := by
  refine nodeC_inj canon (occ'.valid canon).1 (occ.valid canon).1 ?_
  rw [← code_unfold canon occ', ← code_unfold canon occ, renamed]
  obtain ⟨valid, onesEq⟩ := occ.valid canon
  have ok := nodeC_ok canon x.id valid
  rw [← onesEq] at ok
  have rel := CTerm.relevant_toTree _ _ ok
  have le := ones_le_ones_comp x.thin ρ
  have cutOk : (nodeC St x.id).ok (ones (cut (ones x.thin) (comp x.thin ρ))) = true := by
    rw [ones_cut le]; exact ok
  have eq : rename ρ (unfold St x) = rename (cut (ones x.thin) (comp x.thin ρ)) (nodeC St x.id).toTree := by
    simp only [unfold, decode, unfoldC]
    rw [rename_comp]
    exact rename_congr_relevant rel fun j lt => (sel_cut _ lt).symm
  rw [eq, encode_rename cutOk]
  simp only [unfold, decode, unfoldC]
  rw [encode_rename ok]

/-- **A closed subterm is one node wherever it occurs.** -/
theorem closed_one_node {St : Store Head} (canon : Canonical St) {x x' : Ref} (occ : Occurs St x)
    (occ' : Occurs St x') (closed : Closed (unfold St x)) (same : unfold St x = unfold St x') :
    x.id = x'.id :=
  (renamed_one_node canon occ occ' (ρ := []) (by rw [← same, rename_of_closed closed])).symm

/-! ## Controls -/

namespace SharingControls

/-- Two heads: a binder over one field, and application with two plain fields. -/
inductive H where
  | lam
  | app
  deriving DecidableEq, Repr

def lam (b : Term H) : Term H := .node .lam (.cons 1 b .nil)

def app (f x : Term H) : Term H := .node .app (.cons 0 f (.cons 0 x .nil))

/-- `λ. (0 1)`. -/
def t1 : Term H := lam (app (.idx 0) (.idx 1))

/-- `λ. (0 2)`: the same body one binder further out. -/
def t2 : Term H := lam (app (.idx 0) (.idx 2))

/-- Positive: `t1` is stored as three nodes (the variable, the application, the binder). -/
theorem t1_stored : (encodeR [] t1).1.length = 3 := by decide +kernel

/-- Positive: `t2` is `t1`'s node, its free variable placed one further out by the reference
`[false, true]`, and **encoding `t2` adds no node**: nothing is left unused. (In the shifts store
the same two terms leave one unused node: `SharedTerms.SharingControls.t2_garbage`.) -/
theorem t2_shares_t1 :
    (encodeR (encodeR [] t1).1 t2).2 = ⟨[false, true], (encodeR [] t1).2.id⟩ ∧
      (encodeR (encodeR [] t1).1 t2).1.length = 3 := by
  decide +kernel

/-- `(x z)` in the scope `x, y, z` (innermost `z`). -/
def xz : Term H := app (.idx 2) (.idx 0)

/-- `(x y)` in the same scope. -/
def xy : Term H := app (.idx 2) (.idx 1)

/-- `(z x)`. -/
def zx : Term H := app (.idx 0) (.idx 2)

/-- Positive: `(x z)` and `(x y)` are one node: the application of the outer to the inner of two
variables. Only the references differ. -/
theorem xz_xy_one_node :
    (encodeR [] xz).2.id = (encodeR (encodeR [] xz).1 xy).2.id ∧
      (encodeR [] xz).2.thin = [true, false, true] ∧
      (encodeR (encodeR [] xz).1 xy).2.thin = [false, true, true] := by
  decide +kernel

/-- Negative: `(x z)` and `(z x)` use their variables in a different order, and are two nodes. -/
theorem xz_zx_two_nodes : (encodeR [] xz).2.id ≠ (encodeR (encodeR [] xz).1 zx).2.id := by
  decide +kernel

/-- Negative: `λ. (0 1)` and `λ. (0 0)` are different trees, and encoding gives different
references. -/
theorem different_trees_different_refs :
    (encodeR [] t1).2 ≠ (encodeR (encodeR [] t1).1 (lam (app (.idx 0) (.idx 0)))).2 := by
  decide +kernel

end SharingControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
