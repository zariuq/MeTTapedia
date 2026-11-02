import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Rename

/-!
# Co-de-Bruijn terms

A **co-de-Bruijn term** (McBride 2018) records, at every node, exactly which variables of its scope
it uses. Its scope is its **support**: the variables it uses, and no others. Here:

* `var` is the only term whose support is one variable: the variable itself.
* `node h n fields` has support `n`. Each field is `(d, e, t)`: the field sits under `d` binders,
  and the **edge** `e` is an exact thinning from the support of `t` into `d + n`. Its first `d`
  bits say which of the field's bound variables `t` uses (a `false` there is a vacuous binder), the
  other `n` bits say which of the node's variables it uses.
* **Relevance** (`ok`): every edge has length `d + n`, every child is relevant at the number of
  variables its edge keeps, and the fields' outer bits **cover** the node's support: each of the `n`
  variables is used by some field. McBride's binary relevant pairs carry a cover of two thinnings;
  here a node with `k` fields carries a cover of `k`.

A term in a larger scope is a **thing with a thinning** (`Thing`): a relevant co-de-Bruijn term and
a thinning from its support into the scope. It is **canonical** (`Canon`) when the thinning is
trimmed. It stands for the binding tree `decode x = rename x.1 x.2.toTree`.

Example: `λx. λy. x` (de Bruijn `lam (lam 1)`) is the canonical thing
`([], node lam 0 [(1, [true], node lam 1 [(1, [false, true], var)])])`: the outer binder uses its
variable, the inner binder does not (`CodeControls.K_encoding`).

Results:

* `toTree` of a relevant term is relevant (`CTerm.relevant_toTree`), and `toTree` is injective on
  relevant terms (`CTerm.toTree_inj`).
* **Smart constructors** `varR` and `mkNodeR` build canonical things; `mkNodeR` computes the node's
  support as the union of its fields' outer variables and each edge by pulling back along it,
  without looking inside the children (`mkNodeR_spec`).
* **Encoding** a binding tree gives a canonical thing that decodes to it (`encode_spec`).
* **The canonicity invariant**: decoding is injective on canonical things (`decode_inj`), so
  encoding and decoding are inverse bijections between binding trees and canonical things
  (`encode_decode`), and two trees are equal exactly when their codes are (`encode_eq_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Thin

mutual

/-- A co-de-Bruijn term: it uses every variable of its support. -/
inductive CTerm (Head : Type) where
  /-- The variable: its support is itself. -/
  | var
  /-- A node with support `scope`; each field is a binder count, an edge and a child. -/
  | node (head : Head) (scope : ℕ) (fields : CFields Head)

/-- The fields of a co-de-Bruijn node. -/
inductive CFields (Head : Type) where
  | nil
  | cons (depth : ℕ) (edge : Thin) (term : CTerm Head) (rest : CFields Head)

end

deriving instance DecidableEq for CTerm, CFields

variable {Head : Type}

/-! ## Decoding -/

mutual

/-- **The binding tree of a co-de-Bruijn term**, over its own support. -/
def CTerm.toTree : CTerm Head → Term Head
  | .var => .idx 0
  | .node h _ fs => .node h fs.toFields

/-- Each child is renamed along its edge. -/
def CFields.toFields : CFields Head → Fields Head
  | .nil => .nil
  | .cons d e t rest => .cons d (rename e t.toTree) rest.toFields

end

@[simp] theorem CTerm.toTree_var : (CTerm.var : CTerm Head).toTree = .idx 0 := by
  simp [CTerm.toTree]

@[simp] theorem CTerm.toTree_node (h : Head) (n : ℕ) (fs : CFields Head) :
    (CTerm.node h n fs).toTree = .node h fs.toFields := by
  simp [CTerm.toTree]

@[simp] theorem CFields.toFields_nil : (CFields.nil : CFields Head).toFields = .nil := by
  simp [CFields.toFields]

@[simp] theorem CFields.toFields_cons (d : ℕ) (e : Thin) (t : CTerm Head) (rest : CFields Head) :
    (CFields.cons d e t rest).toFields = .cons d (rename e t.toTree) rest.toFields := by
  simp [CFields.toFields]

/-! ## Relevance -/

/-- The outer bits of each field: which of the node's variables it uses. -/
def CFields.outer : CFields Head → List Thin
  | .nil => []
  | .cons d e _ rest => back d e :: rest.outer

/-- The fields **cover** the node's support `n`: together they use each of its `n` variables, and
no other. -/
def CFields.covers (fs : CFields Head) (n : ℕ) : Bool := decide (bors fs.outer = idn n)

mutual

/-- **Relevance**: the term uses exactly the `m` variables of its support. -/
def CTerm.ok : CTerm Head → ℕ → Bool
  | .var, m => decide (m = 1)
  | .node _ n fs, m => decide (m = n) && fs.ok n && fs.covers n

/-- Every edge has length `d + n`, and every child is relevant at what its edge keeps. -/
def CFields.ok : CFields Head → ℕ → Bool
  | .nil, _ => true
  | .cons d e t rest, n => decide (e.length = d + n) && t.ok (ones e) && rest.ok n

end

@[simp] theorem CTerm.ok_var (m : ℕ) : (CTerm.var : CTerm Head).ok m = decide (m = 1) := by
  simp [CTerm.ok]

@[simp] theorem CTerm.ok_node (h : Head) (n : ℕ) (fs : CFields Head) (m : ℕ) :
    (CTerm.node h n fs).ok m = (decide (m = n) && fs.ok n && fs.covers n) := by
  simp [CTerm.ok]

@[simp] theorem CFields.ok_nil (n : ℕ) : (CFields.nil : CFields Head).ok n = true := by
  simp [CFields.ok]

@[simp] theorem CFields.ok_cons (d : ℕ) (e : Thin) (t : CTerm Head) (rest : CFields Head) (n : ℕ) :
    (CFields.cons d e t rest).ok n = (decide (e.length = d + n) && t.ok (ones e) && rest.ok n) := by
  simp [CFields.ok]

theorem bit_idn (n i : ℕ) : bit (idn n) i = decide (i < n) := by
  induction n generalizing i with
  | zero => simp [idn]
  | succ n ih =>
      cases i with
      | zero => simp [idn, List.replicate_succ]
      | succ i =>
          have := ih i
          simp only [idn] at this
          simp [idn, List.replicate_succ, this]

theorem ones_idn (n : ℕ) : ones (idn n) = n := by
  induction n with
  | zero => simp [idn]
  | succ n ih => simpa [idn, List.replicate_succ] using ih

mutual

/-- **A relevant term's tree uses exactly its support.** -/
theorem CTerm.relevant_toTree : ∀ (c : CTerm Head) (m : ℕ), c.ok m = true → Relevant m c.toTree
  | .var, m, h => by
      simp at h; subst h
      intro i; simp; omega
  | .node _ n fs, m, h => by
      simp only [CTerm.ok_node, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨rfl, hfs⟩, hcov⟩ := h
      intro i
      simp only [CTerm.toTree_node, freeAt_node]
      rw [CFields.free_toFields fs m hfs i]
      simp only [CFields.covers, decide_eq_true_eq] at hcov
      rw [hcov, bit_idn, decide_eq_true_eq]

/-- The free variables of relevant fields are the kept positions of their outer bits' union. -/
theorem CFields.free_toFields : ∀ (fs : CFields Head) (n : ℕ), fs.ok n = true →
    ∀ i, fieldsFreeAt fs.toFields i = bit (bors fs.outer) i
  | .nil, _, _, i => by simp [CFields.outer, bors]
  | .cons d e t rest, n, h, i => by
      simp only [CFields.ok_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨_, ht⟩, hrest⟩ := h
      have rel := CTerm.relevant_toTree t (ones e) ht
      simp only [CFields.toFields_cons, fieldsFreeAt_cons, CFields.outer, bors, List.foldr_cons]
      rw [freeAt_rename_relevant rel, CFields.free_toFields rest n hrest i, bit_bor, bit_back]
      simp only [bors]
      rw [Nat.add_comm i d]

end

/-- A tree is relevant at one support only. -/
theorem Relevant.unique {m m' : ℕ} {t : Term Head} (h : Relevant m t) (h' : Relevant m' t) : m = m' := by
  by_contra ne
  rcases Nat.lt_or_gt_of_ne ne with lt | gt
  · exact lt_irrefl m ((h m).mp ((h' m).mpr lt))
  · exact lt_irrefl m' ((h' m').mp ((h m').mpr gt))

mutual

/-- **Decoding loses nothing on relevant terms.** -/
theorem CTerm.toTree_inj : ∀ (c c' : CTerm Head) (m m' : ℕ), c.ok m = true → c'.ok m' = true →
    c.toTree = c'.toTree → c = c'
  | .var, .var, _, _, _, _, _ => rfl
  | .var, .node _ _ _, _, _, _, _, e => by simp at e
  | .node _ _ _, .var, _, _, _, _, e => by simp at e
  | .node h n fs, .node h' n' fs', m, m', ok, ok', e => by
      have rel := CTerm.relevant_toTree _ _ ok
      have rel' := CTerm.relevant_toTree _ _ ok'
      have mm : m = m' := rel.unique (e ▸ rel')
      simp only [CTerm.ok_node, Bool.and_eq_true, decide_eq_true_eq] at ok ok'
      obtain ⟨⟨rfl, hfs⟩, -⟩ := ok
      obtain ⟨⟨rfl, hfs'⟩, -⟩ := ok'
      subst mm
      simp only [CTerm.toTree_node, Term.node.injEq] at e
      obtain ⟨rfl, ef⟩ := e
      rw [CFields.toFields_inj fs fs' m hfs hfs' ef]

theorem CFields.toFields_inj : ∀ (fs fs' : CFields Head) (n : ℕ), fs.ok n = true → fs'.ok n = true →
    fs.toFields = fs'.toFields → fs = fs'
  | .nil, .nil, _, _, _, _ => rfl
  | .nil, .cons _ _ _ _, _, _, _, e => by simp at e
  | .cons _ _ _ _, .nil, _, _, _, e => by simp at e
  | .cons d e t rest, .cons d' e' t' rest', n, ok, ok', eq => by
      simp only [CFields.ok_cons, Bool.and_eq_true, decide_eq_true_eq] at ok ok'
      obtain ⟨⟨le, ht⟩, hrest⟩ := ok
      obtain ⟨⟨le', ht'⟩, hrest'⟩ := ok'
      simp only [CFields.toFields_cons, Fields.cons.injEq] at eq
      obtain ⟨rfl, et, er⟩ := eq
      obtain ⟨rfl, tt⟩ := rename_exact_inj (by rw [le, le'])
        (CTerm.relevant_toTree t _ ht) (CTerm.relevant_toTree t' _ ht') et
      rw [CTerm.toTree_inj t t' _ _ ht ht' tt, CFields.toFields_inj rest rest' n hrest hrest' er]

end

/-! ## Things with thinnings -/

/-- **A thing with a thinning**: a co-de-Bruijn term and a thinning from its support into the
surrounding scope. -/
abbrev Thing (Head : Type) := Thin × CTerm Head

/-- A thing is **canonical** when its thinning is trimmed and its term is relevant at what the
thinning keeps. -/
def Canon (x : Thing Head) : Prop := trimmed x.1 = true ∧ x.2.ok (ones x.1) = true

/-- **The binding tree a thing stands for.** -/
def decode (x : Thing Head) : Term Head := rename x.1 x.2.toTree

/-- **The canonicity invariant**: a canonical thing is determined by the tree it stands for. -/
theorem decode_inj {x y : Thing Head} (hx : Canon x) (hy : Canon y) (e : decode x = decode y) : x = y := by
  obtain ⟨θ, c⟩ := x
  obtain ⟨θ', c'⟩ := y
  obtain ⟨tθ, oc⟩ := hx
  obtain ⟨tθ', oc'⟩ := hy
  obtain ⟨rfl, et⟩ := rename_trimmed_inj tθ tθ' (CTerm.relevant_toTree c _ oc)
    (CTerm.relevant_toTree c' _ oc') e
  rw [CTerm.toTree_inj c c' _ _ oc oc' et]

/-- The free variables of a canonical thing's tree are exactly the kept positions of its thinning:
**the support is read off the reference**. -/
theorem freeAt_decode {x : Thing Head} (hx : Canon x) (i : ℕ) : freeAt (decode x) i = bit x.1 i :=
  freeAt_rename_relevant (CTerm.relevant_toTree x.2 _ hx.2) i

/-! ## Smart constructors -/

/-- **The variable `k`**: the variable node, kept at position `k`. -/
def varR (k : ℕ) : Thing Head := (dropN k [true], .var)

/-- Co-de-Bruijn fields from a list. -/
def CFields.ofList : List (ℕ × Thin × CTerm Head) → CFields Head
  | [] => .nil
  | (d, e, t) :: rest => .cons d e t (CFields.ofList rest)

/-- The node's support: the union of its fields' outer variables. -/
def supportOf (fs : List (ℕ × Thing Head)) : Thin := bors (fs.map fun x => back x.1 x.2.1)

/-- **The smart constructor of a node**: given each field's child as a thing in the field's scope,
the node's support is the union of the children's outer variables, and each edge is the child's
thinning with its outer bits read in that union. The children are not visited. -/
def mkNodeR (h : Head) (fs : List (ℕ × Thing Head)) : Thing Head :=
  (supportOf fs, .node h (ones (supportOf fs))
    (CFields.ofList (fs.map fun x => (x.1, edge x.1 (supportOf fs) x.2.1, x.2.2))))

/-- Binding-tree fields from things. -/
def fieldsOfThings : List (ℕ × Thing Head) → Fields Head
  | [] => .nil
  | (d, x) :: rest => .cons d (decode x) (fieldsOfThings rest)

theorem trimmed_dropN_true (k : ℕ) : trimmed (dropN k [true]) = true := by
  induction k with
  | zero => simp [dropN]
  | succ k ih =>
      simp only [dropN, List.replicate_succ, List.cons_append] at ih ⊢
      exact trimmed_cons ih (by simp)

/-- `varR k` is canonical and stands for `idx k`. -/
theorem varR_spec (k : ℕ) : Canon (varR k : Thing Head) ∧ decode (varR k : Thing Head) = .idx k := by
  refine ⟨⟨trimmed_dropN_true k, by simp [varR]⟩, ?_⟩
  simp [decode, varR, sel_dropN]

theorem trimmed_back {θ : Thin} (h : trimmed θ = true) (d : ℕ) : trimmed (back d θ) = true := by
  induction d generalizing θ with
  | zero => simpa [back] using h
  | succ d ih =>
      cases θ with
      | nil => simp [back]
      | cons b θ =>
          have := ih (trimmed_tail h)
          simpa [back] using this

theorem sub_supportOf {fs : List (ℕ × Thing Head)} {x : ℕ × Thing Head} (mem : x ∈ fs) :
    Sub (back x.1 x.2.1) (supportOf fs) := by
  intro i hi
  rw [supportOf, bit_bors]
  exact ⟨_, List.mem_map_of_mem mem, hi⟩

theorem outer_ofList (l : List (ℕ × Thin × CTerm Head)) :
    (CFields.ofList l).outer = l.map fun x => back x.1 x.2.1 := by
  induction l with
  | nil => simp [CFields.ofList, CFields.outer]
  | cons x l ih => obtain ⟨d, e, t⟩ := x; simp [CFields.ofList, CFields.outer, ih]

theorem ok_ofList {n : ℕ} :
    ∀ l : List (ℕ × Thin × CTerm Head),
      (∀ x ∈ l, x.2.1.length = x.1 + n ∧ x.2.2.ok (ones x.2.1) = true) → (CFields.ofList l).ok n = true
  | [], _ => by simp [CFields.ofList]
  | (d, e, t) :: rest, h => by
      have h0 := h (d, e, t) (by simp)
      simp only [CFields.ofList, CFields.ok_cons, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨h0.1, h0.2⟩, ok_ofList rest fun x m => h x (by simp [m])⟩

/-- A list of exact subscopes of `n` that together keep every variable of `n` covers `n`. -/
theorem bors_eq_idn {n : ℕ} {l : List Thin} (len : ∀ θ ∈ l, θ.length = n)
    (cover : ∀ j < n, ∃ θ ∈ l, bit θ j = true) (empty : l = [] → n = 0) : bors l = idn n := by
  have lenB : (bors l).length = n := by
    cases l with
    | nil => simp [bors, empty rfl]
    | cons θ l =>
        have : ∀ l' : List Thin, (∀ θ ∈ l', θ.length = n) → (bors l').length ≤ n := by
          intro l' h'
          induction l' with
          | nil => simp [bors]
          | cons θ' l' ih =>
              simp only [bors, List.foldr_cons] at ih ⊢
              rw [length_bor, h' θ' (by simp)]
              exact max_le (le_refl n) (ih fun x m => h' x (by simp [m]))
        have le := this (θ :: l) len
        have ge : n ≤ (bors (θ :: l)).length := by
          simp only [bors, List.foldr_cons, length_bor, len θ (by simp)]
          exact le_max_left _ _
        omega
  refine eq_of_bits_of_length (by rw [lenB, idn, List.length_replicate]) fun i => ?_
  rw [bit_idn]
  apply Bool.eq_iff_iff.mpr
  rw [bit_bors, decide_eq_true_eq]
  constructor
  · rintro ⟨θ, mem, hb⟩
    have := (bit_iff_exists_sel θ i).mp hb
    obtain ⟨j, lt, rfl⟩ := this
    have := (bit_sel lt).2
    rw [len θ mem] at this
    exact this
  · intro lt; exact cover i lt

/-- **The smart constructor is correct**: from canonical children it builds a canonical thing that
stands for the node of their trees. -/
theorem mkNodeR_spec (h : Head) {fs : List (ℕ × Thing Head)} (kids : ∀ x ∈ fs, Canon x.2) :
    Canon (mkNodeR h fs) ∧ decode (mkNodeR h fs) = .node h (fieldsOfThings fs) := by
  have subs : ∀ x ∈ fs, Sub (back x.1 x.2.1) (supportOf fs) := fun x m => sub_supportOf m
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact trimmed_bors fun θ m => by
      obtain ⟨x, mx, rfl⟩ := List.mem_map.mp m
      exact trimmed_back (kids x mx).1 _
  · simp only [mkNodeR, CTerm.ok_node, decide_true, Bool.true_and, Bool.and_eq_true]
    refine ⟨ok_ofList _ fun y my => ?_, ?_⟩
    · obtain ⟨x, mx, rfl⟩ := List.mem_map.mp my
      exact ⟨length_edge _ _ _, by rw [ones_edge (subs x mx)]; exact (kids x mx).2⟩
    · simp only [CFields.covers, decide_eq_true_eq, outer_ofList, List.map_map]
      refine bors_eq_idn (fun θ m => ?_) (fun j lt => ?_) (fun e => ?_)
      · obtain ⟨x, -, rfl⟩ := List.mem_map.mp m
        simp [Function.comp, back_edge]
      · have hb : bit (bors (fs.map fun x => back x.1 x.2.1)) (sel (supportOf fs) j) = true :=
          (bit_sel lt).1
        rw [bit_bors] at hb
        obtain ⟨φ, mφ, hφ⟩ := hb
        obtain ⟨x, mx, rfl⟩ := List.mem_map.mp mφ
        refine ⟨pull (supportOf fs) (back x.1 x.2.1),
          List.mem_map.mpr ⟨x, mx, by simp [Function.comp, back_edge]⟩, ?_⟩
        rw [bit_pull _ lt]; exact hφ
      · have : fs = [] := by simpa using e
        subst this
        simp [supportOf, bors]
  · simp only [decode, mkNodeR, CTerm.toTree_node, rename_node]
    congr 1
    have : ∀ l : List (ℕ × Thing Head), (∀ x ∈ l, Canon x.2 ∧ Sub (back x.1 x.2.1) (supportOf fs)) →
        renameFields (supportOf fs)
            (CFields.ofList (l.map fun x => (x.1, edge x.1 (supportOf fs) x.2.1, x.2.2))).toFields =
          fieldsOfThings l := by
      intro l hl
      induction l with
      | nil => simp [CFields.ofList, fieldsOfThings]
      | cons x l ih =>
          obtain ⟨d, θ, c⟩ := x
          obtain ⟨⟨_, oc⟩, sub⟩ := hl (d, θ, c) (by simp)
          simp only [List.map_cons, CFields.ofList, CFields.toFields_cons, renameFields_cons,
            fieldsOfThings, decode]
          rw [ih fun y m => hl y (by simp [m]), rename_comp]
          congr 1
          exact rename_congr_relevant (CTerm.relevant_toTree c _ oc) fun j lt => by
            rw [sel_comp]; exact sel_edge sub lt
    exact this fs fun x m => ⟨kids x m, subs x m⟩

/-! ## Encoding binding trees -/

mutual

/-- **The code of a binding tree**, built bottom-up with the smart constructors. -/
def encode : Term Head → Thing Head
  | .idx k => varR k
  | .node h fs => mkNodeR h (encodeFields fs)

def encodeFields : Fields Head → List (ℕ × Thing Head)
  | .nil => []
  | .cons d t rest => (d, encode t) :: encodeFields rest

end

mutual

/-- **Encoding is correct**: the code is canonical and stands for the tree. -/
theorem encode_spec : ∀ t : Term Head, Canon (encode t) ∧ decode (encode t) = t
  | .idx k => by simpa [encode] using varR_spec k
  | .node h fs => by
      obtain ⟨kids, eq⟩ := encodeFields_spec fs
      obtain ⟨canon, dec⟩ := mkNodeR_spec h kids
      simp only [encode]
      exact ⟨canon, by rw [dec, eq]⟩

theorem encodeFields_spec : ∀ fs : Fields Head,
    (∀ x ∈ encodeFields fs, Canon x.2) ∧ fieldsOfThings (encodeFields fs) = fs
  | .nil => by simp [encodeFields, fieldsOfThings]
  | .cons d t rest => by
      obtain ⟨ct, dt⟩ := encode_spec t
      obtain ⟨cr, dr⟩ := encodeFields_spec rest
      refine ⟨fun x m => ?_, ?_⟩
      · simp only [encodeFields, List.mem_cons] at m
        rcases m with rfl | m
        · exact ct
        · exact cr x m
      · simp [encodeFields, fieldsOfThings, dt, dr]

end

/-- **Encoding inverts decoding** on canonical things. -/
theorem encode_decode {x : Thing Head} (hx : Canon x) : encode (decode x) = x :=
  decode_inj (encode_spec _).1 hx (encode_spec _).2

/-- **Two binding trees are equal exactly when their codes are.** Trees carry no bound names, so
this is alpha-equivalence decided by comparing codes. -/
theorem encode_eq_iff (s t : Term Head) : encode s = encode t ↔ s = t := by
  constructor
  · intro e
    rw [← (encode_spec s).2, ← (encode_spec t).2, e]
  · rintro rfl; rfl

/-- The support of a tree is read off its code. -/
theorem freeAt_iff_bit_encode (t : Term Head) (i : ℕ) : freeAt t i = bit (encode t).1 i := by
  conv_lhs => rw [← (encode_spec t).2]
  exact freeAt_decode (encode_spec t).1 i

/-! ## Examples -/

namespace CodeControls

/-- Heads: a binder over one field, and application with two plain fields. -/
inductive H where
  | lam
  | app
  deriving DecidableEq, Repr

def lam (b : Term H) : Term H := .node .lam (.cons 1 b .nil)

def app (f x : Term H) : Term H := .node .app (.cons 0 f (.cons 0 x .nil))

/-- `K = λc. λe. c`. -/
def K : Term H := lam (lam (.idx 1))

/-- `S = λf. λs. λe. (f e) (s e)`. -/
def S : Term H := lam (lam (lam (app (app (.idx 2) (.idx 0)) (app (.idx 1) (.idx 0)))))

/-- Positive: the code of `K`. The outer binder uses its variable (`[true]`); the inner binder does
not (the first bit of `[false, true]`) and passes the outer variable on (its second bit). -/
theorem K_encoding :
    encode K = ([], .node .lam 0 (.cons 1 [true] (.node .lam 1 (.cons 1 [false, true] .var .nil)) .nil)) := by
  decide +kernel

/-- Positive: `S` is closed, and each of its binders uses its variable. -/
theorem S_closed_binders_used :
    (encode S).1 = [] ∧
      (match (encode S).2 with
        | .node _ _ (.cons _ e₁ (.node _ _ (.cons _ e₂ (.node _ _ (.cons _ e₃ _ .nil)) .nil)) .nil) =>
            bit e₁ 0 && bit e₂ 0 && bit e₃ 0
        | _ => false) = true := by
  decide +kernel

/-- Negative: `λc. λe. e` is not `K`, and its code differs. -/
theorem K_not_KI : encode K ≠ encode (lam (lam (.idx 0))) := by decide +kernel

end CodeControls

end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
