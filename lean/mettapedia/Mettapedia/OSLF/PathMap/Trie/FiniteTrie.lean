/-!
# Finite Trie — Inductive Byte-Indexed Trie

`FTrie V` is the finite (inductive) refinement of the coinductive `CTrie V`.
Children are stored as a sorted association list `List (UInt8 × FTrie V)`,
matching the Rust PathMap `LineListNode` sparse representation.

Operations (join, meet, subtract, restrict) are defined via mutual recursion
with child-list merge helpers.

## References

- PathMap Rust crate: `ring.rs`, `trie_node.rs`
- CoinductiveTrie.lean: canonical coinductive semantics
-/

namespace Mettapedia.OSLF.PathMap.Trie

universe u

/-! ## §1: Core Type -/

/-- A finite byte-indexed trie.  Values can exist at any node (not just leaves).
    Children are stored as a sorted association list for sparse representation. -/
inductive FTrie (V : Type u) where
  /-- The empty trie (no values anywhere). -/
  | empty : FTrie V
  /-- A trie node with an optional value and sorted child list. -/
  | node (val : Option V) (children : List (UInt8 × FTrie V)) : FTrie V

namespace FTrie

variable {V : Type u}

/-! ## §2: Normalization -/

/-- Collapse trivial nodes: `node none [] → empty`. -/
def normalize : FTrie V → FTrie V
  | .node none [] => .empty
  | t => t

/-! ## §3: Lookup (mutual with child helper) -/

mutual
  /-- Look up a value at a byte path. -/
  def lookup : FTrie V → List UInt8 → Option V
    | .empty, _ => none
    | .node val _, [] => val
    | .node _ children, b :: rest => lookupChild b rest children

  /-- Helper: search sorted child list for byte `b`, then recurse. -/
  def lookupChild (b : UInt8) (rest : List UInt8) :
      List (UInt8 × FTrie V) → Option V
    | [] => none
    | (k, child) :: cs =>
      if k == b then lookup child rest
      else lookupChild b rest cs
end

/-! ## §4: Entries (mutual with child helper) -/

mutual
  /-- All (path, value) entries in the trie, in DFS order. -/
  def entries : FTrie V → List (List UInt8 × V)
    | .empty => []
    | .node val children =>
      (match val with | some v => [([], v)] | none => []) ++
      entriesChildren children

  /-- Helper: collect entries from a child list. -/
  def entriesChildren : List (UInt8 × FTrie V) → List (List UInt8 × V)
    | [] => []
    | (b, child) :: cs =>
      (entries child).map (fun (p, v) => (b :: p, v)) ++
      entriesChildren cs
end

/-! ## §5: Singleton -/

/-- Singleton trie: value `v` at path `p`. -/
def singleton : List UInt8 → V → FTrie V
  | [], v => .node (some v) []
  | b :: bs, v => .node none [(b, singleton bs v)]

/-! ## §6: Join (Union) -/

mutual
  /-- Union of two tries.  Left-biased when both have values at the same path. -/
  def join : FTrie V → FTrie V → FTrie V
    | .empty, t => t
    | t, .empty => t
    | .node v₁ c₁, .node v₂ c₂ =>
      .node (v₁ <|> v₂) (joinChildren c₁ c₂)

  /-- Merge two sorted child lists for union. -/
  def joinChildren : List (UInt8 × FTrie V) → List (UInt8 × FTrie V) →
      List (UInt8 × FTrie V)
    | [], cs₂ => cs₂
    | cs₁, [] => cs₁
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
      if b₁ < b₂ then
        (b₁, t₁) :: joinChildren rest₁ ((b₂, t₂) :: rest₂)
      else if b₂ < b₁ then
        (b₂, t₂) :: joinChildren ((b₁, t₁) :: rest₁) rest₂
      else
        let merged := join t₁ t₂
        match merged with
        | .empty => joinChildren rest₁ rest₂
        | _ => (b₁, merged) :: joinChildren rest₁ rest₂
end

/-! ## §7: Meet (Intersection) -/

mutual
  /-- Intersection of two tries.  Keeps the left value when both are present. -/
  def meet : FTrie V → FTrie V → FTrie V
    | .empty, _ => .empty
    | _, .empty => .empty
    | .node v₁ c₁, .node v₂ c₂ =>
      let val := match v₁, v₂ with | some v, some _ => some v | _, _ => none
      (FTrie.node val (meetChildren c₁ c₂)).normalize

  /-- Merge two sorted child lists for intersection. -/
  def meetChildren : List (UInt8 × FTrie V) → List (UInt8 × FTrie V) →
      List (UInt8 × FTrie V)
    | [], _ => []
    | _, [] => []
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
      if b₁ < b₂ then meetChildren rest₁ ((b₂, t₂) :: rest₂)
      else if b₂ < b₁ then meetChildren ((b₁, t₁) :: rest₁) rest₂
      else
        let merged := meet t₁ t₂
        match merged with
        | .empty => meetChildren rest₁ rest₂
        | _ => (b₁, merged) :: meetChildren rest₁ rest₂
end

/-! ## §8: Subtract (Difference) -/

mutual
  /-- Difference of two tries.  Keeps left value only if right has none. -/
  def subtract : FTrie V → FTrie V → FTrie V
    | .empty, _ => .empty
    | t, .empty => t
    | .node v₁ c₁, .node v₂ c₂ =>
      let val := match v₁, v₂ with | some v, none => some v | _, _ => none
      (FTrie.node val (subtractChildren c₁ c₂)).normalize

  /-- Merge two sorted child lists for difference. -/
  def subtractChildren : List (UInt8 × FTrie V) → List (UInt8 × FTrie V) →
      List (UInt8 × FTrie V)
    | [], _ => []
    | cs₁, [] => cs₁
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
      if b₁ < b₂ then (b₁, t₁) :: subtractChildren rest₁ ((b₂, t₂) :: rest₂)
      else if b₂ < b₁ then subtractChildren ((b₁, t₁) :: rest₁) rest₂
      else
        let merged := subtract t₁ t₂
        match merged with
        | .empty => subtractChildren rest₁ rest₂
        | _ => (b₁, merged) :: subtractChildren rest₁ rest₂
end

/-! ## §9: Restrict (Prefix Restriction) -/

mutual
  /-- Prefix restriction: keep paths from `t₁` whose prefix is in `t₂`. -/
  def restrict : FTrie V → FTrie V → FTrie V
    | .empty, _ => .empty
    | _, .empty => .empty
    | t₁, .node (some _) _ => t₁  -- prefix matched: keep entire subtree
    | .node _ c₁, .node none c₂ =>
      (FTrie.node none (restrictChildren c₁ c₂)).normalize

  /-- Merge two sorted child lists for prefix restriction. -/
  def restrictChildren : List (UInt8 × FTrie V) → List (UInt8 × FTrie V) →
      List (UInt8 × FTrie V)
    | [], _ => []
    | _, [] => []
    | (b₁, t₁) :: rest₁, (b₂, t₂) :: rest₂ =>
      if b₁ < b₂ then restrictChildren rest₁ ((b₂, t₂) :: rest₂)
      else if b₂ < b₁ then restrictChildren ((b₁, t₁) :: rest₁) rest₂
      else
        let merged := restrict t₁ t₂
        match merged with
        | .empty => restrictChildren rest₁ rest₂
        | _ => (b₁, merged) :: restrictChildren rest₁ rest₂
end

/-! ## §10: Basic Properties -/

@[simp] theorem lookup_empty (p : List UInt8) :
    (FTrie.empty : FTrie V).lookup p = none := rfl

theorem entries_empty : (FTrie.empty : FTrie V).entries = [] := rfl

/-! ## §11: Join Properties -/

theorem join_empty_left (t : FTrie V) : join .empty t = t := by
  cases t <;> unfold join <;> rfl
theorem join_empty_right (t : FTrie V) : join t .empty = t := by
  cases t <;> unfold join <;> rfl

/-! ## §12: Meet Properties -/

theorem meet_empty_left (t : FTrie V) : meet .empty t = .empty := by
  cases t <;> unfold meet <;> rfl
theorem meet_empty_right (t : FTrie V) : meet t .empty = .empty := by
  cases t <;> unfold meet <;> rfl

/-! ## §13: Upsert and Graft -/

/-- Upsert a child: if key `b` exists, apply `f`; otherwise append `(b, f .empty)`. -/
def upsertChild (b : UInt8) (f : FTrie V → FTrie V) :
    List (UInt8 × FTrie V) → List (UInt8 × FTrie V)
  | [] => [(b, f .empty)]
  | (k, child) :: cs =>
    if k == b then (k, f child) :: cs
    else (k, child) :: upsertChild b f cs

/-- Replace the subtrie at a path with a replacement.
    Uses `upsertChild` to handle both existing and missing children. -/
def graftAtPath : FTrie V → List UInt8 → FTrie V → FTrie V
  | _, [], replacement => replacement
  | .empty, b :: rest, replacement =>
    .node none [(b, graftAtPath .empty rest replacement)]
  | .node val children, b :: rest, replacement =>
    .node val (upsertChild b (fun child => graftAtPath child rest replacement) children)

theorem graftAtPath_root (t replacement : FTrie V) :
    graftAtPath t [] replacement = replacement := rfl

/-! ## §14: upsertChild lookup lemmas -/

theorem upsertChild_lookupChild_hit (b : UInt8) (f : FTrie V → FTrie V)
    (children : List (UInt8 × FTrie V)) (rest : List UInt8) :
    lookupChild b rest (upsertChild b f children) =
    match children.find? (fun (k, _) => k == b) with
    | some (_, child) => (f child).lookup rest
    | none => (f .empty).lookup rest := by
  induction children with
  | nil =>
    unfold upsertChild; simp only [lookupChild, beq_self_eq_true, List.find?]; rfl
  | cons hd tl ih =>
    obtain ⟨k, child⟩ := hd
    unfold upsertChild; simp only [List.find?]
    by_cases hkb : (k == b) = true
    · rw [if_pos hkb]; simp only [lookupChild, hkb]; rfl
    · rw [if_neg hkb]; simp only [lookupChild, hkb, Bool.false_eq_true, ↓reduceIte]; exact ih

theorem upsertChild_lookupChild_other (b q : UInt8) (f : FTrie V → FTrie V)
    (children : List (UInt8 × FTrie V)) (rest : List UInt8) (hne : q ≠ b) :
    lookupChild q rest (upsertChild b f children) =
    lookupChild q rest children := by
  induction children with
  | nil =>
    unfold upsertChild; simp only [lookupChild]
    have hbq : (b == q) = false := by simp [beq_iff_eq, Ne.symm hne]
    rw [hbq]; simp
  | cons hd tl ih =>
    obtain ⟨k, child⟩ := hd
    unfold upsertChild
    by_cases hkb : (k == b) = true
    · rw [if_pos hkb]; simp only [lookupChild]
      have hkeq : k = b := beq_iff_eq.mp hkb
      have hkq : (k == q) = false := by rw [hkeq]; simp [beq_iff_eq, Ne.symm hne]
      rw [hkq]; simp [hkq, ih]
    · rw [if_neg hkb]; simp only [lookupChild]
      by_cases hkq : (k == q) = true
      · rw [if_pos hkq, if_pos hkq]
      · rw [if_neg hkq, if_neg hkq]; exact ih

/-! ## §15: graftAtPath lookup theorems -/

theorem graftAtPath_lookup_under (t replacement : FTrie V)
    (graftPath suffix : List UInt8) :
    (graftAtPath t graftPath replacement).lookup (graftPath ++ suffix) =
    replacement.lookup suffix := by
  induction graftPath generalizing t with
  | nil => rfl
  | cons b rest ih =>
    match t with
    | .empty =>
      show (graftAtPath .empty (b :: rest) replacement).lookup (b :: (rest ++ suffix)) = _
      simp only [graftAtPath, lookup, lookupChild, beq_self_eq_true, ↓reduceIte]
      exact ih .empty
    | .node val children =>
      show (graftAtPath (.node val children) (b :: rest) replacement).lookup
        (b :: (rest ++ suffix)) = _
      simp only [graftAtPath, lookup]
      rw [upsertChild_lookupChild_hit]
      cases hf : children.find? (fun (k, _) => k == b) with
      | some p => exact ih p.2
      | none => exact ih .empty

theorem graftAtPath_lookup_diff_head (t replacement : FTrie V)
    (b : UInt8) (graftRest : List UInt8) (q : UInt8) (queryRest : List UInt8)
    (hne : q ≠ b) :
    (graftAtPath t (b :: graftRest) replacement).lookup (q :: queryRest) =
    t.lookup (q :: queryRest) := by
  match t with
  | .empty =>
    simp only [graftAtPath, lookup, lookupChild]
    have : (b == q) = false := by simp [beq_iff_eq, Ne.symm hne]
    simp [this]
  | .node val children =>
    simp only [graftAtPath, lookup]
    exact upsertChild_lookupChild_other b q _ children queryRest hne

theorem graftAtPath_lookup_nil_cons (t replacement : FTrie V)
    (b : UInt8) (graftRest : List UInt8) :
    (graftAtPath t (b :: graftRest) replacement).lookup [] =
    t.lookup [] := by
  match t with
  | .empty => rfl
  | .node val children => rfl

/-! ## §16: Summary

`FTrie V` is the finite inductive byte-indexed trie with four algebraic
operations (join, meet, subtract, restrict) defined via mutual recursion.

**0 sorries. 0 axioms.**

All operations compile and terminate.  Correctness theorems relating
`FTrie` operations to `CTrie` operations are in `TrieRefinement.lean`.
-/

end FTrie

end Mettapedia.OSLF.PathMap.Trie
