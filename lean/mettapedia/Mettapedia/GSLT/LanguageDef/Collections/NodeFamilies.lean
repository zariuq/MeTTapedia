import Mettapedia.Algebra.Collections.Ornaments
import Mettapedia.GSLT.LanguageDef.Collections.Presentations
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Node families: every term is a tree of cells over the terms that are not cells

A **node family** on terms `T` builds a cell of shape `f` from `arity f`
recursive children and recognizes the terms that are cells (`Nodes`); the
shape carries the cell's other fields. A constructor family with one
recursive argument (`Presentations.Family`) is the case of arity one; binary
trees `(Node l r)`, and any constructor read with several recursive
arguments, are the general case. Nothing marks a datatype: the family is a
reading of terms, chosen by whoever stores them.

* **Every term is uniquely a tree.** The trees are the W-type whose nodes are
  the shapes, with their recursive positions, and whose leaves are the terms
  that are not cells, with none (`Nodes.Tree`). Reading a term as a tree and
  writing the tree back are inverse (`Nodes.equivTree`), so every observation
  of terms is an observation of trees: any layout of these trees, pointer
  nodes or a flat array of shapes in order, is a layout of the terms.
* **Structural recursion is the catamorphism.** Recursion written as one
  equation for cells and one for every other term
  (`Nodes.recurse_node`, `Nodes.recurse_of_none`) is the W-type's fold of the
  tree (`Nodes.recurse_eq_elim`): proved once for every family, and run by
  any walker of the tree.
* **One shape, several readings.** A constructor with two arguments of its own
  kind can be read with both recursive (`binaryNodes`) or with one of them a
  field (`Presentations.Family`). Each reading is a bijection, so each is a
  sound representation; they answer different questions cheaply, and the
  observer decides which one to keep. The tree `(P (P a b) (P c d))` has three
  cells read as a tree and two read along its last argument
  (`Controls.two_readings`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.NodeFamilies

universe u v w

/-- A node family on terms `T` with shapes `F`: cells of shape `f` have
`arity f` recursive children. -/
structure Nodes (T : Type u) (F : Type v) (arity : F → ℕ) where
  node : (f : F) → (Fin (arity f) → T) → T
  unnode : T → Option (Σ f : F, Fin (arity f) → T)
  unnode_node : ∀ f c, unnode (node f c) = some ⟨f, c⟩
  node_unnode : ∀ {t} {p : Σ f : F, Fin (arity f) → T}, unnode t = some p → node p.1 p.2 = t
  /-- A measure that decreases from a cell to each of its children. -/
  rank : T → ℕ
  rank_lt : ∀ {t} {p : Σ f : F, Fin (arity f) → T}, unnode t = some p → ∀ i, rank (p.2 i) < rank t

namespace Nodes

variable {T : Type u} {F : Type v} {arity : F → ℕ} (N : Nodes T F arity)

/-- The terms that are not cells. -/
def Leaf : Type u := {t : T // N.unnode t = none}

/-- Shapes have their positions; leaves have none. -/
def Pos : F ⊕ N.Leaf → Type
  | .inl f => Fin (arity f)
  | .inr _ => Empty

/-- Trees of cells over the terms that are not cells. -/
abbrev Tree := WType N.Pos

/-- Read a term as a tree. -/
def toTree (t : T) : N.Tree :=
  match h : N.unnode t with
  | some p => ⟨.inl p.1, fun i => toTree (p.2 i)⟩
  | none => ⟨.inr ⟨t, h⟩, fun e => nomatch e⟩
termination_by N.rank t
decreasing_by exact N.rank_lt h i

/-- Write a tree as a term. -/
def ofTree : N.Tree → T
  | ⟨.inl f, c⟩ => N.node f fun i => ofTree (c i)
  | ⟨.inr l, _⟩ => l.1

theorem toTree_of_some {t : T} {p : Σ f : F, Fin (arity f) → T} (h : N.unnode t = some p) :
    N.toTree t = ⟨.inl p.1, fun i => N.toTree (p.2 i)⟩ := by
  rw [toTree]
  split
  · next p' h' => rw [h] at h'; cases h'; rfl
  · next h' => rw [h] at h'; cases h'

theorem toTree_of_none {t : T} (h : N.unnode t = none) :
    N.toTree t = ⟨.inr ⟨t, h⟩, fun e => nomatch e⟩ := by
  rw [toTree]
  split
  · next p' h' => rw [h] at h'; cases h'
  · rfl

theorem ofTree_toTree (t : T) : N.ofTree (N.toTree t) = t := by
  induction hr : N.rank t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
      cases h : N.unnode t with
      | none => rw [N.toTree_of_none h]; rfl
      | some p =>
          rw [N.toTree_of_some h, ofTree]
          conv_rhs => rw [← N.node_unnode h]
          congr 1
          funext i
          exact ih _ (hr ▸ N.rank_lt h i) _ rfl

theorem toTree_ofTree : ∀ w : N.Tree, N.toTree (N.ofTree w) = w
  | ⟨.inl f, c⟩ => by
      rw [ofTree, N.toTree_of_some (N.unnode_node f _)]
      congr 1
      funext i
      exact toTree_ofTree (c i)
  | ⟨.inr l, c⟩ => by
      rw [ofTree, N.toTree_of_none l.2]
      congr 1
      funext e
      exact nomatch e

/-- **Every term is uniquely a tree of cells over the terms that are not
cells.** -/
def equivTree : T ≃ N.Tree where
  toFun := N.toTree
  invFun := N.ofTree
  left_inv := N.ofTree_toTree
  right_inv := N.toTree_ofTree

/-! ### Structural recursion -/

/-- Recursion written as one equation for cells, `alg`, and one for every
other term, `leaf`. -/
def recurse {β : Type w} (alg : (f : F) → (Fin (arity f) → β) → β) (leaf : T → β) (t : T) : β :=
  match _h : N.unnode t with
  | some p => alg p.1 fun i => recurse alg leaf (p.2 i)
  | none => leaf t
termination_by N.rank t
decreasing_by exact N.rank_lt _h i

theorem recurse_of_some {β : Type w} (alg : (f : F) → (Fin (arity f) → β) → β) (leaf : T → β)
    {t : T} {p : Σ f : F, Fin (arity f) → T} (h : N.unnode t = some p) :
    N.recurse alg leaf t = alg p.1 fun i => N.recurse alg leaf (p.2 i) := by
  rw [recurse]
  split
  · next p' h' => rw [h] at h'; cases h'; rfl
  · next h' => rw [h] at h'; cases h'

theorem recurse_node {β : Type w} (alg : (f : F) → (Fin (arity f) → β) → β) (leaf : T → β)
    (f : F) (c : Fin (arity f) → T) :
    N.recurse alg leaf (N.node f c) = alg f fun i => N.recurse alg leaf (c i) :=
  N.recurse_of_some alg leaf (N.unnode_node f c)

theorem recurse_of_none {β : Type w} (alg : (f : F) → (Fin (arity f) → β) → β) (leaf : T → β)
    {t : T} (h : N.unnode t = none) : N.recurse alg leaf t = leaf t := by
  rw [recurse]
  split
  · next p' h' => rw [h] at h'; cases h'
  · rfl

/-- The algebra of the tree that reads cells by `alg` and leaves by `leaf`. -/
def treeAlg {β : Type w} (alg : (f : F) → (Fin (arity f) → β) → β) (leaf : T → β) :
    (Σ x : F ⊕ N.Leaf, N.Pos x → β) → β
  | ⟨.inl f, c⟩ => alg f c
  | ⟨.inr l, _⟩ => leaf l.1

/-- **Structural recursion is the catamorphism of the tree.** -/
theorem recurse_eq_elim {β : Type w} (alg : (f : F) → (Fin (arity f) → β) → β) (leaf : T → β)
    (t : T) : N.recurse alg leaf t = WType.elim β (N.treeAlg alg leaf) (N.toTree t) := by
  induction hr : N.rank t using Nat.strong_induction_on generalizing t with
  | _ n ih =>
      cases h : N.unnode t with
      | none =>
          rw [N.recurse_of_none alg leaf h, N.toTree_of_none h]
          rfl
      | some p =>
          rw [N.recurse_of_some alg leaf h, N.toTree_of_some h]
          simp only [WType.elim, treeAlg]
          congr 1
          funext i
          exact ih _ (hr ▸ N.rank_lt h i) _ rfl

end Nodes

/-! ## Binary cells of HE terms -/

section HE

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.GSLT.LanguageDef.Collections.Presentations (nodes nodesAll)

/-- Recognize `(c a b)`. -/
def binaryUnnode (c : String) : Atom → Option (Σ _ : Unit, Fin 2 → Atom)
  | .expression [.symbol c', a, b] => if c' = c then some ⟨(), ![a, b]⟩ else none
  | _ => none

theorem binaryUnnode_eq_some {c : String} {t : Atom} {p : Σ _ : Unit, Fin 2 → Atom} :
    binaryUnnode c t = some p ↔ t = .expression [.symbol c, p.2 0, p.2 1] := by
  obtain ⟨u, ch⟩ := p
  constructor
  · intro h
    match t, h with
    | .expression [.symbol c', a, b], h =>
        simp only [binaryUnnode] at h
        split_ifs at h with same
        cases h
        subst same
        rfl
  · intro h
    subst h
    cases u
    have pair : (![ch 0, ch 1] : Fin 2 → Atom) = ch := by
      funext i
      fin_cases i <;> rfl
    show (if c = c then some (⟨(), ![ch 0, ch 1]⟩ : Σ _ : Unit, Fin 2 → Atom) else none) =
      some ⟨(), ch⟩
    rw [if_pos rfl, pair]

/-- Cells `(c a b)` with both arguments recursive. -/
def binaryNodes (c : String) : Nodes Atom Unit (fun _ => 2) where
  node _ ch := .expression [.symbol c, ch 0, ch 1]
  unnode := binaryUnnode c
  unnode_node u ch := by
    rw [binaryUnnode_eq_some]
  node_unnode h := (binaryUnnode_eq_some.mp h).symm
  rank := nodes
  rank_lt {t p} h i := by
    rw [binaryUnnode_eq_some.mp h]
    fin_cases i <;> simp [nodes, nodesAll] <;> omega

end HE

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.GSLT.LanguageDef.Collections.Presentations (Family last)

/-- `(P (P a b) (P c d))`. -/
def tree : Atom :=
  .expression [.symbol "P", .expression [.symbol "P", .symbol "a", .symbol "b"],
    .expression [.symbol "P", .symbol "c", .symbol "d"]]

/-- The number of cells of a term read as a tree. -/
def cells (t : Atom) : ℕ := (binaryNodes "P").recurse (fun _ c => c 0 + c 1 + 1) (fun _ => 0) t

/-- **Two readings of one term.** Read as a tree it has three cells; read
along its last argument it is a spine of two cells. -/
theorem two_readings :
    cells tree = 3 ∧ ((last "P" 1).spine tree).elems.length = 2 := by
  constructor
  · have leafA : (binaryNodes "P").unnode (.symbol "a") = none := rfl
    have leafB : (binaryNodes "P").unnode (.symbol "b") = none := rfl
    have leafC : (binaryNodes "P").unnode (.symbol "c") = none := rfl
    have leafD : (binaryNodes "P").unnode (.symbol "d") = none := rfl
    have left : (binaryNodes "P").node () ![.symbol "a", .symbol "b"] =
        .expression [.symbol "P", .symbol "a", .symbol "b"] := rfl
    have right : (binaryNodes "P").node () ![.symbol "c", .symbol "d"] =
        .expression [.symbol "P", .symbol "c", .symbol "d"] := rfl
    have whole : (binaryNodes "P").node ()
        ![.expression [.symbol "P", .symbol "a", .symbol "b"],
          .expression [.symbol "P", .symbol "c", .symbol "d"]] = tree := rfl
    unfold cells
    rw [← whole, Nodes.recurse_node]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← left, ← right, Nodes.recurse_node, Nodes.recurse_node]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Nodes.recurse_of_none _ _ _ leafA, Nodes.recurse_of_none _ _ _ leafB,
      Nodes.recurse_of_none _ _ _ leafC, Nodes.recurse_of_none _ _ _ leafD]
  · have : tree = (last "P" 1).build ⟨[⟨[.expression [.symbol "P", .symbol "a", .symbol "b"]], rfl⟩,
        ⟨[.symbol "c"], rfl⟩], .symbol "d"⟩ := rfl
    rw [this, (last "P" 1).spine_build_of_canonical (s := ⟨_, .symbol "d"⟩) rfl]
    rfl

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.NodeFamilies
