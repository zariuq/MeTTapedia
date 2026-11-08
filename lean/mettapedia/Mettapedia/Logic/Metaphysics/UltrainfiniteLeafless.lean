import Mathlib.Data.Countable.Basic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RationalTrees
import Mettapedia.Logic.Metaphysics.UltrainfiniteLawvere

/-!
# Plurality needs labels: the leafless trees

A tree read at its paths (`Rational.Raw`) is **leafless** (`Leafless`) when it is well formed and
every label in it has a child. Leafless trees have no variable or constant leaves, so they are
built from function symbols of positive arity alone.

* **No leafless tree is finite**: it is present at infinitely many paths (`Leafless.infinite_support`),
  and no finite term reads as one (`not_leafless_ofTerm`).
* **Two symbols give uncountably many** (`not_countable_setOf_leafless`): over two distinct symbols
  `f`, `g` of positive arity, the stream trees whose label at depth `n` is `f` or `g` as a Boolean
  sequence says (`streamTree`) are leafless and pairwise distinct (`boolStreamTree_injective`).
* **The rational ones are countable** (`countable_leafless_rational`) when the symbols are: each is
  the unfolding of a finite code (`decode`, `exists_decode_eq`). So some leafless tree is not rational
  (`exists_leafless_not_rational`).
* **Identity is by labels at paths, and no bounded observation decides it**
  (`exists_ne_agree_below`): for every depth `d` there are two distinct leafless trees with the same
  label at every path shorter than `d`.

**Control: one symbol, one tree** (`leafless_unique_of_subsingleton`). When there is at most one
function symbol, any two leafless trees are equal: with a single unary symbol the only leafless tree
is `f(f(f(…)))`, and its membership reading is the Quine atom of `UltrainfiniteSinkless`. Plurality
among leafless wholes comes from labels, never from leaves.

The trees are functions from paths to labels; paths are finite lists, which is the presentation.
The statement "no finite part" is about the tree: no leaf, no finite support, no finite subtree.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Rational
open Raw

variable {σ : LPSignature}

/-- **A leafless tree**: well formed, and every label present has a child. -/
def Leafless (t : Raw σ) : Prop := WF t ∧ ∀ p h, t p = some h → 0 < h.arity

/-- A label with a child is a function symbol. -/
theorem eq_fn_of_arity_pos {h : Head σ} (pos : 0 < h.arity) : ∃ f, h = .fn f := by
  cases h with
  | var v => exact absurd pos (Nat.lt_irrefl 0)
  | const c => exact absurd pos (Nat.lt_irrefl 0)
  | fn f => exact ⟨f, rfl⟩

namespace Leafless

variable {t : Raw σ}

theorem root_fn (l : Leafless t) : ∃ f, t [] = some (.fn f) ∧ 0 < σ.functionArity f := by
  obtain ⟨h, root⟩ := l.1.root_some
  obtain ⟨f, rfl⟩ := eq_fn_of_arity_pos (l.2 [] h root)
  exact ⟨f, root, l.2 [] _ root⟩

theorem child' (l : Leafless t) {h : Head σ} (root : t [] = some h) {i : ℕ} (inside : i < h.arity) :
    Leafless (child i t) :=
  ⟨l.1.child_wf root inside, fun p h' found => l.2 (i :: p) h' found⟩

theorem child_zero (l : Leafless t) : Leafless (child 0 t) :=
  let ⟨h, root⟩ := l.1.root_some
  l.child' root (l.2 [] h root)

theorem present_replicate (l : Leafless t) (n : ℕ) : t (List.replicate n 0) ≠ none := by
  induction n generalizing t with
  | zero => exact l.1.root
  | succ n ih => exact ih l.child_zero

/-- **No leafless tree is finite**: it is present at infinitely many paths. -/
theorem infinite_support (l : Leafless t) : {p | t p ≠ none}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => List.replicate n 0)
    (fun m n same => by simpa using congrArg List.length same) l.present_replicate

/-- Every subtree of a leafless tree is leafless, so none is finite. -/
theorem sub {p : List ℕ} (l : Leafless t) (present : t p ≠ none) : Leafless (Raw.sub p t) :=
  ⟨l.1.sub_wf present, fun q h found => l.2 (p ++ q) h found⟩

theorem infinite_support_sub {p : List ℕ} (l : Leafless t) (present : t p ≠ none) :
    {q | Raw.sub p t q ≠ none}.Infinite :=
  (l.sub present).infinite_support

end Leafless

/-- **No finite term reads as a leafless tree.** -/
theorem not_leafless_ofTerm (u : Term σ) : ¬ Leafless (ofTerm u) := by
  induction u with
  | var v => exact fun l => absurd (l.2 [] _ rfl) (Nat.lt_irrefl 0)
  | const c => exact fun l => absurd (l.2 [] _ rfl) (Nat.lt_irrefl 0)
  | app f ts ih =>
    intro l
    have pos : 0 < σ.functionArity f := l.2 [] (.fn f) rfl
    have kid := l.child_zero
    rw [show child 0 (ofTerm (.app f ts)) = ofTerm (ts ⟨0, pos⟩) from ofTerm_app_child ts ⟨0, pos⟩]
      at kid
    exact ih _ kid

/-! ## Stream trees: the label at depth `n` is `c n` -/

/-- Every label of an unfolding is the label of a node. -/
theorem Graph.exists_label_of_unfold {N : Type*} (G : Graph σ N) (p : List ℕ) :
    ∀ (k : N) {h : Head σ}, G.unfold k p = some h → ∃ k', G.label k' = h := by
  induction p with
  | nil => exact fun k _ found => ⟨k, Option.some.inj found⟩
  | cons i q ih =>
    intro k h found
    have step : G.unfoldAt (i :: q) k = some h := found
    by_cases inside : i < (G.label k).arity
    · rw [Graph.unfoldAt, if_pos inside] at step
      exact ih _ step
    · rw [Graph.unfoldAt, if_neg inside] at step
      cases step

/-- The graph on depths: node `n` is labelled `c n` and all its children are `n + 1`. -/
def streamGraph (c : ℕ → σ.functionSymbols) : Graph σ ℕ where
  label n := .fn (c n)
  edge n _ := n + 1

/-- **The stream tree** of `c`: label `c n` at depth `n`. -/
def streamTree (c : ℕ → σ.functionSymbols) : Raw σ := (streamGraph c).unfold 0

theorem leafless_streamTree {c : ℕ → σ.functionSymbols} (pos : ∀ n, 0 < σ.functionArity (c n)) :
    Leafless (streamTree c) :=
  ⟨(streamGraph c).wf_unfold 0, fun p _ found => by
    obtain ⟨k, rfl⟩ := Graph.exists_label_of_unfold _ p 0 found
    exact pos k⟩

theorem streamGraph_unfold_replicate {c : ℕ → σ.functionSymbols}
    (pos : ∀ n, 0 < σ.functionArity (c n)) (n : ℕ) :
    ∀ k, (streamGraph c).unfold k (List.replicate n 0) = some (.fn (c (k + n))) := by
  induction n with
  | zero => exact fun k => rfl
  | succ n ih =>
    intro k
    have step : (streamGraph c).unfoldAt (0 :: List.replicate n 0) k =
        (streamGraph c).unfoldAt (List.replicate n 0) (k + 1) := if_pos (pos k)
    show (streamGraph c).unfoldAt (0 :: List.replicate n 0) k = _
    rw [step, show k + (n + 1) = k + 1 + n by omega]
    exact ih (k + 1)

/-- Stream trees agree on every path shorter than the depth to which their labels agree. -/
theorem streamGraph_unfold_congr {c c' : ℕ → σ.functionSymbols} (p : List ℕ) :
    ∀ k k', (∀ j ≤ p.length, c (k + j) = c' (k' + j)) →
      (streamGraph c).unfold k p = (streamGraph c').unfold k' p := by
  induction p with
  | nil =>
    intro k k' same
    have root : c k = c' k' := by simpa using same 0 (Nat.zero_le _)
    show some (Head.fn (c k)) = some (Head.fn (c' k'))
    rw [root]
  | cons i q ih =>
    intro k k' same
    have root : c k = c' k' := by simpa using same 0 (Nat.zero_le _)
    have rest : ∀ j ≤ q.length, c (k + 1 + j) = c' (k' + 1 + j) := fun j hj => by
      have := same (j + 1) (by simp; omega)
      rwa [show k + (j + 1) = k + 1 + j by omega, show k' + (j + 1) = k' + 1 + j by omega] at this
    show (streamGraph c).unfoldAt (i :: q) k = (streamGraph c').unfoldAt (i :: q) k'
    by_cases inside : i < σ.functionArity (c k)
    · have inside' : i < σ.functionArity (c' k') := root ▸ inside
      have left : (streamGraph c).unfoldAt (i :: q) k = (streamGraph c).unfoldAt q (k + 1) :=
        if_pos inside
      have right : (streamGraph c').unfoldAt (i :: q) k' = (streamGraph c').unfoldAt q (k' + 1) :=
        if_pos inside'
      rw [left, right]
      exact ih _ _ rest
    · have inside' : ¬ i < σ.functionArity (c' k') := root ▸ inside
      have left : (streamGraph c).unfoldAt (i :: q) k = none := if_neg inside
      have right : (streamGraph c').unfoldAt (i :: q) k' = none := if_neg inside'
      rw [left, right]

/-! ## Two symbols: uncountably many leafless trees -/

section TwoSymbols

variable {f g : σ.functionSymbols}

/-- The symbol sequence of a Boolean sequence: `f` where it is `true`, `g` where it is `false`. -/
def boolSymbols (f g : σ.functionSymbols) (b : ℕ → Bool) : ℕ → σ.functionSymbols :=
  fun n => if b n then f else g

theorem boolSymbols_pos (pf : 0 < σ.functionArity f) (pg : 0 < σ.functionArity g) (b : ℕ → Bool) :
    ∀ n, 0 < σ.functionArity (boolSymbols f g b n) := fun n => by
  unfold boolSymbols
  split
  · exact pf
  · exact pg

/-- **Distinct Boolean sequences give distinct trees.** -/
theorem boolStreamTree_injective (apart : f ≠ g) (pf : 0 < σ.functionArity f)
    (pg : 0 < σ.functionArity g) :
    Function.Injective fun b : ℕ → Bool => streamTree (boolSymbols f g b) := by
  intro b b' same
  funext n
  have at_n := congrFun same (List.replicate n 0)
  simp only [streamTree, streamGraph_unfold_replicate (boolSymbols_pos pf pg _), zero_add,
    Option.some.injEq, Head.fn.injEq] at at_n
  unfold boolSymbols at at_n
  cases hb : b n <;> cases hb' : b' n <;> simp only [hb, hb'] at at_n <;>
    first | rfl | exact absurd at_n apart | exact absurd at_n.symm apart

/-- **Over two symbols of positive arity the leafless trees are uncountable.** -/
theorem not_countable_setOf_leafless (apart : f ≠ g) (pf : 0 < σ.functionArity f)
    (pg : 0 < σ.functionArity g) : ¬ {t : Raw σ | Leafless t}.Countable := by
  intro countable
  have := countable.to_subtype
  have inj : Function.Injective fun b : ℕ → Bool =>
      (⟨streamTree (boolSymbols f g b), leafless_streamTree (boolSymbols_pos pf pg b)⟩ :
        {t : Raw σ | Leafless t}) :=
    fun b b' same => boolStreamTree_injective apart pf pg (congrArg Subtype.val same)
  have : Countable (ℕ → Bool) := inj.countable
  obtain ⟨e, surjective⟩ := exists_surjective_nat (ℕ → Bool)
  exact not_surjective_bool e surjective

/-- **No bounded observation decides a leafless tree**: at every depth there are two distinct
leafless trees with the same labels at all shorter paths. -/
theorem exists_ne_agree_below (apart : f ≠ g) (pf : 0 < σ.functionArity f)
    (pg : 0 < σ.functionArity g) (d : ℕ) :
    ∃ s t : Raw σ, Leafless s ∧ Leafless t ∧ s ≠ t ∧ ∀ p : List ℕ, p.length < d → s p = t p := by
  refine ⟨streamTree (boolSymbols f g fun _ => true),
    streamTree (boolSymbols f g fun n => decide (n < d)),
    leafless_streamTree (boolSymbols_pos pf pg _), leafless_streamTree (boolSymbols_pos pf pg _),
    fun same => ?_, fun p short => streamGraph_unfold_congr p 0 0 fun j hj => ?_⟩
  · have := congrFun (boolStreamTree_injective apart pf pg same) d
    simp at this
  · have below : j < d := by omega
    simp [boolSymbols, below]

end TwoSymbols

/-! ## The rational leafless trees are countable -/

/-- **A finite code**: a number of nodes, and for each node a symbol with a child for each of its
positions, and a root. -/
abbrev Code (σ : LPSignature) :=
  Σ n : ℕ, (Fin n → Σ f : σ.functionSymbols, Fin (σ.functionArity f) → Fin n) × Fin n

/-- The graph of a code. -/
def codeGraph {n : ℕ} (d : Fin n → Σ f : σ.functionSymbols, Fin (σ.functionArity f) → Fin n) :
    Graph σ (Fin n) where
  label k := .fn (d k).1
  edge k i := if inside : i < σ.functionArity (d k).1 then (d k).2 ⟨i, inside⟩ else k

/-- The tree a code presents. -/
def decode (c : Code σ) : Raw σ := (codeGraph c.2.1).unfold c.2.2

/-- **Every rational leafless tree has a finite code.** -/
theorem exists_decode_eq {t : Raw σ} (l : Leafless t) (r : IsRational t) : ∃ c : Code σ, decode c = t := by
  have := (rational_subtrees_finite r).to_subtype
  let e := Finite.equivFin (Subtrees t)
  have fn : ∀ u : Subtrees t, ∃ f, Subtrees.label u = .fn f := fun u => by
    obtain ⟨p, -, same⟩ := u.2
    have root := Subtrees.label_spec u
    rw [same] at root
    exact eq_fn_of_arity_pos (l.2 (p ++ []) _ root)
  choose sym hsym using fn
  let d : Fin (Nat.card (Subtrees t)) →
      Σ f : σ.functionSymbols, Fin (σ.functionArity f) → Fin (Nat.card (Subtrees t)) :=
    fun k => ⟨sym (e.symm k), fun i => e ((subtreeGraph l.1).edge (e.symm k) i)⟩
  have solves : (codeGraph d).Solves fun k => (e.symm k).1 := by
    intro k
    show (e.symm k).1 = _
    conv_lhs => rw [← subtreeGraph_unfold l.1 (e.symm k), (subtreeGraph l.1).unfold_eq]
    show node (Subtrees.label (e.symm k)) (fun i => (subtreeGraph l.1).unfold
        ((subtreeGraph l.1).edge (e.symm k) i)) =
      node (.fn (sym (e.symm k))) fun i => (e.symm ((codeGraph d).edge k i)).1
    rw [hsym]
    refine node_congr fun i inside => ?_
    have edge : (codeGraph d).edge k i = e ((subtreeGraph l.1).edge (e.symm k) i) := dif_pos inside
    rw [edge, Equiv.symm_apply_apply, subtreeGraph_unfold]
  refine ⟨⟨_, d, e ⟨t, [], l.1.root, rfl⟩⟩, ?_⟩
  have at_root := (codeGraph d).solves_unique solves (e ⟨t, [], l.1.root, rfl⟩)
  simp only [Equiv.symm_apply_apply] at at_root
  exact at_root.symm

/-- **The rational leafless trees are countable** when the symbols are. -/
theorem countable_leafless_rational [Countable σ.functionSymbols] :
    {t : Raw σ | Leafless t ∧ IsRational t}.Countable :=
  (Set.countable_range (decode (σ := σ))).mono fun _ ⟨l, r⟩ => exists_decode_eq l r

/-- **Some leafless tree is not rational**, over countably many symbols two of which have positive
arity. -/
theorem exists_leafless_not_rational [Countable σ.functionSymbols] {f g : σ.functionSymbols}
    (apart : f ≠ g) (pf : 0 < σ.functionArity f) (pg : 0 < σ.functionArity g) :
    ∃ t : Raw σ, Leafless t ∧ ¬ IsRational t := by
  by_contra none
  refine not_countable_setOf_leafless apart pf pg (countable_leafless_rational.mono fun t l => ?_)
  exact ⟨l, by_contra fun notRational => none ⟨t, l, notRational⟩⟩

/-! ## Control: one symbol, one tree -/

/-- **With at most one function symbol, any two leafless trees are equal.** -/
theorem leafless_unique_of_subsingleton [Subsingleton σ.functionSymbols] {s t : Raw σ}
    (ls : Leafless s) (lt : Leafless t) : s = t := by
  refine eq_of_bisim_or (fun a b => Leafless a ∧ Leafless b) (fun a b ⟨la, lb⟩ => ?_) ⟨ls, lt⟩
  obtain ⟨f, ra, -⟩ := la.root_fn
  obtain ⟨f', rb, -⟩ := lb.root_fn
  have same : f = f' := Subsingleton.elim f f'
  subst same
  refine Or.inr ⟨ra.trans rb.symm, fun i => ?_⟩
  by_cases inside : i < (Head.fn (σ := σ) f).arity
  · exact Or.inr ⟨la.child' ra inside, lb.child' rb inside⟩
  · exact Or.inl ((la.1.child_eq_bot ra (not_lt.mp inside)).trans
      (lb.1.child_eq_bot rb (not_lt.mp inside)).symm)

/-- With one symbol of positive arity the leafless tree exists, so there is exactly one. -/
theorem existsUnique_leafless_of_subsingleton [Subsingleton σ.functionSymbols]
    (f : σ.functionSymbols) (pf : 0 < σ.functionArity f) : ∃! t : Raw σ, Leafless t :=
  ⟨streamTree fun _ => f, leafless_streamTree fun _ => pf,
    fun _ l => leafless_unique_of_subsingleton l (leafless_streamTree fun _ => pf)⟩

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms Leafless.infinite_support
#print axioms Leafless.infinite_support_sub
#print axioms not_leafless_ofTerm
#print axioms leafless_streamTree
#print axioms streamGraph_unfold_replicate
#print axioms streamGraph_unfold_congr
#print axioms boolStreamTree_injective
#print axioms not_countable_setOf_leafless
#print axioms exists_ne_agree_below
#print axioms exists_decode_eq
#print axioms countable_leafless_rational
#print axioms exists_leafless_not_rational
#print axioms leafless_unique_of_subsingleton
#print axioms existsUnique_leafless_of_subsingleton

end Mettapedia.Logic.Metaphysics.Ultrainfinite
