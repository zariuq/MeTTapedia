import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.Group.End
import Mathlib.Data.Countable.Defs
import Mettapedia.Logic.Metaphysics.UltrainfiniteSinkless
import Mettapedia.Logic.Metaphysics.UltrainfiniteLawvere

/-!
# One with inner diversity: the full binary tree

Identity is kept as structure here, not as a proposition: a self-identification of a whole is an
explicit automorphism, a permutation of its nodes that keeps its edges.

The **full binary tree** has the paths `List Bool` as nodes and an edge from `p` to `p ++ [b]`
(`Child`). Each of its two subtrees below the root is again the full binary tree, so as an
iterated multiset it is `T = {T, T}`. It is sinkless.

* **Its automorphism group is uncountable** (`not_countable_treeAut`). At every node choose to
  swap its two children or not (`swapAt`, a choice `List Bool → Bool`); each choice is an
  automorphism (`swapPerm_mem_treeAut`), and distinct choices give distinct automorphisms
  (`swapPerm_injective`).
* **Control: as a set it is one thing with one self-identification.** Extensional collapse
  identifies the two members of `{T, T}`: the tree pictures the Quine atom at every node
  (`decorate_binaryTree`), so every automorphism of the tree pictures the same hyperset at a node
  and at its image (`decorate_comp_aut`). And every automorphism of the membership structure of
  hypersets is the identity (`eq_self_of_mem_automorphism`), by strong extensionality.

Reading: a single sinkless object, connected (one root reaches every node) but not contractible
(its self-identifications are not all equal). As objects all its self-identifications agree; as
structure there are uncountably many.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet

/-! ## The full binary tree -/

/-- The edges of the full binary tree: from a path to each of its two extensions. -/
def Child (p q : List Bool) : Prop := ∃ b, q = p ++ [b]

/-- **The automorphisms of the full binary tree**: the permutations of the paths that keep the
edges in both directions. -/
def treeAut : Subgroup (Equiv.Perm (List Bool)) where
  carrier := {π | ∀ p q, Child p q ↔ Child (π p) (π q)}
  one_mem' _ _ := Iff.rfl
  mul_mem' {π ρ} hπ hρ p q := (hρ p q).trans (hπ (ρ p) (ρ q))
  inv_mem' {π} hπ p q := by
    have := hπ (π⁻¹ p) (π⁻¹ q)
    rwa [show π (π⁻¹ p) = p from π.apply_symm_apply p, show π (π⁻¹ q) = q from π.apply_symm_apply q,
      Iff.comm] at this

/-- **Each subtree is the whole**: below the root, `p ↦ b :: p` keeps and reflects the edges, so the
subtree at `[b]` is again the full binary tree, and `T = {T, T}`. -/
theorem child_cons_iff (b : Bool) (p q : List Bool) : Child (b :: p) (b :: q) ↔ Child p q := by
  simp [Child]

/-! ## Swapping at chosen nodes -/

/-- Swap the children of each node `p` where `s p` holds: the first step at the root is flipped
when `s []` holds, and below the child reached the choices are those of that child. -/
def swapAt (s : List Bool → Bool) : List Bool → List Bool
  | [] => []
  | b :: q => (b ^^ s []) :: swapAt (fun r => s (b :: r)) q

/-- The inverse of `swapAt`. -/
def unswapAt (s : List Bool → Bool) : List Bool → List Bool
  | [] => []
  | b :: q => (b ^^ s []) :: unswapAt (fun r => s ((b ^^ s []) :: r)) q

theorem xor_xor_cancel (b c : Bool) : ((b ^^ c) ^^ c) = b := by
  cases b <;> cases c <;> rfl

theorem unswapAt_swapAt (s : List Bool → Bool) (p : List Bool) : unswapAt s (swapAt s p) = p := by
  induction p generalizing s with
  | nil => rfl
  | cons b q ih =>
    simp only [swapAt, unswapAt, xor_xor_cancel]
    exact congrArg (b :: ·) (ih _)

theorem swapAt_unswapAt (s : List Bool → Bool) (p : List Bool) : swapAt s (unswapAt s p) = p := by
  induction p generalizing s with
  | nil => rfl
  | cons b q ih =>
    simp only [swapAt, unswapAt, xor_xor_cancel]
    exact congrArg (b :: ·) (ih _)

/-- Swapping at chosen nodes as a permutation of the paths. -/
def swapPerm (s : List Bool → Bool) : Equiv.Perm (List Bool) where
  toFun := swapAt s
  invFun := unswapAt s
  left_inv := unswapAt_swapAt s
  right_inv := swapAt_unswapAt s

/-- The image of an extension: the last step is flipped when `s` holds at the parent. -/
theorem swapAt_append (s : List Bool → Bool) (p : List Bool) (b : Bool) :
    swapAt s (p ++ [b]) = swapAt s p ++ [b ^^ s p] := by
  induction p generalizing s with
  | nil => rfl
  | cons c p ih =>
    show (c ^^ s []) :: swapAt (fun r => s (c :: r)) (p ++ [b]) = _
    rw [ih]
    rfl

/-- **Each choice of swaps is an automorphism.** -/
theorem swapPerm_mem_treeAut (s : List Bool → Bool) : swapPerm s ∈ treeAut := by
  intro p q
  show Child p q ↔ Child (swapAt s p) (swapAt s q)
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b ^^ s p, swapAt_append s p b⟩
  · rintro ⟨c, image⟩
    refine ⟨c ^^ s p, (swapPerm s).injective ?_⟩
    show swapAt s q = swapAt s (p ++ [c ^^ s p])
    rw [swapAt_append, xor_xor_cancel, image]

/-- **Distinct choices give distinct automorphisms.** -/
theorem swapPerm_injective : Function.Injective swapPerm := by
  intro s s' same
  funext p
  have at_p := congrArg (fun π : Equiv.Perm (List Bool) => π (p ++ [false])) same
  simp only [swapPerm, Equiv.coe_fn_mk, swapAt_append] at at_p
  have prefixes : swapAt s p = swapAt s' p := congrArg (fun π : Equiv.Perm (List Bool) => π p) same
  rw [prefixes] at at_p
  have := List.append_cancel_left at_p
  simpa using this

/-- **The automorphism group of the full binary tree is uncountable.** -/
theorem not_countable_treeAut : ¬ Countable treeAut := by
  intro countable
  have inj : Function.Injective fun b : ℕ → Bool =>
      (⟨swapPerm fun p => b p.length, swapPerm_mem_treeAut _⟩ : treeAut) := by
    intro b b' same
    funext n
    have := congrFun (swapPerm_injective (congrArg Subtype.val same)) (List.replicate n false)
    simpa using this
  have : Countable (ℕ → Bool) := inj.countable
  obtain ⟨e, surjective⟩ := exists_surjective_nat (ℕ → Bool)
  exact not_surjective_bool e surjective

/-- A nontrivial automorphism: swap at the root only. -/
theorem swapRoot_ne_one : swapPerm (fun p => p.isEmpty) ≠ 1 := fun same => by
  have := congrArg (fun π : Equiv.Perm (List Bool) => π [false]) same
  simp [swapPerm, swapAt] at this

/-! ## Control: the extensional collapse -/

theorem child_sinkless (p : List Bool) : ∃ q, Child p q := ⟨p ++ [false], false, rfl⟩

/-- **As a set, the full binary tree is the Quine atom at every node.** -/
theorem decorate_binaryTree (p : List Bool) : decorate Child p = quineAtom :=
  decorate_eq_quineAtom_iff_sinkless.mpr fun b _ => child_sinkless b

/-- Every automorphism pictures the same hyperset at a node and at its image. -/
theorem decorate_comp_aut (π : Equiv.Perm (List Bool)) (p : List Bool) :
    decorate Child (π p) = decorate Child p := by
  rw [decorate_binaryTree, decorate_binaryTree]

/-- **Every automorphism of the membership structure of hypersets is the identity.** -/
theorem eq_self_of_mem_automorphism (π : HSet.{0} ≃ HSet.{0})
    (keeps : ∀ x y, y ∈ x ↔ π y ∈ π x) (x : HSet.{0}) : π x = x := by
  refine (eq_of_isBisimulation (R := fun a b => b = π a) ?_ rfl).symm
  rintro a _ rfl
  refine ⟨fun a' ha => ⟨π a', (keeps a a').mp ha, rfl⟩, fun b' hb => ⟨π.symm b', ?_, ?_⟩⟩
  · show π.symm b' ∈ a
    rw [keeps, Equiv.apply_symm_apply]
    exact hb
  · exact (Equiv.apply_symm_apply π b').symm

/-- **One whole, many self-identifications**: uncountably many automorphisms of the tree, all
picturing the one hyperset `Ω`, whose only ∈-automorphism is the identity. -/
theorem inner_diversity :
    ¬ Countable treeAut ∧ (∀ p, decorate Child p = quineAtom) ∧
      ∀ π : HSet.{0} ≃ HSet.{0}, (∀ x y, y ∈ x ↔ π y ∈ π x) → π quineAtom = quineAtom :=
  ⟨not_countable_treeAut, decorate_binaryTree, fun π keeps => eq_self_of_mem_automorphism π keeps _⟩

end Mettapedia.Logic.Metaphysics.Ultrainfinite

namespace Mettapedia.Logic.Metaphysics.Ultrainfinite

#print axioms treeAut
#print axioms child_cons_iff
#print axioms unswapAt_swapAt
#print axioms swapAt_unswapAt
#print axioms swapAt_append
#print axioms swapPerm_mem_treeAut
#print axioms swapPerm_injective
#print axioms not_countable_treeAut
#print axioms swapRoot_ne_one
#print axioms decorate_binaryTree
#print axioms decorate_comp_aut
#print axioms eq_self_of_mem_automorphism
#print axioms inner_diversity

end Mettapedia.Logic.Metaphysics.Ultrainfinite
