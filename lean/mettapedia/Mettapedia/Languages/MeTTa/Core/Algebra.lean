import Mettapedia.Languages.MeTTa.Core.Atomspace
import Mettapedia.Languages.MeTTa.Core.State
import Mettapedia.Languages.MeTTa.Core.Bridge
import Mathlib.Algebra.Group.Defs

/-!
# Algebraic Structures in MeTTa

This file establishes the formal algebraic structures underlying MeTTa:

1. **Atomspace**: Commutative monoid under union (from Multiset)
2. **HashBag (parallel composition)**: Commutative monoid (isomorphic to Atomspace)
3. **State registers**: Multiset-valued, with monoid homomorphisms
4. **Transitions**: Multiset of states (non-determinism monad)

## Key Connections

```
MeTTaIL Pattern                    MeTTaCore Atom
    .collection .hashBag ps  ────►  Atomspace.ofList (ps.map patternToAtom)
                                          │
                                          ▼
                               Commutative Monoid (∪, ∅)
```

The bridge preserves the monoid structure:
- `patternToAtom` on union = union of `patternToAtom`
- Empty parallel = empty atomspace

## References

* Meta-MeTTa paper: multiset semantics
* OSLF paper: process algebra
-/

namespace Mettapedia.Languages.MeTTa.Core.Algebra

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.Core.Bridge

/-! ## Atomspace Commutative Monoid -/

/-- Atomspace union is associative -/
theorem atomspace_add_assoc (s1 s2 s3 : Atomspace) :
    (s1 ∪ s2) ∪ s3 = s1 ∪ (s2 ∪ s3) := union_assoc s1 s2 s3

/-- Atomspace union is commutative -/
theorem atomspace_add_comm (s1 s2 : Atomspace) :
    s1 ∪ s2 = s2 ∪ s1 := union_comm s1 s2

/-- Empty is left identity -/
theorem atomspace_zero_add (s : Atomspace) :
    ∅ ∪ s = s := union_empty_left s

/-- Empty is right identity -/
theorem atomspace_add_zero (s : Atomspace) :
    s ∪ ∅ = s := union_empty_right s

/-- Atomspace forms a commutative monoid (statement).
    The actual instance would require more infrastructure, but the laws hold. -/
theorem atomspace_is_comm_monoid :
    (∀ s1 s2 s3 : Atomspace, (s1 ∪ s2) ∪ s3 = s1 ∪ (s2 ∪ s3)) ∧
    (∀ s1 s2 : Atomspace, s1 ∪ s2 = s2 ∪ s1) ∧
    (∀ s : Atomspace, ∅ ∪ s = s) ∧
    (∀ s : Atomspace, s ∪ ∅ = s) :=
  ⟨atomspace_add_assoc, atomspace_add_comm, atomspace_zero_add, atomspace_add_zero⟩

/-! ## HashBag to Atomspace Bridge -/

/-- Convert a MeTTaIL hashBag pattern to an Atomspace.
    This is the semantic interpretation of parallel composition. -/
def hashBagToAtomspace (ps : List Pattern) : Atomspace :=
  Atomspace.ofList (ps.map patternToAtom)

/-- Empty parallel composition maps to empty atomspace -/
theorem hashBag_empty : hashBagToAtomspace [] = Atomspace.empty := rfl

/-- Singleton parallel composition maps to singleton atomspace -/
theorem hashBag_singleton (p : Pattern) :
    hashBagToAtomspace [p] = Atomspace.empty.add (patternToAtom p) := by
  simp [hashBagToAtomspace, Atomspace.ofList, Atomspace.addMany, Atomspace.add, Atomspace.empty]

/-- Atomspace extensionality: two atomspaces are equal iff their atoms are equal -/
@[ext] lemma Atomspace.ext' {s1 s2 : Atomspace} (h : s1.atoms = s2.atoms) : s1 = s2 := by
  cases s1; cases s2; simp_all

/-- Helper: addMany only depends on atoms field -/
private lemma addMany_atoms_ext (s1 s2 : Atomspace) (h : s1.atoms = s2.atoms) (as : List Atom) :
    (s1.addMany as).atoms = (s2.addMany as).atoms := by
  induction as generalizing s1 s2 with
  | nil => exact h
  | cons a as ih =>
    simp only [Atomspace.addMany, List.foldl_cons]
    apply ih
    simp only [Atomspace.add, h]

/-- Helper: addMany on permuted lists gives equal atoms -/
private lemma addMany_perm_atoms (s : Atomspace) {as bs : List Atom} (h : as.Perm bs) :
    (s.addMany as).atoms = (s.addMany bs).atoms := by
  induction h generalizing s with
  | nil => rfl
  | cons x _ ih =>
    simp only [Atomspace.addMany, List.foldl_cons, Atomspace.add]
    exact ih (s.add x)
  | swap x y l =>
    simp only [Atomspace.addMany, List.foldl_cons, Atomspace.add]
    -- After adding y then x, vs adding x then y, we have swapped atoms
    -- Then foldl on the rest gives same result by addMany_atoms_ext
    apply addMany_atoms_ext
    exact Multiset.cons_swap x y s.atoms
  | trans _ _ ih1 ih2 => exact (ih1 s).trans (ih2 s)

/-- Parallel composition respects permutation (multiset semantics).
    Permuted lists yield equal atomspaces because Atomspace uses Multiset internally. -/
theorem hashBag_perm {ps qs : List Pattern} (h : ps.Perm qs) :
    hashBagToAtomspace ps = hashBagToAtomspace qs := by
  simp only [hashBagToAtomspace, Atomspace.ofList]
  have hmap : (ps.map patternToAtom).Perm (qs.map patternToAtom) := h.map patternToAtom
  apply Atomspace.ext'
  exact addMany_perm_atoms Atomspace.empty hmap

/-! ## State Transitions as Multiset -/

/-- State transitions form a monoid under multiset union -/
abbrev StateTransitions := Multiset MeTTaState

/-- Empty transition set -/
def emptyTransitions : StateTransitions := ∅

/-- Union of transition sets -/
def unionTransitions (t1 t2 : StateTransitions) : StateTransitions := t1 + t2

/-- Transitions form a commutative monoid (inherited from Multiset) -/
theorem transitions_is_comm_monoid :
    (∀ t1 t2 t3 : StateTransitions, (t1 + t2) + t3 = t1 + (t2 + t3)) ∧
    (∀ t1 t2 : StateTransitions, t1 + t2 = t2 + t1) ∧
    (∀ t : StateTransitions, ∅ + t = t) ∧
    (∀ t : StateTransitions, t + ∅ = t) :=
  ⟨fun _ _ _ => add_assoc _ _ _, fun _ _ => add_comm _ _,
   fun _ => zero_add _, fun _ => add_zero _⟩

/-! ## 4-Register State Algebra -/

/-- Total atom count across all registers (invariant under moves) -/
def totalAtomCount (s : MeTTaState) : Nat :=
  s.input.card + s.workspace.card + s.output.card

/-- Knowledge is preserved by workspace operations -/
theorem workspace_preserves_knowledge' (s : MeTTaState) (a : Atom) :
    (s.addWorkspace a).knowledge = s.knowledge := rfl

/-- Knowledge is preserved by output operations -/
theorem output_preserves_knowledge' (s : MeTTaState) (a : Atom) :
    (s.addOutput a).knowledge = s.knowledge := rfl

/-! ## Homomorphism: Size is Additive -/

/-- Size is a monoid homomorphism from Atomspace to ℕ -/
theorem size_add_hom (s1 s2 : Atomspace) :
    (s1 ∪ s2).size = s1.size + s2.size := union_size s1 s2

/-- Size of empty is zero -/
theorem size_zero : Atomspace.empty.size = 0 := empty_size

/-- Size respects the monoid laws -/
theorem size_is_monoid_hom :
    (Atomspace.empty.size = 0) ∧
    (∀ s1 s2 : Atomspace, (s1 ∪ s2).size = s1.size + s2.size) :=
  ⟨size_zero, size_add_hom⟩

/-! ## Connecting Pattern Syntax to Semantic Structure -/

/-- A MeTTaIL Pattern.collection with hashBag type represents a parallel composition -/
def isParallelComposition : Pattern → Bool
  | .collection .hashBag _ _ => true
  | _ => false

/-- Extract processes from a parallel composition -/
def getParallelProcesses : Pattern → Option (List Pattern)
  | .collection .hashBag ps _ => some ps
  | _ => none

/-- Parallel composition pattern has correct structure -/
theorem parallel_structure (ps : List Pattern) (rest : Option String) :
    getParallelProcesses (.collection .hashBag ps rest) = some ps := rfl

/-! ## RhoCalculus Parallel ↔ Atomspace -/

/-- The zero process (0 or PZero) corresponds to empty atomspace -/
theorem rho_zero_is_identity :
    hashBagToAtomspace [] = Atomspace.empty := rfl

/-- Query distributes over union (from Atomspace.lean) -/
theorem query_distributes (s1 s2 : Atomspace) (p : Atom) :
    (s1 ∪ s2).query p = s1.query p + s2.query p := query_union s1 s2 p

/-- Equations distribute over union (from Atomspace.lean) -/
theorem equations_distributes (s1 s2 : Atomspace) :
    (s1 ∪ s2).equations = s1.equations + s2.equations := equations_union s1 s2

/-- Insensitive is preserved under union (from Atomspace.lean) -/
theorem insensitive_preserved {s1 s2 : Atomspace} {t : Atom}
    (h1 : s1.insensitive t) (h2 : s2.insensitive t) :
    (s1 ∪ s2).insensitive t := insensitive_union h1 h2

/-! ## Summary

This file establishes:

1. ✅ `Atomspace` satisfies commutative monoid laws under union
2. ✅ `hashBagToAtomspace` respects permutation (multiset semantics)
3. ✅ `StateTransitions` is a commutative monoid
4. ✅ `size` is a monoid homomorphism
5. ✅ `query`, `equations` distribute over union
6. ✅ `insensitive` is preserved under union

**Key insight**: The MeTTaIL syntactic parallel composition `.collection .hashBag`
corresponds semantically to the Atomspace commutative monoid. This validates
the OSLF claim that processes form an algebra.

**Connection to OSLF**: The `possibly` and `rely` operators (from RhoCalculus/Reduction.lean)
form a Galois connection over this monoid structure, giving rise to the modal logic
interpretation of process types.

**Algebraic Summary**:

| Structure | Operation | Identity | Laws |
|-----------|-----------|----------|------|
| Atomspace | ∪ (union) | ∅ | Commutative Monoid |
| Transitions | + | ∅ | Commutative Monoid |
| size | homomorphism | 0 | Preserves + |
| query | distributes | ∅ | Homomorphism-like |
-/

end Mettapedia.Languages.MeTTa.Core.Algebra
