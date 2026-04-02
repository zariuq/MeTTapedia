import Mettapedia.GSLT.GraphTheory.BohmTree
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Basic

/-!
# Helper Lemmas for Böhm Tree Computation

This file provides infrastructure lemmas about the behavior of `toHNF`, `extractHNF`,
and `headReduce` on lambda terms and applications. These lemmas are needed to prove
congruence properties of Böhm trees.

## Main Results

* `extractHNF_lam_isSome` - extractHNF on lambda: succeeds iff body succeeds
* `toHNF_lam_hnf` - If body is in HNF, lambda term is immediately recognized
* `bohmTree_succ_eq_node_elim` - Decomposition of `.node` Böhm trees
* `bohmTree_succ_bot_of_toHNF_some` - If Böhm tree is ⊥ and toHNF succeeds, extractHNF fails
* `bohmTree_succ_of_toHNF_extractHNF` - Construct Böhm tree from toHNF + extractHNF
* `bohmTree_node_eq_structure` - Structural consequence of Böhm tree node equality

## References

- Barendregt, "The Lambda Calculus", Chapter 8-10
- Current formalization: BohmTree.lean
-/

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core

/-! ## extractHNF Behavior on Lambda Terms

`extractHNF_lam_some`, `extractHNF_lam_none` are imported from BohmTree.lean. -/

/-- Lambda term has extractHNF structure iff its body does. -/
theorem extractHNF_lam_isSome (t : LambdaTerm) :
    (extractHNF (.lam t)).isSome ↔ (extractHNF t).isSome := by
  constructor
  · intro h
    unfold extractHNF at h
    cases ht : extractHNF t with
    | none => simp [ht] at h
    | some val => simp
  · intro h
    unfold extractHNF
    cases ht : extractHNF t with
    | none => simp [ht] at h
    | some val => simp

/-! ## toHNF Behavior on Lambda Terms -/

/-- If a term's body is already in HNF, the lambda term is immediately recognized as in HNF. -/
theorem toHNF_lam_hnf (t : LambdaTerm) (fuel : Nat) :
    (extractHNF t).isSome →
    toHNF (fuel + 1) (.lam t) = some (.lam t) := by
  intro ht
  unfold toHNF
  have : (extractHNF (.lam t)).isSome := by
    rw [extractHNF_lam_isSome]
    exact ht
  simp only [this, ite_true]

/-! ## Böhm Tree Decomposition

These lemmas characterize how `bohmTree` values relate to the intermediate
`toHNF` and `extractHNF` computations. They are the correct way to reason
about Böhm tree structure.

Note: `bohmTree d t` at `d = n+1` internally computes
`toHNF (d * (d + 1) + 1) t` — the reduction fuel is determined by the depth. -/

/-- If `bohmTree (n+1) t` is a node, we can extract the underlying toHNF/extractHNF data. -/
theorem bohmTree_succ_eq_node_elim (t : LambdaTerm) (n k h : Nat) (args : List BohmTree)
    (hb : bohmTree (n + 1) t = .node k h args) :
    ∃ hnf argTerms,
      toHNF ((n + 1) * (n + 1 + 1) + 1) t = some hnf ∧
      extractHNF hnf = some (k, h, argTerms) ∧
      args = argTerms.map (bohmTree n) := by
  unfold bohmTree at hb
  simp only at hb
  split at hb
  · exact absurd hb BohmTree.noConfusion
  · rename_i hnf ht_eq
    split at hb
    · exact absurd hb BohmTree.noConfusion
    · rename_i k' h' argTerms hext_eq
      simp only [BohmTree.node.injEq] at hb
      obtain ⟨hk, hh, hargs⟩ := hb
      subst hk; subst hh
      exact ⟨hnf, argTerms, ht_eq, hext_eq, hargs.symm⟩

/-- If `bohmTree (n+1) t` is ⊥ and toHNF succeeds, then extractHNF must fail. -/
theorem bohmTree_succ_bot_of_toHNF_some (t : LambdaTerm) (n : Nat) (hnf : LambdaTerm)
    (hb : bohmTree (n + 1) t = .bot)
    (ht : toHNF ((n + 1) * (n + 1 + 1) + 1) t = some hnf) :
    extractHNF hnf = none := by
  unfold bohmTree at hb
  simp only at hb
  split at hb
  · rename_i ht_none
    simp_all
  · rename_i hnf' ht_some
    have heq : hnf' = hnf := by simp_all
    subst heq
    split at hb
    · rename_i hext_none
      exact hext_none
    · exact absurd hb BohmTree.noConfusion

/-- If toHNF and extractHNF both succeed, we can compute the Böhm tree directly. -/
theorem bohmTree_succ_of_toHNF_extractHNF (t : LambdaTerm) (n : Nat)
    (hnf : LambdaTerm) (k h : Nat) (argTerms : List LambdaTerm)
    (ht : toHNF ((n + 1) * (n + 1 + 1) + 1) t = some hnf)
    (hext : extractHNF hnf = some (k, h, argTerms)) :
    bohmTree (n + 1) t = .node k h (argTerms.map (bohmTree n)) := by
  unfold bohmTree
  simp only
  split
  · rename_i ht_none
    simp_all
  · rename_i hnf' ht_some
    have heq : hnf' = hnf := by simp_all
    subst heq
    split
    · rename_i hext_none
      simp_all
    · rename_i k' h' argTerms' hext_some
      have : (k', h', argTerms') = (k, h, argTerms) := by simp_all
      have hk : k' = k := by
        have := congr_arg (·.1) this
        simpa using this
      have hh : h' = h := by
        have := congr_arg (·.2.1) this
        simpa using this
      have hargs : argTerms' = argTerms := by
        have := congr_arg (·.2.2) this
        simpa using this
      subst hk; subst hh; subst hargs
      rfl

/-- Key structural consequence: if two terms have the same `.node` Böhm tree,
    both have matching extractHNF structure and their arguments are pointwise
    Böhm-equal at depth `n`. -/
theorem bohmTree_node_eq_structure (t t' : LambdaTerm) (n k h : Nat) (args : List BohmTree)
    (ht  : bohmTree (n + 1) t  = .node k h args)
    (ht' : bohmTree (n + 1) t' = .node k h args) :
    ∃ hnf hnf' argTerms argTerms',
      toHNF ((n + 1) * (n + 1 + 1) + 1) t  = some hnf  ∧
      toHNF ((n + 1) * (n + 1 + 1) + 1) t' = some hnf' ∧
      extractHNF hnf  = some (k, h, argTerms)  ∧
      extractHNF hnf' = some (k, h, argTerms') ∧
      argTerms.map (bohmTree n)  = args ∧
      argTerms'.map (bohmTree n) = args := by
  obtain ⟨hnf, argTerms, htoHNF, hext, hargs⟩ := bohmTree_succ_eq_node_elim t n k h args ht
  obtain ⟨hnf', argTerms', htoHNF', hext', hargs'⟩ :=
    bohmTree_succ_eq_node_elim t' n k h args ht'
  exact ⟨hnf, hnf', argTerms, argTerms', htoHNF, htoHNF', hext, hext',
         hargs.symm, hargs'.symm⟩

/-! ## extractHNF Behavior on Applications

`extractHNF_app_var` is imported from BohmTree.lean. -/

/-! ## Summary

This file establishes the computational infrastructure needed for Böhm tree congruence proofs.
The key insight is that Böhm tree structure is characterized by `toHNF` + `extractHNF` + recursive
`bohmTree` on arguments. The `bohmTree_succ_eq_node_elim` and `bohmTree_node_eq_structure`
lemmas provide the canonical decomposition for reasoning about `.node` Böhm trees.

**Design note**: An earlier version contained `bohmTree_eq_imp_toHNF_eq` which claimed that
Böhm tree equality implies `toHNF` term-level equality. This is false: two terms can have
different `toHNF` results (e.g., one fails while the other succeeds but `extractHNF` rejects
the result) yet both yield `BohmTree.bot`. The correct decomposition works through Böhm tree
VALUES directly, using the elimination and construction lemmas above.
-/

end Mettapedia.GSLT.GraphTheory
