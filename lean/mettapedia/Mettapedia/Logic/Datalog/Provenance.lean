import Mettapedia.Logic.Datalog.Semantics
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.Set.Basic

/-!
# Datalog Provenance: Semiring Annotations (K-Relations)

This file formalizes the semiring provenance framework for Datalog:

- `SemiringWithMonus` — extends `CommSemiring` with a truncated subtraction.
- `KRelation` — an assignment of semiring values to ground atoms.
- `T_P_K` — the immediate consequence operator lifted to K-relations.
- `T_P_K_hom` — homomorphism theorem: semiring homomorphisms commute with `T_P_K`.

## References

- Green, Karvounarakis, Tannen, "Provenance Semirings", PODS 2007.

## API notes (Lean 4.27)

- `apply_ite f P x y : f (if P then x else y) = if P then f x else f y`.
- `map_list_prod : f l.prod = (l.map f).prod` for MonoidHomClass.
- `List.sum_congr` doesn't exist; use `congr 1; simp [List.map_map]` or list extensionality.
- For the ℕ instance of SemiringWithMonus: use `__ := inferInstance` syntax.
- `Nat.add_le_add_left h c : c + a ≤ c + b` when `h : a ≤ b`.
- `Nat.mul_le_mul_left c h : c * a ≤ c * b` when `h : a ≤ b`.
-/

namespace Mettapedia.Logic.Datalog

/-! ## Section 1: SemiringWithMonus -/

/-- A commutative semiring with a "monus" (truncated subtraction) operation and
    order-semiring compatibility laws.

    Extending `Preorder K` gives `le_refl` and `le_trans` for free.
    The two semiring-order axioms ensure ≤ is compatible with + and ×:
    - `add_le_add_of_le_left`: addition is monotone on the left.
    - `mul_le_mul_of_nonneg_left`: multiplication by a nonneg element is monotone. -/
class SemiringWithMonus (K : Type*) extends CommSemiring K, Preorder K where
  monus : K → K → K
  monus_add_cancel : ∀ a b : K, b ≤ a → monus a b + b = a
  add_le_add_of_le_left : ∀ a b c : K, a ≤ b → c + a ≤ c + b
  mul_le_mul_of_nonneg_left : ∀ a b c : K, a ≤ b → 0 ≤ c → c * a ≤ c * b

/-- The natural numbers form a `SemiringWithMonus` via truncated subtraction. -/
instance : SemiringWithMonus ℕ where
  __ := (inferInstance : CommSemiring ℕ)
  __ := (inferInstance : Preorder ℕ)
  monus := (· - ·)
  monus_add_cancel a b h := by omega
  add_le_add_of_le_left a b c h := Nat.add_le_add_left h c
  mul_le_mul_of_nonneg_left a b c h _ := Nat.mul_le_mul_left c h

/-! ## Section 2: K-Relations -/

/-- A K-relation: an assignment of semiring values to ground atoms.

    For `K = ℕ`, this counts the number of derivations (multiplicity provenance). -/
abbrev KRelation (τ : Signature) (K : Type*) := GroundAtom τ → K

/-! ## Section 3: T_P lifted to K-relations -/

/-- T_P lifted to K-relations (provenance-aware semantics). -/
noncomputable def T_P_K {τ : Signature}
    [Fintype τ.vars] [DecidableEq τ.vars]
    [Fintype τ.constants] [DecidableEq τ.constants]
    [DecidableEq τ.relationSymbols]
    (K : Type*) [CommSemiring K]
    (kb : KnowledgeBase τ) (I : KRelation τ K) : KRelation τ K :=
  fun (a : GroundAtom τ) =>
    (if a ∈ kb.db then (1 : K) else 0) +
    ∑ g : Grounding τ,
      (kb.prog.map (fun r =>
        if g.applyAtom r.head = a then
          (r.body.map (fun b => I (g.applyAtom b))).prod
        else 0)).sum

/-! ## Section 4: Homomorphism theorem -/

/-- The homomorphism theorem for K-relations: `h : K →+* K'` commutes with `T_P_K`. -/
theorem T_P_K_hom {τ : Signature}
    [Fintype τ.vars] [DecidableEq τ.vars]
    [Fintype τ.constants] [DecidableEq τ.constants]
    [DecidableEq τ.relationSymbols]
    {K K' : Type*} [CommSemiring K] [CommSemiring K']
    (h : K →+* K') (kb : KnowledgeBase τ) (I : KRelation τ K) :
    T_P_K K' kb (h ∘ I) = h ∘ T_P_K K kb I := by
  funext a
  simp only [T_P_K, Function.comp, map_add, map_sum, map_list_sum]
  congr 1
  · -- EDB part
    rw [apply_ite (h : K → K')]
    simp
  · -- Rules part: each (g, r)-contribution commutes with h
    apply Finset.sum_congr rfl
    intro g _
    -- Goal: (h ∘ rule_contributions).sum = (rule_contributions via h).sum
    -- Use: map_list_sum applied, then go element-wise
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro r _
    simp only [Function.comp]
    -- Goal: if head=a then (h∘I body).prod else 0 = h(if head=a then (I body).prod else 0)
    rw [apply_ite (h : K → K'), h.map_zero]
    split_ifs with hg
    · -- LHS: (List.map (fun b => h (I (g.applyAtom b))) r.body).prod
      -- RHS: h (List.map (fun b => I (g.applyAtom b)) r.body).prod
      -- map_list_prod: h l.prod = (l.map ↑h).prod; then List.map_map
      rw [map_list_prod, List.map_map]
      rfl
    · rfl

/-! ## Section 5: Support and Boolean collapse -/

/-- The support of a K-relation: atoms with nonzero weight. -/
noncomputable def KRelation.support {τ : Signature} {K : Type*} [Zero K] [DecidableEq K]
    (I : KRelation τ K) : Interpretation τ :=
  { a | I a ≠ 0 }

/-- The support of the indicator K-relation for `I` recovers `I`. -/
theorem support_indicator {τ : Signature}
    (I : Interpretation τ) [DecidablePred (· ∈ I)] :
    KRelation.support (fun (a : GroundAtom τ) => if a ∈ I then (1 : ℕ) else 0) = I := by
  ext a
  simp only [KRelation.support, Set.mem_setOf_eq]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => by decide⟩
  · simp [h]

end Mettapedia.Logic.Datalog
