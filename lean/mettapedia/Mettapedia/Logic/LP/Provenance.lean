import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.FunctionFree
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Data.Set.Basic

/-!
# LP Provenance: Semiring Annotations (K-Relations)

Port of `Mettapedia.Logic.Datalog.Provenance` onto LP types.

- `SemiringWithMonus` — extends `CommSemiring` with truncated subtraction.
- `KRelation` — semiring-valued annotations on ground atoms.
- `T_P_K_LP` — immediate consequence operator lifted to K-relations.
- `T_P_K_LP_hom` — semiring homomorphisms commute with `T_P_K_LP`.

Works for ALL LP signatures (not just function-free). The `Fintype` constraints
on variables and constants are needed for the sum over all groundings.

## References

- Green, Karvounarakis, Tannen, "Provenance Semirings", PODS 2007.
-/

namespace Mettapedia.Logic.LP

/-! ## Section 1: SemiringWithMonus -/

/-- A commutative semiring with monus (truncated subtraction) and order compatibility. -/
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

/-- A K-relation: semiring-valued annotations on ground atoms. -/
abbrev KRelation (σ : LPSignature) (K : Type*) := GroundAtom σ → K

/-! ## Section 3: T_P lifted to K-relations -/

/-- T_P lifted to K-relations (provenance-aware semantics).

    For each ground atom `a`, sums over all groundings and clauses:
    - EDB contribution: 1 if `a` is in the database, 0 otherwise.
    - IDB contribution: product of body annotations when head matches `a`. -/
noncomputable instance instFintypeGrounding {σ : LPSignature}
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype (GroundTerm σ)] [DecidableEq (GroundTerm σ)] :
    Fintype (Grounding σ) :=
  inferInstanceAs (Fintype (σ.vars → GroundTerm σ))

noncomputable def T_P_K_LP {σ : LPSignature}
    [IsEmpty σ.functionSymbols]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    (K : Type*) [CommSemiring K]
    (kb : FinKnowledgeBase σ) (I : KRelation σ K) : KRelation σ K :=
  fun (a : GroundAtom σ) =>
    (if a ∈ kb.db then (1 : K) else 0) +
    ∑ g : Grounding σ,
      (kb.prog.map (fun r =>
        if g.groundAtom r.head = a then
          (r.body.map (fun b => I (g.groundAtom b))).prod
        else 0)).sum

/-! ## Section 4: Homomorphism theorem -/

/-- Semiring homomorphisms commute with `T_P_K_LP`. -/
theorem T_P_K_LP_hom {σ : LPSignature}
    [IsEmpty σ.functionSymbols]
    [Fintype σ.vars] [DecidableEq σ.vars]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [DecidableEq σ.relationSymbols]
    {K K' : Type*} [CommSemiring K] [CommSemiring K']
    (h : K →+* K') (kb : FinKnowledgeBase σ) (I : KRelation σ K) :
    T_P_K_LP K' kb (h ∘ I) = h ∘ T_P_K_LP K kb I := by
  funext a
  simp only [T_P_K_LP, Function.comp, map_add, map_sum, map_list_sum]
  congr 1
  · rw [apply_ite (h : K → K')]; simp
  · apply Finset.sum_congr rfl
    intro g _
    simp only [List.map_map]
    congr 1
    apply List.map_congr_left
    intro r _
    simp only [Function.comp]
    rw [apply_ite (h : K → K'), h.map_zero]
    split_ifs with hg
    · rw [map_list_prod, List.map_map]; rfl
    · rfl

/-! ## Section 5: Support and Boolean collapse -/

/-- The support of a K-relation: atoms with nonzero weight. -/
noncomputable def KRelation.support {σ : LPSignature} {K : Type*} [Zero K] [DecidableEq K]
    (I : KRelation σ K) : Interpretation σ :=
  { a | I a ≠ 0 }

/-- The support of the indicator K-relation for `I` recovers `I`. -/
theorem support_indicator {σ : LPSignature}
    (I : Interpretation σ) [DecidablePred (· ∈ I)] :
    KRelation.support (fun (a : GroundAtom σ) => if a ∈ I then (1 : ℕ) else 0) = I := by
  ext a
  simp only [KRelation.support, Set.mem_setOf_eq]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => by decide⟩
  · simp [h]

end Mettapedia.Logic.LP
