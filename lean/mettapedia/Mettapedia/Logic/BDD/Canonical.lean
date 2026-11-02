import Mettapedia.Logic.BDD.StatePredicates

/-!
# Semantic canonicity of the existing reduced ordered BDD carrier

Two well-formed diagrams with the fixed coordinate order represent the same
Boolean function exactly when their trees are equal. The proof uses Shannon
restrictions and independence below each ordered root; it does not define a
normal form by choosing an equivalence-class representative.

This supplies a semantic key law. Physical hash-consed IDs additionally need
an injective intern table, valid lifetimes and a fixed universe/revision.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.Canonical

open StatePredicates

variable {n : Nat}

def nodes : BDD n → Nat
  | .zero | .one => 1
  | .node _ low high => 1 + nodes low + nodes high

theorem ordered_true_one (tree : BDD n) {bound : Option (Fin n)}
    (ordered : tree.Ordered bound) (tautology : ∀ state, tree.eval state = true) : tree = .one := by
  induction tree generalizing bound with
  | zero => have impossible := tautology (fun _ => false); cases impossible
  | one => rfl
  | node v low high ihl ihh =>
      cases ordered with
      | node _ lower higher different =>
          have lowOne : low = .one := by
            apply ihl lower
            intro state
            have value := tautology (Function.update state v false)
            simpa only [BDD.eval, Function.update_self, Bool.false_eq_true, ↓reduceIte,
              BDD.eval_independent low lower state v le_rfl false] using value
          have highOne : high = .one := by
            apply ihh higher
            intro state
            have value := tautology (Function.update state v true)
            simpa only [BDD.eval, Function.update_self, ↓reduceIte,
              BDD.eval_independent high higher state v le_rfl true] using value
          exact False.elim (different (lowOne.trans highOne.symm))

theorem ordered_ext (left right : BDD n) {firstBound secondBound : Option (Fin n)}
    (first : left.Ordered firstBound) (second : right.Ordered secondBound)
    (same : ∀ state, left.eval state = right.eval state) : left = right := by
  have aux : ∀ size (left right : BDD n), nodes left + nodes right = size →
      ∀ firstBound secondBound, left.Ordered firstBound → right.Ordered secondBound →
        (∀ state, left.eval state = right.eval state) → left = right := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro left right sizeEq firstBound secondBound first second same
      cases left with
      | zero => exact (ordered_unsat_zero right second (fun state => (same state).symm)).symm
      | one => exact (ordered_true_one right second (fun state => (same state).symm)).symm
      | node v low high =>
        cases right with
        | zero => exact ordered_unsat_zero _ first same
        | one => exact ordered_true_one _ first same
        | node w lower higher =>
          cases first with
          | node _ lowOrder highOrder distinct =>
            cases second with
            | node _ lowerOrder higherOrder otherDistinct =>
              by_cases equal : v = w
              · subst w
                have lows : low = lower := by
                  apply ih (nodes low + nodes lower) (by simp only [nodes] at sizeEq; omega)
                    low lower rfl (some v) (some v) lowOrder lowerOrder
                  intro state
                  have compared := same (Function.update state v false)
                  simpa only [BDD.eval, Function.update_self, Bool.false_eq_true, ↓reduceIte,
                    BDD.eval_independent low lowOrder state v le_rfl false,
                    BDD.eval_independent lower lowerOrder state v le_rfl false] using compared
                have highs : high = higher := by
                  apply ih (nodes high + nodes higher) (by simp only [nodes] at sizeEq; omega)
                    high higher rfl (some v) (some v) highOrder higherOrder
                  intro state
                  have compared := same (Function.update state v true)
                  simpa only [BDD.eval, Function.update_self, ↓reduceIte,
                    BDD.eval_independent high highOrder state v le_rfl true,
                    BDD.eval_independent higher higherOrder state v le_rfl true] using compared
                simp [lows, highs]
              · rcases lt_or_gt_of_ne equal with earlier | later
                · have rightOrder : (BDD.node w lower higher).Ordered (some v) :=
                    .node (by intro b equal; cases equal; exact earlier) lowerOrder higherOrder otherDistinct
                  have restrictions (state : State n) : low.eval state = high.eval state := by
                    have a := same (Function.update state v false)
                    have b := same (Function.update state v true)
                    rw [BDD.eval_independent _ rightOrder state v le_rfl false] at a
                    rw [BDD.eval_independent _ rightOrder state v le_rfl true] at b
                    simp only [BDD.eval, Function.update_self, Bool.false_eq_true, ↓reduceIte,
                      BDD.eval_independent low lowOrder state v le_rfl false] at a
                    simp only [BDD.eval, Function.update_self, ↓reduceIte,
                      BDD.eval_independent high highOrder state v le_rfl true] at b
                    exact a.trans b.symm
                  exact False.elim (distinct (ih (nodes low + nodes high)
                    (by simp only [nodes] at sizeEq; omega) low high rfl
                    (some v) (some v) lowOrder highOrder restrictions))
                · have leftOrder : (BDD.node v low high).Ordered (some w) :=
                    .node (by intro b equal; cases equal; exact later) lowOrder highOrder distinct
                  have restrictions (state : State n) : lower.eval state = higher.eval state := by
                    have a := same (Function.update state w false)
                    have b := same (Function.update state w true)
                    rw [BDD.eval_independent _ leftOrder state w le_rfl false] at a
                    rw [BDD.eval_independent _ leftOrder state w le_rfl true] at b
                    simp only [BDD.eval, Function.update_self, Bool.false_eq_true, ↓reduceIte,
                      BDD.eval_independent lower lowerOrder state w le_rfl false] at a
                    simp only [BDD.eval, Function.update_self, ↓reduceIte,
                      BDD.eval_independent higher higherOrder state w le_rfl true] at b
                    exact a.symm.trans b
                  exact False.elim (otherDistinct (ih (nodes lower + nodes higher)
                    (by simp only [nodes] at sizeEq; omega) lower higher rfl
                    (some w) (some w) lowerOrder higherOrder restrictions))
  exact aux (nodes left + nodes right) left right rfl firstBound secondBound first second same

theorem diagram_eq_iff_denote (left right : Diagram n) : left = right ↔ denote left = denote right := by
  constructor
  · rintro rfl; rfl
  · intro same
    apply Subtype.ext
    exact ordered_ext left.val right.val left.property right.property
      ((equivalent_iff left right).mp ((equivalent_denote left right).mpr same))

theorem equivalent_iff_equal (left right : Diagram n) : equivalent left right = true ↔ left = right :=
  (equivalent_denote left right).trans (diagram_eq_iff_denote left right).symm

theorem unreduced_tree_is_not_a_canonical_key :
    (∀ state : State 1, (BDD.node 0 .one .one).eval state = BDD.one.eval state) ∧
      (BDD.node (0 : Fin 1) .one .one) ≠ .one ∧
      ¬(BDD.node (0 : Fin 1) .one .one).WF := by
  refine ⟨fun state => by simp [BDD.eval], by decide, ?_⟩
  intro ordered
  cases ordered with
  | node _ _ _ different => exact different rfl

end Mettapedia.Logic.BDDCore.Canonical
