import Mettapedia.GSLT.Topos.PresheafPredicateReification
import Mathlib.CategoryTheory.Category.Preorder

/-!
# A worked consumer of function predicates over two stages

This file exercises the higher-order predicate machinery on a concrete base
where restriction is not the identity, so the quantification over restrictions
in `mem_expPredicate` does real work.

The base is the two-stage category `false ⟶ true`, the same walking arrow the
theory-translation counterexample uses.  Over it, `numbers` carries the
naturals at each stage.  Two properties:

* `sourcePred` — even at the refined stage, unconstrained at the coarse stage;
* `targetPred` — even at every stage.

Both are genuine subfunctors, and they differ (`source_ne_target`), so the
results below are not about two names for one property.

The instructive pair:

* **doubling qualifies** (`double_carries`, `doubleIsHigherOrder`), because
  doubling yields an even number whatever it is given, so it meets the target
  at both stages;
* **the identity is rejected** (`identity_does_not_carry`,
  `no_identity_total`), and not for a degenerate reason.  The identity meets
  the target at the refined stage, where the source already demands evenness.
  It fails at the coarse stage, where the source demands nothing.  Because the
  function predicate quantifies over restrictions, a function claimed at the
  refined stage must already survive the coarse one, so this failure is visible
  to the predicate rather than hidden by the stage it is tested at.

A nonconstant predicate transformer is exercised as well: `preserveEverything`
demands that every property be preserved, and doubling fails it concretely, on
the property of being exactly one (`double_does_not_preserve_singleton`).

## Scope

This consumer is built at the presheaf level. The binder-capable route in
`GSLT/LanguageDef/BindingSignature.lean` and its substitution laws already
exist, independently of the first-order typed-graph compiler. Connecting an
authored higher-order term through that route to this function predicate,
with evaluation and substitution correspondence, remains an integration
obligation. This arithmetic consumer does not establish that correspondence.
-/

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.FunctionPredicateConsumer

open Mettapedia.GSLT.Topos

/-- Two stages, coarse below refined. -/
abbrev Stage := Bool

/-- The naturals at every stage, restricting by the identity. -/
abbrev numbers : Stageᵒᵖ ⥤ Type where
  obj _ := ℕ
  map _ := 𝟙 _

/-- Even at the refined stage, unconstrained at the coarse stage. -/
def sourcePred : Subfunctor numbers where
  obj U := if U.unop = true then {n | n % 2 = 0} else Set.univ
  map {U V} i := by
    intro n held
    by_cases hV : V.unop = true
    · have below : V.unop ≤ U.unop := leOfHom i.unop
      have hU : U.unop = true := by
        cases hu : U.unop
        · rw [hV, hu] at below
          exact absurd below (by decide)
        · rfl
      simp only [hU, if_true] at held
      simp only [hV, if_true]
      show (numbers.map i) n % 2 = 0
      simpa [numbers] using held
    · simp [hV]

/-- Even at every stage. -/
def targetPred : Subfunctor numbers where
  obj _ := {n | n % 2 = 0}
  map _ := by
    intro n held
    show (numbers.map _) n % 2 = 0
    simpa [numbers] using held

abbrev sourceObj : PresheafPredicateTotal Stage :=
  totalOfPredicate numbers sourcePred

abbrev targetObj : PresheafPredicateTotal Stage :=
  totalOfPredicate numbers targetPred

/-- The two properties genuinely differ. -/
theorem source_ne_target : sourcePred ≠ targetPred := by
  intro equal
  have oneIn : (1 : ℕ) ∈ sourcePred.obj (op false) := by simp [sourcePred]
  rw [equal] at oneIn
  have reduced : (1 : ℕ) % 2 = 0 := oneIn
  omega

/-- Doubling, as a presheaf map. -/
def doubleMap : numbers ⟶ numbers where
  app _ := TypeCat.ofHom (fun n => 2 * n)

/-- The identity, as a presheaf map. -/
def identityMap : numbers ⟶ numbers := 𝟙 numbers

/-! ## Doubling qualifies -/

theorem double_carries : sourcePred ≤ targetPred.preimage doubleMap := by
  intro U n _
  show (2 * n) % 2 = 0
  exact Nat.mul_mod_right 2 n

/-- Doubling as a total morphism between the two typed objects. -/
def doubleTotal : sourceObj ⟶ targetObj :=
  homOfEntailment doubleMap double_carries

/-- Doubling in a context, as a map out of a product. -/
def doubleInContext : prodTotal sourceObj (unitTotal Stage) ⟶ targetObj :=
  homOfEntailment (fst numbers (𝟙_ (Stageᵒᵖ ⥤ Type)) ≫ doubleMap) (by
    intro U value held
    exact double_carries U held.1)

/-- Doubling satisfies the function predicate: it curries into the
exponential object. -/
noncomputable def doubleIsHigherOrder :
    unitTotal Stage ⟶ expTotal sourceObj targetObj :=
  expCurry doubleInContext

/-! ## The identity is rejected -/

/-- The identity fails at the coarse stage, where the source demands
nothing. -/
theorem identity_does_not_carry :
    ¬ sourcePred ≤ targetPred.preimage identityMap := by
  intro below
  have oneIn := below (op false) (show (1 : ℕ) ∈ sourcePred.obj (op false) by
    simp [sourcePred])
  have reduced : (1 : ℕ) % 2 = 0 := oneIn
  omega

/-- Consequently the identity carries no total morphism between these
objects. -/
theorem no_identity_total :
    ¬ ∃ g : sourceObj ⟶ targetObj, g.base = identityMap :=
  no_hom_over_of_not_entails (a := sourceObj) (b := targetObj) identityMap
    identity_does_not_carry

/-! ## A nonconstant predicate transformer -/

/-- Being exactly one. -/
def singletonOne : Subfunctor numbers where
  obj _ := {n | n = 1}
  map _ := by
    intro n held
    show (numbers.map _) n = 1
    simpa [numbers] using held

/-- The transformer demanding that every property be preserved. -/
def preserveEverything : Subfunctor numbers → Subfunctor numbers := fun α => α

/-- It is nonconstant. -/
theorem preserveEverything_nonconstant :
    preserveEverything sourcePred ≠ preserveEverything targetPred := by
  intro equal
  have oneIn : (1 : ℕ) ∈ (preserveEverything sourcePred).obj (op false) := by
    simp [preserveEverything, sourcePred]
  rw [equal] at oneIn
  have reduced : (1 : ℕ) % 2 = 0 := oneIn
  omega

/-- Doubling does not preserve every property: it fails on being exactly
one. -/
theorem double_does_not_preserve_singleton :
    ¬ singletonOne ≤ (preserveEverything singletonOne).preimage doubleMap := by
  intro below
  have oneIn := below (op true) (show (1 : ℕ) = 1 from rfl)
  have reduced : 2 * 1 = 1 := oneIn
  omega

end Mettapedia.GSLT.Topos.FunctionPredicateConsumer

#print axioms Mettapedia.GSLT.Topos.FunctionPredicateConsumer.source_ne_target
#print axioms Mettapedia.GSLT.Topos.FunctionPredicateConsumer.double_carries
#print axioms Mettapedia.GSLT.Topos.FunctionPredicateConsumer.identity_does_not_carry
#print axioms Mettapedia.GSLT.Topos.FunctionPredicateConsumer.no_identity_total
#print axioms Mettapedia.GSLT.Topos.FunctionPredicateConsumer.preserveEverything_nonconstant
#print axioms Mettapedia.GSLT.Topos.FunctionPredicateConsumer.double_does_not_preserve_singleton
