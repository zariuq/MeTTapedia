import Mettapedia.CategoryTheory.InternalPredicateExistential
import Mettapedia.CategoryTheory.InternalPredicateImplication

/-!
# Finite logical diagrams determine their complete operation arrows

The all-context adjunctions earned from finite local diagrams determine
the universal, existential and implication arrows uniquely. Evaluating
at identity predicate functions and the two product projections recovers
the complete operations, including both implication inputs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateLogicalUniqueness

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject InternalPredicateFunctionObject InternalPredicateQuantifier

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C]
variable (original : Operations C) (originalLaws : original.Laws)
include originalLaws

theorem universal_operation_unique {source target : C} (route : source ⟶ target)
    (first second : Universal original route) : first.operation = second.operation := by
  let context := power original source
  let : SemilatticeInf (context ⟶ power original target) :=
    (functions original target).semilattice (functionLaws original originalLaws target) context
  let : SemilatticeInf (context ⟶ power original source) :=
    (functions original source).semilattice (functionLaws original originalLaws source) context
  have complete : 𝟙 context ≫ first.operation = 𝟙 context ≫ second.operation :=
    (Universal.adjunction original originalLaws route first context).u_unique
      (Universal.adjunction original originalLaws route second context) (fun _ => rfl)
  simpa only [Category.id_comp] using complete

theorem existential_operation_unique {source target : C} (route : source ⟶ target)
    (first second : InternalPredicateExistential.Existential original route) :
    first.operation = second.operation := by
  let context := power original source
  let : SemilatticeInf (context ⟶ power original source) :=
    (functions original source).semilattice (functionLaws original originalLaws source) context
  let : SemilatticeInf (context ⟶ power original target) :=
    (functions original target).semilattice (functionLaws original originalLaws target) context
  have complete : 𝟙 context ≫ first.operation = 𝟙 context ≫ second.operation :=
    (InternalPredicateExistential.Existential.adjunction original originalLaws route first context).l_unique
      (InternalPredicateExistential.Existential.adjunction original originalLaws route second context)
      (fun _ => rfl)
  simpa only [Category.id_comp] using complete

omit [MonoidalClosed C] in
theorem implication_operation_unique
    (first second : InternalPredicateImplication.Qualification original) :
    first.operation = second.operation := by
  let context := original.proposition ⊗ original.proposition
  let : SemilatticeInf (context ⟶ original.proposition) :=
    original.semilattice originalLaws context
  have complete :
      first.implies original (fst original.proposition original.proposition)
        (snd original.proposition original.proposition) =
      second.implies original (fst original.proposition original.proposition)
        (snd original.proposition original.proposition) :=
    (InternalPredicateImplication.Qualification.adjunction original originalLaws first
      (fst original.proposition original.proposition)).u_unique
      (InternalPredicateImplication.Qualification.adjunction original originalLaws second
        (fst original.proposition original.proposition)) (fun _ => rfl)
  simpa only [InternalPredicateImplication.Qualification.implies,
    InternalPredicateImplication.applyOperation, lift_fst_snd, Category.id_comp] using complete

theorem universal_subsingleton {source target : C} (route : source ⟶ target) :
    Subsingleton (Universal original route) where
  allEq first second := by
    have complete := universal_operation_unique original originalLaws route first second
    cases first
    cases second
    cases complete
    rfl

theorem existential_subsingleton {source target : C} (route : source ⟶ target) :
    Subsingleton (InternalPredicateExistential.Existential original route) where
  allEq first second := by
    have complete := existential_operation_unique original originalLaws route first second
    cases first
    cases second
    cases complete
    rfl

omit [MonoidalClosed C] in
theorem implication_subsingleton :
    Subsingleton (InternalPredicateImplication.Qualification original) where
  allEq first second := by
    have complete := implication_operation_unique original originalLaws first second
    cases first
    cases second
    cases complete
    rfl

end Mettapedia.CategoryTheory.InternalPredicateLogicalUniqueness
