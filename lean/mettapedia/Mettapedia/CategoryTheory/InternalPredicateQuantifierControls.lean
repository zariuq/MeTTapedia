import Mettapedia.CategoryTheory.InternalPredicateQuantifier
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Equalizers

/-!
# Complete finite-diagram quantifier controls

The Boolean universal quantifier reads both coordinates, including under a
varying external parameter. Its actual three local diagrams yield the
all-context adjunction. Projection onto only the first Boolean coordinate
preserves the generic unit but violates the complete counit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateQuantifierControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open InternalConjunctiveObject InternalPredicateFunctionObject InternalPredicateQuantifier

abbrev boolean : Operations Type where
  proposition := Bool
  truth := TypeCat.ofHom (fun _ => true)
  conjunction := TypeCat.ofHom (fun value => value.1 && value.2)

theorem boolean_laws : boolean.Laws where
  commutativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact Bool.and_comm value.2 value.1
  associativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact Bool.and_assoc value.1.1 value.1.2 value.2
  idempotence := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact Bool.and_self value
  truthUnit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact Bool.and_true value

abbrev applyPredicate {value : Type} (predicate : power boolean value) (argument : value) : Bool :=
  (show value ⟶ Bool from predicate) argument

def forgetBoolean : Bool ⟶ PUnit := TypeCat.ofHom (fun _ => PUnit.unit)

def universalOperation : power boolean Bool ⟶ power boolean PUnit :=
  TypeCat.ofHom (fun predicate =>
    TypeCat.ofHom (fun _ => applyPredicate predicate false && applyPredicate predicate true))

private theorem ordered_coordinate (pair : orderedPairs boolean Bool) (argument : Bool) :
    (applyPredicate (secondInput boolean Bool pair) argument &&
      applyPredicate (firstInput boolean Bool pair) argument) =
      applyPredicate (firstInput boolean Bool pair) argument := by
  have equation := equalizer.condition (functions boolean Bool).conjunction
    (fst (power boolean Bool) (power boolean Bool))
  have complete := congrArg (fun arrow : orderedPairs boolean Bool ⟶ power boolean Bool =>
    applyPredicate (arrow pair) argument) equation
  change (applyPredicate (firstInput boolean Bool pair) argument &&
    applyPredicate (secondInput boolean Bool pair) argument) =
      applyPredicate (firstInput boolean Bool pair) argument at complete
  exact (Bool.and_comm _ _).trans complete

theorem universal_monotonicity : Monotonicity boolean universalOperation where
  ordered := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext pair
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext argument
    have atFalse := ordered_coordinate pair false
    have atTrue := ordered_coordinate pair true
    change ((applyPredicate (secondInput boolean Bool pair) false &&
      applyPredicate (secondInput boolean Bool pair) true) &&
      (applyPredicate (firstInput boolean Bool pair) false &&
        applyPredicate (firstInput boolean Bool pair) true)) =
      (applyPredicate (firstInput boolean Bool pair) false &&
        applyPredicate (firstInput boolean Bool pair) true)
    cases firstFalse : applyPredicate (firstInput boolean Bool pair) false <;>
      cases firstTrue : applyPredicate (firstInput boolean Bool pair) true <;>
      cases secondFalse : applyPredicate (secondInput boolean Bool pair) false <;>
      cases secondTrue : applyPredicate (secondInput boolean Bool pair) true <;> simp_all

def quantifier : Universal boolean forgetBoolean where
  operation := universalOperation
  monotonicity := universal_monotonicity
  unit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext predicate
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext argument
    change ((applyPredicate predicate PUnit.unit && applyPredicate predicate PUnit.unit) &&
      applyPredicate predicate argument) = applyPredicate predicate argument
    cases argument
    simp only [Bool.and_self]
  counit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext predicate
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext argument
    change (applyPredicate predicate argument &&
      (applyPredicate predicate false && applyPredicate predicate true)) =
        (applyPredicate predicate false && applyPredicate predicate true)
    cases argument <;> cases applyPredicate predicate false <;>
      cases applyPredicate predicate true <;> rfl

theorem complete_quantifier_adjunction (context : Type) :
    letI : SemilatticeInf (context ⟶ power boolean PUnit) :=
      (functions boolean PUnit).semilattice (functionLaws boolean boolean_laws PUnit) context
    letI : SemilatticeInf (context ⟶ power boolean Bool) :=
      (functions boolean Bool).semilattice (functionLaws boolean boolean_laws Bool) context
    GaloisConnection
      (fun predicate : context ⟶ power boolean PUnit =>
        (predicate ≫ precomposition boolean forgetBoolean : context ⟶ power boolean Bool))
      (fun predicate : context ⟶ power boolean Bool =>
        (predicate ≫ quantifier.operation : context ⟶ power boolean PUnit)) :=
  Universal.adjunction boolean boolean_laws forgetBoolean quantifier context

def varyingInput : Nat ⟶ power boolean Bool :=
  TypeCat.ofHom (fun parameter => TypeCat.ofHom (fun argument =>
    if argument then decide (parameter > 1) else decide (parameter > 0)))

theorem both_inputs_are_retained :
    applyPredicate ((varyingInput ≫ quantifier.operation) 1) PUnit.unit = false ∧
      applyPredicate ((varyingInput ≫ quantifier.operation) 2) PUnit.unit = true := ⟨rfl, rfl⟩

theorem both_independent_coordinates_matter :
    applyPredicate (universalOperation (TypeCat.ofHom (fun _ => true))) PUnit.unit = true ∧
      applyPredicate (universalOperation (TypeCat.ofHom (fun value => !value))) PUnit.unit = false ∧
      applyPredicate (universalOperation (TypeCat.ofHom (fun value => value))) PUnit.unit = false :=
  ⟨rfl, rfl, rfl⟩

def projectingOperation : power boolean Bool ⟶ power boolean PUnit :=
  TypeCat.ofHom (fun predicate => TypeCat.ofHom (fun _ => applyPredicate predicate false))

theorem projection_preserves_unit :
    (functions boolean PUnit).meet
      (precomposition boolean forgetBoolean ≫ projectingOperation) (𝟙 _) = 𝟙 _ := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext predicate
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext argument
  cases argument
  exact Bool.and_self (applyPredicate predicate PUnit.unit)

theorem projection_violates_counit :
    (functions boolean Bool).meet (𝟙 _)
      (projectingOperation ≫ precomposition boolean forgetBoolean) ≠
        projectingOperation ≫ precomposition boolean forgetBoolean := by
  intro admitted
  have complete := congrArg
    (fun operation : power boolean Bool ⟶ power boolean Bool =>
      applyPredicate (operation (TypeCat.ofHom (fun value : Bool => !value))) true) admitted
  exact Bool.false_ne_true complete

theorem projection_has_no_qualification :
    ¬ ∃ supplied : Universal boolean forgetBoolean,
      supplied.operation = projectingOperation := by
  rintro ⟨supplied, reading⟩
  exact projection_violates_counit (reading ▸ supplied.counit)

end Mettapedia.CategoryTheory.InternalPredicateQuantifierControls
