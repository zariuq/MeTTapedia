import Mettapedia.CategoryTheory.PredicateDoctrineQuantifierCoherence
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifier

/-!
# Structural predicates from actual constructor maps

A constructor transports complete argument predicates by its existential
adjoint. Binary constructors first combine both independently supplied child
predicates at the actual product argument. The resulting powerobject arrow
retains every parameter and both inputs. Its root predicate is the actual
constructor image; it need not distinguish syntactic names identified by
the admitted theory equations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalPredicateConstructorImage

open _root_.CategoryTheory
open MonoidalCategory CartesianMonoidalCategory
open HigherOrderInternalPredicateObject HigherOrderInternalPredicateQuantifier

universe u v p
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (doctrine : PredicateDoctrine.HigherOrder.{u,v,p} C)

def root {arguments result : C} (constructor : arguments ⟶ result) : doctrine.Fiber result :=
  doctrine.existsAlong constructor ⊤

def rootName {arguments result : C} (constructor : arguments ⟶ result) :
    result ⟶ doctrine.generic.object := doctrine.generic.characteristic _ (root doctrine constructor)

theorem root_read {arguments result : C} (constructor : arguments ⟶ result) :
    decode doctrine (rootName doctrine constructor) = root doctrine constructor :=
  decode_characteristic doctrine _

theorem root_introduction {arguments result : C} (constructor : arguments ⟶ result) :
    doctrine.reindex constructor (root doctrine constructor) = ⊤ :=
  eq_top_iff.mpr (doctrine.toFirstOrder.exists_unit constructor ⊤)

/-- A structural operation on the whole constructor argument predicate. -/
def operation {arguments result : C} (constructor : arguments ⟶ result) :
    power doctrine arguments ⟶ power doctrine result := existsOperation doctrine constructor

theorem operation_supplied {arguments result parameter : C} (constructor : arguments ⟶ result)
    (predicate : parameter ⟶ power doctrine arguments) :
    family doctrine (predicate ≫ operation doctrine constructor) =
      doctrine.existsAlong (constructor ▷ parameter) (family doctrine predicate) :=
  exists_supplied doctrine constructor predicate

theorem operation_in_root {arguments result parameter : C} (constructor : arguments ⟶ result)
    (predicate : parameter ⟶ power doctrine arguments) :
    family doctrine (predicate ≫ operation doctrine constructor) ≤
      root doctrine (constructor ▷ parameter) := by
  rw [operation_supplied]
  exact doctrine.exists_mono _ le_top

theorem supplied_introduction {arguments result parameter : C} (constructor : arguments ⟶ result)
    (predicate : parameter ⟶ power doctrine arguments) :
    family doctrine predicate ≤ doctrine.reindex (constructor ▷ parameter)
      (family doctrine (predicate ≫ operation doctrine constructor)) := by
  rw [operation_supplied]
  exact doctrine.toFirstOrder.exists_unit _ _

/-- Both child inputs are pulled to the actual complete product argument. -/
def binaryArguments (first second : C) :
    (power doctrine first ⊗ power doctrine second) ⟶ power doctrine (first ⊗ second) :=
  (InternalPredicateFunctionObject.operations (operations doctrine) (first ⊗ second)).meet
    (fst _ _ ≫ InternalPredicateQuantifier.precomposition (operations doctrine) (fst first second))
    (snd _ _ ≫ InternalPredicateQuantifier.precomposition (operations doctrine) (snd first second))

theorem binaryArguments_supplied {first second parameter : C}
    (left : parameter ⟶ power doctrine first) (right : parameter ⟶ power doctrine second) :
    family doctrine (lift left right ≫ binaryArguments doctrine first second) =
      doctrine.reindex (fst first second ▷ parameter) (family doctrine left) ⊓
        doctrine.reindex (snd first second ▷ parameter) (family doctrine right) := by
  rw [binaryArguments, family_substitution, family_meet, doctrine.reindex_inf,
    ← family_substitution, ← family_substitution]
  simp only [← Category.assoc, lift_fst, lift_snd, precomposition_supplied]

def binaryOperation {first second result : C} (constructor : (first ⊗ second) ⟶ result) :
    (power doctrine first ⊗ power doctrine second) ⟶ power doctrine result :=
  binaryArguments doctrine first second ≫ operation doctrine constructor

theorem binaryOperation_supplied {first second result parameter : C}
    (constructor : (first ⊗ second) ⟶ result)
    (left : parameter ⟶ power doctrine first) (right : parameter ⟶ power doctrine second) :
    family doctrine (lift left right ≫ binaryOperation doctrine constructor) =
      doctrine.existsAlong (constructor ▷ parameter)
        (doctrine.reindex (fst first second ▷ parameter) (family doctrine left) ⊓
          doctrine.reindex (snd first second ▷ parameter) (family doctrine right)) := by
  rw [binaryOperation, ← Category.assoc, operation_supplied, binaryArguments_supplied]

theorem binaryOperation_introduction {first second result parameter : C}
    (constructor : (first ⊗ second) ⟶ result)
    (left : parameter ⟶ power doctrine first) (right : parameter ⟶ power doctrine second) :
    doctrine.reindex (fst first second ▷ parameter) (family doctrine left) ⊓
        doctrine.reindex (snd first second ▷ parameter) (family doctrine right) ≤
      doctrine.reindex (constructor ▷ parameter)
        (family doctrine (lift left right ≫ binaryOperation doctrine constructor)) := by
  rw [binaryOperation_supplied]
  exact doctrine.toFirstOrder.exists_unit _ _

theorem operation_future {arguments result first second : C} (constructor : arguments ⟶ result)
    (future : first ⟶ second) (predicate : second ⟶ power doctrine arguments) :
    family doctrine ((future ≫ predicate) ≫ operation doctrine constructor) =
      doctrine.reindex (result ◁ future) (family doctrine (predicate ≫ operation doctrine constructor)) := by
  rw [Category.assoc]
  exact family_substitution doctrine future _

end Mettapedia.CategoryTheory.InternalPredicateConstructorImage
