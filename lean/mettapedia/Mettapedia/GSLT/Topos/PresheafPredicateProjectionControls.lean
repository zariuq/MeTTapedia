import Mettapedia.GSLT.Topos.PresheafPredicateProjection

/-!
# A changed predicate and its actual cartesian lift

The indexing category is the two-object Boolean order. The presheaves of
Boolean pairs and Booleans are connected by exclusive-or. Pulling truth back
along this transformation accepts exactly the unequal pairs. This differs
from retaining the predicate on the first coordinate. A preceding nonidentity
transformation changes the result again, and the actual cartesian lift factors
its composite uniquely.

The example concerns the presheaf predicate fibration, not a classifying
category for generated dependent syntax.
-/

namespace Mettapedia.GSLT.Topos.PredicateProjectionControls

open CategoryTheory CategoryTheory.Functor Opposite

set_option autoImplicit false

def baseArrow : (false : Bool) ⟶ true := homOfLE (by decide)

theorem base_objects_distinct : (false : Bool) ≠ true := by decide

theorem no_reverse_base_arrow : ¬ Nonempty ((true : Bool) ⟶ false) := by
  rintro ⟨reverse⟩
  have impossible := leOfHom reverse
  contradiction

abbrev pairPresheaf : Boolᵒᵖ ⥤ Type := (CategoryTheory.Functor.const Boolᵒᵖ).obj (Bool × Bool)
abbrev boolPresheaf : Boolᵒᵖ ⥤ Type := (CategoryTheory.Functor.const Boolᵒᵖ).obj Bool

def exclusiveOr : pairPresheaf ⟶ boolPresheaf where
  app := fun _ => TypeCat.ofHom (fun pair : Bool × Bool => Bool.xor pair.1 pair.2)

def flipFirst : pairPresheaf ⟶ pairPresheaf where
  app := fun _ => TypeCat.ofHom (fun pair : Bool × Bool => (!pair.1, pair.2))

def truth : Subfunctor boolPresheaf where
  obj := fun _ => {value | value = true}
  map := by intros _ _ _ _ member; exact member

/-- The deliberately wrong unchanged-coordinate predicate. -/
def firstTrue : Subfunctor pairPresheaf where
  obj := fun _ => {pair | pair.1 = true}
  map := by intros _ _ _ _ member; exact member

def unequalPairs : Subfunctor pairPresheaf := truth.preimage exclusiveOr

theorem pulled_predicate (object : Boolᵒᵖ) (pair : Bool × Bool) :
    pair ∈ unequalPairs.obj object ↔ Bool.xor pair.1 pair.2 = true := Iff.rfl

theorem unequal_pair_accepted : (false, true) ∈ unequalPairs.obj (op true) := rfl

theorem equal_pair_rejected : (true, true) ∉ unequalPairs.obj (op false) := by
  change ¬ false = true
  decide

theorem reindexing_changes_predicate : unequalPairs ≠ firstTrue := by
  intro same
  have member := unequal_pair_accepted
  rw [same] at member
  contradiction

theorem controller_map_is_nonidentity : flipFirst ≠ 𝟙 pairPresheaf := by
  intro same
  have atPair := congrArg (fun f : pairPresheaf ⟶ pairPresheaf =>
    f.app (op false) (false, false)) same
  change (true, false) = (false, false) at atPair
  contradiction

/-- A source object and a target object of the total category with their
actual, distinct predicate fibers. -/
abbrev liftSource : PresheafPredicateTotal Bool := predicateLiftDomain truth exclusiveOr
abbrev liftTarget : PresheafPredicateTotal Bool := ⟨boolPresheaf, truth⟩

abbrev actualLift : liftSource ⟶ liftTarget := predicateLift truth exclusiveOr

theorem lift_has_changed_predicate : liftSource.fiber = unequalPairs := rfl

theorem lift_does_not_retain_first_coordinate : liftSource.fiber ≠ firstTrue :=
  reindexing_changes_predicate

theorem lift_is_stronglyCartesian :
    IsStronglyCartesian (presheafPredicateProjection Bool) exclusiveOr actualLift :=
  predicateLift_stronglyCartesian truth exclusiveOr

theorem lift_projects_to_actual_map :
    (presheafPredicateProjection Bool).map actualLift = exclusiveOr := rfl

theorem lift_member_survives_nonidentity_base_restriction :
    (false, true) ∈ liftSource.fiber.obj (op true) ∧
      pairPresheaf.map baseArrow.op (false, true) ∈ liftSource.fiber.obj (op false) := by
  exact ⟨rfl, rfl⟩

theorem composite_reindexing :
    truth.preimage (flipFirst ≫ exclusiveOr) = unequalPairs.preimage flipFirst :=
  Subfunctor.preimage_comp truth flipFirst exclusiveOr

theorem composite_changes_the_answer :
    (false, false) ∉ unequalPairs.obj (op false) ∧
      (false, false) ∈ (truth.preimage (flipFirst ≫ exclusiveOr)).obj (op false) := by
  change (¬ false = true) ∧ true = true
  decide

/-- Factorization is required over the preceding nonidentity map, not merely
over an identity in the presheaf category. -/
theorem composite_lift_factors_uniquely :
    ∃! factor : predicateLiftDomain truth (flipFirst ≫ exclusiveOr) ⟶ liftSource,
      IsHomLift (presheafPredicateProjection Bool) flipFirst factor ∧
        factor ≫ actualLift = predicateLift truth (flipFirst ≫ exclusiveOr) := by
  have : IsHomLift (presheafPredicateProjection Bool) (flipFirst ≫ exclusiveOr)
      (predicateLift truth (flipFirst ≫ exclusiveOr)) :=
    IsHomLift.map (presheafPredicateProjection Bool)
      (predicateLift truth (flipFirst ≫ exclusiveOr))
  exact predicateLift_factorization truth exclusiveOr
    (predicateLiftDomain truth (flipFirst ≫ exclusiveOr))
    flipFirst (predicateLift truth (flipFirst ≫ exclusiveOr))

#print axioms reindexing_changes_predicate
#print axioms lift_is_stronglyCartesian
#print axioms composite_lift_factors_uniquely

end Mettapedia.GSLT.Topos.PredicateProjectionControls
