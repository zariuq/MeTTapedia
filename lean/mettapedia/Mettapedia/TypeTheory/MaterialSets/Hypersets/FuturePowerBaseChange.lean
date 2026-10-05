import Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerFamilies

/-!
# Exact base change of full contextual power predicates

Every context functor gives a map of complete future arguments and therefore
a pullback of stable predicates. Coverage and outgoing lifting are separate
conditions: coverage reflects comparisons, while outgoing lifting makes the
existential image stable. The resulting inverse comparison is proved on the
precisely fibre-invariant source predicates, without choosing representatives.

For substitutions between presheaves over one site, the actual outgoing
context lifts construct inverse future categories. These give an invertible
full power-family comparison, rather than an assumption that arbitrary
functors retain every future.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerBaseChange

open CategoryTheory PowerClassPresheafBaseChange
open Mettapedia.GSLT.Topos.ConstructivePresheaf
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u

variable {D E : Type u} [Category.{u} D] [Category.{u} E]

def argumentMap (change : D ⥤ E) (A : E ⥤ Type u) (point : D) :
    FuturePowerFamilies.Arguments (restrict change A) point ⥤
      FuturePowerFamilies.Arguments A (change.obj point) :=
  Cat.elementsMap (Future.map change point) (Future.domain A (change.obj point))

theorem argumentMap_target (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (argument : FuturePowerFamilies.Arguments (restrict change A) point) :
    ((argumentMap change A point).obj argument).1.1 = change.obj argument.1.1 := rfl

theorem argumentMap_arrow (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (argument : FuturePowerFamilies.Arguments (restrict change A) point) :
    ((argumentMap change A point).obj argument).1.2 = change.map argument.1.2 := rfl

theorem argumentMap_value (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (argument : FuturePowerFamilies.Arguments (restrict change A) point) :
    ((argumentMap change A point).obj argument).2 = argument.2 := rfl

def pullback (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (predicate : FuturePowerFamilies.Predicate A (change.obj point)) :
    FuturePowerFamilies.Predicate (restrict change A) point where
  holds argument := predicate.holds ((argumentMap change A point).obj argument)
  closed step available := predicate.closed ((argumentMap change A point).map step) available

theorem pullback_truth (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (predicate : FuturePowerFamilies.Predicate A (change.obj point))
    (argument : FuturePowerFamilies.Arguments (restrict change A) point) :
    (pullback change A point predicate).holds argument ↔
      predicate.holds ((argumentMap change A point).obj argument) := Iff.rfl

theorem pullback_restriction (change : D ⥤ E) (A : E ⥤ Type u)
    {first second : D} (step : first ⟶ second)
    (predicate : FuturePowerFamilies.Predicate A (change.obj first)) :
    pullback change A second (FuturePowerFamilies.restrict A (change.map step) predicate) =
      FuturePowerFamilies.restrict (restrict change A) step (pullback change A first predicate) := by
  apply FuturePowerFamilies.Predicate.ext
  intro argument
  change predicate.holds ⟨⟨change.obj argument.1.1,
    change.map step ≫ change.map argument.1.2⟩, argument.2⟩ ↔
      predicate.holds ⟨⟨change.obj argument.1.1,
        change.map (step ≫ argument.1.2)⟩, argument.2⟩
  rw [change.map_comp]

def comparison (change : D ⥤ E) (A : E ⥤ Type u) :
    NatTrans (restrict change (FuturePowerFamilies.family A))
      (FuturePowerFamilies.family (restrict change A)) where
  app point := TypeCat.ofHom (pullback change A point)
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro predicate
    exact pullback_restriction change A step predicate

def pullStable (change : D ⥤ E) (A : E ⥤ Type u)
    (predicate : FuturePowerFamilies.StablePredicate A) :
    FuturePowerFamilies.StablePredicate (restrict change A) where
  holds argument := predicate.holds ((Cat.elementsMap change A).obj argument)
  closed step available := predicate.closed ((Cat.elementsMap change A).map step) available

def pullSection (change : D ⥤ E) (A : E ⥤ Type u)
    (term : (FuturePowerFamilies.family A).sections) :
    (FuturePowerFamilies.family (restrict change A)).sections :=
  ⟨fun point => pullback change A point (term.val (change.obj point)), by
    intro first second step
    exact (pullback_restriction change A step (term.val (change.obj first))).symm.trans
      (congrArg (pullback change A second) (term.property (change.map step)))⟩

theorem classifier_square (change : D ⥤ E) (A : E ⥤ Type u)
    (predicate : FuturePowerFamilies.StablePredicate A) :
    pullSection change A (FuturePowerFamilies.classify A predicate) =
      FuturePowerFamilies.classify (restrict change A) (pullStable change A predicate) := by
  apply Subtype.ext
  funext point
  apply FuturePowerFamilies.Predicate.ext
  intro argument
  exact Iff.rfl

theorem classified_square (change : D ⥤ E) (A : E ⥤ Type u)
    (term : (FuturePowerFamilies.family A).sections) :
    FuturePowerFamilies.classifiedPredicate (restrict change A) (pullSection change A term) =
      pullStable change A (FuturePowerFamilies.classifiedPredicate A term) := by
  apply FuturePowerFamilies.StablePredicate.ext
  intro argument
  change (term.val (change.obj argument.1)).holds
      ⟨⟨change.obj argument.1, change.map (𝟙 argument.1)⟩, argument.2⟩ ↔ _
  rw [change.map_id]
  exact Iff.rfl

section ExactRange

variable {L R : Type u} [Category.{u} L] [Category.{u} R]
variable (F : L ⥤ R)

/-- Every actual outgoing target arrow has a source lift with that endpoint.
Endpoint equality does not assert equality of authored event receipts. -/
def OutgoingLifts : Prop := ∀ source {target : R} (_step : F.obj source ⟶ target),
  ∃ next, Nonempty (source ⟶ next) ∧ F.obj next = target

def StableSet := {predicate : L → Prop //
  ∀ {first second : L} (_step : first ⟶ second), predicate first → predicate second}

def setPullback (predicate : StableSet (L := R)) : StableSet (L := L) :=
  ⟨fun source => predicate.val (F.obj source), fun step available => predicate.property (F.map step) available⟩

def FibreInvariant (predicate : StableSet (L := L)) : Prop :=
  ∀ {first second}, F.obj first = F.obj second → (predicate.val first ↔ predicate.val second)

def setImage (lifts : OutgoingLifts F) (predicate : StableSet (L := L)) : StableSet (L := R) :=
  ⟨fun target => ∃ source, F.obj source = target ∧ predicate.val source, by
    intro first second step available
    obtain ⟨source, same, holds⟩ := available
    obtain ⟨next, ⟨lifted⟩, endpoint⟩ := lifts source (eqToHom same ≫ step)
    exact ⟨next, endpoint, predicate.property lifted holds⟩⟩

theorem setPullback_image (lifts : OutgoingLifts F) (predicate : StableSet (L := L))
    (invariant : FibreInvariant F predicate) : setPullback F (setImage F lifts predicate) = predicate := by
  apply Subtype.ext
  funext source
  apply propext
  exact ⟨fun ⟨other, same, holds⟩ => (invariant same).mp holds,
    fun holds => ⟨source, rfl, holds⟩⟩

theorem setImage_pullback (lifts : OutgoingLifts F) (covers : Function.Surjective F.obj)
    (predicate : StableSet (L := R)) : setImage F lifts (setPullback F predicate) = predicate := by
  apply Subtype.ext
  funext target
  apply propext
  constructor
  · rintro ⟨source, same, holds⟩
    exact same ▸ holds
  · intro holds
    obtain ⟨source, same⟩ := covers target
    refine ⟨source, same, ?_⟩
    change predicate.val (F.obj source)
    exact same.symm ▸ holds

theorem setPullback_invariant (predicate : StableSet (L := R)) :
    FibreInvariant F (setPullback F predicate) := by
  intro first second same
  change predicate.val (F.obj first) ↔ predicate.val (F.obj second)
  rw [same]

/-- The complete stable-predicate range is exactly the fibre-invariant
subtype when coverage and outgoing lifting hold. -/
def stableSetEquiv (lifts : OutgoingLifts F) (covers : Function.Surjective F.obj) :
    StableSet (L := R) ≃ {predicate : StableSet (L := L) // FibreInvariant F predicate} where
  toFun predicate := ⟨setPullback F predicate, setPullback_invariant F predicate⟩
  invFun predicate := setImage F lifts predicate.val
  left_inv := setImage_pullback F lifts covers
  right_inv predicate := Subtype.ext (setPullback_image F lifts predicate.val predicate.property)

theorem setPullback_injective (covers : Function.Surjective F.obj) :
    Function.Injective (setPullback F) := by
  intro first second same
  apply Subtype.ext
  funext target
  obtain ⟨source, rfl⟩ := covers target
  exact congrArg (fun predicate : StableSet (L := L) => predicate.val source) same

end ExactRange

def predicateSet (A : E ⥤ Type u) (point : E) :
    FuturePowerFamilies.Predicate A point ≃
      StableSet (L := FuturePowerFamilies.Arguments A point) where
  toFun predicate := ⟨predicate.holds, predicate.closed⟩
  invFun predicate := ⟨predicate.val, predicate.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def PredicateInvariant (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (predicate : FuturePowerFamilies.Predicate (restrict change A) point) : Prop :=
  FibreInvariant (argumentMap change A point)
    (predicateSet (restrict change A) point predicate)

def predicateImage (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (lifts : OutgoingLifts (argumentMap change A point))
    (predicate : FuturePowerFamilies.Predicate (restrict change A) point) :
    FuturePowerFamilies.Predicate A (change.obj point) :=
  (predicateSet A (change.obj point)).symm
    (setImage (argumentMap change A point) lifts
      (predicateSet (restrict change A) point predicate))

theorem predicateImage_truth (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (lifts : OutgoingLifts (argumentMap change A point))
    (predicate : FuturePowerFamilies.Predicate (restrict change A) point)
    (argument : FuturePowerFamilies.Arguments A (change.obj point)) :
    (predicateImage change A point lifts predicate).holds argument ↔
      ∃ source, (argumentMap change A point).obj source = argument ∧
        predicate.holds source := Iff.rfl

theorem predicate_descends_iff (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (lifts : OutgoingLifts (argumentMap change A point))
    (predicate : FuturePowerFamilies.Predicate (restrict change A) point) :
    (∃ target, pullback change A point target = predicate) ↔
      PredicateInvariant change A point predicate := by
  constructor
  · rintro ⟨target, rfl⟩
    exact setPullback_invariant (argumentMap change A point)
      (predicateSet A (change.obj point) target)
  · intro invariant
    refine ⟨predicateImage change A point lifts predicate, ?_⟩
    exact (predicateSet (restrict change A) point).injective
      (setPullback_image (argumentMap change A point) lifts
        (predicateSet (restrict change A) point predicate) invariant)

def predicateRangeEquiv (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (lifts : OutgoingLifts (argumentMap change A point))
    (covers : Function.Surjective (argumentMap change A point).obj) :
    FuturePowerFamilies.Predicate A (change.obj point) ≃
      {predicate : FuturePowerFamilies.Predicate (restrict change A) point //
        PredicateInvariant change A point predicate} where
  toFun predicate := ⟨pullback change A point predicate,
    setPullback_invariant (argumentMap change A point)
      (predicateSet A (change.obj point) predicate)⟩
  invFun predicate := predicateImage change A point lifts predicate.val
  left_inv predicate := (predicateSet A (change.obj point)).injective
    (setImage_pullback (argumentMap change A point) lifts covers
      (predicateSet A (change.obj point) predicate))
  right_inv predicate := Subtype.ext
    ((predicateSet (restrict change A) point).injective
      (setPullback_image (argumentMap change A point) lifts
        (predicateSet (restrict change A) point predicate.val) predicate.property))

theorem pullback_injective (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (covers : Function.Surjective (argumentMap change A point).obj) :
    Function.Injective (pullback change A point) := by
  intro first second same
  apply (predicateSet A (change.obj point)).injective
  exact setPullback_injective (argumentMap change A point) covers
    (congrArg (predicateSet (restrict change A) point) same)

theorem pullback_comp {K : Type u} [Category.{u} K]
    (first : D ⥤ E) (second : E ⥤ K) (A : K ⥤ Type u) (point : D)
    (predicate : FuturePowerFamilies.Predicate A (second.obj (first.obj point))) :
    pullback first (restrict second A) point
        (pullback second A (first.obj point) predicate) =
      pullback (Cat.compose first second) A point predicate := by
  apply FuturePowerFamilies.Predicate.ext
  intro argument
  exact Iff.rfl

theorem pullback_identity (A : D ⥤ Type u) (point : D)
    (predicate : FuturePowerFamilies.Predicate A point) :
    HEq (pullback (Cat.identity D) A point predicate) predicate := by
  apply heq_of_eq
  apply FuturePowerFamilies.Predicate.ext
  intro argument
  rcases argument with ⟨⟨_, _⟩, _⟩
  exact Iff.rfl

theorem pullback_preserves (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (first second : FuturePowerFamilies.Predicate A (change.obj point))
    (included : ∀ argument, first.holds argument → second.holds argument) :
    ∀ argument, (pullback change A point first).holds argument →
      (pullback change A point second).holds argument :=
  fun argument => included ((argumentMap change A point).obj argument)

theorem pullback_reflects (change : D ⥤ E) (A : E ⥤ Type u) (point : D)
    (covers : Function.Surjective (argumentMap change A point).obj)
    (first second : FuturePowerFamilies.Predicate A (change.obj point))
    (included : ∀ argument, (pullback change A point first).holds argument →
      (pullback change A point second).holds argument) :
    ∀ argument, first.holds argument → second.holds argument := by
  intro argument available
  obtain ⟨source, same⟩ := covers argument
  have sourceAvailable : first.holds ((argumentMap change A point).obj source) := same.symm ▸ available
  exact same ▸ included source sourceAvailable

section PresheafSubstitution

open PowerClassPresheafProducts

variable {C : Type u} [Category.{u} C]
variable {P Q : Cᵒᵖ ⥤ Type u} (change : NatTrans Q P)

/-- The inverse retains the actual underlying context arrow and restricts
the source context value. It is constructed, not selected from coverage. -/
def argumentBack (A : P.Elements ⥤ Type u) (point : Q.Elements) :
    FuturePowerFamilies.Arguments A ((elementMap change).obj point) ⥤
      FuturePowerFamilies.Arguments (PowerClassPresheafProducts.reindex change A) point :=
  Cat.elementsBack (Future.map (elementMap change) point) (liftFuture change point)
    (future_right_inverse change point) (Future.domain A ((elementMap change).obj point))

theorem argument_right (A : P.Elements ⥤ Type u) (point : Q.Elements)
    (argument : FuturePowerFamilies.Arguments A ((elementMap change).obj point)) :
    (argumentMap (elementMap change) A point).obj
      ((argumentBack change A point).obj argument) = argument :=
  Cat.elements_right_obj _ _ (future_right_inverse change point) _ argument

theorem argument_left (A : P.Elements ⥤ Type u) (point : Q.Elements)
    (argument : FuturePowerFamilies.Arguments (PowerClassPresheafProducts.reindex change A) point) :
    (argumentBack change A point).obj
      ((argumentMap (elementMap change) A point).obj argument) = argument :=
  Cat.elements_left_obj _ _ (future_left_inverse change point)
    (future_right_inverse change point)
    (Future.domain A ((elementMap change).obj point)) argument

theorem argument_surjective (A : P.Elements ⥤ Type u) (point : Q.Elements) :
    Function.Surjective (argumentMap (elementMap change) A point).obj :=
  fun argument => ⟨(argumentBack change A point).obj argument,
    argument_right change A point argument⟩

theorem argument_injective (A : P.Elements ⥤ Type u) (point : Q.Elements) :
    Function.Injective (argumentMap (elementMap change) A point).obj := by
  intro first second same
  exact (argument_left change A point first).symm.trans
    ((congrArg (argumentBack change A point).obj same).trans
      (argument_left change A point second))

theorem argument_outgoing_lifts (A : P.Elements ⥤ Type u) (point : Q.Elements) :
    OutgoingLifts (argumentMap (elementMap change) A point) := by
  intro source target step
  refine ⟨(argumentBack change A point).obj target, ⟨?_, argument_right change A point target⟩⟩
  exact ⟨eqToHom (argument_left change A point source).symm ≫
    (argumentBack change A point).map step⟩

def pushforward (A : P.Elements ⥤ Type u) (point : Q.Elements)
    (predicate : FuturePowerFamilies.Predicate (PowerClassPresheafProducts.reindex change A) point) :
    FuturePowerFamilies.Predicate A ((elementMap change).obj point) where
  holds argument := predicate.holds ((argumentBack change A point).obj argument)
  closed step available := predicate.closed ((argumentBack change A point).map step) available

/-- Genuine presheaf substitutions retain the entire future classifier.
This does not assert surjectivity on the original global context objects. -/
def substitutionEquiv (A : P.Elements ⥤ Type u) (point : Q.Elements) :
    FuturePowerFamilies.Predicate A ((elementMap change).obj point) ≃
      FuturePowerFamilies.Predicate (PowerClassPresheafProducts.reindex change A) point where
  toFun := pullback (elementMap change) A point
  invFun := pushforward change A point
  left_inv predicate := by
    apply FuturePowerFamilies.Predicate.ext
    intro argument
    change predicate.holds ((argumentMap (elementMap change) A point).obj
      ((argumentBack change A point).obj argument)) ↔ predicate.holds argument
    exact iff_of_eq (congrArg predicate.holds (argument_right change A point argument))
  right_inv predicate := by
    apply FuturePowerFamilies.Predicate.ext
    intro argument
    change predicate.holds ((argumentBack change A point).obj
      ((argumentMap (elementMap change) A point).obj argument)) ↔ predicate.holds argument
    exact iff_of_eq (congrArg predicate.holds (argument_left change A point argument))

theorem substitutionEquiv_truth (A : P.Elements ⥤ Type u) (point : Q.Elements)
    (predicate : FuturePowerFamilies.Predicate A ((elementMap change).obj point))
    (argument : FuturePowerFamilies.Arguments (PowerClassPresheafProducts.reindex change A) point) :
    (substitutionEquiv change A point predicate).holds argument ↔
      predicate.holds ((argumentMap (elementMap change) A point).obj argument) := Iff.rfl

def substitutionComparison (A : P.Elements ⥤ Type u) :
    NatTrans (PowerClassPresheafProducts.reindex change (FuturePowerFamilies.family A))
      (FuturePowerFamilies.family (PowerClassPresheafProducts.reindex change A)) := comparison (elementMap change) A

def substitutionInverse (A : P.Elements ⥤ Type u) :
    NatTrans (FuturePowerFamilies.family (PowerClassPresheafProducts.reindex change A))
      (PowerClassPresheafProducts.reindex change (FuturePowerFamilies.family A)) :=
  Nat.inverse (substitutionComparison change A) (substitutionEquiv change A) (fun _ _ => rfl)

theorem substitution_left (A : P.Elements ⥤ Type u) :
    compose (substitutionComparison change A) (substitutionInverse change A) =
      identity (PowerClassPresheafProducts.reindex change (FuturePowerFamilies.family A)) :=
  Nat.inverse_left _ _ (fun _ _ => rfl)

theorem substitution_right (A : P.Elements ⥤ Type u) :
    compose (substitutionInverse change A) (substitutionComparison change A) =
      identity (FuturePowerFamilies.family (PowerClassPresheafProducts.reindex change A)) :=
  Nat.inverse_right _ _ (fun _ _ => rfl)

def substitutionSectionEquiv (A : P.Elements ⥤ Type u) :
    (PowerClassPresheafProducts.reindex change (FuturePowerFamilies.family A)).sections ≃
      (FuturePowerFamilies.family (PowerClassPresheafProducts.reindex change A)).sections where
  toFun term := ⟨fun point => substitutionEquiv change A point (term.val point), by
    intro first second step
    have square := congrArg (fun operation => operation (term.val first))
      ((substitutionComparison change A).naturality step)
    change substitutionEquiv change A second
        ((PowerClassPresheafProducts.reindex change (FuturePowerFamilies.family A)).map step (term.val first)) =
      (FuturePowerFamilies.family (PowerClassPresheafProducts.reindex change A)).map step
        (substitutionEquiv change A first (term.val first)) at square
    exact square.symm.trans (congrArg (substitutionEquiv change A second) (term.property step))⟩
  invFun term := ⟨fun point => (substitutionEquiv change A point).symm (term.val point), by
    intro first second step
    have square := congrArg (fun operation => operation (term.val first))
      ((substitutionInverse change A).naturality step)
    change (substitutionEquiv change A second).symm
        ((FuturePowerFamilies.family (PowerClassPresheafProducts.reindex change A)).map step (term.val first)) =
      (PowerClassPresheafProducts.reindex change (FuturePowerFamilies.family A)).map step
        ((substitutionEquiv change A first).symm (term.val first)) at square
    exact square.symm.trans (congrArg (substitutionEquiv change A second).symm (term.property step))⟩
  left_inv term := Subtype.ext (funext fun point => (substitutionEquiv change A point).symm_apply_apply _)
  right_inv term := Subtype.ext (funext fun point => (substitutionEquiv change A point).apply_symm_apply _)

theorem substitutionSectionEquiv_truth (A : P.Elements ⥤ Type u)
    (term : (PowerClassPresheafProducts.reindex change (FuturePowerFamilies.family A)).sections)
    (point : Q.Elements)
    (argument : FuturePowerFamilies.Arguments (PowerClassPresheafProducts.reindex change A) point) :
    ((substitutionSectionEquiv change A term).val point).holds argument ↔
      (term.val point).holds ((argumentMap (elementMap change) A point).obj argument) := Iff.rfl

theorem substitutionSectionEquiv_classifier (A : P.Elements ⥤ Type u)
    (predicate : FuturePowerFamilies.StablePredicate A) :
    substitutionSectionEquiv change A
        (CP.restrictSection (elementMap change) (FuturePowerFamilies.family A)
          (FuturePowerFamilies.classify A predicate)) =
      FuturePowerFamilies.classify (PowerClassPresheafProducts.reindex change A)
        (pullStable (elementMap change) A predicate) :=
  classifier_square (elementMap change) A predicate

end PresheafSubstitution

end Mettapedia.TypeTheory.MaterialSets.Hypersets.FuturePowerBaseChange
