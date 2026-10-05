import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPower
import Mettapedia.TypeTheory.ContextualImageFactorization

/-!
# Constructed base change of parameter-indexed covered powers

Pulling an argument family back along a natural parameter map and then
forming its parameter-supported power gives an actual inverse comparison
with pulling back the indexed power. The inverse constructs each pair
from its retained argument and the transported parameter. Its small cover
uses the original receipt carrier, without choosing a preimage.

Both whole natural comparison maps and their inverse laws are constructed.
The admitted truth, transported parameter and actual future arrow are all
retained. This is slice base change for the specified covered-power class,
not an assumption of indexed finality or unrestricted Collection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerBaseChange

open CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization
  (pullback pullbackFirst pullbackSecond)

universe u v w t
variable {D : Type u} [Category.{u} D]
variable {A : D ⥤ Type v} {B : D ⥤ Type w} {F : D ⥤ Type t}
variable (operation : NaturalHom A B) (change : NaturalHom F B)

abbrev argumentFamily := pullback operation change
abbrev argumentProjection := pullbackFirst operation change
abbrev parameterProjection := pullbackSecond operation change
abbrev indexedFamily := IndexedCoveredPower.family (parameterProjection operation change)
abbrev baseFamily := pullback (IndexedCoveredPower.projection operation) change

theorem projected_support (point : D)
    (entry : (indexedFamily operation change).obj point) :
    IndexedCoveredPower.Supports operation point (change.app point entry.val.1)
      (imagePower (argumentProjection operation change) point entry.val.2) := by
  intro argument available
  obtain ⟨pair, same, admitted⟩ := available
  have parameter := entry.property ⟨argument.1, pair⟩ admitted
  change pair.val.2 = F.map argument.1.2 entry.val.1 at parameter
  change pair.val.1 = argument.2 at same
  rw [← same, pair.property, parameter]
  exact (change.naturality argument.1.2 entry.val.1).symm

def forward : NaturalHom (indexedFamily operation change) (baseFamily operation change) where
  app point entry :=
    ⟨(⟨(change.app point entry.val.1,
      imagePower (argumentProjection operation change) point entry.val.2),
      projected_support operation change point entry⟩, entry.val.1), rfl⟩
  naturality step entry := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (change.naturality step entry.val.1)
        (imagePower_restrict (argumentProjection operation change) step entry.val.2)
    · rfl

def liftPredicate (point : D) (parameter : F.obj point) (predicate : Power A point) :
    Predicate (argumentFamily operation change) point where
  holds argument := predicate.val.holds ⟨argument.1, argument.2.val.1⟩ ∧
    argument.2.val.2 = F.map argument.1.2 parameter
  closed {first second} move available := by
    refine ⟨predicate.val.closed
      ((futureArguments (argumentProjection operation change) point).map move) available.1, ?_⟩
    have parameterEq := congrArg
      (fun pair : (argumentFamily operation change).obj second.1.1 => pair.val.2) move.2
    change F.map move.1.1 first.2.val.2 = second.2.val.2 at parameterEq
    have triangle := congrArg (fun arrow => F.map arrow parameter) move.1.2
    have transported : F.map move.1.1 (F.map first.1.2 parameter) = F.map second.1.2 parameter :=
      (F.map_comp_apply first.1.2 move.1.1 parameter).symm.trans triangle
    exact parameterEq.symm.trans
      ((congrArg (fun value => F.map move.1.1 value) available.2).trans transported)

def liftEnumeration (point : D) (parameter : F.obj point) (predicate : Power A point)
    (supported : IndexedCoveredPower.Supports operation point (change.app point parameter) predicate)
    (enumeration : Enumeration predicate.val) :
    Enumeration (liftPredicate operation change point parameter predicate) where
  Carrier := enumeration.Carrier
  value future receipt :=
    ⟨(enumeration.value future receipt, F.map future.2 parameter), by
      have admitted := (enumeration.covered future (enumeration.value future receipt)).mpr ⟨receipt, rfl⟩
      exact (supported ⟨future, enumeration.value future receipt⟩ admitted).trans
        (change.naturality future.2 parameter)⟩
  covered future argument := by
    constructor
    · rintro ⟨admitted, parameterEq⟩
      obtain ⟨receipt, same⟩ := (enumeration.covered future argument.val.1).mp admitted
      exact ⟨receipt, Subtype.ext (Prod.ext same parameterEq.symm)⟩
    · rintro ⟨receipt, same⟩
      have argumentEq := congrArg (fun pair : (argumentFamily operation change).obj future.1 => pair.val.1) same
      have parameterEq := congrArg (fun pair : (argumentFamily operation change).obj future.1 => pair.val.2) same
      exact ⟨(enumeration.covered future argument.val.1).mpr ⟨receipt, argumentEq⟩, parameterEq.symm⟩

def liftPower (point : D) (parameter : F.obj point) (predicate : Power A point)
    (supported : IndexedCoveredPower.Supports operation point (change.app point parameter) predicate) :
    Power (argumentFamily operation change) point :=
  ⟨liftPredicate operation change point parameter predicate, by
    obtain ⟨enumeration⟩ := predicate.property
    exact ⟨liftEnumeration operation change point parameter predicate supported enumeration⟩⟩

theorem lift_support (point : D) (parameter : F.obj point) (predicate : Power A point)
    (supported : IndexedCoveredPower.Supports operation point (change.app point parameter) predicate) :
    IndexedCoveredPower.Supports (parameterProjection operation change) point parameter
      (liftPower operation change point parameter predicate supported) :=
  fun _ admitted => admitted.2

theorem input_support (point : D) (entry : (baseFamily operation change).obj point) :
    IndexedCoveredPower.Supports operation point (change.app point entry.val.2) entry.val.1.val.2 := by
  have baseEq : entry.val.1.val.1 = change.app point entry.val.2 := entry.property
  rw [← baseEq]
  exact entry.val.1.property

def backward : NaturalHom (baseFamily operation change) (indexedFamily operation change) where
  app point entry :=
    ⟨(entry.val.2, liftPower operation change point entry.val.2 entry.val.1.val.2
      (input_support operation change point entry)),
      lift_support operation change point entry.val.2 entry.val.1.val.2
        (input_support operation change point entry)⟩
  naturality {first second} step entry := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Predicate.ext
      intro argument
      change (entry.val.1.val.2).val.holds
          ⟨⟨argument.1.1, step ≫ argument.1.2⟩, argument.2.val.1⟩ ∧
        argument.2.val.2 = F.map (step ≫ argument.1.2) entry.val.2 ↔
        (entry.val.1.val.2).val.holds
          ⟨⟨argument.1.1, step ≫ argument.1.2⟩, argument.2.val.1⟩ ∧
        argument.2.val.2 = F.map argument.1.2 (F.map step entry.val.2)
      rw [F.map_comp_apply]

theorem image_lift (point : D) (parameter : F.obj point) (predicate : Power A point)
    (supported : IndexedCoveredPower.Supports operation point (change.app point parameter) predicate) :
    imagePower (argumentProjection operation change) point
      (liftPower operation change point parameter predicate supported) = predicate := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨pair, same, admitted, _parameterEq⟩
    change pair.val.1 = argument.2 at same
    rw [same] at admitted
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact admitted
  · intro admitted
    refine ⟨⟨(argument.2, F.map argument.1.2 parameter), ?_⟩, rfl, admitted, rfl⟩
    exact (supported argument admitted).trans (change.naturality argument.1.2 parameter)

theorem lift_image (point : D) (entry : (indexedFamily operation change).obj point) :
    liftPower operation change point entry.val.1
      (imagePower (argumentProjection operation change) point entry.val.2)
      (projected_support operation change point entry) = entry.val.2 := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  constructor
  · rintro ⟨⟨other, same, admitted⟩, parameterEq⟩
    have otherParameter := entry.property ⟨argument.1, other⟩ admitted
    change other.val.2 = F.map argument.1.2 entry.val.1 at otherParameter
    change other.val.1 = argument.2.val.1 at same
    have pairEq := Subtype.ext (Prod.ext same (otherParameter.trans parameterEq.symm))
    rw [pairEq] at admitted
    rcases argument with ⟨⟨_, _⟩, _⟩
    exact admitted
  · intro admitted
    exact ⟨⟨argument.2, rfl, admitted⟩, entry.property argument admitted⟩

theorem forward_backward (point : D) (entry : (baseFamily operation change).obj point) :
    (forward operation change).app point ((backward operation change).app point entry) = entry := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact Prod.ext entry.property.symm
      (image_lift operation change point entry.val.2 entry.val.1.val.2
        (input_support operation change point entry))
  · rfl

theorem backward_forward (point : D) (entry : (indexedFamily operation change).obj point) :
    (backward operation change).app point ((forward operation change).app point entry) = entry := by
  apply Subtype.ext
  exact Prod.ext rfl (lift_image operation change point entry)

theorem forward_backward_hom :
    (backward operation change).comp (forward operation change) = identityHom (baseFamily operation change) := by
  apply NaturalHom.ext
  exact forward_backward operation change

theorem backward_forward_hom :
    (forward operation change).comp (backward operation change) = identityHom (indexedFamily operation change) := by
  apply NaturalHom.ext
  exact backward_forward operation change

def fibreEquiv (point : D) :
    (indexedFamily operation change).obj point ≃ (baseFamily operation change).obj point where
  toFun := (forward operation change).app point
  invFun := (backward operation change).app point
  left_inv := backward_forward operation change point
  right_inv := forward_backward operation change point

def sectionEquiv : (indexedFamily operation change).sections ≃ (baseFamily operation change).sections where
  toFun := (forward operation change).mapSection
  invFun := (backward operation change).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact backward_forward operation change point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact forward_backward operation change point (term.val point)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerBaseChange
