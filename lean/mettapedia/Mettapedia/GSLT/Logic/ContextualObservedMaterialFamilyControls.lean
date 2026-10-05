import Mettapedia.GSLT.Logic.ContextualObservedMaterialFamily
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraControls
import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers

/-!
# Growing dependent families over actual observed material members

The material member, rather than a chosen execution receipt, indexes a
small numeric family. Its predicate ranges over all representatives; their
retained result agrees. Context transport preserves a number's bound while
the bound grows at every stage. New members are not images of old members.

Each actual fibre is compared with the independently formed finite interval,
and the whole varying family has its constructed future-universe classifier
and decoder. Provenance aliases cannot be recovered through the observation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedMaterialFamilyControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open ContextualObservedCoalgebraControls

abbrev transition := emptyCoalgebra source
abbrev material := ContextualObservedMaterialFamily.members transition observes worlds arrows atomCoding
abbrev observation := ContextualObservedMaterialFamily.observation transition observes worlds arrows atomCoding

def resultBounds (point : material.Elements) (number : Nat) : Prop :=
  ∀ argument : source.obj point.1, observation.app point.1 argument = point.2 →
    number ≤ argument.1.1 + stageIndex point.1

theorem bound_follows {first second : material.Elements} (step : first ⟶ second)
    {number : Nat} (bound : resultBounds first number) : resultBounds second number := by
  intro next representsNext
  obtain ⟨argument, represents⟩ :=
    ContextualObservedMaterialFamily.observation_cover transition observes worlds arrows atomCoding first.1 first.2
  have observedNext : observation.app second.1 (source.map step.1 argument) = second.2 :=
    (observation.naturality step.1 argument).symm.trans
      ((congrArg (material.map step.1) represents).trans step.2)
  have equality := observedNext.trans representsNext.symm
  have values := congrArg Subtype.val equality
  have readings := equality_preserves_reading second.1 (source.map step.1 argument) next values ⟨0, by decide⟩
  change argument.1.1 = next.1.1 at readings
  have growth := growthLe step.1
  exact (bound argument represents).trans (by rw [readings]; exact Nat.add_le_add_left growth _)

def results : material.Elements ⥤ Type where
  obj point := {number : Nat // resultBounds point number}
  map step := TypeCat.ofHom fun number => ⟨number.val, bound_follows step number.property⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro number
    exact Subtype.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro number
    exact Subtype.ext rfl

def point (stage reading : Nat) : material.Elements :=
  ⟨world stage, observation.app (world stage) (state stage reading 0 false false)⟩

theorem resultBounds_point (stage reading number : Nat) :
    resultBounds (point stage reading) number ↔ number ≤ reading + stage := by
  constructor
  · intro bound
    exact bound (state stage reading 0 false false) rfl
  · intro bound argument represents
    have same := equality_preserves_reading (world stage) argument (state stage reading 0 false false)
      (congrArg Subtype.val represents) ⟨0, by decide⟩
    change argument.1.1 = reading at same
    change number ≤ argument.1.1 + stage
    rw [same]
    exact bound

def fibreEquiv (stage reading : Nat) : results.obj (point stage reading) ≃ Fin (reading + stage + 1) where
  toFun number := ⟨number.val, Nat.lt_succ_of_le ((resultBounds_point stage reading number.val).mp number.property)⟩
  invFun number := ⟨number.val, (resultBounds_point stage reading number.val).mpr (Nat.le_of_lt_succ number.isLt)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Fin.ext rfl

def advancePoint (stage reading : Nat) : point stage reading ⟶ point (stage + 1) reading :=
  CategoryOfElements.homMk _ _ (IndexedCoalgebraQuotientControls.advance stage)
    (observation.naturality (IndexedCoalgebraQuotientControls.advance stage) _)

def newlyAdmitted (stage reading : Nat) : results.obj (point (stage + 1) reading) :=
  ⟨reading + (stage + 1), (resultBounds_point (stage + 1) reading _).mpr (Nat.le_refl _)⟩

theorem new_member_every_stage (stage reading : Nat) :
    ¬ ∃ earlier : results.obj (point stage reading),
      results.map (advancePoint stage reading) earlier = newlyAdmitted stage reading := by
  rintro ⟨earlier, same⟩
  have numbers := congrArg Subtype.val same
  change earlier.val = reading + (stage + 1) at numbers
  have bound := (resultBounds_point stage reading earlier.val).mp earlier.property
  omega

def zeroSection : results.sections :=
  ⟨fun _ => ⟨0, fun _ _ => Nat.zero_le _⟩, fun {_ _} _ => Subtype.ext rfl⟩

abbrev familyCode := Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.classifier results

theorem whole_family_decodes : Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.decodedFamily familyCode = results :=
  Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.decoded_classifier_eq results

theorem reading_parameters_remain_infinite : Function.Injective
    (fun reading => observation.app (world 0) (state 0 reading 0 false false)) := by
  intro first second same
  exact equality_preserves_reading (world 0) _ _ (congrArg Subtype.val same) ⟨0, by decide⟩

abbrev parameters : material.Elements ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev booleanBody : results.Elements ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def alwaysTrue : NatTrans
    (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.overArguments results parameters) booleanBody where
  app _ := TypeCat.ofHom fun _ => true
  naturality _ _ _ := rfl

def onlyZero : NatTrans
    (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.overArguments results parameters) booleanBody where
  app argument := TypeCat.ofHom fun _ => decide (argument.2.val = 0)
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro _
    have numbers := congrArg Subtype.val step.2
    change first.2.val = second.2.val at numbers
    exact congrArg (fun number => decide (number = 0)) numbers.symm

abbrev trueProduct := Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.piCurry results booleanBody alwaysTrue
abbrev zeroProduct := Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.piCurry results booleanBody onlyZero

theorem trueProduct_beta (point : material.Elements) (argument : results.obj point) :
    Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody point
      (trueProduct.app point PUnit.unit) argument = true :=
  congrArg (fun operation : NatTrans
    (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.overArguments results parameters) booleanBody =>
      operation.app ⟨point, argument⟩ PUnit.unit)
        (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.pi_uncurry_curry results booleanBody alwaysTrue)

theorem zeroProduct_beta (point : material.Elements) (argument : results.obj point) :
    Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody point
      (zeroProduct.app point PUnit.unit) argument = decide (argument.val = 0) :=
  congrArg (fun operation : NatTrans
    (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.overArguments results parameters) booleanBody =>
      operation.app ⟨point, argument⟩ PUnit.unit)
        (Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.pi_uncurry_curry results booleanBody onlyZero)

theorem same_all_present_applications (argument : results.obj (point 0 0)) :
    Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody (point 0 0)
      (trueProduct.app (point 0 0) PUnit.unit) argument =
    Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody (point 0 0)
      (zeroProduct.app (point 0 0) PUnit.unit) argument := by
  have zero := Nat.eq_zero_of_le_zero ((resultBounds_point 0 0 argument.val).mp argument.property)
  rw [trueProduct_beta, zeroProduct_beta, zero]
  rfl

theorem full_future_products_differ : trueProduct.app (point 0 0) PUnit.unit ≠
    zeroProduct.app (point 0 0) PUnit.unit := by
  intro same
  have atFuture := congrArg
    (fun term => Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.pi results booleanBody |>.map
      (advancePoint 0 0) term) same
  have first := congrArg (fun map => map PUnit.unit) (trueProduct.naturality (advancePoint 0 0))
  have second := congrArg (fun map => map PUnit.unit) (zeroProduct.naturality (advancePoint 0 0))
  have equality := first.trans (atFuture.trans second.symm)
  change trueProduct.app (point 1 0) PUnit.unit = zeroProduct.app (point 1 0) PUnit.unit at equality
  have applications := congrArg
    (fun term => Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers.evaluateValue results booleanBody
      (point 1 0) term (newlyAdmitted 0 0)) equality
  rw [trueProduct_beta, zeroProduct_beta] at applications
  change true = false at applications
  exact Bool.noConfusion applications

def tags : Stagesᵒᵖ ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def rawTag : NaturalHom source tags where
  app _ argument := argument.2.2
  naturality _ _ := rfl

theorem provenance_has_no_material_factor : ¬ ∃ consumer : NaturalHom material tags,
    observation.comp consumer = rawTag := by
  rintro ⟨consumer, factors⟩
  have aliases := (ContextualObservedMaterialFamily.observation_eq_iff transition observes worlds arrows atomCoding
    (world 0) (state 0 0 0 false true) (state 0 0 0 false false)).mpr
      (same_values_observed _ _ _ rfl)
  have first := congrArg (fun map : NaturalHom source tags => map.app (world 0) (state 0 0 0 false true)) factors
  have second := congrArg (fun map : NaturalHom source tags => map.app (world 0) (state 0 0 0 false false)) factors
  exact Bool.noConfusion (first.symm.trans ((congrArg (consumer.app (world 0)) aliases).trans second))

end Mettapedia.GSLT.ContextualObservedMaterialFamilyControls
