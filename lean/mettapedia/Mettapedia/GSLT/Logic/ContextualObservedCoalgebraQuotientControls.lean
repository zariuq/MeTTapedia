import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraQuotient
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraControls
import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormers

/-!
# Dependent consumers of infinite observed execution classes

The observed quotient keeps infinitely many result readings and permits
new occurrence aliases at every context. A dependent consumer's small
result carrier is bounded by the retained result plus the context stage;
its members genuinely grow at every future stage. Its full future code
and decoder are constructed from that actual family.

A raw provenance-bit consumer has no natural factor through this quotient,
although the dependent numeric-result family and a whole result-value
section do. Quotient coverage does not choose a raw occurrence inverse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedCoalgebraQuotientControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open ContextualObservedCoalgebraControls

abbrev coalgebra := emptyCoalgebra source
abbrev quotient := ContextualObservedCoalgebraQuotient.family coalgebra observes worlds arrows atomCoding
abbrev projection := ContextualObservedCoalgebraQuotient.projection coalgebra observes worlds arrows atomCoding

abbrev resultParameters : Stagesᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def resultReading : NaturalHom source resultParameters where
  app _ term := term.1.1
  naturality _ _ := rfl

theorem result_compatible : ContextualObservedCoalgebraQuotient.Compatible coalgebra observes resultReading := by
  intro point left right related
  exact (ContextualObservedCoalgebra.observed_bisimilar_atoms coalgebra observes related
    (⟨0, by decide⟩, left.1.1)).mp rfl

def result : NaturalHom quotient resultParameters :=
  ContextualObservedCoalgebraQuotient.descend coalgebra observes worlds arrows atomCoding resultReading result_compatible

theorem result_beta (point : Stagesᵒᵖ) (argument : source.obj point) :
    result.app point (projection.app point argument) = argument.1.1 := rfl

theorem result_follows {first second : quotient.Elements} (step : first ⟶ second) :
    result.app first.1 first.2 = result.app second.1 second.2 :=
  (result.naturality step.1 first.2).trans (congrArg (result.app second.1) step.2)

def results : quotient.Elements ⥤ Type where
  obj point := {number : Nat // number ≤ result.app point.1 point.2 + stageIndex point.1}
  map {first second} step := TypeCat.ofHom fun number => ⟨number.val, by
    have same := result_follows step
    have growth := growthLe step.1
    exact number.property.trans (by rw [same]; exact Nat.add_le_add_left growth _)⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro number
    exact Subtype.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro number
    exact Subtype.ext rfl

def retainedResult : results.sections :=
  ⟨fun point => ⟨result.app point.1 point.2, Nat.le_add_right _ _⟩, by
    intro first second step
    apply Subtype.ext
    exact result_follows step⟩

def point (stage reading : Nat) : quotient.Elements :=
  ⟨world stage, projection.app (world stage) (state stage reading 0 false false)⟩

def advancePoint (stage reading : Nat) : point stage reading ⟶ point (stage + 1) reading :=
  CategoryOfElements.homMk _ _ (IndexedCoalgebraQuotientControls.advance stage) rfl

def newlyAdmitted (stage reading : Nat) : results.obj (point (stage + 1) reading) :=
  ⟨reading + (stage + 1), Nat.le_refl _⟩

theorem new_dependent_member_every_stage (stage reading : Nat) :
    ¬ ∃ earlier : results.obj (point stage reading),
      results.map (advancePoint stage reading) earlier = newlyAdmitted stage reading := by
  rintro ⟨earlier, same⟩
  have numbers := congrArg Subtype.val same
  change earlier.val = reading + (stage + 1) at numbers
  have bound := earlier.property
  change earlier.val ≤ reading + stage at bound
  omega

theorem retained_result_values_infinite : Function.Injective
    (fun reading => (retainedResult.val (point 0 reading)).val) := by
  intro first second same
  exact same

theorem family_code_decodes : Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.decodedFamily
    (Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.classifier results) = results :=
  Mettapedia.TypeTheory.ContextualSmallFamilyUniverse.decoded_classifier_eq results

def tags : Stagesᵒᵖ ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def rawTag : NaturalHom source tags where
  app _ term := term.2.2
  naturality _ _ := rfl

theorem raw_tag_has_no_factor : ¬ ∃ consumer : NaturalHom quotient tags,
    projection.comp consumer = rawTag := by
  rintro ⟨consumer, factors⟩
  have aliases := (ContextualObservedCoalgebraQuotient.projection_eq_iff coalgebra observes worlds arrows atomCoding
    (world 0) (state 0 0 0 false true) (state 0 0 0 false false)).mpr
      (same_values_observed _ _ _ rfl)
  have first := congrArg (fun map : NaturalHom source tags => map.app (world 0) (state 0 0 0 false true)) factors
  have second := congrArg (fun map : NaturalHom source tags => map.app (world 0) (state 0 0 0 false false)) factors
  exact Bool.noConfusion (first.symm.trans ((congrArg (consumer.app (world 0)) aliases).trans second))

theorem incompatible_tag_criterion : ¬ ContextualObservedCoalgebraQuotient.Compatible coalgebra observes rawTag :=
  fun compatible => raw_tag_has_no_factor
    ((ContextualObservedCoalgebraQuotient.descends_iff coalgebra observes worlds arrows atomCoding rawTag).mpr compatible)

theorem whole_result_factor_is_unique : ∃! consumer : NaturalHom quotient resultParameters,
    projection.comp consumer = resultReading :=
  ContextualObservedCoalgebraQuotient.unique_descend coalgebra observes worlds arrows atomCoding resultReading result_compatible

end Mettapedia.GSLT.ContextualObservedCoalgebraQuotientControls
