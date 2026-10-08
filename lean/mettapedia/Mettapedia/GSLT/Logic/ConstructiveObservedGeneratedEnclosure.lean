import Mettapedia.GSLT.Logic.ConstructiveObservedMaterialControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedEnclosure

/-!
# Generated enclosure coherence for the constructive observed model

The general mixed-bound enclosure is compared with the independently
constructed enclosure of the observed family grammar. All codes, complete
future products and hereditary W families keep their actual dictionaries.

In the infinite growing instance, the continuation family and a constantly
empty separated family have the same present material carrier but different
future fibres. A present carrier therefore cannot decode generated families.
Enlarging that carrier cannot repair the missing information. Whole member
decoding instead retains the generated code and its restriction maps.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.GSLT.ConstructiveObservedGeneratedEnclosure

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ConstructiveObservedMaterialFamilies

section General

universe u
variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → ContextualCoalgebraLabelledGraph.State A → Prop)
variable (atomCoding : ArgumentCoding Atom)

theorem enclosure_agreement {base : Upper (D := D) ⥤ Type (u+1)} (point : base.Elements) :
    ContextualAuthoredGeneratedEnclosure.enclosure.{u+1,u+1} (raisedWorlds worlds) (raisedArrows arrows)
      (Seed worlds arrows source atoms atomCoding) (seedModel worlds arrows source atoms atomCoding) point =
      enclosure worlds arrows source atoms atomCoding base point := by
  apply HSet.ext
  intro value
  rw [ContextualAuthoredGeneratedEnclosure.mem_enclosure_iff.{u+1,u+1}]
  change (∃ code : Code worlds arrows source atoms atomCoding base,
    HSet.enlarge.{u+1,u+2} (code.decode.models point).carrier = value) ↔ value ∈ HSet.imageUp _
  rw [HSet.mem_imageUp_iff]
  rfl

end General

namespace Controls

open ConstructiveObservedMaterialControls

abbrev active := continuationCode worlds arrows dynamics atoms atomCoding
abbrev nativeWorlds := raisedWorlds worlds
abbrev nativeArrows := raisedArrows arrows
abbrev nativeSeeds := Seed worlds arrows dynamics atoms atomCoding
abbrev nativeModels := seedModel worlds arrows dynamics atoms atomCoding
abbrev Codes := Code worlds arrows dynamics atoms atomCoding params

def nowhere : ContextualReceiptFamilyModels.StablePredicate active.decode.native where
  holds _ _ := False
  map _ _ impossible := impossible.elim

def inactive : Codes := active.separate nowhere

def typeReading (code : Codes) (stage : Nat) : HSet.{2} :=
  ContextualAuthoredGeneratedEnclosure.reading nativeWorlds nativeArrows nativeSeeds nativeModels code (task stage)

theorem inactive_empty (stage : Nat) : ¬ Nonempty (inactive.decode.native.obj (task stage)) := by
  rintro ⟨witness⟩
  exact witness.property

theorem inactive_carrier (stage : Nat) : (inactive.decode.models (task stage)).carrier = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  exact inactive_empty stage ⟨(inactive.decode.models (task stage)).decode ⟨value, member⟩⟩

theorem active_initial_carrier : (active.decode.models (task 0)).carrier = ∅ := by
  apply HSet.eq_empty_iff.mpr
  intro value member
  exact initial_continuations_empty ⟨(active.decode.models (task 0)).decode ⟨value, member⟩⟩

theorem same_present_carrier : typeReading active 0 = typeReading inactive 0 :=
  (ContextualAuthoredGeneratedEnclosure.reading_eq_iff nativeWorlds nativeArrows nativeSeeds nativeModels
    active inactive (task 0)).mpr (active_initial_carrier.trans (inactive_carrier 0).symm)

theorem different_future_fibres :
    Nonempty (active.decode.native.obj (task 2)) ∧ ¬ Nonempty (inactive.decode.native.obj (task 2)) :=
  ⟨⟨cyclicChild⟩, inactive_empty 2⟩

/-- The distinguishing consumer asks about a genuine later native fibre.
It is insensitive to the choice of material graph representatives. -/
theorem future_support_does_not_descend :
    ¬ ∃ read : HSet.{2} → Prop,
      ∀ code : Codes, read (typeReading code 0) ↔ Nonempty (code.decode.native.obj (task 2)) := by
  rintro ⟨read, agrees⟩
  have supported := (agrees active).mpr different_future_fibres.1
  rw [same_present_carrier] at supported
  exact different_future_fibres.2 ((agrees inactive).mp supported)

theorem both_code_carriers_enclosed :
    typeReading active 0 ∈ enclosure worlds arrows dynamics atoms atomCoding params (task 0) ∧
      typeReading inactive 0 ∈ enclosure worlds arrows dynamics atoms atomCoding params (task 0) :=
  ⟨generated_enclosed worlds arrows dynamics atoms atomCoding active (task 0),
    generated_enclosed worlds arrows dynamics atoms atomCoding inactive (task 0)⟩

theorem enlargement_does_not_restore_future_support :
    ¬ ∃ read : HSet.{3} → Prop,
      ∀ code : Codes, read (HSet.enlarge.{2,3} (typeReading code 0)) ↔
        Nonempty (code.decode.native.obj (task 2)) := by
  rintro ⟨read, agrees⟩
  exact future_support_does_not_descend ⟨fun value => read (HSet.enlarge value), agrees⟩

def dependentPi := continuationPiCode worlds arrows dynamics atoms atomCoding

theorem current_function_survives_as_data :
    Nonempty ((argument : domain.native.obj (task 0)) →
      body.native.obj ⟨(task 0).1, ⟨(task 0).2, argument⟩⟩) := ⟨presentProduct⟩

theorem enlarged_future_product_empty :
    ¬ Nonempty {value : HSet.{2} // value ∈ typeReading dependentPi 0} := by
  rintro ⟨member⟩
  exact full_future_product_empty
    ⟨ContextualAuthoredGeneratedEnclosure.fibreDecoder nativeWorlds nativeArrows nativeSeeds nativeModels
      dependentPi (task 0) member⟩

theorem next_level_is_proper : ¬ Function.Surjective (HSet.enlarge.{2,3}) :=
  HSet.not_surjective_lift

end Controls

end Mettapedia.GSLT.ConstructiveObservedGeneratedEnclosure
