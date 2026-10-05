import Mettapedia.TypeTheory.ContextualSmallFamilyPowerClassification
import Mettapedia.GSLT.Logic.ContextualObservedMaterialFamilyControls

/-!
# Infinite future powers over actual material-indexed families

The result-indexed material family genuinely grows at every context.
Its stable subfamilies can admit members only after an arbitrary natural
stage. Their complete-future power codes are pairwise distinct already
at the initial context. Present membership alone identifies distinct codes.

The whole section/subfamily classifier has both actual inverse laws, and
the small-family universe decodes the whole power family. No occurrence,
representative or hypothetical small-section carrier is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyPowersControls

open _root_.CategoryTheory ContextualSmallFamilyPowers
open MaterialSets.Hypersets.PowerClassPresheafDescent.Controls
open Mettapedia.GSLT.ContextualObservedMaterialFamilyControls

def afterStage (threshold : Nat) : Subfamily results where
  holds argument := threshold ≤ stageIndex argument.1.1
  closed step admitted := admitted.trans (growthLe step.1.1)

abbrev classified (threshold : Nat) := classify results (afterStage threshold)
abbrev initialCode (threshold : Nat) := (classified threshold).val (point 0 0)

def arrive (stage : Nat) : point 0 0 ⟶ point stage 0 :=
  CategoryOfElements.homMk _ _ ((homOfLE (Nat.zero_le stage)).op.op)
    (observation.naturality ((homOfLE (Nat.zero_le stage)).op.op) _)

theorem threshold_at_stage (threshold stage : Nat) (argument : results.obj (point stage 0)) :
    member results (point stage 0) argument ((classified threshold).val (point stage 0)) ↔ threshold ≤ stage :=
  classified_member results (afterStage threshold) (point stage 0) argument

theorem initial_equality_observes_every_future (first second stage : Nat)
    (same : initialCode first = initialCode second) : first ≤ stage ↔ second ≤ stage := by
  have transported := congrArg ((power results).map (arrive stage)) same
  have firstNatural := (classified first).property (arrive stage)
  have secondNatural := (classified second).property (arrive stage)
  have equality := firstNatural.symm.trans (transported.trans secondNatural)
  have observed := congrArg (fun predicate => member results (point stage 0)
    (zeroSection.val (point stage 0)) predicate) equality
  exact (threshold_at_stage first stage _).symm.trans
    ((Iff.of_eq observed).trans (threshold_at_stage second stage _))

theorem infinitely_many_future_power_codes : Function.Injective initialCode := by
  intro first second same
  have toFirst := initial_equality_observes_every_future first second first same
  have toSecond := initial_equality_observes_every_future first second second same
  exact Nat.le_antisymm (toSecond.mpr (Nat.le_refl second)) (toFirst.mp (Nat.le_refl first))

theorem present_membership_agrees (argument : results.obj (point 0 0)) :
    member results (point 0 0) argument (initialCode 1) ↔
      member results (point 0 0) argument (initialCode 2) := by
  exact (threshold_at_stage 1 0 argument).trans
    ((by decide : (1 ≤ 0) ↔ (2 ≤ 0)).trans (threshold_at_stage 2 0 argument).symm)

theorem present_membership_does_not_determine_power :
    (∀ argument : results.obj (point 0 0),
      member results (point 0 0) argument (initialCode 1) ↔
        member results (point 0 0) argument (initialCode 2)) ∧ initialCode 1 ≠ initialCode 2 :=
  ⟨present_membership_agrees,
    fun same => (by decide : (1 : Nat) ≠ 2) (infinitely_many_future_power_codes same)⟩

theorem actual_classifier_roundtrip (threshold : Nat) :
    recover results (classified threshold) = afterStage threshold := recover_classify results _

theorem actual_section_roundtrip (threshold : Nat) :
    classify results (recover results (classified threshold)) = classified threshold := classify_recover results _

theorem actual_power_universe_decodes : ContextualSmallFamilyUniverse.decodedFamily
    (code results) = power results := whole_power_decodes results

namespace Parameter

open MaterialSets.Hypersets.CoveredFuturePowerClassifier
open ContextualSmallFamilyTypeFormerCoherence ContextualSmallFamilyPowerClassification

def tags : Stagesᵒᵖ ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev tagged := product material tags
abbrev forgetTags := firstProjection material tags
abbrev pulled := domainUnder forgetTags results

def tagSubfamily : Subfamily pulled where
  holds argument := argument.1.2.2 = true
  closed {first second} step available := by
    have preserved := congrArg Prod.snd step.1.2
    change first.1.2.2 = second.1.2.2 at preserved
    exact preserved.symm.trans available

abbrev classifyingMap := (parameterizedClassifier forgetTags results).symm tagSubfamily
abbrev powerSection := toSection forgetTags (power results) classifyingMap

def tagPoint (tag : Bool) : tagged.Elements := ⟨world 0, ((point 0 0).2, tag)⟩
abbrev tagCode (tag : Bool) : PowerAt results (point 0 0) := powerSection.val (tagPoint tag)

theorem forgetTags_identifies :
    forgetTags.app (world 0) (tagPoint true).2 = forgetTags.app (world 0) (tagPoint false).2 := rfl

theorem tags_are_distinct : (tagPoint true).2 ≠ (tagPoint false).2 := by
  intro same
  exact Bool.noConfusion (congrArg Prod.snd same)

theorem member_iff_tag (tag : Bool) (argument : results.obj (point 0 0)) :
    member results (point 0 0) argument (tagCode tag) ↔ tag = true := by
  have square := parameterized_member forgetTags results classifyingMap (tagPoint tag) argument
  rw [parameterized_right] at square
  exact square.symm

theorem parameterized_codes_distinguish_forgotten_tag : tagCode true ≠ tagCode false := by
  intro same
  have positive := (member_iff_tag true (zeroSection.val (point 0 0))).mpr rfl
  rw [same] at positive
  exact Bool.noConfusion ((member_iff_tag false _).mp positive)

theorem parameterized_classifier_roundtrip :
    parameterizedClassifier forgetTags results classifyingMap = tagSubfamily :=
  parameterized_right forgetTags results tagSubfamily

end Parameter

end Mettapedia.TypeTheory.ContextualSmallFamilyPowersControls
