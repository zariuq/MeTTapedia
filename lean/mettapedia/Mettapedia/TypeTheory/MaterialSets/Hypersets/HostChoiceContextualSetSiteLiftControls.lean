import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftSize
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftSubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetPowersControls

/-!
# Infinite and cyclic controls for the actual contextual model lift

The actual raised advancing site preserves infinitely many changing sets.
Their present member subsets are all empty, while their distinct future
thresholds remain distinct after embedding. Empty and a self-member loop
retain their different material values. A constructed natural Russell set
lies outside the old model's image at every raised world.

These controls concern the actual contextual set models and their natural
member decoders. They do not identify a fixed-site external code successor
with an internal material universe or infer native identity reflection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftCoherence
open HostChoiceContextualSetSiteLiftSubstitution HostChoiceContextualSetSiteLiftSize
open HostChoiceContextualSetInterpretation
open PowerClassPresheafDescent.Controls

universe u
variable {D : Type u} [Category.{u} D]

/-- Preservation is proved from the whole future membership image, rather
than from an empty present slice. -/
theorem embedding_empty (point : UpperSite (D := D)) :
    embedding.app point (emptySet.val point.down) = emptySet.val point := by
  apply (internal_extensionality point _ _).mp
  intro target arrow child
  constructor
  · intro available
    obtain ⟨original, _, belongs⟩ := (future_member_image arrow _ child).mp
      ((futureMember_iff arrow child _).mpr available)
    have member := (futureMember_iff arrow.down original _).mp belongs
    rw [emptySet.property arrow.down] at member
    exact (member_empty target.down original member).elim
  · intro available
    rw [emptySet.property arrow] at available
    exact (member_empty target child available).elim

theorem embedded_loop_self_member (point : UpperSite (D := D)) :
    Member point (embedding.app point (HostChoiceContextualSetInterpretationControls.loopSet.val point.down))
      (embedding.app point (HostChoiceContextualSetInterpretationControls.loopSet.val point.down)) :=
  (current_member_embedding_iff point _ _).mpr
    (HostChoiceContextualSetInterpretationControls.loop_self_member point.down)

theorem embedded_loop_ne_empty (point : UpperSite (D := D)) :
    embedding.app point (HostChoiceContextualSetInterpretationControls.loopSet.val point.down) ≠
      emptySet.val point := by
  intro same
  rw [← embedding_empty point] at same
  exact HostChoiceContextualSetInterpretationControls.loop_ne_empty point.down
    (embedding_injective point same)

namespace Infinite

abbrev site := UpperSite (D := Stagesᵒᵖ)

def raisedWorld (stage : ℕ) : site := PresheafSiteLift.Site.upFunctor.obj (world stage)

def raisedArrival (stage : ℕ) : raisedWorld 0 ⟶ raisedWorld stage :=
  PresheafSiteLift.Site.upFunctor.map (HostChoiceContextualSetPowersControls.Infinite.arrival stage)

noncomputable def lowerThreshold (threshold : ℕ) : (source (D := Stagesᵒᵖ)).sections :=
  ⟨fun point => (HostChoiceContextualSetPowersControls.Infinite.thresholdSet threshold).val point.down,
    fun arrow => (HostChoiceContextualSetPowersControls.Infinite.thresholdSet threshold).property arrow.down⟩

noncomputable def upperThreshold (threshold : ℕ) : (upperSets (D := Stagesᵒᵖ)).sections :=
  embedding.mapSection (lowerThreshold threshold)

theorem threshold_future (threshold : ℕ) (point target : site) (arrow : point ⟶ target)
    (child : upperSets.obj target) :
    FutureMember arrow child ((upperThreshold threshold).val point) ↔
      threshold+1 ≤ stageIndex target.down ∧
        child = embedding.app target (emptySet.val target.down) := by
  change FutureMember arrow child (embedding.app point ((lowerThreshold threshold).val point)) ↔ _
  refine (future_member_image arrow _ child).trans ?_
  constructor
  · rintro ⟨original, observed, belongs⟩
    have facts := (HostChoiceContextualSetPowersControls.Infinite.threshold_future threshold
      point.down target.down arrow.down original).mp belongs
    exact ⟨facts.1, observed.symm.trans (congrArg (embedding.app target) facts.2)⟩
  · rintro ⟨later, same⟩
    refine ⟨emptySet.val target.down, same.symm, ?_⟩
    exact (HostChoiceContextualSetPowersControls.Infinite.threshold_future threshold
      point.down target.down arrow.down _).mpr ⟨later, rfl⟩

theorem threshold_present_empty (threshold : ℕ) (child : upperSets.obj (raisedWorld 0)) :
    ¬ Member (raisedWorld 0) child ((upperThreshold threshold).val (raisedWorld 0)) := by
  intro belongs
  have late := ((threshold_future threshold _ _ (𝟙 _) child).mp belongs).1
  exact Nat.not_succ_le_zero threshold late

theorem threshold_distinct :
    Function.Injective (fun threshold => (upperThreshold threshold).val (raisedWorld 0)) := by
  intro first second same
  exact HostChoiceContextualSetPowersControls.Infinite.threshold_distinct
    (embedding_injective (raisedWorld 0) same)

theorem threshold_changes (threshold : ℕ) :
    FutureMember (raisedArrival (threshold+1))
      (embedding.app (raisedWorld (threshold+1)) (emptySet.val (world (threshold+1))))
      ((upperThreshold threshold).val (raisedWorld 0)) :=
  (threshold_future threshold _ _ _ _).mpr ⟨Nat.le_refl _, rfl⟩

theorem infinitely_many_preserved_changing_values :
    Function.Injective (fun threshold => (upperThreshold threshold).val (raisedWorld 0)) ∧
      ∀ threshold,
        (∀ child, ¬ Member (raisedWorld 0) child ((upperThreshold threshold).val (raisedWorld 0))) ∧
        FutureMember (raisedArrival (threshold+1))
          (embedding.app (raisedWorld (threshold+1)) (emptySet.val (world (threshold+1))))
          ((upperThreshold threshold).val (raisedWorld 0)) :=
  ⟨threshold_distinct, fun threshold => ⟨threshold_present_empty threshold, threshold_changes threshold⟩⟩

theorem present_extensionality_still_fails :
    ¬ (∀ first second : upperSets.obj (raisedWorld 0),
      (∀ child, Member (raisedWorld 0) child first ↔ Member (raisedWorld 0) child second) →
        first = second) := by
  intro reflection
  have same := reflection ((upperThreshold 0).val (raisedWorld 0))
    ((upperThreshold 1).val (raisedWorld 0)) (fun child =>
      ⟨fun belongs => (threshold_present_empty 0 child belongs).elim,
        fun belongs => (threshold_present_empty 1 child belongs).elim⟩)
  exact Nat.zero_ne_one (threshold_distinct same)

theorem new_upper_value_at_every_stage (stage : ℕ) :
    ∀ original : source.obj (raisedWorld stage),
      embedding.app (raisedWorld stage) original ≠ newRussellSet.val (raisedWorld stage) :=
  newRussellSet_not_embedded (raisedWorld stage)

/-- The native comparison decodes the actual acquired child value. -/
noncomputable def acquiredMemberCode (threshold : ℕ) : lowerNative.obj
    ⟨raisedWorld (threshold+1), (lowerThreshold threshold).val (raisedWorld (threshold+1))⟩ :=
  (HostChoiceContextualHypersetModel.memberDecoder
    ⟨world (threshold+1), (HostChoiceContextualSetPowersControls.Infinite.thresholdSet threshold).val
      (world (threshold+1))⟩).symm
    ⟨emptySet.val (world (threshold+1)),
      (HostChoiceContextualSetPowersControls.Infinite.threshold_future threshold
        _ _ (𝟙 _) _).mpr ⟨Nat.le_refl _, rfl⟩⟩

theorem acquiredMemberCode_value (threshold : ℕ) :
    (HostChoiceContextualHypersetModel.memberDecoder
      (upperContext.obj
        ⟨raisedWorld (threshold+1), (lowerThreshold threshold).val (raisedWorld (threshold+1))⟩)
      (codeEquiv _ (acquiredMemberCode threshold))).val =
        embedding.app (raisedWorld (threshold+1)) (emptySet.val (world (threshold+1))) := by
  have value := code_value (D := Stagesᵒᵖ)
    (show (source (D := Stagesᵒᵖ)).Elements from
      ⟨raisedWorld (threshold+1), (lowerThreshold threshold).val (raisedWorld (threshold+1))⟩)
    (acquiredMemberCode threshold)
  exact value.symm.trans (congrArg (embedding.app (raisedWorld (threshold+1)))
    (congrArg Subtype.val ((HostChoiceContextualHypersetModel.memberDecoder _).apply_symm_apply _)))

def taggedParameters : site ⥤ Type 1 where
  obj point := Bool × source.obj point
  map arrow := TypeCat.ofHom fun parameter => ⟨parameter.1, source.map arrow parameter.2⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro parameter
    exact Prod.ext rfl (source.map_id_apply point parameter.2)
  map_comp first later := by
    apply ConcreteCategory.hom_ext
    intro parameter
    exact Prod.ext rfl (source.map_comp_apply first later parameter.2)

def taggedParent : NaturalHom taggedParameters source where
  app _ parameter := parameter.2
  naturality _ _ := rfl

def collapseTags : NaturalHom taggedParameters taggedParameters where
  app _ parameter := ⟨false, parameter.2⟩
  naturality _ _ := rfl

theorem collapseTags_noninjective (point : site) :
    ¬ Function.Injective (collapseTags.app point) := by
  intro faithful
  have same := faithful (show collapseTags.app point ⟨false, emptySet.val point.down⟩ =
    collapseTags.app point ⟨true, emptySet.val point.down⟩ from rfl)
  exact Bool.false_ne_true (congrArg Prod.fst same)

theorem original_parameters_remain_distinct (point : site) (parent : source.obj point) :
    (⟨point, (false, parent)⟩ : taggedParameters.Elements) ≠ ⟨point, (true, parent)⟩ := by
  intro same
  exact Bool.false_ne_true (congrArg (fun parameter : taggedParameters.Elements => parameter.2.1) same)

theorem noninjective_parameter_decoder_square (point : taggedParameters.Elements)
    (code : (lowerUnder (collapseTags.comp taggedParent)).obj point) :
    (forwardUnder (collapseTags.comp taggedParent)).app point code =
      (forwardUnder taggedParent).app ((ContextualSmallFamilyUniverse.elementMap collapseTags).obj point) code :=
  forward_substitution taggedParent collapseTags point code

theorem noninjective_parameter_section_square (term : (lowerUnder taggedParent).sections) :
    sectionsUnder (collapseTags.comp taggedParent) (lowerSectionChange taggedParent collapseTags term) =
      upperSectionChange taggedParent collapseTags (sectionsUnder taggedParent term) :=
  section_substitution taggedParent collapseTags term

end Infinite

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftControls
