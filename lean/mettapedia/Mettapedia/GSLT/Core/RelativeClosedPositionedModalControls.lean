import Mettapedia.GSLT.Core.RelativeClosedPositionedModalControlData
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalReadout

/-!
# Complete generated positioned-modal controls

The predicate inputs are independently classified on the actual mapped assay
and outgoing objects. The resulting family is read from the genuine image of
the generated modal name. Both rule inputs, the exact successor reduct and
the supplied predicate parameter participate in the answer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open Mettapedia.CategoryTheory ElementaryTypePredicateReadout
open PositionedRewritePredicatePower

abbrev source := RelativeClosedPositionedModalControlData.theory
abbrev selected := RelativeClosedPositionedModalControlData.selected
abbrev base := RelativeClosedPositionedModalControlData.base
abbrev frame := RelativeClosedPositionedModalControlData.frame
abbrev rule := RelativeClosedPositionedModalControlData.rule
abbrev Instance := base.obj rule.parameters
abbrev Assay := base.obj frame.assay
abbrev Outgoing := base.obj (frame.assay ⨯ source.program)

def instanceOfPair (pair : Nat × Nat) : Instance :=
  (Types.binaryProductIso Nat Nat).inv pair

def assayFirst : Assay ⟶ Nat := base.map (prod.fst : frame.assay ⟶ source.program)
def outgoingAssay : Outgoing ⟶ Assay := base.map (prod.fst : frame.assay ⨯ source.program ⟶ frame.assay)
def outgoingReduct : Outgoing ⟶ Nat := base.map (prod.snd : frame.assay ⨯ source.program ⟶ source.program)

theorem instantiate_first (pair : Nat × Nat) :
    assayFirst (base.map frame.instantiate (instanceOfPair pair)) = pair.1 := by
  have complete : base.map frame.instantiate ≫ assayFirst =
      base.map (RelativeClosedPositionedModalControlData.upward.map
        (prod.fst : Nat ⨯ Nat ⟶ Nat)) :=
    (base.map_comp frame.instantiate (prod.fst : frame.assay ⟶ source.program)).symm.trans
      (congrArg base.map (prod.lift_fst _ _))
  have reading := congrArg (fun arrow : Instance ⟶ Nat => arrow (instanceOfPair pair)) complete
  exact reading.trans (congrArg (fun arrow : Nat × Nat ⟶ Nat => arrow pair)
    (Types.binaryProductIso_inv_comp_fst Nat Nat))

theorem outgoing_assay_read (pair : Nat × Nat) :
    outgoingAssay (base.map frame.outgoing (instanceOfPair pair)) =
      base.map frame.instantiate (instanceOfPair pair) := by
  have complete : base.map frame.outgoing ≫ outgoingAssay = base.map frame.instantiate :=
    (base.map_comp frame.outgoing (prod.fst : frame.assay ⨯ source.program ⟶ frame.assay)).symm.trans
      (congrArg base.map (prod.lift_fst _ _))
  exact congrArg (fun arrow : Instance ⟶ Assay => arrow (instanceOfPair pair)) complete

theorem outgoing_reduct_read (pair : Nat × Nat) :
    outgoingReduct (base.map frame.outgoing (instanceOfPair pair)) = pair.1 + pair.2 + 1 := by
  have complete : base.map frame.outgoing ≫ outgoingReduct = base.map rule.right :=
    (base.map_comp frame.outgoing (prod.snd : frame.assay ⨯ source.program ⟶ source.program)).symm.trans
      (congrArg base.map (prod.lift_snd _ _))
  exact (congrArg (fun arrow : Instance ⟶ Nat => arrow (instanceOfPair pair)) complete).trans
    (RelativeClosedPositionedModalControlData.the_actual_reduct_retains_both_numbers pair)

theorem forget_read (pair : Nat × Nat) :
    base.map frame.forget (instanceOfPair pair) = pair.2 :=
  congrArg (fun arrow : Nat × Nat ⟶ Nat => arrow pair)
    (Types.binaryProductIso_inv_comp_snd Nat Nat)

private theorem whisker_right_apply {X Y : Type} (mapping : X ⟶ Y) (value : X) (parameter : Nat) :
    (mapping ▷ Nat) (value, parameter) = (mapping value, parameter) := rfl

def relies : Subobject (Assay ⊗ Nat) :=
  fromSet {supplied | assayFirst (fst Assay Nat supplied) > 0}

def postcondition : Subobject (Outgoing ⊗ Nat) :=
  fromSet {supplied | outgoingReduct (fst Outgoing Nat supplied) >
    assayFirst (outgoingAssay (fst Outgoing Nat supplied)) + 1 + snd Outgoing Nat supplied}

def relyName : Nat ⟶ power doctrine Assay := name doctrine relies
def postName : Nat ⟶ power doctrine Outgoing := name doctrine postcondition
def inputs : Nat ⟶ profiles doctrine Assay Outgoing := lift relyName postName

theorem independent_rely_read : family doctrine (inputs ≫ fst _ _) = relies :=
  (congrArg (family doctrine) (lift_fst relyName postName)).trans (family_name doctrine relies)

theorem independent_post_read : family doctrine (inputs ≫ snd _ _) = postcondition :=
  (congrArg (family doctrine) (lift_snd relyName postName)).trans (family_name doctrine postcondition)

theorem relies_read (value : Assay) (parameter : Nat) :
    Contains relies (value, parameter) ↔ assayFirst value > 0 :=
  contains_fromSet _ _

theorem post_read (value : Outgoing) (parameter : Nat) :
    Contains postcondition (value, parameter) ↔
      outgoingReduct value > assayFirst (outgoingAssay value) + 1 + parameter :=
  contains_fromSet _ _

theorem relies_at_instance (pair : Nat × Nat) (parameter : Nat) :
    Contains (doctrine.reindex (base.map frame.instantiate ▷ Nat) relies)
      (instanceOfPair pair, parameter) ↔ pair.1 > 0 := by
  rw [contains_reindex, whisker_right_apply]
  exact (relies_read _ parameter).trans (by rw [instantiate_first])

theorem post_at_instance (pair : Nat × Nat) (parameter : Nat) :
    Contains (doctrine.reindex (base.map frame.outgoing ▷ Nat) postcondition)
      (instanceOfPair pair, parameter) ↔ parameter < pair.2 := by
  rw [contains_reindex, whisker_right_apply]
  exact (post_read _ parameter).trans (by
    rw [outgoing_assay_read, instantiate_first, outgoing_reduct_read]
    change pair.1 + pair.2 + 1 > pair.1 + 1 + parameter ↔ parameter < pair.2
    omega)

def condition : Subobject (Instance ⊗ Nat) :=
  conditionAt doctrine (base.map frame.instantiate) (base.map frame.outgoing) inputs

theorem condition_read (pair : Nat × Nat) (parameter : Nat) :
    Contains condition (instanceOfPair pair, parameter) ↔ (pair.1 > 0 → parameter < pair.2) := by
  change Contains (doctrine.algebra _ |>.himp
    (doctrine.reindex (base.map frame.instantiate ▷ Nat) (family doctrine (inputs ≫ fst _ _)))
    (doctrine.reindex (base.map frame.outgoing ▷ Nat) (family doctrine (inputs ≫ snd _ _)))) _ ↔ _
  rw [independent_rely_read, independent_post_read, contains_implication,
    relies_at_instance, post_at_instance]

def introduction : Subobject (Nat ⊗ Nat) :=
  doctrine.forallAlong (base.map frame.forget ▷ Nat) condition

theorem introduction_read (focus parameter : Nat) :
    Contains introduction (focus, parameter) ↔ parameter < focus := by
  change Contains (doctrine.forallAlong (base.map frame.forget ▷ Nat) condition) _ ↔ _
  rw [contains_forall]
  constructor
  · intro held
    exact (condition_read (1, focus) parameter).mp
      (held (instanceOfPair (1, focus), parameter) (by
        rw [whisker_right_apply, forget_read])) (by omega)
  · intro held supplied reading
    let pair : Nat × Nat := (Types.binaryProductIso Nat Nat).hom supplied.1
    have retained : instanceOfPair pair = supplied.1 :=
      congrArg (fun arrow : Instance ⟶ Instance => arrow supplied.1)
        (Iso.hom_inv_id (Types.binaryProductIso Nat Nat))
    have tupleRead : (instanceOfPair pair, supplied.2) = supplied := by
      apply Prod.ext
      · exact retained
      · rfl
    have coordinates : (pair.2, supplied.2) = (focus, parameter) := by
      have actual : (base.map frame.forget ▷ Nat) (instanceOfPair pair, supplied.2) =
          (focus, parameter) := (congrArg (base.map frame.forget ▷ Nat)
            tupleRead).trans reading
      rwa [whisker_right_apply, forget_read] at actual
    have first : pair.2 = focus := congrArg Prod.fst coordinates
    have second : supplied.2 = parameter := congrArg Prod.snd coordinates
    have guarded : Contains condition (instanceOfPair pair, supplied.2) :=
      (condition_read pair supplied.2).mpr (fun _ => by rw [first, second]; exact held)
    exact tupleRead ▸ guarded

/-- This is the interpreted quotient name, with only earned endpoint casts. -/
def modalImage : profiles doctrine Assay Outgoing ⟶ power doctrine Nat :=
  RelativeClosedPositionedModalReadout.imageAt doctrine source selected base (some (ULift.up false))

def output : Subobject (Nat ⊗ Nat) := family doctrine (inputs ≫ modalImage)

theorem output_exact : output = doctrine.existsAlong (base.map frame.focus ▷ Nat) introduction := by
  unfold output modalImage
  rw [RelativeClosedPositionedModalReadout.imageAt_complete]
  exact supplied_evaluation doctrine (base.map frame.forget) (base.map frame.focus)
    (base.map frame.instantiate) (base.map frame.outgoing) inputs

theorem output_read (focus parameter : Nat) :
    Contains output (focus, parameter) ↔ parameter < focus := by
  rw [output_exact, contains_exists]
  constructor
  · rintro ⟨supplied, admitted, reaches⟩
    change supplied = (focus, parameter) at reaches
    subst supplied
    exact (introduction_read focus parameter).mp admitted
  · intro admitted
    exact ⟨(focus, parameter), (introduction_read focus parameter).mpr admitted, rfl⟩

theorem the_generated_operator_retains_the_parameter :
    Contains output (2, 0) ∧ ¬ Contains output (2, 2) :=
  ⟨(output_read 2 0).mpr (by omega), fun held => Nat.lt_irrefl 2 ((output_read 2 2).mp held)⟩

def future : Nat ⟶ Nat := TypeCat.ofHom Nat.succ

theorem future_read (focus parameter : Nat) :
    Contains (family doctrine ((future ≫ inputs) ≫ modalImage)) (focus, parameter) ↔
      parameter + 1 < focus := by
  have complete := (family_substitution doctrine future (inputs ≫ modalImage)).trans
    (congrArg (family doctrine) (Category.assoc future inputs modalImage).symm)
  rw [← complete, contains_reindex]
  exact output_read focus (parameter + 1)

theorem the_actual_future_changes_the_answer :
    Contains output (1, 0) ∧
      ¬ Contains (family doctrine ((future ≫ inputs) ≫ modalImage)) (1, 0) :=
  ⟨(output_read 1 0).mpr (by omega), fun held => Nat.lt_irrefl 1 ((future_read 1 0).mp held)⟩

/-- An independently classified always-true function is a wrongly supplied modal meaning. -/
def constantTruth : profiles doctrine Assay Outgoing ⟶ power doctrine Nat :=
  name doctrine (⊤ : Subobject (Nat ⊗ profiles doctrine Assay Outgoing))

theorem constantTruth_read : family doctrine (inputs ≫ constantTruth) = ⊤ := by
  rw [← family_substitution, constantTruth, family_name, doctrine.reindex_top]

theorem the_actual_generated_operator_is_not_the_constant_truth_arrow :
    modalImage ≠ constantTruth := by
  intro same
  have admitted : Contains (family doctrine (inputs ≫ constantTruth)) (2, 2) :=
    constantTruth_read ▸ contains_top (2, 2)
  have complete : family doctrine (inputs ≫ constantTruth) = output :=
    congrArg (fun arrow => family doctrine (inputs ≫ arrow)) same.symm
  exact the_generated_operator_retains_the_parameter.2 (complete ▸ admitted)

def wrongAdded : Option RelativeClosedPositionedModalControlData.Origin →
    RelativeClosedSyntax.Interpretation.ArrowValue Type
  | none => RelativeClosedPositionedModalNativeMeaning.added doctrine source selected base none
  | some _ => ⟨profiles doctrine Assay Outgoing, power doctrine Nat, constantTruth⟩

theorem a_wrong_complete_modal_declaration_is_not_realized :
    ¬RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.signature source selected)
      (RelativeClosedPositionedModalRealization.assignment source base
        (RelativeClosedPositionedModalNativeMeaning.meaning doctrine source base) wrongAdded) := by
  intro realized
  have localSquare := RelativeClosedPositionedModalRealization.necessary_local source selected base
    (RelativeClosedPositionedModalNativeMeaning.meaning doctrine source base) wrongAdded realized
      (some (ULift.up false))
  have genuineSquare := RelativeClosedPositionedModalNativeMeaning.admitted
    doctrine source selected base (some (ULift.up false))
  have complete := RelativeClosedSyntax.Interpretation.ArrowValue.arrows_heq
    (localSquare.trans genuineSquare.symm)
  have wrongArrow : constantTruth =
      operation doctrine (base.map frame.forget) (base.map frame.focus)
        (base.map frame.instantiate) (base.map frame.outgoing) := eq_of_heq complete
  have genuineArrow : modalImage =
      operation doctrine (base.map frame.forget) (base.map frame.focus)
        (base.map frame.instantiate) (base.map frame.outgoing) :=
    RelativeClosedPositionedModalReadout.imageAt_complete doctrine source selected base (some (ULift.up false))
  exact the_actual_generated_operator_is_not_the_constant_truth_arrow
    (genuineArrow.trans wrongArrow.symm)

def eventName : Nat ≅ base.obj source.Event :=
  base.mapIso RelativeClosedPositionedModalControlData.event

def eventSource : base.obj source.Event ⟶ Nat := base.map source.source
def eventTarget : base.obj source.Event ⟶ Nat := base.map source.target

theorem event_source_read (value : Nat) :
    eventSource (eventName.hom value) = value := by
  have complete : eventName.hom ≫ eventSource = 𝟙 Nat :=
    ((base.map_comp RelativeClosedPositionedModalControlData.event.hom source.source).symm.trans
      (congrArg base.map RelativeClosedPositionedModalControlData.event_source)).trans
        (base.map_id source.program)
  exact congrArg (fun arrow : Nat ⟶ Nat => arrow value) complete

theorem event_target_read (value : Nat) :
    eventTarget (eventName.hom value) = value + 1 := by
  have complete : eventName.hom ≫ eventTarget =
      base.map RelativeClosedPositionedModalControlData.successor :=
    (base.map_comp RelativeClosedPositionedModalControlData.event.hom source.target).symm.trans
      (congrArg base.map RelativeClosedPositionedModalControlData.event_target)
  exact congrArg (fun arrow : Nat ⟶ Nat => arrow value) complete

theorem every_event_retains_the_actual_successor (supplied : base.obj source.Event) :
    eventTarget supplied = eventSource supplied + 1 := by
  have retained : eventName.hom (eventName.inv supplied) = supplied :=
    congrArg (fun arrow : base.obj source.Event ⟶ base.obj source.Event => arrow supplied)
      eventName.inv_hom_id
  have actualTarget := event_target_read (eventName.inv supplied)
  have actualSource := event_source_read (eventName.inv supplied)
  rw [retained] at actualTarget actualSource
  exact actualTarget.trans (congrArg (fun value : Nat => value + 1) actualSource.symm)

def stepPost : Subobject (Nat ⊗ Nat) := fromSet {supplied | supplied.1 > supplied.2}
def stepPostName : Nat ⟶ power doctrine Nat := name doctrine stepPost

def possibilityImage : power doctrine Nat ⟶ power doctrine Nat :=
  RelativeClosedPositionedModalReadout.imageAt doctrine source selected base none

def oneStepOutput : Subobject (Nat ⊗ Nat) := family doctrine (stepPostName ≫ possibilityImage)

theorem oneStepOutput_exact : oneStepOutput =
    doctrine.existsAlong (eventSource ▷ Nat)
      (doctrine.reindex (eventTarget ▷ Nat) stepPost) := by
  have complete := RelativeClosedPositionedModalReadout.possibility_supplied
    doctrine source selected base stepPostName
  change oneStepOutput = doctrine.existsAlong (eventSource ▷ Nat)
    (doctrine.reindex (eventTarget ▷ Nat) (family doctrine stepPostName)) at complete
  exact complete.trans (congrArg (fun predicate => doctrine.existsAlong (eventSource ▷ Nat)
    (doctrine.reindex (eventTarget ▷ Nat) predicate)) (family_name doctrine stepPost))

theorem stepPost_read (value parameter : Nat) :
    Contains stepPost (value, parameter) ↔ parameter < value := contains_fromSet _ _

theorem post_at_event (supplied : base.obj source.Event) (parameter : Nat) :
    Contains (doctrine.reindex (eventTarget ▷ Nat) stepPost) (supplied, parameter) ↔
      parameter < eventSource supplied + 1 := by
  rw [contains_reindex, whisker_right_apply]
  exact (stepPost_read _ parameter).trans (by rw [every_event_retains_the_actual_successor])

theorem oneStepOutput_read (value parameter : Nat) :
    Contains oneStepOutput (value, parameter) ↔ parameter < value + 1 := by
  rw [oneStepOutput_exact, contains_exists]
  constructor
  · rintro ⟨supplied, admitted, reaches⟩
    have coordinates : (eventSource supplied.1, supplied.2) = (value, parameter) :=
      (whisker_right_apply eventSource supplied.1 supplied.2).symm.trans reaches
    have first : eventSource supplied.1 = value := congrArg Prod.fst coordinates
    have second : supplied.2 = parameter := congrArg Prod.snd coordinates
    have guarded := (post_at_event supplied.1 supplied.2).mp admitted
    rw [first, second] at guarded
    exact guarded
  · intro admitted
    refine ⟨(eventName.hom value, parameter), ?_, ?_⟩
    · apply (post_at_event _ parameter).mpr
      rw [event_source_read]
      exact admitted
    · rw [whisker_right_apply, event_source_read]

theorem an_exact_two_step_target_does_not_authorize_one_step :
    Contains stepPost (5, 4) ∧ ¬ Contains oneStepOutput (3, 4) :=
  ⟨(stepPost_read 5 4).mpr (by omega),
    fun held => Nat.lt_irrefl 4 ((oneStepOutput_read 3 4).mp held)⟩

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalControls
