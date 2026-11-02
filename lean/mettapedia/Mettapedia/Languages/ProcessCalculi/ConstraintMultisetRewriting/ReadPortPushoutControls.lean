import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadPortPushouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Shared-read and exclusive-port controls for the actual pushout squares
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadPortPushouts.Controls

open CategoryTheory CategoryTheory.Limits
open ConstraintMultisetRewriting.Controls

theorem repeated_reads_have_a_left_pushout :
    IsPushout (↾(Sum.inr : Port sharedRead.read → Port sharedRead.taken ⊕ Port sharedRead.read))
      (↾(readContext two_reads_share_one_occurrence))
      (↾(leftMatch two_reads_share_one_occurrence))
      (↾(contextBefore (selection := sharedRead) (before := singletonStore))) :=
  left_pushout two_reads_share_one_occurrence

theorem repeated_reads_have_a_right_pushout :
    IsPushout (↾(Sum.inr : Port sharedRead.read → Port sharedRead.made ⊕ Port sharedRead.read))
      (↾(readContext two_reads_share_one_occurrence))
      (↾(rightMatch two_reads_share_one_occurrence))
      (↾(contextAfter (label := label) (rule := readsRule) (before := singletonStore))) :=
  right_pushout two_reads_share_one_occurrence

theorem the_read_gluing_square_is_a_pushout :
    IsPushout (↾(Sum.inr : Port sharedRead.read → Port sharedRead.taken ⊕ Port sharedRead.read))
      (↾(readQuotient sharedRead)) (↾(quotientLeft sharedRead)) (↾(supportRead sharedRead)) :=
  read_gluing_pushout sharedRead (OccurrenceIdentification.valid_identification two_reads_share_one_occurrence)

theorem repeated_read_positions_are_distinct :
    (⟨⟨0, by decide⟩⟩ : Port sharedRead.read) ≠ ⟨⟨1, by decide⟩⟩ := by decide

theorem repeated_read_positions_have_one_physical_image :
    readQuotient sharedRead ⟨⟨0, by decide⟩⟩ = readQuotient sharedRead ⟨⟨1, by decide⟩⟩ := rfl

theorem genuine_consumption_has_a_left_pushout :
    IsPushout (↾(Sum.inr : Port callSelection.read → Port callSelection.taken ⊕ Port callSelection.read))
      (↾(readContext call_valid)) (↾(leftMatch call_valid))
      (↾(contextBefore (selection := callSelection) (before := initial))) :=
  left_pushout call_valid

theorem genuine_production_has_a_right_pushout :
    IsPushout (↾(Sum.inr : Port callSelection.read → Port callSelection.made ⊕ Port callSelection.read))
      (↾(readContext call_valid)) (↾(rightMatch call_valid))
      (↾(contextAfter (label := label) (rule := callRule) (before := initial))) :=
  right_pushout call_valid

/-- A commuting square that collapses two exclusive positions fails the
universal property: the two positions can be distinguished by a Boolean map. -/
theorem collapsing_two_exclusive_ports_is_not_a_pushout :
    ¬ IsPushout (↾(Sum.inr : Empty → Bool ⊕ Empty)) (↾(id : Empty → Empty))
      (↾(fun _ : Bool ⊕ Empty => false)) (↾(Empty.elim : Empty → Bool)) := by
  intro collapsed
  let separate : Bool ⊕ Empty ⟶ Bool := ↾(Sum.elim id Empty.elim)
  let empty : Empty ⟶ Bool := ↾Empty.elim
  have commutes : (↾(Sum.inr : Empty → Bool ⊕ Empty)) ≫ separate =
      (↾(id : Empty → Empty)) ≫ empty := by
    ext impossible
    cases impossible
  have first := congrArg (fun (map : Bool ⊕ Empty ⟶ Bool) => map (Sum.inl false))
    (collapsed.inl_desc separate empty commutes)
  have second := congrArg (fun (map : Bool ⊕ Empty ⟶ Bool) => map (Sum.inl true))
    (collapsed.inl_desc separate empty commutes)
  exact Bool.false_ne_true (first.symm.trans second)

theorem consuming_and_republishing_refuses_the_shared_read :
    ¬ OccurrenceIdentification.IdentificationCondition (OccurrenceIdentification.rendered sharedRead) := by
  rw [OccurrenceIdentification.rendered_identification_iff]
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadPortPushouts.Controls
