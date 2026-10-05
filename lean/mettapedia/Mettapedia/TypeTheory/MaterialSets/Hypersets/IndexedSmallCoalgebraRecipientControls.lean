import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipientBaseChange
import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoalgebraQuotientControls

/-!
# Infinite growing and noninjective-substitution recipient controls

The constructed recipient is instantiated on an infinite chain of contexts
with Nat parameters and growing Fin(n+1) × Bool occurrences. It retains
infinitely many parameters while identifying bisimilar receipt aliases.
New occurrences appear at every stage outside the restriction image.

A second instance substitutes a growing tagged parameter into its untagged
observation. The behavioral map identifies tags, whereas the literal
dependent pullback and its future children retain the saved tag. No decoder
of the coarser behavioral map can recover both source tags.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipientControls

open _root_.CategoryTheory CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open PowerClassPresheafDescent.Controls

abbrev parameters := IndexedCoalgebraQuotientControls.parameters
abbrev source := IndexedCoalgebraQuotientControls.source
abbrev sourceParameter := IndexedCoalgebraQuotientControls.parameter
abbrev transition := IndexedCoalgebraQuotientControls.transition
abbrev sourceSquare := IndexedCoalgebraQuotientControls.parameter_square

def reading : NaturalHom source (IndexedSmallCoalgebraRecipient.family parameters) :=
  IndexedSmallCoalgebraRecipient.fromSmall parameters sourceParameter transition

theorem reading_eq_iff (point : Stagesᵒᵖ) (left right : source.obj point) :
    reading.app point left = reading.app point right ↔ left.1 = right.1 := by
  constructor
  · intro same
    exact ((IndexedSmallCoalgebraRecipient.small_kernel parameters sourceParameter transition point left right).mp same).2
  · intro same
    exact (IndexedSmallCoalgebraRecipient.small_kernel parameters sourceParameter transition point left right).mpr
      ⟨IndexedCoalgebraQuotientControls.ordinary_all_equivalent point left right, same⟩

theorem infinitely_many_readings : Function.Injective
    (fun base => reading.app (world 0) (IndexedCoalgebraQuotientControls.initialValue base false)) := by
  intro first second same
  exact (reading_eq_iff (world 0) _ _).mp same

theorem different_parameters_retained :
    reading.app (world 0) (IndexedCoalgebraQuotientControls.initialValue 0 false) ≠
      reading.app (world 0) (IndexedCoalgebraQuotientControls.initialValue 1 false) :=
  fun same => Nat.zero_ne_one (infinitely_many_readings same)

theorem raw_receipt_tags_distinct (base : Nat) :
    IndexedCoalgebraQuotientControls.initialValue base true ≠
      IndexedCoalgebraQuotientControls.initialValue base false :=
  IndexedCoalgebraQuotientControls.raw_provenance_distinct base

theorem receipt_readings_agree (base : Nat) :
    reading.app (world 0) (IndexedCoalgebraQuotientControls.initialValue base true) =
      reading.app (world 0) (IndexedCoalgebraQuotientControls.initialValue base false) :=
  (reading_eq_iff (world 0) _ _).mpr rfl

theorem no_both_receipt_decoder (base : Nat)
    (decoder : (IndexedSmallCoalgebraRecipient.family parameters).obj (world 0) → Bool) :
    ¬ (decoder (reading.app (world 0) (IndexedCoalgebraQuotientControls.initialValue base true)) = true ∧
      decoder (reading.app (world 0) (IndexedCoalgebraQuotientControls.initialValue base false)) = false) := by
  rintro ⟨first, second⟩
  exact Bool.noConfusion (first.symm.trans ((congrArg decoder (receipt_readings_agree base)).trans second))

theorem new_occurrences_every_stage (stage base : Nat) :
    ¬ ∃ earlier : source.obj (world stage),
      source.map (IndexedCoalgebraQuotientControls.advance stage) earlier =
        IndexedCoalgebraQuotientControls.newReceipt stage base :=
  IndexedCoalgebraQuotientControls.new_receipt_every_stage stage base

theorem new_occurrence_same_reading (stage base : Nat) :
    reading.app (world (stage + 1)) (IndexedCoalgebraQuotientControls.newReceipt stage base) =
      reading.app (world (stage + 1))
        (source.map (IndexedCoalgebraQuotientControls.advance stage)
          (base, stageValue stage 0 (Nat.zero_lt_succ stage) false)) :=
  (reading_eq_iff (world (stage + 1)) _ _).mpr rfl

theorem actual_unique_small_map : ∃! operation : NaturalHom source (IndexedSmallCoalgebraRecipient.family parameters),
    IndexedCoalgebraQuotientControls.underlying.comp (imageHom operation) =
      operation.comp (IndexedSmallCoalgebraRecipient.coalgebra parameters) ∧
        operation.comp (IndexedSmallCoalgebraRecipient.parameter parameters) = sourceParameter :=
  IndexedSmallCoalgebraRecipient.unique_small parameters sourceParameter transition sourceSquare

def taggedSection (base : Nat) : source.sections :=
  ⟨fun point => (base, stageValue (stageIndex point) 0 (Nat.zero_lt_succ (stageIndex point)) true), by
    intro first second step
    exact Prod.ext rfl (Prod.ext (Fin.ext rfl) rfl)⟩

def readingSection (base : Nat) : (IndexedSmallCoalgebraRecipient.family parameters).sections :=
  reading.mapSection (taggedSection base)

theorem section_retains_base (base : Nat) (point : Stagesᵒᵖ) : ((readingSection base).val point).1 = base := rfl

theorem infinitely_many_sections : Function.Injective readingSection := by
  intro first second same
  exact congrArg (fun term : (IndexedSmallCoalgebraRecipient.family parameters).sections =>
    (term.val (world 0)).1) same

def seedBehavior : (IndexedSmallCoalgebraRecipient.Behavior (D := Stagesᵒᵖ)).obj (world 0) :=
  (reading.app (world 0) (IndexedCoalgebraQuotientControls.initialValue 0 false)).2

def taggedValue (tag : Bool) : (IndexedSmallCoalgebraRecipient.family growingSource).obj (world 0) :=
  (stageValue 0 0 (Nat.zero_lt_one) tag, seedBehavior)

abbrev forgetTag := IndexedCoveredPowerControls.forgetTag

def substituted (tag : Bool) : (IndexedSmallCoalgebraRecipient.family growingTarget).obj (world 0) :=
  (IndexedSmallCoalgebraRecipientBaseChange.reindex growingTarget growingSource forgetTag).app (world 0) (taggedValue tag)

def pulled (tag : Bool) :
    (IndexedSmallCoalgebraRecipientBaseChange.pulledFamily growingTarget growingSource forgetTag).obj (world 0) :=
  (IndexedSmallCoalgebraRecipientBaseChange.forward growingTarget growingSource forgetTag).app (world 0) (taggedValue tag)

theorem substituted_tags_agree : substituted true = substituted false := rfl

theorem pulled_tags_distinct : pulled true ≠ pulled false := by
  intro same
  exact Bool.noConfusion (congrArg (fun entry :
    (IndexedSmallCoalgebraRecipientBaseChange.pulledFamily growingTarget growingSource forgetTag).obj (world 0) =>
      entry.val.2.2) same)

theorem substitution_has_no_both_tag_decoder
    (decoder : (IndexedSmallCoalgebraRecipient.family growingTarget).obj (world 0) → Bool) :
    ¬ (decoder (substituted true) = true ∧ decoder (substituted false) = false) := by
  rintro ⟨first, second⟩
  exact Bool.noConfusion (first.symm.trans ((congrArg decoder substituted_tags_agree).trans second))

theorem pulled_future_retains_tag (level : Nat) (tag : Bool)
    (child : (IndexedSmallCoalgebraRecipientBaseChange.pulledFamily growingTarget growingSource forgetTag).obj (world level))
    (available : ((IndexedSmallCoalgebraRecipientBaseChange.pulledCoalgebra growingTarget growingSource forgetTag).app
      (world 0) (pulled tag)).val.holds
        ⟨⟨world level, (homOfLE (Nat.zero_le level)).op.op⟩, child⟩) : child.val.2.2 = tag := by
  have supported := ((IndexedSmallCoalgebraRecipientBaseChange.pulledIndexedCoalgebra
    growingTarget growingSource forgetTag).app (world 0) (pulled tag)).property
      ⟨⟨world level, (homOfLE (Nat.zero_le level)).op.op⟩, child⟩ available
  exact congrArg Prod.snd supported

theorem whole_substitution_square :
    (IndexedSmallCoalgebraRecipient.coalgebra growingSource).comp
      (imageHom (IndexedSmallCoalgebraRecipientBaseChange.reindex growingTarget growingSource forgetTag)) =
        (IndexedSmallCoalgebraRecipientBaseChange.reindex growingTarget growingSource forgetTag).comp
          (IndexedSmallCoalgebraRecipient.coalgebra growingTarget) :=
  IndexedSmallCoalgebraRecipientBaseChange.reindex_square growingTarget growingSource forgetTag

theorem whole_pulled_indexed_square :
    (IndexedSmallCoalgebraRecipient.indexedCoalgebra growingSource).comp
      (IndexedCoveredPower.image (IndexedSmallCoalgebraRecipient.parameter growingSource)
        (IndexedSmallCoalgebraRecipientBaseChange.pulledParameter growingTarget growingSource forgetTag)
        (IndexedSmallCoalgebraRecipientBaseChange.forward growingTarget growingSource forgetTag)
        (IndexedSmallCoalgebraRecipientBaseChange.forward_parameter growingTarget growingSource forgetTag)) =
      (IndexedSmallCoalgebraRecipientBaseChange.forward growingTarget growingSource forgetTag).comp
        (IndexedSmallCoalgebraRecipientBaseChange.pulledIndexedCoalgebra growingTarget growingSource forgetTag) :=
  IndexedSmallCoalgebraRecipientBaseChange.forward_indexed_square growingTarget growingSource forgetTag

end Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedSmallCoalgebraRecipientControls
