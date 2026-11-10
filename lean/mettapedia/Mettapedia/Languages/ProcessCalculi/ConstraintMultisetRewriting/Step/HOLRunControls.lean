import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLPreparationEncodingControls

/-!
# Finite-run controls: order, event identity and refusal

The source-history model retains the existing evaluator's distinct events
with equal endpoints. Refusing their admission leaves no nonempty run.
Independent small controls separate event order and pullback composition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open RunModelCorrespondence HOLPreparedRunEncoding HOLPreparedEffectEncoding
open HOLRunSpecialization HOLPreparationEncodingControls Step.Evaluation.Controls
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Controls (Store)

def branchPath (label : Bool) :
    @Quiver.Path (EffectCore.EventObject alternatives.effectCore alternatives.eventAdmission) _
      ([] : Store) [(true, false)] :=
  .cons .nil (branchEvent label)

def branchWord (label : Bool) : List (RawEvent alternatives.effectCore) :=
  word alternatives.effectCore alternatives.eventAdmission (branchPath label)

theorem different_words : branchWord true ≠ branchWord false := by
  intro same
  have packets : (toPacket alternatives.effectCore (branchEvent true)).val =
      (toPacket alternatives.effectCore (branchEvent false)).val := by
    simpa only [branchWord, branchPath, word, List.nil_append, List.cons.injEq, and_true] using same
  exact same_endpoints_distinct_packets (Subtype.ext packets)

variable (input : HOLRunModel.Input) (other : TypeFamilySemantics.OperatorFamilies.{0})
  (prior : TypeFamilySemantics.Assignment.{0})

noncomputable def encodedWord (label : Bool) :=
  wordValue alternatives.effectCore input.operations.signature (input.model alternatives.effectCore other prior)
    (input.coding alternatives.effectCore other prior) (input.agreement alternatives.effectCore other prior)
    (branchWord label)

theorem encoded_words_distinct : encodedWord input other prior true ≠ encodedWord input other prior false := by
  intro same
  exact different_words (wordValue_injective alternatives.effectCore _ _
    (input.coding alternatives.effectCore other prior) (input.agreement alternatives.effectCore other prior) same)

theorem loaded_accepts_each_branch (label : Bool) :
    (input.operations.signature.pathValue (input.model alternatives.effectCore other prior)
      (stepValue alternatives.effectCore _ _ (input.coding alternatives.effectCore other prior)
        alternatives.eventAdmission) (encodedWord input other prior label)
      ((input.coding alternatives.effectCore other prior).states.symm (some []))
      ((input.coding alternatives.effectCore other prior).states.symm (some [(true, false)]))).down :=
  encoded_native_path alternatives.effectCore _ _ (input.coding alternatives.effectCore other prior)
    (input.agreement alternatives.effectCore other prior) alternatives.eventAdmission (branchPath label)

theorem loaded_refuses_each_branch (label : Bool) (target : Option Store) :
    ¬ (input.operations.signature.pathValue (input.model alternatives.effectCore other prior)
      (stepValue alternatives.effectCore _ _ (input.coding alternatives.effectCore other prior)
        (fun _ _ => False)) (encodedWord input other prior label)
      ((input.coding alternatives.effectCore other prior).states.symm (some []))
      ((input.coding alternatives.effectCore other prior).states.symm target)).down := by
  intro accepted
  have raw := (raw_path_iff alternatives.effectCore _ _ (input.coding alternatives.effectCore other prior)
    (input.agreement alternatives.effectCore other prior) (fun _ _ => False) (branchWord label) _ _).mp accepted
  apply refused_nonempty alternatives.effectCore _ [] (some []) target
  simpa only [branchWord, branchPath, word, List.nil_append] using raw

def orderedStep (state event target : Bool) : Prop := target = if event then true else !state

theorem noncommuting_words :
    WordRun orderedStep [true, false] false false ∧
    ¬ WordRun orderedStep [false, true] false false := by
  simp [WordRun.cons_iff, WordRun.nil_iff, orderedStep]

def orderedBack (event : Bool) (value : Nat) : Nat := if event then value + 1 else 2 * value

theorem pullback_order :
    [true, false].foldr orderedBack 3 = 7 ∧ [false, true].foldr orderedBack 3 = 8 := by
  decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunControls
