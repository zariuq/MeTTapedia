import Mettapedia.TypeTheory.ContextualLocalUniversesMorphism
import Mettapedia.TypeTheory.ContextualMarkedTypes
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

/-!
# Controls for the actual action on local family presentations

Forgetting an external family mark is a noninjective contextual map.
Its local action still retains the original parameter context and name,
and transports the supplied varying section. A nonidentity substitution
changes the witness; replacing the name by a constant changes the fibre.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.ContextualLocalUniversesMorphismControls

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualLocalUniverses ContextualLocalUniversesMorphism

abbrev target := familiesCwfWithTerminal.{0}
abbrev source := ContextualMarkedTypes.withTerminal target
abbrev forget := ContextualMarkedTypes.decoder target

def markedFamily (mark : Bool) : LocalType source.toCwf Nat :=
  ⟨Nat, (⟨fun n => Fin (n + 1), mark⟩ : source.toCwf.Ty Nat), id⟩

def supplied : Term source.toCwf Nat (markedFamily true) :=
  fun n => ⟨n, Nat.lt_succ_self n⟩

theorem supplied_marks_differ : markedFamily true ≠ markedFamily false := by
  intro same
  have marks := congrArg (fun A : LocalType source.toCwf Nat => A.family.2) same
  exact Bool.noConfusion marks

theorem action_has_a_real_collision :
    typeAction forget (markedFamily true) = typeAction forget (markedFamily false) := rfl

theorem action_retains_parameter_context_and_name :
    (typeAction forget (markedFamily true)).parameters = Nat ∧
      (typeAction forget (markedFamily true)).name = id := ⟨rfl, rfl⟩

theorem supplied_value_retained (n : Nat) : (termAction forget supplied n).val = n := by
  rw [eq_of_heq (termAction_heq forget supplied)]
  rfl

def shift : source.toCwf.Sub Nat Nat := fun n => n + 2

theorem substituted_name (n : Nat) :
    (typeAction forget ((markedFamily true).reindex shift)).name n = n + 2 := rfl

theorem actual_substituted_value (n : Nat) :
    (termAction forget (substituteTerm supplied shift) n).val = n + 2 := by
  rw [eq_of_heq (termAction_heq forget (substituteTerm supplied shift))]
  rfl

theorem omitting_substitution_changes_evidence (n : Nat) :
    (termAction forget (substituteTerm supplied shift) n).val ≠
      (termAction forget supplied n).val := by
  rw [actual_substituted_value, supplied_value_retained]
  omega

def erasedName : LocalType target.toCwf Nat :=
  ⟨Nat, (fun n => Fin (n + 1)), (fun _ => 0)⟩

theorem erasing_the_name_changes_the_decoded_family :
    erasedName.decoded ≠ (typeAction forget (markedFamily true)).decoded := by
  intro same
  have fibres := congrFun same 1
  have cards := congrArg Nat.card fibres
  change Nat.card (Fin 1) = Nat.card (Fin 2) at cards
  norm_num [Nat.card_eq_fintype_card] at cards

theorem decoding_before_or_after_mapping_retains_the_section :
    HEq ((familyDecoder target.toCwf).mapTerm ((strictAction forget).toFamilyMorphism.mapTerm supplied))
      (forget.toFamilyMorphism.mapTerm ((familyDecoder source.toCwf).mapTerm supplied)) :=
  decoder_term_square forget supplied

theorem complete_family_square :
    (familyAction forget).comp (familyDecoder target.toCwf) =
      (familyDecoder source.toCwf).comp forget.toFamilyMorphism :=
  decoder_family_square forget

end Mettapedia.TypeTheory.ContextualLocalUniversesMorphismControls
