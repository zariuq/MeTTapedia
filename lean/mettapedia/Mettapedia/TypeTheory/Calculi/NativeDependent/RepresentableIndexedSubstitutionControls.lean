import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedSubstitution
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedControls

/-!
# Generated substitution changes actual indexed admission

The same independently generated successor fibre is substituted by two
original constant maps. Every zero-substituted point is empty; every
twelve-substituted point retains the supplied original witness eleven.
The raw parser reads those complete reindexed native families.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations.Controls

open _root_.CategoryTheory Opposite

noncomputable section

def zeroMap : naturalObject ⟶ naturalObject := ⟨↾fun _ => 0⟩
def twelveMap : naturalObject ⟶ naturalObject := ⟨↾fun _ => 12⟩

abbrev zeroChanged := (fibreMeaning successorIndexed).reindex (originalMap zeroMap)
abbrev twelveChanged := (fibreMeaning successorIndexed).reindex (originalMap twelveMap)

theorem generated_zero_substitution_reads_the_actual_family :
    (model Base).evaluateType (objectScope naturalObject)
      ((fibreType successorIndexed (.var 0)).substitute (originalSubstitution zeroMap)) =
        some zeroChanged := complete_indexed_family_substitution successorIndexed zeroMap

theorem generated_twelve_substitution_reads_the_actual_family :
    (model Base).evaluateType (objectScope naturalObject)
      ((fibreType successorIndexed (.var 0)).substitute (originalSubstitution twelveMap)) =
        some twelveChanged := complete_indexed_family_substitution successorIndexed twelveMap

theorem every_zero_changed_fibre_is_empty (n : Nat) :
    IsEmpty (zeroChanged.decoded.obj ⟨op unitObject, argument n⟩) := by
  change IsEmpty ((fibreMeaning successorIndexed).decoded.obj ⟨op unitObject, argument 0⟩)
  exact zero_fibre_is_empty

def changedTwelveValue (n : Nat) : twelveChanged.decoded.obj ⟨op unitObject, argument n⟩ :=
  twelveValue

theorem every_twelve_changed_fibre_is_inhabited (n : Nat) :
    Nonempty (twelveChanged.decoded.obj ⟨op unitObject, argument n⟩) :=
  ⟨changedTwelveValue n⟩

theorem complete_original_witness_survives_substitution (n : Nat) :
    (show Nat from (decode successorIndexed (op unitObject) (argument 12)
      (changedTwelveValue n)).val.down PUnit.unit) = 11 := rfl

theorem the_two_generated_substitutions_have_distinct_actual_fibres (n : Nat) :
    zeroChanged.decoded.obj ⟨op unitObject, argument n⟩ ≠
      twelveChanged.decoded.obj ⟨op unitObject, argument n⟩ := by
  intro same
  exact (every_zero_changed_fibre_is_empty n).false (same.symm ▸ changedTwelveValue n)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations.Controls
