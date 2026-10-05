import Mettapedia.TypeTheory.ContextualSmallFamilyWiderControls
import Mettapedia.TypeTheory.ContextualSmallFamilyWiderSubstitution

/-!
# Noninjective substitution of a genuinely wider W consumer

Both source material coordinates are retained in the comprehension. The
wider fold's values commute with the actual parameter map and preserve
the selected whole future tree, even when two source parameters map to
the same parent.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWiderSubstitutionControls

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyUniverseControls ContextualSmallFamilyTypeFormerControls
open ContextualSmallFamilyWControls ContextualSmallFamilyWTypes
open ContextualSmallFamilyWiderControls ContextualSmallFamilyTypeFormerCoherence

noncomputable def changedWideFold (saved : HSet.{0}) :
    wideTarget.obj (parameter 0 HSet.quineAtom) :=
  ContextualSmallFamilyWiderAlgebra.foldValue
    (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall growingPositions)
    (ContextualSmallFamilyWiderSubstitution.substitutedAlgebra selectFirst cyclicSmall growingPositions wideAlgebra)
    (pairedPoint saved) (changedTree saved)

theorem noninjective_change_retains_whole_wider_value (saved : HSet.{0}) :
    changedWideFold saved = ⟨HSet.quineAtom, oneStar 0⟩ :=
  (ContextualSmallFamilyWiderSubstitution.fold_substitution selectFirst cyclicSmall growingPositions wideAlgebra
    (pairedPoint saved) (oneStar 0)).symm.trans
      (wider_fold_value (parameter 0 HSet.quineAtom) (oneStar 0))

theorem collapsed_parent_fold_values_agree : changedWideFold ∅ = changedWideFold HSet.quineAtom :=
  (noninjective_change_retains_whole_wider_value ∅).trans
    (noninjective_change_retains_whole_wider_value HSet.quineAtom).symm

theorem source_parameters_remain_distinct : pairedPoint ∅ ≠ pairedPoint HSet.quineAtom := by
  intro same
  have materials := congrArg (fun point : pairedParameters.Elements => point.2.2) same
  exact HSet.empty_ne_quineAtom materials

noncomputable def changedTotalValue (saved : HSet.{0}) :
    (ContextualSmallFamilyUniverse.total
      (ContextualSmallFamilyWiderSubstitution.targetUnder selectFirst wideTarget)).obj 0 :=
  ⟨(HSet.quineAtom, saved), changedWideFold saved⟩

theorem whole_comprehension_retains_saved_parameter :
    changedTotalValue ∅ ≠ changedTotalValue HSet.quineAtom := by
  intro same
  have materials := congrArg (fun value : (ContextualSmallFamilyUniverse.total
      (ContextualSmallFamilyWiderSubstitution.targetUnder selectFirst wideTarget)).obj 0 => value.1.2) same
  exact HSet.empty_ne_quineAtom materials

end Mettapedia.TypeTheory.ContextualSmallFamilyWiderSubstitutionControls
