import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeProductSubtypingProofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeSubtypingControls

/-!
# Source function subtyping through equal computed domains

The original domain A and first(pair(A,A)) have a supplied typed equality.
The dependent fibre compares its index with an ambient element. Formation is
proved on both sides of the actual source subPi derivation.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeProductSubtypingControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open TowerInterpretation CodedHOL

namespace Source
abbrev church := SetCodeSubtypingControls.Source.church
abbrev context := SetCodeSubtypingControls.Source.context
abbrev before := SetCodeSubtypingControls.Source.before
abbrev after := SetCodeSubtypingControls.Source.after
abbrev fibre := SetCodeSubtypingControls.Source.fibre
def beforeProduct : CTm Nat 2 := .pi before fibre
def afterProduct : CTm Nat 2 := .pi after fibre
theorem before_typed : CTyped church context beforeProduct (.head 2) :=
  .piForm SetCodeEqualityControls.Source.before_typed (by change 0 < 2; decide)
    SetCodeSubtypingControls.Source.fibre_before_typed (by change 0 < 2; decide) rfl
theorem after_typed : CTyped church context afterProduct (.head 2) :=
  .piForm SetCodeSubtypingControls.Source.after_typed (by change 0 < 2; decide)
    SetCodeSubtypingControls.Source.fibre_after_typed (by change 0 < 2; decide) rfl
theorem included : CBelow church context beforeProduct afterProduct :=
  .subPi before_typed (by change 0 < 2; decide) after_typed (by change 0 < 2; decide)
    SetCodeEqualityControls.Source.type_equality (by change 0 < 2; decide) SetCodeSubtypingControls.Source.fibres_included
end Source

def receipt := SetCode.SubtypingProofs.productJudgment Source.context Source.before Source.after (.head 2)
  Source.fibre Source.fibre SetCodeSubtypingControls.bound SetCodeSubtypingControls.sets
  SetCodeEqualityControls.typeReceipt SetCodeSubtypingControls.fibreReceipt

theorem receipt_free : receipt.FunctionExtensionalityFree :=
  SetCode.SubtypingProofs.productJudgment_free Source.context Source.before Source.after (.head 2)
    Source.fibre Source.fibre SetCodeSubtypingControls.bound SetCodeSubtypingControls.sets
    SetCodeEqualityControls.typeReceipt SetCodeSubtypingControls.fibreReceipt
    SetCodeEqualityControls.sets_free SetCodeEqualityControls.typeReceipt_free SetCodeSubtypingControls.fibreReceipt_free

theorem actual_product : (SetCodeSubtypingControls.actualModel.denote (SetCode.expand
    (judgmentAt (.sub Source.context Source.beforeProduct Source.afterProduct) SetCodeSubtypingControls.bound))
      SetCodeSubtypingControls.valuation).down := SetCodeEqualityControls.receipt_valid receipt

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeProductSubtypingControls
