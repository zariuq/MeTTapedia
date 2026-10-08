import Mettapedia.TypeTheory.NativeLocalDisplayComparisons
import Mettapedia.TypeTheory.NativeLocalTheoryRestrictionControls

/-!
# Actual dependent receipts through logical display comparisons

The exchange of worlds changes the native argument fibre. The genuine
sum display arrow carries the complete program-and-pair receipt; its
independent decoder recovers both supplied finite witnesses. The product
display inverse is for the canonical comparison on the same presentation.
Every supplied function has the exact exchanged-argument readout.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NativeLocalDisplayComparisonControls

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafIndexedCwfBridge
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTheoryRestriction
open NativeLocalTheoryRestrictionControls NativeLocalDisplayComparisons

local instance (P : Worldᵒᵖ ⥤ Type) :
    Category ((presheafCwf World).Ty P) :=
  inferInstanceAs (Category (DisplayedFamily P))

local instance (P : Worldᵒᵖ ⥤ Type) :
    Category (TypeOver (localCwf (presheafCwf World)) P) :=
  TypeOver.instCategory (C := localCwf (presheafCwf World)) (Γ := P)

local instance : Category (Functor.Elements domain.decoded) :=
  categoryOfElements (domain.decoded : DisplayedFamily base)

noncomputable def actualSumReceipt :=
  (sumDisplayIso exchange.functor domain codomain).hom.substitution.app falseWorld
    ⟨PUnit.unit, retainedPair⟩

theorem actual_program_point_is_retained : actualSumReceipt.1 = PUnit.unit := rfl

noncomputable def decodedSumReceipt :=
  (eqToIso (C := DisplayedFamily (exchange.functor.op ⋙ base))
    (sigmaDecode (restrict exchange.functor domain) (body exchange.functor domain codomain))).hom.app
      ⟨falseWorld, PUnit.unit⟩ actualSumReceipt.2

theorem independent_decoder_recovers_whole_pair : decodedSumReceipt = suppliedPair :=
  actual_pair_readout

theorem both_dependent_witnesses_survive :
    decodedSumReceipt.1.val = 1 ∧ decodedSumReceipt.2.val = 1 := by
  rw [independent_decoder_recovers_whole_pair]
  exact ⟨rfl, rfl⟩

noncomputable def actualProductIso :=
  productDisplayEquivalence exchange.functor domain codomain

theorem inverse_recovers_the_complete_display_arrow :
    actualProductIso.hom ≫ actualProductIso.inv = 𝟙 _ := actualProductIso.hom_inv_id

theorem inverse_belongs_to_the_canonical_comparison :
    actualProductIso.hom = productDisplayMap exchange.functor domain codomain :=
  productDisplayEquivalence_hom exchange.functor domain codomain

theorem complete_function_is_read_at_the_exchanged_argument
    (function : (restrict exchange.functor (pi domain codomain)).decoded.obj
      ⟨falseWorld, PUnit.unit⟩)
    (argument : (restrict exchange.functor domain).decoded.obj ⟨falseWorld, PUnit.unit⟩) :
    ((((DependentProductNativeComparison.nativeIso
        (DisplayedPresheafTheoryRestriction.restrictFamily exchange.functor base domain.decoded)).hom.app
      (displayedToTotalElements
          (DisplayedPresheafTheoryRestriction.restrictFamily exchange.functor base domain.decoded) ⋙
        (DisplayedPresheafTheoryRestrictionAction.codomainFunctor
          exchange.functor base domain.decoded).obj codomain.decoded)).app
      ⟨falseWorld, PUnit.unit⟩
      ((piDecodeIso (restrict exchange.functor domain)
        (body exchange.functor domain codomain)).hom.app ⟨falseWorld, PUnit.unit⟩
        (((productDisplayMap exchange.functor domain codomain).substitution.app falseWorld
          ⟨PUnit.unit, function⟩).2))).app ⟨falseWorld, PUnit.unit⟩ (𝟙 _) argument) =
    ((((DependentProductNativeComparison.nativeIso domain.decoded).hom.app
      (displayedToTotalElements domain.decoded ⋙ codomain.decoded)).app
      ⟨trueWorld, PUnit.unit⟩
      ((piDecodeIso domain codomain).hom.app ⟨trueWorld, PUnit.unit⟩ function)).app
      ⟨trueWorld, PUnit.unit⟩ (𝟙 _) argument) := supplied_function_readout function argument

theorem forgetting_the_second_input_changes_the_answer :
    decodedSumReceipt.2.val ≠ (0 : Nat) := by
  rw [independent_decoder_recovers_whole_pair]
  decide

theorem omitting_the_theory_route_changes_the_type :
    (restrict exchange.functor domain).decoded.obj ⟨falseWorld, PUnit.unit⟩ ≠
      domain.decoded.obj ⟨falseWorld, PUnit.unit⟩ := omitting_the_world_change_changes_the_type

end Mettapedia.TypeTheory.NativeLocalDisplayComparisonControls
