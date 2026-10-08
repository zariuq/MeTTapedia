import Mettapedia.CategoryTheory.RelativeClosedBaseConservativity
import Mettapedia.CategoryTheory.RelativeClosedBaseUniverse
import Mettapedia.CategoryTheory.RelativeClosedBaseControls

/-!
# Distinct original functions and formal products under conservativity

A generated product expression produces an arrow which negates its input.
The complete equivalence reconstructs that original function, including
both Boolean inputs. Faithfulness rejects its identification with the
identity. Old and formal product expressions remain distinct raw objects,
while their earned comparison retains both coordinates.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.Conservativity.Controls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

abbrev Base := AsSmall.{0} (Type)
abbrev liftedBool : Base := ⟨Bool⟩
def liftedNegation : liftedBool ⟶ liftedBool := ⟨BaseComparisons.Controls.negation⟩
abbrev oldBool := (inclusion (C := Base)).obj liftedBool

def generatedNegation : oldBool ⟶ oldBool :=
  pairing (𝟙 oldBool) ((inclusion (C := Base)).map liftedNegation) ≫
    second oldBool oldBool

theorem generated_product_expression_reads_negation :
    generatedNegation = (inclusion (C := Base)).map liftedNegation :=
  pairing_second _ _

def reconstructedNegation : liftedBool ⟶ liftedBool :=
  (inclusion (C := Base)).preimage generatedNegation

theorem complete_reconstructed_function :
    reconstructedNegation = liftedNegation := by
  apply (inclusion (C := Base)).map_injective
  exact ((inclusion (C := Base)).map_preimage generatedNegation).trans
    generated_product_expression_reads_negation

theorem both_inputs_are_reconstructed :
    reconstructedNegation.down false = true ∧ reconstructedNegation.down true = false := by
  rw [complete_reconstructed_function]
  exact ⟨rfl, rfl⟩

theorem constant_readout_rejected : reconstructedNegation.down false ≠ reconstructedNegation.down true := by
  rw [both_inputs_are_reconstructed.1, both_inputs_are_reconstructed.2]
  exact fun same => Bool.false_ne_true same.symm

theorem distinct_original_functions_stay_distinct :
    (inclusion (C := Base)).map liftedNegation ≠
      (inclusion (C := Base)).map (𝟙 liftedBool) := by
  intro same
  have original := (original_arrow_equality_iff liftedNegation (𝟙 liftedBool)).mp same
  have input := congrArg (fun arrow : liftedBool ⟶ liftedBool => arrow.down false) original
  exact Bool.false_ne_true input.symm

theorem generated_negation_cannot_become_identity : generatedNegation ≠ 𝟙 oldBool := by
  rw [generated_product_expression_reads_negation, ← (inclusion (C := Base)).map_id liftedBool]
  exact distinct_original_functions_stay_distinct

theorem a_formal_product_is_not_the_old_product_expression :
    formalObject (C := Base) (.product liftedBool liftedBool) ≠
      oldObject (C := Base) (.product liftedBool liftedBool) := by
  intro same
  have code := congrArg (fun object : Guest (C := Base) => object.code) same
  cases code

def productPresentationChange :
    oldObject (C := Base) (.product liftedBool liftedBool) ≅
      formalObject (C := Base) (.product liftedBool liftedBool) :=
  comparison (.product liftedBool liftedBool)

theorem product_change_retains_both_projections :
    productPresentationChange.hom ≫ first oldBool oldBool =
        (inclusion (C := Base)).map (CartesianMonoidalCategory.fst liftedBool liftedBool) ∧
      productPresentationChange.hom ≫ second oldBool oldBool =
        (inclusion (C := Base)).map (CartesianMonoidalCategory.snd liftedBool liftedBool) :=
  ⟨product_comparison_first _ _, product_comparison_second _ _⟩

def suppliedPair : oldBool ⟶ product oldBool oldBool :=
  pairing (𝟙 oldBool) ((inclusion (C := Base)).map liftedNegation)

theorem supplied_pair_first : suppliedPair ≫ first oldBool oldBool = 𝟙 oldBool :=
  pairing_first _ _

theorem supplied_pair_second : suppliedPair ≫ second oldBool oldBool =
    (inclusion (C := Base)).map liftedNegation := pairing_second _ _

theorem supplied_pair_has_distinct_coordinates :
    suppliedPair ≫ first oldBool oldBool ≠ suppliedPair ≫ second oldBool oldBool := by
  rw [supplied_pair_first, supplied_pair_second, ← (inclusion (C := Base)).map_id liftedBool]
  exact Ne.symm distinct_original_functions_stay_distinct

theorem every_formal_arrow_between_old_objects_has_a_unique_original
    (formal : oldBool ⟶ oldBool) :
    ∃! original : liftedBool ⟶ liftedBool, (inclusion (C := Base)).map original = formal := by
  refine ⟨(inclusion (C := Base)).preimage formal, (inclusion (C := Base)).map_preimage formal, ?_⟩
  intro original read
  exact (inclusion (C := Base)).map_injective
    (read.trans ((inclusion (C := Base)).map_preimage formal).symm)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.Conservativity.Controls
