import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedHypersetFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosureControls

/-!
# Generated full-family member code controls

Actual material seeds over an infinite growing context generate genuine
dependent sums, complete future products, identity and contextual W.
Every formed family has the independent universe decoder and its real
classification pullback. Raising the external parameter wrapper preserves
the material child readings. A newly appearing cyclic argument still
makes the negative product empty. Recipe provenance remains distinct
even when identity substitution preserves the full decoded functor.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedHypersetFamiliesControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualHypersetFamilyClosure HostChoiceContextualHypersetModel
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualSetInterpretationControls
open HostChoiceContextualHypersetModelControls.Infinite
open HostChoiceContextualHypersetFamilyClosureControls
open HostChoiceContextualGeneratedHypersetFamilies
open PowerClassPresheafDescent.Controls

abbrev raised := raisedParameters parameters
abbrev raisedPoint (world : Stagesᵒᵖ) : raised.Elements := ⟨world, ULift.up PUnit.unit⟩

noncomputable def parent : NaturalHom raised values := (lowerParameters parameters).comp growingParent
noncomputable def generatedInput : Code.{0,0} raised := memberCode parent

noncomputable def singletonMap : NaturalHom (comprehension parent) values :=
  bodyMapUnder growingParent singletonBody (lowerParameters parameters)

noncomputable def partialMap : NaturalHom (comprehension parent) values :=
  bodyMapUnder growingParent selectedEmptyBody (lowerParameters parameters)

noncomputable def memberMap : NaturalHom (comprehension parent) values :=
  bodyMapUnder growingParent (argumentReading growingParent) (lowerParameters parameters)

noncomputable def generatedSingletonBody : Code.{0,0} (ContextualSmallFamilyUniverse.total (decodeFamily generatedInput)) :=
  memberCode singletonMap

noncomputable def generatedPartialBody : Code.{0,0} (ContextualSmallFamilyUniverse.total (decodeFamily generatedInput)) :=
  memberCode partialMap

noncomputable def generatedMemberBody : Code.{0,0} (ContextualSmallFamilyUniverse.total (decodeFamily generatedInput)) :=
  memberCode memberMap

noncomputable def generatedSigma : Code.{0,0} raised := sigmaCode generatedInput generatedSingletonBody
noncomputable def generatedPi : Code.{0,0} raised := piCode generatedInput generatedSingletonBody
noncomputable def generatedPartialPi : Code.{0,0} raised := piCode generatedInput generatedPartialBody
noncomputable def generatedW : Code.{0,0} raised := wCode generatedInput generatedMemberBody
noncomputable def generatedUnaryW : Code.{0,0} raised := wCode generatedInput generatedSingletonBody

theorem generated_sum_whole_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (classifier generatedSigma) = decodeFamily generatedSigma :=
  full_decoder _

theorem generated_product_whole_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (classifier generatedPi) = decodeFamily generatedPi :=
  full_decoder _

theorem generated_W_whole_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (classifier generatedW) = decodeFamily generatedW :=
  full_decoder _

noncomputable def raisedEmptySection : (decodeFamily generatedInput).sections :=
  (raisedMemberSections parameters growingParent).symm growingMemberSection

theorem raisedEmptySection_value (parameter : parameters.Elements) :
    (memberDecoder ((ContextualSmallFamilyUniverse.elementMap growingParent).obj parameter)
      ((raisedMemberSections parameters growingParent raisedEmptySection).val parameter)).val =
        emptySet.val parameter.1 := by
  have same := (raisedMemberSections parameters growingParent).apply_symm_apply growingMemberSection
  exact (congrArg (fun term : (memberFamilyUnder growingParent).sections =>
    (memberDecoder ((ContextualSmallFamilyUniverse.elementMap growingParent).obj parameter)
      (term.val parameter)).val) same).trans (growingMemberSection_value parameter)

noncomputable def generatedIdentity : Code.{0,0} raised :=
  identityCode generatedInput raisedEmptySection raisedEmptySection

theorem generated_identity_whole_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (classifier generatedIdentity) = decodeFamily generatedIdentity :=
  full_decoder _

theorem generated_identity_inhabited (parameter : raised.Elements) :
    Nonempty ((decodeFamily generatedIdentity).obj parameter) :=
  ⟨(ContextualSmallFamilyIdentity.reflexivity (decodeFamily generatedInput) raisedEmptySection).val parameter⟩

noncomputable def raisedSingletonFunction : (decodeFamily generatedPi).obj (raisedPoint (world 0)) :=
  (piSubstitution growingParent singletonBody (lowerParameters parameters)).app _ (singletonProduct (point (world 0)))

theorem generated_product_inhabited :
    Nonempty ((decodeFamily generatedPi).obj (raisedPoint (world 0))) := ⟨raisedSingletonFunction⟩

theorem generated_negative_product_empty :
    ¬ Nonempty ((decodeFamily generatedPartialPi).obj (raisedPoint (world 0))) := by
  rintro ⟨term⟩
  exact complete_product_empty
    ⟨(piSubstitutionInverse growingParent selectedEmptyBody (lowerParameters parameters)).app _ term⟩

noncomputable def raisedLeaf (parameter : raised.Elements) : (decodeFamily generatedW).obj parameter :=
  (familyEqHom (w_substitution growingParent (argumentReading growingParent) (lowerParameters parameters))).app
    parameter (emptyPositionLeaf ((ContextualSmallFamilyUniverse.elementMap (lowerParameters parameters)).obj parameter))

theorem generated_argument_dependent_W_inhabited (parameter : raised.Elements) :
    Nonempty ((decodeFamily generatedW).obj parameter) := ⟨raisedLeaf parameter⟩

theorem generated_singleton_position_W_empty (parameter : raised.Elements) :
    ¬ Nonempty ((decodeFamily generatedUnaryW).obj parameter) := by
  rintro ⟨tree⟩
  exact singleton_positions_admit_no_W _
    ⟨(familyEqHom (w_substitution growingParent singletonBody (lowerParameters parameters)).symm).app parameter tree⟩

theorem generated_all_formers_retain_recipes :
    codeTag generatedInput = 0 ∧ codeTag generatedSigma = 1 ∧ codeTag generatedPi = 2 ∧
      codeTag generatedIdentity = 3 ∧ codeTag generatedW = 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem same_full_family_different_recipe :
    decodeFamily (substitute generatedInput (ContextualSmallMapConstructions.identity raised)) =
      decodeFamily generatedInput ∧
    substitute generatedInput (ContextualSmallMapConstructions.identity raised) ≠ generatedInput :=
  ⟨decoder_substitution_id _, seed_identity_recipe_distinct parent⟩

theorem generated_classification_member_roundtrip (parameter : Stagesᵒᵖ)
    (receipt : (ContextualSmallFamilyUniverse.total (decodeFamily generatedSigma)).obj parameter) :
    (classificationBackward generatedSigma).app parameter
      ((classificationForward generatedSigma).app parameter receipt) = receipt :=
  classification_left _ _ _

noncomputable def generated_full_section_comparison :
    (ContextualSmallFamilyUniverse.total (decodeFamily generatedPi)).sections ≃
      (ContextualSmallFamilyUniverse.GenericPullback (classifier generatedPi)).sections :=
  classificationSections _

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedHypersetFamiliesControls
