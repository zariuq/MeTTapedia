import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedMemberSuccessorCoherence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedHypersetFamiliesControls

/-!+# Infinite, argument-dependent generated successor controls

The original member family acquires a cyclic argument in a later context.
Its independently formed upper product retains that future argument and
the original typed result. A partial dependent body still has an answer
at every present argument and no complete future product. The upper W
controls distinguish an actual empty-position leaf from everywhere
inhabited positions. Full family decoding and recipe distinctions are
both retained through the cumulative embedding.

A genuinely noninjective parameter map tests substitution of the complete
family. These are fixed-site comparisons with original small fibres,
not equality with a lifted material-set universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedMemberSuccessorControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualHypersetFamilyClosure
open HostChoiceContextualHypersetFamilyClosureControls
open HostChoiceContextualGeneratedHypersetFamiliesControls
open HostChoiceContextualGeneratedMemberSuccessorUniverse
open HostChoiceContextualGeneratedMemberSuccessorCoherence
open HostChoiceContextualHypersetModelControls.Infinite
open PowerClassPresheafDescent.Controls

abbrev upperParameters := parametersUp raised
abbrev upperPoint (stage : Stagesᵒᵖ) : upperParameters.Elements :=
  ⟨stage, ULift.up (ULift.up PUnit.unit)⟩

noncomputable def upperInput : Code.{0,0} upperParameters := liftCode generatedInput
noncomputable def positiveProduct : Code.{0,0} upperParameters :=
  upperPi generatedInput generatedSingletonBody
noncomputable def partialProduct : Code.{0,0} upperParameters :=
  upperPi generatedInput generatedPartialBody
noncomputable def positiveSum : Code.{0,0} upperParameters :=
  upperSigma generatedInput generatedSingletonBody
noncomputable def leafTrees : Code.{0,0} upperParameters :=
  upperW generatedInput generatedMemberBody
noncomputable def unaryTrees : Code.{0,0} upperParameters :=
  upperW generatedInput generatedSingletonBody
noncomputable def diagonalIdentity : Code.{0,0} upperParameters :=
  upperIdentity generatedInput raisedEmptySection raisedEmptySection

theorem actual_upper_product_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (classifier positiveProduct) = decodeFamily positiveProduct :=
  full_decoder _

theorem actual_upper_sum_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (classifier positiveSum) = decodeFamily positiveSum :=
  full_decoder _

theorem actual_upper_identity_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (classifier diagonalIdentity) = decodeFamily diagonalIdentity :=
  full_decoder _

theorem actual_upper_W_decoder :
    ContextualSmallFamilyUniverse.decodedFamily (classifier leafTrees) = decodeFamily leafTrees :=
  full_decoder _

noncomputable def upperSingletonFunction : (decodeFamily positiveProduct).obj (upperPoint (world 0)) :=
  (piComparison generatedInput generatedSingletonBody).app _ raisedSingletonFunction

theorem positive_product_inhabited :
    Nonempty ((decodeFamily positiveProduct).obj (upperPoint (world 0))) := ⟨upperSingletonFunction⟩

noncomputable def upperFutureLoopArgument :
    (ContextualSmallFamilyTypeFormers.futureDomain (decodeFamily upperInput) (upperPoint (world 0))).Elements :=
  ⟨⟨world 1, advance⟩, loopArgument⟩

theorem upper_product_keeps_future_result
    (argument : (ContextualSmallFamilyTypeFormers.futureDomain (decodeFamily upperInput)
      (upperPoint (world 0))).Elements) :
    HEq (upperSingletonFunction.val argument)
      (raisedSingletonFunction.val ((ContextualSmallFamilyTypeFormerCoherence.futureArgumentChange
        (parametersDown raised) (lowerFamily generatedInput) (upperPoint (world 0))).obj argument)) :=
  piComparison_value generatedInput generatedSingletonBody _ _ argument

theorem future_cyclic_body_still_empty :
    ¬ Nonempty ((ContextualSmallFamilyComprehension.indexedBody (decodeFamily upperInput)
      (decodeFamily (liftBody generatedInput generatedPartialBody))).obj
        ((ContextualSmallFamilyTypeFormers.futureArguments (decodeFamily upperInput)
          (upperPoint (world 0))).obj upperFutureLoopArgument)) :=
  future_cyclic_body_empty

theorem every_upper_present_argument_has_answer :
    ∀ argument : (decodeFamily upperInput).obj (upperPoint (world 0)),
      Nonempty ((ContextualSmallFamilyComprehension.indexedBody (decodeFamily upperInput)
        (decodeFamily (liftBody generatedInput generatedPartialBody))).obj ⟨upperPoint (world 0), argument⟩) :=
  every_present_argument_has_answer

theorem complete_upper_partial_product_empty :
    ¬ Nonempty ((decodeFamily partialProduct).obj (upperPoint (world 0))) := by
  rintro ⟨term⟩
  exact generated_negative_product_empty
    ⟨(piComparisonInverse generatedInput generatedPartialBody).app _ term⟩

noncomputable def upperLeaf (parameter : upperParameters.Elements) : (decodeFamily leafTrees).obj parameter :=
  (familyEqHom (w_family_comparison generatedInput generatedMemberBody)).app parameter
    (raisedLeaf ((ContextualSmallFamilyUniverse.elementMap (parametersDown raised)).obj parameter))

theorem empty_position_upper_W_inhabited (parameter : upperParameters.Elements) :
    Nonempty ((decodeFamily leafTrees).obj parameter) := ⟨upperLeaf parameter⟩

theorem singleton_position_upper_W_empty (parameter : upperParameters.Elements) :
    ¬ Nonempty ((decodeFamily unaryTrees).obj parameter) := by
  rintro ⟨tree⟩
  exact generated_singleton_position_W_empty _
    ⟨(familyEqHom (w_family_comparison generatedInput generatedSingletonBody).symm).app parameter tree⟩

theorem upper_diagonal_identity_inhabited (parameter : upperParameters.Elements) :
    Nonempty ((decodeFamily diagonalIdentity).obj parameter) :=
  ⟨(ContextualSmallFamilyIdentity.reflexivity (decodeFamily upperInput)
    (sectionEquiv generatedInput raisedEmptySection)).val parameter⟩

theorem lower_recipe_distinctions_survive :
    liftCode (HostChoiceContextualGeneratedHypersetFamilies.substitute generatedInput
      (ContextualSmallMapConstructions.identity raised)) ≠ liftCode generatedInput := by
  intro same
  exact same_full_family_different_recipe.2 ((liftCode_injective raised) same)

theorem independently_formed_recipes_remain_distinct :
    liftCode generatedSigma ≠ positiveSum ∧ liftCode generatedPi ≠ positiveProduct ∧
      liftCode generatedW ≠ leafTrees ∧ liftCode generatedIdentity ≠ diagonalIdentity :=
  ⟨sigma_recipes_distinct _ _, pi_recipes_distinct _ _, w_recipes_distinct _ _,
    identity_recipes_distinct _ _ _⟩

def taggedParameters : Stagesᵒᵖ ⥤ Type 1 where
  obj stage := raised.obj stage × Bool
  map step := TypeCat.ofHom fun receipt => (raised.map step receipt.1, receipt.2)
  map_id stage := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Prod.ext (raised.map_id_apply stage receipt.1) rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Prod.ext (raised.map_comp_apply first second receipt.1) rfl

def forgetTag : NaturalHom taggedParameters raised where
  app _ receipt := receipt.1
  naturality _ _ := rfl

theorem forgetTag_not_injective : ¬ Function.Injective (forgetTag.app (world 0)) := by
  intro injective
  have same := injective (show forgetTag.app (world 0) (ULift.up PUnit.unit, false) =
    forgetTag.app (world 0) (ULift.up PUnit.unit, true) from rfl)
  have impossible : false = true := congrArg Prod.snd same
  cases impossible

theorem noninjective_substitution_keeps_whole_decoder :
    decodeFamily (liftCode (HostChoiceContextualGeneratedHypersetFamilies.substitute generatedInput forgetTag)) =
      decodeFamily (substitute upperInput (changeUp forgetTag)) :=
  lift_substitution_family _ _

theorem noninjective_substitution_keeps_classifier :
    classifier (substitute upperInput (changeUp forgetTag)) =
      (changeUp forgetTag).comp (classifier upperInput) :=
  classifier_substitution _ _

noncomputable def whole_upper_product_sections :
    (ContextualSmallFamilyUniverse.total (decodeFamily positiveProduct)).sections ≃
      (ContextualSmallFamilyUniverse.GenericPullback (classifier positiveProduct)).sections :=
  classificationSections _

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualGeneratedMemberSuccessorControls
