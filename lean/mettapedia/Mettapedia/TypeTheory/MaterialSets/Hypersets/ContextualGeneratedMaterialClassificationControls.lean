import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedMaterialClassification
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls

/-!
# Generated material-map classification controls

The constructed growing observed family and its actual Pi, Sigma,
identity and W dictionaries instantiate the receipt factory. Parameters
range over the wider complete original hyperset carrier. The actual
classification comparisons retain cyclic payloads and whole natural
sections. The product receipts distinguish functions that agree at every
present argument, while identity and unary W supply empty-fibre controls.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedMaterialClassificationControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualGeneratedUniverse ContextualGeneratedMaterialClassification
open ContextualGeneratedUniverse.Growing

/-- This parameter functor contains every original material set, not an
original-bound cover selected for that wider carrier. -/
def parameters : context.base.Elements ⥤ Type 1 where
  obj _ := HSet
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def operation (family : MaterialFamily context) : NaturalHom (dictionaryBare family).source parameters where
  app _ _ := HSet.quineAtom
  naturality _ _ := rfl

theorem parameters_have_no_original_cover (point : context.base.Elements) :
    ¬ Nonempty (Enumeration.{0, 1} (parameters.obj point)) := by
  rintro ⟨enumeration⟩
  exact CoveredFuturePowerControls.hset_has_no_small_cover enumeration.value enumeration.covered

def piFamily : MaterialFamily context := input.pi body arrowCoding
def sigmaFamily : MaterialFamily context := input.sigma body
def identityFamily : MaterialFamily context := input.identity emptySection positiveSection
def wFamily : MaterialFamily context := input.w body arrowCoding

def piCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.ofRaw Seeds observedSeedModel arrowCoding ⟨piFamily, piGenerated⟩

def sigmaCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.ofRaw Seeds observedSeedModel arrowCoding ⟨sigmaFamily, sigmaGenerated⟩

def identityCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.ofRaw Seeds observedSeedModel arrowCoding ⟨identityFamily, identityGenerated⟩

def wCode : ContextualClosedUniverseCodes.Code Seeds observedSeedModel arrowCoding context :=
  ContextualClosedUniverseCodes.ofRaw Seeds observedSeedModel arrowCoding ⟨wFamily, wGenerated⟩

def piFutureFactory (point : context.base.Elements) (parameter : parameters.obj point) :
    ContextualEnumerationCovers.FutureEnumerations (operation piFamily) point parameter :=
  ClosedCodes.futureFactory Seeds observedSeedModel arrowCoding piCode (operation piFamily) point parameter

def sigmaFutureFactory (point : context.base.Elements) (parameter : parameters.obj point) :
    ContextualEnumerationCovers.FutureEnumerations (operation sigmaFamily) point parameter :=
  ClosedCodes.futureFactory Seeds observedSeedModel arrowCoding sigmaCode (operation sigmaFamily) point parameter

def identityFutureFactory (point : context.base.Elements) (parameter : parameters.obj point) :
    ContextualEnumerationCovers.FutureEnumerations (operation identityFamily) point parameter :=
  ClosedCodes.futureFactory Seeds observedSeedModel arrowCoding identityCode (operation identityFamily) point parameter

def wFutureFactory (point : context.base.Elements) (parameter : parameters.obj point) :
    ContextualEnumerationCovers.FutureEnumerations (operation wFamily) point parameter :=
  ClosedCodes.futureFactory Seeds observedSeedModel arrowCoding wCode (operation wFamily) point parameter

def inputClassifiedSection : (mapTotal input (operation input)).sections :=
  (termClassificationEquiv input (operation input)).symm positiveSection

theorem input_whole_section_inverse :
    termClassificationEquiv input (operation input) inputClassifiedSection = positiveSection :=
  (termClassificationEquiv input (operation input)).apply_symm_apply positiveSection

theorem classified_input_value (raw : profile.sourceFace.Elements) :
    ((mapForward input (operation input)).app
      ((PowerClassPresheafDescent.classElements profile.sourceFace profile.classFace profile.observation).obj raw)
      (inputClassifiedSection.val
        ((PowerClassPresheafDescent.classElements profile.sourceFace profile.classFace profile.observation).obj raw))).val =
          (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.positiveTerm raw).1 := by
  have decoded := congrArg (fun term : input.family.sections => (input.model
    ((PowerClassPresheafDescent.classElements profile.sourceFace profile.classFace profile.observation).obj raw)).value
      (term.val ((PowerClassPresheafDescent.classElements profile.sourceFace profile.classFace profile.observation).obj raw)))
    input_whole_section_inverse
  exact (termClassificationEquiv_value input (operation input) inputClassifiedSection _).symm.trans
    (decoded.trans (positiveSection_value raw))

def futureInputReceipt :
    ((futureEnumerations input (operation input) old HSet.quineAtom)
      ⟨later, PowerClassContextualMaterialization.Growing.futureArrow⟩).Carrier :=
  ⟨PowerClassContextualMaterialization.Growing.futureArgument, rfl⟩

theorem constructed_future_receipt_cyclic :
    (((futureEnumerations input (operation input) old HSet.quineAtom)
      ⟨later, PowerClassContextualMaterialization.Growing.futureArrow⟩).value futureInputReceipt).val.val = HSet.quineAtom :=
  cyclic_leaf_shape

theorem every_current_receipt_empty
    (receipt : (fibreEnumeration input (operation input) old HSet.quineAtom).Carrier) :
    ((fibreEnumeration input (operation input) old HSet.quineAtom).value receipt).val.val = ∅ :=
  (input_value old receipt.val).trans
    (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.currentArgument_value receipt.val)

theorem current_receipts_miss_future_value
    (receipt : (fibreEnumeration input (operation input) old HSet.quineAtom).Carrier) :
    ((fibreEnumeration input (operation input) old HSet.quineAtom).value receipt).val.val ≠
      (((futureEnumerations input (operation input) old HSet.quineAtom)
        ⟨later, PowerClassContextualMaterialization.Growing.futureArrow⟩).value futureInputReceipt).val.val := by
  rw [every_current_receipt_empty, constructed_future_receipt_cyclic]
  exact HSet.empty_ne_quineAtom

def identityReceipt : (fibreEnumeration piFamily (operation piFamily) old HSet.quineAtom).Carrier :=
  ⟨PowerClassContextualMaterialization.Growing.identityFunction.val old, rfl⟩

def constantReceipt : (fibreEnumeration piFamily (operation piFamily) old HSet.quineAtom).Carrier :=
  ⟨PowerClassContextualMaterialization.Growing.constantFunction.val old, rfl⟩

theorem full_pi_receipts_distinct :
    ((fibreEnumeration piFamily (operation piFamily) old HSet.quineAtom).value identityReceipt).val.val ≠
      ((fibreEnumeration piFamily (operation piFamily) old HSet.quineAtom).value constantReceipt).val.val :=
  future_functions_differ

theorem current_pi_evaluation_loses_receipts :
    ¬ Function.Injective (fun receipt : (fibreEnumeration piFamily (operation piFamily) old HSet.quineAtom).Carrier =>
      fun argument : input.family.obj old => receipt.val.app old (𝟙 old) argument) := by
  intro injective
  have agreement : (fun argument : input.family.obj old => identityReceipt.val.app old (𝟙 old) argument) =
      (fun argument : input.family.obj old => constantReceipt.val.app old (𝟙 old) argument) := by
    funext argument
    exact Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.current_applications_agree argument
  exact full_pi_receipts_distinct (congrArg (fun receipt =>
    ((fibreEnumeration piFamily (operation piFamily) old HSet.quineAtom).value receipt).val.val) (injective agreement))

def cyclicSigmaReceipt : (fibreEnumeration sigmaFamily (operation sigmaFamily) later HSet.quineAtom).Carrier :=
  ⟨cyclicPair, rfl⟩

theorem sigma_receipt_retains_cyclic_coordinate :
    HSet.fst (((fibreEnumeration sigmaFamily (operation sigmaFamily) later HSet.quineAtom).value cyclicSigmaReceipt).val.val) =
      HSet.quineAtom := cyclicPair_first

theorem later_identity_receipts_empty :
    ¬ Nonempty (fibreEnumeration identityFamily (operation identityFamily) newPoint HSet.quineAtom).Carrier := by
  rintro ⟨receipt⟩
  have member := (identityFamily.model newPoint).value_mem receipt.val
  rw [show (identityFamily.model newPoint).carrier = ∅ from identity_new_carrier] at member
  exact HSet.notMem_empty _ member

def leafFamily : MaterialFamily context := input.w terminalBody arrowCoding

def cyclicLeafReceipt : (fibreEnumeration leafFamily (operation leafFamily) later HSet.quineAtom).Carrier :=
  ⟨leaf later PowerClassContextualMaterialization.Growing.futureArgument, rfl⟩

theorem cyclic_leaf_receipt_material :
    ((fibreEnumeration leafFamily (operation leafFamily) later HSet.quineAtom).value cyclicLeafReceipt).val.val ∈
      (leafFamily.model later).carrier :=
  cyclic_leaf_material_member

def unaryFamily : MaterialFamily context := input.w unaryBody arrowCoding

theorem unary_w_receipts_empty (point : context.base.Elements) :
    ¬ Nonempty (fibreEnumeration unaryFamily (operation unaryFamily) point HSet.quineAtom).Carrier := by
  rintro ⟨receipt⟩
  have member := (unaryFamily.model point).value_mem receipt.val
  rw [show (unaryFamily.model point).carrier = ∅ from unary_w_empty point] at member
  exact HSet.notMem_empty _ member

theorem input_parameter_cover (point : context.base.Elements) :
    Function.Surjective ((ContextualMaterialSmallMapClassification.futureChange
      (dictionaryBare input) (operation input)).app point) :=
  future_parameters_cover input (operation input) point

theorem input_source_cover (point : context.base.Elements) :
    Function.Surjective ((ContextualMaterialSmallMapClassification.futureTop
      (dictionaryBare input) (operation input)).app point) :=
  future_top_cover input (operation input) point

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedMaterialClassificationControls
