import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoherentDescent
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualBoundedCollectionControls

/-!
# Coherent material descent preserves values and forgets raw tags

An authored Boolean tag doubles every occurrence of the actual growing
material family. Its composite map has a constructed coherent small
decoder. Covered-quotient descent reconstructs a whole small natural
section and preserves the cyclic member value. The two tags become the
same material receipt, and the raw tag reading cannot factor through that
cover, even at the original point.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoherentDescentControls

open _root_.CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps ContextualBoundedCollectionControls
open ContextualGeneratedUniverse.Growing

universe u v

def tagged {D : Type u} [Category.{u} D] (family : D ⥤ Type v) : D ⥤ Type v where
  obj point := family.obj point × Bool
  map step := TypeCat.ofHom fun receipt => (family.map step receipt.1, receipt.2)
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Prod.ext (family.map_id_apply point receipt.1) rfl
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Prod.ext (family.map_comp_apply earlier later receipt.1) rfl

abbrev taggedSource := tagged sourceFamily

def tagCover : NaturalHom taggedSource sourceFamily where
  app _ := Prod.fst
  naturality _ _ := rfl

theorem tagCover_onto : Cover tagCover := fun _ member => ⟨(member, false), rfl⟩

abbrev receiverModel := ContextualGeneratedWitnessCollection.mapData input operation

def sourceDecoder (point : parameters.Elements) :
    (receiverModel.family.obj point × Bool) ≃ Fibre (tagCover.comp operation) point.1 point.2 where
  toFun code := ⟨((receiverModel.decoder point code.1).val, code.2), (receiverModel.decoder point code.1).property⟩
  invFun receipt := ((receiverModel.decoder point).symm ⟨receipt.val.1, receipt.property⟩, receipt.val.2)
  left_inv code := Prod.ext ((receiverModel.decoder point).symm_apply_apply code.1) rfl
  right_inv receipt := Subtype.ext (Prod.ext
    (congrArg Subtype.val ((receiverModel.decoder point).apply_symm_apply ⟨receipt.val.1, receipt.property⟩)) rfl)

def sourceModel : Data (tagCover.comp operation) :=
  ofEquivs _ (fun point => receiverModel.family.obj point × Bool) sourceDecoder

def receivedModel : Data operation := ContextualMaterialCoherentDescent.descendedData
  (ContextualGeneratedMaterialClassification.dictionaryBare input) operation tagCover tagCover_onto sourceModel

def sourceSection : sourceFamily.sections :=
  (ContextualGeneratedMaterialClassification.encode input).mapSection positiveSection

def receivedSection : (ContextualSmallFamilyUniverse.total receivedModel.family).sections :=
  receivedModel.sectionEquiv.symm sourceSection

theorem whole_section_recovered : receivedModel.sectionEquiv receivedSection = sourceSection :=
  receivedModel.sectionEquiv.apply_symm_apply sourceSection

theorem recovered_cyclic_value :
    (receivedModel.forward.app newPoint (receivedSection.val newPoint)).val = HSet.quineAtom := by
  have decoded := congrArg (fun termSection : sourceFamily.sections => (termSection.val newPoint).val) whole_section_recovered
  exact decoded.trans (positiveSection_value newRaw)

def originalCode : receiverModel.family.obj ⟨old, PUnit.unit⟩ :=
  (receiverModel.decoder ⟨old, PUnit.unit⟩).symm ⟨emptyMemberSection.val old, rfl⟩

theorem duplicate_tag_receipts_have_same_material_value :
    (ContextualMaterialCoherentDescent.enumeration
      (ContextualGeneratedMaterialClassification.dictionaryBare input) operation tagCover tagCover_onto sourceModel
      old PUnit.unit).value (originalCode, false) =
    (ContextualMaterialCoherentDescent.enumeration
      (ContextualGeneratedMaterialClassification.dictionaryBare input) operation tagCover tagCover_onto sourceModel
      old PUnit.unit).value (originalCode, true) := rfl

def tagFamily : ContextualGeneratedUniverse.Growing.context.base.Elements ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def tagReading : NaturalHom taggedSource tagFamily where
  app _ := Prod.snd
  naturality _ _ := rfl

theorem raw_tag_does_not_descend :
    ¬ ∃ reading : NaturalHom sourceFamily tagFamily, tagCover.comp reading = tagReading := by
  rintro ⟨reading, factors⟩
  have first := congrArg (fun map : NaturalHom taggedSource tagFamily =>
    map.app old (emptyMemberSection.val old, false)) factors
  have second := congrArg (fun map : NaturalHom taggedSource tagFamily =>
    map.app old (emptyMemberSection.val old, true)) factors
  exact Bool.false_ne_true (first.symm.trans second)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoherentDescentControls
