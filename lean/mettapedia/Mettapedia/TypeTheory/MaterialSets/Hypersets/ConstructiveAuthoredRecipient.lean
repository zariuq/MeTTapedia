import Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructiveMaterialRecipientModel
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReceiptFamilySubstitution
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseSizeObstructions

/-!
# A generated constructive material model from the coalgebra recipient

The actual all-small-coalgebra recipient supplies every primitive fibre
dictionary on the raised observed site. Its native classes and graph bound
are `u+1`; literal graph members have type universe `u+2`. Parameters range
over the entire bare `HSet (u+1)` carrier, with no graph or smaller decoder
for that parameter carrier. Dependent dictionaries nevertheless form over
all these parameters and all their actual contextual arrows.

Primitive substitutions recursively generate Sigma, complete future Pi,
discrete identity, hereditary W and stable separation. Every generated
family has actual restriction and section decoders, and every admitted
over-parameter cover receives the constructive Collection diagram. The
receipt bound is raised explicitly. This does not make the recipient a
fixed point for all successor-small coalgebras or imply unrestricted
original-bound Collection for arbitrary wider witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructiveAuthoredRecipient

open CategoryTheory Mettapedia.TypeTheory
open ContextualGeneratedUniverse ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualAuthoredMaterialFamilies

universe u
variable {C : Type u} [Category.{u} C] (context : LabelledContext C)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev World := (ContextualSiteLiftMaterial.context context).base.Elements

abbrev worlds : ArgumentCoding (World context) := (ContextualSiteLiftMaterial.context context).labels

def worldArrows (first second : World context) : ArgumentCoding (first ⟶ second) :=
  MaterialFamily.elementArrowCoding (context := ContextualSiteLiftMaterial.context context)
    (ContextualSiteLiftMaterial.arrows arrows) first second

/-- Bare ambient values remain external parameters. Their maps retain the
actual value while the dependent material family changes with context. -/
def parameters : World context ⥤ Type (u + 2) where
  obj _ := HSet.{u + 1}
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def input : Family (parameters context) where
  native := restrict (CategoryOfElements.π (parameters context))
    (ConstructiveMaterialRecipientModel.recipient context arrows).family
  models point := (ConstructiveMaterialRecipientModel.recipient context arrows).model point.1

theorem input_value (point : (parameters context).Elements)
    (value : (input context arrows).native.obj point) :
    ((input context arrows).models point).value value =
      ((ConstructiveMaterialRecipientModel.recipient context arrows).model point.1).value value := rfl

/-- The native classifier retains the complete authored future functor.
Its independent decoder recovers both fibres and restrictions. -/
theorem input_classifier_decoder :
    decodedFamily (classifier (input context arrows).native) = (input context arrows).native :=
  decoded_classifier_eq (input context arrows).native

def inputSection (term : (ConstructiveMaterialRecipientModel.recipient context arrows).family.sections) :
    (input context arrows).native.sections :=
  ⟨fun point => term.val point.1, fun step => term.property step.1⟩

theorem inputSection_material (term : (ConstructiveMaterialRecipientModel.recipient context arrows).family.sections)
    (point : (parameters context).Elements) :
    (((input context arrows).sectionDecoder (inputSection context arrows term)).val point).val =
      ((ConstructiveMaterialRecipientModel.recipient context arrows).model point.1).value (term.val point.1) :=
  (input context arrows).sectionDecoder_value (inputSection context arrows term) point

def seeds (base : World context ⥤ Type (u + 2)) : Type (u + 2) := NaturalHom base (parameters context)

def seedModel (base : World context ⥤ Type (u + 2)) (index : seeds context base) : Family base :=
  (input context arrows).reindex index

abbrev Code (base : World context ⥤ Type (u + 2)) :=
  ContextualAuthoredGeneratedFamilies.Code.{u + 1, u + 2} (worlds context) (worldArrows context arrows)
    (seeds context) (seedModel context arrows) base

def inputCode : Code context arrows (parameters context) :=
  ContextualAuthoredGeneratedFamilies.Code.seed.{u + 1, u + 2}
    (ContextualSmallMapConstructions.identity (parameters context))

abbrev bodyCode : Code context arrows (inputCode context arrows).decode.extension :=
  (inputCode context arrows).reindex (projection (inputCode context arrows).decode.native)

/-- These sections depend on the actual last argument. In particular,
identity against an authored section distinguishes equal and unequal
material arguments inside the same fibre. -/
def equalityBody (term : (input context arrows).native.sections) :
    Code context arrows (inputCode context arrows).decode.extension :=
  (bodyCode context arrows).identity
    (ContextualSmallFamilyIdentity.lastVariable (input context arrows).native)
    (ContextualSmallFamilyIdentity.reindexSection (projection (input context arrows).native)
      (input context arrows).native term)

def piCode (term : (input context arrows).native.sections) : Code context arrows (parameters context) :=
  (inputCode context arrows).pi (equalityBody context arrows term)

def sigmaCode (term : (input context arrows).native.sections) : Code context arrows (parameters context) :=
  (inputCode context arrows).sigma (equalityBody context arrows term)

noncomputable def wCode (term : (input context arrows).native.sections) : Code context arrows (parameters context) :=
  (inputCode context arrows).w (equalityBody context arrows term)

/-- The external collection of all recursively generated carrier readings
has two further graph raises. Reindexing retains the whole code and its
family; it is not inferred from equality of a present carrier reading. -/
def enclosure (base : World context ⥤ Type (u + 2)) (point : base.Elements) : HSet.{u + 3} :=
  HSet.imageUp fun code : Code context arrows base => HSet.lift (code.decode.models point).carrier

theorem mem_enclosure_iff {base : World context ⥤ Type (u + 2)} {point : base.Elements}
    {value : HSet.{u + 3}} :
    value ∈ enclosure context arrows base point ↔
      ∃ code : Code context arrows base, HSet.lift (HSet.lift (code.decode.models point).carrier) = value :=
  HSet.mem_imageUp_iff

theorem generated_enclosed {base : World context ⥤ Type (u + 2)}
    (code : Code context arrows base) (point : base.Elements) :
    HSet.lift (HSet.lift (code.decode.models point).carrier) ∈ enclosure context arrows base point :=
  HSet.lift_mem_imageUp (fun code : Code context arrows base => HSet.lift (code.decode.models point).carrier) code

theorem equalityBody_inhabited (term : (input context arrows).native.sections)
    (point : (parameters context).Elements) (argument : (input context arrows).native.obj point) :
    Nonempty ((equalityBody context arrows term).decode.native.obj ⟨point.1, ⟨point.2, argument⟩⟩) ↔
      ((input context arrows).models point).value argument =
        ((input context arrows).models point).value (term.val point) :=
  ContextualReceiptFamilyModels.identity_inhabited
    (bodyCode context arrows).decode.native (bodyCode context arrows).decode.models
    (ContextualSmallFamilyIdentity.lastVariable (input context arrows).native)
    (ContextualSmallFamilyIdentity.reindexSection (projection (input context arrows).native)
      (input context arrows).native term) ⟨point.1, ⟨point.2, argument⟩⟩

theorem wide_parameters_not_small (point : World context) :
    ¬ Small.{u + 1} ((parameters context).obj point) := UniverseSizeObstructions.ambient_not_small

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ConstructiveAuthoredRecipient
