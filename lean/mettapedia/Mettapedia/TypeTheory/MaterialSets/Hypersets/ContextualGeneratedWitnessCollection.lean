import Mettapedia.TypeTheory.ContextualBoundedCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedMaterialClassification

/-!
# Bounded witness Collection for interpreted material families

The dictionaries constructed for interpreted and generated material
families supply actual small fibre decoders for authored material maps.
Those decoders instantiate the coherent small-map class. A second
interpreted family supplies a small potential witness family over all
source members, retaining its contextual maps.

The covering square is then constructed from bounded totality of its
natural witness reading. There is no claim that every wider cover admits
such a reading or that arbitrary bare material carriers already have
original-bound generated dictionaries.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedWitnessCollection

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps ContextualGeneratedUniverse

universe u v w
variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable (domain : MaterialFamily context)
variable {A : context.base.Elements ⥤ Type v}
variable (operation : NaturalHom (ContextualGeneratedMaterialClassification.dictionaryBare domain).source A)

/-- The actual saturated material receipt decoder, rather than a selected
presentation of a proof-small host map, supplies the coherent family. -/
def mapData : Data operation where
  family := ContextualGeneratedMaterialClassification.mapSmallFamily domain operation
  decoder := ContextualMaterialSmallMapClassification.fibreDecoder
    (ContextualGeneratedMaterialClassification.dictionaryBare domain) operation
    (ContextualSmallMapConstructions.identity A)
    (ContextualGeneratedMaterialClassification.substitutedEnumeration domain operation
      (ContextualSmallMapConstructions.identity A))
  naturality step term := by
    apply Subtype.ext
    exact (ContextualMaterialSmallMapClassification.decode_restriction
      (ContextualGeneratedMaterialClassification.dictionaryBare domain) operation
      (ContextualSmallMapConstructions.identity A)
      (ContextualGeneratedMaterialClassification.substitutedEnumeration domain operation
        (ContextualSmallMapConstructions.identity A)) step term).symm

theorem mapData_family : (mapData domain operation).family =
    ContextualGeneratedMaterialClassification.mapSmallFamily domain operation := rfl

def witnessFamily (candidate : MaterialFamily context) :
    (ContextualGeneratedMaterialClassification.dictionaryBare domain).source.Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.restrict
    (CategoryOfElements.π (ContextualGeneratedMaterialClassification.dictionaryBare domain).source)
    candidate.family

def witnessDecoder (candidate : MaterialFamily context)
    (point : (ContextualGeneratedMaterialClassification.dictionaryBare domain).source.Elements) :
    MaterialEnumerationDecoders.Members (candidate.model point.1).carrier ≃
      (witnessFamily domain candidate).obj point :=
  (candidate.model point.1).decode

variable {Y : context.base.Elements ⥤ Type w}
variable (cover : NaturalHom Y (ContextualGeneratedMaterialClassification.dictionaryBare domain).source)
variable (candidate : MaterialFamily context)
variable (reading : NaturalHom (ContextualSmallFamilyUniverse.total (witnessFamily domain candidate)) Y)

def collectedData : Data (ContextualBoundedCollection.collectedMap operation cover
    (witnessFamily domain candidate) reading) :=
  ContextualBoundedCollection.collectedData operation (mapData domain operation) cover
    (witnessFamily domain candidate) reading

theorem bounded_collection
    (total : ContextualBoundedCollection.BoundedTotal cover (witnessFamily domain candidate) reading) :
    ContextualCoherentSmallMaps.Cover (ContextualBoundedCollection.comparison operation cover
      (witnessFamily domain candidate) reading) ∧
      SmallFibres (ContextualBoundedCollection.collectedMap operation cover
        (witnessFamily domain candidate) reading) := by
  exact ⟨(ContextualBoundedCollection.comparison_cover_iff operation cover _ reading).mpr total,
    (collectedData domain operation cover candidate reading).smallFibres⟩

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedWitnessCollection
