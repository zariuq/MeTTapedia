import Mettapedia.TypeTheory.ContextualCollectionGenerators
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedWitnessCollection

/-!
# Constructed Collection generators for material dictionaries

The actual material decoder supplies all future small-map enumerations.
For an interpreted covering domain it also supplies the complete small
cover-receipt carrier, whose nonemptiness follows only propositionally
from cover surjectivity. The collected object retains those codes and
constructs the full contextual covering square.

A separate bounded-reading construction permits wider, non-small covers.
It requires totality inside the actual generated witness bound. Neither
construction selects witnesses from pointwise existence, and neither
states Collection for arbitrary bare-material carrier functions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCollectionGenerators

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps ContextualGeneratedUniverse

universe u v w
variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable (domain : MaterialFamily context)
variable {A : context.base.Elements ⥤ Type v}
variable (operation : NaturalHom (ContextualGeneratedMaterialClassification.dictionaryBare domain).source A)

section InterpretedCover

variable (coverDomain : MaterialFamily context)
variable (cover : NaturalHom (ContextualGeneratedMaterialClassification.dictionaryBare coverDomain).source
  (ContextualGeneratedMaterialClassification.dictionaryBare domain).source)
variable (covered : Cover cover)

def generator (point : context.base.Elements) (parameter : A.obj point) :
    ContextualCollectionGenerators.Generator operation cover :=
  ContextualCollectionGenerators.coherentGenerator operation cover
    (ContextualGeneratedWitnessCollection.mapData domain operation)
    (ContextualGeneratedWitnessCollection.mapData coverDomain cover) covered point parameter

include covered in
theorem full_collection :
    Cover (ContextualCollectionGenerators.parameterMap operation cover) ∧
      Cover (ContextualCollectionGenerators.comparison operation cover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap operation cover) ∧
      (ContextualCollectionGenerators.top operation cover).comp (cover.comp operation) =
        (ContextualCollectionGenerators.collectedMap operation cover).comp
          (ContextualCollectionGenerators.parameterMap operation cover) :=
  ContextualCollectionGenerators.coherent_collection operation cover
    (ContextualGeneratedWitnessCollection.mapData domain operation)
    (ContextualGeneratedWitnessCollection.mapData coverDomain cover) covered

theorem generator_root (point : context.base.Elements) (parameter : A.obj point) :
    (generator domain operation coverDomain cover covered point parameter).point = point ∧
      (generator domain operation coverDomain cover covered point parameter).parameter = parameter := ⟨rfl, rfl⟩

end InterpretedCover

section WiderBoundedCover

variable {Y : context.base.Elements ⥤ Type w}
variable (cover : NaturalHom Y (ContextualGeneratedMaterialClassification.dictionaryBare domain).source)
variable (candidate : MaterialFamily context)
variable (reading : NaturalHom (ContextualSmallFamilyUniverse.total
    (ContextualGeneratedWitnessCollection.witnessFamily domain candidate)) Y)
variable (total : ContextualBoundedCollection.BoundedTotal cover
    (ContextualGeneratedWitnessCollection.witnessFamily domain candidate) reading)

def boundedGenerator (point : context.base.Elements) (parameter : A.obj point) :
    ContextualCollectionGenerators.Generator operation cover :=
  ContextualCollectionGenerators.boundedGenerator operation cover
    (ContextualGeneratedWitnessCollection.mapData domain operation)
    (ContextualGeneratedWitnessCollection.witnessFamily domain candidate) reading total point parameter

include candidate reading total in
theorem wider_bounded_collection :
    Cover (ContextualCollectionGenerators.parameterMap operation cover) ∧
      Cover (ContextualCollectionGenerators.comparison operation cover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap operation cover) ∧
      (ContextualCollectionGenerators.top operation cover).comp (cover.comp operation) =
        (ContextualCollectionGenerators.collectedMap operation cover).comp
          (ContextualCollectionGenerators.parameterMap operation cover) :=
  ContextualCollectionGenerators.full_diagram operation cover
    (ContextualCollectionGenerators.bounded_generator_exists operation cover
      (ContextualGeneratedWitnessCollection.mapData domain operation)
      (ContextualGeneratedWitnessCollection.witnessFamily domain candidate) reading total)

end WiderBoundedCover

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCollectionGenerators
