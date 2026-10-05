import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialCwf

/-!
# Recursive constructive generation of authored material families

Declared seed dictionaries generate full families by dependent sums,
complete future products, discrete identity, hereditary W, stable
separation and actual parameter substitution. Bodies are generated over
the genuine comprehension parameter family. Derivations are retained as
data, so no decoder or formation witness is selected from nonemptiness.

Decoding a code yields its actual native restriction maps and constructed
material dictionaries. Its natural sections have the proved two-way
material-member interpretation. Every code inherits the authored-slice
Collection construction. This generated interpretation does not classify
all arbitrary wider presheaves or assert unrestricted same-level material
Collection or a powerclass fixed point.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedFamilies

open CategoryTheory Mettapedia.TypeTheory
open ContextualAuthoredMaterialFamilies ContextualWitnessCover

universe u v
variable {D : Type u} [Category.{u} D]

variable (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (seeds : (base : D ⥤ Type (max u v)) → Type (max (u + 1) v))
variable (seedModel : (base : D ⥤ Type (max u v)) → seeds base → Family base)

inductive Generation : {base : D ⥤ Type (max u v)} → Family base → Type (max (u + 1) (v + 1)) where
  | seed {base} (index : seeds base) : Generation (seedModel base index)
  | sigma {base} {domain : Family base} {body : Family domain.extension} :
      Generation domain → Generation body → Generation (domain.sigma body)
  | pi {base} {domain : Family base} {body : Family domain.extension} :
      Generation domain → Generation body → Generation (domain.pi body worlds arrows)
  | w {base} {domain : Family base} {body : Family domain.extension} :
      Generation domain → Generation body → Generation (domain.w body worlds arrows)
  | identity {base} {domain : Family base} (formed : Generation domain)
      (left right : domain.native.sections) : Generation (domain.identity left right)
  | separate {base} {domain : Family base} (formed : Generation domain)
      (predicate : ContextualReceiptFamilyModels.StablePredicate domain.native) :
      Generation (domain.separate predicate)
  | reindex {base other : D ⥤ Type (max u v)} {domain : Family base}
      (formed : Generation domain) (change : NaturalHom other base) :
      Generation (domain.reindex change)

abbrev Code (base : D ⥤ Type (max u v)) :=
  (family : Family base) × Generation worlds arrows seeds seedModel family

namespace Code

variable {worlds arrows seeds seedModel}
variable {base : D ⥤ Type (max u v)}

abbrev decode (code : Code worlds arrows seeds seedModel base) : Family base := code.1

def seed (index : seeds base) : Code worlds arrows seeds seedModel base :=
  ⟨seedModel base index, .seed index⟩

def sigma (domain : Code worlds arrows seeds seedModel base)
    (body : Code worlds arrows seeds seedModel domain.decode.extension) :
    Code worlds arrows seeds seedModel base :=
  ⟨domain.decode.sigma body.decode, .sigma domain.2 body.2⟩

def pi (domain : Code worlds arrows seeds seedModel base)
    (body : Code worlds arrows seeds seedModel domain.decode.extension) :
    Code worlds arrows seeds seedModel base :=
  ⟨domain.decode.pi body.decode worlds arrows, .pi domain.2 body.2⟩

noncomputable def w (domain : Code worlds arrows seeds seedModel base)
    (body : Code worlds arrows seeds seedModel domain.decode.extension) :
    Code worlds arrows seeds seedModel base :=
  ⟨domain.decode.w body.decode worlds arrows, .w domain.2 body.2⟩

def identity (domain : Code worlds arrows seeds seedModel base)
    (left right : domain.decode.native.sections) : Code worlds arrows seeds seedModel base :=
  ⟨domain.decode.identity left right, .identity domain.2 left right⟩

def separate (domain : Code worlds arrows seeds seedModel base)
    (predicate : ContextualReceiptFamilyModels.StablePredicate domain.decode.native) :
    Code worlds arrows seeds seedModel base :=
  ⟨domain.decode.separate predicate, .separate domain.2 predicate⟩

def reindex {other : D ⥤ Type (max u v)} (domain : Code worlds arrows seeds seedModel base)
    (change : NaturalHom other base) : Code worlds arrows seeds seedModel other :=
  ⟨domain.decode.reindex change, .reindex domain.2 change⟩

abbrev memberSections (code : Code worlds arrows seeds seedModel base) := code.decode.members.sections

/-- This inverse uses every constructed fibre decoder and actual native
restriction; it is not extracted from a formation proposition. -/
def sectionDecoder (code : Code worlds arrows seeds seedModel base) :
    code.decode.native.sections ≃ code.memberSections := code.decode.sectionDecoder

theorem sectionDecoder_value (code : Code worlds arrows seeds seedModel base)
    (term : code.decode.native.sections) (point : base.Elements) :
    ((code.sectionDecoder term).val point).val = (code.decode.models point).value (term.val point) :=
  code.decode.sectionDecoder_value term point

theorem memberRestriction_decode (code : Code worlds arrows seeds seedModel base)
    {first second : base.Elements} (step : first ⟶ second) (member : code.decode.members.obj first) :
    (code.decode.models second).decode (code.decode.members.map step member) =
      code.decode.native.map step ((code.decode.models first).decode member) :=
  code.decode.memberRestriction_decode step member

theorem collection (source target : Code worlds arrows seeds seedModel base)
    (operation : NaturalHom source.decode.extension target.decode.extension)
    (parameterSquare : operation.comp (ContextualSmallFamilyUniverse.projection target.decode.native) =
      ContextualSmallFamilyUniverse.projection source.decode.native)
    (covered : ContextualCoherentSmallMaps.Cover operation) :
    ContextualCoherentSmallMaps.Cover
        (ContextualCollectionGenerators.parameterMap (ContextualSmallFamilyUniverse.projection target.decode.native) operation) ∧
      ContextualCoherentSmallMaps.Cover
        (ContextualCollectionGenerators.comparison (ContextualSmallFamilyUniverse.projection target.decode.native) operation) ∧
      ContextualImageFactorization.SmallFibres
        (ContextualCollectionGenerators.collectedMap (ContextualSmallFamilyUniverse.projection target.decode.native) operation) ∧
      (ContextualCollectionGenerators.top (ContextualSmallFamilyUniverse.projection target.decode.native) operation).comp
          (operation.comp (ContextualSmallFamilyUniverse.projection target.decode.native)) =
        (ContextualCollectionGenerators.collectedMap (ContextualSmallFamilyUniverse.projection target.decode.native) operation).comp
          (ContextualCollectionGenerators.parameterMap (ContextualSmallFamilyUniverse.projection target.decode.native) operation) :=
  source.decode.collection target.decode operation parameterSquare covered

end Code

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredGeneratedFamilies
