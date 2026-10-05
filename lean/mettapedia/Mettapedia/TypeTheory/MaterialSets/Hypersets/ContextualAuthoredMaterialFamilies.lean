import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReceiptFamilyModels
import Mettapedia.TypeTheory.ContextualOverFamilyCollection
import Mettapedia.TypeTheory.WiderPresheafDependentFunctions

/-!
# Constructive authored material families over wider parameters

A family retains its actual small native functor and constructed material
member dictionary. The parameter is an arbitrary wider presheaf. Dependent
bodies live over genuine comprehension, and its proved flattening supplies
the native signature. All four dependent formers construct their material
decoders. Stable separation and arbitrary parameter substitution retain
both the native maps and the material-member interpretation.

Every authored map over this base has explicitly decoded small fibres.
Every pointwise-surjective cover among these families constructs the full
contextual Collection diagram. This interpreted cover class is narrower
than arbitrary covers between wider ambient objects. The full proposition
filters used in separation are also visible; no metatheoretic witness
selector or unrestricted constructive ambient finality is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialFamilies

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyUniverse ContextualSmallFamilyComprehension

universe u v w
variable {D : Type u} [Category.{u} D]

structure Family (base : D ⥤ Type v) where
  native : base.Elements ⥤ Type u
  models : ContextualReceiptFamilyModels.Model native

namespace Family

variable {base : D ⥤ Type v} (domain : Family base)

instance : Category.{max u v} (Family base) where
  Hom first second := WiderPresheafDependentFunctions.Hom first.native second.native
  id first := WiderPresheafDependentFunctions.Hom.identity first.native
  comp earlier later := earlier.comp later
  id_comp := WiderPresheafDependentFunctions.Hom.identity_comp
  comp_id := WiderPresheafDependentFunctions.Hom.comp_identity
  assoc := WiderPresheafDependentFunctions.Hom.assoc

abbrev extension : D ⥤ Type (max u v) := total domain.native

def bodyNative (body : Family domain.extension) : domain.native.Elements ⥤ Type u :=
  restrict (flatten domain.native) body.native

def bodyModels (body : Family domain.extension) (point : domain.native.Elements) :
    PresentedType ((domain.bodyNative body).obj point) :=
  body.models ((flatten domain.native).obj point)

def sigma (body : Family domain.extension) : Family base where
  native := ContextualSmallFamilyTypeFormers.sigma domain.native (domain.bodyNative body)
  models := ContextualReceiptFamilyModels.sigmaModel domain.native domain.models
    (domain.bodyNative body) (domain.bodyModels body)

def pi (body : Family domain.extension) (worlds : ArgumentCoding D)
    (arrows : (first second : D) → ArgumentCoding (first ⟶ second)) : Family base where
  native := ContextualSmallFamilyTypeFormers.pi domain.native (domain.bodyNative body)
  models := ContextualReceiptFamilyModels.piModel domain.native domain.models
    (domain.bodyNative body) (domain.bodyModels body) worlds arrows

noncomputable def w (body : Family domain.extension) (worlds : ArgumentCoding D)
    (arrows : (first second : D) → ArgumentCoding (first ⟶ second)) : Family base where
  native := ContextualSmallFamilyWTypes.w domain.native (domain.bodyNative body)
  models := ContextualReceiptFamilyModels.wModel domain.native domain.models
    (domain.bodyNative body) (domain.bodyModels body) worlds arrows

def identity (left right : domain.native.sections) : Family base where
  native := ContextualSmallFamilyIdentity.identityFamily domain.native left right
  models := ContextualReceiptFamilyModels.identityModel domain.native left right

def separate (predicate : ContextualReceiptFamilyModels.StablePredicate domain.native) : Family base where
  native := ContextualReceiptFamilyModels.separate domain.native predicate
  models := ContextualReceiptFamilyModels.separateModels domain.native domain.models predicate

def reindex {other : D ⥤ Type w} (change : NaturalHom other base) : Family other where
  native := ContextualSmallFamilyIdentity.reindex domain.native change
  models point := domain.models ((elementMap change).obj point)

abbrev members : base.Elements ⥤ Type (u + 1) :=
  ContextualReceiptFamilyModels.members domain.native domain.models

abbrev sectionDecoder : domain.native.sections ≃ domain.members.sections :=
  ContextualReceiptFamilyModels.sectionEquiv domain.native domain.models

theorem sectionDecoder_value (term : domain.native.sections) (point : base.Elements) :
    ((domain.sectionDecoder term).val point).val = (domain.models point).value (term.val point) :=
  ContextualReceiptFamilyModels.sectionEquiv_value domain.native domain.models term point

/-- An authored native consumer computes its material action through the
two complete dictionaries. The actual context naturality square is proved. -/
def memberHom {target : Family base} (operation : domain ⟶ target) :
    WiderPresheafDependentFunctions.Hom domain.members target.members where
  app point member := (target.models point).decode.symm (operation.app point ((domain.models point).decode member))
  naturality {first second} step member := by
    apply (target.models second).decode.injective
    change (target.models second).decode
        (ContextualReceiptFamilyModels.memberMap target.native target.models step
          ((target.models first).decode.symm (operation.app first ((domain.models first).decode member)))) =
      (target.models second).decode ((target.models second).decode.symm
        (operation.app second ((domain.models second).decode
          (ContextualReceiptFamilyModels.memberMap domain.native domain.models step member))))
    exact (ContextualReceiptFamilyModels.memberMap_decode target.native target.models step
      ((target.models first).decode.symm (operation.app first ((domain.models first).decode member)))).trans
      ((congrArg (target.native.map step) ((target.models first).decode.apply_symm_apply _)).trans
        ((operation.naturality step ((domain.models first).decode member)).trans
          ((congrArg (operation.app second)
            (ContextualReceiptFamilyModels.memberMap_decode domain.native domain.models step member)).symm.trans
              ((target.models second).decode.apply_symm_apply _).symm)))

theorem memberHom_decode {target : Family base} (operation : domain ⟶ target)
    (point : base.Elements) (member : domain.members.obj point) :
    (target.models point).decode ((domain.memberHom operation).app point member) =
      operation.app point ((domain.models point).decode member) :=
  (target.models point).decode.apply_symm_apply _

theorem memberHom_identity : domain.memberHom (𝟙 domain) =
    WiderPresheafDependentFunctions.Hom.identity domain.members := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point member
  exact (domain.models point).decode.symm_apply_apply member

theorem memberHom_comp {middle last : Family base} (earlier : domain ⟶ middle) (later : middle ⟶ last) :
    domain.memberHom (earlier ≫ later) = (domain.memberHom earlier).comp (middle.memberHom later) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point member
  change (last.models point).decode.symm (later.app point (earlier.app point ((domain.models point).decode member))) =
    (last.models point).decode.symm (later.app point ((middle.models point).decode
      ((middle.models point).decode.symm (earlier.app point ((domain.models point).decode member)))))
  rw [Equiv.apply_symm_apply]

theorem memberRestriction_decode {first second : base.Elements} (step : first ⟶ second)
    (member : domain.members.obj first) :
    (domain.models second).decode (domain.members.map step member) =
      domain.native.map step ((domain.models first).decode member) :=
  ContextualReceiptFamilyModels.memberMap_decode domain.native domain.models step member

theorem reindex_memberRestriction {other : D ⥤ Type w} (change : NaturalHom other base)
    {first second : other.Elements} (step : first ⟶ second)
    (member : (domain.reindex change).members.obj first) :
    (domain.reindex change).members.map step member = domain.members.map ((elementMap change).map step) member := rfl

theorem sigma_first (body : Family domain.extension) (point : base.Elements)
    (term : (domain.sigma body).native.obj point) :
    HSet.fst (((domain.sigma body).models point).value term) = (domain.models point).value term.1 :=
  ContextualReceiptFamilyModels.sigma_first domain.native domain.models
    (domain.bodyNative body) (domain.bodyModels body) point term

theorem sigma_second (body : Family domain.extension) (point : base.Elements)
    (term : (domain.sigma body).native.obj point) :
    HSet.snd (((domain.sigma body).models point).value term) =
      (body.models ⟨point.1, ⟨point.2, term.1⟩⟩).value term.2 :=
  ContextualReceiptFamilyModels.sigma_second domain.native domain.models
    (domain.bodyNative body) (domain.bodyModels body) point term

/-- Small map data is derived from the actual over-base equation. It is
not an extra coherence or witness-selection field of an authored family. -/
def mapData (target : Family base)
    (operation : NaturalHom domain.extension target.extension)
    (parameterSquare : operation.comp (projection target.native) = projection domain.native) :
    ContextualCoherentSmallMaps.Data operation :=
  ContextualOverFamilyCollection.data domain.native target.native operation parameterSquare

include domain in
theorem collection (target : Family base)
    (operation : NaturalHom domain.extension target.extension)
    (parameterSquare : operation.comp (projection target.native) = projection domain.native)
    (covered : ContextualCoherentSmallMaps.Cover operation) :
    ContextualCoherentSmallMaps.Cover
        (ContextualCollectionGenerators.parameterMap (projection target.native) operation) ∧
      ContextualCoherentSmallMaps.Cover
        (ContextualCollectionGenerators.comparison (projection target.native) operation) ∧
      ContextualImageFactorization.SmallFibres
        (ContextualCollectionGenerators.collectedMap (projection target.native) operation) ∧
      (ContextualCollectionGenerators.top (projection target.native) operation).comp
          (operation.comp (projection target.native)) =
        (ContextualCollectionGenerators.collectedMap (projection target.native) operation).comp
          (ContextualCollectionGenerators.parameterMap (projection target.native) operation) :=
  ContextualOverFamilyCollection.full_collection domain.native target.native operation parameterSquare covered

/-! ## All-witness material Collection in the interpreted typed model -/

def relationRows (body : Family domain.extension)
    (relation : ContextualReceiptFamilyModels.StablePredicate body.native) : Family base :=
  domain.sigma (body.separate relation)

theorem relationRows_value (body : Family domain.extension)
    (relation : ContextualReceiptFamilyModels.StablePredicate body.native)
    (point : base.Elements) (argument : domain.native.obj point)
    (witness : body.native.obj ⟨point.1, ⟨point.2, argument⟩⟩)
    (related : relation.holds ⟨point.1, ⟨point.2, argument⟩⟩ witness) :
    ((domain.relationRows body relation).models point).value ⟨argument, witness, related⟩ =
      HSet.kpair ((domain.models point).value argument)
        ((body.models ⟨point.1, ⟨point.2, argument⟩⟩).value witness) :=
  PresentedType.sum_value _ _ _

theorem typed_strongCollection (body : Family domain.extension)
    (relation : ContextualReceiptFamilyModels.StablePredicate body.native)
    (total : ∀ point (argument : domain.native.obj point),
      ∃ witness : body.native.obj ⟨point.1, ⟨point.2, argument⟩⟩,
        relation.holds ⟨point.1, ⟨point.2, argument⟩⟩ witness)
    (point : base.Elements) :
    (∀ argument : domain.native.obj point,
      ∃ witness : body.native.obj ⟨point.1, ⟨point.2, argument⟩⟩,
        relation.holds ⟨point.1, ⟨point.2, argument⟩⟩ witness ∧
          HSet.kpair ((domain.models point).value argument)
            ((body.models ⟨point.1, ⟨point.2, argument⟩⟩).value witness) ∈
              ((domain.relationRows body relation).models point).carrier) ∧
      (∀ row, row ∈ ((domain.relationRows body relation).models point).carrier →
        ∃ argument : domain.native.obj point,
        ∃ witness : body.native.obj ⟨point.1, ⟨point.2, argument⟩⟩,
          relation.holds ⟨point.1, ⟨point.2, argument⟩⟩ witness ∧
            HSet.kpair ((domain.models point).value argument)
              ((body.models ⟨point.1, ⟨point.2, argument⟩⟩).value witness) = row) := by
  constructor
  · intro argument
    obtain ⟨witness, related⟩ := total point argument
    refine ⟨witness, related, ?_⟩
    rw [← domain.relationRows_value body relation point argument witness related]
    exact ((domain.relationRows body relation).models point).value_mem _
  · intro row member
    let receipt := ((domain.relationRows body relation).models point).decode ⟨row, member⟩
    exact ⟨receipt.1, receipt.2.val, receipt.2.property,
      (domain.relationRows_value body relation point receipt.1 receipt.2.val receipt.2.property).symm.trans
        (((domain.relationRows body relation).models point).value_decode ⟨row, member⟩)⟩

end Family

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualAuthoredMaterialFamilies
