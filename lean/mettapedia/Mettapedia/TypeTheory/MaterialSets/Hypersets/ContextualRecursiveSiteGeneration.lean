import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSiteEquivalence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialWEquivalence

/-!
# Recursive generated formation on the successor site

Each lower derivation is rebuilt from raised primitive seeds and the
actual upper contextual constructors. The recursive result retains its
upper derivation and a natural material equivalence to the lifted lower
interpretation. Dependent bodies move through the constructed inverse
comprehension square, retaining their actual fibre dictionaries.

Primitive upper seeds are pullbacks of declared lower primitive seeds.
Interpreted lower compound codes are not added as primitive seeds. The
comparison concerns semantic families and their complete material values;
it does not identify distinct formation recipes or all upper families.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRecursiveSiteGeneration

open CategoryTheory ContextualGeneratedUniverse ContextualMaterialEquivalence
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent (compose identity)

universe u
variable {C : Type u} [Category.{u} C]
variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

structure PrimitiveSeed (declared : LabelledContext (PresheafSiteLift.Site C)) : Type (u + 2) where
  lower : LabelledContext C
  label : seeds lower
  change : NatTrans declared.base (ContextualSiteLiftMaterial.context lower).base

def primitiveModel (declared : LabelledContext (PresheafSiteLift.Site C))
    (seed : PrimitiveSeed seeds declared) : MaterialFamily declared :=
  (ContextualSiteLiftMaterial.family (seedModel seed.lower seed.label)).reindex seed.change

abbrev UpperGeneration {declared : LabelledContext (PresheafSiteLift.Site C)} (family : MaterialFamily declared) :=
  Generation (PrimitiveSeed seeds) (primitiveModel seeds seedModel) (ContextualSiteLiftMaterial.arrows arrows) family

structure Translation {context : LabelledContext C} (family : MaterialFamily context) where
  result : MaterialFamily (ContextualSiteLiftMaterial.context context)
  derivation : UpperGeneration seeds seedModel arrows result
  comparison : Equivalence result (ContextualSiteLiftMaterial.family family)

namespace Translation

variable {seeds seedModel arrows}

def seed (context : LabelledContext C) (label : seeds context) :
    Translation seeds seedModel arrows (seedModel context label) where
  result := primitiveModel seeds seedModel (ContextualSiteLiftMaterial.context context)
    ⟨context, label, identity (ContextualSiteLiftMaterial.context context).base⟩
  derivation := .seed _
    (⟨context, label, identity (ContextualSiteLiftMaterial.context context).base⟩ :
      PrimitiveSeed seeds (ContextualSiteLiftMaterial.context context))
  comparison := ofEquality (ContextualUniverseCodes.MaterialFamily.reindex_identity
    (ContextualSiteLiftMaterial.family (seedModel context label)))

def empty (context : LabelledContext C) : Translation seeds seedModel arrows (MaterialFamily.empty context) where
  result := MaterialFamily.empty (ContextualSiteLiftMaterial.context context)
  derivation := .empty _
  comparison := ContextualMaterialSiteEquivalence.empty context

def unit (context : LabelledContext C) : Translation seeds seedModel arrows (MaterialFamily.unit context) where
  result := MaterialFamily.unit (ContextualSiteLiftMaterial.context context)
  derivation := .unit _
  comparison := ContextualMaterialSiteEquivalence.unit context

variable {context : LabelledContext C} {domain : MaterialFamily context}
variable {body : MaterialFamily domain.extension}

def bodyChange (first : Translation seeds seedModel arrows domain) :
    NatTrans first.result.extension.base (ContextualSiteLiftMaterial.context domain.extension).base :=
  compose first.comparison.comprehension (PresheafSiteLift.comprehensionFrom context.base domain.family)

def bodyResult (first : Translation seeds seedModel arrows domain) (second : Translation seeds seedModel arrows body) :
    MaterialFamily first.result.extension := second.result.reindex (bodyChange first)

def bodyComparison (first : Translation seeds seedModel arrows domain) (second : Translation seeds seedModel arrows body) :
    Equivalence (bodyResult first second)
      ((ContextualSiteLiftMaterial.body domain body).reindex (other := first.result.extension) first.comparison.comprehension) :=
  (second.comparison.reindex (bodyChange first)).trans
    (ofEquality (ContextualUniverseCodes.MaterialFamily.reindex_comp (ContextualSiteLiftMaterial.family body)
      first.comparison.comprehension (PresheafSiteLift.comprehensionFrom context.base domain.family)).symm)

def pi (first : Translation seeds seedModel arrows domain) (second : Translation seeds seedModel arrows body) :
    Translation seeds seedModel arrows (domain.pi body arrows) where
  result := first.result.pi (bodyResult first second) (ContextualSiteLiftMaterial.arrows arrows)
  derivation := .pi first.derivation (.reindex second.derivation (bodyChange first))
  comparison := (ContextualMaterialTypeFormerEquivalence.pi first.comparison (bodyComparison first second)
    (ContextualSiteLiftMaterial.arrows arrows)).trans (ContextualMaterialSiteEquivalence.pi domain body arrows)

def sigma (first : Translation seeds seedModel arrows domain) (second : Translation seeds seedModel arrows body) :
    Translation seeds seedModel arrows (domain.sigma body) where
  result := first.result.sigma (bodyResult first second)
  derivation := .sigma first.derivation (.reindex second.derivation (bodyChange first))
  comparison := (ContextualMaterialTypeFormerEquivalence.sigma first.comparison (bodyComparison first second)).trans
    (ContextualMaterialSiteEquivalence.sigma domain body)

noncomputable def w (first : Translation seeds seedModel arrows domain) (second : Translation seeds seedModel arrows body) :
    Translation seeds seedModel arrows (domain.w body arrows) where
  result := first.result.w (bodyResult first second) (ContextualSiteLiftMaterial.arrows arrows)
  derivation := .w first.derivation (.reindex second.derivation (bodyChange first))
  comparison := (ContextualMaterialWEquivalence.w first.comparison (bodyComparison first second)
    (ContextualSiteLiftMaterial.arrows arrows)).trans (ContextualMaterialSiteEquivalence.w domain body arrows)

def reindex {other : LabelledContext C} (first : Translation seeds seedModel arrows domain)
    (change : NatTrans other.base context.base) : Translation seeds seedModel arrows (domain.reindex change) where
  result := first.result.reindex (other := ContextualSiteLiftMaterial.context other) (PresheafSiteLift.raiseChange change)
  derivation := .reindex (other := ContextualSiteLiftMaterial.context other)
    first.derivation (PresheafSiteLift.raiseChange change)
  comparison := (first.comparison.reindex (other := ContextualSiteLiftMaterial.context other)
    (PresheafSiteLift.raiseChange change)).trans
      (ContextualMaterialSiteEquivalence.reindex (other := other) domain change)

def identity (first : Translation seeds seedModel arrows domain) (left right : domain.family.sections) :
    Translation seeds seedModel arrows (domain.identity left right) := by
  let lowerLeft := PresheafSiteLift.raiseTerm context.base domain.family left
  let lowerRight := PresheafSiteLift.raiseTerm context.base domain.family right
  let upperLeft := first.comparison.sections.symm lowerLeft
  let upperRight := first.comparison.sections.symm lowerRight
  exact {
    result := first.result.identity upperLeft upperRight
    derivation := .identity first.derivation upperLeft upperRight
    comparison := (ContextualMaterialTypeFormerEquivalence.identity first.comparison upperLeft upperRight).trans
      ((ofEquality (congrArg₂ (ContextualSiteLiftMaterial.family domain).identity
        (first.comparison.sections.apply_symm_apply lowerLeft) (first.comparison.sections.apply_symm_apply lowerRight))).trans
          (ContextualMaterialSiteEquivalence.identity domain left right)) }

def piUnder {other : LabelledContext C}
    (first : Translation seeds seedModel arrows domain) (second : Translation seeds seedModel arrows body)
    (change : NatTrans other.base context.base) : Translation seeds seedModel arrows (domain.piUnder body arrows change) :=
  let rebuilt := (pi first second).reindex change
  { result := rebuilt.result
    derivation := rebuilt.derivation
    comparison := rebuilt.comparison.trans
      (ContextualMaterialSiteEquivalence.liftEquivalence (ContextualMaterialSiteEquivalence.piUnder domain body arrows change)) }

def sigmaUnder {other : LabelledContext C}
    (first : Translation seeds seedModel arrows domain) (second : Translation seeds seedModel arrows body)
    (change : NatTrans other.base context.base) : Translation seeds seedModel arrows (domain.sigmaUnder body change) :=
  let rebuilt := (sigma first second).reindex change
  { result := rebuilt.result
    derivation := rebuilt.derivation
    comparison := rebuilt.comparison.trans
      (ContextualMaterialSiteEquivalence.liftEquivalence (ContextualMaterialSiteEquivalence.sigmaUnder domain body change)) }

end Translation

noncomputable def translate {context : LabelledContext C} {family : MaterialFamily context}
    (derivation : Generation seeds seedModel arrows family) : Translation seeds seedModel arrows family :=
  match derivation with
  | .seed context label => Translation.seed context label
  | .empty context => Translation.empty context
  | .unit context => Translation.unit context
  | .pi first second => Translation.pi (translate first) (translate second)
  | .sigma first second => Translation.sigma (translate first) (translate second)
  | .w first second => Translation.w (translate first) (translate second)
  | .identity first left right => Translation.identity (translate first) left right
  | .reindex first change => (translate first).reindex change
  | .piUnder first second change => Translation.piUnder (translate first) (translate second) change
  | .sigmaUnder first second change => Translation.sigmaUnder (translate first) (translate second) change

variable {context : LabelledContext C} {family : MaterialFamily context}
variable (derivation : Generation seeds seedModel arrows family)

private def lowerLift {T : Type u} : ULift.{u + 1, u} T ≃ T where
  toFun := ULift.down
  invFun := ULift.up
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def semantic (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    (translate seeds seedModel arrows derivation).result.family.obj point ≃
      family.family.obj ((PresheafSiteLift.elementsDown context.base).obj point) :=
  ((translate seeds seedModel arrows derivation).comparison.fibre point).trans lowerLift

theorem value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (term : (translate seeds seedModel arrows derivation).result.family.obj point) :
    ((translate seeds seedModel arrows derivation).result.model point).value term =
      HSet.lift ((family.model ((PresheafSiteLift.elementsDown context.base).obj point)).value
        (semantic seeds seedModel arrows derivation point term)) :=
  ((translate seeds seedModel arrows derivation).comparison.value point term).symm

theorem semantic_natural {point next : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : point ⟶ next) (term : (translate seeds seedModel arrows derivation).result.family.obj point) :
    semantic seeds seedModel arrows derivation next
      ((translate seeds seedModel arrows derivation).result.family.map step term) =
      family.family.map ((PresheafSiteLift.elementsDown context.base).map step)
        (semantic seeds seedModel arrows derivation point term) :=
  congrArg ULift.down ((translate seeds seedModel arrows derivation).comparison.naturality step term)

theorem carrier (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    ((translate seeds seedModel arrows derivation).result.model point).carrier =
      HSet.lift ((family.model ((PresheafSiteLift.elementsDown context.base).obj point)).carrier) :=
  ((translate seeds seedModel arrows derivation).comparison.carrier point).trans
    (ContextualSiteLiftMaterial.carrier family point)

noncomputable def memberComparison (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    {value : HSet.{u + 1} // value ∈ ((translate seeds seedModel arrows derivation).result.model point).carrier} ≃
      {value : HSet.{u} // value ∈ (family.model ((PresheafSiteLift.elementsDown context.base).obj point)).carrier} :=
  PresentedTypeCumulativity.memberEquiv (family.model ((PresheafSiteLift.elementsDown context.base).obj point))
    ((translate seeds seedModel arrows derivation).result.model point) (semantic seeds seedModel arrows derivation point)

theorem member_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((translate seeds seedModel arrows derivation).result.model point).carrier}) :
    HSet.lift (memberComparison seeds seedModel arrows derivation point member).val = member.val :=
  PresentedTypeCumulativity.memberEquiv_value _ _ _ (value seeds seedModel arrows derivation point) member

theorem decoder (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((translate seeds seedModel arrows derivation).result.model point).carrier}) :
    (family.model ((PresheafSiteLift.elementsDown context.base).obj point)).decode
      (memberComparison seeds seedModel arrows derivation point member) =
    semantic seeds seedModel arrows derivation point
      (((translate seeds seedModel arrows derivation).result.model point).decode member) :=
  PresentedTypeCumulativity.decode_memberEquiv _ _ _ member

theorem member_natural {point next : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : point ⟶ next)
    (member : {value : HSet.{u + 1} // value ∈ ((translate seeds seedModel arrows derivation).result.model point).carrier}) :
    memberComparison seeds seedModel arrows derivation next
      ((translate seeds seedModel arrows derivation).result.memberRestriction step member) =
      family.memberRestriction ((PresheafSiteLift.elementsDown context.base).map step)
        (memberComparison seeds seedModel arrows derivation point member) := by
  apply (family.model ((PresheafSiteLift.elementsDown context.base).obj next)).decode.injective
  rw [decoder, MaterialFamily.memberRestriction_decode, MaterialFamily.memberRestriction_decode, decoder]
  exact semantic_natural seeds seedModel arrows derivation step _

noncomputable def sectionComparison :
    (translate seeds seedModel arrows derivation).result.family.sections ≃ family.family.sections :=
  (translate seeds seedModel arrows derivation).comparison.sections.trans
    (PresheafSiteLift.termEquiv context.base family.family).symm

theorem section_value (term : (translate seeds seedModel arrows derivation).result.family.sections)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    ((translate seeds seedModel arrows derivation).result.model point).value (term.val point) =
      HSet.lift ((family.model ((PresheafSiteLift.elementsDown context.base).obj point)).value
        ((sectionComparison seeds seedModel arrows derivation term).val
          ((PresheafSiteLift.elementsDown context.base).obj point))) :=
  value seeds seedModel arrows derivation point (term.val point)

theorem generated_enclosed (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    HSet.lift ((translate seeds seedModel arrows derivation).result.model point).carrier ∈
      enclosure (PrimitiveSeed seeds) (primitiveModel seeds seedModel) (ContextualSiteLiftMaterial.arrows arrows)
        (ContextualSiteLiftMaterial.context context) point :=
  generated_mem_enclosure (PrimitiveSeed seeds) (primitiveModel seeds seedModel) (ContextualSiteLiftMaterial.arrows arrows)
    (translate seeds seedModel arrows derivation).derivation point

/-- The external carrier enclosure is cumulative for the recursively
translated grammar, with both material universe shifts visible. -/
theorem enclosure_embedding (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : HSet.{u + 1})
    (belongs : member ∈ enclosure seeds seedModel arrows context ((PresheafSiteLift.elementsDown context.base).obj point)) :
    HSet.lift member ∈
      enclosure (PrimitiveSeed seeds) (primitiveModel seeds seedModel) (ContextualSiteLiftMaterial.arrows arrows)
        (ContextualSiteLiftMaterial.context context) point := by
  obtain ⟨code, represented⟩ := (mem_enclosure_iff seeds seedModel arrows).mp belongs
  have translated := generated_enclosed seeds seedModel arrows code.2 point
  have equality := (congrArg HSet.lift (carrier seeds seedModel arrows code.2 point)).trans
    (congrArg HSet.lift represented)
  exact Eq.mp (congrArg (fun value : HSet.{u + 2} => value ∈
    enclosure (PrimitiveSeed seeds) (primitiveModel seeds seedModel) (ContextualSiteLiftMaterial.arrows arrows)
      (ContextualSiteLiftMaterial.context context) point) equality) translated

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualRecursiveSiteGeneration
