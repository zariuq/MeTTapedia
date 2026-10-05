import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualDoubleSuccessorUniverse
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverseComparisons
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSiteEquivalence

/-!
# Independent formation across two cumulative successors

Both upper stages independently form the full contextual products, sums,
identities and hereditary-natural W-types. Their comparisons compose
actual fibre equivalences, dependent comprehension transport, material
dictionaries and restriction maps. Complete future positions and parallel
arrows are retained by the two underlying site comparisons.

The resulting semantic and material comparisons do not identify the
independent constructor recipe with a cumulative seed. The literal
material value laws use deliberately transported labels.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualDoubleSuccessorComparisons

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory
open ContextualMaterialEquivalence
open ContextualDoubleSuccessorUniverse
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable {context : LabelledContext C}

/-- The member comparison is constructed from the two actual decoders,
not from a chosen representative of a material member. -/
def materialMembers {first second : MaterialFamily context} (equivalence : Equivalence first second)
    (point : context.base.Elements) :
    {value : HSet.{u} // value ∈ (first.model point).carrier} ≃
      {value : HSet.{u} // value ∈ (second.model point).carrier} :=
  (first.model point).decode.trans ((equivalence.fibre point).trans (second.model point).decode.symm)

theorem materialMembers_decode {first second : MaterialFamily context} (equivalence : Equivalence first second)
    (point : context.base.Elements) (member : {value : HSet.{u} // value ∈ (first.model point).carrier}) :
    (second.model point).decode (materialMembers equivalence point member) =
      equivalence.fibre point ((first.model point).decode member) :=
  (second.model point).decode.apply_symm_apply _

theorem materialMembers_value {first second : MaterialFamily context} (equivalence : Equivalence first second)
    (point : context.base.Elements) (member : {value : HSet.{u} // value ∈ (first.model point).carrier}) :
    (materialMembers equivalence point member).val = member.val :=
  (equivalence.value point ((first.model point).decode member)).trans ((first.model point).value_decode member)

theorem materialMembers_restriction {first second : MaterialFamily context}
    (equivalence : Equivalence first second) {point next : context.base.Elements} (step : point ⟶ next)
    (member : {value : HSet.{u} // value ∈ (first.model point).carrier}) :
    materialMembers equivalence next (first.memberRestriction step member) =
      second.memberRestriction step (materialMembers equivalence point member) := by
  apply (second.model next).decode.injective
  rw [materialMembers_decode, MaterialFamily.memberRestriction_decode,
    MaterialFamily.memberRestriction_decode, materialMembers_decode]
  exact equivalence.naturality step ((first.model point).decode member)

variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev Kind := ContextualSuccessorUniverseComparisons.Kind

variable (kind : Kind)
variable (domain : LowerCode seeds seedModel arrows context)
variable (body : LowerCode seeds seedModel arrows (lowerFamily seeds seedModel arrows domain).extension)

abbrev lowerFormer := ContextualSuccessorUniverseComparisons.lowerFormer seeds seedModel arrows kind domain body
abbrev firstFormer := ContextualSuccessorUniverseComparisons.rebuild seeds seedModel arrows kind domain body

def independentBody : Code seeds seedModel arrows (twiceFamily (lowerFamily seeds seedModel arrows domain)).extension :=
  ContextualSuccessorUniverse.liftBody (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) (liftFirst seeds seedModel arrows domain)
    (ContextualSuccessorUniverse.liftBody seeds seedModel arrows domain body)

theorem decode_independentBody :
    decode seeds seedModel arrows (independentBody seeds seedModel arrows domain body) =
      twiceBody (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body) :=
  ContextualSuccessorUniverse.decode_liftBody _ _ _ _ _

/-- The second body is reindexed through a second actual comprehension
square. In particular it is not the direct lift of the old body context. -/
def independentFormer : Code seeds seedModel arrows (twiceContext context) :=
  ContextualSuccessorUniverseComparisons.rebuild (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) kind
    (liftFirst seeds seedModel arrows domain)
    (ContextualSuccessorUniverse.liftBody seeds seedModel arrows domain body)

theorem decode_independentFormer :
    decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body) =
      ContextualClosedUniverseCodes.materialBinary (secondArrows arrows) kind
        (twiceFamily (lowerFamily seeds seedModel arrows domain))
        (twiceBody (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body)) :=
  ContextualClosedUniverseCodes.decode_binary (secondSeeds seeds seedModel arrows)
    (secondModels seeds seedModel arrows) (secondArrows arrows) kind
    (liftTwice seeds seedModel arrows domain) (independentBody seeds seedModel arrows domain body)

noncomputable def firstEquivalence :
    Equivalence (firstFamily seeds seedModel arrows (firstFormer seeds seedModel arrows kind domain body))
      (firstFamily seeds seedModel arrows (liftFirst seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))) where
  fibre point := (ContextualSuccessorUniverseComparisons.semantic seeds seedModel arrows kind domain body point).trans Equiv.ulift.symm
  naturality step term := congrArg ULift.up
    (ContextualSuccessorUniverseComparisons.semantic_restriction seeds seedModel arrows kind domain body step term)
  value point term := (ContextualSuccessorUniverseComparisons.semantic_value seeds seedModel arrows kind domain body point term).symm

noncomputable def nextEquivalence :
    Equivalence (decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body))
      (decode seeds seedModel arrows (liftNext seeds seedModel arrows (firstFormer seeds seedModel arrows kind domain body))) :=
  firstEquivalence (firstSeeds seeds seedModel arrows) (firstModels seeds seedModel arrows) (firstArrows arrows)
    kind (liftFirst seeds seedModel arrows domain) (ContextualSuccessorUniverse.liftBody seeds seedModel arrows domain body)

noncomputable def equivalence :
    Equivalence (decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body))
      (decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))) :=
  (nextEquivalence seeds seedModel arrows kind domain body).trans
    (ContextualMaterialSiteEquivalence.liftEquivalence (firstEquivalence seeds seedModel arrows kind domain body))

noncomputable def semantic (point : (twiceContext context).base.Elements) :
    (decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).family.obj point ≃
      (lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).family.obj (lowerPoint context point) :=
  ((equivalence seeds seedModel arrows kind domain body).fibre point).trans
    (ContextualDoubleSuccessorUniverse.semantic seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body) point)

theorem semantic_value (point : (twiceContext context).base.Elements)
    (term : (decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).family.obj point) :
    ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).value term =
      HSet.lift (HSet.lift (((lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).model
        (lowerPoint context point)).value (semantic seeds seedModel arrows kind domain body point term))) :=
  ((equivalence seeds seedModel arrows kind domain body).value point term).symm.trans
    (ContextualDoubleSuccessorUniverse.semantic_value seeds seedModel arrows _ point _)

theorem semantic_restriction {point next : (twiceContext context).base.Elements} (step : point ⟶ next)
    (term : (decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).family.obj point) :
    semantic seeds seedModel arrows kind domain body next
        ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).family.map step term) =
      (lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).family.map (lowerArrow step)
        (semantic seeds seedModel arrows kind domain body point term) :=
  congrArg (ContextualDoubleSuccessorUniverse.semantic seeds seedModel arrows _ next)
    ((equivalence seeds seedModel arrows kind domain body).naturality step term)

theorem carrier_equality (point : (twiceContext context).base.Elements) :
    ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).carrier =
      ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))).model point).carrier :=
  (equivalence seeds seedModel arrows kind domain body).carrier point

noncomputable def memberComparison (point : (twiceContext context).base.Elements) :=
  materialMembers (equivalence seeds seedModel arrows kind domain body) point

theorem memberComparison_value (point : (twiceContext context).base.Elements)
    (member : {value : HSet.{u + 2} // value ∈
      ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).carrier}) :
    (memberComparison seeds seedModel arrows kind domain body point member).val = member.val :=
  materialMembers_value (equivalence seeds seedModel arrows kind domain body) point member

theorem memberComparison_decode (point : (twiceContext context).base.Elements)
    (member : {value : HSet.{u + 2} // value ∈
      ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).carrier}) :
    ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))).model point).decode
        (memberComparison seeds seedModel arrows kind domain body point member) =
      (equivalence seeds seedModel arrows kind domain body).fibre point
        (((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).decode member) :=
  materialMembers_decode (equivalence seeds seedModel arrows kind domain body) point member

theorem memberComparison_restriction {point next : (twiceContext context).base.Elements} (step : point ⟶ next)
    (member : {value : HSet.{u + 2} // value ∈
      ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).carrier}) :
    memberComparison seeds seedModel arrows kind domain body next
        ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).memberRestriction step member) =
      (decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))).memberRestriction step
        (memberComparison seeds seedModel arrows kind domain body point member) :=
  materialMembers_restriction (equivalence seeds seedModel arrows kind domain body) step member

noncomputable def sectionComparison := (equivalence seeds seedModel arrows kind domain body).sections

theorem sectionComparison_value
    (term : (decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).family.sections)
    (point : (twiceContext context).base.Elements) :
    ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))).model point).value
        ((sectionComparison seeds seedModel arrows kind domain body term).val point) =
      ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).value (term.val point) :=
  (equivalence seeds seedModel arrows kind domain body).sections_value term point

noncomputable def lowerSectionComparison :=
  (sectionComparison seeds seedModel arrows kind domain body).trans
    (ContextualDoubleSuccessorUniverse.sectionEquiv seeds seedModel arrows
      (lowerFormer seeds seedModel arrows kind domain body)).symm

theorem lowerSectionComparison_value
    (term : (decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).family.sections)
    (point : (twiceContext context).base.Elements) :
    ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).value (term.val point) =
      HSet.lift (HSet.lift (((lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).model
        (lowerPoint context point)).value
          ((lowerSectionComparison seeds seedModel arrows kind domain body term).val (lowerPoint context point)))) := by
  have preserved := ContextualDoubleSuccessorUniverse.section_value seeds seedModel arrows
    (lowerFormer seeds seedModel arrows kind domain body)
    (lowerSectionComparison seeds seedModel arrows kind domain body term) point
  have roundtrip := (ContextualDoubleSuccessorUniverse.sectionEquiv seeds seedModel arrows
    (lowerFormer seeds seedModel arrows kind domain body)).apply_symm_apply
      (sectionComparison seeds seedModel arrows kind domain body term)
  change ContextualDoubleSuccessorUniverse.sectionEquiv seeds seedModel arrows
    (lowerFormer seeds seedModel arrows kind domain body) (lowerSectionComparison seeds seedModel arrows kind domain body term) =
      sectionComparison seeds seedModel arrows kind domain body term at roundtrip
  rw [roundtrip] at preserved
  exact (sectionComparison_value seeds seedModel arrows kind domain body term point).symm.trans preserved

noncomputable def reindexedEquivalence {other : LabelledContext (SecondSite (C := C))}
    (change : NatTrans other.base (twiceContext context).base) :
    Equivalence
      (decode seeds seedModel arrows (ContextualDoubleSuccessorUniverse.reindex seeds seedModel arrows change (independentFormer seeds seedModel arrows kind domain body)))
      (decode seeds seedModel arrows (ContextualDoubleSuccessorUniverse.reindex seeds seedModel arrows change
        (liftTwice seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)))) :=
  (ofEquality (ContextualDoubleSuccessorUniverse.decode_reindex seeds seedModel arrows change _)).trans
    (((equivalence seeds seedModel arrows kind domain body).reindex change).trans
      (ofEquality (ContextualDoubleSuccessorUniverse.decode_reindex seeds seedModel arrows change _).symm))

/-- Under an authored lower substitution, the independently formed upper
family compares to the actual lift of the substituted lower code. The
equation concerns decoding, not cumulative seed provenance. -/
noncomputable def substitutionEquivalence {other : LabelledContext C}
    (change : NatTrans other.base context.base) :
    Equivalence
      (decode seeds seedModel arrows (ContextualDoubleSuccessorUniverse.reindex seeds seedModel arrows (other := twiceContext other)
        (raiseChange change) (independentFormer seeds seedModel arrows kind domain body)))
      (decode seeds seedModel arrows (liftTwice seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change
          (lowerFormer seeds seedModel arrows kind domain body)))) :=
  (reindexedEquivalence seeds seedModel arrows kind domain body (raiseChange change)).trans
    (ofEquality (decode_liftTwice_reindex seeds seedModel arrows change
      (lowerFormer seeds seedModel arrows kind domain body)).symm)

theorem independent_not_next_lift (previous : FirstCode seeds seedModel arrows (firstContext context)) :
    independentFormer seeds seedModel arrows kind domain body ≠ liftNext seeds seedModel arrows previous :=
  ContextualSuccessorUniverseComparisons.rebuild_not_lift (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) kind
    (liftFirst seeds seedModel arrows domain) (ContextualSuccessorUniverse.liftBody seeds seedModel arrows domain body) previous

theorem independent_not_twice_lift (previous : LowerCode seeds seedModel arrows context) :
    independentFormer seeds seedModel arrows kind domain body ≠ liftTwice seeds seedModel arrows previous :=
  independent_not_next_lift seeds seedModel arrows kind domain body (liftFirst seeds seedModel arrows previous)

theorem independent_enclosed (point : (twiceContext context).base.Elements) :
    HSet.lift ((decode seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body)).model point).carrier ∈
      enclosure seeds seedModel arrows (twiceContext context) point :=
  code_enclosed seeds seedModel arrows (independentFormer seeds seedModel arrows kind domain body) point

namespace Identity

variable (left right : (lowerFamily seeds seedModel arrows domain).family.sections)

abbrev lowerCode := ContextualSuccessorUniverseComparisons.Identity.lowerCode seeds seedModel arrows domain left right
abbrev firstCode := ContextualSuccessorUniverseComparisons.Identity.rebuild seeds seedModel arrows domain left right

def independentCode : Code seeds seedModel arrows (twiceContext context) :=
  ContextualSuccessorUniverseComparisons.Identity.rebuild (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) (liftFirst seeds seedModel arrows domain)
    (ContextualSuccessorUniverse.sectionEquiv seeds seedModel arrows domain left)
    (ContextualSuccessorUniverse.sectionEquiv seeds seedModel arrows domain right)

theorem decode_independentCode :
    decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right) =
      (twiceFamily (lowerFamily seeds seedModel arrows domain)).identity
        (ContextualDoubleSuccessorUniverse.sectionEquiv seeds seedModel arrows domain left)
        (ContextualDoubleSuccessorUniverse.sectionEquiv seeds seedModel arrows domain right) :=
  ContextualSuccessorUniverse.decode_identity (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) (liftTwice seeds seedModel arrows domain)
    (ContextualDoubleSuccessorUniverse.sectionEquiv seeds seedModel arrows domain left)
    (ContextualDoubleSuccessorUniverse.sectionEquiv seeds seedModel arrows domain right)

def firstEquivalence :
    Equivalence (firstFamily seeds seedModel arrows (firstCode seeds seedModel arrows domain left right))
      (firstFamily seeds seedModel arrows (liftFirst seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right))) where
  fibre point := (ContextualSuccessorUniverseComparisons.Identity.semantic seeds seedModel arrows domain left right point).trans Equiv.ulift.symm
  naturality step term := congrArg ULift.up
    (ContextualSuccessorUniverseComparisons.Identity.semantic_restriction seeds seedModel arrows domain left right step term)
  value point term := (ContextualSuccessorUniverseComparisons.Identity.semantic_value seeds seedModel arrows domain left right point term).symm

def nextEquivalence :
    Equivalence (decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right))
      (decode seeds seedModel arrows (liftNext seeds seedModel arrows (firstCode seeds seedModel arrows domain left right))) :=
  firstEquivalence (firstSeeds seeds seedModel arrows) (firstModels seeds seedModel arrows) (firstArrows arrows)
    (liftFirst seeds seedModel arrows domain)
    (ContextualSuccessorUniverse.sectionEquiv seeds seedModel arrows domain left)
    (ContextualSuccessorUniverse.sectionEquiv seeds seedModel arrows domain right)

def equivalence :
    Equivalence (decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right))
      (decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right))) :=
  (nextEquivalence seeds seedModel arrows domain left right).trans
    (ContextualMaterialSiteEquivalence.liftEquivalence (firstEquivalence seeds seedModel arrows domain left right))

theorem carrier_equality (point : (twiceContext context).base.Elements) :
    ((decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).model point).carrier =
      ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right))).model point).carrier :=
  (equivalence seeds seedModel arrows domain left right).carrier point

def memberComparison (point : (twiceContext context).base.Elements) :=
  materialMembers (equivalence seeds seedModel arrows domain left right) point

theorem memberComparison_value (point : (twiceContext context).base.Elements)
    (member : {value : HSet.{u + 2} // value ∈
      ((decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).model point).carrier}) :
    (memberComparison seeds seedModel arrows domain left right point member).val = member.val :=
  materialMembers_value (equivalence seeds seedModel arrows domain left right) point member

theorem memberComparison_decode (point : (twiceContext context).base.Elements)
    (member : {value : HSet.{u + 2} // value ∈
      ((decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).model point).carrier}) :
    ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right))).model point).decode
        (memberComparison seeds seedModel arrows domain left right point member) =
      (equivalence seeds seedModel arrows domain left right).fibre point
        (((decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).model point).decode member) :=
  materialMembers_decode (equivalence seeds seedModel arrows domain left right) point member

theorem memberComparison_restriction {point next : (twiceContext context).base.Elements} (step : point ⟶ next)
    (member : {value : HSet.{u + 2} // value ∈
      ((decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).model point).carrier}) :
    memberComparison seeds seedModel arrows domain left right next
        ((decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).memberRestriction step member) =
      (decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right))).memberRestriction step
        (memberComparison seeds seedModel arrows domain left right point member) :=
  materialMembers_restriction (equivalence seeds seedModel arrows domain left right) step member

def sectionComparison := (equivalence seeds seedModel arrows domain left right).sections

theorem sectionComparison_value
    (term : (decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).family.sections)
    (point : (twiceContext context).base.Elements) :
    ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right))).model point).value
        ((sectionComparison seeds seedModel arrows domain left right term).val point) =
      ((decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).model point).value (term.val point) :=
  (equivalence seeds seedModel arrows domain left right).sections_value term point

def reindexedEquivalence {other : LabelledContext (SecondSite (C := C))}
    (change : NatTrans other.base (twiceContext context).base) :
    Equivalence
      (decode seeds seedModel arrows (ContextualDoubleSuccessorUniverse.reindex seeds seedModel arrows change (independentCode seeds seedModel arrows domain left right)))
      (decode seeds seedModel arrows (ContextualDoubleSuccessorUniverse.reindex seeds seedModel arrows change
        (liftTwice seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right)))) :=
  (ofEquality (ContextualDoubleSuccessorUniverse.decode_reindex seeds seedModel arrows change _)).trans
    (((equivalence seeds seedModel arrows domain left right).reindex change).trans
      (ofEquality (ContextualDoubleSuccessorUniverse.decode_reindex seeds seedModel arrows change _).symm))

def substitutionEquivalence {other : LabelledContext C} (change : NatTrans other.base context.base) :
    Equivalence
      (decode seeds seedModel arrows (ContextualDoubleSuccessorUniverse.reindex seeds seedModel arrows (other := twiceContext other)
        (raiseChange change) (independentCode seeds seedModel arrows domain left right)))
      (decode seeds seedModel arrows (liftTwice seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change
          (lowerCode seeds seedModel arrows domain left right)))) :=
  (reindexedEquivalence seeds seedModel arrows domain left right (raiseChange change)).trans
    (ofEquality (decode_liftTwice_reindex seeds seedModel arrows change
      (lowerCode seeds seedModel arrows domain left right)).symm)

theorem independent_not_next_lift (previous : FirstCode seeds seedModel arrows (firstContext context)) :
    independentCode seeds seedModel arrows domain left right ≠ liftNext seeds seedModel arrows previous :=
  ContextualSuccessorUniverseComparisons.Identity.rebuild_not_lift (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) (liftFirst seeds seedModel arrows domain)
    (ContextualSuccessorUniverse.sectionEquiv seeds seedModel arrows domain left)
    (ContextualSuccessorUniverse.sectionEquiv seeds seedModel arrows domain right) previous

theorem independent_enclosed (point : (twiceContext context).base.Elements) :
    HSet.lift ((decode seeds seedModel arrows (independentCode seeds seedModel arrows domain left right)).model point).carrier ∈
      enclosure seeds seedModel arrows (twiceContext context) point :=
  code_enclosed seeds seedModel arrows (independentCode seeds seedModel arrows domain left right) point

end Identity

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualDoubleSuccessorComparisons
