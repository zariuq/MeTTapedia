import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverse

/-!
# Two constructed cumulative successors

The second successor uses the actual first successor's seed, model and
arrow data. Its independently generated codes live over the twice-raised
site; no enclosing universe or closure operation is an input. The two
cumulative embeddings retain formation provenance, while whole-family
decoding, material members, natural sections and substitution commute.

The second semantic bound is u+2, its code carrier is Type (u+3), and the
external enclosing material set has bound u+3. Iterating the polymorphic
successor at any fixed universe expression is possible; this construction
does not posit a universe level indexed by a term-level natural number or
an internally small or transfinite universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualDoubleSuccessorUniverse

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev FirstSite := PresheafSiteLift.Site C
abbrev SecondSite := PresheafSiteLift.Site (FirstSite (C := C))
abbrev firstContext (context : LabelledContext C) := ContextualSiteLiftMaterial.context context
abbrev twiceContext (context : LabelledContext C) := ContextualSiteLiftMaterial.context (firstContext context)

abbrev firstSeeds := ContextualSuccessorUniverse.LiftSeed seeds seedModel arrows
abbrev firstModels := ContextualSuccessorUniverse.liftSeedModel seeds seedModel arrows
abbrev firstArrows := ContextualSiteLiftMaterial.arrows arrows
abbrev secondSeeds := ContextualSuccessorUniverse.LiftSeed
  (firstSeeds seeds seedModel arrows) (firstModels seeds seedModel arrows) (firstArrows arrows)
abbrev secondModels := ContextualSuccessorUniverse.liftSeedModel
  (firstSeeds seeds seedModel arrows) (firstModels seeds seedModel arrows) (firstArrows arrows)
abbrev secondArrows := ContextualSiteLiftMaterial.arrows (firstArrows arrows)

abbrev LowerCode (context : LabelledContext C) := ContextualSuccessorUniverse.LowerCode seeds seedModel arrows context
abbrev FirstCode (context : LabelledContext (FirstSite (C := C))) : Type (u + 2) :=
  ContextualSuccessorUniverse.Code seeds seedModel arrows context
abbrev Code (context : LabelledContext (SecondSite (C := C))) : Type (u + 3) :=
  ContextualSuccessorUniverse.Code (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) context

abbrev lowerFamily {context : LabelledContext C} :=
  ContextualSuccessorUniverse.lowerFamily seeds seedModel arrows (context := context)
abbrev firstFamily {context : LabelledContext (FirstSite (C := C))} :=
  ContextualSuccessorUniverse.decode seeds seedModel arrows (context := context)
abbrev decode {context : LabelledContext (SecondSite (C := C))} :=
  ContextualSuccessorUniverse.decode (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) (context := context)

def liftFirst {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context) :
    FirstCode seeds seedModel arrows (firstContext context) :=
  ContextualSuccessorUniverse.liftCode seeds seedModel arrows code

def liftNext {context : LabelledContext (FirstSite (C := C))}
    (code : FirstCode seeds seedModel arrows context) :
    Code seeds seedModel arrows (ContextualSiteLiftMaterial.context context) :=
  ContextualSuccessorUniverse.liftCode (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) code

def liftTwice {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context) :
    Code seeds seedModel arrows (twiceContext context) :=
  liftNext seeds seedModel arrows (liftFirst seeds seedModel arrows code)

theorem liftFirst_injective (context : LabelledContext C) :
    Function.Injective (liftFirst seeds seedModel arrows (context := context)) :=
  ContextualSuccessorUniverse.liftCode_injective seeds seedModel arrows context

theorem liftNext_injective (context : LabelledContext (FirstSite (C := C))) :
    Function.Injective (liftNext seeds seedModel arrows (context := context)) :=
  ContextualSuccessorUniverse.liftCode_injective (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) context

theorem liftTwice_injective (context : LabelledContext C) :
    Function.Injective (liftTwice seeds seedModel arrows (context := context)) := by
  intro first second same
  exact liftFirst_injective seeds seedModel arrows context
    (liftNext_injective seeds seedModel arrows (firstContext context) same)

theorem decode_next {context : LabelledContext (FirstSite (C := C))}
    (code : FirstCode seeds seedModel arrows context) :
    decode seeds seedModel arrows (liftNext seeds seedModel arrows code) =
      ContextualSiteLiftMaterial.family (firstFamily seeds seedModel arrows code) := rfl

abbrev twiceFamily {context : LabelledContext C} (family : MaterialFamily context) :
    MaterialFamily (twiceContext context) :=
  ContextualSiteLiftMaterial.family (ContextualSiteLiftMaterial.family family)

theorem decode_twice {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context) :
    decode seeds seedModel arrows (liftTwice seeds seedModel arrows code) =
      twiceFamily (lowerFamily seeds seedModel arrows code) := rfl

def lowerPoint (context : LabelledContext C) (point : (twiceContext context).base.Elements) : context.base.Elements :=
  (PresheafSiteLift.elementsDown context.base).obj
    ((PresheafSiteLift.elementsDown (firstContext context).base).obj point)

def lowerArrow {context : LabelledContext C} {point next : (twiceContext context).base.Elements}
    (step : point ⟶ next) : lowerPoint context point ⟶ lowerPoint context next :=
  (PresheafSiteLift.elementsDown context.base).map
    ((PresheafSiteLift.elementsDown (firstContext context).base).map step)

def raisePoint (context : LabelledContext C) (point : context.base.Elements) :
    (twiceContext context).base.Elements :=
  (PresheafSiteLift.elementsUp (firstContext context).base).obj
    ((PresheafSiteLift.elementsUp context.base).obj point)

theorem lower_raise_point (context : LabelledContext C) (point : context.base.Elements) :
    lowerPoint context (raisePoint context point) = point := rfl

theorem raise_lower_point (context : LabelledContext C) (point : (twiceContext context).base.Elements) :
    raisePoint context (lowerPoint context point) = point := rfl

def semantic {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (point : (twiceContext context).base.Elements) :
    (decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).family.obj point ≃
      (lowerFamily seeds seedModel arrows code).family.obj (lowerPoint context point) where
  toFun term := term.down.down
  invFun term := ⟨⟨term⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem semantic_value {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (point : (twiceContext context).base.Elements)
    (term : (decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).family.obj point) :
    ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).model point).value term =
      HSet.lift (HSet.lift (((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).value
        (semantic seeds seedModel arrows code point term))) := rfl

theorem semantic_restriction {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    {point next : (twiceContext context).base.Elements} (step : point ⟶ next)
    (term : (decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).family.obj point) :
    semantic seeds seedModel arrows code next
        ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).family.map step term) =
      (lowerFamily seeds seedModel arrows code).family.map (lowerArrow step)
        (semantic seeds seedModel arrows code point term) := rfl

theorem carrier {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (point : (twiceContext context).base.Elements) :
    ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).model point).carrier =
      HSet.lift (HSet.lift (((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).carrier)) := rfl

def memberEquiv {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (point : (twiceContext context).base.Elements) :
    {value : HSet.{u} // value ∈ ((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).carrier} ≃
      {value : HSet.{u + 2} // value ∈
        ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).model point).carrier} :=
  (HSet.liftedMembersEquiv _).trans (HSet.liftedMembersEquiv _)

theorem member_value {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (point : (twiceContext context).base.Elements)
    (member : {value : HSet.{u} // value ∈ ((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).carrier}) :
    (memberEquiv seeds seedModel arrows code point member).val = HSet.lift (HSet.lift member.val) := rfl

theorem member_decode {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (point : (twiceContext context).base.Elements)
    (member : {value : HSet.{u} // value ∈ ((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).carrier}) :
    ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).model point).decode
        (memberEquiv seeds seedModel arrows code point member) =
      ULift.up (ULift.up (((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).decode member)) := by
  change ((ContextualSiteLiftMaterial.family (ContextualSiteLiftMaterial.family
    (lowerFamily seeds seedModel arrows code))).model point).decode
      (ContextualSiteLiftMaterial.liftMember _ point
        (ContextualSiteLiftMaterial.liftMember _ _ member)) = _
  exact (ContextualSiteLiftMaterial.decode_lift_member _ point
    (ContextualSiteLiftMaterial.liftMember _ _ member)).trans
      (congrArg ULift.up (ContextualSiteLiftMaterial.decode_lift_member _
        ((PresheafSiteLift.elementsDown (firstContext context).base).obj point) member))

theorem member_restriction {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    {point next : (twiceContext context).base.Elements} (step : point ⟶ next)
    (member : {value : HSet.{u} // value ∈ ((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).carrier}) :
    (decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).memberRestriction step
        (memberEquiv seeds seedModel arrows code point member) =
      memberEquiv seeds seedModel arrows code next
        ((lowerFamily seeds seedModel arrows code).memberRestriction (lowerArrow step) member) := by
  apply ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).model next).decode.injective
  rw [MaterialFamily.memberRestriction_decode, member_decode, member_decode, MaterialFamily.memberRestriction_decode]
  rfl

def sectionEquiv {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context) :
    (lowerFamily seeds seedModel arrows code).family.sections ≃
      (decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).family.sections :=
  (ContextualSuccessorUniverse.sectionEquiv seeds seedModel arrows code).trans
    (ContextualSuccessorUniverse.sectionEquiv (firstSeeds seeds seedModel arrows)
      (firstModels seeds seedModel arrows) (firstArrows arrows) (liftFirst seeds seedModel arrows code))

theorem section_value {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (term : (lowerFamily seeds seedModel arrows code).family.sections)
    (point : (twiceContext context).base.Elements) :
    ((decode seeds seedModel arrows (liftTwice seeds seedModel arrows code)).model point).value
        ((sectionEquiv seeds seedModel arrows code term).val point) =
      HSet.lift (HSet.lift (((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).value
        (term.val (lowerPoint context point)))) := rfl

theorem section_restriction {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (term : (lowerFamily seeds seedModel arrows code).family.sections)
    {point next : (twiceContext context).base.Elements} (step : point ⟶ next) :
    semantic seeds seedModel arrows code next ((sectionEquiv seeds seedModel arrows code term).val next) =
      (lowerFamily seeds seedModel arrows code).family.map (lowerArrow step)
        (semantic seeds seedModel arrows code point ((sectionEquiv seeds seedModel arrows code term).val point)) :=
  (term.property (lowerArrow step)).symm

def raiseChange {context other : LabelledContext C} (change : NatTrans other.base context.base) :
    NatTrans (twiceContext other).base (twiceContext context).base :=
  PresheafSiteLift.raiseChange (PresheafSiteLift.raiseChange change)

theorem raiseChange_identity (context : LabelledContext C) :
    raiseChange (identity context.base) = identity (twiceContext context).base := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem raiseChange_comp {context middle other : LabelledContext C}
    (first : NatTrans other.base middle.base) (later : NatTrans middle.base context.base) :
    raiseChange (compose first later) = compose (raiseChange first) (raiseChange later) := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem liftedFamily_reindex {context other : LabelledContext C} (family : MaterialFamily context)
    (change : NatTrans other.base context.base) :
    ContextualSiteLiftMaterial.family (family.reindex (other := other) change) =
      (ContextualSiteLiftMaterial.family family).reindex (other := firstContext other)
        (PresheafSiteLift.raiseChange change) :=
  ContextualUniverseCodes.MaterialFamily.ext
    (ContextualSiteLiftMaterial.reindex_family family change) (heq_of_eq rfl)

theorem twiceFamily_reindex {context other : LabelledContext C} (family : MaterialFamily context)
    (change : NatTrans other.base context.base) :
    twiceFamily (family.reindex change) =
      (twiceFamily family).reindex (other := twiceContext other) (raiseChange change) := by
  exact (congrArg (fun value : MaterialFamily (firstContext other) => ContextualSiteLiftMaterial.family value)
    (liftedFamily_reindex family change)).trans
      (liftedFamily_reindex (C := FirstSite (C := C))
        (context := firstContext context) (other := firstContext other)
        (ContextualSiteLiftMaterial.family family) (PresheafSiteLift.raiseChange change))

/-- Two constructed comprehension squares transport a genuinely dependent
body from its original extension to the twice-lifted domain's extension. -/
def bodyChange {context : LabelledContext C} (domain : MaterialFamily context) :
    NatTrans (twiceFamily domain).extension.base (twiceContext domain.extension).base :=
  compose (PresheafSiteLift.comprehensionFrom (firstContext context).base
    (ContextualSiteLiftMaterial.family domain).family)
      (PresheafSiteLift.raiseChange (PresheafSiteLift.comprehensionFrom context.base domain.family))

def bodyChangeInverse {context : LabelledContext C} (domain : MaterialFamily context) :
    NatTrans (twiceContext domain.extension).base (twiceFamily domain).extension.base :=
  compose (PresheafSiteLift.raiseChange (PresheafSiteLift.comprehensionTo context.base domain.family))
    (PresheafSiteLift.comprehensionTo (firstContext context).base (ContextualSiteLiftMaterial.family domain).family)

theorem bodyChange_inverse {context : LabelledContext C} (domain : MaterialFamily context) :
    compose (bodyChange domain) (bodyChangeInverse domain) = identity (twiceFamily domain).extension.base := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem inverse_bodyChange {context : LabelledContext C} (domain : MaterialFamily context) :
    compose (bodyChangeInverse domain) (bodyChange domain) = identity (twiceContext domain.extension).base := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

theorem bodyChange_projection {context : LabelledContext C} (domain : MaterialFamily context) :
    compose (bodyChange domain) (raiseChange (PowerClassPresheafProducts.projection domain.family)) =
      PowerClassPresheafProducts.projection (twiceFamily domain).family := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro receipt
  rfl

abbrev twiceBody {context : LabelledContext C} (domain : MaterialFamily context)
    (body : MaterialFamily domain.extension) : MaterialFamily (twiceFamily domain).extension :=
  ContextualSiteLiftMaterial.body (ContextualSiteLiftMaterial.family domain)
    (ContextualSiteLiftMaterial.body domain body)

theorem twiceBody_reindex {context : LabelledContext C} (domain : MaterialFamily context)
    (body : MaterialFamily domain.extension) :
    twiceBody domain body = (twiceFamily body).reindex (other := (twiceFamily domain).extension) (bodyChange domain) := by
  have transported := liftedFamily_reindex (C := FirstSite (C := C))
    (context := firstContext domain.extension) (other := (ContextualSiteLiftMaterial.family domain).extension)
    (ContextualSiteLiftMaterial.family body) (PresheafSiteLift.comprehensionFrom context.base domain.family)
  exact (congrArg (fun value : MaterialFamily (ContextualSiteLiftMaterial.context
      (ContextualSiteLiftMaterial.family domain).extension) =>
        value.reindex (other := (twiceFamily domain).extension)
          (PresheafSiteLift.comprehensionFrom (firstContext context).base
            (ContextualSiteLiftMaterial.family domain).family)) transported).trans
    (ContextualUniverseCodes.MaterialFamily.reindex_comp (C := SecondSite (C := C))
      (context := twiceContext domain.extension)
      (middle := ContextualSiteLiftMaterial.context (ContextualSiteLiftMaterial.family domain).extension)
      (other := (twiceFamily domain).extension) (twiceFamily body)
      (PresheafSiteLift.comprehensionFrom (firstContext context).base (ContextualSiteLiftMaterial.family domain).family)
      (PresheafSiteLift.raiseChange (PresheafSiteLift.comprehensionFrom context.base domain.family)))

def reindex {context other : LabelledContext (SecondSite (C := C))} (change : NatTrans other.base context.base) :
    Code seeds seedModel arrows context → Code seeds seedModel arrows other :=
  ContextualSuccessorUniverse.reindex (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) change

theorem decode_reindex {context other : LabelledContext (SecondSite (C := C))}
    (change : NatTrans other.base context.base) (code : Code seeds seedModel arrows context) :
    decode seeds seedModel arrows (reindex seeds seedModel arrows change code) =
      (decode seeds seedModel arrows code).reindex change :=
  ContextualSuccessorUniverse.decode_reindex _ _ _ change code

theorem reindex_identity {context : LabelledContext (SecondSite (C := C))}
    (code : Code seeds seedModel arrows context) :
    reindex seeds seedModel arrows (identity context.base) code = code :=
  ContextualSuccessorUniverse.reindex_identity _ _ _ code

theorem reindex_comp {context middle other : LabelledContext (SecondSite (C := C))}
    (first : NatTrans other.base middle.base) (later : NatTrans middle.base context.base)
    (code : Code seeds seedModel arrows context) :
    reindex seeds seedModel arrows first (reindex seeds seedModel arrows later code) =
      reindex seeds seedModel arrows (compose first later) code :=
  ContextualSuccessorUniverse.reindex_comp _ _ _ first later code

theorem decode_liftTwice_reindex {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : LowerCode seeds seedModel arrows context) :
    decode seeds seedModel arrows
        (liftTwice seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change code)) =
      decode seeds seedModel arrows
        (reindex seeds seedModel arrows (other := twiceContext other) (raiseChange change)
          (liftTwice seeds seedModel arrows code)) := by
  have outer := ContextualSuccessorUniverse.decode_reindex
    (firstSeeds seeds seedModel arrows) (firstModels seeds seedModel arrows) (firstArrows arrows)
    (other := twiceContext other) (raiseChange change) (liftTwice seeds seedModel arrows code)
  exact (decode_twice seeds seedModel arrows _).trans
    ((congrArg (fun value : MaterialFamily other => twiceFamily value)
      (ContextualClosedUniverseCodes.decode_reindex seeds seedModel arrows change code)).trans
        ((twiceFamily_reindex _ change).trans outer.symm))

/-- A strict recipe equation across substitution would have to identify
the original cumulative seed contexts. Semantic decoder coherence alone
does not supply this stronger equation. -/
theorem liftTwice_reindex_eq_requires_same_origin {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : LowerCode seeds seedModel arrows context)
    (same : liftTwice seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change code) =
      reindex seeds seedModel arrows (other := twiceContext other) (raiseChange change)
        (liftTwice seeds seedModel arrows code)) : twiceContext other = twiceContext context := by
  have traces := congrArg (ContextualCodeSeedTrace.codeTrace (secondSeeds seeds seedModel arrows)
    (secondModels seeds seedModel arrows) (secondArrows arrows)) same
  simp only [reindex, ContextualSuccessorUniverse.reindex, ContextualCodeSeedTrace.codeTrace_reindex] at traces
  change ContextualCodeSeedTrace.Trace.seed
      ⟨twiceContext other, ContextualSuccessorUniverse.LiftSeed.lower (firstContext other) _⟩ =
    ContextualCodeSeedTrace.Trace.seed
      ⟨twiceContext context, ContextualSuccessorUniverse.LiftSeed.lower (firstContext context) _⟩ at traces
  exact congrArg Sigma.fst (ContextualCodeSeedTrace.Trace.seed.inj traces)

theorem section_reindex_square {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : LowerCode seeds seedModel arrows context)
    (term : (lowerFamily seeds seedModel arrows code).family.sections)
    (point : (twiceContext other).base.Elements) :
    (PresheafSiteLift.raiseTerm (firstContext other).base
      (ContextualSiteLiftMaterial.family ((lowerFamily seeds seedModel arrows code).reindex change)).family
      (PresheafSiteLift.raiseTerm other.base ((lowerFamily seeds seedModel arrows code).reindex change).family
        (ContextualSuccessorUniverse.pulledLowerSection seeds seedModel arrows change code term))).val point =
      (sectionEquiv seeds seedModel arrows code term).val
        ((PowerClassPresheafProducts.elementMap (raiseChange change)).obj point) := rfl

def enclosure (context : LabelledContext (SecondSite (C := C))) (point : context.base.Elements) : HSet.{u + 3} :=
  ContextualSuccessorUniverse.enclosure (firstSeeds seeds seedModel arrows)
    (firstModels seeds seedModel arrows) (firstArrows arrows) context point

theorem code_enclosed {context : LabelledContext (SecondSite (C := C))}
    (code : Code seeds seedModel arrows context) (point : context.base.Elements) :
    HSet.lift ((decode seeds seedModel arrows code).model point).carrier ∈
      enclosure seeds seedModel arrows context point :=
  ContextualSuccessorUniverse.code_enclosed _ _ _ code point

theorem lower_carrier_enclosed {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (point : (twiceContext context).base.Elements) :
    HSet.lift (HSet.lift (HSet.lift (((lowerFamily seeds seedModel arrows code).model (lowerPoint context point)).carrier))) ∈
      enclosure seeds seedModel arrows (twiceContext context) point :=
  code_enclosed seeds seedModel arrows (liftTwice seeds seedModel arrows code) point

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualDoubleSuccessorUniverse
