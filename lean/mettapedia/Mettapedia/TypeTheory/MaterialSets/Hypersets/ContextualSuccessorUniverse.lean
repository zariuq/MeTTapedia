import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCodeSeedTrace
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSiteLiftMaterial

/-!
# A generated cumulative successor on the raised site

The cumulative seeds are previously constructed closed codes, interpreted
by the explicit lift of their whole contextual material families. The
successor grammar independently forms products, sums, identities and
hereditary-natural W-types at the raised bound. No enclosing universe or
closure operator is supplied, and arbitrary ambient families are not seeds.

The seed-sensitive trace proves that the cumulative embedding retains lower
code distinctions, including distinctions invisible to material decoding.
Sections, members and actual restrictions commute with the constructed site
transport. Semantic decoding commutes with raised base substitution; the
original seed provenance need not agree as strict upper code syntax.

The site and semantic fibre bound rise from u to u+1. The successor code
carrier has type Type (u+2), and its external material enclosure has type
HSet at bound u+2. This is not an internally small universe presheaf or a
claim of transfinite closure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverse

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev LowerCode (context : LabelledContext C) :=
  ContextualClosedUniverseCodes.Code seeds seedModel arrows context

abbrev lowerFamily {context : LabelledContext C} :=
  ContextualClosedUniverseCodes.decodeFamily seeds seedModel arrows (context := context)

/-- Only previously constructed lower codes are cumulative seed data.
The origin context is retained, rather than reconstructed from a carrier. -/
inductive LiftSeed : (upperContext : LabelledContext (PresheafSiteLift.Site C)) → Type (u + 2) where
  | lower (context : LabelledContext C) (code : LowerCode seeds seedModel arrows context) :
      LiftSeed (ContextualSiteLiftMaterial.context context)

def liftSeedModel : (context : LabelledContext (PresheafSiteLift.Site C)) →
    LiftSeed seeds seedModel arrows context → MaterialFamily context
  | _, .lower _ code => ContextualSiteLiftMaterial.family (lowerFamily seeds seedModel arrows code)

abbrev Code (context : LabelledContext (PresheafSiteLift.Site C)) : Type (u + 2) :=
  ContextualClosedUniverseCodes.Code (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) context

abbrev decode {context : LabelledContext (PresheafSiteLift.Site C)} :=
  ContextualClosedUniverseCodes.decodeFamily (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) (context := context)

def liftCode {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context) :
    Code seeds seedModel arrows (ContextualSiteLiftMaterial.context context) :=
  ContextualClosedUniverseCodes.seed (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows)
    (ContextualSiteLiftMaterial.context context) (LiftSeed.lower context code)

theorem decode_lift {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context) :
    decode seeds seedModel arrows (liftCode seeds seedModel arrows code) =
      ContextualSiteLiftMaterial.family (lowerFamily seeds seedModel arrows code) := rfl

theorem liftCode_injective (context : LabelledContext C) :
    Function.Injective (liftCode seeds seedModel arrows (context := context)) := by
  intro first second same
  have labels := ContextualCodeSeedTrace.seed_injective (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows)
    (ContextualSiteLiftMaterial.context context) same
  exact LiftSeed.lower.inj labels

def pi {context : LabelledContext (PresheafSiteLift.Site C)}
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decode seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows context :=
  ContextualClosedUniverseCodes.pi (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) domain body

def sigma {context : LabelledContext (PresheafSiteLift.Site C)}
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decode seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows context :=
  ContextualClosedUniverseCodes.sigma (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) domain body

def w {context : LabelledContext (PresheafSiteLift.Site C)}
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decode seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows context :=
  ContextualClosedUniverseCodes.w (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) domain body

def identity {context : LabelledContext (PresheafSiteLift.Site C)}
    (domain : Code seeds seedModel arrows context)
    (left right : (decode seeds seedModel arrows domain).family.sections) :
    Code seeds seedModel arrows context :=
  ContextualClosedUniverseCodes.identity (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) domain left right

theorem decode_pi {context : LabelledContext (PresheafSiteLift.Site C)}
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decode seeds seedModel arrows domain).extension) :
    decode seeds seedModel arrows (pi seeds seedModel arrows domain body) =
      (decode seeds seedModel arrows domain).pi (decode seeds seedModel arrows body)
        (ContextualSiteLiftMaterial.arrows arrows) :=
  ContextualClosedUniverseCodes.decode_binary _ _ _ .pi domain body

theorem decode_sigma {context : LabelledContext (PresheafSiteLift.Site C)}
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decode seeds seedModel arrows domain).extension) :
    decode seeds seedModel arrows (sigma seeds seedModel arrows domain body) =
      (decode seeds seedModel arrows domain).sigma (decode seeds seedModel arrows body) :=
  ContextualClosedUniverseCodes.decode_binary _ _ _ .sigma domain body

theorem decode_w {context : LabelledContext (PresheafSiteLift.Site C)}
    (domain : Code seeds seedModel arrows context)
    (body : Code seeds seedModel arrows (decode seeds seedModel arrows domain).extension) :
    decode seeds seedModel arrows (w seeds seedModel arrows domain body) =
      (decode seeds seedModel arrows domain).w (decode seeds seedModel arrows body)
        (ContextualSiteLiftMaterial.arrows arrows) :=
  ContextualClosedUniverseCodes.decode_binary _ _ _ .w domain body

theorem decode_identity {context : LabelledContext (PresheafSiteLift.Site C)}
    (domain : Code seeds seedModel arrows context)
    (left right : (decode seeds seedModel arrows domain).family.sections) :
    decode seeds seedModel arrows (identity seeds seedModel arrows domain left right) =
      (decode seeds seedModel arrows domain).identity left right :=
  ContextualClosedUniverseCodes.decode_identity _ _ _ domain left right

def reindex {context other : LabelledContext (PresheafSiteLift.Site C)}
    (change : NatTrans other.base context.base) :
    Code seeds seedModel arrows context → Code seeds seedModel arrows other :=
  ContextualClosedUniverseCodes.reindex (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) change

theorem decode_reindex {context other : LabelledContext (PresheafSiteLift.Site C)}
    (change : NatTrans other.base context.base) (code : Code seeds seedModel arrows context) :
    decode seeds seedModel arrows (reindex seeds seedModel arrows change code) =
      (decode seeds seedModel arrows code).reindex change :=
  ContextualClosedUniverseCodes.decode_reindex _ _ _ change code

theorem reindex_identity {context : LabelledContext (PresheafSiteLift.Site C)}
    (code : Code seeds seedModel arrows context) :
    reindex seeds seedModel arrows (Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity context.base) code = code :=
  ContextualClosedUniverseCodes.reindex_identity _ _ _ code

theorem reindex_comp {context middle other : LabelledContext (PresheafSiteLift.Site C)}
    (earlier : NatTrans other.base middle.base) (later : NatTrans middle.base context.base)
    (code : Code seeds seedModel arrows context) :
    reindex seeds seedModel arrows earlier (reindex seeds seedModel arrows later code) =
      reindex seeds seedModel arrows (compose earlier later) code :=
  ContextualClosedUniverseCodes.reindex_comp _ _ _ earlier later code

/-- The dependent body is genuinely reindexed through the constructed
upper comprehension comparison before upper formation. -/
def liftBody {context : LabelledContext C} (domain : LowerCode seeds seedModel arrows context)
    (body : LowerCode seeds seedModel arrows (lowerFamily seeds seedModel arrows domain).extension) :
    Code seeds seedModel arrows (decode seeds seedModel arrows (liftCode seeds seedModel arrows domain)).extension :=
  reindex seeds seedModel arrows
    (context := ContextualSiteLiftMaterial.context (lowerFamily seeds seedModel arrows domain).extension)
    (other := (ContextualSiteLiftMaterial.family (lowerFamily seeds seedModel arrows domain)).extension)
    (PresheafSiteLift.comprehensionFrom context.base (lowerFamily seeds seedModel arrows domain).family)
    (liftCode seeds seedModel arrows body)

theorem decode_liftBody {context : LabelledContext C} (domain : LowerCode seeds seedModel arrows context)
    (body : LowerCode seeds seedModel arrows (lowerFamily seeds seedModel arrows domain).extension) :
    decode seeds seedModel arrows (liftBody seeds seedModel arrows domain body) =
      ContextualSiteLiftMaterial.body (lowerFamily seeds seedModel arrows domain)
        (lowerFamily seeds seedModel arrows body) :=
  decode_reindex seeds seedModel arrows _ _

def sectionEquiv {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context) :
    (lowerFamily seeds seedModel arrows code).family.sections ≃
      (decode seeds seedModel arrows (liftCode seeds seedModel arrows code)).family.sections :=
  PresheafSiteLift.termEquiv context.base (lowerFamily seeds seedModel arrows code).family

theorem section_value {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    (term : (lowerFamily seeds seedModel arrows code).family.sections)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    ((decode seeds seedModel arrows (liftCode seeds seedModel arrows code)).model point).value
      ((sectionEquiv seeds seedModel arrows code term).val point) =
        HSet.lift (((lowerFamily seeds seedModel arrows code).model
          ((PresheafSiteLift.elementsDown context.base).obj point)).value
          (term.val ((PresheafSiteLift.elementsDown context.base).obj point))) :=
  ContextualSiteLiftMaterial.term_value _ term point

theorem member_restriction {context : LabelledContext C} (code : LowerCode seeds seedModel arrows context)
    {first second : (ContextualSiteLiftMaterial.context context).base.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ ((lowerFamily seeds seedModel arrows code).model
      ((PresheafSiteLift.elementsDown context.base).obj first)).carrier}) :
    (decode seeds seedModel arrows (liftCode seeds seedModel arrows code)).memberRestriction step
        (ContextualSiteLiftMaterial.liftMember (lowerFamily seeds seedModel arrows code) first member) =
      ContextualSiteLiftMaterial.liftMember (lowerFamily seeds seedModel arrows code) second
        ((lowerFamily seeds seedModel arrows code).memberRestriction
          ((PresheafSiteLift.elementsDown context.base).map step) member) :=
  ContextualSiteLiftMaterial.member_restriction _ step member

/-- Equality of the complete interpretations includes all restriction maps
and dictionaries. It does not assert equality of the seed provenance. -/
theorem decode_lift_reindex {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : LowerCode seeds seedModel arrows context) :
    decode seeds seedModel arrows
        (liftCode seeds seedModel arrows (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change code)) =
      decode seeds seedModel arrows
        (reindex seeds seedModel arrows (other := ContextualSiteLiftMaterial.context other)
          (PresheafSiteLift.raiseChange change) (liftCode seeds seedModel arrows code)) := by
  rw [decode_lift, decode_reindex, decode_lift]
  simp only [lowerFamily, ContextualClosedUniverseCodes.decode_reindex]
  exact ContextualUniverseCodes.MaterialFamily.ext
    (ContextualSiteLiftMaterial.reindex_family _ change) (heq_of_eq rfl)

/-- Strict equality under the present equation theory preserves the seed's
origin. Decoder coherence does not erase that formation information. -/
theorem lift_reindex_eq_requires_same_origin {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : LowerCode seeds seedModel arrows context)
    (same : liftCode seeds seedModel arrows
        (ContextualClosedUniverseCodes.reindex seeds seedModel arrows change code) =
      reindex seeds seedModel arrows (other := ContextualSiteLiftMaterial.context other)
        (PresheafSiteLift.raiseChange change) (liftCode seeds seedModel arrows code)) :
    ContextualSiteLiftMaterial.context other = ContextualSiteLiftMaterial.context context := by
  have traces := congrArg
    (ContextualCodeSeedTrace.codeTrace (LiftSeed seeds seedModel arrows)
      (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows)) same
  simp only [reindex, ContextualCodeSeedTrace.codeTrace_reindex] at traces
  change ContextualCodeSeedTrace.Trace.seed
    ⟨ContextualSiteLiftMaterial.context other, LiftSeed.lower other _⟩ =
      ContextualCodeSeedTrace.Trace.seed
        ⟨ContextualSiteLiftMaterial.context context, LiftSeed.lower context code⟩ at traces
  exact congrArg Sigma.fst (ContextualCodeSeedTrace.Trace.seed.inj traces)

def pulledLowerSection {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : LowerCode seeds seedModel arrows context)
    (term : (lowerFamily seeds seedModel arrows code).family.sections) :
    ((lowerFamily seeds seedModel arrows code).reindex change).family.sections :=
  ⟨fun point => term.val ((PowerClassPresheafProducts.elementMap change).obj point), by
    intro _ _ step
    exact term.property ((PowerClassPresheafProducts.elementMap change).map step)⟩

/-- The two routes retain the same actual section value at every raised
point, including the authored nonidentity context substitution. -/
theorem section_reindex_square {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : LowerCode seeds seedModel arrows context)
    (term : (lowerFamily seeds seedModel arrows code).family.sections)
    (point : (ContextualSiteLiftMaterial.context other).base.Elements) :
    (PresheafSiteLift.raiseTerm other.base ((lowerFamily seeds seedModel arrows code).reindex change).family
        (pulledLowerSection seeds seedModel arrows change code term)).val point =
      (sectionEquiv seeds seedModel arrows code term).val
        ((PowerClassPresheafProducts.elementMap (PresheafSiteLift.raiseChange change)).obj point) := rfl

theorem section_reindex_value {context other : LabelledContext C}
    (change : NatTrans other.base context.base) (code : LowerCode seeds seedModel arrows context)
    (term : (lowerFamily seeds seedModel arrows code).family.sections)
    (point : (ContextualSiteLiftMaterial.context other).base.Elements) :
    ((ContextualSiteLiftMaterial.family ((lowerFamily seeds seedModel arrows code).reindex change)).model point).value
      ((PresheafSiteLift.raiseTerm other.base ((lowerFamily seeds seedModel arrows code).reindex change).family
        (pulledLowerSection seeds seedModel arrows change code term)).val point) =
      ((decode seeds seedModel arrows (liftCode seeds seedModel arrows code)).model
        ((PowerClassPresheafProducts.elementMap (PresheafSiteLift.raiseChange change)).obj point)).value
        ((sectionEquiv seeds seedModel arrows code term).val
          ((PowerClassPresheafProducts.elementMap (PresheafSiteLift.raiseChange change)).obj point)) := rfl

def enclosure (context : LabelledContext (PresheafSiteLift.Site C))
    (point : context.base.Elements) : HSet.{u + 2} :=
  ContextualGeneratedUniverse.enclosure (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) context point

theorem code_enclosed {context : LabelledContext (PresheafSiteLift.Site C)}
    (code : Code seeds seedModel arrows context) (point : context.base.Elements) :
    HSet.lift ((decode seeds seedModel arrows code).model point).carrier ∈
      enclosure seeds seedModel arrows context point :=
  ContextualClosedUniverseCodes.interpreted_code_enclosed _ _ _ code point

theorem lower_carrier_enclosed {context : LabelledContext C}
    (code : LowerCode seeds seedModel arrows context)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    HSet.lift (HSet.lift (((lowerFamily seeds seedModel arrows code).model
      ((PresheafSiteLift.elementsDown context.base).obj point)).carrier)) ∈
        enclosure seeds seedModel arrows (ContextualSiteLiftMaterial.context context) point :=
  code_enclosed seeds seedModel arrows (liftCode seeds seedModel arrows code) point

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverse
