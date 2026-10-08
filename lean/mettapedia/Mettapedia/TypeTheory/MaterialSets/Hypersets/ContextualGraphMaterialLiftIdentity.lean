import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyIdentity
import Mettapedia.TypeTheory.ContextualSmallFamilyIdentityExt

/-!
# Actual discrete identity and dependent J across the material universe lift

Both native endpoints and their identity witness are raised and recovered
by explicit inverse context maps. Arbitrary upper dependent motives are
pulled through those maps; the independently formed eliminators agree on
whole sections, computation, and parameter substitution. No upper motive
is assumed to have a smaller presentation.

This is the discrete identity interpretation. Full-future graph matching
remains a separate observation and does not replace the identity witness.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftIdentity
open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyIdentity ContextualSmallFamilyComprehension
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualGraphMaterialFamilies ContextualGraphMaterialLift
universe u
variable {D : Type u} [Category.{u} D] {original : D ⥤ Type u}
variable (domain : Family original)

def identityDown : NaturalHom (identityContext (native domain)) (base (identityContext domain.native)) where
  app _ receipt := ULift.up
    ⟨⟨⟨receipt.1.1.1.down, receipt.1.1.2.down⟩, receipt.1.2.down⟩,
      PresheafIdentityWitness.encode (congrArg ULift.down (PresheafIdentityWitness.decode receipt.2))⟩
  naturality _ _ := by
    apply ULift.ext
    apply receipt_ext domain.native <;> rfl

def identityUp : NaturalHom (base (identityContext domain.native)) (identityContext (native domain)) where
  app _ receipt :=
    ⟨⟨⟨ULift.up receipt.down.1.1.1, ULift.up receipt.down.1.1.2⟩, ULift.up receipt.down.1.2⟩,
      PresheafIdentityWitness.encode (congrArg ULift.up (PresheafIdentityWitness.decode receipt.down.2))⟩
  naturality _ _ := by
    apply receipt_ext (native domain) <;> rfl

theorem down_up : (identityDown domain).comp (identityUp domain) =
    ContextualSmallMapConstructions.identity (identityContext (native domain)) := by
  apply NaturalHom.ext
  intro _ _
  apply receipt_ext (native domain) <;> rfl

theorem up_down : (identityUp domain).comp (identityDown domain) =
    ContextualSmallMapConstructions.identity (base (identityContext domain.native)) := by
  apply NaturalHom.ext
  intro _ _
  apply ULift.ext
  apply receipt_ext domain.native <;> rfl

def totalUp : NaturalHom (base (total domain.native)) (total (native domain)) where
  app _ receipt := ⟨ULift.up receipt.down.1, ULift.up receipt.down.2⟩
  naturality _ _ := rfl

def liftedHom {first second : D ⥤ Type u} (operation : NaturalHom first second) :
    NaturalHom (base first) (base second) where
  app point receipt := ULift.up (operation.app point.down receipt.down)
  naturality step receipt := congrArg ULift.up (operation.naturality step.down receipt.down)

theorem diagonal_up : (liftedHom (diagonal domain.native)).comp (identityUp domain) =
    (totalUp domain).comp (diagonal (native domain)) := by
  apply NaturalHom.ext
  intro _ _
  apply receipt_ext (native domain) <;> rfl

theorem diagonal_down : (diagonal (native domain)).comp (identityDown domain) =
    (bodyBaseMap domain).comp (liftedHom (diagonal domain.native)) := by
  apply NaturalHom.ext
  intro _ _
  apply ULift.ext
  apply receipt_ext domain.native <;> rfl

theorem readLeft_down : (identityDown domain).comp (liftedHom (readLeft domain.native)) =
    (readLeft (native domain)).comp (bodyBaseMap domain) := by
  apply NaturalHom.ext
  intro _ _
  rfl


def lowerIdentityFunctor : (identityContext (native domain)).Elements ⥤ (identityContext domain.native).Elements :=
  PresheafSiteLift.compose (elementMap (identityDown domain))
    (elementsDown (identityContext domain.native))

def upperIdentityFunctor : (identityContext domain.native).Elements ⥤ (identityContext (native domain)).Elements :=
  PresheafSiteLift.compose (elementsUp (identityContext domain.native))
    (elementMap (identityUp domain))

theorem identity_roundtrip_point (point : (identityContext (native domain)).Elements) :
    (upperIdentityFunctor domain).obj ((lowerIdentityFunctor domain).obj point) = point := by
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply receipt_ext (native domain) <;> rfl

theorem lower_roundtrip_point (point : (identityContext domain.native).Elements) :
    (lowerIdentityFunctor domain).obj ((upperIdentityFunctor domain).obj point) = point := by
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply receipt_ext domain.native <;> rfl

def upperComprehensionFunctor : (total domain.native).Elements ⥤ (total (native domain)).Elements :=
  PresheafSiteLift.compose (elementsUp (total domain.native)) (elementMap (totalUp domain))

theorem readLeft_roundtrip_point (point : (identityContext (native domain)).Elements) :
    (upperComprehensionFunctor domain).obj
        ((elementMap (readLeft domain.native)).obj ((lowerIdentityFunctor domain).obj point)) =
      (elementMap (readLeft (native domain))).obj point := rfl

universe h a b c d

def pullSection {E : Type a} {F : Type b} [Category.{c} E] [Category.{d} F]
    (change : E ⥤ F) (family : F ⥤ Type h) (term : family.sections) :
    (PresheafSiteLift.compose change family).sections :=
  ⟨fun point => term.val (change.obj point), fun step => term.property (change.map step)⟩

theorem sectionValue_heq {E : Type a} [Category.{b} E] (family : E ⥤ Type h)
    (term : family.sections) {first second : E} (same : first = second) :
    HEq (term.val first) (term.val second) := by
  cases same
  rfl

variable (motive : (identityContext (native domain)).Elements ⥤ Type h)

def lowerMotive : (identityContext domain.native).Elements ⥤ Type h :=
  PresheafSiteLift.compose (upperIdentityFunctor domain) motive

theorem motive_roundtrip :
    PresheafSiteLift.compose (lowerIdentityFunctor domain) (lowerMotive domain motive) = motive := by
  refine Functor.hext (fun point => congrArg motive.obj (identity_roundtrip_point domain point)) ?_
  intro first second step
  exact familyArrow_heq motive
    (identity_roundtrip_point domain first) (identity_roundtrip_point domain second) _ _
    (elementsArrow_heq (identity_roundtrip_point domain first) (identity_roundtrip_point domain second) _ _ HEq.rfl)

theorem reflexive_motive :
    PresheafSiteLift.compose (upperComprehensionFunctor domain)
      (ContextualSmallFamilyIdentity.reindex motive (diagonal (native domain))) =
    ContextualSmallFamilyIdentity.reindex (lowerMotive domain motive) (diagonal domain.native) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

variable (method : (ContextualSmallFamilyIdentity.reindex motive (diagonal (native domain))).sections)

def lowerMethod : (ContextualSmallFamilyIdentity.reindex (lowerMotive domain motive) (diagonal domain.native)).sections :=
  sectionCast (reflexive_motive domain motive)
    (pullSection (upperComprehensionFunctor domain)
      (ContextualSmallFamilyIdentity.reindex motive (diagonal (native domain))) method)

theorem J_value_comparison (point : (identityContext (native domain)).Elements) :
    HEq ((J (native domain) motive method).val point)
      ((J domain.native (lowerMotive domain motive) (lowerMethod domain motive method)).val
        ((lowerIdentityFunctor domain).obj point)) := by
  have upper := J_value_heq (native domain) motive method point
  have lower := J_value_heq domain.native (lowerMotive domain motive)
    (lowerMethod domain motive method) ((lowerIdentityFunctor domain).obj point)
  have castMethod := sectionCast_value (reflexive_motive domain motive)
    (pullSection (upperComprehensionFunctor domain)
      (ContextualSmallFamilyIdentity.reindex motive (diagonal (native domain))) method)
    ((elementMap (readLeft domain.native)).obj ((lowerIdentityFunctor domain).obj point))
  have methods := sectionValue_heq
    (ContextualSmallFamilyIdentity.reindex motive (diagonal (native domain)))
    method (readLeft_roundtrip_point domain point)
  exact upper.trans (methods.symm.trans (castMethod.symm.trans lower.symm))

set_option maxHeartbeats 2000000 in
theorem J_comparison : J (native domain) motive method =
    sectionCast (motive_roundtrip domain motive)
      (pullSection (lowerIdentityFunctor domain) (lowerMotive domain motive)
        (J domain.native (lowerMotive domain motive) (lowerMethod domain motive method))) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  exact (J_value_comparison domain motive method point).trans
    (sectionCast_value (motive_roundtrip domain motive)
      (pullSection (lowerIdentityFunctor domain) (lowerMotive domain motive)
        (J domain.native (lowerMotive domain motive) (lowerMethod domain motive method))) point).symm

theorem J_beta_comparison :
    reindexSection (diagonal (native domain)) motive
      (sectionCast (motive_roundtrip domain motive)
        (pullSection (lowerIdentityFunctor domain) (lowerMotive domain motive)
          (J domain.native (lowerMotive domain motive) (lowerMethod domain motive method)))) = method := by
  rw [← J_comparison]
  exact J_beta (native domain) motive method

theorem J_comparison_substitution {other : Upper (D := D) ⥤ Type a}
    (change : NaturalHom other (base original)) :
    reindexSection (identityReindex change (native domain)) motive
      (sectionCast (motive_roundtrip domain motive)
        (pullSection (lowerIdentityFunctor domain) (lowerMotive domain motive)
          (J domain.native (lowerMotive domain motive) (lowerMethod domain motive method)))) =
      J (ContextualSmallFamilyIdentity.reindex (native domain) change)
        (ContextualSmallFamilyIdentity.reindex motive (identityReindex change (native domain)))
        (reindexMethod change (native domain) motive method) := by
  rw [← J_comparison]
  exact J_substitution change (native domain) motive method


theorem J_beta_comparison_substitution {other : Upper (D := D) ⥤ Type a}
    (change : NaturalHom other (base original)) :
    reindexSection (diagonal (ContextualSmallFamilyIdentity.reindex (native domain) change))
      (ContextualSmallFamilyIdentity.reindex motive (identityReindex change (native domain)))
      (reindexSection (identityReindex change (native domain)) motive
        (sectionCast (motive_roundtrip domain motive)
          (pullSection (lowerIdentityFunctor domain) (lowerMotive domain motive)
            (J domain.native (lowerMotive domain motive) (lowerMethod domain motive method))))) =
      reindexMethod change (native domain) motive method := by
  rw [J_comparison_substitution]
  exact J_beta _ _ _

open ContextualGraphDiagrams ContextualRealizedGraphs

/-- The same whole-section comparison preserves any declared natural
material reading of the upper motive, without lowering that motive. -/
theorem J_readout_comparison
    (reading : NaturalHom (total motive) (values (Upper (D := D))))
    (point : (identityContext (native domain)).Elements) :
    reading.app point.1 ⟨point.2, (J (native domain) motive method).val point⟩ =
      reading.app point.1 ⟨point.2,
        (sectionCast (motive_roundtrip domain motive)
          (pullSection (lowerIdentityFunctor domain) (lowerMotive domain motive)
            (J domain.native (lowerMotive domain motive) (lowerMethod domain motive method)))).val point⟩ :=
  congrArg (fun result : motive.sections => reading.app point.1 ⟨point.2, result.val point⟩)
    (J_comparison domain motive method)

section Formation

variable (point : (base original).Elements) (left right : (native domain).obj point)

def witnessUp (witness : PresheafIdentityWitness.Witness left.down right.down) :
    PresheafIdentityWitness.Witness left right :=
  PresheafIdentityWitness.encode (congrArg ULift.up (PresheafIdentityWitness.decode witness))

def witnessDown (witness : PresheafIdentityWitness.Witness left right) :
    PresheafIdentityWitness.Witness left.down right.down :=
  PresheafIdentityWitness.encode (congrArg ULift.down (PresheafIdentityWitness.decode witness))

def witnessComparison (world : Upper (D := D)) :
    Equal (ContextualGraphUniverseLift.value (ContextualGraphFamilyBodyIdentity.witnessValue world.down))
      (ContextualGraphFamilyBodyIdentity.witnessValue world) :=
  extensionality
    (fun _ _ _ membership => False.elim membership.1.property)
    (fun _ _ _ membership => False.elim membership.1.property)

def identityForth (element : Value (Upper (D := D)) point.1)
    (membership : Member element (ContextualGraphUniverseLift.value
      (ContextualGraphFamilyBodyIdentity.identityCarrier domain.native
        ((elementsDown original).obj point) left.down right.down))) :
    Member element (ContextualGraphFamilyBodyIdentity.identityCarrier (native domain) point left right) := by
  let lower := ContextualGraphFamilyBodyIdentity.identityCarrier domain.native
    ((elementsDown original).obj point) left.down right.down
  let child := ContextualGraphUniverseLift.childDecoder lower membership.1
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode
    (witnessFamily domain.native) (ContextualGraphFamilyBodyIdentity.witnessReading domain.native)
    ⟨point.1.down, ⟨⟨point.2.down, left.down⟩, right.down⟩⟩
    (childValue D lower child) (Member.atChild lower child)
  exact ContextualGraphFamilyBodyComparison.memberIntro
    (witnessFamily (native domain)) (ContextualGraphFamilyBodyIdentity.witnessReading (native domain))
    ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩ element (witnessUp domain point left right decoded.1)
    (membership.2.trans ((ContextualGraphUniverseLift.preserve decoded.2).trans (witnessComparison point.1)))

def identityBack (element : Value (Upper (D := D)) point.1)
    (membership : Member element
      (ContextualGraphFamilyBodyIdentity.identityCarrier (native domain) point left right)) :
    Member element (ContextualGraphUniverseLift.value
      (ContextualGraphFamilyBodyIdentity.identityCarrier domain.native
        ((elementsDown original).obj point) left.down right.down)) := by
  let decoded := ContextualGraphFamilyBodyComparison.memberDecode
    (witnessFamily (native domain)) (ContextualGraphFamilyBodyIdentity.witnessReading (native domain))
    ⟨point.1, ⟨⟨point.2, left⟩, right⟩⟩ element membership
  let lowerMember := ContextualGraphFamilyBodyComparison.memberIntro
    (witnessFamily domain.native) (ContextualGraphFamilyBodyIdentity.witnessReading domain.native)
    ⟨point.1.down, ⟨⟨point.2.down, left.down⟩, right.down⟩⟩
    (ContextualGraphFamilyBodyIdentity.witnessValue point.1.down)
    (witnessDown domain point left right decoded.1) (Equal.refl _)
  exact Member.transportChild (decoded.2.trans (witnessComparison point.1).symm).symm
    (ContextualGraphUniverseLift.memberPreserve lowerMember)

/-- Actual identity carriers agree at every future context, including
members whose upper graph presentations are not lower images. -/
def identityCarrierComparison :
    Equal (ContextualGraphUniverseLift.value
      (ContextualGraphFamilyBodyIdentity.identityCarrier domain.native
        ((elementsDown original).obj point) left.down right.down))
      (ContextualGraphFamilyBodyIdentity.identityCarrier (native domain) point left right) := by
  apply extensionality
  · intro target arrival element membership
    let next : (base original).Elements := ⟨target, (base original).map arrival point.2⟩
    let step : point ⟶ next := CategoryOfElements.homMk (F := base original) point next arrival rfl
    exact identityForth domain next ((native domain).map step left) ((native domain).map step right)
      element membership
  · intro target arrival element membership
    let next : (base original).Elements := ⟨target, (base original).map arrival point.2⟩
    let step : point ⟶ next := CategoryOfElements.homMk (F := base original) point next arrival rfl
    exact identityBack domain next ((native domain).map step left) ((native domain).map step right)
      element membership

end Formation

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphMaterialLiftIdentity
