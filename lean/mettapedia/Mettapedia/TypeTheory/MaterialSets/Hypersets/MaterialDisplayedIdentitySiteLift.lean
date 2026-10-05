import Mettapedia.TypeTheory.MaterialSets.Hypersets.DisplayedPresheafIdentitySiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSiteLiftMaterial

/-!
# Actual material motive values in successor-site identity elimination

Three material comprehension extensions construct the two-endpoint and
singleton-witness context. Its independently raised dictionaries retain
the complete nested material labels. Motive graphs are actually lifted and
reindexed along the constructed endpoint-and-witness context inverse.
Full dependent J commutes with their material values and member decoders.

This is the discrete interpretation and a single successor translation.
The construction neither equates all upper families with translations nor
imposes an identity rule on another calculus.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialDisplayedIdentitySiteLift

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory

universe u
variable {C : Type u} [Category.{u} C] {original : LabelledContext C}
variable (domain : MaterialFamily original)

abbrev second : MaterialFamily domain.extension :=
  domain.reindex (other := domain.extension) (PowerClassPresheafProducts.projection domain.family)

abbrev endpointContext : LabelledContext C := (second domain).extension

abbrev endpointDomain : MaterialFamily (endpointContext domain) :=
  (second domain).reindex (other := (endpointContext domain)) (PowerClassPresheafProducts.projection (second domain).family)

abbrev leftEndpoint : (endpointDomain domain).family.sections := DisplayedPresheafIdentity.leftEndpoint domain.family
abbrev rightEndpoint : (endpointDomain domain).family.sections := DisplayedPresheafIdentity.rightEndpoint domain.family

def witnesses : MaterialFamily (endpointContext domain) :=
  (endpointDomain domain).identity (leftEndpoint domain) (rightEndpoint domain)

abbrev identityContext : LabelledContext C := (witnesses domain).extension

theorem context_base : (identityContext domain).base = DisplayedPresheafIdentity.identityContext domain.family := rfl

private theorem extension_label {context : LabelledContext C} (family : MaterialFamily context)
    (point : family.extension.base.Elements) : family.extension.labels.reading point =
      HSet.kpair (context.labels.reading ⟨point.1, point.2.1⟩) ((family.model ⟨point.1, point.2.1⟩).value point.2.2) := by
  change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) = _
  rw [AccessiblePointedGraph.mk_kpairGraph, PresentedType.mk_termGraph]
  rfl

theorem context_label (point : (identityContext domain).base.Elements) :
    (identityContext domain).labels.reading point = HSet.kpair
      (HSet.kpair (HSet.kpair (original.labels.reading ⟨point.1, point.2.1.1.1⟩)
        ((domain.model ⟨point.1, point.2.1.1.1⟩).value point.2.1.1.2))
        ((domain.model ⟨point.1, point.2.1.1.1⟩).value point.2.1.2)) ∅ := by
  have witnessValue : ((witnesses domain).model ⟨point.1, point.2.1⟩).value point.2.2 = ∅ :=
    (PresheafIdentityWitness.member_condition point.2.2).1
  exact (extension_label (witnesses domain) point).trans
    (congrArg₂ HSet.kpair ((extension_label (second domain) ⟨point.1, point.2.1⟩).trans
      (congrArg (fun originalLabel => HSet.kpair originalLabel
        ((domain.model ⟨point.1, point.2.1.1.1⟩).value point.2.1.2))
        (extension_label domain ⟨point.1, point.2.1.1⟩))) witnessValue)

abbrev upperContext := identityContext (ContextualSiteLiftMaterial.family domain)

abbrev lowerPoint (point : (upperContext domain).base.Elements) : (identityContext domain).base.Elements :=
  (PresheafSiteLift.elementsDown (identityContext domain).base).obj
    ((PowerClassPresheafProducts.elementMap (DisplayedPresheafIdentitySiteLift.contextFrom original.base domain.family)).obj point)

/-- The upper context is formed with three actual material extensions,
not merely assigned the lifted lower label dictionary. -/
theorem upper_context_label (point : (upperContext domain).base.Elements) :
    (upperContext domain).labels.reading point = HSet.lift ((identityContext domain).labels.reading (lowerPoint domain point)) := by
  rw [context_label, context_label, HSet.lift_kpair, HSet.lift_kpair, HSet.lift_kpair, HSet.lift_empty]
  rfl

variable (motive : MaterialFamily (identityContext domain))

abbrev upperMotive : MaterialFamily (upperContext domain) :=
  (ContextualSiteLiftMaterial.family motive).reindex (other := upperContext domain)
    (DisplayedPresheafIdentitySiteLift.contextFrom original.base domain.family)

theorem motive_carrier (point : (upperContext domain).base.Elements) :
    ((upperMotive domain motive).model point).carrier = HSet.lift ((motive.model (lowerPoint domain point)).carrier) := rfl

def memberEquiv (point : (upperContext domain).base.Elements) :
    {value : HSet.{u + 1} // value ∈ ((upperMotive domain motive).model point).carrier} ≃
      {value : HSet.{u} // value ∈ (motive.model (lowerPoint domain point)).carrier} :=
  (HSet.liftedMembersEquiv (motive.model (lowerPoint domain point)).carrier).symm

theorem member_value (point : (upperContext domain).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((upperMotive domain motive).model point).carrier}) :
    HSet.lift (memberEquiv domain motive point member).val = member.val :=
  congrArg Subtype.val ((HSet.liftedMembersEquiv (motive.model (lowerPoint domain point)).carrier).apply_symm_apply member)

variable (method : (PowerClassPresheafProducts.reindex (DisplayedPresheafIdentity.diagonal domain.family) motive.family).sections)

def J : (upperMotive domain motive).family.sections :=
  DisplayedPresheafIdentity.J (ContextualSiteLiftMaterial.family domain).family (upperMotive domain motive).family
    (DisplayedPresheafIdentitySiteLift.upperMethod original.base domain.family motive.family method)

theorem J_value (point : (upperContext domain).base.Elements) :
    ((upperMotive domain motive).model point).value ((J domain motive method).val point) =
      HSet.lift ((motive.model (lowerPoint domain point)).value
        ((DisplayedPresheafIdentity.J domain.family motive.family method).val (lowerPoint domain point))) := by
  exact congrArg (fun term : (upperMotive domain motive).family.sections =>
    ((upperMotive domain motive).model point).value (term.val point))
    (DisplayedPresheafIdentitySiteLift.J_lift original.base domain.family motive.family method)

theorem J_decoder (point : (upperContext domain).base.Elements) :
    (motive.model (lowerPoint domain point)).decode
      (memberEquiv domain motive point (((upperMotive domain motive).model point).decode.symm ((J domain motive method).val point))) =
      (DisplayedPresheafIdentity.J domain.family motive.family method).val (lowerPoint domain point) := by
  apply (motive.model (lowerPoint domain point)).value_injective
  refine ((motive.model (lowerPoint domain point)).value_decode _).trans ?_
  apply HSet.lift_injective
  exact (member_value domain motive point (((upperMotive domain motive).model point).decode.symm ((J domain motive method).val point))).trans
    (J_value domain motive method point)

theorem J_naturality {point next : (upperContext domain).base.Elements} (step : point ⟶ next) :
    (upperMotive domain motive).family.map step ((J domain motive method).val point) = (J domain motive method).val next :=
  (J domain motive method).property step

theorem J_beta : PowerClassPresheafProducts.reindexSection
    (DisplayedPresheafIdentity.diagonal (ContextualSiteLiftMaterial.family domain).family) (upperMotive domain motive).family
    (J domain motive method) = DisplayedPresheafIdentitySiteLift.upperMethod original.base domain.family motive.family method :=
  DisplayedPresheafIdentity.J_beta _ _ _

section Substitution

variable {other : LabelledContext C} (change : NatTrans other.base original.base)

abbrev sourceDomain : MaterialFamily other := domain.reindex change

abbrev sourceMotive : MaterialFamily (upperContext (sourceDomain domain change)) :=
  (upperMotive domain motive).reindex (other := upperContext (sourceDomain domain change))
    (DisplayedPresheafIdentitySiteLift.identityChange original.base domain.family change)

def sourceMethod : (PowerClassPresheafProducts.reindex
    (DisplayedPresheafIdentity.diagonal (ContextualSiteLiftMaterial.family (sourceDomain domain change)).family)
      (sourceMotive domain motive change).family).sections :=
  DisplayedPresheafIdentitySiteLift.substitutedMethod original.base domain.family change
    (upperMotive domain motive).family (DisplayedPresheafIdentitySiteLift.upperMethod original.base domain.family motive.family method)

def sourceJ : (sourceMotive domain motive change).family.sections :=
  DisplayedPresheafIdentity.J (ContextualSiteLiftMaterial.family (sourceDomain domain change)).family
    (sourceMotive domain motive change).family (sourceMethod domain motive method change)

theorem J_substitution : PowerClassPresheafProducts.reindexSection
    (DisplayedPresheafIdentitySiteLift.identityChange original.base domain.family change) (upperMotive domain motive).family
    (J domain motive method) = sourceJ domain motive method change :=
  DisplayedPresheafIdentitySiteLift.J_substitution original.base domain.family change
    (upperMotive domain motive).family (DisplayedPresheafIdentitySiteLift.upperMethod original.base domain.family motive.family method)

/-- The motive after substitution uses the actual reindexed graph and
decoder. Its J value is the original complete material motive value. -/
theorem J_substitution_value (point : (upperContext (sourceDomain domain change)).base.Elements) :
    ((sourceMotive domain motive change).model point).value ((sourceJ domain motive method change).val point) =
      ((upperMotive domain motive).model
        ((PowerClassPresheafProducts.elementMap (DisplayedPresheafIdentitySiteLift.identityChange original.base domain.family change)).obj point)).value
        ((J domain motive method).val
          ((PowerClassPresheafProducts.elementMap (DisplayedPresheafIdentitySiteLift.identityChange original.base domain.family change)).obj point)) := by
  have terms := congrArg (fun term : (sourceMotive domain motive change).family.sections => term.val point)
    (J_substitution domain motive method change).symm
  exact congrArg ((sourceMotive domain motive change).model point).value terms

theorem J_substitution_beta : PowerClassPresheafProducts.reindexSection
    (DisplayedPresheafIdentity.diagonal (ContextualSiteLiftMaterial.family (sourceDomain domain change)).family)
    (sourceMotive domain motive change).family (sourceJ domain motive method change) = sourceMethod domain motive method change :=
  DisplayedPresheafIdentity.J_beta _ _ _

end Substitution

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialDisplayedIdentitySiteLift
