import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftIdentity

/-!
# Full dependent J through the actual member and site inverses

An arbitrary natural motive on the larger identity context is pulled to
the original identity context through constructed maps. Its result universe
is independent of both member bounds. The reflexive method is transported
through the actual comprehension. The two independently formed dependent
eliminators agree, retaining both endpoints and the singleton witness.

This is the discrete model comparison. It neither installs native UIP or
reflection nor assumes an arbitrary upper motive has a lower presentation.
The actual set-model member recovery remains explicitly external Choice.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftIdentityElimination

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftFamilies
open HostChoiceContextualSetSiteLiftIdentity
open ContextualSmallFamilyComprehension

universe u v h a b c d
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (parent : NaturalHom P (lowerSets (D := D)))

private def pullSection {E : Type a} {F : Type b} [Category.{c} E] [Category.{d} F]
    (change : E ⥤ F) (family : F ⥤ Type h) (term : family.sections) :
    (PresheafSiteLift.compose change family).sections :=
  ⟨fun point => term.val (change.obj point), fun step => term.property (change.map step)⟩

private theorem sectionValue_heq {E : Type a} [Category.{b} E] (family : E ⥤ Type h)
    (term : family.sections) {first second : E} (same : first = second) :
    HEq (term.val first) (term.val second) := by
  cases same
  rfl

noncomputable def lowerIdentityFunctor : (upperContext parent).Elements ⥤ (lowerContext parent).Elements :=
  PresheafSiteLift.compose (ContextualSmallFamilyUniverse.elementMap (contextDown parent))
    (ContextualFutureSiteLift.elementsDown (lowerContext parent))

noncomputable def upperIdentityFunctor : (lowerContext parent).Elements ⥤ (upperContext parent).Elements :=
  PresheafSiteLift.compose (ContextualFutureSiteLift.elementsUp (lowerContext parent))
    (ContextualSmallFamilyUniverse.elementMap (contextUp parent))

theorem identity_roundtrip_point (point : (upperContext parent).Elements) :
    (upperIdentityFunctor parent).obj ((lowerIdentityFunctor parent).obj point) = point :=
  Sigma.ext rfl (heq_of_eq
    (congrArg (fun operation => operation.app point.1 point.2) (context_down_up parent)))

theorem lower_roundtrip_point (point : (lowerContext parent).Elements) :
    (lowerIdentityFunctor parent).obj ((upperIdentityFunctor parent).obj point) = point :=
  Sigma.ext rfl (heq_of_eq
    (congrArg (fun operation => operation.app (PresheafSiteLift.Site.upFunctor.obj point.1) point.2)
      (context_up_down parent)))

noncomputable def upperComprehensionFunctor :
    (HostChoiceContextualHypersetFamilyClosure.comprehension parent).Elements ⥤
      (ContextualSmallFamilyUniverse.total (upperDomain parent)).Elements :=
  PresheafSiteLift.compose
    (ContextualFutureSiteLift.elementsUp (HostChoiceContextualHypersetFamilyClosure.comprehension parent))
    (ContextualSmallFamilyUniverse.elementMap (comprehensionUp parent))

theorem readLeft_roundtrip_point (point : (upperContext parent).Elements) :
    (upperComprehensionFunctor parent).obj
        ((ContextualSmallFamilyUniverse.elementMap (ContextualSmallFamilyIdentity.readLeft (lowerDomain parent))).obj
          ((lowerIdentityFunctor parent).obj point)) =
      (ContextualSmallFamilyUniverse.elementMap (ContextualSmallFamilyIdentity.readLeft (upperDomain parent))).obj point := by
  refine Sigma.ext rfl ?_
  exact heq_of_eq (Sigma.ext rfl
    (heq_of_eq (member_up_down parent ⟨point.1, point.2.1.1.1⟩ point.2.1.1.2)))

variable (motive : (upperContext parent).Elements ⥤ Type h)

noncomputable def lowerMotive : (lowerContext parent).Elements ⥤ Type h :=
  PresheafSiteLift.compose (upperIdentityFunctor parent) motive

theorem motive_roundtrip :
    PresheafSiteLift.compose (lowerIdentityFunctor parent) (lowerMotive parent motive) = motive := by
  refine Functor.hext (fun point => congrArg motive.obj (identity_roundtrip_point parent point)) ?_
  intro first second step
  exact ContextualSmallFamilyUniverse.familyArrow_heq motive
    (identity_roundtrip_point parent first) (identity_roundtrip_point parent second) _ _
    (ContextualSmallFamilyUniverse.elementsArrow_heq
      (identity_roundtrip_point parent first) (identity_roundtrip_point parent second) _ _ HEq.rfl)

theorem reflexive_motive :
    PresheafSiteLift.compose (upperComprehensionFunctor parent)
      (ContextualSmallFamilyIdentity.reindex motive (ContextualSmallFamilyIdentity.diagonal (upperDomain parent))) =
    ContextualSmallFamilyIdentity.reindex (lowerMotive parent motive)
      (ContextualSmallFamilyIdentity.diagonal (lowerDomain parent)) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

variable (method : (ContextualSmallFamilyIdentity.reindex motive
  (ContextualSmallFamilyIdentity.diagonal (upperDomain parent))).sections)

noncomputable def lowerMethod : (ContextualSmallFamilyIdentity.reindex (lowerMotive parent motive)
    (ContextualSmallFamilyIdentity.diagonal (lowerDomain parent))).sections :=
  sectionCast (reflexive_motive parent motive)
    (pullSection (upperComprehensionFunctor parent)
      (ContextualSmallFamilyIdentity.reindex motive (ContextualSmallFamilyIdentity.diagonal (upperDomain parent))) method)

theorem J_value_comparison (point : (upperContext parent).Elements) :
    HEq ((ContextualSmallFamilyIdentity.J (upperDomain parent) motive method).val point)
      ((ContextualSmallFamilyIdentity.J (lowerDomain parent) (lowerMotive parent motive)
        (lowerMethod parent motive method)).val ((lowerIdentityFunctor parent).obj point)) := by
  have upper := ContextualSmallFamilyIdentity.J_value_heq (upperDomain parent) motive method point
  have lower := ContextualSmallFamilyIdentity.J_value_heq (lowerDomain parent) (lowerMotive parent motive)
    (lowerMethod parent motive method) ((lowerIdentityFunctor parent).obj point)
  have castMethod := sectionCast_value (reflexive_motive parent motive)
    (pullSection (upperComprehensionFunctor parent)
      (ContextualSmallFamilyIdentity.reindex motive (ContextualSmallFamilyIdentity.diagonal (upperDomain parent))) method)
    ((ContextualSmallFamilyUniverse.elementMap (ContextualSmallFamilyIdentity.readLeft (lowerDomain parent))).obj
      ((lowerIdentityFunctor parent).obj point))
  have methods := sectionValue_heq
    (ContextualSmallFamilyIdentity.reindex motive (ContextualSmallFamilyIdentity.diagonal (upperDomain parent)))
    method (readLeft_roundtrip_point parent point)
  exact upper.trans (methods.symm.trans (castMethod.symm.trans lower.symm))

set_option maxHeartbeats 2000000 in
theorem J_comparison : ContextualSmallFamilyIdentity.J (upperDomain parent) motive method =
    sectionCast (motive_roundtrip parent motive)
      (pullSection (lowerIdentityFunctor parent) (lowerMotive parent motive)
        (ContextualSmallFamilyIdentity.J (lowerDomain parent) (lowerMotive parent motive)
          (lowerMethod parent motive method))) := by
  apply Subtype.ext
  funext point
  apply eq_of_heq
  exact (J_value_comparison parent motive method point).trans
    (sectionCast_value (motive_roundtrip parent motive)
      (pullSection (lowerIdentityFunctor parent) (lowerMotive parent motive)
        (ContextualSmallFamilyIdentity.J (lowerDomain parent) (lowerMotive parent motive)
          (lowerMethod parent motive method))) point).symm

theorem J_beta_comparison :
    ContextualSmallFamilyIdentity.reindexSection (ContextualSmallFamilyIdentity.diagonal (upperDomain parent)) motive
      (sectionCast (motive_roundtrip parent motive)
        (pullSection (lowerIdentityFunctor parent) (lowerMotive parent motive)
          (ContextualSmallFamilyIdentity.J (lowerDomain parent) (lowerMotive parent motive)
            (lowerMethod parent motive method)))) = method := by
  rw [← J_comparison]
  exact ContextualSmallFamilyIdentity.J_beta (upperDomain parent) motive method

theorem J_comparison_substitution
    {other : UpperSite (D := D) ⥤ Type a}
    (change : NaturalHom other (ContextualFutureSiteLift.base P)) :
    ContextualSmallFamilyIdentity.reindexSection
        (ContextualSmallFamilyIdentity.identityReindex change (upperDomain parent)) motive
        (sectionCast (motive_roundtrip parent motive)
          (pullSection (lowerIdentityFunctor parent) (lowerMotive parent motive)
            (ContextualSmallFamilyIdentity.J (lowerDomain parent) (lowerMotive parent motive)
              (lowerMethod parent motive method)))) =
      ContextualSmallFamilyIdentity.J (ContextualSmallFamilyIdentity.reindex (upperDomain parent) change)
        (ContextualSmallFamilyIdentity.reindex motive
          (ContextualSmallFamilyIdentity.identityReindex change (upperDomain parent)))
        (ContextualSmallFamilyIdentity.reindexMethod change (upperDomain parent) motive method) := by
  rw [← J_comparison]
  exact ContextualSmallFamilyIdentity.J_substitution change (upperDomain parent) motive method

theorem J_beta_comparison_substitution
    {other : UpperSite (D := D) ⥤ Type a}
    (change : NaturalHom other (ContextualFutureSiteLift.base P)) :
    ContextualSmallFamilyIdentity.reindexSection
      (ContextualSmallFamilyIdentity.diagonal (ContextualSmallFamilyIdentity.reindex (upperDomain parent) change))
      (ContextualSmallFamilyIdentity.reindex motive
        (ContextualSmallFamilyIdentity.identityReindex change (upperDomain parent)))
      (ContextualSmallFamilyIdentity.reindexSection
        (ContextualSmallFamilyIdentity.identityReindex change (upperDomain parent)) motive
        (sectionCast (motive_roundtrip parent motive)
          (pullSection (lowerIdentityFunctor parent) (lowerMotive parent motive)
            (ContextualSmallFamilyIdentity.J (lowerDomain parent) (lowerMotive parent motive)
              (lowerMethod parent motive method))))) =
      ContextualSmallFamilyIdentity.reindexMethod change (upperDomain parent) motive method := by
  rw [J_comparison_substitution]
  exact ContextualSmallFamilyIdentity.J_beta _ _ _

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftIdentityElimination
