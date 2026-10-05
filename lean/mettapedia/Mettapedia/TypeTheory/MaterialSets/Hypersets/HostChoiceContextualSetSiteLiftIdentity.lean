import Mettapedia.TypeTheory.ContextualSmallFamilyIdentityExt
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftFamilies

/-!
# Actual discrete identity contexts across the larger set model

The two endpoint values and their constructed singleton witness are raised
and recovered together. Their natural inverse context maps commute with
the actual comprehension and reflexivity diagonal. This comparison is
the local discrete identity interpretation; it does not impose native UIP
or reflection or erase proof-relevant identity interpretations.

The model member inverse has the external Choice dependency already named
by the actual set-model lift.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftIdentity

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftFamilies

universe u v h
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (parent : NaturalHom P (lowerSets (D := D)))

noncomputable abbrev lowerContext := ContextualSmallFamilyIdentity.identityContext (lowerDomain parent)
noncomputable abbrev upperContext := ContextualSmallFamilyIdentity.identityContext (upperDomain parent)

noncomputable def memberUp (point : (ContextualFutureSiteLift.base P).Elements)
    (code : (lowerDomain parent).obj ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    (upperDomain parent).obj point := domainEquiv parent point (ULift.up code)

noncomputable def memberDown (point : (ContextualFutureSiteLift.base P).Elements)
    (code : (upperDomain parent).obj point) :
    (lowerDomain parent).obj ((ContextualFutureSiteLift.elementsDown P).obj point) :=
  ((domainEquiv parent point).symm code).down

theorem member_down_up (point : (ContextualFutureSiteLift.base P).Elements)
    (code : (lowerDomain parent).obj ((ContextualFutureSiteLift.elementsDown P).obj point)) :
    memberDown parent point (memberUp parent point code) = code :=
  congrArg ULift.down ((domainEquiv parent point).symm_apply_apply (ULift.up code))

theorem member_up_down (point : (ContextualFutureSiteLift.base P).Elements)
    (code : (upperDomain parent).obj point) : memberUp parent point (memberDown parent point code) = code :=
  (domainEquiv parent point).apply_symm_apply code

theorem member_up_natural {first second : (ContextualFutureSiteLift.base P).Elements}
    (step : first ⟶ second) (code : (lowerDomain parent).obj ((ContextualFutureSiteLift.elementsDown P).obj first)) :
    (upperDomain parent).map step (memberUp parent first code) =
      memberUp parent second ((lowerDomain parent).map ((ContextualFutureSiteLift.elementsDown P).map step) code) :=
  domain_natural parent step (ULift.up code)

theorem member_down_natural {first second : (ContextualFutureSiteLift.base P).Elements}
    (step : first ⟶ second) (code : (upperDomain parent).obj first) :
    (lowerDomain parent).map ((ContextualFutureSiteLift.elementsDown P).map step) (memberDown parent first code) =
      memberDown parent second ((upperDomain parent).map step code) := by
  exact congrArg ULift.down ((domainBackward parent).naturality step code)

noncomputable def contextUp : NaturalHom (ContextualFutureSiteLift.base (lowerContext parent)) (upperContext parent) where
  app point receipt :=
    ⟨⟨⟨receipt.1.1.1, memberUp parent ⟨point, receipt.1.1.1⟩ receipt.1.1.2⟩,
      memberUp parent ⟨point, receipt.1.1.1⟩ receipt.1.2⟩,
      PresheafIdentityWitness.encode (congrArg (memberUp parent ⟨point, receipt.1.1.1⟩)
        (PresheafIdentityWitness.decode receipt.2))⟩
  naturality {first second} step receipt := by
    apply ContextualSmallFamilyIdentity.receipt_ext (upperDomain parent)
    · rfl
    · exact heq_of_eq (member_up_natural parent
        (CategoryOfElements.homMk (F := ContextualFutureSiteLift.base P)
          ⟨first, receipt.1.1.1⟩ ⟨second, P.map step.down receipt.1.1.1⟩ step rfl) receipt.1.1.2)
    · exact heq_of_eq (member_up_natural parent
        (CategoryOfElements.homMk (F := ContextualFutureSiteLift.base P)
          ⟨first, receipt.1.1.1⟩ ⟨second, P.map step.down receipt.1.1.1⟩ step rfl) receipt.1.2)

noncomputable def contextDown : NaturalHom (upperContext parent) (ContextualFutureSiteLift.base (lowerContext parent)) where
  app point receipt :=
    ⟨⟨⟨receipt.1.1.1, memberDown parent ⟨point, receipt.1.1.1⟩ receipt.1.1.2⟩,
      memberDown parent ⟨point, receipt.1.1.1⟩ receipt.1.2⟩,
      PresheafIdentityWitness.encode (congrArg (memberDown parent ⟨point, receipt.1.1.1⟩)
        (PresheafIdentityWitness.decode receipt.2))⟩
  naturality {first second} step receipt := by
    apply ContextualSmallFamilyIdentity.receipt_ext (lowerDomain parent)
    · rfl
    · exact heq_of_eq (member_down_natural parent
        (CategoryOfElements.homMk (F := ContextualFutureSiteLift.base P)
          ⟨first, receipt.1.1.1⟩ ⟨second, P.map step.down receipt.1.1.1⟩ step rfl) receipt.1.1.2)
    · exact heq_of_eq (member_down_natural parent
        (CategoryOfElements.homMk (F := ContextualFutureSiteLift.base P)
          ⟨first, receipt.1.1.1⟩ ⟨second, P.map step.down receipt.1.1.1⟩ step rfl) receipt.1.2)

theorem context_up_down : (contextUp parent).comp (contextDown parent) =
    ContextualSmallMapConstructions.identity (ContextualFutureSiteLift.base (lowerContext parent)) := by
  apply NaturalHom.ext
  intro point receipt
  apply ContextualSmallFamilyIdentity.receipt_ext (lowerDomain parent)
  · rfl
  · exact heq_of_eq (member_down_up parent ⟨point, receipt.1.1.1⟩ receipt.1.1.2)
  · exact heq_of_eq (member_down_up parent ⟨point, receipt.1.1.1⟩ receipt.1.2)

theorem context_down_up : (contextDown parent).comp (contextUp parent) =
    ContextualSmallMapConstructions.identity (upperContext parent) := by
  apply NaturalHom.ext
  intro point receipt
  apply ContextualSmallFamilyIdentity.receipt_ext (upperDomain parent)
  · rfl
  · exact heq_of_eq (member_up_down parent ⟨point, receipt.1.1.1⟩ receipt.1.1.2)
  · exact heq_of_eq (member_up_down parent ⟨point, receipt.1.1.1⟩ receipt.1.2)

noncomputable def contextEquiv (point : UpperSite (D := D)) :
    (ContextualFutureSiteLift.base (lowerContext parent)).obj point ≃ (upperContext parent).obj point where
  toFun := (contextUp parent).app point
  invFun := (contextDown parent).app point
  left_inv receipt := congrArg (fun operation => operation.app point receipt) (context_up_down parent)
  right_inv receipt := congrArg (fun operation => operation.app point receipt) (context_down_up parent)

noncomputable def raisedDiagonal : NaturalHom
    (ContextualFutureSiteLift.base (HostChoiceContextualHypersetFamilyClosure.comprehension parent))
    (ContextualFutureSiteLift.base (lowerContext parent)) where
  app point := (ContextualSmallFamilyIdentity.diagonal (lowerDomain parent)).app point.down
  naturality step := (ContextualSmallFamilyIdentity.diagonal (lowerDomain parent)).naturality step.down

noncomputable def raisedReadLeft : NaturalHom
    (ContextualFutureSiteLift.base (lowerContext parent))
    (ContextualFutureSiteLift.base (HostChoiceContextualHypersetFamilyClosure.comprehension parent)) where
  app point := (ContextualSmallFamilyIdentity.readLeft (lowerDomain parent)).app point.down
  naturality step := (ContextualSmallFamilyIdentity.readLeft (lowerDomain parent)).naturality step.down

theorem diagonal_up : (raisedDiagonal parent).comp (contextUp parent) =
    (comprehensionUp parent).comp (ContextualSmallFamilyIdentity.diagonal (upperDomain parent)) := by
  apply NaturalHom.ext
  intro point receipt
  apply ContextualSmallFamilyIdentity.receipt_ext (upperDomain parent) <;> rfl

theorem diagonal_down : (ContextualSmallFamilyIdentity.diagonal (upperDomain parent)).comp (contextDown parent) =
    (comprehensionDown parent).comp (raisedDiagonal parent) := by
  apply NaturalHom.ext
  intro point receipt
  apply ContextualSmallFamilyIdentity.receipt_ext (lowerDomain parent) <;> rfl

theorem readLeft_up : (contextUp parent).comp (ContextualSmallFamilyIdentity.readLeft (upperDomain parent)) =
    (raisedReadLeft parent).comp (comprehensionUp parent) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem readLeft_down : (ContextualSmallFamilyIdentity.readLeft (upperDomain parent)).comp (comprehensionDown parent) =
    (contextDown parent).comp (raisedReadLeft parent) := by
  apply NaturalHom.ext
  intro _ _
  rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftIdentity
