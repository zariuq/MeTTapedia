import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyControls

/-!
# Varying dependent identity with material collision controls

The endpoint motive ranges over the strictly growing receipt family.
Its material body is cyclic at zero and terminal at positive receipts.
Dependent J retains this varying reading. Two distinct positive receipts
have matching material bodies but their native discrete identity carrier
has no member.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyIdentityControls

open CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover
open ContextualSmallFamilyUniverse ContextualSmallFamilyIdentity
open ContextualGraphDiagrams ContextualRealizedGraphs
open ContextualGraphFamilyBodies ContextualGraphFamilyBodySubstitution
open ContextualGraphFamilyBodyIdentity
open ContextualGraphFamilyControls (unitBase growing parameter)
open ContextualGraphFamilyBodyControls (reading material attached retained)

abbrev motive := endpointMotive growing

def motiveReading : NaturalHom (total motive) (values Nat) :=
  readingUnder (secondFamily growing) (readingUnder growing reading (projection growing)) (readLeft growing)

def method : (literal (methodFamily growing motive) (methodReading growing motive motiveReading)).sections :=
  (sectionDecoder _ _).symm (endpointMethod growing)

def result : (literal motive motiveReading).sections := receiptJ growing motive motiveReading method

theorem J_decodes_endpoint (point : (identityContext growing).Elements) :
    decode motive motiveReading point (result.val point) = point.2.1.1.2 := by
  have square := receiptJ_native growing motive motiveReading method
  exact (congrArg (fun term => term.val point) square).trans (J_endpoint_value growing point)

def J_retains_endpoint_body (point : (identityContext growing).Elements) :
    Equal (material point.1 point.2.1.1.2)
      ((ContextualGraphReceiptFamilies.sectionReading (parent motive motiveReading) result).app point.1 point.2) :=
  (Equal.ofEq (congrArg (material point.1) (J_decodes_endpoint point).symm)).trans
    (ContextualGraphFamilyBodyComparison.sectionComparison motive motiveReading result point)

def endpointPoint (stage : Nat) (term : Fin (stage+1)) : (identityContext growing).Elements :=
  ⟨stage, ⟨⟨⟨PUnit.unit, term⟩, term⟩, PresheafIdentityWitness.encode rfl⟩⟩

theorem J_material_is_nonconstant :
    ¬ Nonempty (Equal
      ((ContextualGraphReceiptFamilies.sectionReading (parent motive motiveReading) result).app 1
        (endpointPoint 1 ⟨0, by decide⟩).2)
      ((ContextualGraphReceiptFamilies.sectionReading (parent motive motiveReading) result).app 1
        (endpointPoint 1 ⟨1, by decide⟩).2)) := by
  rintro ⟨same⟩
  have original := (J_retains_endpoint_body (endpointPoint 1 ⟨0, by decide⟩)).trans
    (same.trans (J_retains_endpoint_body (endpointPoint 1 ⟨1, by decide⟩)).symm)
  exact (by decide : ¬ (1 : Nat) = 0)
    (ContextualGraphFamilyBodyControls.matching_preserves_zero 1 _ _ original rfl)

theorem matching_does_not_form_identity :
    Nonempty (Equal (attached 2 ⟨1, by decide⟩) (attached 2 ⟨2, by decide⟩)) ∧
      ¬ ∃ element : Value Nat 2, Nonempty (Member element
        (identityCarrier (literal growing reading) (parameter 2)
          (retained 2 ⟨1, by decide⟩) (retained 2 ⟨2, by decide⟩))) :=
  ⟨ContextualGraphFamilyBodyControls.positive_bodies_match,
    fun belongs => ContextualGraphFamilyBodyControls.positive_receipts_distinct
      ((identity_material_nonempty_iff (literal growing reading) (parameter 2) _ _).mp belongs)⟩

def reflexive_identity_member (point : unitBase.Elements) (term : growing.obj point) :
    Member (witnessValue point.1) (identityCarrier growing point term term) :=
  ContextualGraphFamilyBodyComparison.memberIntro (witnessFamily growing) (witnessReading growing)
    ⟨point.1, ⟨⟨point.2, term⟩, term⟩⟩ _ (PresheafIdentityWitness.encode rfl) (Equal.refl _)

theorem J_computation :
    substituteSection motive motiveReading (diagonal growing) result = method :=
  receiptJ_beta growing motive motiveReading method

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGraphFamilyBodyIdentityControls
