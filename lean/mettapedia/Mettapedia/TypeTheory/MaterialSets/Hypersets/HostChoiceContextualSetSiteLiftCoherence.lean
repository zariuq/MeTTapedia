import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetModel
import Mettapedia.TypeTheory.WiderPresheafDependentFunctions

/-!
# Actual member decoding across the contextual set-model lift

An embedded parent has exactly the embedded original members. The forward
member map is injective and surjective. Its explicitly named host selection
constructs an inverse, and both inverse laws retain actual child values.
The independently chosen native member families are then compared through
these literal members, not by identifying their representation codes.

The forward and inverse code maps are natural across actual raised-site
arrows and induce whole compatible-section inverses. Over embedded parents
the original Type-u member carrier remains sufficient, although the upper
model's arbitrary member families use the successor bound. External host
Choice is inherited and also explicitly used by the member recovery.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftCoherence

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetInterpretation

universe u v w
variable {D : Type u} [Category.{u} D]

abbrev LowerMember (point : UpperSite (D := D)) (parent : source.obj point) :=
  {child : source.obj point // Member point.down child parent}

abbrev UpperMember (point : UpperSite (D := D)) (parent : source.obj point) :=
  {child : upperSets.obj point // Member point child (embedding.app point parent)}

noncomputable def memberForward (point : UpperSite (D := D)) (parent : source.obj point)
    (member : LowerMember point parent) : UpperMember point parent :=
  ⟨embedding.app point member.val, (current_member_embedding_iff point parent member.val).mpr member.property⟩

theorem memberForward_injective (point : UpperSite (D := D)) (parent : source.obj point) :
    Function.Injective (memberForward point parent) := by
  intro first second same
  exact Subtype.ext (embedding_injective point (congrArg Subtype.val same))

theorem memberForward_surjective (point : UpperSite (D := D)) (parent : source.obj point) :
    Function.Surjective (memberForward point parent) := by
  intro member
  obtain ⟨original, same, belongs⟩ := (current_member_image point parent member.val).mp member.property
  exact ⟨⟨original, belongs⟩, Subtype.ext same⟩

/-- This inverse uses explicit external host selection from the proved
surjection. It is not obtained from a propositional cover in the pure model. -/
noncomputable def selectedMemberRecovery (point : UpperSite (D := D)) (parent : source.obj point)
    (member : UpperMember point parent) : LowerMember point parent :=
  Classical.choose (memberForward_surjective point parent member)

theorem selectedMemberRecovery_forward (point : UpperSite (D := D)) (parent : source.obj point)
    (member : UpperMember point parent) :
    memberForward point parent (selectedMemberRecovery point parent member) = member :=
  Classical.choose_spec (memberForward_surjective point parent member)

noncomputable def memberEquiv (point : UpperSite (D := D)) (parent : source.obj point) :
    LowerMember point parent ≃ UpperMember point parent where
  toFun := memberForward point parent
  invFun := selectedMemberRecovery point parent
  left_inv member := memberForward_injective point parent
    (selectedMemberRecovery_forward point parent (memberForward point parent member))
  right_inv := selectedMemberRecovery_forward point parent

theorem memberEquiv_value (point : UpperSite (D := D)) (parent : source.obj point)
    (member : LowerMember point parent) :
    (memberEquiv point parent member).val = embedding.app point member.val := rfl

theorem memberEquiv_inverse_value (point : UpperSite (D := D)) (parent : source.obj point)
    (member : UpperMember point parent) :
    embedding.app point ((memberEquiv point parent).symm member).val = member.val :=
  congrArg Subtype.val ((memberEquiv point parent).apply_symm_apply member)

def lowerContext : (source (D := D)).Elements ⥤ (lowerSets (D := D)).Elements where
  obj point := ⟨point.1.down, point.2⟩
  map step := ⟨step.1.down, step.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def upperContext : (source (D := D)).Elements ⥤ (upperSets (D := D)).Elements :=
  ContextualSmallFamilyUniverse.elementMap (embedding (D := D))

noncomputable def lowerNative : (source (D := D)).Elements ⥤ Type u :=
  PresheafSiteLift.compose lowerContext (HostChoiceContextualHypersetModel.memberFamily (D := D))

noncomputable def upperNative : (source (D := D)).Elements ⥤ Type (u+1) :=
  PresheafSiteLift.compose upperContext
    (HostChoiceContextualHypersetModel.memberFamily (D := UpperSite (D := D)))

noncomputable def codeEquiv (point : (source (D := D)).Elements) :
    lowerNative.obj point ≃ upperNative.obj point :=
  (HostChoiceContextualHypersetModel.memberDecoder (lowerContext.obj point)).trans
    ((memberEquiv point.1 point.2).trans
      (HostChoiceContextualHypersetModel.memberDecoder (upperContext.obj point)).symm)

theorem code_value (point : (source (D := D)).Elements) (code : lowerNative.obj point) :
    embedding.app point.1 (HostChoiceContextualHypersetModel.memberDecoder (lowerContext.obj point) code).val =
      (HostChoiceContextualHypersetModel.memberDecoder (upperContext.obj point) (codeEquiv point code)).val :=
  (congrArg Subtype.val
    ((HostChoiceContextualHypersetModel.memberDecoder (upperContext.obj point)).apply_symm_apply
      (memberEquiv point.1 point.2
        (HostChoiceContextualHypersetModel.memberDecoder (lowerContext.obj point) code)))).symm

set_option maxHeartbeats 1000000 in
theorem code_natural {first second : (source (D := D)).Elements} (step : first ⟶ second)
    (code : lowerNative.obj first) :
    upperNative.map step (codeEquiv first code) = codeEquiv second (lowerNative.map step code) := by
  apply (HostChoiceContextualHypersetModel.memberDecoder (upperContext.obj second)).injective
  apply Subtype.ext
  have upperMoved := HostChoiceContextualHypersetModel.memberDecoder_restriction_value
    (upperContext.map step) (codeEquiv first code)
  have firstValue := code_value first code
  have secondValue := code_value second (lowerNative.map step code)
  have lowerMoved := HostChoiceContextualHypersetModel.memberDecoder_restriction_value
    (lowerContext.map step) code
  have natural := (embedding (D := D)).naturality step.1
    (HostChoiceContextualHypersetModel.memberDecoder (lowerContext.obj first) code).val
  exact upperMoved.symm.trans
    ((congrArg ((upperSets (D := D)).map step.1) firstValue.symm).trans
      (natural.trans ((congrArg ((embedding (D := D)).app second.1) lowerMoved).trans secondValue)))

set_option maxHeartbeats 1000000 in
noncomputable def forward : WiderPresheafDependentFunctions.Hom (lowerNative (D := D)) upperNative where
  app point code := codeEquiv point code
  naturality step code := code_natural step code

noncomputable def backward : WiderPresheafDependentFunctions.Hom (upperNative (D := D)) lowerNative where
  app point := (codeEquiv point).symm
  naturality {first second} step code := by
    apply (codeEquiv second).injective
    exact (code_natural step ((codeEquiv first).symm code)).symm.trans
      ((congrArg (upperNative.map step) ((codeEquiv first).apply_symm_apply code)).trans
        ((codeEquiv second).apply_symm_apply (upperNative.map step code)).symm)

theorem forward_backward : (forward (D := D)).comp backward =
    WiderPresheafDependentFunctions.Hom.identity lowerNative := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point code
  exact (codeEquiv point).symm_apply_apply code

theorem backward_forward : (backward (D := D)).comp forward =
    WiderPresheafDependentFunctions.Hom.identity upperNative := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point code
  exact (codeEquiv point).apply_symm_apply code

noncomputable def sections : (lowerNative (D := D)).sections ≃ (upperNative (D := D)).sections where
  toFun := forward.mapSection
  invFun := backward.mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (codeEquiv point).symm_apply_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (codeEquiv point).apply_symm_apply (term.val point)

theorem section_value (term : (lowerNative (D := D)).sections) (point : source.Elements) :
    embedding.app point.1 (HostChoiceContextualHypersetModel.memberDecoder (lowerContext.obj point) (term.val point)).val =
      (HostChoiceContextualHypersetModel.memberDecoder (upperContext.obj point) ((sections term).val point)).val :=
  code_value point (term.val point)

variable {parameters : UpperSite (D := D) ⥤ Type v}
variable (parent : NaturalHom parameters source)

noncomputable def lowerUnder : parameters.Elements ⥤ Type u :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.elementMap parent) lowerNative

noncomputable def upperUnder : parameters.Elements ⥤ Type (u+1) :=
  ContextualSmallFamilyUniverse.restrict (ContextualSmallFamilyUniverse.elementMap parent) upperNative

noncomputable def forwardUnder : WiderPresheafDependentFunctions.Hom (lowerUnder parent) (upperUnder parent) where
  app point := codeEquiv ((ContextualSmallFamilyUniverse.elementMap parent).obj point)
  naturality step code := code_natural ((ContextualSmallFamilyUniverse.elementMap parent).map step) code

noncomputable def backwardUnder : WiderPresheafDependentFunctions.Hom (upperUnder parent) (lowerUnder parent) where
  app point := backward.app ((ContextualSmallFamilyUniverse.elementMap parent).obj point)
  naturality step code := backward.naturality ((ContextualSmallFamilyUniverse.elementMap parent).map step) code

theorem parameter_value_square (point : parameters.Elements) (code : (lowerUnder parent).obj point) :
    embedding.app point.1
      (HostChoiceContextualHypersetModel.memberDecoder
        (lowerContext.obj ((ContextualSmallFamilyUniverse.elementMap parent).obj point)) code).val =
      (HostChoiceContextualHypersetModel.memberDecoder
        (upperContext.obj ((ContextualSmallFamilyUniverse.elementMap parent).obj point))
        ((forwardUnder parent).app point code)).val :=
  code_value ((ContextualSmallFamilyUniverse.elementMap parent).obj point) code

theorem forwardUnder_backwardUnder : (forwardUnder parent).comp (backwardUnder parent) =
    WiderPresheafDependentFunctions.Hom.identity (lowerUnder parent) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point code
  exact (codeEquiv ((ContextualSmallFamilyUniverse.elementMap parent).obj point)).symm_apply_apply code

theorem backwardUnder_forwardUnder : (backwardUnder parent).comp (forwardUnder parent) =
    WiderPresheafDependentFunctions.Hom.identity (upperUnder parent) := by
  apply WiderPresheafDependentFunctions.Hom.ext
  intro point code
  exact (codeEquiv ((ContextualSmallFamilyUniverse.elementMap parent).obj point)).apply_symm_apply code

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftCoherence
