import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSiteLiftMaterial
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSiteLift

/-!
# Independently constructed material W formation on the successor site

The upper W carrier uses the actual labelled contextual-tree construction
with newly constructed successor context, arrow and fibre dictionaries. Its
encoded roots and all future rows are proved to be the material lifts of
the lower encoding. Thus the carrier, decoder and restriction comparisons
follow from an independent construction, rather than from relabelling the
lower W model as the target.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWSiteLift

open CategoryTheory
open Mettapedia.TypeTheory
open ContextualGeneratedUniverse
open ContextualWTypes (RawTree NaturalTree Position)

universe u
variable {C : Type u} [Category.{u} C] {original : LabelledContext C}
variable (domain : MaterialFamily original) (codomain : MaterialFamily domain.extension)
variable (arrowCoding : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev lowerPosition := PowerClassPresheafProducts.indexedBody domain.family codomain.family
abbrev upperDomain := ContextualSiteLiftMaterial.family domain
abbrev upperBody := ContextualSiteLiftMaterial.body domain codomain

abbrev oldPositions (point : domain.family.Elements) := codomain.model ⟨point.1.1, ⟨point.1.2, point.2⟩⟩
abbrev newPosition := PresheafSiteLift.body original.base domain.family (lowerPosition domain codomain)
abbrev newPositions (point : (upperDomain domain).family.Elements) :=
  (upperBody domain codomain).model ⟨point.1.1, ⟨point.1.2, point.2⟩⟩

def formed : MaterialFamily (ContextualSiteLiftMaterial.context original) where
  family := ContextualWTypes.family (upperDomain domain).family (newPosition domain codomain)
  model point := MaterialContextualWTypes.naturalModel (upperDomain domain).family (newPosition domain codomain)
    (ContextualSiteLiftMaterial.context original).labels
    (MaterialFamily.elementArrowCoding (context := ContextualSiteLiftMaterial.context original) (ContextualSiteLiftMaterial.arrows arrowCoding))
    (upperDomain domain).model (newPositions domain codomain) point

theorem formed_family : (formed domain codomain arrowCoding).family =
    ((upperDomain domain).w (upperBody domain codomain) (ContextualSiteLiftMaterial.arrows arrowCoding)).family :=
  congrArg (ContextualWTypes.family (upperDomain domain).family)
    (ContextualSiteLiftMaterial.indexed_body domain codomain).symm

theorem shape_tag (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (label : (upperDomain domain).family.obj point) :
    ContextualWLabels.shapeTag (ContextualSiteLiftMaterial.context original).labels point
      (((upperDomain domain).model point).value label) =
      HSet.lift (ContextualWLabels.shapeTag original.labels
        ((PresheafSiteLift.elementsDown original.base).obj point)
        ((domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).value label.down)) := by
  rw [ContextualWLabels.shapeTag, ContextualWLabels.shapeTag, HSet.lift_kpair, HSet.lift_empty, HSet.lift_kpair]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem position_tag (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (label : (upperDomain domain).family.obj point)
    (branch : ContextualWLabels.Branch (upperDomain domain).family (newPosition domain codomain) label) :
    ContextualWLabels.positionTag (upperDomain domain).family (newPosition domain codomain)
      (ContextualSiteLiftMaterial.context original).labels
      (MaterialFamily.elementArrowCoding (context := ContextualSiteLiftMaterial.context original) (ContextualSiteLiftMaterial.arrows arrowCoding))
      (upperDomain domain).model (newPositions domain codomain) ⟨point, label⟩ branch =
      HSet.lift (ContextualWLabels.positionTag domain.family (lowerPosition domain codomain)
        original.labels (MaterialFamily.elementArrowCoding (context := original) arrowCoding) domain.model (oldPositions domain codomain)
        ⟨(PresheafSiteLift.elementsDown original.base).obj point, label.down⟩
        ⟨(PresheafSiteLift.elementsDown original.base).obj branch.1,
          (PresheafSiteLift.elementsDown original.base).map branch.2.1, branch.2.2.down⟩) := by
  dsimp only [ContextualWLabels.positionTag]
  rw [ContextualWLabels.shapeCoding_reading, ContextualWLabels.shapeCoding_reading,
    ContextualWLabels.branchCoding_reading, ContextualWLabels.branchCoding_reading,
    HSet.lift_kpair, HSet.lift_singleton, HSet.lift_empty,
    HSet.lift_kpair, HSet.lift_kpair, HSet.lift_kpair, HSet.lift_kpair]
  rfl

abbrev lowerEncode {point : original.base.Elements} (tree : RawTree domain.family (lowerPosition domain codomain) point) :=
  MaterialContextualWTypes.encode domain.family (lowerPosition domain codomain)
    original.labels (MaterialFamily.elementArrowCoding (context := original) arrowCoding) domain.model (oldPositions domain codomain) tree

abbrev upperEncode {point : (ContextualSiteLiftMaterial.context original).base.Elements}
    (tree : RawTree (upperDomain domain).family (newPosition domain codomain) point) :=
  MaterialContextualWTypes.encode (upperDomain domain).family (newPosition domain codomain)
    (ContextualSiteLiftMaterial.context original).labels
    (MaterialFamily.elementArrowCoding (context := ContextualSiteLiftMaterial.context original) (ContextualSiteLiftMaterial.arrows arrowCoding))
    (upperDomain domain).model (newPositions domain codomain) tree

set_option backward.isDefEq.respectTransparency false in
theorem encode_lift {point : (ContextualSiteLiftMaterial.context original).base.Elements}
    (tree : RawTree (upperDomain domain).family (newPosition domain codomain) point) :
    upperEncode domain codomain arrowCoding tree =
      HSet.lift (lowerEncode domain codomain arrowCoding
        (ContextualWSiteLift.lowerRaw original.base domain.family (lowerPosition domain codomain) tree)) := by
  induction tree with
  | @sup point label children earlier =>
    apply HSet.ext
    intro root
    rw [MaterialContextualWTypes.mem_encode_sup_iff, HSet.mem_lift_iff]
    constructor
    · rintro (same | ⟨branch, same⟩)
      · refine ⟨HSet.kpair (ContextualWLabels.shapeTag original.labels
          ((PresheafSiteLift.elementsDown original.base).obj point)
          ((domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).value label.down)) ∅, ?_, ?_⟩
        · apply (MaterialContextualWTypes.mem_encode_sup_iff _ _ _ _ _ _ _ _ _).mpr
          exact Or.inl rfl
        · exact (HSet.lift_kpair _ _).trans
            ((congrArg₂ HSet.kpair (shape_tag domain point label).symm HSet.lift_empty).trans same.symm)
      · let oldBranch : ContextualWLabels.Branch domain.family (lowerPosition domain codomain) label.down :=
          ⟨(PresheafSiteLift.elementsDown original.base).obj branch.1,
            (PresheafSiteLift.elementsDown original.base).map branch.2.1, branch.2.2.down⟩
        refine ⟨HSet.kpair (ContextualWLabels.positionTag domain.family (lowerPosition domain codomain)
          original.labels (MaterialFamily.elementArrowCoding (context := original) arrowCoding) domain.model (oldPositions domain codomain)
          ⟨(PresheafSiteLift.elementsDown original.base).obj point, label.down⟩ oldBranch)
          (lowerEncode domain codomain arrowCoding
            (ContextualWSiteLift.lowerRaw original.base domain.family (lowerPosition domain codomain)
              (children branch.1 branch.2.1 branch.2.2))), ?_, ?_⟩
        · apply (MaterialContextualWTypes.mem_encode_sup_iff _ _ _ _ _ _ _ _ _).mpr
          exact Or.inr ⟨oldBranch, rfl⟩
        · exact (HSet.lift_kpair _ _).trans
            ((congrArg₂ HSet.kpair (position_tag domain codomain arrowCoding point label branch).symm
              (earlier branch.1 branch.2.1 branch.2.2).symm).trans same.symm)
    · rintro ⟨old, belongs, same⟩
      change old ∈ lowerEncode domain codomain arrowCoding (.sup label.down
        (fun next arrow branch => ContextualWSiteLift.lowerRaw original.base domain.family (lowerPosition domain codomain)
          (children ((PresheafSiteLift.elementsUp original.base).obj next)
            ((PresheafSiteLift.elementsUp original.base).map arrow) (ULift.up branch)))) at belongs
      rcases (MaterialContextualWTypes.mem_encode_sup_iff _ _ _ _ _ _ _ _ _).mp belongs with shapeRow | ⟨branch, childRow⟩
      · apply Or.inl
        exact same.symm.trans ((congrArg HSet.lift shapeRow).trans
          ((HSet.lift_kpair _ _).trans (congrArg₂ HSet.kpair (shape_tag domain point label).symm HSet.lift_empty)))
      · let newBranch : ContextualWLabels.Branch (upperDomain domain).family (newPosition domain codomain) label :=
          ⟨(PresheafSiteLift.elementsUp original.base).obj branch.1,
            (PresheafSiteLift.elementsUp original.base).map branch.2.1, ULift.up branch.2.2⟩
        refine Or.inr ⟨newBranch, ?_⟩
        exact same.symm.trans ((congrArg HSet.lift childRow).trans
          ((HSet.lift_kpair _ _).trans (congrArg₂ HSet.kpair
            (position_tag domain codomain arrowCoding point label newBranch).symm
            (earlier newBranch.1 newBranch.2.1 newBranch.2.2).symm)))

noncomputable def semanticEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    (formed domain codomain arrowCoding).family.obj point ≃
      (domain.w codomain arrowCoding).family.obj ((PresheafSiteLift.elementsDown original.base).obj point) :=
  ContextualWSiteLift.naturalEquiv original.base domain.family (lowerPosition domain codomain) point

theorem formed_value (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (tree : (formed domain codomain arrowCoding).family.obj point) :
    ((formed domain codomain arrowCoding).model point).value tree =
      HSet.lift (((domain.w codomain arrowCoding).model ((PresheafSiteLift.elementsDown original.base).obj point)).value
        (semanticEquiv domain codomain arrowCoding point tree)) := by
  change upperEncode domain codomain arrowCoding tree.val =
    HSet.lift (lowerEncode domain codomain arrowCoding (ContextualWSiteLift.lowerRaw original.base domain.family
      (lowerPosition domain codomain) tree.val))
  exact encode_lift domain codomain arrowCoding tree.val

theorem formed_carrier (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    ((formed domain codomain arrowCoding).model point).carrier =
      HSet.lift (((domain.w codomain arrowCoding).model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier) :=
  PresentedTypeCumulativity.carrier_eq_lift_of_values _ _ (semanticEquiv domain codomain arrowCoding point)
    (formed_value domain codomain arrowCoding point)

noncomputable def memberEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    {value : HSet.{u + 1} // value ∈ ((formed domain codomain arrowCoding).model point).carrier} ≃
      {value : HSet.{u} // value ∈ ((domain.w codomain arrowCoding).model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier} :=
  PresentedTypeCumulativity.memberEquiv _ _ (semanticEquiv domain codomain arrowCoding point)

theorem member_value (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain codomain arrowCoding).model point).carrier}) :
    HSet.lift (memberEquiv domain codomain arrowCoding point member).val = member.val :=
  PresentedTypeCumulativity.memberEquiv_value _ _ (semanticEquiv domain codomain arrowCoding point)
    (formed_value domain codomain arrowCoding point) member

theorem decoder (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain codomain arrowCoding).model point).carrier}) :
    ((domain.w codomain arrowCoding).model ((PresheafSiteLift.elementsDown original.base).obj point)).decode
      (memberEquiv domain codomain arrowCoding point member) =
      semanticEquiv domain codomain arrowCoding point (((formed domain codomain arrowCoding).model point).decode member) :=
  PresentedTypeCumulativity.decode_memberEquiv _ _ _ member

theorem term_graph (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (tree : (formed domain codomain arrowCoding).family.obj point) :
    ((formed domain codomain arrowCoding).model point).termGraph tree ≈
      (((domain.w codomain arrowCoding).model ((PresheafSiteLift.elementsDown original.base).obj point)).termGraph
        (semanticEquiv domain codomain arrowCoding point tree)).lift :=
  PresentedTypeCumulativity.termGraph_bisimilar _ _ (semanticEquiv domain codomain arrowCoding point)
    (formed_value domain codomain arrowCoding point) tree

theorem semantic_restriction {first second : (ContextualSiteLiftMaterial.context original).base.Elements}
    (arrow : first ⟶ second) (tree : (formed domain codomain arrowCoding).family.obj first) :
    semanticEquiv domain codomain arrowCoding second ((formed domain codomain arrowCoding).family.map arrow tree) =
      (domain.w codomain arrowCoding).family.map ((PresheafSiteLift.elementsDown original.base).map arrow)
        (semanticEquiv domain codomain arrowCoding first tree) :=
  Subtype.ext (ContextualWSiteLift.lower_restrict original.base domain.family (lowerPosition domain codomain) arrow tree.val)

set_option backward.isDefEq.respectTransparency false in
theorem member_restriction {first second : (ContextualSiteLiftMaterial.context original).base.Elements}
    (arrow : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain codomain arrowCoding).model first).carrier}) :
    memberEquiv domain codomain arrowCoding second ((formed domain codomain arrowCoding).memberRestriction arrow member) =
      (domain.w codomain arrowCoding).memberRestriction ((PresheafSiteLift.elementsDown original.base).map arrow)
        (memberEquiv domain codomain arrowCoding first member) := by
  apply ((domain.w codomain arrowCoding).model ((PresheafSiteLift.elementsDown original.base).obj second)).decode.injective
  rw [decoder, MaterialFamily.memberRestriction_decode, MaterialFamily.memberRestriction_decode, decoder]
  exact semantic_restriction domain codomain arrowCoding arrow (((formed domain codomain arrowCoding).model first).decode member)

namespace Growing

abbrev input := ContextualGeneratedUniverse.Growing.input
abbrev baseContext := ContextualGeneratedUniverse.Growing.context
abbrev arrows := ContextualGeneratedUniverse.Growing.arrowCoding
abbrev terminalBody := ContextualGeneratedUniverse.Growing.terminalBody
abbrev upperPoint (point : baseContext.base.Elements) := (PresheafSiteLift.elementsUp baseContext.base).obj point

noncomputable def cyclicLeaf : (formed input terminalBody arrows).family.obj
    (upperPoint ContextualGeneratedUniverse.Growing.later) :=
  (semanticEquiv input terminalBody arrows (upperPoint ContextualGeneratedUniverse.Growing.later)).symm
    (ContextualGeneratedUniverse.Growing.leaf ContextualGeneratedUniverse.Growing.later
      PowerClassContextualMaterialization.Growing.futureArgument)

theorem cyclic_leaf_member :
    ((formed input terminalBody arrows).model (upperPoint ContextualGeneratedUniverse.Growing.later)).value cyclicLeaf ∈
      ((formed input terminalBody arrows).model (upperPoint ContextualGeneratedUniverse.Growing.later)).carrier :=
  ((formed input terminalBody arrows).model _).value_mem cyclicLeaf

theorem cyclic_payload :
    ((upperDomain input).model (upperPoint ContextualGeneratedUniverse.Growing.later)).value
      (ULift.up PowerClassContextualMaterialization.Growing.futureArgument) = HSet.lift HSet.quineAtom :=
  congrArg HSet.lift ContextualGeneratedUniverse.Growing.cyclic_leaf_shape

theorem cyclic_leaf_value :
    ((formed input terminalBody arrows).model (upperPoint ContextualGeneratedUniverse.Growing.later)).value cyclicLeaf =
      HSet.lift (((input.w terminalBody arrows).model ContextualGeneratedUniverse.Growing.later).value
        (ContextualGeneratedUniverse.Growing.leaf ContextualGeneratedUniverse.Growing.later
          PowerClassContextualMaterialization.Growing.futureArgument)) := by
  exact (formed_value input terminalBody arrows _ cyclicLeaf).trans
    (congrArg (fun tree => HSet.lift (((input.w terminalBody arrows).model ContextualGeneratedUniverse.Growing.later).value tree))
      ((semanticEquiv input terminalBody arrows _).apply_symm_apply _))

theorem unary_empty (point : baseContext.base.Elements) :
    ((formed input ContextualGeneratedUniverse.Growing.unaryBody arrows).model (upperPoint point)).carrier = ∅ := by
  exact (formed_carrier input ContextualGeneratedUniverse.Growing.unaryBody arrows (upperPoint point)).trans
    ((congrArg HSet.lift (ContextualGeneratedUniverse.Growing.unary_w_empty point)).trans HSet.lift_empty)

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualWSiteLift
