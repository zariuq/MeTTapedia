import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWSignature
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialEquivalence

/-!
# Actual contextual material W signature equivalences

Natural material domain and dependent-body equivalences construct the
position transports used by indexed tree recursion. Both directions retain
the same context, every actual future arrow and the complete material shape
and position values. Preservation of the actual faithful tree encodings
proves the inverse laws; neither a W comparison nor its inverse is supplied.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialWEquivalence

open CategoryTheory ContextualGeneratedUniverse ContextualMaterialEquivalence
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open ContextualWTypes (RawTree Position Natural NaturalTree)

universe u
variable {C : Type u} [Category.{u} C] {context : LabelledContext C}
variable {first second : MaterialFamily context}
variable (domain : Equivalence first second)
variable {left : MaterialFamily first.extension} {right : MaterialFamily second.extension}
variable (body : Equivalence left (right.reindex (other := first.extension) domain.comprehension))

abbrev leftPosition := PowerClassPresheafProducts.indexedBody first.family left.family
abbrev rightPosition := PowerClassPresheafProducts.indexedBody second.family right.family

private theorem arrow_heq {P : Cᵒᵖ ⥤ Type u}
    {first first' next next' : P.Elements} (sources : first = first') (targets : next = next')
    (earlier : first ⟶ next) (later : first' ⟶ next') (arrows : HEq earlier.1 later.1) : HEq earlier later := by
  cases sources
  cases targets
  exact heq_of_eq (Subtype.ext (eq_of_heq arrows))

private theorem map_heq {D : Type u} [Category.{u} D] (family : D ⥤ Type u)
    {first first' next next' : D} (sources : first = first') (targets : next = next')
    (earlier : first ⟶ next) (later : first' ⟶ next') (arrows : HEq earlier later)
    (member : family.obj first) (member' : family.obj first') (members : HEq member member') :
    HEq (family.map earlier member) (family.map later member') := by
  cases sources
  cases targets
  cases eq_of_heq arrows
  cases eq_of_heq members
  rfl

/-- The generic position naturality is derived from the actual body action
on the two comprehension contexts and their underlying arrows. -/
def signature : ContextualWSignature.Signature
    (shape := first.family) (nextShape := second.family)
    (position := leftPosition (left := left)) (nextPosition := rightPosition (right := right)) where
  shapes := domain.fibre
  shape_natural := domain.naturality
  positions point label := body.fibre ⟨point.1, ⟨point.2, label⟩⟩
  position_natural {point next} step label branch := by
    let start : first.extension.base.Elements := ⟨point.1, ⟨point.2, label⟩⟩
    let finish : first.extension.base.Elements := ⟨next.1, ⟨next.2, first.family.map step label⟩⟩
    let bodyStep : start ⟶ finish :=
      (Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements first.family).map
        (argumentMap first.family step label)
    have preserved := body.naturality bodyStep branch
    have targets : (PowerClassPresheafProducts.elementMap domain.comprehension).obj finish =
        (⟨next.1, ⟨next.2, second.family.map step (domain.fibre point label)⟩⟩ : second.extension.base.Elements) :=
      congrArg (fun argument => (⟨next.1, ⟨next.2, argument⟩⟩ : second.extension.base.Elements))
        (domain.naturality step label)
    let targetStep :=
      (Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements second.family).map
        (argumentMap second.family step (domain.fibre point label))
    have underlying : ((PowerClassPresheafProducts.elementMap domain.comprehension).map bodyStep).1 = targetStep.1 := by
      change ((Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements first.family).map
        (argumentMap first.family step label)).1 =
        ((Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements second.family).map
          (argumentMap second.family step (domain.fibre point label))).1
      rw [Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements_underlying,
        Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements_underlying]
      rfl
    have arrows := arrow_heq rfl targets
      ((PowerClassPresheafProducts.elementMap domain.comprehension).map bodyStep) targetStep (heq_of_eq underlying)
    exact (heq_of_eq preserved).trans (map_heq right.family rfl targets _ _ arrows _ _ (heq_of_eq rfl))

/-- The reverse dependent signature is constructed by actual inverse
comprehension reindexing and the proved whole-family round trip. -/
def bodyBackward : Equivalence right (left.reindex (other := second.extension) domain.comprehensionInverse) :=
  ((body.reindex (other := second.extension) domain.comprehensionInverse).trans
    (ofEquality (domain.symm.transportBody_roundtrip right))).symm

abbrev leftPositions (point : first.family.Elements) := left.model ⟨point.1.1, ⟨point.1.2, point.2⟩⟩
abbrev rightPositions (point : second.family.Elements) := right.model ⟨point.1.1, ⟨point.1.2, point.2⟩⟩

private theorem modelValue_eq {I : Type u} (family : I → Type u) (models : (index : I) → PresentedType (family index))
    {first second : I} (same : first = second) (left : family first) (right : family second) (members : HEq left right) :
    (models first).value left = (models second).value right := by
  cases same
  cases eq_of_heq members
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem position_value {point next : context.base.Elements} (label : first.family.obj point) (step : point ⟶ next)
    (branch : Position first.family (leftPosition (left := left)) label step) :
    ((rightPositions (right := right)) ⟨next, second.family.map step (domain.fibre point label)⟩).value
      (ContextualWSignature.forwardPosition (signature domain body) label step branch) =
      ((leftPositions (left := left)) ⟨next, first.family.map step label⟩).value branch := by
  have same : (⟨next.1, ⟨next.2, domain.fibre next (first.family.map step label)⟩⟩ : second.extension.base.Elements) =
      ⟨next.1, ⟨next.2, second.family.map step (domain.fibre point label)⟩⟩ :=
    congrArg (fun argument => (⟨next.1, ⟨next.2, argument⟩⟩ : second.extension.base.Elements)) (domain.naturality step label)
  exact (modelValue_eq right.family.obj right.model same _ _
    (ContextualWSignature.forwardPosition_heq (signature domain body) label step branch).symm).symm.trans
      (body.value ⟨next.1, ⟨next.2, first.family.map step label⟩⟩ branch)

variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev leftEncode {point : context.base.Elements} (tree : RawTree first.family (leftPosition (left := left)) point) :=
  MaterialContextualWTypes.encode first.family (leftPosition (left := left)) context.labels
    (MaterialFamily.elementArrowCoding (context := context) arrows) first.model (leftPositions (left := left)) tree

abbrev rightEncode {point : context.base.Elements} (tree : RawTree second.family (rightPosition (right := right)) point) :=
  MaterialContextualWTypes.encode second.family (rightPosition (right := right)) context.labels
    (MaterialFamily.elementArrowCoding (context := context) arrows) second.model (rightPositions (right := right)) tree

theorem shape_tag (point : context.base.Elements) (label : first.family.obj point) :
    ContextualWLabels.shapeTag context.labels point ((second.model point).value (domain.fibre point label)) =
      ContextualWLabels.shapeTag context.labels point ((first.model point).value label) :=
  congrArg (ContextualWLabels.shapeTag context.labels point) (domain.value point label)

def branchMap {point : context.base.Elements} (label : first.family.obj point)
    (branch : ContextualWLabels.Branch first.family (leftPosition (left := left)) label) :
    ContextualWLabels.Branch second.family (rightPosition (right := right)) (domain.fibre point label) :=
  ⟨branch.1, branch.2.1, ContextualWSignature.forwardPosition (signature domain body) label branch.2.1 branch.2.2⟩

def branchInverse {point : context.base.Elements} (label : first.family.obj point)
    (branch : ContextualWLabels.Branch second.family (rightPosition (right := right)) (domain.fibre point label)) :
    ContextualWLabels.Branch first.family (leftPosition (left := left)) label :=
  ⟨branch.1, branch.2.1, (ContextualWSignature.forwardPosition (signature domain body) label branch.2.1).symm branch.2.2⟩

set_option backward.isDefEq.respectTransparency false in
theorem branch_map_inverse {point : context.base.Elements} (label : first.family.obj point)
    (branch : ContextualWLabels.Branch second.family (rightPosition (right := right)) (domain.fibre point label)) :
    branchMap domain body label (branchInverse domain body label branch) = branch := by
  dsimp only [branchMap, branchInverse]
  rw [Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
theorem branch_inverse_map {point : context.base.Elements} (label : first.family.obj point)
    (branch : ContextualWLabels.Branch first.family (leftPosition (left := left)) label) :
    branchInverse domain body label (branchMap domain body label branch) = branch := by
  dsimp only [branchMap, branchInverse]
  rw [Equiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
theorem position_tag (point : context.base.Elements) (label : first.family.obj point)
    (branch : ContextualWLabels.Branch first.family (leftPosition (left := left)) label) :
    ContextualWLabels.positionTag second.family (rightPosition (right := right)) context.labels
      (MaterialFamily.elementArrowCoding (context := context) arrows) second.model (rightPositions (right := right))
      ⟨point, domain.fibre point label⟩ (branchMap domain body label branch) =
    ContextualWLabels.positionTag first.family (leftPosition (left := left)) context.labels
      (MaterialFamily.elementArrowCoding (context := context) arrows) first.model (leftPositions (left := left)) ⟨point, label⟩ branch := by
  dsimp only [ContextualWLabels.positionTag]
  rw [ContextualWLabels.shapeCoding_reading, ContextualWLabels.shapeCoding_reading,
    ContextualWLabels.branchCoding_reading, ContextualWLabels.branchCoding_reading]
  exact congrArg (HSet.kpair {∅}) (congrArg₂ HSet.kpair
    (congrArg (HSet.kpair (context.labels.reading point)) (domain.value point label))
    (congrArg (HSet.kpair (context.labels.reading branch.1))
      (congrArg (HSet.kpair ((MaterialFamily.elementArrowCoding (context := context) arrows point branch.1).reading branch.2.1))
        (position_value domain body label branch.2.1 branch.2.2))))

set_option backward.isDefEq.respectTransparency false in
theorem encode_map {point : context.base.Elements} (tree : RawTree first.family (leftPosition (left := left)) point) :
    rightEncode (right := right) arrows (ContextualWSignature.mapRaw (signature domain body) tree) =
      leftEncode (left := left) arrows tree := by
  induction tree with
  | @sup point label children earlier =>
    apply HSet.ext
    intro value
    rw [ContextualWSignature.mapRaw_sup]
    change value ∈ rightEncode (right := right) arrows
      (.sup (domain.fibre point label) (fun next step branch =>
        ContextualWSignature.mapRaw (signature domain body)
          (children next step ((ContextualWSignature.forwardPosition (signature domain body) label step).symm branch)))) ↔
      value ∈ leftEncode (left := left) arrows (.sup label children)
    rw [MaterialContextualWTypes.mem_encode_sup_iff, MaterialContextualWTypes.mem_encode_sup_iff]
    constructor
    · rintro (same | ⟨branch, same⟩)
      · exact Or.inl (same.trans (congrArg (fun tag => HSet.kpair tag ∅) (shape_tag domain point label)))
      · let oldBranch := branchInverse domain body label branch
        refine Or.inr ⟨oldBranch, ?_⟩
        have tags := (congrArg (fun entry => ContextualWLabels.positionTag second.family
          (rightPosition (right := right)) context.labels
          (MaterialFamily.elementArrowCoding (context := context) arrows) second.model (rightPositions (right := right))
          ⟨point, domain.fibre point label⟩ entry) (branch_map_inverse domain body label branch)).symm.trans
            (position_tag domain body arrows point label oldBranch)
        exact same.trans (congrArg₂ HSet.kpair tags (earlier oldBranch.1 oldBranch.2.1 oldBranch.2.2))
    · rintro (same | ⟨branch, same⟩)
      · exact Or.inl (same.trans (congrArg (fun tag => HSet.kpair tag ∅) (shape_tag domain point label).symm))
      · refine Or.inr ⟨branchMap domain body label branch, ?_⟩
        have recovers := (ContextualWSignature.forwardPosition (signature domain body) label branch.2.1).symm_apply_apply branch.2.2
        have childValues := (congrArg (fun input => rightEncode (right := right) arrows
          (ContextualWSignature.mapRaw (signature domain body) (children branch.1 branch.2.1 input))) recovers).trans
            (earlier branch.1 branch.2.1 branch.2.2)
        exact same.trans (congrArg₂ HSet.kpair (position_tag domain body arrows point label branch).symm childValues.symm)

include arrows in
set_option backward.isDefEq.respectTransparency false in
theorem map_backward_map {point : context.base.Elements} (tree : RawTree first.family (leftPosition (left := left)) point) :
    ContextualWSignature.mapRaw (signature domain.symm (bodyBackward domain body))
      (ContextualWSignature.mapRaw (signature domain body) tree) = tree := by
  apply MaterialContextualWTypes.encode_injective first.family (leftPosition (left := left)) context.labels
    (MaterialFamily.elementArrowCoding (context := context) arrows) first.model (leftPositions (left := left))
  exact (encode_map domain.symm (bodyBackward domain body) arrows _).trans (encode_map domain body arrows tree)

include arrows in
set_option backward.isDefEq.respectTransparency false in
theorem map_map_backward {point : context.base.Elements} (tree : RawTree second.family (rightPosition (right := right)) point) :
    ContextualWSignature.mapRaw (signature domain body)
      (ContextualWSignature.mapRaw (signature domain.symm (bodyBackward domain body)) tree) = tree := by
  apply MaterialContextualWTypes.encode_injective second.family (rightPosition (right := right)) context.labels
    (MaterialFamily.elementArrowCoding (context := context) arrows) second.model (rightPositions (right := right))
  exact (encode_map domain body arrows _).trans (encode_map domain.symm (bodyBackward domain body) arrows tree)

noncomputable def rawEquiv (point : context.base.Elements) :
    RawTree first.family (leftPosition (left := left)) point ≃
      RawTree second.family (rightPosition (right := right)) point where
  toFun := ContextualWSignature.mapRaw (signature domain body)
  invFun := ContextualWSignature.mapRaw (signature domain.symm (bodyBackward domain body))
  left_inv := map_backward_map domain body arrows
  right_inv := map_map_backward domain body arrows

noncomputable def naturalEquiv (point : context.base.Elements) :
    NaturalTree first.family (leftPosition (left := left)) point ≃
      NaturalTree second.family (rightPosition (right := right)) point where
  toFun := ContextualWSignature.mapNatural (signature domain body)
  invFun := ContextualWSignature.mapNatural (signature domain.symm (bodyBackward domain body))
  left_inv tree := Subtype.ext (map_backward_map domain body arrows tree.val)
  right_inv tree := Subtype.ext (map_map_backward domain body arrows tree.val)

noncomputable def w : Equivalence (first.w left arrows) (second.w right arrows) where
  fibre := naturalEquiv domain body arrows
  naturality step tree := ContextualWSignature.mapNatural_restrict (signature domain body) step tree
  value _point tree := encode_map domain body arrows tree.val

include domain body in
theorem carrier (point : context.base.Elements) :
    ((first.w left arrows).model point).carrier = ((second.w right arrows).model point).carrier :=
  (w domain body arrows).carrier point

noncomputable def memberEquiv (point : context.base.Elements) :
    {value : HSet.{u} // value ∈ ((first.w left arrows).model point).carrier} ≃
      {value : HSet.{u} // value ∈ ((second.w right arrows).model point).carrier} :=
  (((first.w left arrows).model point).decode.trans (naturalEquiv domain body arrows point)).trans
    ((second.w right arrows).model point).decode.symm

theorem member_value (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((first.w left arrows).model point).carrier}) :
    (memberEquiv domain body arrows point member).val = member.val :=
  ((w domain body arrows).value point (((first.w left arrows).model point).decode member)).trans
    (((first.w left arrows).model point).value_decode member)

theorem decoder (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((first.w left arrows).model point).carrier}) :
    ((second.w right arrows).model point).decode (memberEquiv domain body arrows point member) =
      naturalEquiv domain body arrows point (((first.w left arrows).model point).decode member) :=
  ((second.w right arrows).model point).decode.apply_symm_apply _

theorem member_restriction {point next : context.base.Elements} (step : point ⟶ next)
    (member : {value : HSet.{u} // value ∈ ((first.w left arrows).model point).carrier}) :
    memberEquiv domain body arrows next ((first.w left arrows).memberRestriction step member) =
      (second.w right arrows).memberRestriction step (memberEquiv domain body arrows point member) := by
  apply ((second.w right arrows).model next).decode.injective
  rw [decoder, MaterialFamily.memberRestriction_decode, MaterialFamily.memberRestriction_decode, decoder]
  exact (w domain body arrows).naturality step (((first.w left arrows).model point).decode member)

variable (target : context.base.Elements ⥤ Type u)

def algebraBackward (algebra : ContextualWTypes.Algebra second.family (rightPosition (right := right)) target) :
    ContextualWTypes.Algebra first.family (leftPosition (left := left)) target :=
  ContextualWSignature.pullAlgebra (signature domain body) target algebra

def algebraForward (algebra : ContextualWTypes.Algebra first.family (leftPosition (left := left)) target) :
    ContextualWTypes.Algebra second.family (rightPosition (right := right)) target :=
  ContextualWSignature.pullAlgebra (signature domain.symm (bodyBackward domain body)) target algebra

theorem fold_comparison (algebra : ContextualWTypes.Algebra second.family (rightPosition (right := right)) target)
    (point : context.base.Elements) (tree : (first.w left arrows).family.obj point) :
    ContextualWTypes.fold second.family (rightPosition (right := right)) algebra
      (naturalEquiv domain body arrows point tree) =
      ContextualWTypes.fold first.family (leftPosition (left := left)) (algebraBackward domain body target algebra) tree :=
  ContextualWSignature.fold_map (signature domain body) target algebra tree

theorem fold_forward (algebra : ContextualWTypes.Algebra first.family (leftPosition (left := left)) target)
    (point : context.base.Elements) (tree : (first.w left arrows).family.obj point) :
    ContextualWTypes.fold second.family (rightPosition (right := right)) (algebraForward domain body target algebra)
      (naturalEquiv domain body arrows point tree) =
      ContextualWTypes.fold first.family (leftPosition (left := left)) algebra tree :=
  (ContextualWSignature.fold_map (signature domain.symm (bodyBackward domain body)) target algebra
    ((naturalEquiv domain body arrows point) tree)).symm.trans
      (congrArg (ContextualWTypes.fold first.family (leftPosition (left := left)) algebra)
        ((naturalEquiv domain body arrows point).symm_apply_apply tree))

theorem foldMap_comparison (algebra : ContextualWTypes.Algebra second.family (rightPosition (right := right)) target) :
    Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.compose (w domain body arrows).hom
      (ContextualWTypes.foldMap second.family (rightPosition (right := right)) algebra) =
      ContextualWTypes.foldMap first.family (leftPosition (left := left)) (algebraBackward domain body target algebra) := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  exact fold_comparison domain body arrows target algebra point

theorem fold_decoder (algebra : ContextualWTypes.Algebra second.family (rightPosition (right := right)) target)
    (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ ((first.w left arrows).model point).carrier}) :
    ContextualWTypes.fold second.family (rightPosition (right := right)) algebra
      (((second.w right arrows).model point).decode (memberEquiv domain body arrows point member)) =
      ContextualWTypes.fold first.family (leftPosition (left := left)) (algebraBackward domain body target algebra)
        (((first.w left arrows).model point).decode member) :=
  (congrArg (ContextualWTypes.fold second.family (rightPosition (right := right)) algebra)
    (decoder domain body arrows point member)).trans
      (fold_comparison domain body arrows target algebra point (((first.w left arrows).model point).decode member))

theorem constructor_comparison (point : context.base.Elements) (label : first.family.obj point)
    (branches : ContextualWTypes.Branches first.family (leftPosition (left := left)) (first.w left arrows).family label) :
    naturalEquiv domain body arrows point ((ContextualWTypes.treeAlgebra first.family (leftPosition (left := left))).make point label branches) =
      (ContextualWTypes.treeAlgebra second.family (rightPosition (right := right))).make point (domain.fibre point label)
        ((ContextualWSignature.mapBranches (signature domain body) (first.w left arrows).family label branches).map
          (w domain body arrows).hom) :=
  Subtype.ext rfl

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialWEquivalence
