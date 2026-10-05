import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedUniverse
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWBaseChange

/-!
# Generated contextual W families under substitution

The newly formed hereditary-natural W family has the original material
dictionary transported through the constructed indexed-tree equivalence.
The comparison preserves complete future branches, restriction maps,
constructors and folds. Fresh independently chosen labels may give another
material graph encoding of the same tree family.

The enclosure statement uses the generated reindexing of the original W
family. It does not identify universe codes from equality of carriers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedWBaseChange

open CategoryTheory

noncomputable section
open ContextualGeneratedUniverse
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable {context other : LabelledContext C}
variable (domain : MaterialFamily context) (body : MaterialFamily domain.extension)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable (change : NatTrans other.base context.base)

def wComparison (point : other.base.Elements) :
    ((domain.w body arrows).reindex change).family.obj point ≃
      (ContextualWTypes.family
        (PowerClassPresheafProducts.reindex change domain.family)
        (PowerClassPresheafBaseChange.bodyReindex change domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family))).obj point :=
  ContextualWBaseChange.naturalEquiv change domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family) point

/-- Native W formation after substitution, with its material dictionary
transported through the proved full contextual W comparison. -/
def wUnder : MaterialFamily other where
  family := ContextualWTypes.family
    (PowerClassPresheafProducts.reindex change domain.family)
    (PowerClassPresheafBaseChange.bodyReindex change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family))
  model point := (((domain.w body arrows).reindex change).model point).relabel
    (wComparison domain body arrows change point)

theorem wUnder_carrier (point : other.base.Elements) :
    ((wUnder domain body arrows change).model point).carrier =
      (((domain.w body arrows).reindex change).model point).carrier := rfl

theorem wUnder_value (point : other.base.Elements)
    (tree : ((domain.w body arrows).reindex change).family.obj point) :
    ((wUnder domain body arrows change).model point).value
      (wComparison domain body arrows change point tree) =
        (((domain.w body arrows).reindex change).model point).value tree := by
  change (((domain.w body arrows).reindex change).model point).value
    ((wComparison domain body arrows change point).symm
      (wComparison domain body arrows change point tree)) = _
  exact congrArg (((domain.w body arrows).reindex change).model point).value
    ((wComparison domain body arrows change point).symm_apply_apply tree)

def wUnderMember (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ (((domain.w body arrows).reindex change).model point).carrier}) :
    {value : HSet.{u} // value ∈ ((wUnder domain body arrows change).model point).carrier} := member

theorem wUnder_decoder (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ (((domain.w body arrows).reindex change).model point).carrier}) :
    ((wUnder domain body arrows change).model point).decode
      (wUnderMember domain body arrows change point member) =
        wComparison domain body arrows change point
          ((((domain.w body arrows).reindex change).model point).decode member) := rfl

def wMemberComparison (point : other.base.Elements) :
    {value : HSet.{u} // value ∈ (((domain.w body arrows).reindex change).model point).carrier} ≃
      {value : HSet.{u} // value ∈ ((wUnder domain body arrows change).model point).carrier} :=
  ((((domain.w body arrows).reindex change).model point).decode.trans
    (wComparison domain body arrows change point)).trans
      (((wUnder domain body arrows change).model point).decode.symm)

theorem wMemberComparison_decode (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ (((domain.w body arrows).reindex change).model point).carrier}) :
    ((wUnder domain body arrows change).model point).decode
      (wMemberComparison domain body arrows change point member) =
        wComparison domain body arrows change point
          ((((domain.w body arrows).reindex change).model point).decode member) :=
  ((wUnder domain body arrows change).model point).decode.apply_symm_apply _

theorem wMemberComparison_value (point : other.base.Elements)
    (member : {value : HSet.{u} // value ∈ (((domain.w body arrows).reindex change).model point).carrier}) :
    (wMemberComparison domain body arrows change point member).val = member.val := by
  change ((wUnder domain body arrows change).model point).value
    (wComparison domain body arrows change point
      ((((domain.w body arrows).reindex change).model point).decode member)) = member.val
  exact (wUnder_value domain body arrows change point _).trans
    ((((domain.w body arrows).reindex change).model point).value_decode member)

theorem wUnder_restriction {first second : other.base.Elements} (step : first ⟶ second)
    (tree : ((domain.w body arrows).reindex change).family.obj first) :
    wComparison domain body arrows change second
      (((domain.w body arrows).reindex change).family.map step tree) =
        (wUnder domain body arrows change).family.map step
          (wComparison domain body arrows change first tree) :=
  Subtype.ext (ContextualWBaseChange.pullRaw_restrict change domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family) step tree.val)

theorem wMemberComparison_restriction {first second : other.base.Elements}
    (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ (((domain.w body arrows).reindex change).model first).carrier}) :
    wMemberComparison domain body arrows change second
      (((domain.w body arrows).reindex change).memberRestriction step member) =
        (wUnder domain body arrows change).memberRestriction step
          (wMemberComparison domain body arrows change first member) := by
  apply ((wUnder domain body arrows change).model second).decode.injective
  exact (wMemberComparison_decode domain body arrows change second _).trans
    ((congrArg (wComparison domain body arrows change second)
      (((domain.w body arrows).reindex change).memberRestriction_decode step member)).trans
      ((wUnder_restriction domain body arrows change step _).trans
        ((congrArg ((wUnder domain body arrows change).family.map step)
          (wMemberComparison_decode domain body arrows change first member).symm).trans
          ((wUnder domain body arrows change).memberRestriction_decode step
            (wMemberComparison domain body arrows change first member)).symm)))

theorem wUnder_constructor (point : other.base.Elements)
    (label : domain.family.obj ((PowerClassPresheafProducts.elementMap change).obj point))
    (branches : ContextualWTypes.Branches domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family)
      (domain.w body arrows).family label) :
    wComparison domain body arrows change point
      ((ContextualWTypes.treeAlgebra domain.family
        (PowerClassPresheafProducts.indexedBody domain.family body.family)).make
          ((PowerClassPresheafProducts.elementMap change).obj point) label branches) =
      (ContextualWTypes.treeAlgebra
        (PowerClassPresheafProducts.reindex change domain.family)
        (PowerClassPresheafBaseChange.bodyReindex change domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family))).make point label
        (ContextualWBaseChange.pullTreeBranches change domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family) point label branches) :=
  ContextualWBaseChange.constructor_baseChange change domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family) point label branches

theorem wUnder_constructor_value (point : other.base.Elements)
    (label : domain.family.obj ((PowerClassPresheafProducts.elementMap change).obj point))
    (branches : ContextualWTypes.Branches domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family)
      (domain.w body arrows).family label) :
    ((wUnder domain body arrows change).model point).value
      ((ContextualWTypes.treeAlgebra
        (PowerClassPresheafProducts.reindex change domain.family)
        (PowerClassPresheafBaseChange.bodyReindex change domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family))).make point label
        (ContextualWBaseChange.pullTreeBranches change domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family) point label branches)) =
      (((domain.w body arrows).reindex change).model point).value
        ((ContextualWTypes.treeAlgebra domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family)).make
            ((PowerClassPresheafProducts.elementMap change).obj point) label branches) :=
  (congrArg ((wUnder domain body arrows change).model point).value
    (wUnder_constructor domain body arrows change point label branches).symm).trans
      (wUnder_value domain body arrows change point _)

theorem wUnder_fold (target : MaterialFamily context)
    (algebra : ContextualWTypes.Algebra domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family) target.family)
    (point : other.base.Elements)
    (tree : ((domain.w body arrows).reindex change).family.obj point) :
    ((target.reindex change).model point).value
      (ContextualWTypes.fold (PowerClassPresheafProducts.reindex change domain.family)
        (PowerClassPresheafBaseChange.bodyReindex change domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family))
        (ContextualWBaseChange.pullAlgebra change domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family) target.family algebra)
        (wComparison domain body arrows change point tree)) =
      (target.model ((PowerClassPresheafProducts.elementMap change).obj point)).value
        (ContextualWTypes.fold domain.family
          (PowerClassPresheafProducts.indexedBody domain.family body.family) algebra tree) :=
  congrArg (target.model ((PowerClassPresheafProducts.elementMap change).obj point)).value
    (ContextualWBaseChange.fold_baseChange change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family) target.family algebra point tree)

variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)

theorem wUnder_mem_enclosure
    (first : Generation seeds seedModel arrows domain)
    (second : Generation seeds seedModel arrows body) (point : other.base.Elements) :
    HSet.lift ((wUnder domain body arrows change).model point).carrier ∈
      enclosure seeds seedModel arrows other point :=
  generated_mem_enclosure seeds seedModel arrows (.reindex (.w first second) change) point

namespace Growing

open ContextualGeneratedUniverse.Growing

/-- The substitution is the actual comprehension projection of the observed
family, retaining a material argument in its source context. -/
def projection : NatTrans input.extension.base ContextualGeneratedUniverse.Growing.context.base :=
  PowerClassPresheafProducts.projection input.family

def cyclicPoint : input.extension.base.Elements :=
  ⟨later.1, ⟨later.2, PowerClassContextualMaterialization.Growing.futureArgument⟩⟩

def cyclicLeaf : (wUnder input terminalBody arrowCoding projection).family.obj cyclicPoint :=
  wComparison input terminalBody arrowCoding projection cyclicPoint
    (leaf later PowerClassContextualMaterialization.Growing.futureArgument)

theorem cyclicLeaf_value :
    ((wUnder input terminalBody arrowCoding projection).model cyclicPoint).value cyclicLeaf =
      ((input.w terminalBody arrowCoding).model later).value
        (leaf later PowerClassContextualMaterialization.Growing.futureArgument) :=
  wUnder_value input terminalBody arrowCoding projection cyclicPoint _

theorem cyclicLeaf_member :
    ((input.w terminalBody arrowCoding).model later).value
      (leaf later PowerClassContextualMaterialization.Growing.futureArgument) ∈
        ((wUnder input terminalBody arrowCoding projection).model cyclicPoint).carrier := by
  rw [← cyclicLeaf_value]
  exact ((wUnder input terminalBody arrowCoding projection).model cyclicPoint).value_mem cyclicLeaf

theorem cyclic_payload :
    ((input.reindex projection).model cyclicPoint).value
      PowerClassContextualMaterialization.Growing.futureArgument = HSet.quineAtom :=
  cyclic_leaf_shape

/-- Inhabited unary positions produce no inductive tree, also after the
nontrivial comprehension substitution. -/
theorem unary_wUnder_empty (point : input.extension.base.Elements) :
    ((wUnder input unaryBody arrowCoding projection).model point).carrier = ∅ :=
  unary_w_empty ((PowerClassPresheafProducts.elementMap projection).obj point)

end Growing

end

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedWBaseChange
