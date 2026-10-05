import Mettapedia.TypeTheory.PresheafSiteLift
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedUniverse
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeCumulativity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseSizeObstructions

/-!
# Material families on the constructed successor site

The successor site raises worlds and actual arrows, not just fibre carriers.
Its context dictionaries and every interpreted fibre graph are constructed
by graph lifting. The explicit member, term and restriction comparisons
retain the decoded lower value. Comprehension and base change retain the
whole parent point and its actual substitution arrow.

This translates existing material interpretations. It neither constructs a
fixed-level internal universe nor asserts that every upper semantic family
is a translation. The ambient material carrier gives a concrete obstruction
to the latter claim.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSiteLiftMaterial

open CategoryTheory
open ContextualGeneratedUniverse
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

open Mettapedia.TypeTheory

universe u
variable {C : Type u} [Category.{u} C]

abbrev context (original : LabelledContext C) : LabelledContext (PresheafSiteLift.Site C) where
  base := PresheafSiteLift.base original.base
  labels := {
    graph := fun point => (original.labels.graph ((PresheafSiteLift.elementsDown original.base).obj point)).lift
    injective := by
      intro first second same
      apply PresheafSiteLift.elementsDown_obj_injective original.base
      apply original.labels.injective
      exact HSet.lift_injective same }

theorem context_label (original : LabelledContext C) (point : (context original).base.Elements) :
    (context original).labels.reading point =
      HSet.lift (original.labels.reading ((PresheafSiteLift.elementsDown original.base).obj point)) := rfl

def arrows (original : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
    (first second : (PresheafSiteLift.Site C)ᵒᵖ) : ArgumentCoding (first ⟶ second) where
  graph step := (original (PresheafSiteLift.downOp.obj first) (PresheafSiteLift.downOp.obj second)).graph (PresheafSiteLift.downOp.map step) |>.lift
  injective := by
    intro left right same
    apply PresheafSiteLift.downOp_map_injective
    apply (original (PresheafSiteLift.downOp.obj first) (PresheafSiteLift.downOp.obj second)).injective
    exact HSet.lift_injective same

theorem arrow_label (original : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
    {first second : (PresheafSiteLift.Site C)ᵒᵖ} (step : first ⟶ second) :
    (arrows original first second).reading step =
      HSet.lift ((original (PresheafSiteLift.downOp.obj first) (PresheafSiteLift.downOp.obj second)).reading (PresheafSiteLift.downOp.map step)) := rfl

abbrev family {original : LabelledContext C} (domain : MaterialFamily original) : MaterialFamily (context original) where
  family := PresheafSiteLift.family original.base domain.family
  model point := PresentedTypeCumulativity.liftModel (domain.model ((PresheafSiteLift.elementsDown original.base).obj point))

theorem carrier {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements) :
    ((family domain).model point).carrier =
      HSet.lift ((domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier) := rfl

theorem value {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements) (term : (family domain).family.obj point) :
    ((family domain).model point).value term =
      HSet.lift ((domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).value term.down) := rfl

def liftMember {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier}) :
    {value : HSet.{u + 1} // value ∈ ((family domain).model point).carrier} :=
  HSet.liftedMembersEquiv _ member

def lowerMember {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((family domain).model point).carrier}) :
    {value : HSet.{u} // value ∈ (domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier} :=
  (HSet.liftedMembersEquiv _).symm member

theorem lower_lift_member {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier}) :
    lowerMember domain point (liftMember domain point member) = member := Equiv.symm_apply_apply _ _

theorem lift_lower_member {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((family domain).model point).carrier}) :
    liftMember domain point (lowerMember domain point member) = member := Equiv.apply_symm_apply _ _

theorem lift_member_value {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier}) :
    (liftMember domain point member).val = HSet.lift member.val := rfl

theorem decode_lift_member {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier}) :
    ((family domain).model point).decode (liftMember domain point member) =
      ULift.up ((domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).decode member) := by
  change ULift.up ((domain.model _).decode ((HSet.liftedMembersEquiv _).symm
    (HSet.liftedMembersEquiv _ member))) = _
  exact congrArg ULift.up (congrArg (domain.model _).decode
    ((HSet.liftedMembersEquiv _).symm_apply_apply member))

theorem decode_lower_member {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((family domain).model point).carrier}) :
    (domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).decode (lowerMember domain point member) =
      (((family domain).model point).decode member).down := rfl

theorem member_restriction {original : LabelledContext C} (domain : MaterialFamily original)
    {first second : (context original).base.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ (domain.model ((PresheafSiteLift.elementsDown original.base).obj first)).carrier}) :
    (family domain).memberRestriction step (liftMember domain first member) =
      liftMember domain second (domain.memberRestriction ((PresheafSiteLift.elementsDown original.base).map step) member) := by
  apply ((family domain).model second).decode.injective
  rw [MaterialFamily.memberRestriction_decode, decode_lift_member, decode_lift_member,
    MaterialFamily.memberRestriction_decode]
  rfl

theorem lower_member_restriction {original : LabelledContext C} (domain : MaterialFamily original)
    {first second : (context original).base.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈ ((family domain).model first).carrier}) :
    lowerMember domain second ((family domain).memberRestriction step member) =
      domain.memberRestriction ((PresheafSiteLift.elementsDown original.base).map step) (lowerMember domain first member) := by
  apply (domain.model ((PresheafSiteLift.elementsDown original.base).obj second)).decode.injective
  exact (congrArg ULift.down ((family domain).memberRestriction_decode step member)).trans
    (domain.memberRestriction_decode ((PresheafSiteLift.elementsDown original.base).map step)
      (lowerMember domain first member)).symm

theorem term_value {original : LabelledContext C} (domain : MaterialFamily original)
    (term : domain.family.sections) (point : (context original).base.Elements) :
    ((family domain).model point).value ((PresheafSiteLift.raiseTerm original.base domain.family term).val point) =
      HSet.lift ((domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).value
        (term.val ((PresheafSiteLift.elementsDown original.base).obj point))) := rfl

theorem term_graph {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (context original).base.Elements) (term : (family domain).family.obj point) :
    ((family domain).model point).termGraph term ≈
      ((domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).termGraph term.down).lift := by
  apply HSet.mk_eq_mk_iff.mp
  rw [← HSet.lift_mk, PresentedType.mk_termGraph, PresentedType.mk_termGraph, value]

theorem reindex_family {original other : LabelledContext C}
    (domain : MaterialFamily original) (change : NatTrans other.base original.base) :
    (family (domain.reindex change)).family =
      ((family domain).reindex (PresheafSiteLift.raiseChange change)).family := by
  refine Functor.hext (fun _ => rfl) ?_
  intro _ _ _
  rfl

theorem reindex_carrier {original other : LabelledContext C}
    (domain : MaterialFamily original) (change : NatTrans other.base original.base)
    (point : (context other).base.Elements) :
    ((family (domain.reindex change)).model point).carrier =
      (((family domain).reindex (PresheafSiteLift.raiseChange change)).model point).carrier := rfl

theorem reindex_value {original other : LabelledContext C}
    (domain : MaterialFamily original) (change : NatTrans other.base original.base)
    (point : (context other).base.Elements)
    (term : (family (domain.reindex change)).family.obj point) :
    ((family (domain.reindex change)).model point).value term =
      (((family domain).reindex (other := context other) (PresheafSiteLift.raiseChange change)).model point).value
        (ULift.up term.down) := rfl

theorem extension_label {original : LabelledContext C} (domain : MaterialFamily original)
    (point : (family domain).extension.base.Elements) :
    (family domain).extension.labels.reading point =
      HSet.lift (domain.extension.labels.reading
        ((PresheafSiteLift.elementsDown (totalSpace domain.family)).obj
          ((PresheafSiteLift.elementsMap (PresheafSiteLift.comprehensionFrom original.base domain.family)).obj point))) := by
  change HSet.mk (AccessiblePointedGraph.kpairGraph _ _) = HSet.lift (HSet.mk (AccessiblePointedGraph.kpairGraph _ _))
  rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph,
    PresentedType.mk_termGraph, PresentedType.mk_termGraph, HSet.lift_kpair]
  rfl

/-- A dependent body is transported along the constructed comprehension
comparison, retaining its parent and first coordinate. -/
abbrev body {original : LabelledContext C} (domain : MaterialFamily original)
    (codomain : MaterialFamily domain.extension) : MaterialFamily (family domain).extension :=
  (family codomain).reindex (other := (family domain).extension)
    (PresheafSiteLift.comprehensionFrom original.base domain.family)

theorem indexed_body {original : LabelledContext C} (domain : MaterialFamily original)
    (codomain : MaterialFamily domain.extension) :
    PowerClassPresheafProducts.indexedBody (family domain).family (body domain codomain).family =
      PresheafSiteLift.body original.base domain.family
        (PowerClassPresheafProducts.indexedBody domain.family codomain.family) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second step
  apply heq_of_eq
  apply ConcreteCategory.hom_ext
  intro term
  apply congrArg ULift.up
  apply congrArg (fun arrow => codomain.family.map arrow term.down)
  apply CategoryOfElements.ext domain.extension.base
  change PresheafSiteLift.downOp.map
      ((DisplayedPresheafIndexedCwfBridge.displayedToTotalElements (family domain).family).map step).val =
    ((DisplayedPresheafIndexedCwfBridge.displayedToTotalElements domain.family).map
      ((PresheafSiteLift.displayedElementsDown original.base domain.family).map step)).val
  rw [DisplayedPresheafIndexedCwfBridge.displayedToTotalElements_underlying,
    DisplayedPresheafIndexedCwfBridge.displayedToTotalElements_underlying]
  rfl

theorem body_value {original : LabelledContext C} (domain : MaterialFamily original)
    (codomain : MaterialFamily domain.extension) (point : (family domain).extension.base.Elements)
    (term : (body domain codomain).family.obj point) :
    ((body domain codomain).model point).value term =
      HSet.lift ((codomain.model
        ((PresheafSiteLift.elementsDown domain.extension.base).obj
          ((PresheafSiteLift.elementsMap (PresheafSiteLift.comprehensionFrom original.base domain.family)).obj point))).value
        term.down) := rfl

/-- An upper semantic carrier cannot always descend to a lower carrier.
The obstruction is size, not failure to choose a graph representative. -/
theorem ambient_not_lower_image (T : Type u) : ¬ Nonempty (ULift.{u + 1, u} T ≃ HSet.{u}) := by
  rintro ⟨equivalence⟩
  apply UniverseSizeObstructions.ambient_not_small
  exact Small.mk' (equivalence.symm.trans Equiv.ulift)

namespace Growing

abbrev original := ContextualGeneratedUniverse.Growing.context
abbrev input := ContextualGeneratedUniverse.Growing.input

def raisedContext : LabelledContext (PresheafSiteLift.Site ContextualGeneratedUniverse.Growing.Stages) := context original

def raisedInput : MaterialFamily raisedContext := family input

def raisePoint (point : original.base.Elements) : raisedContext.base.Elements :=
  (PresheafSiteLift.elementsUp original.base).obj point

theorem actual_growing_value (point : original.base.Elements) (term : input.family.obj point) :
    (raisedInput.model (raisePoint point)).value (ULift.up term) =
      HSet.lift (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.valueAt point term) := by
  change HSet.lift ((input.model point).value term) = _
  rw [ContextualGeneratedUniverse.Growing.input_value]

theorem contextual_transport {first second : original.base.Elements} (step : first ⟶ second)
    (term : input.family.obj first) :
    raisedInput.family.map ((PresheafSiteLift.elementsUp original.base).map step) (ULift.up term) =
      ULift.up (input.family.map step term) := rfl

theorem world_injective : Function.Injective (fun stage : ContextualGeneratedUniverse.Growing.Stages =>
    PresheafSiteLift.Site.upFunctor.obj stage) := by
  intro first second same
  exact congrArg PresheafSiteLift.Site.downFunctor.obj same

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSiteLiftMaterial
